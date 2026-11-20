import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/- Phase 5.1 isolation: `TurnEvent` and `applyTurnEvent` drive `turnNumber`,
`activePlayer`, `step`, `isNight`, `extraTurns` (CR 500.7 LIFO), and
`additionalCombatPhases` (CR 500.8). Step/phase/turn transitions emit
`stepEnded`, `phaseEnded`, `phaseBegan`, `stepBegan`, `turnEnded`, and
`turnBegan`. -/
#guard
  let g0 := quiet afterDraw
  -- Extra turns LIFO (CR 500.7) and extra combat phase (CR 500.8)
  let g1 :=
    (g0.record (GameEvent.extraTurnAdded g0.turnNumber me .current
      (cause := .oneShotEffect (some ⟨97⟩) none (some me)))).record
      (GameEvent.extraTurnAdded g0.turnNumber opp .current
        (cause := .oneShotEffect (some ⟨98⟩) none (some me)))
  let g2 := g1.record (GameEvent.extraPhaseAdded g1.turnNumber .combat .current
    (cause := .oneShotEffect (some ⟨99⟩) none (some me)))
  let g3 := g2.record (GameEvent.turnBegan (g2.turnNumber + 1) opp (extra := true))
  let g4 := (g3.record (GameEvent.stepBegan g3.turnNumber .endOfCombat opp)).record
    (GameEvent.phaseBegan g3.turnNumber .combat)
  let g5 := g4.applyChange (.rules (.turn (.dayNightChanged true)))
  -- Step advance across phase boundary (draw -> precombatMain)
  let gStep := (quiet (afterDraw.record (GameEvent.stepBegan afterDraw.turnNumber .draw afterDraw.activePlayer))).advanceStep
  let turnEvents := gStep.events.filterMap (fun e =>
    match e.change with
    | .rules (.turn te) => some te
    | _ => none)
  g1.extraTurns == #[opp, me] &&
    g2.additionalCombatPhases == g0.additionalCombatPhases + 1 &&
    g3.turnNumber == g0.turnNumber + 1 &&
    g3.activePlayer == opp &&
    !g3.isFirstTurn &&
    g3.extraTurns == #[me] &&
    g4.additionalCombatPhases == g0.additionalCombatPhases &&
    g5.isNight &&
    turnEvents.contains (.stepEnded .draw) &&
    turnEvents.contains (.phaseEnded .beginning) &&
    turnEvents.contains (.phaseBegan .precombatMain) &&
    turnEvents.contains (.stepBegan .precombatMain me) &&
    allRulesEventsClassified g1 &&
    allRulesEventsClassified g2 &&
    allRulesEventsClassified gStep

/- Phase 5.2 isolation: `CombatEvent` (`attackersDeclared`, `becameAttacking`,
`blockersDeclared`, `becameBlocked`, `remainedUnblocked`, `damageAssigned`,
`removedFromCombat`) and `AttackTarget` (`player`, `planeswalker`, `battle`).
Verifies that `declareAttackers` batches `attackersDeclared` and non-vigilance
`PermanentEvent.tapped` under one `BatchId`, and that 508.4 `becameAttacking`
sets `attacking := true` and `attackingTarget` without firing "whenever …
attacks" triggers (CR 508.3a). -/
#guard
  let attackWatcher : CardDef :=
    { (creature "Attack Watcher" ManaCost.empty #["Hero"] 2 2) with
      triggeredAbilities := #[TriggeredAbility.fra (.fra .creatureYouControlAttacks) "" (.draw 1)] }
  let oppWalker : CardDef :=
    { name := "Opp Walker"
      types := #[.planeswalker]
      subtypes := #["Jace"]
      loyalty := some 4 }
  let g0 :=
    let g := addPermanent (addPermanent (addPermanent (addPermanent afterDraw attackWatcher me me) bear me me) hero me me) oppWalker opp opp
    let g := addPermanent g bear opp opp
    let g := (g.record (GameEvent.stepBegan g.turnNumber .declareAttackers g.activePlayer)).change (.pending .declareAttackers)
    quiet g
  let bMe := (g0.battlefield.filter (fun o => o.name == bear.name && g0.controlledBy o me))[0]!
  let hMe := (g0.battlefield.filter (fun o => o.name == hero.name && g0.controlledBy o me))[0]!
  let pwOpp := (g0.battlefield.filter (·.name == "Opp Walker"))[0]!
  let bOpp := (g0.battlefield.filter (fun o => o.name == bear.name && g0.controlledBy o opp))[0]!
  -- 1. 508.4 becameAttacking (targeting planeswalker) does NOT fire attack triggers
  let gBecame := g0.record (GameEvent.becameAttacking g0.turnNumber (g0.snapshot hMe) (.planeswalker pwOpp.id)
    (cause := .oneShotEffect (some ⟨77⟩) none (some me)))
  let hAfterBecame := gBecame.object! hMe.id
  let becameEvents := gBecame.events.filter (fun e =>
    match e.change with
    | .rules (.combat (.becameAttacking c (.planeswalker pid))) =>
      c.id == some hMe.id && pid == pwOpp.id
    | _ => false)
  -- 2. declareAttackers with bMe attacking opp
  let gAtk :=
    match g0.declareAttackers me #[bMe.id] (each := #[some opp]) with
    | .ok g => g
    | .error _ => g0
  let bAfterAtk := gAtk.object! bMe.id
  let atkCombatAndTap := gAtk.events.filter (fun e =>
    match e.change with
    | .rules (.combat (.attackersDeclared _ _)) => true
    | .rules (.permanent (.tapped o _)) => o.id == some bMe.id
    | _ => false)
  -- 3. declareBlockers with bOpp blocking bMe while hMe (made attacking) remains unblocked
  let gBothAtk := (quiet gAtk).record (GameEvent.becameAttacking gAtk.turnNumber (gAtk.snapshot (gAtk.object! hMe.id)) (.player opp)
    (cause := .oneShotEffect (some ⟨78⟩) none (some me)))
  let gToBlk := quiet ((gBothAtk.record (GameEvent.stepBegan gBothAtk.turnNumber .declareBlockers gBothAtk.activePlayer)).changes #[
    .pending .declareBlockers,
    .blockersQueue #[opp]
  ])
  let gBlk :=
    match gToBlk.declareBlockers opp #[(bOpp.id, bMe.id)] with
    | .ok g => g
    | .error _ => gToBlk
  let hasBlockersDeclared := gBlk.events.any (fun e =>
    match e.change with
    | .rules (.combat (.blockersDeclared p decls)) =>
      p == opp && decls.any (fun (b, aid) => b.id == some bOpp.id && aid == bMe.id)
    | _ => false)
  let hasBecameBlocked := gBlk.events.any (fun e =>
    match e.change with
    | .rules (.combat (.becameBlocked a bids)) =>
      a.id == some bMe.id && bids == #[bOpp.id]
    | _ => false)
  let hasRemainedUnblocked := gBlk.events.any (fun e =>
    match e.change with
    | .rules (.combat (.remainedUnblocked a)) => a.id == some hMe.id
    | _ => false)
  -- 4. CombatEvent.removedFromCombat clears combat status
  let gRem := (quiet gBlk).removeFromCombat (gBlk.object! bMe.id)
    (cause := some (.oneShotEffect (some ⟨79⟩) none (some me)))
  let bAfterRem := gRem.object! bMe.id
  let bOppAfterRem := gRem.object! bOpp.id
  -- 5. Entering attacking (default defendingPlayer vs planeswalker target via Sneak / tokens)
  let gEnter0 := insertObject (quiet g0) bear me (.graveyard me)
  let gyBearId := (gEnter0.objects.filter (fun o => o.name == bear.name && o.zone == .graveyard me))[0]!.id
  let (gEnterDefault, enteredDefId) := gEnter0.putOntoBattlefield gyBearId me (attacking := true)
    (cause := some (.oneShotEffect (some ⟨80⟩) none (some me)))
  let enteredDefMovedTarget := gEnterDefault.events.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield _ _ _ _)) =>
      if after.id == some enteredDefId then after.attackingTarget else none
    | _ => none)
  let enteredDefBecameTarget := gEnterDefault.events.findSome? (fun e =>
    match e.change with
    | .rules (.combat (.becameAttacking c tgt)) =>
      if c.id == some enteredDefId then some tgt else none
    | _ => none)
  let gSneak0 :=
    let g := (quiet g0).record (GameEvent.becameAttacking g0.turnNumber (g0.snapshot hMe) (.planeswalker pwOpp.id)
      (cause := .oneShotEffect (some ⟨81⟩) none (some me)))
    let g := insertObject g bear me .stack (some me) {}
    let spId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    (g.record (GameEvent.stepBegan g.turnNumber .declareBlockers g.activePlayer)).change (.pending .none)
  let sneakSpellId := gSneak0.stack.back!.objectId
  let gSneak1 :=
    match gSneak0.paySneak me sneakSpellId hMe.id with
    | .ok g => g.resolveTop
    | .error _ => gSneak0
  let sneakEntered? := gSneak1.battlefield.find? (fun o =>
    o.name == bear.name && gSneak1.controlledBy o me && o.id != bMe.id)
  let gTokPw := (quiet g0).createKindTokens me .spirit 1 (tapped := true)
    (attacking := true) (attackingTarget := some (.planeswalker pwOpp.id))
    (cause := some (.oneShotEffect (some ⟨82⟩) none (some me)))
  let tokPw? := gTokPw.battlefield.find? (·.printed.isToken)
  -- Andúril (ruling 181): when multiple legal attack targets exist (opp and pwOpp),
  -- each Spirit token is asked separately before entering and may attack a different target.
  let gAnduril0 := (quiet g0).createAndMarkTokensAttacking me .spirit 2 true true (some hMe.id)
  let gAnduril1 :=
    match gAnduril0.apply me (.chooseMode 1) with
    | .ok g1 => g1
    | .error _ => gAnduril0
  let gAnduril2 :=
    match gAnduril1.apply me (.chooseMode 0) with
    | .ok g2 => g2
    | .error _ => gAnduril1
  let andurilSpirits := gAnduril2.battlefield.filter (·.printed.isToken)
  let andurilCreatedTargets := gAnduril2.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.created obj _)) => some (obj.attacking, obj.attackingTarget, e.batch)
    | _ => none)
  let andurilBecameTargets := gAnduril2.events.filterMap (fun e =>
    match e.change with
    | .rules (.combat (.becameAttacking _ tgt)) => some (tgt, e.batch)
    | _ => none)
  -- Grim Reaper / returnFromGyTappedAttackingFinality (CR 508.4): asks before entering when multiple targets exist
  let gReaper0 := insertObject (quiet g0) bear me (.graveyard me)
  let reaperGyId := (gReaper0.objects.filter (fun o => o.name == bear.name && o.zone == .graveyard me))[0]!.id
  let gReaper1 := gReaper0.returnFromGyTappedAttackingFinality me reaperGyId
  let gReaper2 :=
    match gReaper1.apply me (.chooseMode 1) with
    | .ok g => g
    | .error _ => gReaper1
  let reaperBear? := gReaper2.battlefield.find? (fun o =>
    o.name == bear.name && gReaper2.controlledBy o me && o.id != bMe.id)
  let reaperMovedTarget := gReaper2.events.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) => after.attackingTarget
    | _ => none)
  hAfterBecame.status.attacking &&
    hAfterBecame.status.attackingTarget == some (AttackTarget.planeswalker pwOpp.id) &&
    !gBecame.declaredAsAttackerThisTurn hAfterBecame.id &&
    gBecame.defendingPlayerOf hAfterBecame == opp &&
    becameEvents.size == 1 &&
    gBecame.waitingTriggers.isEmpty &&
    bAfterAtk.status.attacking &&
    bAfterAtk.status.attackingTarget == some (AttackTarget.player opp) &&
    gAtk.declaredAsAttackerThisTurn bAfterAtk.id &&
    atkCombatAndTap.size == 2 &&
    atkCombatAndTap[0]!.batch == atkCombatAndTap[1]!.batch &&
    atkCombatAndTap[0]!.cause? == some (.turnBased .declareAttackers) &&
    !gAtk.stack.isEmpty &&
    hasBlockersDeclared &&
    hasBecameBlocked &&
    hasRemainedUnblocked &&
    (gBlk.object! bMe.id).status.blocked &&
    (gBlk.object! bOpp.id).status.blocking == #[bMe.id] &&
    !bAfterRem.status.attacking &&
    bAfterRem.status.attackingTarget.isNone &&
    !bAfterRem.status.blocked &&
    !bOppAfterRem.status.blocking.isEmpty &&
    (gRem.creaturesBlockedBy bOppAfterRem).isEmpty &&
    (gRem.blockersOf bMe.id).isEmpty &&
    (gEnterDefault.object! enteredDefId).status.attackingTarget == some (AttackTarget.player gEnterDefault.defendingPlayer) &&
    enteredDefMovedTarget == some (AttackTarget.player gEnterDefault.defendingPlayer) &&
    enteredDefBecameTarget == some (AttackTarget.player gEnterDefault.defendingPlayer) &&
    (sneakEntered?.map (·.status.attackingTarget)) == some (some (AttackTarget.planeswalker pwOpp.id)) &&
    (tokPw?.map (·.status.attackingTarget)) == some (some (AttackTarget.planeswalker pwOpp.id)) &&
    !(gAnduril0.battlefield.any (·.printed.isToken)) &&
    !(gAnduril1.battlefield.any (·.printed.isToken)) &&
    andurilSpirits.size == 2 &&
    andurilSpirits[0]!.status.attackingTarget == some (AttackTarget.planeswalker pwOpp.id) &&
    andurilSpirits[1]!.status.attackingTarget == some (AttackTarget.player opp) &&
    andurilCreatedTargets.size == 2 &&
    andurilBecameTargets.size == 2 &&
    andurilCreatedTargets[0]!.1 &&
    andurilCreatedTargets[0]!.2.1 == some (AttackTarget.planeswalker pwOpp.id) &&
    andurilCreatedTargets[1]!.1 &&
    andurilCreatedTargets[1]!.2.1 == some (AttackTarget.player opp) &&
    andurilCreatedTargets[0]!.2.2 == andurilBecameTargets[0]!.2 &&
    andurilCreatedTargets[0]!.2.2 == andurilCreatedTargets[1]!.2.2 &&
    andurilCreatedTargets[0]!.2.2 == andurilBecameTargets[1]!.2 &&
    (gReaper1.object! reaperGyId).zone == .graveyard me &&
    (reaperBear?.map (·.status.attackingTarget)) == some (some (AttackTarget.planeswalker pwOpp.id)) &&
    reaperMovedTarget == some (AttackTarget.planeswalker pwOpp.id) &&
    allRulesEventsClassified gBecame &&
    allRulesEventsClassified gAtk &&
    allRulesEventsClassified gBlk &&
    allRulesEventsClassified gRem &&
    allRulesEventsClassified gEnterDefault &&
    allRulesEventsClassified gSneak1 &&
    allRulesEventsClassified gTokPw &&
    allRulesEventsClassified gAnduril2 &&
    allRulesEventsClassified gReaper2

/- Phase 5.3 isolation: `CastEvent` (`proposed`, `announced`, `targeted`,
`spellCast`, `abilityActivated`), `TriggerQueueEvent.putOnStack`,
`StackObjectEvent` (`copied`, `removedOnResolution`), and `GameEvent.landsPlayed`
via `ZoneEvent.moved` (`verb == .playLand`). Verifies that `applyStackObjectEvent`
copies `StackEntry` decisions (`targets`, `targetsAnnounced`, `chosenMode`,
`extraModes`, `dividedDamage`), `GameObject` stack/cast/adventure fields
(`chosenX`, `kicked`, `teamworkPaid`, `sneakPaid`, `sneakAttackWhom`,
`giftPromisedTo`, `adventurerCard`, `abilityEffect`, `triggeredAbility`,
`sourceId`), and `lastKnownPower` / `lastKnownToughness`. -/
#guard
  -- 1. Land play re-pointed at ZoneEvent.moved (.playLand) and recordLandPlayed helper
  let gLand0 := quiet afterDraw
  let gLand1 := gLand0.recordLandPlayed me
  let landMovedEvents := gLand1.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.outside _) (.outside _) .playLand (some p) _ _)) =>
      p == me && e.cause? == some (.specialAction .playLand me)
    | _ => false)
  -- 2. CastEvent milestones via applyCastEvent
  let testModalSpell : CardDef :=
    { name := "Test Modal X Bolt"
      manaCost := { symbols := #[.x, .colored .red] }
      types := #[.instant]
      chooseOneOrBoth := true
      kicker := some (ManaCost.ofGeneric 1)
      giftTreasure := true
      spellModes := #[.dealDamage 2, .gainLife 2] }
  let gCast0 := insertObject (quiet afterDraw) testModalSpell me .stack (some me)
    (adventurerCard := some bear)
  let spId := (gCast0.objects.filter (·.name == "Test Modal X Bolt"))[0]!.id
  let gCast0 := gCast0.putStackEntry me spId
  let gCast1 := gCast0.record (GameEvent.proposed gCast0.turnNumber spId me (.graveyard me) (.alternative "flashback"))
  let gCast2 := gCast1.record (GameEvent.announced gCast1.turnNumber spId
    (modes := #[0, 1]) (x := some 3) (costs := #[.kicker, .gift opp, .teamwork #[⟨1⟩, ⟨2⟩]]))
  let gCast3 := gCast2.record (GameEvent.targeted gCast2.turnNumber spId
    #[Target.player opp] (division := #[2]))
  let gCast4 := gCast3.record (GameEvent.spellCast gCast3.turnNumber me
    (gCast3.snapshot (gCast3.object! spId)) (.graveyard me))
  let spObj := gCast4.object! spId
  let spEntry := (gCast4.stackEntry? spId).getD { objectId := spId, controller := me, targets := #[] }
  -- 3. StackObjectEvent.copied copies StackEntry decisions and GameObject fields across stack copiers
  let gCast4 := gCast4.record (GameEvent.announced gCast4.turnNumber spId
    (costs := #[.sneak ⟨99⟩ (some (.player opp))])
    (cause := some (.costPayment .returnToHand me (some spId))))
  let gCast4 := gCast4.setStackEntryLastKnown spId
    (lastKnownPower := some 5) (lastKnownToughness := some 6)
  let gCast4 := gCast4.createEffect (.exileInstantSorceryInstead spId)
      (cause := some (.oneShotEffect (some ⟨86⟩) none (some me)))
  let gCopy1 := gCast4.copyStackSpell (gCast4.object! spId) me
  let copy1Entry := gCopy1.stack.back!
  let copy1Obj := gCopy1.object! copy1Entry.objectId
  let trigSpecId : ObjectId := ⟨gCopy1.nextObjectId⟩
  let gTrigSpec := gCopy1.record (GameEvent.triggerPutOnStack gCopy1.turnNumber trigSpecId
    (gCopy1.snapshot (gCopy1.object! spId)) me
    (spec := {
      reflexiveResolution := some (.draw (.fixed 2) .you)
      fraCauseId := some ⟨71⟩
      fraCauseController := some opp
      fraCausePower := some 4
      fraCauseStatus := some { counters := #[(.plusOnePlusOne, 2)] }
      lastKnownPower := some 5
      lastKnownToughness := some 6 }))
  let gCopyTrig := gTrigSpec.copyStackSpell (gTrigSpec.object! trigSpecId) me
  let copyTrigObj := gCopyTrig.object! gCopyTrig.stack.back!.objectId
  -- Also test Loki and Way of the Cryomancer delayed spell-copy triggers
  let cryoCause : EventCause := .oneShotEffect (some ⟨87⟩) none (some me)
  let lokiCause : EventCause := .oneShotEffect (some ⟨88⟩) (some ⟨70⟩) (some me)
  let gCryoLoki0 :=
    let g := gCast4.registerDelayedTrigger
      { controller := me, source := none, kind := .copyNextInstantSorceryThisTurn, cause := cryoCause }
    g.registerDelayedTrigger
      { controller := me, source := none, kind := .lokiCopyNextInstantSorceryThisTurn (some ⟨70⟩) 10, cause := lokiCause }
  let gCryoLokiCast := gCryoLoki0.becomeCast me (gCryoLoki0.object! spId)
  let gCryoLokiStacked :=
    if gCryoLokiCast.pending != .none then applyIdle gCryoLokiCast
    else applyIdle (gCryoLokiCast.receivePriority me)
  let resolveCopyTrig (g : Game) : Game :=
    let g := g.resolveTop
    if g.pending != .none then applyIdle g else g
  let gCryoLoki := resolveCopyTrig (resolveCopyTrig (resolveCopyTrig gCryoLokiStacked))
  let copiedEvents := gCryoLoki.events.filterMap (fun e =>
    match e with
    | .rules _ (.stackObject (.copied orig copy ctrl)) c _ => some (orig, copy, ctrl, c)
    | _ => none)
  -- 4. TriggerQueueEvent.putOnStack and StackObjectEvent.removedOnResolution (CR 608.2b)
  let gTrig0 := addPermanent (quiet afterDraw) bear opp opp
  let oppBear := (gTrig0.battlefield.filter (fun o => o.name == bear.name && gTrig0.controlledBy o opp))[0]!
  let trigAb := TriggeredAbility.fra .enter "When this enters, destroy target creature an opponent controls." (.destroy (.target .creature)) (spec := .oppCreature)
  let gTrigPut := gTrig0.putTriggeredAbilityOnStack me (gTrig0.object! oppBear.id) trigAb "enters"
  let gTrig1 := gTrigPut.setStackEntryTargets gTrigPut.stack.back!.objectId #[Target.permanent oppBear.id]
  let hasTrigPutOnStack := gTrig1.events.any (fun e =>
    match e.change with
    | .rules (.triggerQueue (.putOnStack stackId _ ctrl _)) =>
      ctrl == me && gTrig1.stack.any (·.objectId == stackId) &&
        e.cause? == some (.gameRule .triggeredAbility)
    | _ => false)
  let (gTrig2, _) := (quiet gTrig1).move oppBear.id (.graveyard opp) (verb := some .destroy)
    (cause := some (.oneShotEffect (some ⟨89⟩) none (some me)))
  let gTrig3 := gTrig2.resolveTop
  let hasRemovedOnResolution := gTrig3.events.any (fun e =>
    match e.change with
    | .rules (.stackObject (.removedOnResolution _)) =>
      e.cause? == some (.gameRule .abilityFinishedResolving)
    | _ => false)
  -- Spell fizzle on resolution records .instantOrSorceryFinishedResolving cause
  let gFizzle0 := addPermanent (quiet afterDraw) bear opp opp
  let fizzleBear := (gFizzle0.battlefield.filter (fun o => o.name == bear.name && gFizzle0.controlledBy o opp))[0]!
  let gFizzle0 := insertObject gFizzle0 lightningBolt me .stack (some me) {}
  let fizzleSpId := (gFizzle0.objects.filter (·.name == lightningBolt.name))[0]!.id
  let gFizzle0 := (gFizzle0.putStackEntry me fizzleSpId).setStackEntryTargets fizzleSpId #[Target.permanent fizzleBear.id]
  let (gFizzle1, _) := gFizzle0.move fizzleBear.id (.graveyard opp) (verb := some .destroy)
    (cause := some (.oneShotEffect (some ⟨90⟩) none (some me)))
  let gFizzle2 := (quiet gFizzle1).resolveTop
  let hasSpellRemovedOnResolution := gFizzle2.events.any (fun e =>
    match e.change with
    | .rules (.stackObject (.removedOnResolution _)) =>
      e.cause? == some (.gameRule .instantOrSorceryFinishedResolving)
    | _ => false)
  gLand1.loggedLandsPlayed me == 1 &&
    landMovedEvents.size == 1 &&
    !(gLand1.events.any GameEvent.enteredBattlefield) &&
    gCast4.castFromGraveyard spObj.id &&
    gCast4.wasCast spObj.id &&
    spObj.chosenX == some 3 &&
    gCast4.wasKicked spObj.id &&
    gCast4.giftPromisedTo? spObj.id == some opp &&
    gCast4.teamworkPaid spObj.id &&
    spEntry.chosenMode == some 0 &&
    spEntry.extraModes == #[1] &&
    spEntry.targets == #[Target.player opp] &&
    spEntry.dividedDamage == #[2] &&
    spEntry.targetsAnnounced &&
    copy1Obj.isCopy &&
    !gCopy1.wasCast copy1Obj.id &&
    !gCopy1.castFromGraveyard copy1Obj.id &&
    !gCopy1.castFromHand copy1Obj.id &&
    !gCopy1.exileInstantSorceryInstead copy1Obj &&
    !gCopy1.treasureManaSpent copy1Obj.id &&
    !gCopy1.isPreparedSpell copy1Obj.id &&
    (gCopy1.boastExiledOf copy1Obj.id).isEmpty &&
    copy1Obj.chosenX == some 3 &&
    gCopy1.wasKicked copy1Obj.id &&
    gCopy1.giftPromisedTo? copy1Obj.id == some opp &&
    gCopy1.teamworkPaid copy1Obj.id &&
    gCopy1.sneakPaid copy1Obj.id &&
    gCopy1.sneakAttackWhom? copy1Obj.id == some opp &&
    gCopy1.sneakAttackTarget? copy1Obj.id == some (.player opp) &&
    copy1Obj.adventurerCard == some bear &&
    copyTrigObj.reflexiveResolution == some (.draw (.fixed 2) .you) &&
    copyTrigObj.fraCauseId == some ⟨71⟩ &&
    copyTrigObj.fraCauseController == some opp &&
    copyTrigObj.fraCausePower == some 4 &&
    copyTrigObj.fraCauseStatus == some { counters := #[(.plusOnePlusOne, 2)] } &&
    gCopyTrig.lastKnownPowerOf? copyTrigObj.id == some 5 &&
    gCopyTrig.lastKnownToughnessOf? copyTrigObj.id == some 6 &&
    gCopy1.lastKnownPowerOf? copy1Obj.id == some 5 &&
    gCopy1.lastKnownToughnessOf? copy1Obj.id == some 6 &&
    copy1Entry.chosenMode == some 0 &&
    copy1Entry.extraModes == #[1] &&
    copy1Entry.targets == #[Target.player opp] &&
    copy1Entry.dividedDamage == #[2] &&
    copy1Entry.targetsAnnounced &&
    copiedEvents.size == 2 &&
    copiedEvents.all (fun (orig, _, ctrl, _) => orig == spId && ctrl == me) &&
    copiedEvents.any (fun (_, _, _, c) => c == cryoCause) &&
    copiedEvents.any (fun (_, _, _, c) => c == lokiCause) &&
    hasTrigPutOnStack &&
    hasRemovedOnResolution &&
    hasSpellRemovedOnResolution &&
    allRulesEventsClassified gLand1 &&
    allRulesEventsClassified gCast4 &&
    allRulesEventsClassified gCopy1 &&
    allRulesEventsClassified gCryoLoki &&
    allRulesEventsClassified gTrig1 &&
    allRulesEventsClassified gTrig3 &&
    allRulesEventsClassified gFizzle2

/- Phase 6: `matchTriggers (pre : GameSnapshot) (post : Game) (batch : Array GameEvent)`
evaluates all triggers at outermost batch close, covers CR 603.10a–f look-back
via `pre`, records `TriggerQueueEvent.triggered`
with `cause := .gameRule .triggeredAbility`, and queries once-each-turn
triggers from the event log instead of `Status.firedOnceEachTurn`. -/
#guard
  -- 1. Simultaneous deaths (CR 603.10a): two creatures with "whenever another
  --    creature you control dies" dying in the same batch both see each other
  --    on `pre` and both trigger.
  let deathWatcherAb : TriggeredAbility :=
    .triggered (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
      { resolution := .gainLife (.fixed 1), phrase := "You gain 1 life" }
      {}
  let deathWatcherDef : CardDef :=
    { bear with
      name := "Simultaneous Watcher"
      triggeredAbilities := #[deathWatcherAb] }
  let gSim0 :=
    addPermanent (addPermanent (quiet afterDraw) deathWatcherDef me me) deathWatcherDef me me
  let watchers := gSim0.battlefield.filter (·.name == "Simultaneous Watcher")
  let w1 := watchers[0]!
  let w2 := watchers[1]!
  let simCause : EventCause := .oneShotEffect (some ⟨90⟩) none (some me)
  let gSim1 :=
    gSim0.withBatch (some simCause) fun g =>
      let g := g.moveToOwnerGraveyard w1 "w1 dies" (verb := some .destroy) (cause := some simCause)
      g.moveToOwnerGraveyard w2 "w2 dies" (verb := some .destroy) (cause := some simCause)
  let simTrigSources := gSim1.waitingTriggers.map (·.source.id)
  let simTrigEvents := gSim1.events.filterMap (fun e =>
    match e with
    | .rules _ (.triggerQueue (.triggered src ctrl ab origin)) c b =>
      some (src.id, ctrl, ab, origin, c, b)
    | _ => none)
  let simDeathsOk :=
    simTrigSources.size == 2 &&
    simTrigSources.contains w1.id &&
    simTrigSources.contains w2.id &&
    simTrigEvents.size == 2 &&
    simTrigEvents.all (fun (_, ctrl, ab, origin, cause, bid) =>
      ctrl == me && ab == deathWatcherAb && origin == bid &&
        cause == .gameRule .triggeredAbility)
  -- 3. Phasing out (CR 603.10b / 702.26b / 702.26d): phasing out emits a
  --    look-back `phasedOut` event, does not fire `.leaving` triggers, and a
  --    watcher that phases out in the same simultaneous batch as a dying
  --    creature still sees the death in `pre`.
  let leaveWatcherAb : TriggeredAbility :=
    .triggered .leaving
      { resolution := .gainLife (.fixed 2), phrase := "You gain 2 life" }
      {}
  let phaserDef : CardDef :=
    { bear with
      name := "Phasing Watcher"
      triggeredAbilities := #[leaveWatcherAb, deathWatcherAb] }
  let gPhase0 :=
    addPermanent (addPermanent (quiet afterDraw) phaserDef me me) bear me me
  let phaser := (gPhase0.battlefield.filter (·.name == "Phasing Watcher"))[0]!
  let victim := (gPhase0.battlefield.filter (·.name == bear.name))[0]!
  let phaseCause : EventCause := .oneShotEffect (some ⟨91⟩) none (some me)
  let gPhaseOnly := gPhase0.phaseOut phaser (cause := some phaseCause)
  let phaseOutNoLeaveOk :=
    gPhaseOnly.waitingTriggers.isEmpty &&
    gPhaseOnly.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut snap false)) =>
        snap.id == some phaser.id
      | _ => false)
  let gPhaseAndDie :=
    gPhase0.withBatch (some (.oneShotEffect (some ⟨91⟩) none (some me))) fun g =>
      let g := g.phaseOut phaser
      g.moveToOwnerGraveyard victim "Bear dies" (verb := some .destroy)
        (cause := some (.oneShotEffect (some ⟨91⟩) none (some me)))
  let phaseLookBackOk :=
    gPhaseAndDie.waitingTriggers.size == 1 &&
    gPhaseAndDie.waitingTriggers[0]!.source.id == phaser.id &&
    gPhaseAndDie.waitingTriggers[0]!.ability == deathWatcherAb
  -- 4. Once-each-turn triggers are tracked via `TriggerQueueEvent.triggered`
  --    in `g.events` (`g.loggedTriggeredThisTurn`) rather than `Status`.
  let onceAb : TriggeredAbility :=
    .triggered .youGainLife
      { resolution := .scry 1, phrase := "Scry 1" }
      { onceEachTurn := true }
  let onceDef : CardDef :=
    { bear with
      name := "Once Life Watcher"
      triggeredAbilities := #[onceAb] }
  let gOnce0 := addPermanent (quiet afterDraw) onceDef me me
  let onceObj := (gOnce0.battlefield.filter (·.name == "Once Life Watcher"))[0]!
  let gOnce1 := gOnce0.gainLife me 1 (cause := some (.oneShotEffect (some ⟨92⟩) none (some me)))
  let gOnce2 := gOnce1.gainLife me 1 (cause := some (.oneShotEffect (some ⟨93⟩) none (some me)))
  let gOnceNextTurn :=
    (gOnce2.record (GameEvent.turnBegan (gOnce2.turnNumber + 1) me)).gainLife me 1
      (cause := some (.oneShotEffect (some ⟨94⟩) none (some me)))
  let onceEachTurnOk :=
    gOnce1.loggedTriggeredThisTurn onceObj.id onceAb &&
    gOnce1.waitingTriggers.size == 1 &&
    gOnce2.waitingTriggers.size == 1 &&
    gOnceNextTurn.waitingTriggers.size == 2
  -- 5. Simultaneous batch damage to an attacking Hulk increments
  --    `enrageGrantsAdditionalCombat` once per batch, and `sourceDealtDamage`
  --    sums damage across packets/events in the batch before replicating
  --    `extraTriggerCopies` across distinct abilities.
  let hulkEnrageAb : TriggeredAbility :=
    .triggered .sourceDealtDamage (Effect.ofTrigger (.watch .hulk)) {}
  let hulkDef : CardDef :=
    { bear with
      name := "Test Hulk"
      power := some 6
      toughness := some 6
      triggeredAbilities := #[hulkEnrageAb] }
  let gHulk0 := addPermanent (quiet afterDraw) hulkDef me me
  let hulk0 := (gHulk0.battlefield.filter (·.name == "Test Hulk"))[0]!
  let gHulk0 := gHulk0.markAttacking hulk0.id
  let hulkCause : EventCause := .oneShotEffect (some ⟨95⟩) none (some me)
  let gHulkBatch :=
    gHulk0.withBatch (some hulkCause) fun g =>
      let h := g.object! hulk0.id
      let g := g.dealDamageToPermanent h 1 (source := some (g.snapshot h)) (cause := some hulkCause)
      let h := g.object! hulk0.id
      g.dealDamageToPermanent h 2 (source := some (g.snapshot h)) (cause := some hulkCause)
  let hulkBatchOk :=
    gHulkBatch.waitingTriggers.size == 1 &&
    gHulkBatch.waitingTriggers[0]!.lastKnownPower == some 3
  let dmgAb1 : TriggeredAbility :=
    .triggered .sourceDealtDamage
      { resolution := .gainLife (.fixed 1), phrase := "You gain 1 life" }
      {}
  let dmgAb2 : TriggeredAbility :=
    .triggered .sourceDealtDamage
      { resolution := .scry 1, phrase := "Scry 1" }
      {}
  let dmgWatcherDef : CardDef :=
    { bear with
      name := "Dual Damage Watcher"
      triggeredAbilities := #[dmgAb1, dmgAb2] }
  let doublerDef : CardDef :=
    { bear with
      name := "Trigger Doubler"
      staticAbilities := #[.extraTriggerAnotherYouControl #[] #[.creature]] }
  let gDmg0 :=
    addPermanent (addPermanent (quiet afterDraw) dmgWatcherDef me me) doublerDef me me
  let dmgWatcher := (gDmg0.battlefield.filter (·.name == "Dual Damage Watcher"))[0]!
  let dmgCause : EventCause := .oneShotEffect (some ⟨96⟩) none (some me)
  let gDmgBatch :=
    gDmg0.withBatch (some dmgCause) fun g =>
      let w := g.object! dmgWatcher.id
      let g := g.dealDamageToPermanent w 1 (source := some (g.snapshot w)) (cause := some dmgCause)
      let w := g.object! dmgWatcher.id
      g.dealDamageToPermanent w 1 (source := some (g.snapshot w)) (cause := some dmgCause)
  let dmgTrigEvents := gDmgBatch.events.filter (fun e =>
    match e.change with
    | .rules (.triggerQueue (.triggered ..)) => true
    | _ => false)
  let dmgBatchCopiesOk :=
    gDmgBatch.waitingTriggers.size == 4 &&
    (gDmgBatch.waitingTriggers.filter (·.ability == dmgAb1)).size == 2 &&
    (gDmgBatch.waitingTriggers.filter (·.ability == dmgAb2)).size == 2 &&
    gDmgBatch.waitingTriggers.all (·.lastKnownPower == some 2) &&
    dmgTrigEvents.size == 4
  simDeathsOk &&
    phaseOutNoLeaveOk &&
    phaseLookBackOk &&
    onceEachTurnOk &&
    hulkBatchOk &&
    dmgBatchCopiesOk &&
    allRulesEventsClassified gSim1 &&
    allRulesEventsClassified gPhaseOnly &&
    allRulesEventsClassified gPhaseAndDie &&
    allRulesEventsClassified gHulkBatch &&
    allRulesEventsClassified gDmgBatch

/- Phase 7 isolation (CR 614.5): each `ReplacementId` in `applied` applies at
most once to an event or any modified event that replaced it, even when
multiple replacement specs remain structurally applicable after the first
modification or share a `ReplacementId`. -/
#guard
  let gTerm0 := addPermanent (quiet afterDraw) bear me me
  let bTerm := (gTerm0.battlefield.filter (·.name == "Event Bear"))[0]!
  let idAddCtr : ReplacementId := { kind := .addCountersPut, object := some bTerm.id }
  let idMulCtr : ReplacementId := { kind := .multiplyCountersPut, object := some bTerm.id }
  let repDupA : ReplacementSpec :=
    { id := idAddCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some bTerm.id) (some .plusOnePlusOne) (add := 1) (mult := 1) }
  let repDupB : ReplacementSpec :=
    { id := idAddCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some bTerm.id) (some .plusOnePlusOne) (add := 10) (mult := 1) }
  let repSecond : ReplacementSpec :=
    { id := idMulCtr, source := some bTerm.id, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some bTerm.id) (some .plusOnePlusOne) (add := 0) (mult := 2) }
  let gTerm1 :=
    ((gTerm0.createEffect (.replacement repDupA)).createEffect
      (.replacement repDupB)).createEffect (.replacement repSecond)
  let baseCause : EventCause := .oneShotEffect (some ⟨701⟩) none (some me)
  let gTermPaused :=
    (quiet gTerm1).addPlusOnePlusOneTo (gTerm1.object! bTerm.id) 2 (cause := some baseCause)
  let gTerm2 :=
    ((quiet gTermPaused).apply me (.chooseReplacement idAddCtr)).toOption.getD gTermPaused
  -- `idAddCtr` applies once (2 -> 3), the duplicate `idAddCtr` is skipped by CR 614.5,
  -- and `idMulCtr` applies once (3 -> 6), then the loop terminates.
  let termCounterEvents := gTerm2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .plusOnePlusOne (.put n) _)) => n == 6
    | _ => false)
  (gTerm2.object! bTerm.id).status.plusOnePlusOne == 6 &&
    termCounterEvents.size == 1 &&
    termCounterEvents[0]!.cause? ==
      some (.replaced idMulCtr (.replaced idAddCtr baseCause)) &&
    allRulesEventsClassified gTerm2

/- Phase 7 isolation (CR 614.6): a replaced event never happens (is never
recorded in `g.events`), so abilities watching the replaced event do not
trigger, and the modified event carries `EventCause.replaced`. -/
#guard
  -- 2a. Death replaced by finality counter exile (CR 122.1h / 614.6).
  let diesWatcherAb : TriggeredAbility :=
    .triggered .dies
      { resolution := .gainLife (.fixed 5), phrase := "You gain 5 life" }
      {}
  let finalityBearDef : CardDef :=
    { bear with
      name := "Finality Bear"
      triggeredAbilities := #[diesWatcherAb] }
  let gFin0 := addPermanent (quiet afterDraw) finalityBearDef me me
  let finBear0 := (gFin0.battlefield.filter (·.name == "Finality Bear"))[0]!
  let gFin1 := gFin0.recordPutCounters finBear0.id .finality 1 (some me)
    (cause := some (.oneShotEffect (some ⟨702⟩) none (some me)))
  let finDeathCause : EventCause := .oneShotEffect (some ⟨703⟩) none (some me)
  let gFin2 :=
    (quiet gFin1).moveToOwnerGraveyard (gFin1.object! finBear0.id) "dies"
      (verb := some .destroy) (cause := some finDeathCause)
  let finHasGyMove := gFin2.events.any (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield (.graveyard _) ..)) => true
    | _ => false)
  let finExileMoves := gFin2.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved before _ .battlefield .exile .destroy _ _ _)) =>
      before.id == some finBear0.id
    | _ => false)
  let finalityId : ReplacementId := { kind := .finalityCounterExile, object := some finBear0.id }
  -- 2b. Destruction replaced by shield counter removal (CR 122.1c / 614.6).
  let gShd0 := addPermanent (quiet afterDraw) bear me me
  let shdBear0 := (gShd0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gShd1 := gShd0.recordPutCounters shdBear0.id .shield 1 (some me)
    (cause := some (.oneShotEffect (some ⟨704⟩) none (some me)))
  let shdDestroyCause : EventCause := .oneShotEffect (some ⟨705⟩) none (some me)
  let gShd2 :=
    (quiet gShd1).destroyPermanent (gShd1.object! shdBear0.id) (cause := some shdDestroyCause)
  let shdId : ReplacementId := { kind := .shieldCounterDestroy, object := some shdBear0.id }
  let shdRemovedEvents := gShd2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object o) .shield (.removed 1) _)) =>
      o.id == some shdBear0.id
    | _ => false)
  -- 2c. Untap during untap step replaced by stun counter removal (CR 122.1d / 614.6).
  let gStun0 := addPermanent (quiet afterDraw) bear me me
  let stunBear0 := (gStun0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gStun1 :=
    (gStun0.becomeTapped (gStun0.object! stunBear0.id)
      (cause := some (.oneShotEffect (some ⟨706⟩) none (some me)))).recordPutCounters
      stunBear0.id .stun 1 (some me)
      (cause := some (.oneShotEffect (some ⟨707⟩) none (some me)))
  let gStun2 := (quiet gStun1).beginStep .untap
  let stunId : ReplacementId := { kind := .stunCounterUntap, object := some stunBear0.id }
  let stunUntapEvents := gStun2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.untapped o)) => o.id == some stunBear0.id
    | _ => false)
  let stunRemovedEvents := gStun2.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object o) .stun (.removed 1) _)) =>
      o.id == some stunBear0.id
    | _ => false)
  -- 2d. Draw replaced by two draws (`drawTwoExceptFirstDrawStep`, CR 614.11 / 121.2).
  let drawReplaceDef : CardDef :=
    { bear with
      name := "Draw Replacer"
      drawTwoExceptFirstDrawStep := true }
  let gDrw0 := addPermanent (quiet afterDraw) drawReplaceDef me me
  let drwReplacer := (gDrw0.battlefield.filter (·.name == "Draw Replacer"))[0]!
  let drwCause : EventCause := .oneShotEffect (some ⟨708⟩) none (some me)
  let gDrw1 := (quiet gDrw0).draw me 1 (cause := some drwCause)
  let drwRepId : ReplacementId := { kind := .drawTwoExceptFirstDrawStep, object := some drwReplacer.id }
  let drwMoves := gDrw1.events.filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) (.hand _) (.draw _) _ _ _)) => true
    | _ => false)
  -- 2e. Damage prevented by a prevention effect (CR 615.1 / 615.6).
  let gPrev0 := addPermanent (quiet afterDraw) bear me me
  let prevBear := (gPrev0.battlefield.filter (·.name == "Event Bear"))[0]!
  let prevSpec : PreventionSpec :=
    { id := { kind := .preventAllDamageToPermanent, object := some prevBear.id }, source := some prevBear.id, controller := some me,
      affectedPlayer := me, kind := .preventAllDamageToPermanent prevBear.id }
  let gPrev1 := gPrev0.createEffect (.prevention prevSpec)
  let prevCause : EventCause := .oneShotEffect (some ⟨709⟩) none (some me)
  let gPrev2 :=
    (quiet gPrev1).dealDamageToPermanent (gPrev1.object! prevBear.id) 3
      (source := some (gPrev1.snapshot prevBear)) (cause := some prevCause)
  let prevDealtEvents := gPrev2.events.filter (fun e =>
    match e.change with
    | .rules (.damage (.dealt ..)) => true
    | _ => false)
  let prevPreventedEvents := gPrev2.events.filter (fun e =>
    match e.change with
    | .rules (.damage (.prevented _ (.permanent p) 3)) => p.id == prevBear.id
    | _ => false)
  !finHasGyMove &&
    gFin2.waitingTriggers.isEmpty &&
    finExileMoves.size == 1 &&
    finExileMoves[0]!.cause? == some (.replaced finalityId finDeathCause) &&
    gShd2.events.all (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => false
      | _ => true) &&
    (gShd2.object! shdBear0.id).zone == .battlefield &&
    (gShd2.object! shdBear0.id).status.shield == 0 &&
    shdRemovedEvents.size == 1 &&
    shdRemovedEvents[0]!.cause? == some (.replaced shdId shdDestroyCause) &&
    stunUntapEvents.isEmpty &&
    (gStun2.object! stunBear0.id).status.tapped &&
    (gStun2.object! stunBear0.id).status.stun == 0 &&
    stunRemovedEvents.size == 1 &&
    stunRemovedEvents[0]!.cause? == some (.replaced stunId (.turnBased .untapAll)) &&
    drwMoves.size == 2 &&
    drwMoves.all (fun e => e.cause? == some (.replaced drwRepId drwCause)) &&
    prevDealtEvents.isEmpty &&
    prevPreventedEvents.size == 1 &&
    prevPreventedEvents[0]!.cause? == some (.replaced prevSpec.id prevCause) &&
    (gPrev2.object! prevBear.id).status.damage == 0 &&
    allRulesEventsClassified gFin2 &&
    allRulesEventsClassified gShd2 &&
    allRulesEventsClassified gStun2 &&
    allRulesEventsClassified gDrw1 &&
    allRulesEventsClassified gPrev2

/- Phase 7 isolation (CR 616.1a–e): priority ordering (`self` -> `control` ->
`copy` -> `backFaceUp` -> `other`) applies in strict tier order even when
`g.replacementOrder` lists lower-priority tiers first. -/
#guard
  let dfcBackFace : CardDef :=
    { bear with name := "Back Face Bear", power := some 5, toughness := some 5 }
  let dfcFrontDef : CardDef :=
    { bear with
      name := "Front Face Bear"
      otherFace := some dfcBackFace }
  let copyTemplateDef : CardDef :=
    { hero with name := "Template Hero", otherFace := some dfcBackFace }
  let gTier0 :=
    insertObject (quiet afterDraw) dfcFrontDef opp (.hand opp)
  let enterCardId :=
    ((gTier0.player opp).hand.filter (fun id => (gTier0.object! id).name == "Front Face Bear"))[0]!
  let enteredExpectedId : ObjectId := ⟨gTier0.nextObjectId⟩
  let idSelf : ReplacementId :=
    { kind := .entersWithPlusOneCounters, object := some enteredExpectedId }
  let idControl : ReplacementId := { kind := .entersUnderControl }
  let idCopy : ReplacementId := { kind := .entersAsCopy }
  let idBack : ReplacementId := { kind := .entersBackFaceUp }
  let idOther : ReplacementId := { kind := .entersWithExtraCounters }
  let specSelf : ReplacementSpec :=
    { id := idSelf, source := some enteredExpectedId, controller := some opp,
      affectedPlayer := opp, kind := .entersWithCountersSelf enteredExpectedId .plusOnePlusOne 1 }
  let specControl : ReplacementSpec :=
    { id := idControl, source := none, controller := some me,
      affectedPlayer := opp, kind := .entersUnderControl none me }
  let specCopy : ReplacementSpec :=
    { id := idCopy, source := none, controller := some me,
      affectedPlayer := me, kind := .entersAsCopy none copyTemplateDef }
  let specBack : ReplacementSpec :=
    { id := idBack, source := none, controller := some me,
      affectedPlayer := me, kind := .entersBackFaceUp none }
  let specOther : ReplacementSpec :=
    { id := idOther, source := none, controller := some me,
      affectedPlayer := me, kind := .entersWithExtraCounters none .plusOnePlusOne 2 }
  let gTier1 :=
    (((((gTier0.createEffect (.replacement specSelf)).createEffect
        (.replacement specControl)).createEffect
        (.replacement specCopy)).createEffect
        (.replacement specBack)).createEffect
        (.replacement specOther)).change
      (.replacementOrder #[idOther, idBack, idCopy, idControl, idSelf])
  let etbBaseCause : EventCause := .oneShotEffect (some ⟨710⟩) none (some me)
  let enterCandidate : GameObject :=
    { (gTier1.object! enterCardId) with
      id := enteredExpectedId, controller := some opp, defaultController := some opp }
  let etbRes :=
    gTier1.applyEtbReplacements enterCandidate (cause := some etbBaseCause)
  let (gTier2, enteredPermId) :=
    (quiet gTier1).putOntoBattlefield enterCardId opp (cause := some etbBaseCause)
  let enteredPerm := gTier2.object! enteredPermId
  etbRes.applied == #[idControl, idCopy, idBack, idOther, idSelf] &&
    enteredPermId == enteredExpectedId &&
    enteredPerm.controller == some me &&
    enteredPerm.name == "Back Face Bear" &&
    enteredPerm.status.transformed &&
    !enteredPerm.status.tapped &&
    enteredPerm.status.plusOnePlusOne == 3 &&
    etbRes.cause ==
      some (.replaced idSelf
        (.replaced idOther
          (.replaced idBack
            (.replaced idCopy
              (.replaced idControl etbBaseCause))))) &&
    allRulesEventsClassified gTier2

/- Phase 7 isolation (CR 616.1e): player-chosen ordering within tier `616.1e`
(`g.replacementOrder` and `Pending.chooseReplacement` / `Action.chooseReplacement`),
resumption of paused events, non-sticky consumption of `replacementOrder`,
rejection of out-of-band `Action.chooseReplacement`, non-resolving `wrapReplacedCause`
preserving `nextEffectId`, `createAndMarkTokensAttacking` single-pass token
replacements, single-pass `replaceDamage` in `dealDamageFrom` / `dealDamageToPermanent`,
and Arwen + Doc Samson ETB counter replacement. -/
#guard
  let gOrd0 := addPermanent (quiet afterDraw) bear me me
  let ordBear := (gOrd0.battlefield.filter (·.name == "Event Bear"))[0]!
  let idAddDmg : ReplacementId := { kind := .addNoncombatDamage, object := some ordBear.id }
  let idMulDmg : ReplacementId := { kind := .multiplyDamage, object := some ordBear.id }
  let specAddDmg : ReplacementSpec :=
    { id := idAddDmg, source := some ordBear.id, controller := some me,
      affectedPlayer := opp, kind := .addNoncombatDamage (some ordBear.id) 2 }
  let specMulDmg : ReplacementSpec :=
    { id := idMulDmg, source := some ordBear.id, controller := some me,
      affectedPlayer := opp, kind := .multiplyDamage (some ordBear.id) 2 }
  let gOrd1 :=
    (gOrd0.createEffect (.replacement specAddDmg)).createEffect
      (.replacement specMulDmg)
  -- Out-of-band `Action.chooseReplacement` is rejected when no `.chooseReplacement` is pending.
  let outOfBandRejected :=
    match gOrd1.apply opp (.chooseReplacement idAddDmg) with
    | .error _ => true
    | .ok _ => false
  -- Live prompt: dealing 3 noncombat damage with both +2 and *2 active pauses on `.chooseReplacement`.
  let dmgOrdCause : EventCause := .oneShotEffect (some ⟨711⟩) none (some me)
  let gDmgPaused :=
    (quiet gOrd1).dealDamageToPlayer opp 3
      (source := some (gOrd1.object! ordBear.id)) (cause := some dmgOrdCause)
  let pausedPromptOk :=
    gDmgPaused.pending == .chooseReplacement opp #[idAddDmg, idMulDmg] &&
    (gDmgPaused.player opp).life == (gOrd0.player opp).life
  -- Choosing `idAddDmg` first resumes the damage event: (3 + 2) * 2 = 10 damage, and consumes `replacementOrder`.
  let gDmgAddFirst :=
    ((quiet gDmgPaused).apply opp (.chooseReplacement idAddDmg)).toOption.getD gDmgPaused
  -- Choosing `idMulDmg` first resumes the damage event: (3 * 2) + 2 = 8 damage, and consumes `replacementOrder`.
  let gDmgMulFirst :=
    ((quiet gDmgPaused).apply opp (.chooseReplacement idMulDmg)).toOption.getD gDmgPaused
  -- A subsequent damage event on `gDmgAddFirst` prompts again because `replacementOrder` was consumed.
  let gDmgSecondPaused :=
    (quiet gDmgAddFirst).dealDamageToPlayer opp 3
      (source := some (gDmgAddFirst.object! ordBear.id)) (cause := some dmgOrdCause)
  -- Competing graveyard replacements (Finality counter exile vs Head of the Hunt exile + Wolf trigger) prompt `chooseReplacement`.
  let gFinComp0 := addPermanent (addPermanent (quiet afterDraw) bear me me)
    { bear with name := "Head of the Hunt Test", staticAbilities := #[.exileOppDeathCreateWolf] } opp opp
  let finCompBear := (gFinComp0.battlefield.filter (·.name == "Event Bear"))[0]!
  let headSource := (gFinComp0.battlefield.filter (·.name == "Head of the Hunt Test"))[0]!
  let idFinExile : ReplacementId := { kind := .finalityCounterExile, object := some finCompBear.id }
  let idHeadWolf : ReplacementId := { kind := .exileOppDeath, object := some headSource.id }
  let gFinComp1 :=
    gFinComp0.recordPutCounters finCompBear.id .finality 1 (some me)
      (cause := some (.oneShotEffect (some ⟨713⟩) none (some me)))
  let gFinCompPaused :=
    (quiet gFinComp1).moveToOwnerGraveyard (gFinComp1.object! finCompBear.id) "dies"
      (verb := some .destroy) (cause := some (.oneShotEffect (some ⟨714⟩) none (some me)))
  let gFinChoseHead :=
    ((quiet gFinCompPaused).apply me (.chooseReplacement idHeadWolf)).toOption.getD gFinCompPaused
  let gFinChoseExile :=
    ((quiet gFinCompPaused).apply me (.chooseReplacement idFinExile)).toOption.getD gFinCompPaused
  let finChoiceOk :=
    gFinCompPaused.pending == .chooseReplacement me #[idFinExile, idHeadWolf] &&
    gFinChoseHead.objects.any (fun o => o.zone == .exile && o.name == "Event Bear") &&
    (gFinChoseHead.waitingTriggers.size + gFinChoseHead.stack.size) == 1 &&
    gFinChoseExile.objects.any (fun o => o.zone == .exile && o.name == "Event Bear") &&
    (gFinChoseExile.waitingTriggers.size + gFinChoseExile.stack.size) == 0
  -- Non-resolving replacement (`cause := none` outside a resolving spell/ability) does not mint an `EffectId`.
  let effBefore := gOrd1.nextEffectId
  let wrappedNonResolving := gOrd1.wrapReplacedCause idAddDmg none (some me)
  let nonResolvingCauseOk :=
    wrappedNonResolving == some (.replaced idAddDmg (.gameRule .continuousEffect)) &&
    gOrd1.nextEffectId == effBefore
  -- `createAndMarkTokensAttacking` with a token doubler + token-kind replacement applies each once.
  let specDoubleTok : ReplacementSpec :=
    { id := { kind := .multiplyTokenCreation, object := some ordBear.id }, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .multiplyTokenCreation me 2 }
  let specFoodTok : ReplacementSpec :=
    { id := { kind := .artifactTokensBecome, object := some ordBear.id }, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .artifactTokensBecome me foodToken }
  let gAtkTok0 :=
    ((gOrd0.createEffect (.replacement specDoubleTok)).createEffect
      (.replacement specFoodTok)).change (.resolvingAbility (some ordBear.id))
  let gAtkTok1 :=
    (quiet gAtkTok0).createAndMarkTokensAttacking me .treasure 1 false true
  let atkTokFoods := gAtkTok1.battlefield.filter (·.name == foodToken.name)
  let atkTokOk := atkTokFoods.size == 2
  -- Single-pass `replaceDamage` on `dealDamageFrom` and `dealDamageToPermanent` with a shield counter.
  let gShdDmg0 :=
    addPermanent (addPermanent (quiet afterDraw) bear me me)
      { bear with name := "Attacker Bear" } opp opp
  let shdVictim := (gShdDmg0.battlefield.filter (·.name == "Event Bear"))[0]!
  let shdAttacker := (gShdDmg0.battlefield.filter (·.name == "Attacker Bear"))[0]!
  let shdRepId : ReplacementId := { kind := .shieldCounterPreventDamage, object := some shdVictim.id }
  let gShdDmg1 :=
    gShdDmg0.recordPutCounters shdVictim.id .shield 1 (some me)
      (cause := some (.oneShotEffect (some ⟨715⟩) none (some me)))
  let shdDmgCause : EventCause := .oneShotEffect (some ⟨716⟩) none (some opp)
  let gShdFrom :=
    (quiet gShdDmg1).dealDamageFrom "Attacker Bear" (gShdDmg1.object! shdVictim.id) 2
      (source := some (gShdDmg1.object! shdAttacker.id)) (cause := some shdDmgCause)
  let shdFromRemoved := gShdFrom.events.filter (fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object o) .shield (.removed 1) _)) =>
      o.id == some shdVictim.id
    | _ => false)
  let singlePassDamageOk :=
    (gShdFrom.object! shdVictim.id).status.shield == 0 &&
    (gShdFrom.object! shdVictim.id).status.damage == 0 &&
    shdFromRemoved.size == 1 &&
    shdFromRemoved[0]!.cause? == some (.replaced shdRepId shdDmgCause)
  -- Arwen (`othersEnterWithPlusOneEqualToughness := true`) + Doc Samson (`.extraCounterOnPermanents`) ETB counter replacement.
  let samsonDef : CardDef :=
    { bear with name := "Doc Samson Test", staticAbilities := #[.extraCounterOnPermanents] }
  let arwenDef : CardDef :=
    { bear with name := "Arwen Test", toughness := some 2, othersEnterWithPlusOneEqualToughness := true }
  let gArw0 :=
    insertObject
      (addPermanent (addPermanent (quiet afterDraw) samsonDef me me) arwenDef me me)
      { bear with name := "Newcomer Bear" } me (.hand me)
  let newcomerCardId :=
    ((gArw0.player me).hand.filter (fun id => (gArw0.object! id).name == "Newcomer Bear"))[0]!
  let arwCause : EventCause := .oneShotEffect (some ⟨717⟩) none (some me)
  let (gArw1, newcomerPermId) :=
    (quiet gArw0).putOntoBattlefield newcomerCardId me (cause := some arwCause)
  let arwenMovedBagOk := gArw1.events.any (fun e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield _ _ bag _)) =>
      after.id == some newcomerPermId && bag.any (fun (k, c) => k == .plusOnePlusOne && c == 3)
    | _ => false)
  let arwenSamsonOk :=
    (gArw1.object! newcomerPermId).status.plusOnePlusOne == 3 &&
    arwenMovedBagOk
  -- Life gain replacement choice (`+2` vs `*2`) and APNAP tie-breaking.
  let idAddLife : ReplacementId := { kind := .addLifeGain, object := some ordBear.id }
  let idMulLife : ReplacementId := { kind := .multiplyLifeGain, object := some ordBear.id }
  let specAddLife : ReplacementSpec :=
    { id := idAddLife, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .modifyLifeGain me (add := 2) (mult := 1) }
  let specMulLife : ReplacementSpec :=
    { id := idMulLife, source := some ordBear.id, controller := some me,
      affectedPlayer := me, kind := .modifyLifeGain me (add := 0) (mult := 2) }
  let gLife0 :=
    (gOrd0.createEffect (.replacement specAddLife)).createEffect
      (.replacement specMulLife)
  let lifeCause : EventCause := .oneShotEffect (some ⟨712⟩) none (some me)
  let gLifePaused := (quiet gLife0).gainLife me 3 (cause := some lifeCause)
  let gLifeAddFirst :=
    ((quiet gLifePaused).apply me (.chooseReplacement idAddLife)).toOption.getD gLifePaused
  let gLifeMulFirst :=
    ((quiet gLifePaused).apply me (.chooseReplacement idMulLife)).toOption.getD gLifePaused
  let idLifeMe : ReplacementId := { kind := .addLifeGain, player := some me }
  let idLifeOpp : ReplacementId := { kind := .addLifeGain, player := some opp }
  let candMe : ReplacementCandidate :=
    (ReplacementOrPrevention.replacement {
      id := idLifeMe, affectedPlayer := me, kind := .modifyLifeGain me 1 1 }).toCandidate
  let candOpp : ReplacementCandidate :=
    (ReplacementOrPrevention.replacement {
      id := idLifeOpp, affectedPlayer := opp, kind := .modifyLifeGain opp 1 1 }).toCandidate
  let gActiveMe := gOrd0.record (GameEvent.turnBegan gOrd0.turnNumber me)
  let gActiveOpp := gOrd0.record (GameEvent.turnBegan (gOrd0.turnNumber + 1) opp)
  -- Simultaneous graveyard move and SBA sweep resumption across multiple dying creatures.
  let finSetupCause : EventCause := .oneShotEffect (some ⟨718⟩) none (some me)
  let gSim0 := addPermanent gFinComp1 { bear with name := "Sim Dying Two" } me me
  let simC1 := (gSim0.battlefield.filter (·.name == "Event Bear"))[0]!
  let simC2 := (gSim0.battlefield.filter (·.name == "Sim Dying Two"))[0]!
  let gSim0 := gSim0.recordPutCounters simC2.id .finality 1 (some me)
    (cause := some finSetupCause)
  let c1FinId : ReplacementId := { kind := .finalityCounterExile, object := some simC1.id }
  let c2FinId : ReplacementId := { kind := .finalityCounterExile, object := some simC2.id }
  let gSimPaused1 := (quiet gSim0).moveSimultaneousToGraveyard #[simC1.id, simC2.id]
    (cause := some finSetupCause)
  let gSimPaused2 :=
    (gSimPaused1.apply me (.chooseReplacement c1FinId)).toOption.getD gSimPaused1
  let gSimDone :=
    (gSimPaused2.apply me (.chooseReplacement c2FinId)).toOption.getD gSimPaused2
  let simMoveBatches := gSimDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved ..)) => some e.batch
    | _ => none)
  let simMoveOk :=
    gSimPaused1.pending == .chooseReplacement me #[c1FinId, idHeadWolf] &&
    gSimPaused2.pending == .chooseReplacement me #[c2FinId, idHeadWolf] &&
    gSimDone.pending == .none &&
    !gSimDone.battlefield.any (fun o => o.id == simC1.id || o.id == simC2.id) &&
    simMoveBatches.size == 2 && simMoveBatches[0]! == simMoveBatches[1]!
  -- SBA sweep: Creature 1 has lethal damage + Finality + Head of the Hunt; Creature 2 has lethal damage.
  -- Choosing Finality on Creature 1 queues no trigger, and Creature 2 still dies in the same SBA batch.
  let gSba0 :=
    setMarkedDamage (setMarkedDamage gSim0 simC1.id 2) simC2.id 2
  let gSbaPaused := (quiet gSba0).checkSBA
  let gSbaAfter1 :=
    (gSbaPaused.apply me (.chooseReplacement c1FinId)).toOption.getD gSbaPaused
  let gSbaDone :=
    (gSbaAfter1.apply me (.chooseReplacement c2FinId)).toOption.getD gSbaAfter1
  let sbaMoveBatches := gSbaDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved ..)) => some e.batch
    | _ => none)
  let sbaResumeOk :=
    gSbaPaused.pending == .chooseReplacement me #[c1FinId, idHeadWolf] &&
    gSbaAfter1.pending == .chooseReplacement me #[c2FinId, idHeadWolf] &&
    gSbaDone.pending == .none &&
    !gSbaDone.battlefield.any (fun o => o.id == simC1.id || o.id == simC2.id) &&
    sbaMoveBatches.size == 2 && sbaMoveBatches[0]! == sbaMoveBatches[1]!
  -- `fightCreatures` chains the second creature's fight damage after a replacement choice on the first.
  let gFight0 :=
    addPermanent (addPermanent gOrd0 { bear with name := "Fighter A" } me me)
      { bear with name := "Fighter B", toughness := some 10 } opp opp
  let fighterA := (gFight0.battlefield.filter (·.name == "Fighter A"))[0]!
  let fighterB := (gFight0.battlefield.filter (·.name == "Fighter B"))[0]!
  let idFightAdd : ReplacementId := { kind := .addNoncombatDamage, object := some fighterA.id }
  let idFightMul : ReplacementId := { kind := .multiplyDamage, object := some fighterA.id }
  let gFight0 :=
    (gFight0.createEffect (.replacement {
      id := idFightAdd, source := some fighterA.id, controller := some me,
      affectedPlayer := opp, kind := .addNoncombatDamage (some fighterA.id) 2 })
      (cause := some dmgOrdCause)).createEffect
      (.replacement {
        id := idFightMul, source := some fighterA.id, controller := some me,
        affectedPlayer := opp, kind := .multiplyDamage (some fighterA.id) 2 })
      (cause := some dmgOrdCause)
  let gFightPaused := (quiet gFight0).fightCreatures (gFight0.object! fighterA.id)
    (gFight0.object! fighterB.id) (cause := some dmgOrdCause)
  let gFightDone :=
    (gFightPaused.apply opp (.chooseReplacement idFightAdd)).toOption.getD gFightPaused
  let fightBatches := gFightDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.damage (.dealt ..)) => some e.batch
    | _ => none)
  let fightResumeOk :=
    gFightPaused.pending == .chooseReplacement opp #[idFightAdd, idFightMul] &&
    gFightDone.pending == .none &&
    (gFightDone.object! fighterB.id).status.damage == 8 &&
    (gFightDone.object! fighterA.id).status.damage == 2 &&
    fightBatches.size == 2 && fightBatches[0]! == fightBatches[1]!
  -- `finishEnteringAttackCard` stops on a `.counter` mod that opens `.chooseReplacement` before running `afterPermanentEnters`.
  let gEntAtk0 :=
    insertObject gOrd0 { bear with name := "Entering Striker" } me (.hand me)
  let strikerHandId :=
    ((gEntAtk0.player me).hand.filter (fun id => (gEntAtk0.object! id).name == "Entering Striker"))[0]!
  let (gEntAtk0, strikerId) :=
    (quiet gEntAtk0).putOntoBattlefield strikerHandId me (cause := some arwCause)
  let idCtrAdd : ReplacementId := { kind := .addCountersPut, object := some strikerId }
  let idCtrMul : ReplacementId := { kind := .multiplyCountersPut, object := some strikerId }
  let gEntAtk0 :=
    (gEntAtk0.createEffect (.replacement {
      id := idCtrAdd, source := some strikerId, controller := some me,
      affectedPlayer := me, kind := .modifyCountersPut (some strikerId) (some .plusOnePlusOne) (add := 1) (mult := 1) })
      (cause := some arwCause)).createEffect
      (.replacement {
        id := idCtrMul, source := some strikerId, controller := some me,
        affectedPlayer := me, kind := .modifyCountersPut (some strikerId) (some .plusOnePlusOne) (add := 0) (mult := 2) })
      (cause := some arwCause)
  let gEntAtkPaused := gEntAtk0.finishEnteringAttackCard strikerId me "Entering Striker"
    [.counter .plusOnePlusOne 1 false, .counter .shield 1 false] .putOntoBattlefield (cause := some arwCause)
  let gEntAtkDone :=
    (gEntAtkPaused.apply me (.chooseReplacement idCtrAdd)).toOption.getD gEntAtkPaused
  let entAtkOk :=
    gEntAtkPaused.pending == .chooseReplacement me #[idCtrAdd, idCtrMul] &&
    (gEntAtkPaused.object! strikerId).status.shield == 0 &&
    gEntAtkDone.pending == .none &&
    (gEntAtkDone.object! strikerId).status.plusOnePlusOne == 4 &&
    (gEntAtkDone.object! strikerId).status.shield == 1
  -- Draw-step sub-draw pause: a `replaceDraw me 2 false` draws the first card of the draw step,
  -- then the second sub-draw pauses on competing `exceptFirst := true` replacements without restarting the first draw.
  let idDrwAll : ReplacementId := { kind := .replaceDraw, player := some me }
  let idDrwEx2 : ReplacementId := { kind := .drawTwoExceptFirstDrawStep, player := some me }
  let idDrwEx3 : ReplacementId := { kind := .drawThreeExceptFirstDrawStep, player := some me }
  let drwSubCause : EventCause := .oneShotEffect (some ⟨719⟩) none (some me)
  let gDrwSub0 :=
    (((((quiet started).record (GameEvent.turnBegan started.turnNumber me)).record
      (GameEvent.stepBegan started.turnNumber .draw me)).createEffect
      (.replacement {
        id := idDrwAll, source := none, controller := some me,
        affectedPlayer := me, kind := .replaceDraw me 2 false })
      (cause := some drwSubCause)).createEffect
      (.replacement {
        id := idDrwEx2, source := none, controller := some me,
        affectedPlayer := me, kind := .replaceDraw me 2 true })
      (cause := some drwSubCause))
    |>.createEffect
      (.replacement {
        id := idDrwEx3, source := none, controller := some me,
        affectedPlayer := me, kind := .replaceDraw me 3 true })
      (cause := some drwSubCause)
  let handBeforeDrwSub := (gDrwSub0.player me).hand.size
  let gDrwSubPaused := (quiet gDrwSub0).draw me 1
  let gDrwSubDone :=
    (gDrwSubPaused.apply me (.chooseReplacement idDrwEx2)).toOption.getD gDrwSubPaused
  let drwSubResumeOk :=
    gDrwSubPaused.pending == .chooseReplacement me #[idDrwEx2, idDrwEx3] &&
    (gDrwSubPaused.player me).hand.size - handBeforeDrwSub == 1 &&
    gDrwSubDone.pending == .none &&
    (gDrwSubDone.player me).hand.size - handBeforeDrwSub == 7
  -- `commitEnteringAttackItems` pauses on an as-enters `.fraChoice` (`asEntersChooseOddEven`) before putting the second card onto the battlefield, keeping both in one batch.
  let oddEvenDef1 : CardDef := { bear with name := "Parity Striker 1", asEntersChooseOddEven := true }
  let oddEvenDef2 : CardDef := { bear with name := "Parity Striker 2", asEntersChooseOddEven := true }
  let gFraEnt0 :=
    insertObject
      (insertObject gOrd0 oddEvenDef1 me (.hand me))
      oddEvenDef2 me (.hand me)
  let pCard1 := ((gFraEnt0.player me).hand.filter (fun id => (gFraEnt0.object! id).name == "Parity Striker 1"))[0]!
  let pCard2 := ((gFraEnt0.player me).hand.filter (fun id => (gFraEnt0.object! id).name == "Parity Striker 2"))[0]!
  let item1 : EnteringAttackItem :=
    .card pCard1 me me true false #[] [] .putOntoBattlefield #[.player opp]
  let item2 : EnteringAttackItem :=
    .card pCard2 me me true false #[] [] .putOntoBattlefield #[.player opp]
  let gFraEntPaused1 :=
    (quiet gFraEnt0).commitEnteringAttackItems #[(item1, some (.player opp)), (item2, some (.player opp))]
      (cause := some arwCause)
  let gFraEntPaused2 :=
    (gFraEntPaused1.apply me (.chooseMode 0)).toOption.getD gFraEntPaused1
  let entered1Id := ((gFraEntPaused2.battlefield.filter (·.name == "Parity Striker 1"))[0]!).id
  let gFraEntDone :=
    (gFraEntPaused2.apply me (.chooseMode 1)).toOption.getD gFraEntPaused2
  let entered2Id := ((gFraEntDone.battlefield.filter (·.name == "Parity Striker 2"))[0]!).id
  let entAtkFraBatches := gFraEntDone.events.filterMap (fun e =>
    match e.change with
    | .rules (.zone (.moved ..)) => some e.batch
    | _ => none)
  let entAtkFraOk :=
    (match gFraEntPaused1.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => c.object == some entered1Id && c.kind == .asEntersChooseOdd false)
     | _ => false) &&
    !gFraEntPaused1.battlefield.any (·.name == "Parity Striker 1") &&
    (match gFraEntPaused2.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => c.object == some entered2Id && c.kind == .asEntersChooseOdd true)
     | _ => false) &&
    (gFraEntPaused2.object! entered1Id).status.chosenOdd == some false &&
    gFraEntDone.pending == .none &&
    (gFraEntDone.object! entered2Id).status.chosenOdd == some true &&
    entAtkFraBatches.size == 2 && entAtkFraBatches[0]! == entAtkFraBatches[1]!
  -- `dealAssignedCombatDamage` consumes `replacementOrder` per damage packet rather than leaking across blockers (CR 616.1).
  let cbtLifelinkDef : CardDef :=
    { bear with name := "Lifelink Striker", keywords := { lifelink := true } }
  let idCbtMul : ReplacementId := { kind := .multiplyDamage }
  let idCbtLifeAdd : ReplacementId := { kind := .addLifeGain, player := some me }
  let idCbtLifeMul : ReplacementId := { kind := .multiplyLifeGain, player := some me }
  let gCbt0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) cbtLifelinkDef me me)
        { bear with name := "Second Striker" } me me)
      { bear with name := "Shield Blocker" } opp opp
  let cbtAtk1 := (gCbt0.battlefield.filter (·.name == "Lifelink Striker"))[0]!
  let cbtAtk2 := (gCbt0.battlefield.filter (·.name == "Second Striker"))[0]!
  let cbtBlk := (gCbt0.battlefield.filter (·.name == "Shield Blocker"))[0]!
  let idCbtBlkShield : ReplacementId := { kind := .shieldCounterPreventDamage, object := some cbtBlk.id }
  let gCbt1 :=
    (((((gCbt0.recordPutCounters cbtBlk.id .shield 1 (some opp)
          (cause := some (.oneShotEffect (some ⟨720⟩) none (some opp)))).createEffect
        (.replacement {
          id := idCbtMul, source := none, controller := some me,
          affectedPlayer := opp, kind := .multiplyDamage none 2 })
        (cause := some drwSubCause)).createEffect
        (.replacement {
          id := idCbtLifeAdd, source := none, controller := some me,
          affectedPlayer := me, kind := .modifyLifeGain me 2 1 })
        (cause := some drwSubCause)).createEffect
        (.replacement {
          id := idCbtLifeMul, source := none, controller := some me,
          affectedPlayer := me, kind := .modifyLifeGain me 0 2 })
        (cause := some drwSubCause)).change (.replacementOrder #[idCbtMul])).record
      (GameEvent.rules gCbt0.turnNumber (.combat (.damageAssigned false true #[
        { source := cbtAtk1.id, toCreatures := #[], toPlayer := 2 },
        { source := cbtAtk2.id, toCreatures := #[(cbtBlk.id, 2)], toPlayer := 0 }
      ])) (.turnBased (.assignCombatDamage false)))
  let gCbtPaused := (quiet gCbt1).dealAssignedCombatDamage
  let gCbtAfterDmg :=
    (gCbtPaused.apply opp (.chooseReplacement idCbtMul)).toOption.getD gCbtPaused
  let gCbtDone :=
    (gCbtAfterDmg.apply me (.chooseReplacement idCbtLifeAdd)).toOption.getD gCbtAfterDmg
  let cbtLifelinkOrderOk :=
    gCbtPaused.pending == .chooseReplacement opp #[idCbtBlkShield, idCbtMul] &&
    gCbtPaused.replacementOrder.isEmpty &&
    gCbtAfterDmg.pending == .chooseReplacement me #[idCbtLifeAdd, idCbtLifeMul] &&
    gCbtDone.pending == .none &&
    gCbtDone.replacementOrder.isEmpty &&
    (gCbt1.player opp).life - (gCbtDone.player opp).life == 4 &&
    (gCbtDone.player me).life - (gCbt1.player me).life == 12 &&
    (gCbtDone.object! cbtBlk.id).status.shield == 0 &&
    (gCbtDone.object! cbtBlk.id).status.damage == 0
  outOfBandRejected &&
    pausedPromptOk &&
    gDmgAddFirst.pending == Pending.none &&
    gDmgAddFirst.replacementOrder.isEmpty &&
    gDmgMulFirst.pending == Pending.none &&
    gDmgMulFirst.replacementOrder.isEmpty &&
    gDmgSecondPaused.pending == .chooseReplacement opp #[idAddDmg, idMulDmg] &&
    (gOrd0.player opp).life - (gDmgAddFirst.player opp).life == 10 &&
    (gOrd0.player opp).life - (gDmgMulFirst.player opp).life == 8 &&
    finChoiceOk &&
    nonResolvingCauseOk &&
    atkTokOk &&
    singlePassDamageOk &&
    arwenSamsonOk &&
    simMoveOk &&
    sbaResumeOk &&
    fightResumeOk &&
    entAtkOk &&
    drwSubResumeOk &&
    entAtkFraOk &&
    cbtLifelinkOrderOk &&
    (gLifeAddFirst.player me).life - (gOrd0.player me).life == 10 &&
    (gLifeMulFirst.player me).life - (gOrd0.player me).life == 8 &&
    (gActiveMe.selectNextReplacementStep #[candOpp, candMe] #[]) == .chosen candMe #[] &&
    (gActiveOpp.selectNextReplacementStep #[candOpp, candMe] #[]) == .chosen candOpp #[] &&
    allRulesEventsClassified gDmgAddFirst &&
    allRulesEventsClassified gDmgMulFirst &&
    allRulesEventsClassified gFinChoseHead &&
    allRulesEventsClassified gFinChoseExile &&
    allRulesEventsClassified gShdFrom &&
    allRulesEventsClassified gArw1 &&
    allRulesEventsClassified gSimDone &&
    allRulesEventsClassified gSbaDone &&
    allRulesEventsClassified gFightDone &&
    allRulesEventsClassified gEntAtkDone &&
    allRulesEventsClassified gDrwSubDone &&
    allRulesEventsClassified gFraEntDone &&
    allRulesEventsClassified gCbtDone &&
    allRulesEventsClassified gLifeAddFirst &&
    allRulesEventsClassified gLifeMulFirst

/- Phase 8 isolation (CR 611 / 613):
1. `ContinuousEffectEvent` (`created` / `expired`) and `ContinuousEffectSpec`
   evaluate Layers 1–7 (`copy`, `control`, `text`, `types` with `ObjectScope`
   dependency CR 613.8, `colors`, `abilities` add/remove, and `7a`–`7d` P/T
   sublayers `ptCda`, `ptSet`, `ptModify`, `ptSwitch`) purely from `g.activeEffects`.
2. `DelayedTrigger` (`CR 603.7`) table (`g.delayedTriggers`), including
   `.enrageAdditionalCombat` (`oneShot := true`).
3. `CounterBag` (`Status.counters` single source of truth), expanded `PlayerEvent`
   (`ringTempted`, `tookInitiative`, `completedDungeon`, `becameMonarch`,
   `ascended`, `becameDay`, `becameNight`), `CR 400.7d` cast metadata across
   `.stack -> .battlefield`, and `ContinuationFrame` stack (`g.continuations`). -/
#guard
  let g0 := addPermanent (addPermanent (quiet afterDraw) bear me me) hero me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let cause8 : EventCause := .oneShotEffect (some ⟨801⟩) (some h.id) (some me)
  -- Layer 3 (text), Layer 4 (types + conditional scope CR 613.8), Layer 5 (colors),
  -- Layer 6 (abilities add/remove), and Layer 7a–7d (ptCda, ptSet, ptModify, ptSwitch):
  -- Even when 7d (`ptSwitch`), 7c (`ptModify`), and 7b (`ptSet`) are created out of
  -- sublayer order, CR 613.4 applies 7b (4/1) -> 7c (+2/+3 = 6/4 +1/+1 counter = 7/5) -> 7d (5/7).
  let gLayers :=
    (((((((g0.recordPutCounters b.id .plusOnePlusOne 1 (some me) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) .ptSwitch .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.ptModify 2 3) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.ptSet 4 1) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.text (.replaceCreatureType .bear .elf)) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.creaturesControlledBy me) (.types .add #[.artifact] #[.construct] #[.legendary]) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.colors .set { blue := true }) .untilEndOfTurn) (cause := some cause8)).createEffect
        (.layered (.objects #[b.id]) (.abilities { keywords := Keyword.flying } .none) .untilEndOfTurn) (cause := some cause8)
  let bAfter := gLayers.object! b.id
  let layersOk :=
    gLayers.power bAfter == 5 &&
    gLayers.toughness bAfter == 7 &&
    (gLayers.subtypes bAfter).contains .elf &&
    !(gLayers.subtypes bAfter).contains .bear &&
    (gLayers.subtypes bAfter).contains .construct &&
    gLayers.isArtifact bAfter &&
    gLayers.isLegendary bAfter &&
    gLayers.colors bAfter == ({ blue := true } : ColorSet) &&
    gLayers.hasFlying bAfter &&
    bAfter.status.counters == #[(.plusOnePlusOne, 1)]
  -- Delayed trigger `.endStepSacrifice` (CR 603.7): fires at `.end` step and removes itself (`isOneShot == true`).
  let gDelayed0 :=
    (g0.registerDelayedTrigger {
      controller := me
      source := some h
      kind := .endStepSacrifice b.id
      cause := cause8 }).record (GameEvent.stepBegan g0.turnNumber .postcombatMain g0.activePlayer)
  let gDelayed1 := (quiet gDelayed0).beginStep .end
  let delayedOk :=
    !gDelayed1.delayedTriggers.any (·.kind == .endStepSacrifice b.id) &&
    gDelayed1.stack.size == g0.stack.size + 1
  -- Expanded `PlayerEvent`s (`ringTempted`, `becameMonarch`, `gainedDesignation`) and `TurnEvent.dayNightChanged`
  let gPlEv :=
    (((((quiet g0).record (GameEvent.ringTempted g0.turnNumber me (some b.id) 1 (cause := some cause8))).record
      (GameEvent.becameMonarch g0.turnNumber me (cause := some cause8))).record
      (GameEvent.gainedDesignation g0.turnNumber me .citysBlessing (cause := some cause8))).record
      (GameEvent.rules g0.turnNumber (.turn (.dayNightChanged true)) cause8)).record
      (GameEvent.rules g0.turnNumber (.turn (.dayNightChanged false)) cause8)
  let plEvOk :=
    (gPlEv.player me).ringBearerId == some b.id &&
    (gPlEv.player me).theRingAbilities == 1 &&
    (gPlEv.player me).isMonarch &&
    (gPlEv.player me).citysBlessing &&
    !gPlEv.isNight
  -- ContinuationFrame stack (`g.continuations`): nested frame isolates scratch state and restores outer frame on pop.
  let gCont0 := (g0.change (.pushContinuationFrame {})).change (.continuation (.notedCountThisWay 7))
  let gContPushed := (gCont0.change (.pushContinuationFrame {})).change (.continuation (.notedCountThisWay 99))
  let gContInner :=
    if gContPushed.notedCountThisWay == 99 then gContPushed.change .popContinuationFrame
    else (gContPushed.change (.continuation (.notedCountThisWay 0))).change .popContinuationFrame
  let contOk :=
    gCont0.notedCountThisWay == 7 &&
    gContPushed.notedCountThisWay == 99 &&
    gContInner.notedCountThisWay == 7 &&
    gContInner.continuations.size == gCont0.continuations.size
  layersOk &&
    delayedOk &&
    plEvOk &&
    contOk &&
    allRulesEventsClassified gLayers &&
    allRulesEventsClassified gDelayed1 &&
    allRulesEventsClassified gPlEv

/- Extra-turn cause alignment when a lost player's extra turn is skipped
(CR 500.7 / 800.4k): `pendingExtraCauses` pops alongside `extraTurns` so the
surviving player's extra turn inherits its own cause, not the skipped player's. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let g0 := quiet afterDraw
  let causeMe1 : EventCause := .oneShotEffect (some ⟨901⟩) none (some me)
  let causeMe2 : EventCause := .oneShotEffect (some ⟨902⟩) none (some me)
  let causeOpp : EventCause := .oneShotEffect (some ⟨903⟩) none (some opp)
  let gQueued :=
    (((g0.record (GameEvent.extraTurnAdded g0.turnNumber me .current (cause := causeMe1))).record
        (GameEvent.extraTurnAdded g0.turnNumber me .current (cause := causeMe2))).record
        (GameEvent.extraTurnAdded g0.turnNumber opp .current (cause := causeOpp))).record
        (GameEvent.playerLost g0.turnNumber opp .effect (cause := some causeMe1))
  let gExtra1 := gQueued.startNextTurn
  let powerUpsCause? (g : Game) : Option EventCause :=
    g.events.findSomeRev? fun e =>
      match e.change with
      | .rules (.continuousEffect (.created _ .powerUpsForbiddenThisTurn)) => e.cause?
      | _ => none
  let gExtra2 := (gExtra1.clearEOT).startNextTurn
  gQueued.extraTurns == #[opp, me, me] &&
    gExtra1.activePlayer == me &&
    gExtra1.extraTurns == #[me] &&
    powerUpsCause? gExtra1 == some causeMe2 &&
    gExtra2.activePlayer == me &&
    gExtra2.extraTurns.isEmpty &&
    powerUpsCause? gExtra2 == some causeMe1 &&
    allRulesEventsClassified gExtra2

/- `.untilEndOfNextTurnOf` play permissions and control effects (CR 514.2 /
611.2a): `.turnBased .cleanupClear` events emitted during the creation turn's
cleanup step (and any CR 514.3a extra cleanup or an opponent's turn) do not
count as a turn of `p` beginning, so both last until cleanup of `p`'s next turn. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let g0 := addPermanent (addPermanent (quiet afterDraw) bear opp opp) hero me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let causeNext : EventCause := .oneShotEffect (some ⟨910⟩) (some h.id) (some me)
  let (g1, exId) := g0.move h.id .exile none (cause := some causeNext)
  let gInit :=
    (((g1.changeControl (g1.object! b.id) me (turnEndsLeft := 2)).createEffect
        (.playPermission exId { player := me } (turnEnds := 2)) (cause := some causeNext)).createEffect
        (.keywordsUntilEot b.id Keyword.haste) (cause := some causeNext)).record
        (GameEvent.damageMarked g1.turnNumber b.id 1 (cause := causeNext))
  let hasPlayPerm (g : Game) : Bool :=
    g.activeEffects.any fun (_, s) =>
      match s with
      | .permission p (.playFromExile oid _) _ => p == some me && oid == exId
      | _ => false
  -- Turn 1 cleanup (emits `.cleanupClear` events from haste expiration and marked damage)
  let gClean1 := gInit.clearEOT
  let hadCleanupClear := gClean1.events.any (fun e => e.cause? == some (.turnBased .cleanupClear))
  -- Second CR 514.3a cleanup in Turn 1
  let gClean1b := gClean1.clearEOT
  -- Advance to `opp`'s turn and run `opp`'s cleanup
  let gOppTurn := gClean1b.startNextTurn
  let gOppClean := gOppTurn.clearEOT
  -- Advance to `me`'s next turn (`TurnEvent.turnBegan me false` recorded)
  let gMeNext := gOppClean.startNextTurn
  -- Cleanup of `me`'s next turn finally expires both
  let gMeNextClean := gMeNext.clearEOT
  hadCleanupClear &&
    !gClean1.hasHaste (gClean1.object! b.id) &&
    gClean1.controllerOf (gClean1.object! b.id) == some me &&
    gClean1.controlTurnEndsLeft (gClean1.object! b.id) == 2 &&
    hasPlayPerm gClean1 &&
    gClean1b.controllerOf (gClean1b.object! b.id) == some me &&
    hasPlayPerm gClean1b &&
    gOppTurn.activePlayer == opp &&
    gOppClean.controllerOf (gOppClean.object! b.id) == some me &&
    gOppClean.controlTurnEndsLeft (gOppClean.object! b.id) == 2 &&
    hasPlayPerm gOppClean &&
    gMeNext.activePlayer == me &&
    gMeNext.controllerOf (gMeNext.object! b.id) == some me &&
    gMeNext.controlTurnEndsLeft (gMeNext.object! b.id) == 1 &&
    hasPlayPerm gMeNext &&
    gMeNextClean.controllerOf (gMeNextClean.object! b.id) == some opp &&
    gMeNextClean.controlTurnEndsLeft (gMeNextClean.object! b.id) == 0 &&
    !hasPlayPerm gMeNextClean

/- Layer 4 CR 613.7 timestamp order and CR 613.8 dependency ordering:
1. Later object-scoped `.set` overrides an earlier `.creaturesControlledBy`
   type-adding effect without re-adding the overwritten type.
2. Earlier `.creaturesControlledBy` waits for a later `.additionalCreature` on
   a noncreature permanent (CR 613.8) and then applies to it.
3. `.notACreature`, `.returnedAsArtifact`, and `.onlyFoodArtifact` apply at
   their own timestamps instead of overriding later type/subtype additions. -/
#guard
  let shrineDef : CardDef := enchantment "Event Shrine" ManaCost.empty ""
  let g0 := addPermanent (addPermanent (addPermanent (quiet afterDraw) bear me me) hero me me) shrineDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let s := (g0.battlefield.filter (·.name == "Event Shrine"))[0]!
  let c1 : EventCause := .oneShotEffect (some ⟨921⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨922⟩) none (some me)
  -- 1 & 2: earlier team artifact grant, then `b` becomes Enchantment Creature — God, and `s` becomes a creature
  let gSetOverride :=
    (((g0.createEffect
        (.layered (.creaturesControlledBy me) (.types .add #[.artifact] #[.construct] #[]) .untilEndOfTurn)
        (cause := some c1)).createEffect
        (.layered (.objects #[b.id]) (.types .set #[.enchantment, .creature] #[.god] #[.legendary]) .untilEndOfTurn)
        (cause := some c2)).createEffect
        (.additionalCreature s.id true) (cause := some c2))
  let bSet := gSetOverride.object! b.id
  let hSet := gSetOverride.object! h.id
  let sSet := gSetOverride.object! s.id
  let setAndDepOk :=
    gSetOverride.types bSet == #[.enchantment, .creature] &&
    !gSetOverride.isArtifact bSet &&
    gSetOverride.subtypes bSet == #[.god] &&
    gSetOverride.isLegendary bSet &&
    gSetOverride.isArtifact hSet &&
    (gSetOverride.subtypes hSet).contains .construct &&
    gSetOverride.isEnchantment sSet &&
    gSetOverride.isCreature sSet &&
    gSetOverride.isArtifact sSet &&
    (gSetOverride.subtypes sSet).contains .construct
  -- 3a: `.notACreature` / `.returnedAsArtifact` vs later `.additionalCreature`
  let gNotThenAdd :=
    ((g0.createEffect (.notACreature b.id) (cause := some c1)).createEffect
      (.additionalCreature b.id true) (cause := some c2))
  let gAddThenNot :=
    ((g0.createEffect (.additionalCreature s.id true) (cause := some c1)).createEffect
      (.notACreature s.id) (cause := some c2))
  let gRetThenAdd :=
    ((g0.createEffect (.returnedAsArtifact h.id) (cause := some c1)).createEffect
      (.additionalCreature h.id true) (cause := some c2))
  -- 3b: `.onlyFoodArtifact` vs `.additionalSubtype`
  let gFoodThenTreasure :=
    ((g0.createEffect (.onlyFoodArtifact b.id) (cause := some c1)).createEffect
      (.additionalSubtype b.id .treasure) (cause := some c2))
  let gTreasureThenFood :=
    ((g0.createEffect (.additionalSubtype b.id .treasure) (cause := some c1)).createEffect
      (.onlyFoodArtifact b.id) (cause := some c2))
  setAndDepOk &&
    gNotThenAdd.isCreature (gNotThenAdd.object! b.id) &&
    !gAddThenNot.isCreature (gAddThenNot.object! s.id) &&
    gRetThenAdd.isCreature (gRetThenAdd.object! h.id) &&
    gRetThenAdd.isArtifact (gRetThenAdd.object! h.id) &&
    gFoodThenTreasure.types (gFoodThenTreasure.object! b.id) == #[.artifact] &&
    gFoodThenTreasure.subtypes (gFoodThenTreasure.object! b.id) == #[.food, .treasure] &&
    gTreasureThenFood.subtypes (gTreasureThenFood.object! b.id) == #[.food] &&
    allRulesEventsClassified gSetOverride

/- Layer 6 CR 613.1f / 613.7c / 613.7e keyword-counter and ability-loss ordering:
1. Keyword counters (including `flying`, `shadow`, `deathtouch`, `lifelink`,
   `trample`, `indestructible`) placed BEFORE `.losesAbilitiesUntilEot` or
   BEFORE attaching a loses-abilities Aura are stripped.
2. Keyword counters placed AFTER ability loss grant their keywords while earlier
   printed and counter keywords remain lost.
3. Placing another counter of an earlier kind AFTER ability loss refreshes that
   counter kind's timestamp (CR 613.7c) and restores only that keyword. -/
#guard
  let wingedDef : CardDef :=
    creature "WingedGuard" ManaCost.empty #["Bird"] 2 2 (keywords := Keyword.vigilance)
  let freezeAura : CardDef :=
    { (enchantment "FreezeAura" ManaCost.empty "") with
      subtypes := #["Aura"]
      staticAbilities := #[.enchantedLosesAbilitiesCantUntap] }
  let g0 := addPermanent (addPermanent (quiet afterDraw) wingedDef me me) freezeAura me me
  let w := (g0.battlefield.filter (·.name == "WingedGuard"))[0]!
  let aura := (g0.battlefield.filter (·.name == "FreezeAura"))[0]!
  let c1 : EventCause := .oneShotEffect (some ⟨931⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨932⟩) none (some me)
  let c3 : EventCause := .oneShotEffect (some ⟨933⟩) none (some me)
  -- Put counters first, then lose all abilities until EOT
  let gCountersFirst :=
    (((((((g0.recordPutCounters w.id .flying 1 (some me) (cause := some c1)).recordPutCounters
        w.id .shadow 1 (some me) (cause := some c1)).recordPutCounters
        w.id .deathtouch 1 (some me) (cause := some c1)).recordPutCounters
        w.id .lifelink 1 (some me) (cause := some c1)).recordPutCounters
        w.id .trample 1 (some me) (cause := some c1)).recordPutCounters
        w.id .indestructible 1 (some me) (cause := some c1)).createEffect
        (.losesAbilitiesUntilEot w.id) (cause := some c2))
  let wLost := gCountersFirst.object! w.id
  let strippedOk :=
    !gCountersFirst.hasVigilance wLost &&
    !gCountersFirst.hasFlying wLost &&
    !gCountersFirst.hasShadow wLost &&
    !gCountersFirst.hasDeathtouch wLost &&
    !gCountersFirst.hasLifelink wLost &&
    !gCountersFirst.hasTrample wLost &&
    !gCountersFirst.hasIndestructible wLost &&
    gCountersFirst.effectiveKeywords wLost == Keywords.none
  -- Refresh `.flying` counter timestamp (CR 613.7c) and add new `.haste` counter after ability loss
  let gRefreshed :=
    (gCountersFirst.recordPutCounters w.id .flying 1 (some me) (cause := some c3)).recordPutCounters
      w.id .haste 1 (some me) (cause := some c3)
  let wRef := gRefreshed.object! w.id
  let refreshedOk :=
    gRefreshed.hasFlying wRef &&
    gRefreshed.hasHaste wRef &&
    !gRefreshed.hasVigilance wRef &&
    !gRefreshed.hasShadow wRef &&
    !gRefreshed.hasDeathtouch wRef &&
    !gRefreshed.hasLifelink wRef &&
    !gRefreshed.hasTrample wRef &&
    !gRefreshed.hasIndestructible wRef &&
    gRefreshed.effectiveKeywords wRef == { flying := true, haste := true }
  -- Attached loses-abilities Aura ordering (CR 613.7e vs 613.7c):
  -- Counter before attachment is stripped; counter after attachment applies.
  let gBeforeAura :=
    ((g0.recordPutCounters w.id .deathtouch 1 (some me) (cause := some c1)).record
      (GameEvent.attached g0.turnNumber (g0.snapshot aura) w.id (cause := c2))).recordPutCounters
      w.id .lifelink 1 (some me) (cause := some c3)
  let wAura := gBeforeAura.object! w.id
  let auraOk :=
    !gBeforeAura.hasVigilance wAura &&
    !gBeforeAura.hasDeathtouch wAura &&
    gBeforeAura.hasLifelink wAura &&
    gBeforeAura.effectiveKeywords wAura == Keyword.lifelink
  strippedOk && refreshedOk && auraOk &&
    allRulesEventsClassified gRefreshed &&
    allRulesEventsClassified gBeforeAura

/- Layer 6 CR 613.1f / 613.7 timestamp ordering for `triggeredAbilities`,
`matchTriggers` (including subtype-enter and combat-damage token arms),
`hasCantBeBlocked` (Bilbo's Ring and My Precious), and `prowessTriggers`
(printed and Equipment-granted prowess). -/
#guard
  let c1 : EventCause := .oneShotEffect (some ⟨941⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨942⟩) none (some me)
  let c3 : EventCause := .oneShotEffect (some ⟨943⟩) none (some me)
  let c4 : EventCause := .oneShotEffect (some ⟨944⟩) none (some me)
  -- 1. Triggered abilities (printed, granted, attached Equipment, subtype-enter, combat-damage token)
  let subEnterAb : TriggeredAbility := .onThisOrAnotherSubtypeEntersCreateTokens "Dwarf" .treasure 1
  let combatTokAb : TriggeredAbility := .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2
  let preGrantAb : TriggeredAbility :=
    TriggeredAbility.fra .attack "Whenever this creature attacks, draw a card." (.draw 1)
  let postGrantAb : TriggeredAbility :=
    TriggeredAbility.fra .attack "Whenever this creature attacks, you gain 2 life." (.gainLife 2)
  let captainDef : CardDef :=
    creature "DwarfCaptain" ManaCost.empty #["Dwarf"] 2 2
      (triggeredAbilities := #[.onAttackScry 1, subEnterAb, combatTokAb])
  let strikerDef : CardDef :=
    creature "DwarfStriker" ManaCost.empty #["Dwarf"] 2 2
  let kitesailDef : CardDef :=
    { name := "Test Kitesail"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.fra .equippedMedicsKitesail] }
  let gT0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) captainDef me me)
        strikerDef me me)
      kitesailDef me me
  let cap := (gT0.battlefield.filter (·.name == "DwarfCaptain"))[0]!
  let striker := (gT0.battlefield.filter (·.name == "DwarfStriker"))[0]!
  let kitesail := (gT0.battlefield.filter (·.name == "Test Kitesail"))[0]!
  let gEquippedAndGranted :=
    ((gT0.record (GameEvent.attached gT0.turnNumber (gT0.snapshot kitesail) cap.id (cause := c1))).createEffect
      (.grantedTriggered cap.id preGrantAb false) (cause := some c1)).createEffect
      (.grantedTriggered cap.id (.onEnterDraw 1) true) (cause := some c1)
  let beforeTriggerCount := (gEquippedAndGranted.triggeredAbilities (gEquippedAndGranted.object! cap.id)).size
  let gCapLost :=
    gEquippedAndGranted.createEffect (.losesAbilitiesUntilEot cap.id) (cause := some c2)
  let capLostEmpty := (gCapLost.triggeredAbilities (gCapLost.object! cap.id)).isEmpty
  -- Attacking while abilities are lost queues 0 triggers (neither printed, pre-grant, nor Kitesail)
  let atkEv :=
    GameEvent.attackersDeclared gCapLost.turnNumber me
      #[(gCapLost.snapshot (gCapLost.object! cap.id), .player ⟨1⟩)] (cause := some c3)
  let gAtkLost := gCapLost.record atkEv
  -- Dwarf token created OR nontoken Dwarf moved onto battlefield while abilities are lost queues 0 triggers
  let (gEnterTokLost, _) := gCapLost.createToken me strikerDef (cause := some c3)
  let gEnterMoveLost := addPermanent gCapLost strikerDef me me
  -- Striker dealing combat damage to player or battle while DwarfCaptain lost abilities queues 0 triggers
  let strikeSnap := gCapLost.snapshot (gCapLost.object! striker.id)
  let gDmgPlayerLost :=
    gCapLost.record (GameEvent.damagedPlayer gCapLost.turnNumber strikeSnap ⟨1⟩ 2 true (cause := c3))
  let battleSnap : EventObject := { name := "TestBattle", owner := ⟨1⟩, zone := .battlefield }
  let gDmgBattleLost :=
    gCapLost.record
      (GameEvent.rules gCapLost.turnNumber
        (.damage (.dealt #[{ source := strikeSnap, recipient := .battle battleSnap, amount := 2, combat := true }]))
        c3)
  -- Post-removal grant and post-removal re-attachment ARE retained and DO fire
  let gPostGrant :=
    (gCapLost.createEffect (.grantedTriggered cap.id postGrantAb true) (cause := some c3)).record
      (GameEvent.attached gCapLost.turnNumber (gCapLost.snapshot (gCapLost.object! kitesail.id)) cap.id (cause := c4))
  let postTriggers := gPostGrant.triggeredAbilities (gPostGrant.object! cap.id)
  let gAtkPost :=
    gPostGrant.record
      (GameEvent.attackersDeclared gPostGrant.turnNumber me
        #[(gPostGrant.snapshot (gPostGrant.object! cap.id), .player ⟨1⟩)] (cause := some c4))
  let triggersOk :=
    beforeTriggerCount == 6 &&
    capLostEmpty &&
    gAtkLost.waitingTriggers.isEmpty &&
    gEnterTokLost.waitingTriggers.isEmpty &&
    gEnterMoveLost.waitingTriggers.isEmpty &&
    gDmgPlayerLost.waitingTriggers.isEmpty &&
    gDmgBattleLost.waitingTriggers.isEmpty &&
    postTriggers.size == 2 &&
    postTriggers.contains postGrantAb &&
    gAtkPost.waitingTriggers.size == 2
  -- 2. `hasCantBeBlocked` with Bilbo's Ring and My Precious
  let ringDef : CardDef :=
    { name := "Test Ring"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedHexproofUnblockableDuringYourTurn] }
  let preciousDef : CardDef :=
    { name := "Test Precious"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof] }
  let gEq0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear me me)
        ringDef me me)
      preciousDef me me
  let host := (gEq0.battlefield.filter (·.name == "Event Bear"))[0]!
  let ring := (gEq0.battlefield.filter (·.name == "Test Ring"))[0]!
  let precious := (gEq0.battlefield.filter (·.name == "Test Precious"))[0]!
  let gRingPre :=
    gEq0.record (GameEvent.attached gEq0.turnNumber (gEq0.snapshot ring) host.id (cause := c1))
  let gRingLost :=
    gRingPre.createEffect (.losesAbilitiesUntilEot host.id) (cause := some c2)
  let gRingRe :=
    gRingLost.record (GameEvent.attached gRingLost.turnNumber (gRingLost.snapshot (gRingLost.object! ring.id)) host.id (cause := c3))
  let gPrecPre :=
    gEq0.record (GameEvent.attached gEq0.turnNumber (gEq0.snapshot precious) host.id (cause := c1))
  let gPrecLost :=
    gPrecPre.createEffect (.losesAbilitiesUntilEot host.id) (cause := some c2)
  let gPrecRe :=
    gPrecLost.record (GameEvent.attached gPrecLost.turnNumber (gPrecLost.snapshot (gPrecLost.object! precious.id)) host.id (cause := c3))
  let unblockableOk :=
    gRingPre.hasCantBeBlocked (gRingPre.object! host.id) &&
    gRingPre.hasHexproof (gRingPre.object! host.id) &&
    !gRingLost.hasCantBeBlocked (gRingLost.object! host.id) &&
    !gRingLost.hasHexproof (gRingLost.object! host.id) &&
    gRingRe.hasCantBeBlocked (gRingRe.object! host.id) &&
    gRingRe.hasHexproof (gRingRe.object! host.id) &&
    gPrecPre.hasCantBeBlocked (gPrecPre.object! host.id) &&
    gPrecPre.hasHexproof (gPrecPre.object! host.id) &&
    !gPrecLost.hasCantBeBlocked (gPrecLost.object! host.id) &&
    !gPrecLost.hasHexproof (gPrecLost.object! host.id) &&
    gPrecRe.hasCantBeBlocked (gPrecRe.object! host.id) &&
    gPrecRe.hasHexproof (gPrecRe.object! host.id)
  -- 3. `prowessTriggers` with printed prowess and Wizard's Staff
  let mageDef : CardDef :=
    { (creature "ProwessMage" ManaCost.empty #["Wizard"] 1 2 (keywords := Keyword.prowess)) with
      prowessInstances := 1 }
  let staffDef : CardDef :=
    { name := "Test Staff"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureHasKeywords Keyword.prowess] }
  let gPw0 :=
    addPermanent (addPermanent (quiet afterDraw) mageDef me me) staffDef me me
  let mage := (gPw0.battlefield.filter (·.name == "ProwessMage"))[0]!
  let staff := (gPw0.battlefield.filter (·.name == "Test Staff"))[0]!
  let gPwPre :=
    gPw0.record (GameEvent.attached gPw0.turnNumber (gPw0.snapshot staff) mage.id (cause := c1))
  let gPwLost :=
    gPwPre.createEffect (.losesAbilitiesUntilEot mage.id) (cause := some c2)
  let gPwRe :=
    gPwLost.record (GameEvent.attached gPwLost.turnNumber (gPwLost.snapshot (gPwLost.object! staff.id)) mage.id (cause := c3))
  let prowessOk :=
    (gPwPre.prowessTriggers (gPwPre.object! mage.id)).size == 2 &&
    (gPwLost.prowessTriggers (gPwLost.object! mage.id)).isEmpty &&
    !(gPwLost.effectiveKeywords (gPwLost.object! mage.id)).prowess &&
    (gPwRe.prowessTriggers (gPwRe.object! mage.id)).size == 1 &&
    (gPwRe.effectiveKeywords (gPwRe.object! mage.id)).prowess
  triggersOk && unblockableOk && prowessOk &&
    allRulesEventsClassified gAtkPost &&
    allRulesEventsClassified gRingRe &&
    allRulesEventsClassified gPrecRe &&
    allRulesEventsClassified gPwRe

/- Phase 8 (PR #584 review round 3): `combatDamageCreatesTreasure` (including
attached Reaver Cleaver), `ironFistTapGrants`, `canBlock` (`printed.cantBlock`
vs `.cantBlockUntilEot`), and `wardCostsOn` (printed ward, ward statics,
attached ward Equipment, and lord ward) all evaluate in Layer 6 timestamp
order (CR 613.1f / 613.7 / 702.21). -/
#guard
  let opp : PlayerId := ⟨1⟩
  let c1 : EventCause := .oneShotEffect (some ⟨1001⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨1002⟩) none (some me)
  let c3 : EventCause := .oneShotEffect (some ⟨1003⟩) none (some me)
  let c4 : EventCause := .oneShotEffect (some ⟨1004⟩) none (some me)
  -- 1. `combatDamageCreatesTreasure` & Reaver Cleaver timestamp ordering
  let cleaverDef : CardDef :=
    { name := "Test Cleaver"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedGetsTrampleAndCombatTreasures 1 1] }
  let gTr0 := addPermanent (addPermanent (quiet afterDraw) bear me me) cleaverDef me me
  let atk := (gTr0.battlefield.filter (·.name == "Event Bear"))[0]!
  let cleaver := (gTr0.battlefield.filter (·.name == "Test Cleaver"))[0]!
  let gTrPre :=
    ((gTr0.markAttacking atk.id).record
      (GameEvent.attached gTr0.turnNumber (gTr0.snapshot cleaver) atk.id (cause := c1))).createEffect
      (.combatDamageCreatesTreasureUntilEot atk.id) (cause := some c1)
  let gTrLost :=
    gTrPre.createEffect (.losesAbilitiesUntilEot atk.id) (cause := some c2)
  let gTrLostCombat :=
    (((gTrLost.record (GameEvent.rules gTrLost.turnNumber
      (.combat (.damageAssigned false true #[{ source := atk.id, toPlayer := 2 }]))
      (.turnBased (.assignCombatDamage false)))).dealAssignedCombatDamage).receivePriority me).resolveTop
  let gTrRe :=
    gTrLost.record (GameEvent.attached gTrLost.turnNumber (gTrLost.snapshot (gTrLost.object! cleaver.id)) atk.id (cause := c3))
  let gTrReCombat :=
    (((gTrRe.record (GameEvent.rules gTrRe.turnNumber
      (.combat (.damageAssigned false true #[{ source := atk.id, toPlayer := 2 }]))
      (.turnBased (.assignCombatDamage false)))).dealAssignedCombatDamage).receivePriority me).resolveTop
  let gTrPostEff :=
    gTrLost.createEffect (.combatDamageCreatesTreasureUntilEot atk.id) (cause := some c4)
  let countTreasures (g : Game) : Nat :=
    (g.permanentsOf me).filter (fun o => g.hasSubtype o .treasure) |>.size
  let treasureOk :=
    (gTrPre.triggeredAbilities (gTrPre.object! atk.id)).size == 2 &&
    (gTrLost.triggeredAbilities (gTrLost.object! atk.id)).isEmpty &&
    countTreasures gTrLostCombat == 0 &&
    (gTrRe.triggeredAbilities (gTrRe.object! atk.id)).size == 1 &&
    countTreasures gTrReCombat == 2 &&
    (gTrPostEff.triggeredAbilities (gTrPostEff.object! atk.id)).size == 1
  -- 2. `ironFistTapGrants` timestamp ordering (effect removal + Aura removal)
  let stripAuraDef : CardDef :=
    { name := "Strip Aura"
      types := #[.enchantment]
      subtypes := #["Aura"]
      staticAbilities := #[.enchantedLosesAbilitiesCantUntap] }
  let gFist0 := addPermanent (addPermanent (quiet afterDraw) bear me me) stripAuraDef me me
  let fist := (gFist0.battlefield.filter (·.name == "Event Bear"))[0]!
  let stripAura := (gFist0.battlefield.filter (·.name == "Strip Aura"))[0]!
  let gFistPre :=
    (gFist0.createEffect (.ironFistTapUntilEot fist.id) (cause := some c1)).createEffect
      (.ironFistTapUntilEot fist.id) (cause := some c1)
  let gFistLost :=
    gFistPre.createEffect (.losesAbilitiesUntilEot fist.id) (cause := some c2)
  let gFistPost :=
    gFistLost.createEffect (.ironFistTapUntilEot fist.id) (cause := some c3)
  let gFistAuraLost :=
    gFistPost.record (GameEvent.attached gFistPost.turnNumber (gFistPost.snapshot (gFistPost.object! stripAura.id)) fist.id (cause := c4))
  let ironFistOk :=
    gFistPre.ironFistTapGrants (gFistPre.object! fist.id) == 2 &&
    gFistLost.ironFistTapGrants (gFistLost.object! fist.id) == 0 &&
    gFistPost.ironFistTapGrants (gFistPost.object! fist.id) == 1 &&
    gFistAuraLost.ironFistTapGrants (gFistAuraLost.object! fist.id) == 0
  -- 3. `canBlock`: `printed.cantBlock` is removed in Layer 6, `.cantBlockUntilEot` is not
  let cantBlockDef : CardDef :=
    { (creature "Reluctant Blocker" ManaCost.empty #["Human"] 2 2) with
      cantBlock := true }
  let gBlk0 :=
    addPermanent (addPermanent (quiet afterDraw) bear me me) cantBlockDef opp opp
  let attacker := (gBlk0.battlefield.filter (·.name == "Event Bear"))[0]!
  let blocker := (gBlk0.battlefield.filter (·.name == "Reluctant Blocker"))[0]!
  let gBlkAtk := gBlk0.markAttacking attacker.id (some (.player opp))
  let gBlkLost := gBlkAtk.createEffect (.losesAbilitiesUntilEot blocker.id) (cause := some c1)
  let gBlkRule := gBlkLost.createEffect (.cantBlockUntilEot blocker.id) (cause := some c2)
  let gBlkRuleThenLost :=
    (gBlkAtk.createEffect (.cantBlockUntilEot blocker.id) (cause := some c1)).createEffect
      (.losesAbilitiesUntilEot blocker.id) (cause := some c2)
  let canBlockOk :=
    !gBlkAtk.canBlock (gBlkAtk.object! blocker.id) (gBlkAtk.object! attacker.id) &&
    gBlkLost.canBlock (gBlkLost.object! blocker.id) (gBlkLost.object! attacker.id) &&
    !gBlkRule.canBlock (gBlkRule.object! blocker.id) (gBlkRule.object! attacker.id) &&
    !gBlkRuleThenLost.canBlock (gBlkRuleThenLost.object! blocker.id) (gBlkRuleThenLost.object! attacker.id)
  -- 4. `wardCostsOn`: printed ward, ward statics, attached ward Equipment, and lord ward
  let wardHeroDef : CardDef :=
    { (creature "Ward Hero" ManaCost.empty #["Hero"] 3 3) with
      supertypes := #[.legendary]
      ward := some 2
      staticAbilities := #[.wardDiscardOrPay 1] }
  let wardEqDef : CardDef :=
    { name := "Ward Cloak"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureGetsAndWard 1 1 3] }
  let wardLordDef : CardDef :=
    { (creature "Ward Lord" ManaCost.empty #["Advisor"] 2 2) with
      staticAbilities := #[.legendaryCreaturesGetAndWard 1 1 4] }
  let gWd0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) wardLordDef me me)
        wardHeroDef me me)
      wardEqDef me me
  let wHero := (gWd0.battlefield.filter (·.name == "Ward Hero"))[0]!
  let wCloak := (gWd0.battlefield.filter (·.name == "Ward Cloak"))[0]!
  let wLord := (gWd0.battlefield.filter (·.name == "Ward Lord"))[0]!
  let gWdPre :=
    gWd0.record (GameEvent.attached gWd0.turnNumber (gWd0.snapshot wCloak) wHero.id (cause := c1))
  let preWards := gWdPre.wardCostsOn (gWdPre.object! wHero.id)
  let gWdLost :=
    gWdPre.createEffect (.losesAbilitiesUntilEot wHero.id) (cause := some c2)
  let lostWards := gWdLost.wardCostsOn (gWdLost.object! wHero.id)
  let gWdRe :=
    addPermanent
      (gWdLost.record (GameEvent.attached gWdLost.turnNumber (gWdLost.snapshot (gWdLost.object! wCloak.id)) wHero.id (cause := c3)))
      wardLordDef me me
  let reWards := gWdRe.wardCostsOn (gWdRe.object! wHero.id)
  let gWdLordLost :=
    gWdPre.createEffect (.losesAbilitiesUntilEot wLord.id) (cause := some c2)
  let lordLostWards := gWdLordLost.wardCostsOn (gWdLordLost.object! wHero.id)
  let wardOk :=
    preWards.size == 4 &&
    preWards.contains (.genericMana 2) &&
    preWards.contains (.discardOrPay 1) &&
    preWards.contains (.genericMana 3) &&
    preWards.contains (.genericMana 4) &&
    lostWards.isEmpty &&
    reWards == #[.genericMana 3, .genericMana 4] &&
    lordLostWards.size == 3 &&
    !lordLostWards.contains (.genericMana 4)
  treasureOk && ironFistOk && canBlockOk && wardOk &&
    allRulesEventsClassified gTrReCombat &&
    allRulesEventsClassified gFistAuraLost &&
    allRulesEventsClassified gWdRe

/- Phase 8 (PR #584 review round 4): `cantLoseGame` (battlefield + command zone),
`opponentsCantWin`, `unspentManaBecomesColorless`, `planeswalkersYouControlHave`
(timestamp order + Layer 4 `isPlaneswalker`), `grantedManaAbilities`
(`otherSubtypeHaveTapAddOneOf` + `grantCreaturesTapAddAnyColor` in timestamp
order), and `intrinsicLandMana` / `landsCouldProduce` (`grantLandsTapAnyColor` +
land ability removal) all obey Layer 6 (CR 104.2a / 106.7 / 605.1a / 613.1f / 613.7). -/
#guard
  let opp : PlayerId := ⟨1⟩
  let c1 : EventCause := .oneShotEffect (some ⟨1101⟩) none (some me)
  let c2 : EventCause := .oneShotEffect (some ⟨1102⟩) none (some me)
  -- 1. `cantLoseGame` & `opponentsCantWin` (battlefield + command zone)
  let angelDef : CardDef :=
    { (creature "Platinum Test" ManaCost.empty #["Angel"] 4 4) with
      cantLoseGame := true
      opponentsCantWin := true }
  let gAngel0 :=
    (addPermanent (quiet afterDraw) angelDef me me).setLifeTotal me 0
  let angel := (gAngel0.battlefield.filter (·.name == "Platinum Test"))[0]!
  let gAngelPre := gAngel0.checkSBA
  let gAngelLost :=
    (gAngel0.createEffect (.losesAbilitiesUntilEot angel.id) (cause := some c1)).checkSBA
  let (gCmd0, cmdObj) :=
    ((quiet afterDraw).setLifeTotal me 0).allocObject angelDef me .command (some me)
  let gCmdPre := gCmd0.checkSBA
  let gCmdLost :=
    (gCmd0.createEffect (.losesAbilitiesUntilEot cmdObj.id) (cause := some c1)).checkSBA
  let cantLoseWinOk :=
    !(gAngelPre.player me).lost &&
    gAngelPre.result.isNone &&
    (gAngelLost.player me).lost &&
    gAngelLost.result == some (.won opp) &&
    !(gCmdPre.player me).lost &&
    gCmdPre.result.isNone &&
    (gCmdLost.player me).lost &&
    gCmdLost.result == some (.won opp)
  -- 2. `unspentManaBecomesColorless`
  let horizonDef : CardDef :=
    { (creature "Horizon Test" ManaCost.empty #["Rogue"] 3 3) with
      unspentManaBecomesColorless := true }
  let gMana0 :=
    (addPermanent (quiet afterDraw) horizonDef me me).addMana me (.colored .red) 1
  let horizon := (gMana0.battlefield.filter (·.name == "Horizon Test"))[0]!
  let gManaKept := gMana0.emptyManaPools
  let gManaLost :=
    (gMana0.createEffect (.losesAbilitiesUntilEot horizon.id) (cause := some c1)).emptyManaPools
  let unspentManaOk :=
    (gManaKept.player me).manaPool.colorless == 1 &&
    (gManaKept.player me).manaPool.total == 1 &&
    (gManaLost.player me).manaPool.isEmpty
  -- 3. `planeswalkersYouControlHave` (Layer 6 timestamp order + Layer 4 `isPlaneswalker`)
  let loyaltyGrantAb : ActivatedAbility :=
    { cost := { loyalty := some (.plus 1) }
      effect := {} }
  let pwDef : CardDef :=
    { name := "Test Planeswalker"
      types := #[.planeswalker]
      loyalty := some 4 }
  let healerDef : CardDef :=
    { name := "Way of Test"
      types := #[.enchantment]
      planeswalkersYouControlHave := #[loyaltyGrantAb] }
  let gPw0 := addPermanent (addPermanent (quiet afterDraw) healerDef me me) pwDef me me
  let pw := (gPw0.battlefield.filter (·.name == "Test Planeswalker"))[0]!
  let gPwLost := gPw0.createEffect (.losesAbilitiesUntilEot pw.id) (cause := some c1)
  let gPwRe := addPermanent gPwLost healerDef me me
  let gPwFood := gPw0.createEffect (.onlyFoodArtifact pw.id) (cause := some c2)
  let pwGrantOk :=
    (gPw0.activatedAbilitiesOf (gPw0.object! pw.id)).size == 1 &&
    (gPwLost.activatedAbilitiesOf (gPwLost.object! pw.id)).isEmpty &&
    (gPwRe.activatedAbilitiesOf (gPwRe.object! pw.id)).size == 1 &&
    (gPwFood.activatedAbilitiesOf (gPwFood.object! pw.id)).isEmpty
  -- 4. `grantedManaAbilities` (`otherSubtypeHaveTapAddOneOf` + `grantCreaturesTapAddAnyColor`)
  let elfDef : CardDef := creature "Test Elf" ManaCost.empty #["Elf"] 1 1
  let subtypeLordDef : CardDef :=
    { (creature "Elf Mana Lord" ManaCost.empty #["Advisor"] 2 2) with
      staticAbilities := #[.otherSubtypeHaveTapAddOneOf #[.elf] #[.colored .green, .colored .blue]] }
  let chorusDef : CardDef :=
    { name := "Test Chorus"
      types := #[.enchantment]
      grantCreaturesTapAddAnyColor := true }
  let gGr0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) subtypeLordDef me me)
        chorusDef me me)
      elfDef me me
  let elf := (gGr0.battlefield.filter (·.name == "Test Elf"))[0]!
  let gGrLost := gGr0.createEffect (.losesAbilitiesUntilEot elf.id) (cause := some c1)
  let gGrRe := addPermanent gGrLost subtypeLordDef me me
  let grantedManaOk :=
    (gGr0.grantedManaAbilities (gGr0.object! elf.id)).size == 5 &&
    (gGrLost.grantedManaAbilities (gGrLost.object! elf.id)).isEmpty &&
    (gGrLost.manaAbilitiesOf (gGrLost.object! elf.id)).isEmpty &&
    gGrRe.grantedManaAbilities (gGrRe.object! elf.id) == #[.colored .green, .colored .blue]
  -- 5. `intrinsicLandMana` / `landsCouldProduce` (`grantLandsTapAnyColor` + land ability loss)
  let mtnDef : CardDef := { name := "Test Mountain", types := #[.land], subtypes := #["Mountain"] }
  let lanternDef : CardDef :=
    { name := "Test Lantern"
      types := #[.artifact]
      grantLandsTapAnyColor := true }
  let gLd0 := addPermanent (addPermanent (quiet afterDraw) lanternDef me me) mtnDef me me
  let mtn := (gLd0.battlefield.filter (·.name == "Test Mountain"))[0]!
  let lantern := (gLd0.battlefield.filter (·.name == "Test Lantern"))[0]!
  let gLanternLost := gLd0.createEffect (.losesAbilitiesUntilEot lantern.id) (cause := some c1)
  let gBothLost := gLanternLost.createEffect (.losesAbilitiesUntilEot mtn.id) (cause := some c2)
  let gMtnLost := gLd0.createEffect (.losesAbilitiesUntilEot mtn.id) (cause := some c1)
  let gMtnReLantern := addPermanent gMtnLost lanternDef me me
  let landManaOk :=
    (gLd0.intrinsicLandMana (gLd0.object! mtn.id)).size == 5 &&
    gLanternLost.intrinsicLandMana (gLanternLost.object! mtn.id) == #[.colored .red] &&
    (gBothLost.intrinsicLandMana (gBothLost.object! mtn.id)).isEmpty &&
    (gBothLost.landsCouldProduce #[gBothLost.object! mtn.id]).isEmpty &&
    (gMtnLost.intrinsicLandMana (gMtnLost.object! mtn.id)).isEmpty &&
    (gMtnLost.manaAbilityDefs (gMtnLost.object! mtn.id)).isEmpty &&
    (gMtnReLantern.intrinsicLandMana (gMtnReLantern.object! mtn.id)).size == 5 &&
    (gMtnReLantern.manaAbilityDefs (gMtnReLantern.object! mtn.id)).size == 1
  cantLoseWinOk && unspentManaOk && pwGrantOk && grantedManaOk && landManaOk &&
    allRulesEventsClassified gAngelLost &&
    allRulesEventsClassified gManaKept &&
    allRulesEventsClassified gManaLost &&
    allRulesEventsClassified gPwRe &&
    allRulesEventsClassified gGrRe &&
    allRulesEventsClassified gMtnReLantern

/- Phase 9 isolation suite (CR 613.1a–b / 707 / 800.4a): Layer 1 copy and
Layer 2 control effects are purely derived from `g.activeEffects` without
mutating `GameObject.printed` / `GameObject.controller` or emitting secondary
`ObjectChange` or `.staticAbility` churn on creation or expiry. Copy-of-copy
reads Layer 1 `copiableValues`. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let giantDef : CardDef :=
    { creature "Phase9 Giant" ManaCost.empty #["Giant"] 4 5 with
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let cloneDef : CardDef :=
    creature "Phase9 Clone" ManaCost.empty #["Shapeshifter"] 0 0
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear opp opp)
        giantDef me me)
      cloneDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gt := (g0.battlefield.filter (·.name == "Phase9 Giant"))[0]!
  let cl := (g0.battlefield.filter (·.name == "Phase9 Clone"))[0]!
  let gCopy1 := (quiet g0).becomeCopyOf b gt (untilEot := true)
  let gCopy2 := gCopy1.becomeCopyOf (gCopy1.object! cl.id) (gCopy1.object! b.id) (untilEot := true)
  let noPrintedMutation :=
    (gCopy1.object! b.id).printed.name == "Event Bear" &&
    (gCopy2.object! cl.id).printed.name == "Phase9 Clone"
  let copyValuesOk :=
    gCopy1.name (gCopy1.object! b.id) == "Phase9 Giant" &&
    gCopy1.power (gCopy1.object! b.id) == 4 &&
    gCopy1.toughness (gCopy1.object! b.id) == 5 &&
    gCopy2.name (gCopy2.object! cl.id) == "Phase9 Giant" &&
    gCopy2.hasTrample (gCopy2.object! cl.id)
  let gRevert := (quiet gCopy2).clearEOT
  let copyRevertClean :=
    gRevert.name (gRevert.object! b.id) == "Event Bear" &&
    gRevert.name (gRevert.object! cl.id) == "Phase9 Clone"
  let gCtrl := (quiet g0).changeControl b me (untilEot := true)
  let gCtrlEnd := (quiet gCtrl).clearEOT
  let layer2PureOk :=
    (gCtrl.object! b.id).controller == some opp &&
    gCtrl.controllerOf (gCtrl.object! b.id) == some me &&
    gCtrlEnd.controllerOf (gCtrlEnd.object! b.id) == some opp
  noPrintedMutation && copyValuesOk && copyRevertClean && layer2PureOk

/- Phase 9 isolation suite (CR 613.3 / 702.73a / 205.3d): Changeling applies
first in Layer 4 as a CDA so a later Layer 4 subtype-replacing effect overwrites
all creature subtypes, and losing `.creature` in Layer 4 strips creature subtypes. -/
#guard
  let changelingDef : CardDef :=
    { creature "Phase9 Changeling" ManaCost.empty #["Shapeshifter"] 2 2 with
      keywords := { changeling := true } }
  let g0 := addPermanent (quiet afterDraw) changelingDef me me
  let ch := (g0.battlefield.filter (·.name == "Phase9 Changeling"))[0]!
  let cdaOk :=
    g0.hasSubtype ch .bear &&
    g0.hasSubtype ch .elf &&
    g0.hasSubtype ch .construct &&
    (g0.snapshot ch).subtypes.contains .bear &&
    (g0.snapshot ch).changeling
  let gOverwrite := g0.createEffect (.replacedCreatureTypesUntilEot ch.id #[.construct, .hero])
  let ch1 := gOverwrite.object! ch.id
  let overwriteOk :=
    gOverwrite.subtypes ch1 == #[.construct, .hero] &&
    !gOverwrite.hasSubtype ch1 .bear &&
    !gOverwrite.hasSubtype ch1 .elf
  let gNonCreature := g0.createEffect (.notACreature ch.id)
  let ch2 := gNonCreature.object! ch.id
  let lostCreatureSubtypesOk :=
    !gNonCreature.isCreature ch2 &&
    (gNonCreature.subtypes ch2).isEmpty
  cdaOk && overwriteOk && lostCreatureSubtypesOk

/- Phase 9 isolation suite (CR 613.7a / 613.7e):
1. A static ability granted by an effect has timestamp
   `max(objectEntryTimestamp, grantingEffectTimestamp)` (CR 613.7a).
2. Reattaching an Equipment updates its attachment timestamp (CR 613.7e) so its
   ability grant overrides an earlier `.losesAbilitiesUntilEot` on the host. -/
#guard
  let kiteDef : CardDef :=
    { name := "Phase9 Kitesail"
      types := #[.artifact]
      subtypes := #["Equipment"]
      staticAbilities := #[.equippedCreatureHasKeywords { flying := true }] }
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear me me)
        hero me me)
      kiteDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let kite := (g0.battlefield.filter (·.name == "Phase9 Kitesail"))[0]!
  let handCount : Int := Int.ofNat (g0.player me).hand.size
  -- CR 613.7a: setBasePT (9, 9) -> grantedStatic powerEqualCardsInHand -> setBasePT (7, 7)
  let g1 := g0.createEffect (.setBasePTUntilEot b.id (9, 9))
  let g2 := g1.createEffect (.grantedStatic b.id .powerEqualCardsInHand)
  let g3 := g2.createEffect (.setBasePTUntilEot b.id (7, 7))
  let grantedTsOk :=
    g1.power (g1.object! b.id) == 9 &&
    g2.power (g2.object! b.id) == handCount &&
    g2.toughness (g2.object! b.id) == 9 &&
    g3.power (g3.object! b.id) == 7 &&
    g3.toughness (g3.object! b.id) == 7
  -- CR 613.7e: attach Kitesail to Bear -> Bear loses abilities -> reattach to Hero then Bear
  let gEq1 := g0.attachSourceTo kite b
  let gEqLost := gEq1.createEffect (.losesAbilitiesUntilEot b.id)
  let gEqOther := gEqLost.attachSourceTo (gEqLost.object! kite.id) (gEqLost.object! h.id)
  let gEqRe := gEqOther.attachSourceTo (gEqOther.object! kite.id) (gEqOther.object! b.id)
  let reattachTsOk :=
    gEq1.hasFlying (gEq1.object! b.id) &&
    !gEqLost.hasFlying (gEqLost.object! b.id) &&
    gEqRe.hasFlying (gEqRe.object! b.id)
  grantedTsOk && reattachTsOk

/- Phase 9 isolation suite (CR 613.8): Dependency ordering overrides timestamp
order across Layer 2 (controller-scoped control change), Layer 3 (chained text
changes), Layer 5 (subtype-scoped color grant vs text change), and Layer 6
(`ObjectScope.creaturesWithout` ability grant vs `AbilityRemoval.all`). -/
#guard
  let opp : PlayerId := ⟨1⟩
  let flyerDef : CardDef :=
    { creature "Phase9 Flyer" ManaCost.empty #["Bird"] 2 2 with
      keywords := { flying := true } }
  let g0 :=
    addPermanent
      (addPermanent (quiet afterDraw) bear opp opp)
      flyerDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let fl := (g0.battlefield.filter (·.name == "Phase9 Flyer"))[0]!
  -- Layer 2: earlier `.creaturesControlledBy me -> opp` waits for later `.objects #[b] -> me`
  let gL2 :=
    (g0.createEffect (.layered (.creaturesControlledBy me) (.control opp) .untilEndOfTurn)).createEffect
      (.layered (.objects #[b.id]) (.control me) .untilEndOfTurn)
  let l2DepOk := gL2.controllerOf (gL2.object! b.id) == some opp
  -- Layer 5: earlier `.permanentsOfSubtype me .bear` color-add + later `.additionalSubtype`
  let gL5 :=
    (g0.createEffect
      (.layered (.permanentsOfSubtype me .bear) (.colors .add (ColorSet.singleton .green)) .untilEndOfTurn)).createEffect
      (.additionalSubtype fl.id .bear)
  let l5DepOk := (gL5.colors (gL5.object! fl.id)).contains .green
  -- Layer 6: earlier `.creaturesWithout flying -> vigilance` waits for later `losesAbilitiesUntilEot`
  let gL6 :=
    (g0.createEffect
      (.layered (.creaturesWithout { flying := true })
        (.abilities { keywords := { vigilance := true } } .none) .untilEndOfTurn)).createEffect
      (.losesAbilitiesUntilEot fl.id)
  let flAfter := gL6.object! fl.id
  let l6DepOk := !gL6.hasFlying flAfter && gL6.hasVigilance flAfter
  l2DepOk && l5DepOk && l6DepOk

/- Phase 9 isolation suite (CR 613.4b–d):
1. Layer 7b timestamp order across `setBasePTUntilEot`, an attached
   `.fra .enchantedIsConstruct55` Aura (5/5), and `cardsInHandPowerUntilEot`.
2. Layer 7c (`pumpPerArtifactUntilEot` and +1/+1 counters) applies after 7b
   regardless of timestamp, and Layer 7d (`ptSwitch`) applies after 7b and 7c. -/
#guard
  let baubleDef : CardDef := { name := "Phase9 Bauble", types := #[.artifact] }
  let constructAuraDef : CardDef := {
    name := "Phase9 Construct Aura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.fra .enchantedIsConstruct55]
  }
  let g0 := addPermanent (addPermanent (quiet afterDraw) bear me me) baubleDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let handCount : Int := Int.ofNat (g0.player me).hand.size
  -- 7b timestamp order: (8, 4) -> attached Construct 5/5 Aura -> handSize -> (3, 6)
  let g7b1 := g0.createEffect (.setBasePTUntilEot b.id (8, 4))
  let g7b2a := addPermanent g7b1 constructAuraDef me me
  let auraObj := (g7b2a.battlefield.filter (·.name == "Phase9 Construct Aura"))[0]!
  let g7b2 := g7b2a.record (GameEvent.attached g7b2a.turnNumber (g7b2a.snapshot auraObj) b.id (cause := .gameRule .spellCast))
  let g7b3 := g7b2.createEffect (.cardsInHandPowerUntilEot b.id)
  let g7b4 := g7b3.createEffect (.setBasePTUntilEot b.id (3, 6))
  let order7bOk :=
    (g7b1.power (g7b1.object! b.id), g7b1.toughness (g7b1.object! b.id)) == (8, 4) &&
    (g7b2.power (g7b2.object! b.id), g7b2.toughness (g7b2.object! b.id)) == (5, 5) &&
    (g7b3.power (g7b3.object! b.id), g7b3.toughness (g7b3.object! b.id)) == (handCount, 5) &&
    (g7b4.power (g7b4.object! b.id), g7b4.toughness (g7b4.object! b.id)) == (3, 6)
  -- 7c (`pumpPerArtifactUntilEot` + +1/+1 counter) created BEFORE 7b `(3, 6)` + 7d `ptSwitch`:
  -- 1 artifact (`Phase9 Bauble`) => +1/+1, +1/+1 counter => +1/+1, so (3+2, 6+2) = (5, 8), switched => (8, 5).
  let gSublayers :=
    (((g0.createEffect (.pumpPerArtifactUntilEot b.id)).addPlusOnePlusOneTo b 1).createEffect
      (.layered (.objects #[b.id]) .ptSwitch .untilEndOfTurn)).createEffect
      (.setBasePTUntilEot b.id (3, 6))
  let sublayersOk :=
    (gSublayers.power (gSublayers.object! b.id), gSublayers.toughness (gSublayers.object! b.id)) == (8, 5)
  order7bOk && sublayersOk

/- Phase 9 isolation suite (CR 302.6): A land played this turn enters with
`status.summoningSick = true`, can tap for mana while noncreature, becomes
summoning-sick (unable to activate `{T}` mana abilities or attack) if animated
into a creature on the same turn without haste, can act when granted haste, and
a creature whose controller changes mid-turn without haste becomes summoning-sick. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let forestDef : CardDef :=
    { name := "Phase9 Forest", types := #[.land], subtypes := #["Forest"], supertypes := #[.basic] }
  let (g0, fObj) := (quiet afterDraw).allocObject forestDef me (.hand me) none
  let gPlayed :=
    match g0.playLand me fObj.id with
    | .ok g' => g'
    | .error _ => g0
  let land := (gPlayed.battlefield.filter (·.name == "Phase9 Forest"))[0]!
  let noncreatureLandOk :=
    land.status.summoningSick &&
    !gPlayed.hasSummoningSickness land &&
    (gPlayed.manaSources me).any (fun (s, _) => s.id == land.id)
  let gAnim := gPlayed.createEffect (.additionalCreature land.id (untilEot := true))
  let animLand := gAnim.object! land.id
  let animatedSickOk :=
    gAnim.isCreature animLand &&
    gAnim.hasSummoningSickness animLand &&
    !(gAnim.manaSources me).any (fun (s, _) => s.id == land.id)
  let gHaste := gAnim.createEffect (.keywordsUntilEot land.id Keyword.haste)
  let hasteLand := gHaste.object! land.id
  let hasteOk :=
    !gHaste.hasSummoningSickness hasteLand &&
    (gHaste.manaSources me).any (fun (s, _) => s.id == land.id)
  -- Creature controlled since start of turn (`summoningSick := false`) changing control mid-turn
  let gCreature0 := addPermanent (quiet afterDraw) bear opp opp
  let b0 := (gCreature0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gCreatureReady := gCreature0
  let gStolen := gCreatureReady.changeControl (gCreatureReady.object! b0.id) me (untilEot := true)
  let controlSickOk :=
    !gCreatureReady.hasSummoningSickness (gCreatureReady.object! b0.id) &&
    gStolen.hasSummoningSickness (gStolen.object! b0.id)
  noncreatureLandOk && animatedSickOk && hasteOk && controlSickOk

/- Phase 9 isolation suite (CR 110.2 / 707.2 / 708.2 / 702.37e):
1. `initialControllerOf` starts from `defaultController` while that player is in
   the game, ignoring stale raw `o.controller` mutations (`none` or another
   player), and falls back cleanly when `defaultController` has left the game.
2. Layer 1 `copiableValues` includes Layer 1b face-down masking: copying a
   face-down permanent produces a nameless colorless 2/2 creature with no
   abilities, while `unmaskedCopiableValues` still exposes the original
   face-down permanent's morph cost. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let morphDef : CardDef :=
    { creature "Phase9 Morph Angel" { symbols := #[.colored .white, .colored .white] } #["Angel"] 5 5 with
      keywords := { flying := true }
      morph := some (ManaCost.ofGeneric 3) }
  let cloneDef : CardDef := creature "Phase9 Copy" ManaCost.empty #["Shapeshifter"] 0 0
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear opp opp)
        morphDef me me)
      cloneDef me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let m := (g0.battlefield.filter (·.name == "Phase9 Morph Angel"))[0]!
  let cl := (g0.battlefield.filter (·.name == "Phase9 Copy"))[0]!
  -- Divergent `o.controller` fixture does not override living `defaultController`
  let gRawNone := g0.change (.materializeObject { b with controller := none } none)
  let gRawMe := g0.change (.materializeObject { b with controller := some me } none)
  let gOppLost := gRawNone.record (GameEvent.playerLost gRawNone.turnNumber opp .conceded)
  let gOppLeft := gOppLost.record (GameEvent.playerLeftGame gOppLost.turnNumber opp)
  let initCtrlOk :=
    gRawNone.controllerOf (gRawNone.object! b.id) == some opp &&
    gRawMe.controllerOf (gRawMe.object! b.id) == some opp &&
    gOppLost.controllerOf (gOppLost.object! b.id) == some opp &&
    gOppLeft.controllerOf (gOppLeft.object! b.id) == none
  -- Face-down permanent copied via `becomeCopyOf` and `createToken` (`copiableValues`)
  let gFd := setFaceDown g0 m.id true
  let gCopied := gFd.becomeCopyOf (gFd.object! cl.id) (gFd.object! m.id) (untilEot := true)
  let (gTok, tok) := gCopied.createToken me (gCopied.copiableValues (gCopied.object! m.id))
  let clAfter := gTok.object! cl.id
  let tokAfter := gTok.object! tok.id
  let mAfter := gTok.object! m.id
  let faceDownCopyOk :=
    !clAfter.status.faceDown &&
    gTok.name clAfter == "" &&
    gTok.power clAfter == 2 &&
    gTok.toughness clAfter == 2 &&
    gTok.colors clAfter == ColorSet.empty &&
    !gTok.hasFlying clAfter &&
    (gTok.activatedAbilitiesOf clAfter).isEmpty &&
    !tokAfter.status.faceDown &&
    gTok.name tokAfter == "" &&
    gTok.power tokAfter == 2 &&
    gTok.toughness tokAfter == 2 &&
    !gTok.hasFlying tokAfter &&
    (gTok.activatedAbilitiesOf tokAfter).isEmpty &&
    (gTok.activatedAbilitiesOf mAfter).size == 1
  initCtrlOk && faceDownCopyOk

/- Phase 9 isolation suite (CR 302.6 edge cases & evaluated battlefield helpers):
1. A no-op `changeControl` on a creature you already controlled since your turn
   began does not cause summoning sickness, nor does expiring a redundant
   control effect while another still gives you control.
2. A scoped `.creaturesControlledBy` control effect causes summoning sickness on
   the turn control changes and clears once the new controller's next turn begins.
3. Noncreature tokens (`createTreasureTokens`) and flickered lands/artifacts
   (`exileThenReturn`) become summoning-sick if animated on the same turn.
4. `chooseCreatureTypeFor`, `returnCreaturesNotOfType`, and
   `chooseCreaturesDestroyRest` evaluate Layer 4 types and subtypes. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let relicDef : CardDef := { name := "Phase9 Relic", types := #[.artifact] }
  let landDef : CardDef :=
    { name := "Phase9 Wastes", types := #[.land] }
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (quiet afterDraw) bear me me)
          hero opp opp)
        relicDef me me)
      landDef me me
  let bMe := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let hOpp := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let relic := (g0.battlefield.filter (·.name == "Phase9 Relic"))[0]!
  let land := (g0.battlefield.filter (·.name == "Phase9 Wastes"))[0]!
  -- 1a. No-op control effect on `me`'s own creature
  let gNoop := g0.changeControl bMe me (untilEot := true)
  let noopOk := !gNoop.hasSummoningSickness (gNoop.object! bMe.id)
  -- 1b. Redundant control effect expiring on `me`'s next turn while permanent control stays active
  let gPermSteal :=
    (g0.changeControl hOpp me).startNextTurn.startNextTurn
  let gRedundant := gPermSteal.changeControl (gPermSteal.object! hOpp.id) me (untilEot := true)
  let gRedundantExp := gRedundant.clearEOT
  let redundantOk :=
    !gPermSteal.hasSummoningSickness (gPermSteal.object! hOpp.id) &&
    !gRedundant.hasSummoningSickness (gRedundant.object! hOpp.id) &&
    gRedundantExp.controllerOf (gRedundantExp.object! hOpp.id) == some me &&
    !gRedundantExp.hasSummoningSickness (gRedundantExp.object! hOpp.id)
  -- 2. Scoped `.creaturesControlledBy opp -> .control me` effect
  let gScoped :=
    g0.createEffect (.layered (.creaturesControlledBy opp) (.control me) .indefinite)
  let gScopedNext := gScoped.startNextTurn.startNextTurn
  let scopedOk :=
    gScoped.controllerOf (gScoped.object! hOpp.id) == some me &&
    gScoped.hasSummoningSickness (gScoped.object! hOpp.id) &&
    gScopedNext.controllerOf (gScopedNext.object! hOpp.id) == some me &&
    !gScopedNext.hasSummoningSickness (gScopedNext.object! hOpp.id)
  -- 3. Treasure token & flickered land animated on the same turn
  let gTr := g0.createTreasureTokens me 1
  let tr := (gTr.battlefield.filter (·.name == "Treasure"))[0]!
  let gTrAnim := gTr.createEffect (.additionalCreature tr.id (untilEot := true))
  let gFlicker := g0.exileThenReturn land "flickers" (land := true)
  let flickLand := (gFlicker.battlefield.filter (·.name == "Phase9 Wastes"))[0]!
  let gFlickAnim := gFlicker.createEffect (.additionalCreature flickLand.id (untilEot := true))
  let noncreatureArrivalOk :=
    !gTr.hasSummoningSickness tr &&
    gTrAnim.hasSummoningSickness (gTrAnim.object! tr.id) &&
    !gFlicker.hasSummoningSickness flickLand &&
    gFlickAnim.hasSummoningSickness (gFlickAnim.object! flickLand.id)
  -- 4. Evaluated Layer 4 types/subtypes in battlefield helpers
  let gTyped :=
    ((gTrAnim.createEffect (.replacedCreatureTypesUntilEot bMe.id #[.elf])).createEffect
      (.additionalCreature relic.id (untilEot := true))).createEffect
      (.notACreature hOpp.id)
  let chosenTypeOk := gTyped.chooseCreatureTypeFor me == .elf
  let gBounced := gTyped.returnCreaturesNotOfType .elf
  let bounceOk :=
    (gBounced.findObject? bMe.id).any (·.isOnBattlefield) &&
    (gBounced.findObject? hOpp.id).any (·.isOnBattlefield) &&
    !(gBounced.findObject? relic.id).any (·.isOnBattlefield)
  let gDestroyed := gTyped.chooseCreaturesDestroyRest #[bMe.id]
  let destroyOk :=
    (gDestroyed.findObject? bMe.id).any (·.isOnBattlefield) &&
    (gDestroyed.findObject? hOpp.id).any (·.isOnBattlefield) &&
    !(gDestroyed.findObject? relic.id).any (·.isOnBattlefield)
  noopOk && redundantOk && scopedOk && noncreatureArrivalOk &&
    chosenTypeOk && bounceOk && destroyOk

/- Phase 9 isolation suite (CR 514.2 / CR 800.4a / CR 800.4c on non-singleton
Layer 2 control effects):
1. `clearEOT` ends `.untilEndOfTurn` and `.untilEndOfNextTurnOf` Layer 2
   control effects across `.creaturesControlledBy`, `.permanentsOfSubtype`,
   `.creaturesWithout`, and multi-id `.objects`, reverting control (and exiling
   under CR 800.4c when the default controller has left the game).
2. `playerLeavesGame` ends scoped Layer 2 control effects via the same
   per-permanent CR 800.4c check: exiling when the default controller already
   left, and keeping the permanent on the battlefield when another scoped
   control effect still gives a living player control. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3p :=
    match Start.start { seats := #[{ name := "P0", deck := testRedDeck },
                                   { name := "P1", deck := testRedDeck },
                                   { name := "P2", deck := testRedDeck }],
                        startingPlayer := some 0, seed := 7 } with
    | .ok g => quiet (keepOpeningHands g 16)
    | .error e => panic! e
  -- 1. Cleanup expires scoped & multi-id `.untilEndOfTurn` and `.untilEndOfNextTurnOf` control effects
  let g0 :=
    addPermanent
      (addPermanent (quiet afterDraw) bear me me)
      hero me me
  let b := (g0.battlefield.filter (·.name == "Event Bear"))[0]!
  let h := (g0.battlefield.filter (·.name == "Event Hero"))[0]!
  let gScopedEot :=
    g0.createEffect (.layered (.creaturesControlledBy me) (.control opp) .untilEndOfTurn)
  let gScopedClean := gScopedEot.clearEOT
  let gWithoutEot :=
    g0.createEffect (.layered (.creaturesWithout Keyword.flying) (.control opp) .untilEndOfTurn)
  let gWithoutClean := gWithoutEot.clearEOT
  let gMultiEot :=
    g0.createEffect (.layered (.objects #[b.id, h.id]) (.control opp) .untilEndOfTurn)
  let gMultiClean := gMultiEot.clearEOT
  let gNextTurnEnd :=
    g0.createEffect (.layered (.permanentsOfSubtype me .bear) (.control opp) (.untilEndOfNextTurnOf opp))
  let gNextTurnEndAfter1 := gNextTurnEnd.clearEOT
  let gNextTurnEndOpp := gNextTurnEndAfter1.startNextTurn
  let gNextTurnEndAfter2 := gNextTurnEndOpp.clearEOT
  let cleanupScopedOk :=
    gScopedEot.controllerOf (gScopedEot.object! b.id) == some opp &&
    gScopedClean.controllerOf (gScopedClean.object! b.id) == some me &&
    gScopedClean.activeEffects.isEmpty &&
    gWithoutEot.controllerOf (gWithoutEot.object! b.id) == some opp &&
    gWithoutClean.controllerOf (gWithoutClean.object! b.id) == some me &&
    gWithoutClean.activeEffects.isEmpty &&
    gMultiEot.controllerOf (gMultiEot.object! b.id) == some opp &&
    gMultiEot.controllerOf (gMultiEot.object! h.id) == some opp &&
    gMultiClean.controllerOf (gMultiClean.object! b.id) == some me &&
    gMultiClean.controllerOf (gMultiClean.object! h.id) == some me &&
    gNextTurnEndAfter1.controllerOf (gNextTurnEndAfter1.object! b.id) == some opp &&
    gNextTurnEndAfter2.controllerOf (gNextTurnEndAfter2.object! b.id) == some me
  -- 2a. Scoped control effect ending when leaving player leaves exiles permanent whose defaultController already left
  let gBribe := addPermanent g3p bear p2 p0
  let bb := (gBribe.battlefield.filter (·.name == "Event Bear"))[0]!
  let gScopedSteal :=
    gBribe.createEffect (.layered (.creaturesWithout Keyword.flying) (.control p1) .indefinite)
  let gP0Left := gScopedSteal.playerLeavesGame p0
  let gP1Left := gP0Left.playerLeavesGame p1
  let scopedLeaveExileOk :=
    gP0Left.controllerOf (gP0Left.object! bb.id) == some p1 &&
    !gP1Left.battlefield.any (·.name == "Event Bear") &&
    gP1Left.objects.any (fun o => o.name == "Event Bear" && o.zone == .exile)
  -- 2b. Singleton control effect ending while a scoped control effect still gives living `p2` control keeps permanent
  let gBoth :=
    (gBribe.createEffect
      (.layered (.creaturesWithout Keyword.flying) (.control p2) .indefinite)).changeControl bb p1
  let gBothP0Left := gBoth.playerLeavesGame p0
  let gBothP1Left := gBothP0Left.playerLeavesGame p1
  let bbSurv := (gBothP1Left.battlefield.filter (·.name == "Event Bear"))[0]?
  let scopedOthersRemainOk :=
    gBothP0Left.controllerOf (gBothP0Left.object! bb.id) == some p1 &&
    bbSurv.isSome &&
    gBothP1Left.controllerOf bbSurv.get! == some p2
  -- 3. CR 800.4m: `.untilEndOfNextTurnOf p1` control effect expires when left player `p1`'s turn would have begun
  let g3pOwn := addPermanent g3p bear p0 p0
  let bOwn := (g3pOwn.battlefield.filter (·.name == "Event Bear"))[0]!
  let gUntilP1End :=
    (g3pOwn.createEffect
      (.layered (.objects #[bOwn.id]) (.control p2) (.untilEndOfNextTurnOf p1))).playerLeavesGame p1
  let gSkippedP1 := gUntilP1End.startNextTurn
  let leftPlayerNextTurnEndOk :=
    gUntilP1End.controllerOf (gUntilP1End.object! bOwn.id) == some p2 &&
    gSkippedP1.activePlayer == p2 &&
    gSkippedP1.controllerOf (gSkippedP1.object! bOwn.id) == some p0
  g3p.players.size == 3 && cleanupScopedOk && scopedLeaveExileOk &&
    scopedOthersRemainOk && leftPlayerNextTurnEndOk

/- Phase 9 isolation suite (peer static preservation when skipping timestamps,
CR 611.2a vs CR 611.2b phasing durations, and CR 202.2 / 612.2 Layer 3 text
substitutions vs mana-derived colors):
1. `evalLayer6Aux` preserves printed and Layer-6-granted static abilities on
   peer permanents when `needStaticsTs == false` and `hasCwStaticEff == true`,
   while suppressing phased-out peers (CR 613.1f / 702.26b).
2. `EffectDuration.untilSourceLeaves` (CR 611.2a / 702.26d) keeps `"until ~
   leaves the battlefield"` copy and control effects active while the source is
   phased out and expires them when the source leaves `.battlefield`, whereas
   `EffectDuration.whileSourceOnBattlefield` (CR 611.2b / 702.26f) suspends
   `"for as long as ~ remains on the battlefield"` effects while phased out.
3. Layer 3 `.replaceColorWord` rewrites color words in rules-text abilities
   (protection, cast-color triggers, target filters) without altering colors
   derived from `manaCost` or `colorIndicator` (CR 202.2 / 612.1 / 612.2). -/
#guard
  let opp : PlayerId := ⟨1⟩
  -- 1. Peer static abilities preserved under `hasCwStaticEff && !needStaticsTs`
  let lordCard : CardDef :=
    { creature "Phase9 Trample Lord" ManaCost.empty #["Beast"] 3 3 with
      staticAbilities := #[.fra .creaturesYouControlHaveTrample] }
  let gPeer0 :=
    addPermanent
      (addPermanent (quiet afterDraw) lordCard me me)
      bear me me
  let lord := (gPeer0.battlefield.filter (·.name == "Phase9 Trample Lord"))[0]!
  let peerBear := (gPeer0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gCw :=
    gPeer0.createEffect
      (.layered (.creaturesWithout Keyword.flying)
        (.abilities { staticAbilities := #[.noMaximumHandSize] } .none) .untilEndOfTurn)
  let gCwPhased := gCw.phaseOut (gCw.object! lord.id)
  let gGrantPeer :=
    ((addPermanent (addPermanent (quiet afterDraw) hero me me) bear me me).createEffect
      (.layered (.objects #[(addPermanent (addPermanent (quiet afterDraw) hero me me) bear me me |>.battlefield.filter (·.name == "Event Hero"))[0]!.id])
        (.abilities { staticAbilities := #[.fra .creaturesYouControlHaveTrample] } .none) .untilEndOfTurn)).createEffect
      (.layered (.creaturesWithout Keyword.flying)
        (.abilities { staticAbilities := #[.noMaximumHandSize] } .none) .untilEndOfTurn)
  let grantBear := (gGrantPeer.battlefield.filter (·.name == "Event Bear"))[0]!
  let peerStaticsOk :=
    gCw.hasTrample (gCw.object! peerBear.id) &&
    (gCw.staticAbilities (gCw.object! lord.id)).contains (.fra .creaturesYouControlHaveTrample) &&
    (gCw.staticAbilities (gCw.object! lord.id)).contains .noMaximumHandSize &&
    !gCwPhased.hasTrample (gCwPhased.object! peerBear.id) &&
    gGrantPeer.hasTrample grantBear
  -- 2. `untilSourceLeaves` vs `whileSourceOnBattlefield` across phasing
  let invCard : CardDef :=
    { name := "Phase9 Secret Invasion", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gPh0 :=
    addPermanent
      (addPermanent
        (addPermanent (quiet afterDraw) bear me me)
        hero opp opp)
      invCard me me
  let host := (gPh0.battlefield.filter (·.name == "Event Bear"))[0]!
  let copied := (gPh0.battlefield.filter (·.name == "Event Hero"))[0]!
  let inv := (gPh0.battlefield.filter (·.name == "Phase9 Secret Invasion"))[0]!
  let gUntil :=
    (gPh0.becomeCopyOf host copied (untilSourceLeaves := some inv.id)).changeControl
      host opp (untilSourceLeaves := some inv.id)
  let gUntilPhased := gUntil.phaseOut (gUntil.object! inv.id)
  let gUntilLeft := gUntilPhased.moveToOwnerGraveyard (gUntilPhased.object! inv.id) "leaves"
  let gWhile :=
    (gPh0.createEffect (.controlWhileSource host.id opp inv.id)).createEffect
      (.hexproofWhileSource host.id inv.id)
  let gWhilePhased := gWhile.phaseOut (gWhile.object! inv.id)
  let phasingDurationOk :=
    (gUntilPhased.object! inv.id).status.phasedOut &&
    gUntilPhased.name (gUntilPhased.object! host.id) == "Event Hero" &&
    gUntilPhased.controllerOf (gUntilPhased.object! host.id) == some opp &&
    gUntilLeft.name (gUntilLeft.object! host.id) == "Event Bear" &&
    gUntilLeft.controllerOf (gUntilLeft.object! host.id) == some me &&
    gWhile.controllerOf (gWhile.object! host.id) == some opp &&
    gWhile.hasHexproof (gWhile.object! host.id) &&
    gWhilePhased.controllerOf (gWhilePhased.object! host.id) == some me &&
    !gWhilePhased.hasHexproof (gWhilePhased.object! host.id)
  -- 3. Layer 3 text substitutions vs mana-cost/color-indicator colors
  let blueMage : CardDef :=
    { bear with
      name := "Phase9 Blue Mage"
      manaCost := { symbols := #[.colored .blue] }
      protectionFromColors := #[.blue]
      triggeredAbilities := #[.onCastColorScry .blue 2] }
  let redGoblin : CardDef :=
    { bear with name := "Phase9 Red Goblin", manaCost := { symbols := #[.colored .red] } }
  let blueMerfolk : CardDef :=
    { bear with name := "Phase9 Blue Merfolk", manaCost := { symbols := #[.colored .blue] } }
  let whiteKnight : CardDef :=
    { bear with name := "Phase9 White Knight", manaCost := { symbols := #[.colored .white] } }
  let critCard : CardDef :=
    { name := "Phase9 Criticism"
      manaCost := { symbols := #[.colored .black] }
      types := #[.instant]
      spellEffect := some .terminalCriticism }
  let gTxt0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent
            (addPermanent (quiet afterDraw) blueMage me me)
            redGoblin opp opp)
          blueMerfolk opp opp)
        whiteKnight opp opp)
      critCard me (.hand me)
  let u := (gTxt0.battlefield.filter (·.name == "Phase9 Blue Mage"))[0]!
  let rSrc := (gTxt0.battlefield.filter (·.name == "Phase9 Red Goblin"))[0]!
  let bSrc := (gTxt0.battlefield.filter (·.name == "Phase9 Blue Merfolk"))[0]!
  let wSrc := (gTxt0.battlefield.filter (·.name == "Phase9 White Knight"))[0]!
  let crit := (gTxt0.handObjects me |>.filter (·.name == "Phase9 Criticism"))[0]!
  let gTxt :=
    (gTxt0.createEffect
      (.layered (.objects #[u.id]) (.text (.replaceColorWord .blue .red)) .untilEndOfTurn)).createEffect
      (.layered (.objects #[crit.id]) (.text (.replaceColorWord .blue .white)) .untilEndOfTurn)
  let critTargets := gTxt.legalSpellTargets me (gTxt.object! crit.id)
  let textColorOk :=
    gTxt.colors (gTxt.object! u.id) == ColorSet.singleton .blue &&
    gTxt.frcProtectedFrom (gTxt.object! u.id) (gTxt.object! rSrc.id) &&
    !gTxt.frcProtectedFrom (gTxt.object! u.id) (gTxt.object! bSrc.id) &&
    gTxt.triggeredAbilities (gTxt.object! u.id) == #[.onCastColorScry .red 2] &&
    gTxt.colors (gTxt.object! crit.id) == ColorSet.singleton .black &&
    critTargets.contains (.permanent wSrc.id) &&
    critTargets.contains (.permanent rSrc.id) &&
    !critTargets.contains (.permanent bSrc.id)
  peerStaticsOk && phasingDurationOk && textColorOk

/- Phase 9 isolation suite (summoning sickness across phasing and arrival zone
continuity, plus `post.snapshot` in `.creatureYouControlDealtDamage` and
`.creatureYouControlTapped`):
1. Phasing a creature out and back in preserves `status.summoningSick` (CR
   302.6 / 702.26d), and `hasSummoningSickness` tracks `o`'s zone across arrival
   rather than pinning `oAt.zone` to `.battlefield` before `o` entered.
2. `matchTriggers` (`.creatureYouControlDealtDamage`) and `becomeTapped`
   (`.creatureYouControlTapped`) build event objects via `snapshot`, so creatures
   controlled via Layer 2 effects and noncreatures animated in Layer 4 queue the
   triggers for their evaluated controller. -/
#guard
  let opp : PlayerId := ⟨1⟩
  -- 1. Summoning sickness across phasing & arrival zone continuity
  let (gHand, handBear) := afterDraw.allocObject bear me (.hand me) none
  let (gArr, arrId) := gHand.putOntoBattlefield handBear.id me
  let gPhOut := gArr.phaseOut (gArr.object! arrId)
  let gPhIn := gPhOut.phaseIn (gPhOut.object! arrId)
  let arrObj := gArr.object! arrId
  let gUntapCleared :=
    gArr.change (.materializeObject { arrObj with status := { arrObj.status with summoningSick := false } } none)
  let (gGobHand, handGob) := afterDraw.allocObject ragingGoblin me (.hand me) none
  let (gGobArr, gobId) := gGobHand.putOntoBattlefield handGob.id me
  let gGobStripped :=
    gGobArr.createEffect (.layered (.objects #[gobId]) (.abilities {} .all) .untilEndOfTurn)
  let gPreExisting := addPermanent afterDraw hero me me
  let preHero := (gPreExisting.battlefield.filter (·.name == "Event Hero"))[0]!
  let gPrePhIn := (gPreExisting.phaseOut preHero).phaseIn ((gPreExisting.phaseOut preHero).object! preHero.id)
  let phaseSickOk :=
    (gPhIn.object! arrId).status.summoningSick &&
    gPhIn.hasSummoningSickness (gPhIn.object! arrId) &&
    !(gUntapCleared.object! arrId).status.summoningSick &&
    gUntapCleared.hasSummoningSickness (gUntapCleared.object! arrId) &&
    !gGobArr.hasSummoningSickness (gGobArr.object! gobId) &&
    gGobStripped.hasSummoningSickness (gGobStripped.object! gobId) &&
    !gPrePhIn.hasSummoningSickness (gPrePhIn.object! preHero.id)
  -- 2. `.creatureYouControlDealtDamage` and `.creatureYouControlTapped` with Layer 2 & Layer 4
  let dmgWatchAb : TriggeredAbility := .triggered .fromEffect Effect.watchSheHulkRedirectOnce {}
  let tapWatchAb : TriggeredAbility := .triggered .fromEffect Effect.watchFirstTapUntap {}
  let watcherDef : CardDef :=
    { name := "Phase9 Damage Tap Watcher"
      manaCost := ManaCost.empty
      types := #[.enchantment]
      triggeredAbilities := #[dmgWatchAb, tapWatchAb] }
  let relicDef : CardDef :=
    { name := "Phase9 Animated Relic", manaCost := ManaCost.empty, types := #[.artifact] }
  let gW0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (quiet afterDraw) watcherDef me me)
          watcherDef opp opp)
        bear opp opp)
      relicDef me me
  let oppBear := (gW0.battlefield.filter (·.name == "Event Bear"))[0]!
  let relic := (gW0.battlefield.filter (·.name == "Phase9 Animated Relic"))[0]!
  let gLayered :=
    (gW0.createEffect (.layered (.objects #[oppBear.id]) (.control me) .untilEndOfTurn)).createEffect
      (.additionalCreature relic.id (untilEot := true))
  let cause1 : EventCause := .oneShotEffect (some ⟨201⟩) none (some me)
  let gDmgStolen :=
    gLayered.withBatch (some cause1) fun g =>
      let target := g.object! oppBear.id
      g.dealDamageToPermanent target 1 (source := some (g.snapshot target)) (cause := some cause1)
  let gDmgAnim :=
    gLayered.withBatch (some cause1) fun g =>
      let target := g.object! relic.id
      g.dealDamageToPermanent target 1 (source := some (g.snapshot target)) (cause := some cause1)
  let gTapStolen :=
    gLayered.withBatch (some cause1) fun g =>
      g.becomeTapped (g.object! oppBear.id) (cause := some cause1)
  let gTapAnim :=
    gLayered.withBatch (some cause1) fun g =>
      g.becomeTapped (g.object! relic.id) (cause := some cause1)
  let dmgAndTapSnapOk :=
    (gLayered.object! oppBear.id).controller == some opp &&
    gDmgStolen.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == dmgWatchAb) &&
    !gDmgStolen.waitingTriggers.any (fun wt => wt.controller == opp && wt.ability == dmgWatchAb) &&
    gDmgAnim.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == dmgWatchAb) &&
    gTapStolen.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == tapWatchAb) &&
    gTapAnim.waitingTriggers.any (fun wt => wt.controller == me && wt.ability == tapWatchAb)
  phaseSickOk && dmgAndTapSnapOk

/- Phase 10 isolation:
1. `ManaPool` stores `ManaUnit` provenance (`source` and `restriction`, CR 106.4 /
   106.6) across `manaAdded`, `manaEmptied` (`keptColorless := true` under
   `unspentManaBecomesColorless`), and `manaSpent` (`treasureManaSpentOn` and
   `legendaryManaSpentOn`).
2. `shuffleLibrary` emits `PlayerEvent.shuffled` even on 0-card and 1-card
   libraries (CR 701.24e), and `closeBatch` emits `PlayerEvent.gainedDesignation`
   inside the closing batch.
3. `.fraEmblem` expiration emits `ZoneEvent.ceasedToExist` alongside a pure
   `applyContinuousEffectEvent` table update, and `ringBearerId` is the single
   stored Ring-bearer source of truth.
4. `DelayedTriggerEvent` (`created`, one-shot `consumed`, duration `expired`)
   records explicit `EventCause` provenance on every transition.
5. CR 608.2n / 608.2p / 608.3 mid-resolution stack residency keeps resolving
   spells on `g.stack` across `Pending` pauses, excludes self-targeting on the
   stack (CR 115.5), handles mid-resolution self-exile without moving to the
   graveyard, emits `StackObjectEvent.resolved` on completion, and drains
   `g.continuations` back to `#[]`. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let p10Cause : EventCause := .oneShotEffect (some ⟨1001⟩) none (some me)
  -- 1. `ManaUnit` provenance across `manaAdded`, `manaEmptied` (`keptColorless := true`), and `manaSpent`
  let horizonDef : CardDef :=
    { (creature "Phase10 Horizon" ManaCost.empty #["Rogue"] 3 3) with
      unspentManaBecomesColorless := true }
  let gTr0 := (addPermanent (quiet afterDraw) horizonDef me me).createTreasureTokens me 1 (cause := some p10Cause)
  let trObj := (gTr0.battlefield.filter (·.printed.isToken))[0]!
  let gTrMana :=
    match gTr0.tapForMana me trObj.id (.colored .green) with
    | .ok g' => g'
    | .error _ => gTr0
  let unitLeg : ManaUnit :=
    { mana := .colored .green
      source := none
      restriction := some .legendarySpell }
  let gManaAdded := gTrMana.record (GameEvent.manaAdded gTrMana.turnNumber me #[unitLeg] (cause := some p10Cause))
  let gManaConv := gManaAdded.emptyManaPools
  let convUnits := (gManaConv.player me).manaPool.units
  let targetSpellId : ObjectId := ⟨7777⟩
  let gManaSpent := gManaConv.record (GameEvent.manaSpent gManaConv.turnNumber me convUnits targetSpellId)
  let manaProvenanceOk :=
    convUnits.size == 2 &&
    convUnits.all (·.mana == .colorless) &&
    convUnits[0]!.source == some trObj.id &&
    convUnits[1]!.restriction == some .legendarySpell &&
    gManaConv.events.any (fun e =>
      match e.change with
      | .rules (.player (.manaEmptied p us true)) =>
        p == me && us.size == 2 && us[0]!.source == some trObj.id &&
          us[1]!.restriction == some .legendarySpell
      | _ => false) &&
    GameEvent.treasureManaSpentOn gManaSpent.events targetSpellId &&
    GameEvent.legendaryManaSpentOn gManaSpent.events targetSpellId
  -- 2. 0-card and 1-card `PlayerEvent.shuffled` (CR 701.24e) and `gainedDesignation` inside `closeBatch`
  let gEmptyLib0 :=
    quiet ((afterDraw.player me).library.foldl (fun acc id => (acc.move id .exile none (cause := some p10Cause)).1) afterDraw)
  let gShuf0 := gEmptyLib0.shuffleLibrary me
  let (gOneAlloc, oneRaw) := gEmptyLib0.allocObject bear me (.outside me) none
  let (gOneLib0, oneCardId) := gOneAlloc.move oneRaw.id (.library me) none (cause := some p10Cause)
  let gShuf1 := (quiet gOneLib0).shuffleLibrary me
  let storiedDef : CardDef :=
    { name := "Phase10 Storied Relic"
      manaCost := ManaCost.empty
      types := #[.artifact]
      keywords := Keyword.storied }
  let (gStoryH1, sCard1) := afterDraw.allocObject storiedDef me (.hand me) none
  let (gStoryH2, sCard2) := gStoryH1.allocObject storiedDef me (.hand me) none
  let (gStoryH3, sCard3) := gStoryH2.allocObject storiedDef me (.hand me) none
  let gStoryDone :=
    (quiet gStoryH3).withBatch (some p10Cause) fun g =>
      let (g, _) := g.putOntoBattlefield sCard1.id me (cause := some p10Cause)
      let (g, _) := g.putOntoBattlefield sCard2.id me (cause := some p10Cause)
      (g.putOntoBattlefield sCard3.id me (cause := some p10Cause)).1
  let shufAndDesigOk :=
    gShuf0.pending == .none &&
    gShuf0.events.any (fun e =>
      match e.change with
      | .rules (.player (.shuffled p ord)) => p == me && ord.isEmpty
      | _ => false) &&
    gShuf1.pending == .none &&
    gShuf1.events.any (fun e =>
      match e.change with
      | .rules (.player (.shuffled p ord)) => p == me && ord == #[oneCardId]
      | _ => false) &&
    (gStoryDone.player me).enduringStory &&
    gStoryDone.events.any (fun e =>
      match e.change with
      | .rules (.player (.gainedDesignation p .enduringStory)) => p == me && e.batch.any (·.raw > 0)
      | _ => false)
  -- 3. `.fraEmblem` expiration (`ZoneEvent.ceasedToExist` + pure `applyContinuousEffectEvent`) & `ringBearerId`
  let (gEmb0, embObj) := (quiet afterDraw).allocObject
    { name := "Phase10 Emblem", types := #[] } me .command (some me)
  let embEffId : EffectId := ⟨1050⟩
  let gEmbCreated :=
    gEmb0.record (GameEvent.effectCreated gEmb0.turnNumber embEffId
      (.fraEmblemUntilTurnOf embObj.id opp) p10Cause)
  let gEmbPureApplier :=
    gEmbCreated.applyChange (.rules (.continuousEffect (.expired embEffId)))
  let gEmbExpired := gEmbCreated.expireEffectById embEffId (cause := some (.turnBased .expireAtStepBegin))
  let gRing0 := addPermanent (quiet afterDraw) bear me me
  let ringBear := (gRing0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gRing1 := gRing0.record (GameEvent.ringTempted gRing0.turnNumber me (some ringBear.id) 1 (cause := some p10Cause))
  let emblemAndRingOk :=
    !gEmbPureApplier.activeEffects.any (·.1 == embEffId) &&
    (gEmbPureApplier.findObject? embObj.id).isSome &&
    !gEmbExpired.activeEffects.any (·.1 == embEffId) &&
    (gEmbExpired.findObject? embObj.id).isNone &&
    gEmbExpired.events.any (fun e =>
      match e.change with
      | .rules (.zone (.ceasedToExist eo)) => eo.id == some embObj.id
      | _ => false) &&
    (gRing1.player me).ringBearerId == some ringBear.id &&
    gRing1.isRingBearer me (gRing1.object! ringBear.id)
  -- 4. `DelayedTriggerEvent` (`created`, one-shot `consumed`, duration `expired`) + cause totality
  let gDt0 := addPermanent (addPermanent (quiet afterDraw) bear me me) hero me me
  let dtBear := (gDt0.battlefield.filter (·.name == "Event Bear"))[0]!
  let dtHero := (gDt0.battlefield.filter (·.name == "Event Hero"))[0]!
  let dtOneShot : DelayedTrigger :=
    { controller := me, source := some dtHero, kind := .endStepSacrifice dtBear.id, cause := p10Cause }
  let dtUntilEot : DelayedTrigger :=
    { controller := me, source := some dtHero, kind := .attackPumpPerPlains, cause := p10Cause }
  let gDtReg := ((gDt0.registerDelayedTrigger dtOneShot).registerDelayedTrigger dtUntilEot).record
    (GameEvent.stepBegan gDt0.turnNumber .postcombatMain gDt0.activePlayer)
  let gDtConsumed := gDtReg.beginStep .end
  let gDtExpired := gDtConsumed.clearTurnActivations
  let delayedTriggerEventsOk :=
    gDtReg.events.any (fun e =>
      match e.change with
      | .rules (.delayedTrigger (.created dt)) => dt == dtOneShot
      | _ => false) &&
    gDtConsumed.events.any (fun e =>
      match e.change with
      | .rules (.delayedTrigger (.consumed dt)) => dt == dtOneShot
      | _ => false) &&
    !gDtConsumed.delayedTriggers.any (·.kind == .endStepSacrifice dtBear.id) &&
    gDtConsumed.delayedTriggers.any (·.kind == .attackPumpPerPlains) &&
    gDtExpired.events.any (fun e =>
      match e.change with
      | .rules (.delayedTrigger (.expired dt)) => dt == dtUntilEot
      | _ => false) &&
    gDtExpired.delayedTriggers.isEmpty &&
    allRulesEventsClassified gDtExpired
  -- 5. CR 608.2n / 608.2p / 608.3 mid-resolution stack residency, CR 115.5, self-exile, and `continuations == #[]`
  let scrySpellDef : CardDef :=
    { name := "Phase10 Scry Instant"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellEffect := some (Effect.scry 2) }
  let (gSp0, spObj) := (quiet afterDraw).allocObject scrySpellDef me .stack (some me)
  let gSpOnStack := gSp0.putStackEntry me spObj.id
  let gSpMid := gSpOnStack.resolveTop
  let midStackOk :=
    (match gSpMid.pending with | .scry p 2 _ => p == me | _ => false) &&
    gSpMid.stack.any (·.objectId == spObj.id) &&
    (gSpMid.findObject? spObj.id).any (·.zone == .stack) &&
    gSpMid.resolvingSpell == some spObj.id &&
    !gSpMid.continuations.isEmpty &&
    !(gSpMid.legalStackSpellTargets (fun _ => true) (some spObj.id)).contains (.card spObj.id) &&
    !gSpMid.events.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved ..)) => true
      | _ => false)
  let keepScry2 (g : Game) : Game :=
    match g.apply me (.scry (g.scryLookedIds me 2) #[]) with
    | .ok g' => g'
    | .error _ => g
  let gSpDone := keepScry2 gSpMid
  let doneStackOk :=
    gSpDone.pending == .none &&
    gSpDone.stack.isEmpty &&
    gSpDone.continuations.isEmpty &&
    gSpDone.resolvingSpell.isNone &&
    gSpDone.objects.any (fun o => o.name == "Phase10 Scry Instant" && o.zone == .graveyard me) &&
    gSpDone.events.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved eo ..)) => eo.id == some spObj.id
      | _ => false) &&
    allRulesEventsClassified gSpDone
  let (gSpMidExiled, exiledSpId) := gSpMid.move spObj.id .exile none (cause := some p10Cause)
  let gSpSelfExileDone := keepScry2 gSpMidExiled
  let selfExileOk :=
    gSpSelfExileDone.stack.isEmpty &&
    gSpSelfExileDone.continuations.isEmpty &&
    (gSpSelfExileDone.findObject? exiledSpId).any (·.zone == .exile) &&
    !gSpSelfExileDone.objects.any (fun o => o.name == "Phase10 Scry Instant" && o.zone == .graveyard me) &&
    gSpSelfExileDone.events.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved eo ..)) => eo.id == some spObj.id
      | _ => false) &&
    allRulesEventsClassified gSpSelfExileDone
  manaProvenanceOk &&
    shufAndDesigOk &&
    emblemAndRingOk &&
    delayedTriggerEventsOk &&
    midStackOk &&
    doneStackOk &&
    selfExileOk &&
    allRulesEventsClassified gManaSpent &&
    noOneShotCauses gShuf0 &&
    gShuf0.nextEffectId == gEmptyLib0.nextEffectId &&
    noOneShotCauses gShuf1 &&
    gShuf1.nextEffectId == gOneLib0.nextEffectId &&
    allRulesEventsClassified gStoryDone &&
    allRulesEventsClassified gEmbExpired &&
    allRulesEventsClassified gRing1

/- Phase 10 review-invariant suite:
1. Painland `activateManaAbility` records `.gameRule .abilityActivated` on life loss without bumping `nextEffectId` (even inside `withResolvingContext`).
2. `applyPermanentAction` (`.untap`, `.doubleStrikeCounter`, `.tapAndStun`) and `replaceUntap` / `wrapReplacedCause` outside `withResolvingContext` record non-one-shot causes and leave `nextEffectId` unchanged.
3. `temptWithTheRing`, `finishScry`, `finishSurveil`, and `supplyOrder` leave `nextEffectId` unchanged outside `withResolvingContext` and share one minted `EffectId` inside `withResolvingContext`.
4. `shuffleLibrary` on a 2+-card library transitions to `Pending.resolveRandom (.shuffleLibrary p)` even if `g.pending != .none`, and `shuffleThen` chains `PendingReplacement.shuffleThen` behind an as-enters choice instead of recording an unrandomized order.
5. `beholdAndMaybeUntap` mints two distinct `EffectId`s across its two instructions ("Behold X. If you do, untap") when resolving and allocates zero `EffectId`s outside resolution.
6. `becomePrepared`, `unprepare` (`.gameRule .spellCast`), and `phaseOut` (`.turnBased .phaseInOut`) allocate zero one-shot `EffectId`s outside `withResolvingContext` and share one `EffectId` inside `withResolvingContext`.
7. `Start.start` and `allocObject` / `insertObject` materialize objects via `EngineChange.materializeObject` without emitting `ZoneEvent.created`, driving tier-3 `materializedAt` timestamps and `hasSummoningSickness`. -/
#guard
  -- 1. Painland mana ability life-loss cause
  let painLandDef : CardDef :=
    { name := "Phase10 Painland"
      types := #[.land]
      tapAddOneOfDealsDamage := some (#[.colored .red, .colored .white], 1) }
  let gPain0 := quiet (addPermanent afterDraw painLandDef me me)
  let painObj := (gPain0.battlefield.filter (·.name == "Phase10 Painland"))[0]!
  let gPainQuiet :=
    match gPain0.activateManaAbility me painObj.id 0 #[.colored .red] with
    | .ok g' => g'
    | .error _ => gPain0
  let gPainRes :=
    gPain0.withResolvingContext (some painObj.id) me (fun g =>
      match g.activateManaAbility me painObj.id 0 #[.colored .red] with
      | .ok g' => g'
      | .error _ => g)
  let painCauses (g : Game) :=
    g.events.filterMap (fun e =>
      match e.change with
      | .rules (.life (.lost ..)) => e.cause?
      | _ => none)
  let painOk :=
    gPainQuiet.nextEffectId == gPain0.nextEffectId &&
    painCauses gPainQuiet == #[.gameRule .abilityActivated] &&
    gPainRes.nextEffectId == gPain0.nextEffectId &&
    painCauses gPainRes == #[.gameRule .abilityActivated] &&
    noOneShotCauses gPainQuiet &&
    noOneShotCauses gPainRes
  -- 2. `applyPermanentAction` and stun-counter `replaceUntap` outside resolution
  let gAct0 :=
    let g := addPermanent afterDraw bear me me
    let bid := (g.battlefield.filter (·.name == "Event Bear"))[0]!.id
    quiet (setTapped (g.recordPutCounters bid .stun 1) bid true)
  let actBear := (gAct0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gUntapStun := gAct0.applyPermanentAction actBear .untap
  let gDbl := gAct0.applyPermanentAction actBear .doubleStrikeCounter
  let gTapStun := gAct0.applyPermanentAction actBear .tapAndStun
  let stunCauses :=
    gUntapStun.events.filterMap (fun e =>
      match e.change with
      | .rules _ => e.cause?
      | _ => none)
  let permActionOk :=
    gUntapStun.nextEffectId == gAct0.nextEffectId &&
    stunCauses == #[.replaced { kind := .stunCounterUntap, object := some actBear.id } (.turnBased .untapAll)] &&
    gDbl.nextEffectId == gAct0.nextEffectId &&
    gTapStun.nextEffectId == gAct0.nextEffectId &&
    noOneShotCauses gUntapStun &&
    noOneShotCauses gDbl &&
    noOneShotCauses gTapStun
  -- 3. `temptWithTheRing`, `finishScry`, `finishSurveil`, `supplyOrder` outside vs inside resolution
  let gRingQuiet := gAct0.temptWithTheRing me
  let gRingRes := gAct0.withResolvingContext (some actBear.id) me (fun g => g.temptWithTheRing me)
  let ringResIds := (GameEvent.oneShotEffectsWithId gRingRes.events).map Prod.fst
  let gScry0 := (gAct0.beginScry me 1)
  let gScryQuiet :=
    match gScry0.finishScry me (gScry0.scryLookedIds me 1) #[] with
    | .ok g' => g'
    | .error _ => gScry0
  let gSurv0 := (gAct0.beginSurveil me 1)
  let gSurvQuiet :=
    match gSurv0.finishSurveil me #[] (gSurv0.scryLookedIds me 1) with
    | .ok g' => g'
    | .error _ => gSurv0
  let resolvingHelpersOk :=
    gRingQuiet.nextEffectId == gAct0.nextEffectId &&
    gRingRes.nextEffectId == gAct0.nextEffectId + 1 &&
    ringResIds.size == 2 &&
    ringResIds[0]! == ringResIds[1]! &&
    gScryQuiet.nextEffectId == gAct0.nextEffectId &&
    gSurvQuiet.nextEffectId == gAct0.nextEffectId &&
    noOneShotCauses gRingQuiet &&
    noOneShotCauses gScryQuiet &&
    noOneShotCauses gSurvQuiet
  -- 4. `shuffleLibrary` with `pending != .none` and `shuffleThen` behind an as-enters choice
  let gPending2 := gAct0.change (.pending (.scry me 1 1))
  let gShufWhilePending := gPending2.shuffleLibrary me
  let roomDef : CardDef :=
    { name := "Phase10 Room"
      types := #[.land]
      staticAbilities := #[.fra .entersTappedChooseColor] }
  let gSearchAsEnters0 := quiet (insertObject afterDraw roomDef me (.library me))
  let roomLibId := ((gSearchAsEnters0.player me).library.filter (fun id => (gSearchAsEnters0.object! id).name == "Phase10 Room"))[0]!
  let gSearchAsEntersMid :=
    gSearchAsEnters0.withResolvingContext none me (fun g =>
      g.finishLibrarySearch me #[roomLibId] (.battlefield true) none "land card")
  let midNoPrematureShuffled :=
    (match gSearchAsEntersMid.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => match c.kind with | .asEntersChooseColor _ => true | _ => false)
     | _ => false) &&
    !gSearchAsEntersMid.events.any (fun e =>
      match e.change with | .rules (.player (.shuffled ..)) => true | _ => false)
  let gSearchAfterColor :=
    match gSearchAsEntersMid.apply me (.chooseMode 1) with
    | .ok g' => g'
    | .error _ => gSearchAsEntersMid
  let shuffleGuardOk :=
    (gAct0.player me).library.size > 1 &&
    gShufWhilePending.pending == .resolveRandom (.shuffleLibrary me) &&
    !gShufWhilePending.events.any (fun e =>
      match e.change with | .rules (.player (.shuffled ..)) => true | _ => false) &&
    midNoPrematureShuffled &&
    gSearchAfterColor.pending == .resolveRandom (.shuffleLibrary me)
  -- 5. `beholdAndMaybeUntap` mints two distinct `EffectId`s when resolving and zero outside resolution
  let dragonLandDef : CardDef :=
    { name := "Phase10 Dragon Roost"
      types := #[.land] }
  let dragonCreatureDef : CardDef :=
    creature "Phase10 Dragon" ManaCost.empty #["Dragon"] 4 4
  let gBeh0 :=
    let g := addPermanent (addPermanent afterDraw dragonLandDef me me) dragonCreatureDef me me
    let lid := (g.battlefield.filter (·.name == "Phase10 Dragon Roost"))[0]!.id
    quiet (setTapped g lid true)
  let dLand := (gBeh0.battlefield.filter (·.name == "Phase10 Dragon Roost"))[0]!
  let gBehQuiet := gBeh0.beholdAndMaybeUntap me dLand.id .dragon
  let gBehRes := gBeh0.withResolvingContext (some dLand.id) me (fun g =>
    g.beholdAndMaybeUntap me dLand.id .dragon)
  let behResIds := (GameEvent.oneShotEffectsWithId gBehRes.events).map Prod.fst
  let beholdUntapOk :=
    gBehQuiet.nextEffectId == gBeh0.nextEffectId &&
    !(gBehQuiet.object! dLand.id).status.tapped &&
    gBehRes.nextEffectId == gBeh0.nextEffectId + 2 &&
    behResIds.size == 2 &&
    behResIds[0]! != behResIds[1]! &&
    noOneShotCauses gBehQuiet &&
    allRulesEventsClassified gBehRes
  -- 6. `becomePrepared`, `unprepare`, and `phaseOut` outside vs inside resolution
  let prepDef : CardDef :=
    { creature "Phase10 Prepared" ManaCost.empty #["Knight"] 2 2 with
      prepareFace := some { name := "Phase10 Seed" } }
  let gPrep0 := quiet (addPermanent afterDraw prepDef me me)
  let prepObj := (gPrep0.battlefield.filter (·.name == "Phase10 Prepared"))[0]!
  let gPrepQuiet := gPrep0.becomePrepared prepObj
  let prepQuietOneShots := GameEvent.oneShotEffectsWithId gPrepQuiet.events
  let gUnprepQuiet := (quiet gPrepQuiet).unprepare (gPrepQuiet.object! prepObj.id)
  let unprepCauses :=
    gUnprepQuiet.events.filterMap (fun e =>
      match e.change with
      | .rules (.permanent (.designation _ .prepared false)) => e.cause?
      | _ => none)
  let gPrepRes := gPrep0.withResolvingContext (some prepObj.id) me (fun g => g.becomePrepared prepObj)
  let prepResIds := (GameEvent.oneShotEffectsWithId gPrepRes.events).map Prod.fst
  let prepEffOneShots :=
    gPrepRes.events.filterMap (fun e =>
      match e.change with
      | .rules (.continuousEffect (.created ..)) => e.cause?.bind EventCause.oneShotEffectId?
      | _ => none)
  let gPhaseQuiet := gPrep0.phaseOut prepObj
  let gPhaseRes := gPrep0.withResolvingContext (some prepObj.id) me (fun g => g.phaseOut prepObj)
  let phaseResIds := (GameEvent.oneShotEffectsWithId gPhaseRes.events).map Prod.fst
  let prepAndPhaseOk :=
    prepQuietOneShots.isEmpty &&
    gUnprepQuiet.nextEffectId == gPrepQuiet.nextEffectId &&
    unprepCauses == #[.gameRule .spellCast] &&
    prepResIds.size == 2 &&
    prepResIds[0]! == prepResIds[1]! &&
    prepEffOneShots == #[prepResIds[0]!] &&
    gPhaseQuiet.nextEffectId == gPrep0.nextEffectId &&
    gPhaseRes.nextEffectId == gPrep0.nextEffectId + 1 &&
    phaseResIds.size == 1 &&
    noOneShotCauses gPrepQuiet &&
    noOneShotCauses gUnprepQuiet &&
    noOneShotCauses gPhaseQuiet &&
    allRulesEventsClassified gPhaseRes
  -- 7. `allocObject` / `insertObject` materialize via `EngineChange.materializeObject` (0 `ZoneEvent.created`, tier-1 timestamps)
  let auraDef : CardDef := enchantment "Phase10 Aura" ManaCost.empty "Enchant creature"
  let gTs0 := insertObject (quiet started) bear me .battlefield (some me)
    { summoningSick := true, counters := #[(.plusOnePlusOne, 1)] }
  let tsBear := (gTs0.battlefield.filter (·.name == "Event Bear"))[0]!
  let (gTs1, tsAura) := gTs0.allocObject auraDef me .battlefield (some me) (attachedTo := some tsBear.id)
  let hasZoneCreated (evs : Array GameEvent) : Bool :=
    evs.any (fun e => match e.change with | .rules (.zone (.created ..)) => true | _ => false)
  let createdTsOk :=
    !hasZoneCreated started.events &&
    !hasZoneCreated gTs1.events &&
    (gTs1.objectEntryTimestamp tsBear).1 == 1 &&
    (gTs1.counterTimestamp tsBear.id .plusOnePlusOne).1 == 1 &&
    (gTs1.attachmentTimestamp tsAura tsBear.id).1 == 1 &&
    gTs1.hasSummoningSickness tsBear &&
    noOneShotCauses started &&
    noOneShotCauses gTs1
  -- 8. Round-2 continuation-frame & 0-card `shuffleThen` invariants:
  --    (a) `requestShuffle` with `after != .none` on a quiet board keeps `afterRandom` without minting `EffectId`
  --    (b) 0-card remaining library `shuffleThen` behind an as-enters choice waits for the choice before shuffling or running `onDone`
  --    (c) `applyGainLifeSearchBasicPlusOne` on a quiet board keeps `plusOneAfterSearch` and adds the +1/+1 counter without minting `EffectId`
  let gEmptyForReq :=
    quiet ((afterDraw.player me).library.foldl (fun acc id => (acc.move id .exile none (cause := some testCause)).1) afterDraw)
  let gReq0 := gEmptyForReq.requestShuffle me (.gainLife me 1)
  let gReqMany := gAct0.requestShuffle me (.gainLife me 1)
  let gReqManyDone :=
    match gReqMany.supplyOrder (gReqMany.player me).library with
    | .ok g' => g'
    | .error _ => gReqMany
  let gZeroAfterSearch0 :=
    let g := addPermanent gEmptyForReq dragonCreatureDef me me
    quiet (insertObject g roomDef me (.library me))
  let onlyRoomId := (gZeroAfterSearch0.player me).library[0]!
  let gZeroMid :=
    gZeroAfterSearch0.finishLibrarySearch me #[onlyRoomId] (.battlefieldTappedBeholdUntap .dragon) none "land card"
  let zeroMidDeferred :=
    (match gZeroMid.pending with
     | .chooseReplacement p cs =>
       p == me && cs.any (fun c => match c.kind with | .asEntersChooseColor _ => true | _ => false)
     | _ => false) &&
    !gZeroMid.events.any (fun e =>
      match e.change with
      | .rules (.player (.shuffled ..)) => true
      | .rules (.player (.beheld ..)) => true
      | _ => false)
  let gZeroDone :=
    match gZeroMid.apply me (.chooseMode 1) with
    | .ok g' => g'
    | .error _ => gZeroMid
  let basicPlainsDef : CardDef :=
    { name := "Plains", types := #[.land], supertypes := #[.basic], subtypes := #["Plains"] }
  let gRestTech0 :=
    let g := addPermanent gEmptyForReq bear me me
    quiet (insertObject g basicPlainsDef me (.library me))
  let restBear := (gRestTech0.battlefield.filter (·.name == "Event Bear"))[0]!
  let basicLibId := (gRestTech0.player me).library[0]!
  let gRestMid :=
    gRestTech0.applyGainLifeSearchBasicPlusOne me #[.player me, .permanent restBear.id] 2
  let gRestDone :=
    match gRestMid.answerFraChoice me (.objects #[basicLibId]) with
    | .ok g' => g'
    | .error _ => gRestMid
  let round2ContinuationOk :=
    gReq0.afterRandom == .gainLife me 1 &&
    gReq0.nextEffectId == gEmptyForReq.nextEffectId &&
    noOneShotCauses gReq0 &&
    gReqMany.afterRandom == .gainLife me 1 &&
    gReqManyDone.nextEffectId == gAct0.nextEffectId &&
    noOneShotCauses gReqManyDone &&
    zeroMidDeferred &&
    gZeroDone.events.any (fun e => match e.change with | .rules (.player (.shuffled ..)) => true | _ => false) &&
    gZeroDone.events.any (fun e => match e.change with | .rules (.player (.beheld _ .dragon)) => true | _ => false) &&
    gZeroDone.nextEffectId == gZeroMid.nextEffectId &&
    noOneShotCauses gZeroDone &&
    (gRestDone.object! restBear.id).status.plusOnePlusOne == 1 &&
    gRestDone.nextEffectId == gRestTech0.nextEffectId &&
    noOneShotCauses gRestDone
  painOk &&
    permActionOk &&
    resolvingHelpersOk &&
    shuffleGuardOk &&
    beholdUntapOk &&
    prepAndPhaseOk &&
    createdTsOk &&
    round2ContinuationOk

-- Phase 11: Non-token materialization vs `ZoneEvent.created`, `Game.snapshot`
-- Layer 1–7 snapshots, CR 614.12 / 702.34a replacements, `*/*` CDA creature
-- spells on the stack, and CR 702.73a off-battlefield changeling search/behold.
#guard
  let hasCreated (evs : Array GameEvent) : Bool :=
    evs.any fun e => match e.change with | .rules (.zone (.created ..)) => true | _ => false
  let hasMaterialized (evs : Array GameEvent) : Bool :=
    evs.any fun e => match e.change with | .engine (.materializeObject ..) => true | _ => false
  -- 1. Materialization vs `ZoneEvent.created` isolation
  let gSb0 := quiet (afterDraw.change (.player me (.sideboard #[bear])))
  let gSb1 := gSb0.materializeSideboard me
  let gEmb := (quiet afterDraw).createCommandObject me { name := "Phase11 Emblem", types := #[] }
  let actBearDef : CardDef := {
    bear with
    activatedAbilities := #[{ cost := {}, effect := {} }]
  }
  let gAb0 := quiet (addPermanent afterDraw actBearDef me me)
  let baseBear := (gAb0.battlefield.filter (·.name == "Event Bear"))[0]!
  let gAbStack := gAb0.putTriggeredAbilityOnStack me baseBear (.onEnterDraw 1) "enters"
  let gActStack :=
    match gAb0.activateAbility me baseBear.id 0 with
    | .ok g => g
    | .error _ => gAb0
  let (gTok, _) := gAb0.createToken me treasureToken
  let gPrepCopy := gAb0.createPreparedCopy baseBear { name := "Phase11 Seed" }
  let hasTrigPut (evs : Array GameEvent) : Bool :=
    evs.any fun e => match e.change with | .rules (.triggerQueue (.putOnStack ..)) => true | _ => false
  let materializeIsolationOk :=
    !hasCreated started.events && hasMaterialized started.events &&
    !hasCreated gSb1.events && hasMaterialized gSb1.events &&
    !hasCreated gEmb.events && hasMaterialized gEmb.events &&
    !hasCreated gAbStack.events && hasTrigPut gAbStack.events &&
    !hasCreated gActStack.events && hasMaterialized gActStack.events &&
    hasCreated gTok.events &&
    hasCreated gPrepCopy.events
  -- 2. `Game.snapshot` planeswalker loyalty, `attached` `previous`, and per-ability `resolved`
  let rockDef : CardDef := { name := "Phase11 Rock", types := #[.artifact] }
  let loyaltyWatcherDef : CardDef := {
    name := "Phase11 Loyalty Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.fra (.fra .youPutLoyaltyCounters) "" (.draw 1)]
  }
  let gPw0 := addPermanent (addPermanent afterDraw rockDef me me) loyaltyWatcherDef me me
  let pwRock := (gPw0.battlefield.filter (·.name == "Phase11 Rock"))[0]!
  let gPw1 := quiet (gPw0.createEffect
    (.layered (.objects #[pwRock.id]) (.types .add #[.planeswalker] #[.jace] #[]) .untilEndOfTurn))
  let gPw2 := gPw1.withBatch none fun g =>
    g.recordPutCounters pwRock.id .loyalty 1 (byPlayer := some me)
  let pwSnapOk :=
    gPw2.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters (.object eo) .loyalty (.put 1) (some p))) =>
        eo.id == some pwRock.id && p == me && eo.types.contains .planeswalker
      | _ => false) &&
    gPw2.waitingTriggers.any (·.event == .fra .youPutLoyaltyCounters)
  let eqDef : CardDef := { name := "Phase11 Blade", types := #[.artifact], subtypes := #["Equipment"] }
  let bear2Def : CardDef := creature "Event Bear 2" ManaCost.empty #["Bear"] 2 2
  let gEq0 := quiet (addPermanent (addPermanent gAb0 bear2Def me me) eqDef me me)
  let eqObj := (gEq0.battlefield.filter (·.name == "Phase11 Blade"))[0]!
  let host1 := (gEq0.battlefield.filter (·.name == "Event Bear"))[0]!
  let host2 := (gEq0.battlefield.filter (·.name == "Event Bear 2"))[0]!
  let gEq1 := gEq0.attachSourceTo eqObj host1
  let gEq2 := gEq1.attachSourceTo (gEq1.object! eqObj.id) host2
  let eqAttached := gEq2.events.filterMap fun e =>
    match e.change with
    | .rules (.permanent (.attached eo hid prev)) => some (eo, hid, prev)
    | _ => none
  let attachedPrevOk :=
    eqAttached.size == 2 &&
    eqAttached[0]!.1.subtypes.contains .equipment &&
    eqAttached[0]!.2.1 == host1.id &&
    eqAttached[0]!.2.2 == none &&
    eqAttached[1]!.1.subtypes.contains .equipment &&
    eqAttached[1]!.2.1 == host2.id &&
    eqAttached[1]!.2.2 == some host1.id
  let abA : TriggeredAbility := .triggered .enter (Effect.ofTrigger .belladonnaTokenReward)
  let abB : TriggeredAbility := .triggered .yourUpkeep (Effect.ofTrigger .belladonnaTokenReward)
  let gRes0 := quiet gAb0
  let gRes1 := (gRes0.putTriggeredAbilityOnStack me baseBear abA "enters").resolveTop
  let gRes2 := (gRes1.putTriggeredAbilityOnStack me (gRes1.object! baseBear.id) abB "upkeep").resolveTop
  let gRes3 := (gRes2.putTriggeredAbilityOnStack me (gRes2.object! baseBear.id) abA "enters").resolveTop
  let resolvedEvents := gRes3.events.filterMap fun e =>
    match e.change with
    | .rules (.stackObject (.resolved obj ord sid ab?)) => some (ord, obj, sid, ab?)
    | _ => none
  let perAbilityResolvedOk :=
    resolvedEvents.size == 3 &&
    resolvedEvents[0]!.1 == 1 && resolvedEvents[0]!.2.2.1 == some baseBear.id && resolvedEvents[0]!.2.2.2 == some abA &&
    resolvedEvents[1]!.1 == 1 && resolvedEvents[1]!.2.2.1 == some baseBear.id && resolvedEvents[1]!.2.2.2 == some abB &&
    resolvedEvents[2]!.1 == 2 && resolvedEvents[2]!.2.2.1 == some baseBear.id && resolvedEvents[2]!.2.2.2 == some abA
  let snapshotAlignmentOk := pwSnapOk && attachedPrevOk && perAbilityResolvedOk
  -- 3. CR 614.12 clone & Layer 6 ability-loss ETB lookahead + CR 702.34a `.flashbackUntilEot`
  let tappedPwDef : CardDef := {
    name := "Phase11 Tapped Walker"
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 4
    entersTapped := true
  }
  let (gClone0, cloneCand) := afterDraw.allocObject bear me (.outside me) (some me)
  let gClone1 := gClone0.createEffect (.layered (.objects #[cloneCand.id]) (.copy tappedPwDef) .indefinite)
  let cloneEtb := gClone1.applyEtbReplacements (gClone1.object! cloneCand.id)
  let humCreatureDef : CardDef := {
    name := "Phase11 Counters Bear"
    types := #[.creature]
    power := some 1
    toughness := some 1
    entersTapped := true
    entersWithPlusOneCounters := 2
  }
  let (gHum0, humCand) := afterDraw.allocObject humCreatureDef me (.outside me) (some me)
  let gHum1 := gHum0.createEffect (.layered (.creaturesControlledBy me) (.abilities {} .all) .indefinite)
  let humEtb := gHum1.applyEtbReplacements (gHum1.object! humCand.id)
  let boltDef : CardDef := { name := "Phase11 Bolt", types := #[.instant] }
  let (gFb0, fbSpell) := (quiet afterDraw).allocObject boltDef me .stack (some me)
  let gFb1 := quiet (gFb0.createEffect (.flashbackUntilEot fbSpell.id))
  let (gFbMoved, fbNewId) := gFb1.move fbSpell.id (.graveyard me) none
  let fbExiledOk :=
    (gFbMoved.object! fbNewId).zone == .exile &&
    gFbMoved.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.zone (.moved _ _ .stack .exile ..)), some (.replaced rep _) =>
        rep.kind == .flashbackExile && rep.object == some fbSpell.id
      | _, _ => false)
  let etbAndFlashbackOk :=
    cloneEtb.candidate.status.tapped &&
    cloneEtb.entersWith.count .loyalty == 4 &&
    !humEtb.candidate.status.tapped &&
    humEtb.entersWith.count .plusOnePlusOne == 0 &&
    fbExiledOk
  -- 4. `*/*` CDA creature spells on the stack
  let cdaSpellDef : CardDef := {
    name := "Phase11 Lands Avatar"
    types := #[.creature]
    subtypes := #["Avatar"]
    staticAbilities := #[.powerToughnessEqualLandsYouControl]
  }
  let forestDef : CardDef := { name := "Forest", types := #[.land], subtypes := #["Forest"] }
  let gCda0 := addPermanent (addPermanent (addPermanent afterDraw forestDef me me) forestDef me me) forestDef me me
  let (gCda1, cdaSpell) := gCda0.allocObject cdaSpellDef me .stack (some me)
  let gCda2 := gCda1.change (.pushStack { objectId := cdaSpell.id, controller := me, targets := #[] })
  let stackCdaOk :=
    gCda2.snapshotPower cdaSpell == 3 &&
    gCda2.snapshotToughness cdaSpell == 3 &&
    (gCda2.snapshot cdaSpell).power == some 3 &&
    (gCda2.snapshot cdaSpell).toughness == some 3 &&
    (gCda2.legalTargetsForSpec opp (.creatureSpellPTAtMost 3) none).contains (.card cdaSpell.id) &&
    !(gCda2.legalTargetsForSpec opp (.creatureSpellPTAtMost 2) none).contains (.card cdaSpell.id)
  -- 5. CR 702.73a off-battlefield changeling behold & subtype queries
  let changelingDef : CardDef := {
    name := "Phase11 Changeling"
    types := #[.creature]
    subtypes := #["Shapeshifter"]
    keywords := { changeling := true }
    power := some 2
    toughness := some 2
  }
  let gCh0 := quiet (insertObject (emptyHand afterDraw me) changelingDef me (.hand me))
  let gChDragon := gCh0.beholdQuality me .dragon (cause := some (.gameRule .spellCast))
  let gChForest := gCh0.beholdQuality me .forest (cause := some (.gameRule .spellCast))
  let changelingOffBfOk :=
    changelingDef.hasSubtype .dragon &&
    !changelingDef.hasSubtype .forest &&
    !changelingDef.hasSubtype .equipment &&
    gChDragon.events.any (fun e => match e.change with | .rules (.player (.beheld p .dragon)) => p == me | _ => false) &&
    !gChForest.events.any (fun e => match e.change with | .rules (.player (.beheld ..)) => true | _ => false)
  -- 6. Off-battlefield token-creation probe (Draconic Visitor ruling 782), CR 707.2
  --    `isToken` + arrival status preservation across `entersAsCopy` / `entersBackFaceUp`,
  --    and tier-1 timestamps for `TriggerQueueEvent.putOnStack` / `CastEvent.abilityActivated`.
  let bilboDef : CardDef := {
    name := "Phase11 Bilbo"
    types := #[.enchantment]
    foodAlsoCreatesTreasure := true
  }
  let visitorDef : CardDef := {
    name := "Phase11 Visitor"
    types := #[.enchantment]
    staticAbilities := #[.artifactTokensBecomeDragons]
  }
  let foodTemplate : CardDef := {
    name := "Food"
    types := #[.artifact]
    subtypes := #["Food"]
  }
  let gProbe0 := quiet (addPermanent (addPermanent afterDraw bilboDef me me) visitorDef me me)
  let gProbeBfLeaks :=
    quiet ((gProbe0.createEffect
      (.layered (.creaturesControlledBy me) (.types .add #[.artifact] #[.food] #[]) .indefinite)).createEffect
      (.layered (.creaturesControlledBy me) (.copy foodTemplate) .indefinite))
  let (probeBatchesPlain, probeAppPlain, probeChoicePlain) := gProbeBfLeaks.replaceTokenCreationChoice {
    controller := me
    printed := humanSoldierToken
    count := 1
  }
  let gProbeWildcard :=
    quiet (gProbeBfLeaks.createEffect
      (.replacement {
        id := { kind := .entersAsCopy }
        affectedPlayer := me
        kind := .entersAsCopy none foodTemplate
      } .untilEndOfTurn))
  let (_, _, probeChoiceCopy) := gProbeWildcard.replaceTokenCreationChoice {
    controller := me
    printed := humanSoldierToken
    count := 1
  }
  let tokenProbeOk :=
    probeBatchesPlain.size == 1 &&
    probeBatchesPlain[0]!.printed.name == "Human Soldier" &&
    probeAppPlain.isEmpty &&
    probeChoicePlain.isNone &&
    probeChoiceCopy.any (fun (p, cs) => p == me && cs.size == 2)
  let dfcNontokenTemplate : CardDef := {
    name := "Phase11 Siege Front"
    types := #[.enchantment]
    asEntersChooseMarduOrJeskai := true
    asEntersChooseCardType := true
    entersPrepared := true
    isToken := false
    otherFace := some {
      name := "Phase11 Siege Back"
      types := #[.creature]
      power := some 4
      toughness := some 4
      asEntersChooseMarduOrJeskai := true
      entersPrepared := true
      isToken := false
    }
  }
  let gTokCopy0 := quiet (afterDraw.createEffect
    (.replacement {
      id := { kind := .entersAsCopy }
      affectedPlayer := me
      kind := .entersAsCopy none dfcNontokenTemplate
    } .untilEndOfTurn))
  let (gTokCopy1a, _) := gTokCopy0.createOneToken me humanSoldierToken
  let gTokCopy1 := applyIdle (applyIdle gTokCopy1a)
  let placedTokCopied := (gTokCopy1.battlefield.filter (·.name == "Phase11 Siege Front"))[0]!
  let gTokBack0 := quiet (gTokCopy0.createEffect
    (.replacement {
      id := { kind := .entersBackFaceUp }
      affectedPlayer := me
      kind := .entersBackFaceUp none
    } .untilEndOfTurn))
  let (gTokBack1a, _) := gTokBack0.createOneToken me humanSoldierToken
  let gTokBack1 := applyIdle gTokBack1a
  let placedTokBack := (gTokBack1.battlefield.filter (·.name == "Phase11 Siege Back"))[0]!
  let tokenCopyStatusOk :=
    placedTokCopied.printed.isToken &&
    placedTokCopied.printed.otherFace.all (·.isToken) &&
    placedTokCopied.status.chosenAnchor == some "Mardu" &&
    placedTokCopied.status.prepared &&
    placedTokCopied.status.chosenCardType == some .creature &&
    gTokCopy1.isCreature placedTokCopied &&
    placedTokBack.status.transformed &&
    placedTokBack.printed.name == "Phase11 Siege Back" &&
    placedTokBack.printed.isToken &&
    placedTokBack.printed.otherFace.all (·.isToken) &&
    placedTokBack.status.chosenAnchor == some "Mardu" &&
    placedTokBack.status.prepared
  let gTrigBase := addPermanent afterDraw actBearDef me me
  let trigBear := (gTrigBase.battlefield.filter (·.name == "Event Bear"))[0]!
  let gTrigTs0 := gTrigBase.createEffect
    (.layered (.creaturesControlledBy me) (.abilities {} .all) .untilEndOfTurn)
  let effEid := gTrigTs0.activeEffects.back!.1
  let effPos := gTrigTs0.activeEffects.size - 1
  let effTs := gTrigTs0.effectTimestamp effEid effPos
  let gTrigTs1 := gTrigTs0.putTriggeredAbilityOnStack me (gTrigTs0.object! trigBear.id) (.onEnterDraw 1) "enters"
  let trigStackObj := gTrigTs1.object! gTrigTs1.stack.back!.objectId
  let trigTs := gTrigTs1.objectEntryTimestamp trigStackObj
  let directAbId : ObjectId := ⟨gTrigTs1.nextObjectId⟩
  let gDirectAct := gTrigTs1.record (GameEvent.abilityActivated gTrigTs1.turnNumber directAbId
    (gTrigTs1.snapshot (gTrigTs1.object! trigBear.id)) me (.nonMana none false false false (some 0) false))
  let directActObj := gDirectAct.object! directAbId
  let directActTs := gDirectAct.objectEntryTimestamp directActObj
  let bearBeforeBoastTs := gDirectAct.objectEntryTimestamp (gDirectAct.object! trigBear.id)
  let gAfterBoast := gDirectAct.markBoastUsed (gDirectAct.object! trigBear.id)
  let bearAfterBoastTs := gAfterBoast.objectEntryTimestamp (gAfterBoast.object! trigBear.id)
  let stackAbilityTsOk :=
    effTs.1 == 1 &&
    trigTs.1 == 1 && trigTs.2 > effTs.2 &&
    directActTs.1 == 1 && directActTs.2 > trigTs.2 &&
    bearBeforeBoastTs.1 == 1 && bearAfterBoastTs == bearBeforeBoastTs
  materializeIsolationOk &&
    snapshotAlignmentOk &&
    etbAndFlashbackOk &&
    stackCdaOk &&
    changelingOffBfOk &&
    tokenProbeOk &&
    tokenCopyStatusOk &&
    stackAbilityTsOk

end Mtg.Engine.EventTests
