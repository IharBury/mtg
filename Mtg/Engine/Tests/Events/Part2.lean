import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/- Phase 12: CR 733.1 illegal-proposal reversal integrity, `Game.replayEvents`
fidelity from `({} : Game)`, `.exchangeControl` batch/cause & CR 701.12a–b,
second combat-damage step `TurnEvent`s (CR 510.4 / 702.7b / 500.9), Path of
Ancestry scry via `ManaUnit.source`, `matchTriggers` cast / target / Ward
triggers (CR 702.85a / 702.21a / 109.2), and `entersTappedUnlessPayLife` in the
unified CR 614.12 / 616.1 ETB replacement pipeline. -/
#guard
  -- 1. CR 733.1 proposal reversal: zero phantom events/triggers, intact `followMoved`,
  --    top-of-library exemption, `.crew` / `.zemoBoastExile` retraction, Chandra refund,
  --    and CR 733.1 library-visibility irreversibility guard.
  let tapWatcherDef : CardDef := {
    name := "Phase12 Tap Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.ofPattern .creaturesYouControlBecomeTapped "" (.draw 1) (grouping := .oncePerBatch),
      TriggeredAbility.ofPattern .youCastNoncreature "" (.draw 1)]
  }
  let manaDorkDef : CardDef := {
    name := "Phase12 Mana Dork"
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 1
    toughness := some 1
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])]
  }
  let twoGenericSorcery : CardDef := {
    name := "Phase12 Two-Mana Divination"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let gPropBase0 :=
    let g := addPermanent (addPermanent afterDraw tapWatcherDef me me) manaDorkDef me me
    insertObject g twoGenericSorcery me (.hand me)
  let spellHandId :=
    ((gPropBase0.player me).hand.filter (fun id => (gPropBase0.object! id).name == "Phase12 Two-Mana Divination"))[0]!
  let dorkId := (gPropBase0.battlefield.filter (·.name == "Phase12 Mana Dork"))[0]!.id
  let preEvCount := gPropBase0.events.size
  let gProposed := mustApply gPropBase0 me (.cast spellHandId)
  let midReplayOk := Game.replayEvents gProposed.events == gProposed
  let gTappedDuring := mustApply gProposed me (.tapForMana dorkId (.colored .green))
  let gRev := mustApply gTappedDuring me .pay
  let postSlice := gRev.events.extract preEvCount gRev.events.size
  let noPhantomRules :=
    postSlice.all (fun e => match e.change with | .engine (.logMsg _) => true | _ => false)
  let spellRevOk :=
    midReplayOk &&
    noPhantomRules &&
    gRev.proposalCheckpoint.isNone &&
    gRev.proposedSpell.isNone &&
    gRev.pending == .none &&
    gRev.priority == gPropBase0.priority &&
    gRev.consecutivePasses == gPropBase0.consecutivePasses &&
    gRev.waitingTriggers.isEmpty &&
    gRev.stack.isEmpty &&
    !(gRev.object! dorkId).status.tapped &&
    !(gRev.becameTappedThisTurn dorkId) &&
    !(gRev.wasCast spellHandId) &&
    ((gRev.player me).hand.contains spellHandId) &&
    gRev.followMoved spellHandId == spellHandId &&
    gRev.nextObjectId == gPropBase0.nextObjectId &&
    gRev.nextBatchId == gPropBase0.nextBatchId &&
    Game.replayEvents gRev.events == gRev
  -- Top-of-library cast (Elven Chorus) reverses cleanly (`toZone == .stack` is exempted by CR 733.1)
  let chorusDef : CardDef := {
    name := "Phase12 Chorus"
    types := #[.enchantment]
    staticAbilities := #[.mayCastCreaturesFromTop]
  }
  let costlyElfDef : CardDef := {
    name := "Phase12 Costly Elf"
    manaCost := ManaCost.ofGeneric 3
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 2
    toughness := some 2
  }
  let gTop0 :=
    let g := addPermanent afterDraw chorusDef me me
    insertObject g costlyElfDef me (.library me)
  let topCardId := (gTop0.player me).library.back!
  let gTopProp := mustApply gTop0 me (.cast topCardId)
  let gTopRev := mustApply gTopProp me .pay
  let topRevOk :=
    gTopProp.castingFromTop &&
    !gTopRev.castingFromTop &&
    (gTopRev.player me).library.back? == some topCardId &&
    gTopRev.followMoved topCardId == topCardId &&
    Game.replayEvents gTopRev.events == gTopRev
  -- `.crew` and `.zemoBoastExile` non-`ProposedSpell` activation declines retract cleanly
  let boatDef : CardDef := {
    name := "Phase12 Boat"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    keywords := #[.crew 2]
  }
  let gCrew0 := addPermanent (addPermanent afterDraw boatDef me me) grizzlyBears me me
  let boatId := (gCrew0.battlefield.filter (·.name == "Phase12 Boat"))[0]!.id
  let crewPilotId := (gCrew0.battlefield.filter (·.name == "Grizzly Bears"))[0]!.id
  let gCrewAsk := mustApply gCrew0 me (.activate boatId 0)
  let crewPayableDeclineBlocked := !(gCrewAsk.apply me .decline).isOk
  let gCrewUnpayable := gCrewAsk.becomeTapped (gCrewAsk.object! crewPilotId)
  let gCrewDec := mustApply gCrewUnpayable me .decline
  let crewRevOk :=
    crewPayableDeclineBlocked &&
    gCrewDec.stack.isEmpty &&
    gCrewDec.proposedSpell.isNone &&
    gCrewDec.nextObjectId == gCrew0.nextObjectId &&
    Game.replayEvents gCrewDec.events == gCrewDec
  let zemoDef : CardDef := {
    name := "Phase12 Zemo"
    types := #[.creature]
    power := some 3
    toughness := some 3
    activatedAbilities := #[ActivatedAbility.zemoBoastAbility]
  }
  let heavyBlackCard : CardDef := {
    name := "Phase12 Fifteen Black"
    manaCost := { symbols := Array.replicate 15 (.colored .black) }
    types := #[.creature]
    power := some 1
    toughness := some 1
  }
  let gZemo0 :=
    let g := addPermanent afterDraw zemoDef me me
    let g := insertObject g heavyBlackCard me (.graveyard me)
    let z := (g.battlefield.filter (·.name == "Phase12 Zemo"))[0]!
    g.record (GameEvent.attacked g.turnNumber me (g.snapshot z) opp)
  let zemoId := (gZemo0.battlefield.filter (·.name == "Phase12 Zemo"))[0]!.id
  let hvyId := (gZemo0.objects.filter (·.name == "Phase12 Fifteen Black"))[0]!.id
  let gZemoAsk := mustApply gZemo0 me (.activate zemoId 0)
  let zemoPayableDeclineBlocked := !(gZemoAsk.apply me .decline).isOk
  let (gZemoUnpayable, _) := gZemoAsk.move hvyId .exile none
  let gZemoDec := mustApply gZemoUnpayable me .decline
  let zemoRevOk :=
    zemoPayableDeclineBlocked &&
    gZemoDec.stack.isEmpty &&
    gZemoDec.proposedSpell.isNone &&
    gZemoDec.nextObjectId == gZemo0.nextObjectId &&
    Game.replayEvents gZemoDec.events == gZemoDec
  -- Chandra `castExiledAsAbilityResolves`: targeted exiled spell reversed restores mana & `.mayCastExiledElseDamage`
  let gChandra0 :=
    let g := insertObject afterDraw lightningBolt me .exile
    let g := g.addMana me (.colored .red) 1
    let boltExId := (g.objects.filter (fun o => o.name == "Lightning Bolt" && o.zone == .exile))[0]!.id
    g.change (.pending (.mayCastExiledElseDamage me boltExId 2 none))
  let boltExId := (gChandra0.objects.filter (fun o => o.name == "Lightning Bolt" && o.zone == .exile))[0]!.id
  let gChandraProp := mustApply gChandra0 me (.cast boltExId)
  let gChandraRev := gChandraProp.reverseProposedSpell
  let chandraRevOk :=
    gChandraRev.pending == .mayCastExiledElseDamage me boltExId 2 none &&
    (gChandraRev.player me).manaPool.red == 1 &&
    (gChandraRev.object! boltExId).zone == .exile &&
    gChandraRev.followMoved boltExId == boltExId &&
    Game.replayEvents gChandraRev.events == gChandraRev
  -- CR 733.1–733.2 library-event preservation: reversing an illegal cast still
  -- reverses the spell and restores priority, undoing hand reveals while
  -- keeping mill, library shuffle, and library-card reveal events.
  let handCardId := (gProposed.player me).hand[0]!
  let topLibId := (gProposed.player me).library.back!
  let libCardId := (gProposed.player me).library[0]!
  let shuffledOrder := (gProposed.player me).library.reverse
  let gHandRev :=
    (gProposed.record (GameEvent.revealed gProposed.turnNumber me #[handCardId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let gMillRev := (gProposed.mill me 1).reverseProposedSpell
  let gShuffleRev :=
    (gProposed.record (GameEvent.shuffled gProposed.turnNumber me shuffledOrder
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let gLibRevealRev :=
    (gProposed.record (GameEvent.revealed gProposed.turnNumber me #[libCardId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let baseRestored (g : Game) : Bool :=
    g.proposalCheckpoint.isNone &&
    g.proposedSpell.isNone &&
    g.stack.isEmpty &&
    g.priority == me &&
    (g.player me).hand.contains spellHandId
  let hasRevealOf (g : Game) (cid : ObjectId) : Bool :=
    (g.events.extract preEvCount g.events.size).any (fun e =>
      match e.change with
      | .rules (.player (.revealed p ids)) => p == me && ids == #[cid]
      | _ => false)
  let hasAnyRevealAfter (startIdx : Nat) (g : Game) : Bool :=
    (g.events.extract startIdx g.events.size).any (fun e =>
      match e.change with
      | .rules (.player (.revealed ..)) => true
      | _ => false)
  -- Chronological zone-at-reveal checks (CR 733.1):
  -- (i) Graveyard reveal of a card that is only *later* put into a library (even
  --     reusing the same `ObjectId` so `g.objects` ends with it in `.library`) is undone.
  let gPropGy0 := insertObject gPropBase0 bear me (.graveyard me)
  let gyCardId := (gPropGy0.player me).graveyard.back!
  let preGyEv := gPropGy0.events.size
  let gGyThenLibRev :=
    let g := mustApply gPropGy0 me (.cast spellHandId)
    let g := g.record (GameEvent.revealed g.turnNumber me #[gyCardId]
      (cause := some (.gameRule .spellCast)))
    let gySnap := g.snapshot (g.object! gyCardId)
    let libAfterSnap : EventObject := { gySnap with id := some gyCardId, zone := .library me }
    let g := g.record (GameEvent.moved g.turnNumber gySnap (.graveyard me) (.library me)
      (after := some libAfterSnap) (libraryPosition := some .top) (cause := .gameRule .spellCast))
    g.reverseProposedSpell
  -- (ii) Card that started in `.library`, moved to `.hand` earlier in the slice,
  --      and was then revealed is NOT kept as a library reveal.
  let gDrawnThenRev :=
    let g := gProposed.draw me 1
    let drawnHandId := (g.player me).hand.back!
    let g := g.record (GameEvent.revealed g.turnNumber me #[topLibId, drawnHandId]
      (cause := some (.gameRule .spellCast)))
    g.reverseProposedSpell
  -- (iii) Top-of-library spell (`.library -> .stack`) revealed after moving to `.stack`
  --       is NOT kept as a library reveal.
  let preTopEv := gTop0.events.size
  let topStackId := gTopProp.stack.back!.objectId
  let gTopStackRev :=
    (gTopProp.record (GameEvent.revealed gTopProp.turnNumber me #[topCardId, topStackId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  -- (iv) Card moved into `.library` by an earlier kept move and *then* revealed IS kept.
  let (gPutLibMid, putLibId) :=
    gProposed.move handCardId (.library me) none (libraryPosition := some .top)
      (cause := some (.gameRule .spellCast))
  let gPutLibThenRev :=
    (gPutLibMid.record (GameEvent.revealed gPutLibMid.turnNumber me #[putLibId]
      (cause := some (.gameRule .spellCast)))).reverseProposedSpell
  let chronoRevealOk :=
    !hasAnyRevealAfter preGyEv gGyThenLibRev &&
    (gGyThenLibRev.player me).library.contains gyCardId &&
    Game.replayEvents gGyThenLibRev.events == gGyThenLibRev &&
    !hasAnyRevealAfter preEvCount gDrawnThenRev &&
    Game.replayEvents gDrawnThenRev.events == gDrawnThenRev &&
    !hasAnyRevealAfter preTopEv gTopStackRev &&
    (gTopStackRev.player me).library.back? == some topCardId &&
    Game.replayEvents gTopStackRev.events == gTopStackRev &&
    hasRevealOf gPutLibThenRev putLibId &&
    Game.replayEvents gPutLibThenRev.events == gPutLibThenRev
  let libGuardOk :=
    baseRestored gHandRev &&
    !hasRevealOf gHandRev handCardId &&
    Game.replayEvents gHandRev.events == gHandRev &&
    baseRestored gMillRev &&
    (gMillRev.object! (gMillRev.followMoved topLibId)).zone == .graveyard me &&
    (gMillRev.player me).graveyard.size == (gPropBase0.player me).graveyard.size + 1 &&
    Game.replayEvents gMillRev.events == gMillRev &&
    baseRestored gShuffleRev &&
    (gShuffleRev.player me).library == shuffledOrder &&
    Game.replayEvents gShuffleRev.events == gShuffleRev &&
    baseRestored gLibRevealRev &&
    hasRevealOf gLibRevealRev libCardId &&
    Game.replayEvents gLibRevealRev.events == gLibRevealRev &&
    chronoRevealOk
  -- Failed may-cast (split second on stack) clears caller `proposalCheckpoint`,
  -- and a subsequent `castAsPartOfResolution` takes its own fresh checkpoint
  -- rather than truncating back across events recorded in between.
  let splitSecondGranter : CardDef := {
    name := "Phase12 Split Granter"
    types := #[.enchantment]
    staticAbilities := #[.instantSorcerySplitSecond]
  }
  let targetCreatureSorcery : CardDef := {
    name := "Phase12 Impossible Removal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .creature
      resolution := .destroyTarget
      phrase := "Destroy target creature"
    }
  }
  let gMayCastCkpt :=
    let g := addPermanent afterDraw splitSecondGranter opp opp
    let g := insertObject g lightningBolt opp (.hand opp)
    let ssHandId := ((g.player opp).hand.filter (fun id => (g.object! id).name == "Lightning Bolt"))[0]!
    let (g, ssStackId) := g.move ssHandId .stack (some opp) (verb := some .cast) (actor := some opp)
      (cause := some (.gameRule .spellCast))
    let g := g.putStackEntry opp ssStackId
    let g := insertObject g lightningBolt me (.hand me)
    let g := insertObject g targetCreatureSorcery me (.hand me)
    let boltH := ((g.player me).hand.filter (fun id => (g.object! id).name == "Lightning Bolt"))[0]!
    let remH := ((g.player me).hand.filter (fun id => (g.object! id).name == "Phase12 Impossible Removal"))[0]!
    let g := g.change (.pending (.fraChoice me (.mayCastInstantSorceryFromHand #[boltH])))
    let gBlocked :=
      match g.answerFraChoice me (.objects #[boltH]) with
      | .ok g' => g'
      | .error _ => g
    let clearedOnFail := gBlocked.proposalCheckpoint.isNone
    let (gMid, _) := gBlocked.move ssStackId (.graveyard opp) none (cause := some testCause)
    let gMid := gMid.gainLife me 5
    let gSecondRev := gMid.castAsPartOfResolution me remH
    (clearedOnFail, gSecondRev, remH)
  let mayCastCkptOk :=
    gMayCastCkpt.1 &&
    gMayCastCkpt.2.1.proposalCheckpoint.isNone &&
    gMayCastCkpt.2.1.proposedSpell.isNone &&
    (gMayCastCkpt.2.1.player me).life == (25 : Int) &&
    ((gMayCastCkpt.2.1.player me).hand.contains gMayCastCkpt.2.2) &&
    Game.replayEvents gMayCastCkpt.2.1.events == gMayCastCkpt.2.1
  let reversalAllOk :=
    spellRevOk && topRevOk && crewRevOk && zemoRevOk && chandraRevOk && libGuardOk && mayCastCkptOk

  -- 2. Full-game `Game.replayEvents g.events == g` from `({} : Game)` and empty `withBatch` non-bump
  let gFull := Agent.play drawnHands 400
  let gNoopBatch := afterDraw.withBatch none id
  let replayAllOk :=
    gFull.over &&
    Game.replayEvents gFull.events == gFull &&
    gNoopBatch.nextBatchId == afterDraw.nextBatchId &&
    Game.replayEvents gNoopBatch.events == gNoopBatch

  -- 3. `.exchangeControl` single-batch / single-cause & CR 701.12a–b guards
  let gExBase := quiet (addPermanent (addPermanent afterDraw bear me me) hero opp opp)
  let exBear := (gExBase.battlefield.filter (·.name == bear.name))[0]!
  let exHero := (gExBase.battlefield.filter (·.name == hero.name))[0]!
  let exEffect : Effect := {
    targeting := .of (TargetSpec.creature.append .creature)
    resolution := .exchangeControl
    phrase := "Exchange control of two target creatures"
  }
  let gExDone :=
    gExBase.withResolvingContext (some exBear.id) me (fun g =>
      g.applyEffect me exEffect #[Target.permanent exBear.id, Target.permanent exHero.id]
        (sourceId := some exBear.id))
  let isCtrlEffectCreated (e : GameEvent) : Bool :=
    match e.change with
    | .rules (.continuousEffect (.created _ (.layered _ (.control _) _))) => true
    | _ => false
  let ctrlEvents := gExDone.events.filter isCtrlEffectCreated
  let gExSame :=
    let gSame0 := quiet (addPermanent (addPermanent afterDraw bear me me) hero me me)
    let b1 := (gSame0.battlefield.filter (·.name == bear.name))[0]!
    let h1 := (gSame0.battlefield.filter (·.name == hero.name))[0]!
    gSame0.applyEffect me exEffect #[Target.permanent b1.id, Target.permanent h1.id]
  let gExLost :=
    let gLost0 := quiet (gExBase.record (GameEvent.playerLost gExBase.turnNumber opp .conceded))
    gLost0.applyEffect me exEffect #[Target.permanent exBear.id, Target.permanent exHero.id]
  let gExMissing :=
    gExBase.applyEffect me exEffect #[Target.permanent exBear.id, Target.permanent ⟨99999⟩]
  let hasNoCtrlChange (g : Game) : Bool :=
    !g.events.any isCtrlEffectCreated
  -- Ring-bearer designation on BOTH exchanged permanents shares the exchange's
  -- single `BatchId` and resolved `.oneShotEffect (some eid)` cause (not `.staticAbility`).
  let gExRbInit := addPermanent (addPermanent afterDraw bear me me) hero opp opp
  let exRbBear := (gExRbInit.battlefield.filter (·.name == bear.name))[0]!
  let exRbHero := (gExRbInit.battlefield.filter (·.name == hero.name))[0]!
  let gExRb0 :=
    let g := gExRbInit.setRingBearer me (some exRbBear.id) (cause := some testCause)
    g.setRingBearer opp (some exRbHero.id) (cause := some testCause)
  let preExRbIdx := gExRb0.events.size
  let gExRbDone :=
    gExRb0.withResolvingContext (some exRbBear.id) me (fun g =>
      g.applyEffect me exEffect #[Target.permanent exRbBear.id, Target.permanent exRbHero.id]
        (sourceId := some exRbBear.id))
  let exRbSlice := gExRbDone.events.extract preExRbIdx gExRbDone.events.size
  let exRbRules := exRbSlice.filter (fun e =>
    match e.change with
    | .rules (.permanent (.designation _ .ringBearer false))
    | .rules (.continuousEffect (.created _ (.layered _ (.control _) _))) => true
    | _ => false)
  let exRbCauseOk :=
    exRbRules.size == 4 &&
    exRbRules.all (fun e => e.batch == exRbRules[0]!.batch && e.cause? == exRbRules[0]!.cause?) &&
    (match exRbRules[0]!.cause? with
     | some (.oneShotEffect (some _) (some src) (some ctrl)) => src == exRbBear.id && ctrl == me
     | _ => false) &&
    Game.replayEvents gExRbDone.events == gExRbDone
  let exchangeAllOk :=
    ctrlEvents.size == 2 &&
    ctrlEvents[0]!.batch == ctrlEvents[1]!.batch &&
    ctrlEvents[0]!.cause? == ctrlEvents[1]!.cause? &&
    (match ctrlEvents[0]!.cause? with | some (.oneShotEffect (some _) _ _) => true | _ => false) &&
    gExDone.controllerOf (gExDone.object! exBear.id) == some opp &&
    gExDone.controllerOf (gExDone.object! exHero.id) == some me &&
    exRbCauseOk &&
    hasNoCtrlChange gExSame &&
    hasNoCtrlChange gExLost &&
    hasNoCtrlChange gExMissing

  -- 4. Second combat-damage step `TurnEvent`s (CR 510.4 / 702.7b / 500.9) and derived helpers
  let fsAttackerDef : CardDef :=
    { (creature "Phase12 First Striker" ManaCost.empty #["Knight"] 2 2) with
      keywords := #[Keyword.firstStrike] }
  let gCbt0 :=
    let g := addPermanent (addPermanent afterDraw fsAttackerDef me me) bear me me
    let fk := (g.battlefield.filter (·.name == "Phase12 First Striker"))[0]!
    let br := (g.battlefield.filter (·.name == bear.name))[0]!
    let g := g.beginStep .beginningOfCombat
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g me (.declareAttackers #[fk.id, br.id] none #[] #[])
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g opp (.declareBlockers #[])
    g
  let fkId := (gCbt0.battlefield.filter (·.name == "Phase12 First Striker"))[0]!.id
  -- Also check replacement pause mid-first-strike keeps derived flags `false`
  let gCbtPause0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw fsAttackerDef me me) bear me me) hero opp opp
    let fk := (g.battlefield.filter (·.name == "Phase12 First Striker"))[0]!
    let br := (g.battlefield.filter (·.name == bear.name))[0]!
    let blk := (g.battlefield.filter (·.name == hero.name))[0]!
    let g := g.recordPutCounters blk.id .shield 1 (some opp) (cause := some testCause)
    let g := g.createEffect
      (.prevention { id := { kind := .preventAllDamageToPermanent, object := some blk.id },
                     affectedPlayer := opp, kind := .preventAllDamageToPermanent blk.id } .untilEndOfTurn)
    let g := g.beginStep .beginningOfCombat
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g me (.declareAttackers #[fk.id, br.id] none #[] #[])
    let g := mustApply (mustApply g me .pass) opp .pass
    let g := mustApply g opp (.declareBlockers #[(blk.id, fk.id)])
    mustApply (mustApply g me .pass) opp .pass
  let pauseFlagsOk :=
    (match gCbtPause0.pending with | .chooseReplacement .. => true | _ => false) &&
    !gCbtPause0.firstStrikeDamageDone &&
    !gCbtPause0.pendingRegularCombatDamage &&
    gCbtPause0.firstStrikeAssignedThisCombat.isEmpty &&
    Game.replayEvents gCbtPause0.events == gCbtPause0
  -- Normal two-step combat progression through `Turns.advanceStep`
  let preFsOk :=
    !gCbt0.firstStrikeDamageDone &&
    !gCbt0.pendingRegularCombatDamage &&
    gCbt0.firstStrikeAssignedThisCombat.isEmpty
  let gAfterFs := mustApply (mustApply gCbt0 me .pass) opp .pass
  let afterFsOk :=
    gAfterFs.step == .combatDamage &&
    gAfterFs.firstStrikeDamageDone &&
    gAfterFs.pendingRegularCombatDamage &&
    gAfterFs.firstStrikeAssignedThisCombat == #[fkId] &&
    (gAfterFs.player opp).life == 18 &&
    gAfterFs.events.any (fun e =>
      match e.change with
      | .rules (.turn (.extraStepAdded .combatDamage .afterCurrent)) => true
      | _ => false)
  let preSecondStepIdx := gAfterFs.events.size
  let gAfterReg := mustApply (mustApply gAfterFs me .pass) opp .pass
  let regStepSlice := gAfterReg.events.extract preSecondStepIdx gAfterReg.events.size
  let afterRegOk :=
    gAfterReg.step == .combatDamage &&
    gAfterReg.firstStrikeDamageDone &&
    !gAfterReg.pendingRegularCombatDamage &&
    gAfterReg.firstStrikeAssignedThisCombat == #[fkId] &&
    (gAfterReg.player opp).life == 16 &&
    regStepSlice.any (fun e => match e.change with | .rules (.turn (.stepEnded .combatDamage)) => true | _ => false) &&
    regStepSlice.any (fun e => match e.change with | .rules (.turn (.stepBegan .combatDamage _)) => true | _ => false) &&
    Game.replayEvents gAfterReg.events == gAfterReg
  let combatStepAllOk := pauseFlagsOk && preFsOk && afterFsOk && afterRegOk

  -- 5. Path of Ancestry scry via `ManaUnit.source` (tapped during proposal, floated before proposal,
  --    and LKI when Path of Ancestry left the battlefield before `becomeCast`)
  let poaDef : CardDef := {
    name := "Phase12 Path of Ancestry"
    types := #[.land]
    staticAbilities := #[.entersTapped]
    activatedAbilities := #[ActivatedAbility.manaAbility (.colorAmong (.commanderColorIdentity .you) false)]
    triggeredAbilities := #[TriggeredAbility.onManaSpentCastCommanderTypeScry]
  }
  let elfCmdrDef : CardDef := {
    name := "Phase12 Elf Commander"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    supertypes := #[.legendary]
    subtypes := #["Elf"]
    power := some 2
    toughness := some 2
  }
  let oneGreenElf : CardDef := {
    name := "Phase12 Llanowar Scout"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 1
    toughness := some 1
  }
  let oneGreenGoblin : CardDef := {
    name := "Phase12 Goblin Scout"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    subtypes := #["Goblin"]
    power := some 1
    toughness := some 1
  }
  let ancestryBase : Game :=
    match Start.start {
      seats := #[
        { name := "Chandra", deck := testRedDeck, commanders := #[elfCmdrDef] },
        { name := "Nissa", deck := testGreenDeck }
      ]
      format := .constructed
      seed := 1
      startingPlayer := some 0
    } with
    | .ok g => passBoth (keepOpeningHands g 8)
    | .error e => panic! e
  let mkAncestryGame (spellDef : CardDef) : Game × ObjectId × ObjectId :=
    let g := addPermanent ancestryBase poaDef me me
    let poa := (g.battlefield.filter (·.name == "Phase12 Path of Ancestry"))[0]!
    let g := insertObject g spellDef me (.hand me)
    let spId := ((g.player me).hand.filter (fun id => (g.object! id).name == spellDef.name))[0]!
    (g, poa.id, spId)
  -- (a) Tapped during proposal
  let (gPoaDuring0, poaIdA, elfIdA) := mkAncestryGame oneGreenElf
  let gPoaDuring :=
    let g := mustApply gPoaDuring0 me (.cast elfIdA)
    let g := mustApply g me (.tapForMana poaIdA (.colored .green))
    mustApply g me .pay
  -- (b) Floated before proposal, Path of Ancestry destroyed before `becomeCast` (LKI resolution)
  let (gPoaLki0, poaIdB, elfIdB) := mkAncestryGame oneGreenElf
  let gPoaLki :=
    let g := mustApply gPoaLki0 me (.tapForMana poaIdB (.colored .green))
    let g := g.destroyPermanent (g.object! poaIdB)
    let g := mustApply g me (.cast elfIdB)
    mustApply g me .pay
  -- (c) Non-matching creature subtype does not scry
  let (gPoaMiss0, poaIdC, gobIdC) := mkAncestryGame oneGreenGoblin
  let gPoaMiss :=
    let g := mustApply gPoaMiss0 me (.tapForMana poaIdC (.colored .green))
    let g := mustApply g me (.cast gobIdC)
    mustApply g me .pay
  -- (d) Copy-land LKI (CR 707.2 / 608.2h): a Forest copying `poaDef` under an
  --     exception name (`"Thespian's Stage"`) scries after dying, whereas a
  --     printed `poaDef` copying a basic Forest does NOT scry after dying.
  let (gPoaCopyHit0, poaTemplateId, elfIdD) := mkAncestryGame oneGreenElf
  let gPoaCopyHit :=
    let g := addPermanent gPoaCopyHit0 forest me me
    let fstObj := (g.battlefield.filter (·.name == "Forest"))[0]!
    let g := g.becomeCopyOf fstObj (g.object! poaTemplateId) (exceptName := some "Thespian's Stage")
    let g := mustApply g me (.tapForMana fstObj.id (.colored .green))
    let g := g.destroyPermanent (g.object! fstObj.id)
    let g := mustApply g me (.cast elfIdD)
    mustApply g me .pay
  let (gPoaCopyMiss0, poaOverwrittenId, elfIdE) := mkAncestryGame oneGreenElf
  let gPoaCopyMiss :=
    let g := addPermanent gPoaCopyMiss0 forest me me
    let fstObj := (g.battlefield.filter (·.name == "Forest"))[0]!
    let g := g.becomeCopyOf (g.object! poaOverwrittenId) fstObj
    let g := mustApply g me (.tapForMana poaOverwrittenId (.colored .green))
    let g := g.destroyPermanent (g.object! poaOverwrittenId)
    let g := mustApply g me (.cast elfIdE)
    mustApply g me .pay
  -- (e) Phased-out Path of Ancestry (CR 702.26d): tapping for `{G}` and phasing out
  --     before casting the creature spell still resolves the live `.battlefield` object
  --     (`isBattlefieldObject`) and scries; a phased-out copy overwritten onto Forest does not.
  let (gPoaPhased0, poaPhasedId, elfIdF) := mkAncestryGame oneGreenElf
  let gPoaPhased :=
    let g := mustApply gPoaPhased0 me (.tapForMana poaPhasedId (.colored .green))
    let g := g.phaseOut (g.object! poaPhasedId)
    let g := mustApply g me (.cast elfIdF)
    mustApply g me .pay
  let (gPoaPhasedCopy0, poaPhasedCopyId, elfIdG) := mkAncestryGame oneGreenElf
  let gPoaPhasedCopyMiss :=
    let g := addPermanent gPoaPhasedCopy0 forest me me
    let fstObj := (g.battlefield.filter (·.name == "Forest"))[0]!
    let g := g.becomeCopyOf (g.object! poaPhasedCopyId) fstObj
    let g := mustApply g me (.tapForMana poaPhasedCopyId (.colored .green))
    let g := g.phaseOut (g.object! poaPhasedCopyId)
    let g := mustApply g me (.cast elfIdG)
    mustApply g me .pay
  let hasScryPendingOrQueued (g : Game) : Bool :=
    (match g.pending with | .scry p 1 1 => p == me | _ => false) ||
      g.stack.any (fun e => (g.object! e.objectId).triggeredAbility.any (fun ab =>
        ab.effect.resolution == .scry 1))
  let ancestryAllOk :=
    hasScryPendingOrQueued gPoaDuring &&
    hasScryPendingOrQueued gPoaLki &&
    !hasScryPendingOrQueued gPoaMiss &&
    hasScryPendingOrQueued gPoaCopyHit &&
    !hasScryPendingOrQueued gPoaCopyMiss &&
    (gPoaPhased.object! poaPhasedId).status.phasedOut &&
    !(gPoaPhased.object! poaPhasedId).isOnBattlefield &&
    (gPoaPhased.object! poaPhasedId).isBattlefieldObject &&
    hasScryPendingOrQueued gPoaPhased &&
    !hasScryPendingOrQueued gPoaPhasedCopyMiss &&
    Game.replayEvents gPoaLki.events == gPoaLki &&
    Game.replayEvents gPoaCopyHit.events == gPoaCopyHit &&
    Game.replayEvents gPoaCopyMiss.events == gPoaCopyMiss &&
    Game.replayEvents gPoaPhased.events == gPoaPhased &&
    Game.replayEvents gPoaPhasedCopyMiss.events == gPoaPhasedCopyMiss

  -- 6. `matchTriggers`: `.onCastCascade` + CR 109.2 battlefield-doubler guard,
  --    Photon Blast Barrage `.copySourceSpellXTimes`, `.youTargetSomething` on targeted
  --    `.abilityActivated`, and Ward triggers on `WaitingTrigger` / `g.stack`.
  let doublerDef : CardDef := {
    name := "Phase12 Trigger Doubler"
    types := #[.enchantment]
    staticAbilities := #[.extraTriggerAnotherYouControl #[] #[.creature]]
  }
  let cascadeCreatureDef : CardDef := {
    name := "Phase12 Cascade Beast"
    manaCost := ManaCost.ofGeneric 3
    types := #[.creature]
    power := some 2
    toughness := some 2
    keywords := #[Keyword.cascade]
  }
  let gCasc0 :=
    let g := addPermanent afterDraw doublerDef me me
    let g := insertObject g cascadeCreatureDef me (.hand me)
    g.addMana me .colorless 3
  let cascId := ((gCasc0.player me).hand.filter (fun id => (gCasc0.object! id).name == "Phase12 Cascade Beast"))[0]!
  let gCascCast := mustApply (mustApply gCasc0 me (.cast cascId)) me .pay
  let cascadeStackItems := gCascCast.stack.filter (fun se =>
    (gCascCast.object! se.objectId).triggeredAbility == some .onCastCascade)
  -- Photon Blast Barrage X=2 cast trigger via `matchTriggers`
  let pbbDef : CardDef := {
    name := "Phase12 Barrage"
    manaCost := { symbols := #[.x, .colored .red, .colored .red] }
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .creature
      resolution := .copyThisSpellXTimesThenDamage 1
      phrase := "Deal 1 damage to target creature"
    }
  }
  let gPbb0 :=
    let g := addPermanent afterDraw bear opp opp
    let g := insertObject g pbbDef me (.hand me)
    g.addMana me (.colored .red) 4
  let pbbHandId := ((gPbb0.player me).hand.filter (fun id => (gPbb0.object! id).name == "Phase12 Barrage"))[0]!
  let oppBearPbb := (gPbb0.battlefield.filter (fun o => o.name == bear.name && gPbb0.controlledBy o opp))[0]!
  let gPbbCast :=
    let g := mustApply gPbb0 me (.cast pbbHandId)
    let g := mustApply g me (.chooseX 2)
    let g := mustApply g me (.target (.permanent oppBearPbb.id))
    mustApply g me .pay
  let pbbTriggerOnStack := gPbbCast.stack.any (fun se =>
    ((gPbbCast.object! se.objectId).triggeredAbility.map (·.effect.resolution)) == some .copySourceSpellXTimes)
  -- `.youTargetSomething` on targeted `.abilityActivated`
  let youTargetTrig : TriggeredAbility :=
    SharedTrigger.watch .youTargetDrawOnce |>.toTriggeredAbility
  let targetWatcherDef : CardDef := {
    name := "Phase12 Target Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[youTargetTrig]
  }
  let pingerDef : CardDef := {
    name := "Phase12 Pinger"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := { targeting := .of .creature, resolution := .tapTargets, phrase := "Tap target creature" }
    }]
  }
  let gTgtAct0 :=
    addPermanent (addPermanent (addPermanent afterDraw targetWatcherDef me me) pingerDef me me) bear opp opp
  let pingerId := (gTgtAct0.battlefield.filter (·.name == "Phase12 Pinger"))[0]!.id
  let oppBearTgt := (gTgtAct0.battlefield.filter (fun o => o.name == bear.name && gTgtAct0.controlledBy o opp))[0]!.id
  let gTgtAct1 :=
    let g := mustApply gTgtAct0 me (.activate pingerId 0)
    mustApply g me (.target (.permanent oppBearTgt))
  let youTargetActOk := gTgtAct1.stack.any (fun se =>
    (gTgtAct1.object! se.objectId).triggeredAbility == some youTargetTrig)
  -- Ward triggers: activated ability, triggered ability, retarget, fizzle when spell gone,
  -- decline counter cause, and uncounterable spell still prompting `.payWard`.
  let wardTwoBear : CardDef := { bear with name := "Phase12 Ward Bear", keywords := #[.ward (CostSpec.ofGeneric 2)] }
  let gWardBase := addPermanent (addPermanent afterDraw pingerDef me me) wardTwoBear opp opp
  let wardBearId := (gWardBase.battlefield.filter (·.name == "Phase12 Ward Bear"))[0]!.id
  let wardPingerId := (gWardBase.battlefield.filter (·.name == "Phase12 Pinger"))[0]!.id
  -- (a) Activated ability targeting opponent's Ward creature queues Ward on stack
  let gWardAct :=
    let g := mustApply gWardBase me (.activate wardPingerId 0)
    mustApply g me (.target (.permanent wardBearId))
  let wardActOnStack := gWardAct.stack.any (fun se =>
    (gWardAct.object! se.objectId).triggeredAbility == some (.onWard (CostSpec.ofGeneric 2)))
  -- (b) Triggered ability choosing opponent's Ward creature as target queues Ward
  let etbTapTrigger : TriggeredAbility :=
    TriggeredAbility.mkTrigger .thisEnters { targeting := .of .creature, resolution := .tapTargets, phrase := "Tap target creature" }
  let gWardTrig :=
    let g := gWardBase.putTriggeredAbilityOnStack me (gWardBase.object! wardPingerId) etbTapTrigger "enters"
    let g := g.promptTriggerTargetsIfNeeded
    mustApply g me (.target (.permanent wardBearId))
  let wardTrigQueued :=
    gWardTrig.stack.any (fun se => (gWardTrig.object! se.objectId).triggeredAbility == some (.onWard (CostSpec.ofGeneric 2))) ||
      gWardTrig.waitingTriggers.any (·.ability == .onWard (CostSpec.ofGeneric 2))
  -- (c) Retargeting a spell onto opponent's Ward creature queues Ward
  let gWardRetarget0 :=
    let g := addPermanent gWardBase hero opp opp
    let oppHeroId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let g := insertObject (g.addMana me (.colored .red) 1) lightningBolt me (.hand me)
    let boltId := ((g.player me).hand.filter (fun id => (g.object! id).name == "Lightning Bolt"))[0]!
    let g := mustApply g me (.cast boltId)
    let g := mustApply g me (.target (.permanent oppHeroId))
    mustApply g me .pay
  let retargetSpellId := gWardRetarget0.stack.back!.objectId
  let gWardRetarget1 := gWardRetarget0.retargetStackSpell retargetSpellId #[.permanent wardBearId]
  let wardRetargetQueued := gWardRetarget1.waitingTriggers.any (·.ability == .onWard (CostSpec.ofGeneric 2))
  -- (c2) Retargeting one slot of a copied two-target spell does not re-ward a
  --      permanent that was already targeted on the copy (CR 702.21a / 603.2).
  let twoTargetTap : CardDef := {
    name := "Phase12 Twin Frost"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some {
      targeting := .of (TargetSpec.creature.append .creature)
      resolution := .tapTargets
      phrase := "Tap two target creatures"
    }
  }
  let wardBear2Def : CardDef := { bear with name := "Phase12 Ward Bear Two", keywords := #[.ward (CostSpec.ofGeneric 3)] }
  let gCopyDelta :=
    let g := addPermanent (addPermanent (addPermanent gWardBase hero opp opp) bear opp opp) wardBear2Def opp opp
    let oppHeroId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let oppBearId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let wardBear2Id := (g.battlefield.filter (·.name == "Phase12 Ward Bear Two"))[0]!.id
    let g := insertObject g twoTargetTap me (.hand me)
    let twinId := ((g.player me).hand.filter (fun id => (g.object! id).name == "Phase12 Twin Frost"))[0]!
    let g := mustApply g me (.cast twinId)
    let g := mustApply g me (.target (.permanent wardBearId))
    let g := mustApply g me (.target (.permanent oppHeroId))
    -- Clear initial cast Ward trigger so we measure only the copy's retarget delta
    let g := g.change (.waitingTriggers #[])
    let origStackId := (g.stack.filter (fun se => (g.object! se.objectId).name == "Phase12 Twin Frost"))[0]!.objectId
    let gCopied := g.copyStackSpell (g.object! origStackId) me
    let copyId := gCopied.stack.back!.objectId
    let gRetargetNonWard := gCopied.setSpellTargetAt copyId 1 (.permanent oppBearId)
    let gRetargetSecondWard := gCopied.setSpellTargetAt copyId 1 (.permanent wardBear2Id)
    (gRetargetNonWard.waitingTriggers, gRetargetSecondWard.waitingTriggers)
  let copyRetargetDeltaOk :=
    gCopyDelta.1.isEmpty &&
    gCopyDelta.2.size == 1 &&
    gCopyDelta.2[0]!.ability == .onWard (CostSpec.ofGeneric 3)
  -- (d) Spell leaves stack before Ward resolves -> Ward resolves as no-op;
  --     Declining Ward counters with `.oneShotEffect` cause;
  --     Uncounterable spell still prompts `.payWard` and survives decline.
  let uncounterableBolt : CardDef :=
    { lightningBolt with name := "Phase12 Inescapable Bolt", staticAbilities := #[.spellCantBeCountered] }
  let castAtWard (spellDef : CardDef) : Game :=
    let g := insertObject (gWardBase.addMana me (.colored .red) 1) spellDef me (.hand me)
    let sid := ((g.player me).hand.filter (fun id => (g.object! id).name == spellDef.name))[0]!
    let g := mustApply g me (.cast sid)
    let g := mustApply g me (.target (.permanent wardBearId))
    mustApply g me .pay
  let gWardSpellOnStack := castAtWard lightningBolt
  let boltStackId := (gWardSpellOnStack.stack.filter (fun se => (gWardSpellOnStack.object! se.objectId).name == "Lightning Bolt"))[0]!.objectId
  let gWardSpellRemoved :=
    let (g, _) := gWardSpellOnStack.move boltStackId .exile none (cause := some testCause)
    mustApply (mustApply g me .pass) opp .pass
  let wardFizzledOk := gWardSpellRemoved.pending == .none
  let gWardDeclined :=
    let g := mustApply (mustApply gWardSpellOnStack me .pass) opp .pass
    mustApply g me .decline
  let wardCounterCauseOk := gWardDeclined.events.any (fun e =>
    match e.change, e.cause? with
    | .rules (.zone (.moved _ _ .stack (.graveyard _) .counter ..)),
      some (.oneShotEffect (some _) (some src) (some ctrl)) =>
      src == wardBearId && ctrl == opp
    | _, _ => false)
  let gWardUnc :=
    let g := castAtWard uncounterableBolt
    mustApply (mustApply g me .pass) opp .pass
  let wardUncPrompted :=
    match gWardUnc.pending with
    | .payWard p _ cost _ => (p == me) && cost.soleGenericMana? == some 2
    | _ => false
  let gWardUncDeclined := mustApply gWardUnc me .decline
  let wardUncSurvived := gWardUncDeclined.stack.any (fun se =>
    (gWardUncDeclined.object! se.objectId).name == "Phase12 Inescapable Bolt")
  let triggersAllOk :=
    cascadeStackItems.size == 1 &&
    pbbTriggerOnStack &&
    youTargetActOk &&
    wardActOnStack &&
    wardTrigQueued &&
    wardRetargetQueued &&
    copyRetargetDeltaOk &&
    wardFizzledOk &&
    wardCounterCauseOk &&
    wardUncPrompted &&
    wardUncSurvived

  -- 7. `CardDef.entersTappedUnlessPayLife` (The Black Gate) through CR 614.12 / 616.1
  let blackGateDef : CardDef := {
    name := "Phase12 Black Gate"
    supertypes := #[.legendary]
    types := #[.land]
    subtypes := #["Gate"]
    staticAbilities := #[.entersTappedUnlessPayLife 3]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .black, .const 1)])]
  }
  let gBg0 := insertObject afterDraw blackGateDef me (.hand me)
  let bgHandId := ((gBg0.player me).hand.filter (fun id => (gBg0.object! id).name == "Phase12 Black Gate"))[0]!
  -- (a) `playLand` accept (pays 3 life, enters untapped) vs decline (no life lost, enters tapped)
  let gBgPlay := mustApply gBg0 me (.playLand bgHandId)
  let bgPlayAsked :=
    match gBgPlay.pending with
    | .chooseReplacement p cs => p == me && cs.any (·.kind == .entersUntappedPayLife 3)
    | _ => false
  let gBgPaid := mustApply gBgPlay me .accept
  let bgPaidPerm := (gBgPaid.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  let gBgDeclined := mustApply gBgPlay me .decline
  let bgDeclinedPerm := (gBgDeclined.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  -- (b) Non-`playLand` `putOntoBattlefield`
  let (gBgPut, _) := gBg0.putOntoBattlefield bgHandId me (cause := some testCause)
  let bgPutAsked :=
    match gBgPut.pending with
    | .chooseReplacement p cs => p == me && cs.any (·.kind == .entersUntappedPayLife 3)
    | _ => false
  let gBgPutPaid := mustApply gBgPut me .accept
  let bgPutPerm := (gBgPutPaid.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  -- (c) CR 616.1c copy-entry onto The Black Gate
  let gBgCopy0 :=
    let g := insertObject afterDraw bear me (.hand me)
    let cid := ((g.player me).hand.filter (fun id => (g.object! id).name == bear.name))[0]!
    let g := g.createEffect
      (.replacement { id := { kind := .entersAsCopy }, affectedPlayer := me, kind := .entersAsCopy none blackGateDef } .untilEndOfTurn)
    (g.putOntoBattlefield cid me (cause := some testCause)).1
  let bgCopyAsked :=
    match gBgCopy0.pending with
    | .chooseReplacement p cs => p == me && cs.any (·.kind == .entersUntappedPayLife 3)
    | _ => false
  -- (d) Unpayable life (`lifeCantChange` or `life < 3`) auto-enters tapped without prompting
  let gBgLocked :=
    let g := gBg0.createEffect (.lifeCantChange me)
    mustApply g me (.playLand bgHandId)
  let bgLockedPerm := (gBgLocked.battlefield.filter (·.name == "Phase12 Black Gate"))[0]!
  let blackGateAllOk :=
    bgPlayAsked &&
    !bgPaidPerm.status.tapped && (gBgPaid.player me).life == 17 &&
    bgDeclinedPerm.status.tapped && (gBgDeclined.player me).life == 20 &&
    bgPutAsked && !bgPutPerm.status.tapped && (gBgPutPaid.player me).life == 17 &&
    bgCopyAsked &&
    gBgLocked.pending == .none && bgLockedPerm.status.tapped &&
    Game.replayEvents gBgPaid.events == gBgPaid &&
    Game.replayEvents gBgDeclined.events == gBgDeclined

  reversalAllOk &&
    replayAllOk &&
    exchangeAllOk &&
    combatStepAllOk &&
    ancestryAllOk &&
    triggersAllOk &&
    blackGateAllOk

/- Phase 13: CR 733.1 action-level mana-ability / library irreversibility &
`ProposalCheckpoint` batch-pause replay parity, mid-resolution cast reversal
continuations & deferred `PostCastCleanup`, interactive CR 614.1c / 614.12
as-enters choices without `StatusChange`, pausing `replaceUntap` / Saga
`replaceCountersPutChoice`, pain-land `DamageEvent.dealt`, CR 903.3 commander
zone-change persistence, CR 800.4d `leftGame` waiting-trigger cleanup, delayed
spell-copy / combat-Treasure / reflexive `WaitingTrigger` routing, pre-move
`PlayerEvent.revealed`, declined hand-or-library search shuffle, and
departed-source `lastKnownBefore?` LKI + Step 4 audits. -/
#guard
  let opp : PlayerId := ⟨1⟩

  -- 1. CR 733.1 action-level mana-ability / library irreversibility &
  --    `ProposalCheckpoint` batch-pause replay parity.
  let dorkDef : CardDef := {
    name := "Phase13 Mana Dork"
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 1
    toughness := some 1
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])]
  }
  let filterLandDef : CardDef := {
    name := "Phase13 Filter Land"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.combination (.explicit #[.colored .red, .colored .white]) (.const 2))
      (cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf])]
  }
  let bigSorceryDef : CardDef := {
    name := "Phase13 Five-Mana Sorcery"
    manaCost := ManaCost.ofGeneric 5
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let gAct0 :=
    let g := addPermanent (addPermanent (addPermanent afterDraw dorkDef me me) dorkDef me me) filterLandDef me me
    insertObject g bigSorceryDef me (.hand me)
  let dorks := gAct0.battlefield.filter (·.name == "Phase13 Mana Dork")
  let dork1Id := dorks[0]!.id
  let dork2Id := dorks[1]!.id
  let filterId := (gAct0.battlefield.filter (·.name == "Phase13 Filter Land"))[0]!.id
  let bigSpellH := ((gAct0.player me).hand.filter (fun id => (gAct0.object! id).name == "Phase13 Five-Mana Sorcery"))[0]!
  let gActProp := mustApply gAct0 me (.cast bigSpellH)
  -- Tap dork1 (upstream feeder) and dork2 (unrelated mana ability).
  let gActD1 := mustApply gActProp me (.tapForMana dork1Id (.colored .green))
  let gActD2 := mustApply gActD1 me (.tapForMana dork2Id (.colored .green))
  -- Simulate a discrete `.manaAbility (some filterId)` action that spends dork1's mana,
  -- taps `filterId`, adds `{R}{W}`, AND reveals/mills a library card inside the same action:
  -- CR 733.1 keeps the whole `filterId` mana ability AND upstream `dork1` (whose mana fed it),
  -- while reversing unrelated `dork2` and returning `bigSpellH` to hand.
  let gActRev :=
    let g := gActD2.change (.beginProposalAction (.manaAbility (some filterId)))
    let spentUnit : ManaUnit := { mana := .colored .green, source := some dork1Id }
    let g := g.record (GameEvent.manaSpent g.turnNumber me #[spentUnit] filterId
      (cause := some (.costPayment .mana me (some filterId))))
    let g := g.becomeTapped (g.object! filterId) (cause := some (.costPayment .tap me (some filterId)))
    let fSnap := g.snapshot (g.object! filterId)
    let g := g.record (GameEvent.abilityActivated g.turnNumber filterId fSnap me (.mana none))
    let g := g.record (GameEvent.manaAdded g.turnNumber me
      #[{ mana := .colored .red, source := some filterId },
        { mana := .colored .white, source := some filterId }])
    let g := g.mill me 1
    let g := g.change .endProposalAction
    mustApply g me .pay
  let actionIrrevOk :=
    gActRev.proposalCheckpoint.isNone &&
    gActRev.proposedSpell.isNone &&
    ((gActRev.player me).hand.contains bigSpellH) &&
    (gActRev.object! filterId).status.tapped &&
    (gActRev.object! dork1Id).status.tapped &&
    !(gActRev.object! dork2Id).status.tapped &&
    (gActRev.player me).manaPool.red == 1 &&
    (gActRev.player me).manaPool.white == 1 &&
    (gActRev.player me).manaPool.green == 0 &&
    (gActRev.player me).graveyard.size == (gAct0.player me).graveyard.size + 1 &&
    Game.replayEvents gActRev.events == gActRev

  -- `ProposalCheckpoint` batch-pause replay parity + pain-land `DamageEvent.dealt` (group 5):
  let painLandDef : CardDef := {
    name := "Phase13 Pain Land"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)]),
      ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored .red, .colored .white]) (.const 1)) (damageYou := 1)
    ]
  }
  let gPainCkpt0 :=
    let g := addPermanent afterDraw painLandDef me me
    let g := insertObject g bigSorceryDef me (.hand me)
    let pid := (g.battlefield.filter (·.name == "Phase13 Pain Land"))[0]!.id
    -- Two competing damage replacements so tapping painLand pauses on `Pending.chooseReplacement`
    -- while `proposalCheckpoint` is active!
    let g := g.createEffect
      (.replacement { id := { kind := .multiplyDamage, object := some pid, player := some me, grantor := some ⟨9001⟩ },
                      affectedPlayer := me, kind := .multiplyDamage (some pid) 2 } .untilEndOfTurn)
    g.createEffect
      (.replacement { id := { kind := .addNoncombatDamage, object := some pid, player := some me, grantor := some ⟨9002⟩ },
                      affectedPlayer := me, kind := .addNoncombatDamage (some pid) 1 } .untilEndOfTurn)
  let painCkptId := (gPainCkpt0.battlefield.filter (·.name == "Phase13 Pain Land"))[0]!.id
  let painSpellH := ((gPainCkpt0.player me).hand.filter (fun id => (gPainCkpt0.object! id).name == "Phase13 Five-Mana Sorcery"))[0]!
  let gPainProp := mustApply gPainCkpt0 me (.cast painSpellH)
  let gPainPaused := mustApply gPainProp me (.tapForMana painCkptId (.colored .red))
  let painPausedAtChoice :=
    match gPainPaused.pending with
    | .chooseReplacement p cs =>
      p == me && cs.size == 2 && gPainPaused.proposalCheckpoint.isSome
    | _ => false
  let painMidReplayOk := Game.replayEvents gPainPaused.events == gPainPaused
  let gPainResolved :=
    match gPainPaused.pending with
    | .chooseReplacement _ cs => mustApply gPainPaused me (.chooseReplacement cs[0]!)
    | _ => gPainPaused
  let gPainRev := mustApply gPainResolved me .pay
  let batchPauseReplayOk :=
    painPausedAtChoice &&
    painMidReplayOk &&
    gPainResolved.pending == .activateManaAbilities me &&
    (gPainResolved.player me).life == 17 && -- (1 * 2) + 1 = 3 damage dealt
    Game.replayEvents gPainResolved.events == gPainResolved &&
    gPainRev.proposalCheckpoint.isNone &&
    !(gPainRev.object! painCkptId).status.tapped &&
    (gPainRev.player me).life == 20 &&
    ((gPainRev.player me).hand.contains painSpellH) &&
    Game.replayEvents gPainRev.events == gPainRev

  -- 2. Mid-resolution cast reversal continuations & deferred `PostCastCleanup`.
  let impossibleRemDef : CardDef := {
    name := "Phase13 Impossible Removal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .creature
      resolution := .destroyTarget
      phrase := "Destroy target creature"
    }
  }
  let freeDrawDef : CardDef := {
    name := "Phase13 Free Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  -- (a) Deferred `PostCastCleanup.lookedBottom`: library order untouched while paused on
  --     `Pending.chooseTargets`, then bottomed when `becomeCast` completes OR when
  --     `reverseProposedSpell` aborts the cast.
  let gLook0 :=
    let g := addPermanent afterDraw bear opp opp
    let g := insertObject g freeDrawDef me (.library me)
    insertObject g impossibleRemDef me (.library me)
  let lookBearId := (gLook0.battlefield.filter (·.name == bear.name))[0]!.id
  let remLibId := (gLook0.player me).library.back!
  let drawLibId := (gLook0.player me).library[(gLook0.player me).library.size - 2]!
  let gLookAsk := gLook0.change (.pending (.mayCastFromLooked me #[remLibId, drawLibId] 10))
  -- Propose targeted `remLibId`: pauses at `Pending.chooseTargets` BEFORE bottoming `drawLibId`!
  let gLookPaused := mustApply gLookAsk me (.cast remLibId)
  let lookDeferredDuringTargets :=
    gLookPaused.pending == .chooseTargets me &&
    (gLookPaused.player me).library.back? == some drawLibId &&
    Game.replayEvents gLookPaused.events == gLookPaused
  -- Branch 1: choosing legal target completes `becomeCast` and runs `PostCastCleanup.lookedBottom` on `drawLibId`.
  let gLookCast :=
    let g1 := mustApply gLookPaused me (.target (.permanent lookBearId))
    match g1.pending with
    | .resolveRandom (.orderInto ..) => mustApply g1 me (.supplyOrder #[])
    | _ => g1
  let lookPostCastBottomOk :=
    gLookCast.stack.size == 1 &&
    (gLookCast.player me).library[0]? != some drawLibId ||
      (gLookCast.object! (gLookCast.followMoved drawLibId)).zone == .library me
  let lookCastBottomed :=
    gLookCast.stack.size == 1 &&
    gLookCast.postCastCleanup.isNone &&
    (gLookCast.player me).library[0]? == some (gLookCast.followMoved drawLibId) &&
    Game.replayEvents gLookCast.events == gLookCast
  -- Branch 2: reversing the paused proposal returns `remLibId` to `.library` and restores the
  -- CR 733.1 checkpoint taken while `Pending.mayCastFromLooked` was still open (Phase 24 item
  -- 2): nothing is bottomed and the choice is offered again.
  let gLookRev :=
    let g1 := gLookPaused.reverseProposedSpell
    match g1.pending with
    | .resolveRandom (.orderInto ..) => mustApply g1 me (.supplyOrder #[])
    | _ => g1
  let lookRevRestored :=
    gLookRev.stack.isEmpty &&
    gLookRev.postCastCleanup.isNone &&
    gLookRev.pending == .mayCastFromLooked me #[remLibId, drawLibId] 10 &&
    (gLookRev.player me).library.back? == some remLibId &&
    lookPostCastBottomOk &&
    lookDeferredDuringTargets &&
    Game.replayEvents gLookRev.events == gLookRev
  let lookPostCastBottomOk := lookCastBottomed
  -- (b) Reversing a paused mid-resolution free cast (modal + kicker `{5}` failing `.pay`)
  --     resumes `triggerSequenceRest` (`gainLife 1`).
  let modalKickerDef : CardDef := {
    name := "Phase13 Modal Kicker"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    keywords := #[.kicker (CostSpec.ofGeneric 5)]
    spellModes := #[
      { resolution := .draw 1, phrase := "Draw a card" },
      { resolution := .gainLife 1, phrase := "Gain 1 life" }
    ]
  }
  let gSeqRev :=
    let g := insertObject afterDraw modalKickerDef me (.hand me)
    let rid := ((g.player me).hand.filter (fun id => (g.object! id).name == "Phase13 Modal Kicker"))[0]!
    let g := (g.change (.pushContinuationFrame {})).change (.triggerSequenceRest (some {
      controller := me
      ability := TriggeredAbility.ofPattern .youCastNoncreature "" (.draw 1)
      sourceId := none
      targets := #[]
      steps := [.gainLife (.fixed 1)]
    }))
    let gPaused := g.castAsPartOfResolution me rid
    let gMode := mustApply gPaused me (.chooseMode 0)
    let gKick := mustApply gMode me (.announceKicker true)
    mustApply gKick me .pay
  let seqContOk :=
    gSeqRev.triggerSequenceRest.isNone &&
    (gSeqRev.player me).life == 21 &&
    Game.replayEvents gSeqRev.events == gSeqRev
  -- (c) Doom Reigns `.mayCastUpToFromExile`: reversing a paused first exiled cast restores the choice for the second!
  let gQueueRev :=
    let g := insertObject (insertObject afterDraw modalKickerDef me .exile) freeDrawDef me .exile
    let exSac := (g.objects.filter (fun o => o.name == "Phase13 Modal Kicker" && o.zone == .exile))[0]!.id
    let exDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := g.beginFraChoice me (.mayCastUpToFromExile #[exSac, exDraw] 2) "cast exiled"
    let gPaused := mustApply g me (.choosePermanents #[exSac])
    let gMode := mustApply gPaused me (.chooseMode 0)
    let gKick := mustApply gMode me (.announceKicker true)
    let gRev := mustApply gKick me .pay
    let gSecond := mustApply gRev me (.choosePermanents #[exDraw])
    let gDone := mustApply gSecond me .decline
    (gDone, exSac, exDraw)
  let queueContOk :=
    gQueueRev.1.pendingMayCastFromExile.isNone &&
    (gQueueRev.1.object! gQueueRev.2.1).zone == .exile &&
    gQueueRev.1.stack.size == 1 &&
    (gQueueRev.1.object! gQueueRev.1.stack[0]!.objectId).name == "Phase13 Free Draw" &&
    Game.replayEvents gQueueRev.1.events == gQueueRev.1
  let continuationsAllOk := lookRevRestored && lookPostCastBottomOk && seqContOk && queueContOk

  -- 3. Interactive CR 614.1c / 614.12 as-enters choices & `StatusChange` removal.
  let roomDef : CardDef := {
    name := "Phase13 Room of Refuge"
    types := #[.land]
    staticAbilities := #[.entersTappedChooseColor]
    activatedAbilities := #[ActivatedAbility.manaAbility (.oneOf .chosenColorOnSource (.const 1))]
  }
  let partyDef : CardDef := {
    name := "Phase13 Unexpected Party"
    types := #[.enchantment]
    staticAbilities := #[.asEntersChooseCreatureType]
  }
  let gollumDef : CardDef := {
    name := "Phase13 Gollum"
    types := #[.creature]
    subtypes := #["Halfling"]
    power := some 2
    toughness := some 2
    staticAbilities := #[.asEntersChooseOddEven]
  }
  let mageDef : CardDef := {
    name := "Phase13 Meddling Mage"
    types := #[.creature]
    subtypes := #["Human", "Wizard"]
    power := some 2
    toughness := some 2
    staticAbilities := #[.asEntersChooseNonlandCardName]
  }
  let emissaryDef : CardDef := {
    name := "Phase13 Emissary"
    types := #[.creature]
    subtypes := #["Angel"]
    power := some 7
    toughness := some 7
    staticAbilities := #[.asEntersChooseCardType]
  }
  let siegeDef : CardDef := {
    name := "Phase13 Windcrag Siege"
    types := #[.enchantment]
    staticAbilities := #[.asEntersChooseNamedAnchors #["Mardu", "Jeskai"]]
  }
  let mirrorDef : CardDef := {
    name := "Phase13 Cursed Mirror"
    types := #[.artifact]
    staticAbilities := #[.asEntersMayCopyCreatureHasteUntilEot]
  }
  let sanctumDef : CardDef := {
    name := "Phase13 Sanctum"
    types := #[.land]
    staticAbilities := #[.entersTappedUnlessBehold .villain]
  }
  let villainCard : CardDef :=
    creature "Phase13 Hand Villain" ManaCost.empty #["Villain"] 2 2
  let putAndResolve (base : Game) (cd : CardDef) (act : Game → Game) : Game :=
    let g := insertObject base cd me (.hand me)
    let hid := ((g.player me).hand.filter (fun id => (g.object! id).name == cd.name))[0]!
    let (g1, _) := g.putOntoBattlefield hid me (cause := some testCause)
    act g1
  let pickRepl (pred : ReplacementEffectKind → Bool) (g : Game) : Game :=
    match g.pending with
    | .chooseReplacement p cs =>
      match cs.find? (fun c => pred c.kind) with
      | some rid => mustApply g p (.chooseReplacement rid)
      | none => g
    | _ => g
  let gRoom := putAndResolve afterDraw roomDef
    (pickRepl (fun | .asEntersChooseColor .blue => true | _ => false))
  let roomPerm := (gRoom.battlefield.filter (·.name == "Phase13 Room of Refuge"))[0]!
  let roomMoveAfterOk :=
    gRoom.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ afterSnap _ .battlefield ..)) =>
        afterSnap.id == some roomPerm.id && afterSnap.chosenColor == some .blue
      | _ => false)
  let gParty := putAndResolve afterDraw partyDef (fun g => mustApply g me (.chooseName "Elf"))
  let partyPerm := (gParty.battlefield.filter (·.name == "Phase13 Unexpected Party"))[0]!
  let gGollum := putAndResolve afterDraw gollumDef
    (pickRepl (fun | .asEntersChooseOdd true => true | _ => false))
  let gollumPerm := (gGollum.battlefield.filter (·.name == "Phase13 Gollum"))[0]!
  let gMage := putAndResolve afterDraw mageDef (fun g => mustApply g me (.chooseName "Lightning Bolt"))
  let magePerm := (gMage.battlefield.filter (·.name == "Phase13 Meddling Mage"))[0]!
  let gEmissary := putAndResolve afterDraw emissaryDef
    (pickRepl (fun | .asEntersChooseCardType .creature => true | _ => false))
  let emissaryPerm := (gEmissary.battlefield.filter (·.name == "Phase13 Emissary"))[0]!
  let gSiege := putAndResolve afterDraw siegeDef
    (pickRepl (fun | .asEntersChooseAnchor "Mardu" => true | _ => false))
  let siegePerm := (gSiege.battlefield.filter (·.name == "Phase13 Windcrag Siege"))[0]!
  let gMirrorBase := addPermanent afterDraw hero opp opp
  let heroOnBfId := (gMirrorBase.battlefield.filter (·.name == hero.name))[0]!.id
  let gMirrorCopy := putAndResolve gMirrorBase mirrorDef
    (pickRepl (fun | .entersAsCopyCreatureUntilEot tid => tid == heroOnBfId | _ => false))
  let gMirrorDecl := putAndResolve gMirrorBase mirrorDef
    (pickRepl (fun | .declineEntersAsCopy => true | _ => false))
  let gSanctumBase := insertObject afterDraw villainCard me (.hand me)
  let villainHandId := ((gSanctumBase.player me).hand.filter (fun id => (gSanctumBase.object! id).name == "Phase13 Hand Villain"))[0]!
  let gSanctumAcc := putAndResolve gSanctumBase sanctumDef
    (pickRepl (fun | .entersUntappedBehold bid _ => bid == villainHandId | _ => false))
  let sanctumAccPerm := (gSanctumAcc.battlefield.filter (·.name == "Phase13 Sanctum"))[0]!
  let gSanctumDec := putAndResolve gSanctumBase sanctumDef
    (pickRepl (fun | .entersTappedDeclineBehold => true | _ => false))
  let sanctumDecPerm := (gSanctumDec.battlefield.filter (·.name == "Phase13 Sanctum"))[0]!
  let asEntersAllOk :=
    roomPerm.status.chosenColor == some .blue && roomMoveAfterOk &&
    partyPerm.status.chosenCreatureType == some CardSubtype.elf &&
    gollumPerm.status.chosenOdd == some true &&
    magePerm.status.chosenName == some "Lightning Bolt" &&
    emissaryPerm.status.chosenCardType == some .creature &&
    siegePerm.status.chosenAnchor == some "Mardu" &&
    (gMirrorCopy.battlefield.filter (fun o => gMirrorCopy.name o == hero.name)).size == 2 &&
    (gMirrorDecl.battlefield.filter (fun o => gMirrorDecl.name o == "Phase13 Cursed Mirror")).size == 1 &&
    !sanctumAccPerm.status.tapped &&
    gSanctumAcc.events.any (fun e =>
      match e.change with
      | .rules (.player (.revealed p ids)) => p == me && ids == #[villainHandId]
      | _ => false) &&
    sanctumDecPerm.status.tapped &&
    [gRoom, gParty, gGollum, gMage, gEmissary, gSiege, gMirrorCopy, gMirrorDecl, gSanctumAcc, gSanctumDec].all
      (fun g => Game.replayEvents g.events == g)

  -- 4. Pausing `replaceUntap` & Saga `addLoreCounters` `replaceCountersPutChoice`.
  let gUntap0 :=
    let g := addPermanent afterDraw bear me me
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.becomeTapped (g.object! bid) (cause := some testCause)
    let g := g.recordPutCounters bid .stun 2 (some me) (cause := some testCause)
    g.createEffect
      (.replacement { id := { kind := .stunCounterUntap, object := some bid, grantor := some ⟨8888⟩ },
                      affectedPlayer := me, kind := .stunCounterUntap bid } .untilEndOfTurn)
  let stunBearId := (gUntap0.battlefield.filter (·.name == bear.name))[0]!.id
  let gUntapPaused := gUntap0.untapPermanent (gUntap0.object! stunBearId) (cause := some testCause)
  let untapAsked :=
    match gUntapPaused.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2
    | _ => false
  let gUntapDone :=
    match gUntapPaused.pending with
    | .chooseReplacement _ cs => mustApply gUntapPaused me (.chooseReplacement cs[0]!)
    | _ => gUntapPaused
  let stunAfter := gUntapDone.object! stunBearId
  let untapReplacedCauseOk :=
    gUntapDone.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.counters (.object snap) .stun (.removed 1) _)), some (.replaced rid _) =>
        snap.id == some stunBearId && rid.kind == .stunCounterUntap
      | _, _ => false)
  -- `untapPermanent` with `duringUntapStep := true` records `PermanentEvent.untapped` (not stun removal)
  -- and respects an explicit caller `cause` while defaulting `none` to `.turnBased .untapAll`:
  let gUntapStep0 :=
    let g := addPermanent afterDraw bear me me
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    (g.becomeTapped (g.object! bid) (cause := some testCause), bid)
  let preUntapStepIdx := gUntapStep0.1.events.size
  let gUntapStepDef := gUntapStep0.1.untapPermanent (gUntapStep0.1.object! gUntapStep0.2) (duringUntapStep := true)
  let gUntapStepExplicit :=
    gUntapStep0.1.untapPermanent (gUntapStep0.1.object! gUntapStep0.2)
      (duringUntapStep := true) (cause := some testCause)
  let untapStepSlice := gUntapStepDef.events.extract preUntapStepIdx gUntapStepDef.events.size
  let untapStepExplicitSlice := gUntapStepExplicit.events.extract preUntapStepIdx gUntapStepExplicit.events.size
  let untapStepFlagOk :=
    !(gUntapStepDef.object! gUntapStep0.2).status.tapped &&
    untapStepSlice.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.untapped snap)), some (.turnBased .untapAll) =>
        snap.id == some gUntapStep0.2
      | _, _ => false) &&
    !untapStepSlice.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters _ .stun _ _)) => true
      | _ => false) &&
    untapStepExplicitSlice.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.untapped snap)), some c =>
        snap.id == some gUntapStep0.2 && c == testCause
      | _, _ => false) &&
    Game.replayEvents gUntapStepDef.events == gUntapStepDef &&
    Game.replayEvents gUntapStepExplicit.events == gUntapStepExplicit

  let sagaDef : CardDef := {
    name := "Phase13 Saga"
    types := #[.enchantment]
    subtypes := #["Saga"]
    triggeredAbilities := #[
      TriggeredAbility.sagaChapter 1 (Effect.gainLife 1),
      TriggeredAbility.sagaChapter 2 (Effect.gainLife 1),
      TriggeredAbility.sagaChapter 3 (Effect.gainLife 1),
      TriggeredAbility.sagaChapter 4 (Effect.gainLife 1),
      TriggeredAbility.sagaChapter 5 (Effect.gainLife 1)
    ]
  }
  let gSaga0 :=
    let g := addPermanent afterDraw sagaDef me me
    let sid := (g.battlefield.filter (·.name == "Phase13 Saga"))[0]!.id
    let g := g.createEffect
      (.replacement { id := { kind := .addCountersPut, object := some sid, grantor := some ⟨8889⟩ },
                      affectedPlayer := me, kind := .modifyCountersPut (some sid) none (add := 1) (mult := 1) } .untilEndOfTurn)
    g.createEffect
      (.replacement { id := { kind := .multiplyCountersPut, object := some sid, grantor := some ⟨8890⟩ },
                      affectedPlayer := me, kind := .modifyCountersPut (some sid) none (add := 0) (mult := 2) } .untilEndOfTurn)
  let sagaId := (gSaga0.battlefield.filter (·.name == "Phase13 Saga"))[0]!.id
  let preLore := (gSaga0.object! sagaId).status.lore
  let gSagaPaused := gSaga0.addLoreCounters (gSaga0.object! sagaId) 1
  let sagaAsked :=
    match gSagaPaused.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2
    | _ => false
  -- Choose `+1` first (`(1 + 1) * 2 = 4` lore counters added!).
  let gSagaDone :=
    pickRepl (fun | .addCountersPut => true | _ => false) gSagaPaused
  let sagaReplacedCauseOk :=
    gSagaDone.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.counters (.object snap) .lore (.put 4) _)), some (.replaced ..) =>
        snap.id == some sagaId
      | _, _ => false)
  let untapAndSagaOk :=
    untapAsked && stunAfter.status.tapped && stunAfter.status.stun == 1 && untapReplacedCauseOk &&
    untapStepFlagOk &&
    Game.replayEvents gUntapDone.events == gUntapDone &&
    sagaAsked && (gSagaDone.object! sagaId).status.lore == preLore + 4 && sagaReplacedCauseOk &&
    Game.replayEvents gSagaDone.events == gSagaDone

  -- 5. Pain-land `DamageEvent.dealt` + prevention (CR 120.3a / 615).
  let gPainPlain0 := addPermanent afterDraw painLandDef me me
  let painPlainId := (gPainPlain0.battlefield.filter (·.name == "Phase13 Pain Land"))[0]!.id
  let prePainEv := gPainPlain0.events.size
  let gPainTapped := mustApply gPainPlain0 me (.tapForMana painPlainId (.colored .red))
  let painSlice := gPainTapped.events.extract prePainEv gPainTapped.events.size
  let painDealtEventOk :=
    painSlice.any (fun e =>
      match e.change with
      | .rules (.damage (.dealt pkts)) =>
        pkts.any (fun pkt =>
          pkt.recipient == .player me && pkt.amount == 1 && !pkt.combat &&
            pkt.source.id == some painPlainId)
      | _ => false) &&
    painSlice.any (fun e =>
      match e.change with
      | .rules (.life (.lost p 1 true false)) => p == me
      | _ => false)
  let gPainProt0 := gPainPlain0.createEffect (.protectionFromEverything me)
  let gPainProtTapped := mustApply gPainProt0 me (.tapForMana painPlainId (.colored .red))
  let painAllOk :=
    painDealtEventOk &&
    (gPainTapped.player me).life == 19 &&
    (gPainTapped.player me).manaPool.red == 1 &&
    (gPainProtTapped.player me).life == 20 &&
    (gPainProtTapped.player me).manaPool.red == 1 &&
    Game.replayEvents gPainTapped.events == gPainTapped &&
    Game.replayEvents gPainProtTapped.events == gPainProtTapped

  -- 6. CR 903.3 Commander zone-change persistence & `Start.materializeSeat`.
  let cmdDef : CardDef := {
    (creature "Phase13 Commander" (ManaCost.ofGeneric 2) #["Hero"] 3 3) with
    supertypes := #[.legendary]
  }
  let cmdCfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, commanders := #[cmdDef] },
      { name := "Nissa", deck := testGreenDeck }
    ]
    format := .constructed
    seed := 7
    startingPlayer := some 0
  }
  let gCmdStart :=
    match Start.start cmdCfg with
    | .ok g => keepOpeningHands g 8
    | .error e => panic! e
  let cmdInit := (gCmdStart.objects.filter (fun o => o.name == "Phase13 Commander"))[0]!
  let (gCmd1, cmdStackId) := gCmdStart.move cmdInit.id .stack (some me) (cause := some testCause)
  let (gCmd2, cmdBfId) := gCmd1.move cmdStackId .battlefield (some me) (cause := some testCause)
  let (gCmd3, cmdGyId) := gCmd2.move cmdBfId (.graveyard me) none (cause := some testCause)
  let (gCmd4, cmdHandId) := gCmd3.move cmdGyId (.hand me) none (cause := some testCause)
  let (gCmd5, cmdLibId) := gCmd4.move cmdHandId (.library me) none (libraryPosition := some .top) (cause := some testCause)
  let (gCmd6, cmdExId) := gCmd5.move cmdLibId .exile none (cause := some testCause)
  let commanderAllOk :=
    cmdInit.zone == .command && cmdInit.isCommander &&
    (gCmd1.object! cmdStackId).isCommander &&
    (gCmd2.object! cmdBfId).isCommander &&
    (gCmd3.object! cmdGyId).isCommander &&
    (gCmd4.object! cmdHandId).isCommander &&
    (gCmd5.object! cmdLibId).isCommander &&
    (gCmd6.object! cmdExId).isCommander &&
    Game.replayEvents gCmd6.events == gCmd6

  -- 7. CR 800.4d `leftGame` waiting-trigger cleanup via single writer `applyPlayerEvent`.
  let threeCfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed := 3
    startingPlayer := some 0
  }
  let gThree0 :=
    match Start.start threeCfg with
    | .ok g => keepOpeningHands g 12
    | .error e => panic! e
  let gThreeQueued :=
    let g := gThree0.putReflexiveTrigger ⟨0⟩ none { resolution := .draw 1, phrase := "Draw a card" } (deferToPriority := true)
    g.putReflexiveTrigger ⟨1⟩ none { resolution := .draw 1, phrase := "Draw a card" } (deferToPriority := true)
  let gThreeConceded := gThreeQueued.concede ⟨0⟩
  -- Simultaneous SBA / leaving-caused reflexive triggers (Head of the Hunt, CR 800.4d):
  -- when player `⟨0⟩` loses the game in the same SBA sweep where an opponent's creature dies
  -- under `⟨0⟩`'s Head of the Hunt (or when `putReflexiveTrigger` runs after `⟨0⟩` left),
  -- no `waitingTriggers` controlled by `⟨0⟩` remain or are enqueued.
  let headTestDef : CardDef := {
    bear with
    name := "Phase13 Head of the Hunt"
    staticAbilities := #[.exileOppDeathCreateWolf]
  }
  let gThreeSba0 :=
    let g := addPermanent (addPermanent gThree0 headTestDef ⟨0⟩ ⟨0⟩) bear ⟨1⟩ ⟨1⟩
    let oppBear := (g.battlefield.filter (fun o => o.name == bear.name && o.owner == ⟨1⟩))[0]!
    let g := g.markDamageOn oppBear 2 "lethal" (cause := some testCause)
    g.loseLife ⟨0⟩ 20 (cause := some testCause)
  let gThreeSbaDone :=
    (gThreeSba0.checkSBA).putReflexiveTrigger ⟨0⟩ none
      { resolution := .draw 1, phrase := "Draw a card" } (deferToPriority := true)
  let leftGameTriggersOk :=
    gThreeQueued.waitingTriggers.size == 2 &&
    !gThreeConceded.over &&
    !gThreeConceded.waitingTriggers.any (·.controller == ⟨0⟩) &&
    (gThreeConceded.waitingTriggers.any (·.controller == ⟨1⟩) ||
      gThreeConceded.stack.any (·.controller == ⟨1⟩)) &&
    Game.replayEvents gThreeConceded.events == gThreeConceded &&
    (gThreeSbaDone.player ⟨0⟩).leftTheGame &&
    !gThreeSbaDone.waitingTriggers.any (·.controller == ⟨0⟩) &&
    Game.replayEvents gThreeSbaDone.events == gThreeSbaDone

  -- 8. Delayed spell-copy, combat-Treasure `matchTriggers`, & reflexive `WaitingTrigger` routing.
  let gDt0 :=
    let g := insertObject afterDraw freeDrawDef me (.hand me)
    let (g, dtCause1) := g.allocDelayedCause (some me)
    let g := g.registerDelayedTrigger { controller := me, kind := .copyNextInstantSorceryThisTurn, cause := dtCause1 }
    let (g, dtCause2) := g.allocDelayedCause (some me)
    g.registerDelayedTrigger { controller := me, kind := .lokiCopyNextInstantSorceryThisTurn none 2, cause := dtCause2 }
  let dtSpellH := ((gDt0.player me).hand.filter (fun id => (gDt0.object! id).name == "Phase13 Free Draw"))[0]!
  let handPreDt := (gDt0.player me).hand.size
  let gDtCast := mustApply gDt0 me (.cast dtSpellH)
  let gDtStacked := mustApply gDtCast me (.stackTriggers #[0, 1])
  -- Stack has [original, trig1, trig2]: resolve trig2 -> copy1, resolve copy1, resolve trig1 -> copy2, resolve copy2, resolve original!
  let gDtResolved := gDtStacked.resolveTop.resolveTop.resolveTop.resolveTop.resolveTop
  let dtEventsOk :=
    gDtResolved.delayedTriggers.isEmpty &&
    (gDtResolved.player me).hand.size == handPreDt - 1 + 3 &&
    gDtResolved.events.any (fun e => match e.change with | .rules (.delayedTrigger (.consumed _)) => true | _ => false) &&
    gDtResolved.events.any (fun e => match e.change with | .rules (.stackObject (.copied ..)) => true | _ => false) &&
    Game.replayEvents gDtResolved.events == gDtResolved
  -- Unconsumed delayed spell-copy expires at cleanup (`DelayedTriggerEvent.expired`).
  let gDtExp :=
    let (g, c) := afterDraw.allocDelayedCause (some me)
    let g := g.registerDelayedTrigger { controller := me, kind := .copyNextInstantSorceryThisTurn, cause := c }
    g.clearTurnActivations
  let dtExpireOk :=
    gDtExp.delayedTriggers.isEmpty &&
    gDtExp.events.any (fun e => match e.change with | .rules (.delayedTrigger (.expired _)) => true | _ => false) &&
    Game.replayEvents gDtExp.events == gDtExp

  -- Combat-damage Treasure separation: `combatDamageCreatesTreasureUntilEot` (1 Treasure on player only)
  -- vs Reaver Cleaver `equippedGetsTrampleAndCombatTreasures` (`that many` Treasures on player/planeswalker).
  let bigBear : CardDef := creature "Phase13 Big Bear" ManaCost.empty #["Bear"] 3 3
  let cleaverDef : CardDef := {
    name := "Phase13 Cleaver"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.equippedGetsTrampleAndCombatTreasures 1 1]
  }
  let gTrOne :=
    let g := addPermanent afterDraw bigBear me me
    let bid := (g.battlefield.filter (·.name == "Phase13 Big Bear"))[0]!.id
    let g := g.createEffect (.combatDamageCreatesTreasureUntilEot bid)
    let g := g.markAttacking bid (some (.player opp))
    let g := g.record (GameEvent.combatDamageAssigned g.turnNumber true #[{ source := bid, toPlayer := 3 }])
    (g.dealAssignedCombatDamage.receivePriority me).resolveTop
  let gTrCleaver :=
    let g := addPermanent (addPermanent afterDraw bigBear me me) cleaverDef me me
    let bearPerm := (g.battlefield.filter (·.name == "Phase13 Big Bear"))[0]!
    let cleaverPerm := (g.battlefield.filter (·.name == "Phase13 Cleaver"))[0]!
    let g := g.attachSourceTo cleaverPerm bearPerm
    let armed := (g.battlefield.filter (·.name == "Phase13 Big Bear"))[0]!
    let g := g.markAttacking armed.id (some (.player opp))
    let g := g.record (GameEvent.combatDamageAssigned g.turnNumber true #[{ source := armed.id, toPlayer := 4 }])
    (g.dealAssignedCombatDamage.receivePriority me).resolveTop
  let treasureRoutingOk :=
    gTrOne.countSubtype me .treasure == 1 &&
    gTrCleaver.countSubtype me .treasure == 4 &&
    Game.replayEvents gTrOne.events == gTrOne &&
    Game.replayEvents gTrCleaver.events == gTrCleaver &&
    dtEventsOk && dtExpireOk

  -- 9. Pre-move `PlayerEvent.revealed` & declined hand-or-library search shuffle.
  let preRevIdx := afterDraw.events.size
  let (gRevLib, hitId?, _) :=
    afterDraw.revealUntil me 5 (fun o => o.printed.isLand) #[] (cause := some testCause)
  let revSlice := gRevLib.events.extract preRevIdx gRevLib.events.size
  let preMoveRevealOk :=
    hitId?.isSome &&
    revSlice.any (fun e => match e.change with | .rules (.player (.revealed p ids)) => p == me && !ids.isEmpty | _ => false) &&
    !revSlice.any (fun e => match e.change with | .rules (.zone _) => true | _ => false) &&
    Game.replayEvents gRevLib.events == gRevLib

  let gSearch0 :=
    let g := insertObject (insertObject afterDraw bear me (.hand me)) bear me (.library me)
    g.beginLibrarySearch me (·.isCreature) "creature card" .battlefieldFromHandOrLibrary (alsoHand := true)
  let preSearchDecIdx := gSearch0.events.size
  let gSearchDeclined :=
    let g1 := mustApply gSearch0 me .decline
    match g1.pending with
    | .resolveRandom (.shuffleLibrary p) => mustApply g1 p (.supplyOrder #[])
    | _ => g1
  let decSlice := gSearchDeclined.events.extract preSearchDecIdx gSearchDeclined.events.size
  let searchDeclineOk :=
    decSlice.any (fun e => match e.change with | .rules (.player (.searched p _ _)) => p == me | _ => false) &&
    decSlice.any (fun e => match e.change with | .rules (.player (.shuffled p _)) => p == me | _ => false) &&
    Game.replayEvents gSearchDeclined.events == gSearchDeclined &&
    preMoveRevealOk

  -- 10. Departed-source `lastKnownBefore?` LKI & Step 4 audits (`effectiveMaxHandSize` timestamps,
  --     filter-scoped Layer 2 control expiration).
  let lethalLifelinker : CardDef := {
    (creature "Phase13 Lifelinker" ManaCost.empty #["Vampire"] 1 1) with
    keywords := #[Keyword.lifelink, Keyword.deathtouch]
  }
  let toughBlocker : CardDef := creature "Phase13 Wall" ManaCost.empty #["Wall"] 0 5
  let gLki0 := addPermanent (addPermanent afterDraw lethalLifelinker me me) toughBlocker opp opp
  let vamp := (gLki0.battlefield.filter (·.name == "Phase13 Lifelinker"))[0]!
  let wall := (gLki0.battlefield.filter (·.name == "Phase13 Wall"))[0]!
  -- Vampire leaves battlefield BEFORE its 1 damage resolves: LKI preserves lifelink + deathtouch!
  let (gLkiLeft, _) := gLki0.move vamp.id .exile none (cause := some testCause)
  let vampLki? := gLkiLeft.lastKnownBefore? vamp.id
  let gLkiDmg :=
    (gLkiLeft.dealDamageToPermanent wall 1 (source := vampLki?) (cause := some testCause)).checkSBA
  -- CR 616.1 damage replacement choices on a departed source whose lifelink + deathtouch were
  -- granted on the battlefield (so `followMoved` to the graveyard card would drop them):
  let gLkiChoiceBase :=
    let g := addPermanent (addPermanent afterDraw bear me me) toughBlocker opp opp
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.createEffect
      (.keywordsUntilEot bid (#[Keyword.lifelink, Keyword.deathtouch]))
      (cause := some testCause)
    let (g, _) := g.move bid (.graveyard me) none (cause := some testCause)
    let g := g.createEffect
      (.replacement { id := { kind := .noncombatDamagePlusOne, grantor := some ⟨8991⟩ },
                      affectedPlayer := opp, kind := .addNoncombatDamage none 1 } .untilEndOfTurn)
    let g := g.createEffect
      (.replacement { id := { kind := .equippedDealsDoubleDamage, grantor := some ⟨8992⟩ },
                      affectedPlayer := opp, kind := .multiplyDamage none 2 } .untilEndOfTurn)
    (g, bid)
  let depSrc? := gLkiChoiceBase.1.damageSourceById? gLkiChoiceBase.2
  let depSnap? := gLkiChoiceBase.1.lastKnownBefore? gLkiChoiceBase.2
  let wallChoiceObj := (gLkiChoiceBase.1.battlefield.filter (·.name == "Phase13 Wall"))[0]!
  -- (a) `dealDamageToPlayer` paused on `.chooseReplacement`: `(1 + 1) * 2 = 4` damage + 4 lifelink.
  let gChoicePlPaused :=
    gLkiChoiceBase.1.dealDamageToPlayer opp 1 (source := depSrc?) (cause := some testCause)
  let gChoicePlDone :=
    pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoicePlPaused
  -- (b) `dealDamageFrom` paused on `.chooseReplacement`: 4 damage (< 5 toughness) kills 0/5 wall via
  --     departed LKI deathtouch AND gains 4 life via departed LKI lifelink.
  let gChoiceFromPaused :=
    gLkiChoiceBase.1.dealDamageFrom bear.name wallChoiceObj 1 (source := depSrc?) (cause := some testCause)
  let gChoiceFromDone :=
    (pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceFromPaused).checkSBA
  -- (c) `markDamageOn` paused on `.chooseReplacement`: kills 0/5 wall via departed LKI deathtouch.
  let gChoiceMarkPaused :=
    gLkiChoiceBase.1.markDamageOn wallChoiceObj 1 "hit" (source := depSnap?) (cause := some testCause)
  let gChoiceMarkDone :=
    (pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceMarkPaused).checkSBA
  -- (d) `dealDamageToPlayers` across two opponents in `gThree0` with competing replacements:
  let gChoiceMulti0 :=
    let g := addPermanent gThree0 bear ⟨0⟩ ⟨0⟩
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.createEffect
      (.keywordsUntilEot bid #[Keyword.lifelink]) (cause := some testCause)
    let (g, _) := g.move bid (.graveyard ⟨0⟩) none (cause := some testCause)
    let g := g.createEffect
      (.replacement { id := { kind := .noncombatDamagePlusOne, grantor := some ⟨8993⟩ },
                      affectedPlayer := ⟨1⟩, kind := .addNoncombatDamage none 1 } .untilEndOfTurn)
    let g := g.createEffect
      (.replacement { id := { kind := .equippedDealsDoubleDamage, grantor := some ⟨8994⟩ },
                      affectedPlayer := ⟨1⟩, kind := .multiplyDamage none 2 } .untilEndOfTurn)
    (g, bid)
  let gChoiceMultiP1 :=
    gChoiceMulti0.1.dealDamageToPlayers #[⟨1⟩, ⟨2⟩] 1
      (source := gChoiceMulti0.1.damageSourceById? gChoiceMulti0.2) (cause := some testCause)
  let gChoiceMultiP2 :=
    pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceMultiP1
  let gChoiceMultiDone :=
    pickRepl (fun | .noncombatDamagePlusOne => true | _ => false) gChoiceMultiP2
  let lkiOk :=
    vampLki?.isSome &&
    (gLkiDmg.player me).life == 21 &&
    (gLkiDmg.findObject? wall.id).isNone &&
    Game.replayEvents gLkiDmg.events == gLkiDmg &&
    (match gChoicePlPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    (gChoicePlDone.player opp).life == 16 &&
    (gChoicePlDone.player me).life == 24 &&
    (match gChoiceFromPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    (gChoiceFromDone.findObject? wallChoiceObj.id).isNone &&
    (gChoiceFromDone.player me).life == 24 &&
    (match gChoiceMarkPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    (gChoiceMarkDone.findObject? wallChoiceObj.id).isNone &&
    (gChoiceMultiDone.player ⟨1⟩).life == 16 &&
    (gChoiceMultiDone.player ⟨2⟩).life == 16 &&
    (gChoiceMultiDone.player ⟨0⟩).life == 28 &&
    [gChoicePlDone, gChoiceFromDone, gChoiceMarkDone, gChoiceMultiDone].all
      (fun g => Game.replayEvents g.events == g)

  -- CR 613.7a `effectiveMaxHandSize` timestamp ordering:
  let noMaxDef : CardDef := {
    name := "Phase13 Reliquary"
    types := #[.artifact]
    staticAbilities := #[.noMaximumHandSize]
  }
  let capTwoDef : CardDef := {
    name := "Phase13 Cursed Rack"
    types := #[.artifact]
    staticAbilities := #[.maximumHandSize 2]
  }
  let gHsCapLast := addPermanent (addPermanent afterDraw noMaxDef me me) capTwoDef me me
  let gHsNoMaxLast := addPermanent (addPermanent afterDraw capTwoDef me me) noMaxDef me me
  let maxHandTsOk :=
    gHsCapLast.effectiveMaxHandSize me == some 2 &&
    gHsNoMaxLast.effectiveMaxHandSize me == none

  -- Filter-scoped Layer 2 control effect (`ObjectScope.creaturesControlledBy`) reverts control &
  -- clears stolen ring-bearer designation on EOT expiration:
  let gFiltCtrl0 :=
    let g := addPermanent afterDraw bear opp opp
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.createEffect
      (.layered (.creaturesControlledBy opp) (.control me) .untilEndOfTurn)
      (cause := some testCause)
    let g := g.setRingBearer me (some bid) (cause := some testCause)
    (g, bid)
  let preExpIdx := gFiltCtrl0.1.events.size
  let gFiltExpired := gFiltCtrl0.1.clearEOT
  let expSlice := gFiltExpired.events.extract preExpIdx gFiltExpired.events.size
  let filterCtrlExpOk :=
    gFiltCtrl0.1.controllerOf (gFiltCtrl0.1.object! gFiltCtrl0.2) == some me &&
    (gFiltCtrl0.1.player me).ringBearerId == some gFiltCtrl0.2 &&
    gFiltExpired.controllerOf (gFiltExpired.object! gFiltCtrl0.2) == some opp &&
    (gFiltExpired.player me).ringBearerId == none &&
    expSlice.any (fun e =>
      match e.change with
      | .rules (.permanent (.designation snap .ringBearer false)) =>
        snap.id == some gFiltCtrl0.2
      | _ => false) &&
    Game.replayEvents gFiltExpired.events == gFiltExpired

  -- Continuation resumption (`finishFraChoice`) across activation cost-pick reversal
  -- (`beginActivationPayment` / `afterTargetsChosen`) and `chooseCastFromLooked`
  -- (`beginResolutionCastTargets` illegal mode/target, synchronous cast, and decline):
  let mkSeqFrame (g : Game) (gain : Nat) : Game :=
    (g.change (.pushContinuationFrame {})).change (.triggerSequenceRest (some {
      controller := me
      ability := TriggeredAbility.ofPattern .youCastNoncreature "" (.draw 1)
      sourceId := none
      targets := #[]
      steps := [.gainLife (.fixed gain)]
    }))
  let sacArtEngineDef : CardDef := {
    name := "Phase13 Sac Artifact Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .hasType .artifact]))]
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let gActPayRev :=
    let g := (addPermanent afterDraw sacArtEngineDef me me).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Artifact Engine"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let gAct := mustApply g me (.activate engId 0)
    let gMana := mustApply gAct me (.tapForMana trId (.colored .red))
    (mustApply gMana me .pay, trId)
  let actPayRevOk :=
    gActPayRev.1.triggerSequenceRest.isNone &&
    gActPayRev.1.continuations.isEmpty &&
    (gActPayRev.1.player me).life == 24 &&
    (gActPayRev.1.findObject? gActPayRev.2).any (·.isOnBattlefield) &&
    gActPayRev.1.stack.isEmpty &&
    Game.replayEvents gActPayRev.1.events == gActPayRev.1
  let tapTwoTargetedDef : CardDef := {
    name := "Phase13 Tap Two Targeted Engine"
    types := #[.creature]
    subtypes := #["Artificer"]
    power := some 2
    toughness := some 2
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapObjects (.exact 2) (.all #[.hasType .artifact, .tapped false, .controlledBy .you])]
      effect := {
        targeting := .of .player
        resolution := .gainLife 1
        phrase := "Target player gains 1 life"
      }
    }]
  }
  let gActTargetRev :=
    let g := (addPermanent afterDraw tapTwoTargetedDef me me).createTreasureTokens me 2 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Tap Two Targeted Engine"))[0]!.id
    let tr0 := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let gAct := mustApply g me (.activate engId 0)
    let gTapOne := gAct.becomeTapped (gAct.object! tr0) (cause := some testCause)
    mustApply gTapOne me (.target (.player me))
  let actTargetRevOk :=
    gActTargetRev.triggerSequenceRest.isNone &&
    gActTargetRev.continuations.isEmpty &&
    (gActTargetRev.player me).life == 24 &&
    gActTargetRev.stack.isEmpty &&
    Game.replayEvents gActTargetRev.events == gActTargetRev
  let impossibleModalDef : CardDef := {
    name := "Phase13 Impossible Modal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellModes := #[
      { targeting := .of .creature, resolution := .destroyTarget, phrase := "Destroy target creature" },
      { targeting := .of .creature, resolution := .exileTarget, phrase := "Exile target creature" }
    ]
  }
  let mkTopLook1 (d : CardDef) : Game × ObjectId :=
    let g := insertObject afterDraw d me (.library me)
    let cid := (g.player me).library.back!
    let g := mkSeqFrame g 3
    (g.beginMayCastFromLooked me 1 5, cid)
  -- CR 601.2b–c / 733.1 (Phase 24 item 2): a looked-at card with no legal target or no
  -- choosable mode is rejected up front by `mayCastFromLookedError`; the choice stays open
  -- and declining it finishes the ability.
  let rejectsNoTarget (g : Game) (cid : ObjectId) : Bool :=
    match g.apply me (.cast cid) with
    | .error e => mentions e "has no legal target and can't be cast"
    | .ok _ => false
  let (gLookNoTgt0, lookNoTgtId) := mkTopLook1 impossibleRemDef
  let lookNoTgtRejected := rejectsNoTarget gLookNoTgt0 lookNoTgtId
  let gLookNoTgt := mustApply gLookNoTgt0 me .decline
  let (gLookNoMode0, lookNoModeId) := mkTopLook1 impossibleModalDef
  let lookNoModeRejected := rejectsNoTarget gLookNoMode0 lookNoModeId
  let gLookNoMode := mustApply gLookNoMode0 me .decline
  let (gLookSync0, lookSyncId) := mkTopLook1 freeDrawDef
  let gLookSync := mustApply gLookSync0 me (.cast lookSyncId)
  let gLookDec := mustApply gLookSync0 me .decline
  let lookedContAllOk :=
    lookNoTgtRejected && lookNoModeRejected &&
    gLookNoTgt.triggerSequenceRest.isNone && gLookNoTgt.continuations.isEmpty &&
    (gLookNoTgt.player me).life == 23 && gLookNoTgt.stack.isEmpty &&
    gLookNoMode.triggerSequenceRest.isNone && gLookNoMode.continuations.isEmpty &&
    (gLookNoMode.player me).life == 23 && gLookNoMode.stack.isEmpty &&
    gLookSync.triggerSequenceRest.isNone && gLookSync.continuations.isEmpty &&
    (gLookSync.player me).life == 23 && gLookSync.stack.size == 1 &&
    gLookDec.triggerSequenceRest.isNone && gLookDec.continuations.isEmpty &&
    (gLookDec.player me).life == 23 && gLookDec.stack.isEmpty &&
    [gLookNoTgt, gLookNoMode, gLookSync, gLookDec].all (fun g => Game.replayEvents g.events == g)
  let reviewRound2ContOk := actPayRevOk && actTargetRevOk && lookedContAllOk

  -- Successful ability activations (`becomeActivated`) preserve and resume open
  -- continuations across immediate, mana-paid, `.costPicks`, `.sacrificePermanent`,
  -- and `.crew` accept paths, while preserving CR 117.3c priority outside continuations:
  let freeActDef : CardDef := {
    name := "Phase13 Free Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.empty
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let manaActDef : CardDef := {
    name := "Phase13 Mana Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)]
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let sacOtherActDef : CardDef := {
    name := "Phase13 Sac Other Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))]
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let crewVehDef : CardDef := {
    name := "Phase13 Crew Skiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 3
    toughness := some 3
    keywords := #[.crew 2]
  }
  let gFreeActPaid :=
    let g := addPermanent afterDraw freeActDef me me
    let engId := (g.battlefield.filter (·.name == "Phase13 Free Engine"))[0]!.id
    mustApply (mkSeqFrame g 4) me (.activate engId 0)
  let gManaActPaid :=
    let g := (addPermanent afterDraw manaActDef me me).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Mana Engine"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me (.tapForMana trId (.colored .red))
    mustApply g me .pay
  let gCostPicksPaid :=
    let g := (addPermanent afterDraw sacArtEngineDef me me).createTreasureTokens me 2 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Artifact Engine"))[0]!.id
    let trs := (g.battlefield.filter (·.printed.isToken)).map (·.id)
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me (.tapForMana trs[0]! (.colored .red))
    let g := mustApply g me .pay
    mustApply g me (.choosePermanents #[trs[1]!])
  let gSacOtherPaid :=
    let g := (addPermanent afterDraw sacOtherActDef me me).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Other Engine"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me .pay
    mustApply g me (.sacrifice trId)
  let gCrewPaid :=
    let g := addPermanent (addPermanent afterDraw crewVehDef me me) tapTwoTargetedDef me me
    let vehId := (g.battlefield.filter (·.name == "Phase13 Crew Skiff"))[0]!.id
    let pilotId := (g.battlefield.filter (·.name == "Phase13 Tap Two Targeted Engine"))[0]!.id
    let g := mkSeqFrame g 4
    let g := mustApply g me (.activate vehId 0)
    mustApply g me (.choosePermanents #[pilotId])
  let gOppCrewPrio :=
    let g := addPermanent (addPermanent afterDraw crewVehDef opp opp) tapTwoTargetedDef opp opp
    let g := mustApply g me .pass
    let vehId := (g.battlefield.filter (·.name == "Phase13 Crew Skiff"))[0]!.id
    let pilotId := (g.battlefield.filter (·.name == "Phase13 Tap Two Targeted Engine"))[0]!.id
    let g := mustApply g opp (.activate vehId 0)
    mustApply g opp (.choosePermanents #[pilotId])
  let paidActStates := [gFreeActPaid, gManaActPaid, gCostPicksPaid, gSacOtherPaid, gCrewPaid]
  let reviewRound3ContOk :=
    paidActStates.all (fun g =>
      g.triggerSequenceRest.isNone &&
      g.continuations.isEmpty &&
      (g.player me).life == 24 &&
      g.stack.size == 1 &&
      Game.replayEvents g.events == g) &&
    gOppCrewPrio.priority == opp &&
    gOppCrewPrio.stack.size == 1 &&
    Game.replayEvents gOppCrewPrio.events == gOppCrewPrio

  -- Activation and spell costs that pause on `Pending.chooseReplacement` chain
  -- `.receivePriority caster` outside open continuations (checking SBAs, putting
  -- waiting triggers on the stack, and preserving non-active activator/caster
  -- priority per CR 117.3c) and chain `.finishFraChoice` when `triggerSequenceRest`,
  -- `pendingMayCastFromExile`, or an outer `pendingReplacement` is open:
  let headHuntDef : CardDef :=
    { bear with name := "Phase13 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
  let zeroToughDef : CardDef :=
    { bear with name := "Phase13 Zero Tough", power := some 0, toughness := some 0 }
  let sacSpellDef : CardDef := {
    name := "Phase13 Altar Bolt"
    manaCost := ManaCost.empty
    types := #[.instant]
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  -- (a) Non-active player `opp` activates `sacOtherActDef` sacrificing a creature
  -- with competing death replacements (finality counter vs `me`'s `headHuntDef`):
  let (gOppActRepPaused, gOppActRepDone, oppZeroId) :=
    let g := addPermanent (addPermanent (addPermanent afterDraw sacOtherActDef opp opp) bear opp opp) headHuntDef me me
    let g := mustApply g me .pass
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Other Engine"))[0]!.id
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some opp) (cause := some testCause)
    let g := addPermanent g zeroToughDef me me
    let zeroId := (g.battlefield.filter (·.name == "Phase13 Zero Tough"))[0]!.id
    let g := mustApply g opp (.activate engId 0)
    let g := mustApply g opp .pay
    let gPaused := mustApply g opp (.sacrifice sacBearId)
    let gDone := mustApply gPaused opp (.chooseReplacement idHead)
    (gPaused, gDone, zeroId)
  let oppActRepOk :=
    (match gOppActRepPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    gOppActRepDone.pending == .none &&
    gOppActRepDone.continuations.isEmpty &&
    gOppActRepDone.waitingTriggers.isEmpty &&
    gOppActRepDone.stack.size == 2 &&
    gOppActRepDone.priority == opp &&
    (gOppActRepDone.findObject? oppZeroId).all (!·.isOnBattlefield) &&
    Game.replayEvents gOppActRepPaused.events == gOppActRepPaused &&
    Game.replayEvents gOppActRepDone.events == gOppActRepDone
  -- (b) Non-active player `opp` casts an instant with `additionalCostSacrificeCreature`
  -- whose sacrifice pauses on `Pending.chooseReplacement`:
  let (gOppSpellRepPaused, gOppSpellRepDone, oppSpellZeroId) :=
    let g := insertObject (addPermanent (addPermanent afterDraw bear opp opp) headHuntDef me me) sacSpellDef opp (.hand opp)
    let spellCardId := (g.player opp).hand.back!
    let g := mustApply g me .pass
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some opp) (cause := some testCause)
    let g := addPermanent g zeroToughDef me me
    let zeroId := (g.battlefield.filter (·.name == "Phase13 Zero Tough"))[0]!.id
    let g := mustApply g opp (.cast spellCardId)
    let g := mustApply g opp .pay
    let gPaused := mustApply g opp (.sacrifice sacBearId)
    let gDone := mustApply gPaused opp (.chooseReplacement idHead)
    (gPaused, gDone, zeroId)
  let oppSpellRepOk :=
    (match gOppSpellRepPaused.pending with | .chooseReplacement p cs => p == opp && cs.size == 2 | _ => false) &&
    gOppSpellRepDone.pending == .none &&
    gOppSpellRepDone.continuations.isEmpty &&
    gOppSpellRepDone.waitingTriggers.isEmpty &&
    gOppSpellRepDone.stack.size == 2 &&
    gOppSpellRepDone.priority == opp &&
    (gOppSpellRepDone.findObject? oppSpellZeroId).all (!·.isOnBattlefield) &&
    Game.replayEvents gOppSpellRepPaused.events == gOppSpellRepPaused &&
    Game.replayEvents gOppSpellRepDone.events == gOppSpellRepDone
  -- (c) Doom Reigns `.mayCastUpToFromExile` + `triggerSequenceRest` across a spell
  -- sacrifice cost that pauses on `Pending.chooseReplacement`:
  let (gQueueSpellPaused, gQueueSpellDone) :=
    let g := addPermanent (addPermanent afterDraw bear me me) headHuntDef opp opp
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := insertObject (insertObject g sacSpellDef me .exile) freeDrawDef me .exile
    let exSac := (g.objects.filter (fun o => o.name == "Phase13 Altar Bolt" && o.zone == .exile))[0]!.id
    let exDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := (mkSeqFrame g 4).change (.pending (.fraChoice me (.mayCastUpToFromExile #[exSac, exDraw] 2)))
    let g := mustApply g me (.choosePermanents #[exSac])
    let g := mustApply g me .pay
    let gPaused := mustApply g me (.sacrifice sacBearId)
    let gAfterFirst := mustApply gPaused me (.chooseReplacement idHead)
    let gDone := mustApply gAfterFirst me (.choosePermanents #[exDraw])
    (gPaused, gDone)
  let queueSpellRepOk :=
    (match gQueueSpellPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gQueueSpellDone.pending == .none &&
    gQueueSpellDone.pendingMayCastFromExile.isNone &&
    gQueueSpellDone.triggerSequenceRest.isNone &&
    gQueueSpellDone.continuations.isEmpty &&
    gQueueSpellDone.waitingTriggers.isEmpty &&
    (gQueueSpellDone.player me).life == 24 &&
    gQueueSpellDone.stack.size == 3 &&
    Game.replayEvents gQueueSpellPaused.events == gQueueSpellPaused &&
    Game.replayEvents gQueueSpellDone.events == gQueueSpellDone
  -- (d) Activation with `.costPicks` (`sacArtEngineDef`) while both `triggerSequenceRest`
  -- and an outer `pendingReplacement` are open, and the sacrificed artifact creature
  -- pauses on `Pending.chooseReplacement`:
  let artBearDef : CardDef :=
    { bear with name := "Phase13 Clockwork Bear", types := #[.artifact, .creature] }
  let (gActOuterPaused, gActOuterDone) :=
    let g := (addPermanent (addPermanent (addPermanent afterDraw sacArtEngineDef me me) artBearDef me me) headHuntDef opp opp).createTreasureTokens me 1 (cause := some testCause)
    let engId := (g.battlefield.filter (·.name == "Phase13 Sac Artifact Engine"))[0]!.id
    let artBearId := (g.battlefield.filter (·.name == "Phase13 Clockwork Bear"))[0]!.id
    let trId := (g.battlefield.filter (·.printed.isToken))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters artBearId .finality 1 (some me) (cause := some testCause)
    let g := (mkSeqFrame g 4).change (.pendingReplacement (some .checkSBA))
    let g := mustApply g me (.activate engId 0)
    let g := mustApply g me (.tapForMana trId (.colored .red))
    let g := mustApply g me .pay
    let gPaused := mustApply g me (.choosePermanents #[artBearId])
    let gDone := mustApply gPaused me (.chooseReplacement idHead)
    (gPaused, gDone)
  let actOuterRepOk :=
    (match gActOuterPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gActOuterDone.pending == .none &&
    gActOuterDone.triggerSequenceRest.isNone &&
    gActOuterDone.continuations.isEmpty &&
    gActOuterDone.waitingTriggers.isEmpty &&
    (gActOuterDone.player me).life == 24 &&
    gActOuterDone.stack.size == 2 &&
    Game.replayEvents gActOuterPaused.events == gActOuterPaused &&
    Game.replayEvents gActOuterDone.events == gActOuterDone
  let reviewRound4ContOk := oppActRepOk && oppSpellRepOk && queueSpellRepOk && actOuterRepOk

  let mustHold (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 13 guard failed: {label}"
  mustHold "actionIrrevOk" actionIrrevOk &&
    mustHold "batchPauseReplayOk" batchPauseReplayOk &&
    mustHold "continuationsAllOk" continuationsAllOk &&
    mustHold "asEntersAllOk" asEntersAllOk &&
    mustHold "untapAndSagaOk" untapAndSagaOk &&
    mustHold "painAllOk" painAllOk &&
    mustHold "commanderAllOk" commanderAllOk &&
    mustHold "leftGameTriggersOk" leftGameTriggersOk &&
    mustHold "treasureRoutingOk" treasureRoutingOk &&
    mustHold "searchDeclineOk" searchDeclineOk &&
    mustHold "lkiOk" lkiOk &&
    mustHold "maxHandTsOk" maxHandTsOk &&
    mustHold "filterCtrlExpOk" filterCtrlExpOk &&
    mustHold "reviewRound2ContOk" reviewRound2ContOk &&
    mustHold "reviewRound3ContOk" reviewRound3ContOk &&
    mustHold "reviewRound4ContOk" reviewRound4ContOk

/- Phase 13 Review Round 5 regressions: dual replacement pauses across
`CostPick` + `payActivationExtraCosts`, multi-step non-active priority
preservation via `proposalCheckpoint` (CR 117.3c), and deferred `becomeCast`
follow-ups (Path of Ancestry scry, `pendingMayCastFromExile`, and
`pendingFreeCopies`) after a cost pauses on `Pending.chooseReplacement`. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let headHuntDef : CardDef :=
    { bear with name := "Phase13 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
  let sacSpellDef : CardDef := {
    name := "Phase13 Altar Bolt"
    manaCost := ManaCost.empty
    types := #[.instant]
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let freeDrawDef : CardDef := {
    name := "Phase13 Free Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  -- (a) `{T}, Sacrifice this, Sacrifice a legendary artifact` where BOTH the
  --     chosen legendary artifact AND the sacrificed source pause on
  --     `Pending.chooseReplacement` must defer `completeActivation` /
  --     `payActivationExtraCosts` until the first choice finishes instead of
  --     overwriting it:
  let mountDoomEngineDef : CardDef := {
    bear with
    name := "Phase13 Mount Doom Engine"
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self, .sacrifice (.exact 1) (.filter (.all #[.hasSupertype .legendary, .hasType .artifact]))]
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let legArtBearDef : CardDef := {
    bear with
    name := "Phase13 Legendary Relic Bear"
    supertypes := #[.legendary]
    types := #[.artifact, .creature]
  }
  let (gMdPause1, gMdPause2, gMdDone, mdEngId, mdArtId) :=
    let g := addPermanent (addPermanent (addPermanent afterDraw mountDoomEngineDef me me) legArtBearDef me me) headHuntDef opp opp
    let engId := (g.battlefield.filter (·.name == "Phase13 Mount Doom Engine"))[0]!.id
    let artId := (g.battlefield.filter (·.name == "Phase13 Legendary Relic Bear"))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters engId .finality 1 (some me) (cause := some testCause)
    let g := g.recordPutCounters artId .finality 1 (some me) (cause := some testCause)
    let g := mustApply g me (.activate engId 0)
    let gP1 := mustApply g me (.choosePermanents #[artId])
    let gP2 := mustApply gP1 me (.chooseReplacement idHead)
    let gD := mustApply gP2 me (.chooseReplacement idHead)
    (gP1, gP2, gD, engId, artId)
  let mountDoomDualPauseOk :=
    (match gMdPause1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gMdPause1.proposedSpell.isSome &&
    (gMdPause1.findObject? mdEngId).any (fun o => o.isOnBattlefield && !o.status.tapped) &&
    (gMdPause1.findObject? mdArtId).any (·.isOnBattlefield) &&
    (match gMdPause2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gMdPause2.findObject? mdArtId).all (!·.isOnBattlefield) &&
    (gMdPause2.findObject? mdEngId).any (fun o => o.isOnBattlefield && o.status.tapped) &&
    gMdDone.pending == .none &&
    gMdDone.continuations.isEmpty &&
    gMdDone.waitingTriggers.isEmpty &&
    (gMdDone.findObject? mdArtId).all (!·.isOnBattlefield) &&
    (gMdDone.findObject? mdEngId).all (!·.isOnBattlefield) &&
    gMdDone.stack.size == 3 &&
    gMdDone.priority == me &&
    Game.replayEvents gMdPause1.events == gMdPause1 &&
    Game.replayEvents gMdPause2.events == gMdPause2 &&
    Game.replayEvents gMdDone.events == gMdDone

  -- (b) Multi-step activation costs by non-active player `opp` where step 1 pauses
  --     on `Pending.chooseReplacement` (pushing a `ContinuationFrame`) and step 2
  --     does NOT pause must still return priority to `opp` (CR 117.3c) and drain
  --     `continuations`:
  let dualSacActDef : CardDef := {
    bear with
    name := "Phase13 Dual Sac Engine"
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.sacrifice (.exact 1) .self, .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))]
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let twoPickActDef : CardDef := {
    bear with
    name := "Phase13 Two Pick Engine"
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.all #[.hasSupertype .legendary, .hasType .artifact])), .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .hasType .creature]))]
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let gOppDualSacDone :=
    let g := addPermanent (addPermanent (addPermanent afterDraw dualSacActDef opp opp) bear opp opp) headHuntDef me me
    let g := mustApply g me .pass
    let engId := (g.battlefield.filter (·.name == "Phase13 Dual Sac Engine"))[0]!.id
    let plainBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters engId .finality 1 (some opp) (cause := some testCause)
    let g := mustApply g opp (.activate engId 0)
    let g := mustApply g opp .pay
    let g := mustApply g opp (.chooseReplacement idHead)
    mustApply g opp (.sacrifice plainBearId)
  let gOppTwoPickDone :=
    let g := addPermanent (addPermanent (addPermanent (addPermanent afterDraw twoPickActDef opp opp) legArtBearDef opp opp) bear opp opp) headHuntDef me me
    let g := mustApply g me .pass
    let engId := (g.battlefield.filter (·.name == "Phase13 Two Pick Engine"))[0]!.id
    let legArtId := (g.battlefield.filter (fun o => o.name == "Phase13 Legendary Relic Bear" && o.controller == some opp))[0]!.id
    let plainBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters legArtId .finality 1 (some opp) (cause := some testCause)
    let g := mustApply g opp (.activate engId 0)
    let g := mustApply g opp (.choosePermanents #[legArtId])
    let g := mustApply g opp (.chooseReplacement idHead)
    mustApply g opp (.choosePermanents #[plainBearId])
  let oppMultiStepPrioOk :=
    gOppDualSacDone.pending == .none &&
    gOppDualSacDone.continuations.isEmpty &&
    gOppDualSacDone.priority == opp &&
    gOppDualSacDone.stack.size == 3 &&
    Game.replayEvents gOppDualSacDone.events == gOppDualSacDone &&
    gOppTwoPickDone.pending == .none &&
    gOppTwoPickDone.continuations.isEmpty &&
    gOppTwoPickDone.priority == opp &&
    gOppTwoPickDone.stack.size == 3 &&
    Game.replayEvents gOppTwoPickDone.events == gOppTwoPickDone

  -- (c) Path of Ancestry scry after a creature spell's sacrifice cost pauses on
  --     `Pending.chooseReplacement` (for both active `me` and non-active `opp`):
  let poaDef5 : CardDef := {
    name := "Phase13 Path of Ancestry"
    types := #[.land]
    staticAbilities := #[.entersTapped]
    activatedAbilities := #[ActivatedAbility.manaAbility (.colorAmong (.commanderColorIdentity .you) false)]
    triggeredAbilities := #[TriggeredAbility.onManaSpentCastCommanderTypeScry]
  }
  let elfCmdrDef5 : CardDef := {
    name := "Phase13 Elf Commander"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    supertypes := #[.legendary]
    subtypes := #["Elf"]
    power := some 2
    toughness := some 2
  }
  let elfSacCreatureDef : CardDef := {
    name := "Phase13 Altar Elf"
    manaCost := ⟨#[.colored .green]⟩
    types := #[.creature]
    subtypes := #["Elf"]
    keywords := #[Keyword.flash]
    power := some 1
    toughness := some 1
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature]
  }
  let (gAncPaused, gAncScry, gAncDone) :=
    let g0 : Game :=
      match Start.start {
        seats := #[
          { name := "Chandra", deck := testRedDeck, commanders := #[elfCmdrDef5] },
          { name := "Nissa", deck := testGreenDeck }
        ]
        format := .constructed
        seed := 1
        startingPlayer := some 0
      } with
      | .ok g => passBoth (keepOpeningHands g 8)
      | .error e => panic! e
    let g := insertObject (addPermanent (addPermanent (addPermanent g0 poaDef5 me me) bear me me) headHuntDef opp opp) elfSacCreatureDef me (.hand me)
    let poaId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Path of Ancestry" && o.controller == some me))[0]!.id
    let sacBearId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let elfSpellId := (g.player me).hand.back!
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := mustApply g me (.cast elfSpellId)
    let g := mustApply g me (.tapForMana poaId (.colored .green))
    let g := mustApply g me .pay
    let gPaused := mustApply g me (.sacrifice sacBearId)
    let gScry := mustApply gPaused me (.chooseReplacement idHead)
    let topId := (gScry.player me).library.back!
    let gDone := mustApply gScry me (.scry #[topId] #[])
    (gPaused, gScry, gDone)
  let gOppAncDone :=
    let g0 : Game :=
      match Start.start {
        seats := #[
          { name := "Chandra", deck := testRedDeck },
          { name := "Nissa", deck := testGreenDeck, commanders := #[elfCmdrDef5] }
        ]
        format := .constructed
        seed := 1
        startingPlayer := some 0
      } with
      | .ok g => passBoth (keepOpeningHands g 8)
      | .error e => panic! e
    let g := insertObject (addPermanent (addPermanent (addPermanent g0 poaDef5 opp opp) bear opp opp) headHuntDef me me) elfSacCreatureDef opp (.hand opp)
    let poaId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Path of Ancestry" && o.controller == some opp))[0]!.id
    let sacBearId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let headId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let elfSpellId := (g.player opp).hand.back!
    let g := g.recordPutCounters sacBearId .finality 1 (some opp) (cause := some testCause)
    let g := mustApply g me .pass
    let g := mustApply g opp (.cast elfSpellId)
    let g := mustApply g opp (.tapForMana poaId (.colored .green))
    let g := mustApply g opp .pay
    let g := mustApply g opp (.sacrifice sacBearId)
    let gScry := mustApply g opp (.chooseReplacement idHead)
    let topId := (gScry.player opp).library.back!
    mustApply gScry opp (.scry #[topId] #[])
  let ancestryAfterCostRepOk :=
    (match gAncPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (match gAncScry.pending with | .scry p 1 1 => p == me | _ => false) &&
    gAncDone.pending == Pending.none &&
    gAncDone.continuations.isEmpty &&
    gAncDone.priority == me &&
    gAncDone.stack.size == 2 &&
    gOppAncDone.pending == Pending.none &&
    gOppAncDone.continuations.isEmpty &&
    gOppAncDone.priority == opp &&
    gOppAncDone.stack.size == 2 &&
    Game.replayEvents gAncPaused.events == gAncPaused &&
    Game.replayEvents gAncScry.events == gAncScry &&
    Game.replayEvents gAncDone.events == gAncDone &&
    Game.replayEvents gOppAncDone.events == gOppAncDone

  -- (d) `pendingMayCastFromExile` and `pendingFreeCopies` offers must still run
  --     after a cast spell's sacrifice cost pauses on `Pending.chooseReplacement`:
  let (gMayExNext, gMayExDone) :=
    let g := addPermanent (addPermanent afterDraw bear me me) headHuntDef opp opp
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := insertObject (insertObject g sacSpellDef me .exile) freeDrawDef me .exile
    let exSac := (g.objects.filter (fun o => o.name == "Phase13 Altar Bolt" && o.zone == .exile))[0]!.id
    let exDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := (g.change (.pushContinuationFrame {})).change (.pending (.fraChoice me (.mayCastUpToFromExile #[exSac, exDraw] 2)))
    let g := mustApply g me (.choosePermanents #[exSac])
    let g := mustApply g me .pay
    let g := mustApply g me (.sacrifice sacBearId)
    let gNext := mustApply g me (.chooseReplacement idHead)
    let gDone := mustApply gNext me (.choosePermanents #[exDraw])
    (gNext, gDone)
  let (gCopyNext, gCopyDone) :=
    let g := addPermanent (addPermanent afterDraw bear me me) headHuntDef opp opp
    let sacBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase13 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters sacBearId .finality 1 (some me) (cause := some testCause)
    let g := insertObject (insertObject g sacSpellDef me .exile) freeDrawDef me .exile
    let cpSac := (g.objects.filter (fun o => o.name == "Phase13 Altar Bolt" && o.zone == .exile))[0]!.id
    let cpDraw := (g.objects.filter (fun o => o.name == "Phase13 Free Draw" && o.zone == .exile))[0]!.id
    let g := (g.change (.pushContinuationFrame {})).change (.pending (.fraChoice me (.castCopiesFree #[cpSac, cpDraw] 4 2)))
    let g := mustApply g me (.cast cpSac)
    let g := mustApply g me .pay
    let g := mustApply g me (.sacrifice sacBearId)
    let gNext := mustApply g me (.chooseReplacement idHead)
    let gDone := mustApply gNext me (.cast cpDraw)
    (gNext, gDone)
  let exileAndCopyOffersAfterCostRepOk :=
    (match gMayExNext.pending with | .fraChoice p (.mayCastUpToFromExile ids left) => p == me && ids.size == 1 && left == 1 | _ => false) &&
    gMayExDone.pending == Pending.none &&
    gMayExDone.pendingMayCastFromExile.isNone &&
    gMayExDone.continuations.isEmpty &&
    gMayExDone.stack.size == 3 &&
    Game.replayEvents gMayExNext.events == gMayExNext &&
    Game.replayEvents gMayExDone.events == gMayExDone &&
    (match gCopyNext.pending with | .fraChoice p (.castCopiesFree ids _ left) => p == me && ids.size == 1 && left == 1 | _ => false) &&
    gCopyDone.pending == Pending.none &&
    gCopyDone.pendingFreeCopies.isNone &&
    gCopyDone.continuations.isEmpty &&
    gCopyDone.stack.size == 3 &&
    Game.replayEvents gCopyNext.events == gCopyNext &&
    Game.replayEvents gCopyDone.events == gCopyDone
  let reviewRound5ContOk :=
    mountDoomDualPauseOk && oppMultiStepPrioOk && ancestryAfterCostRepOk && exileAndCopyOffersAfterCostRepOk

  let mustHold (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 13 Round 5 guard failed: {label}"
  mustHold "mountDoomDualPauseOk" mountDoomDualPauseOk &&
    mustHold "oppMultiStepPrioOk" oppMultiStepPrioOk &&
    mustHold "ancestryAfterCostRepOk" ancestryAfterCostRepOk &&
    mustHold "exileAndCopyOffersAfterCostRepOk" exileAndCopyOffersAfterCostRepOk &&
    mustHold "reviewRound5ContOk" reviewRound5ContOk

/- Phase 14 isolation & replay tests:
   1. Paused `withProposalAction` / `activateManaAbility` CR 733.1 bracketing.
   2. Multi-step `payCostPickItems` `chooseReplacement` chaining & loyalty `+N`
      activation cost replacement (CR 118.11).
   3. Irreversible `lookedAt`, `searched`, and `drawFromEmptyAttempted` during
      CR 733.1 proposal reversal (plus SBA empty-library loss).
   4. Face-down morph `turnFaceUp` (`ProposalKind.turnFaceUp`, priority/control
      gates, CR 733.1 reversal, post-turn-face-up SBA) & mid-resolution `{X}`
      `castExiledAsAbilityResolves` (`resolutionCast := true`).
   5. Single-writer `entersWith` without duplicate post-entry counter events,
      Cursed Mirror EOT `isCopy == false`, `PendingReplacement.move` `attachedTo`
      preservation, replaced `ZoneVerb.discard` / `.sacrifice`,
      `recordPutCounters` replaced count `n'` (no double-multiply on
      `.tapAndStun` / `empowerJace`), and CR 119.5 `setLife` life gain.
   6. Combat `replaceDamage` CR 616.1 chooser, `DamageEvent.prevented`, and
      unpreventable shield + loyalty removal on planeswalkers (CR 120.3c / 122.1c).
   7. Simultaneous batch `preBattlefield` look-back, `.attackPumpPerPlains`
      `DelayedTrigger` routing & CR 608.2b fizzle, reflexive trigger CR 608.2b
      fizzle, and flicker `followMovedToZone?` isolation across a 2nd move.
   8. CR 800.4a/c/d/i/j multiplayer `concede` cleanup & replay determinism. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let headHuntDef : CardDef :=
    { bear with name := "Phase14 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
  let samsonDef14 : CardDef :=
    { bear with name := "Phase14 Doc Samson", staticAbilities := #[.extraCounterOnPermanents] }
  let pwPlusDef14 : CardDef := {
    name := "Phase14 Plus PW"
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Chandra"]
    loyalty := some 4
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.loyalty (.plus 1)]
      effect := { resolution := .draw 1, phrase := "Draw a card" }
    }]
  }
  let planDef14 : CardDef := {
    name := "Phase14 Plan"
    types := #[.enchantment]
  }
  let openProposalActionDepth (g : Game) : Nat :=
    g.events.foldl (fun d e =>
      match e.change with
      | .engine (.beginProposalAction _) => d + 1
      | .engine .endProposalAction => d - 1
      | _ => d) 0

  -- 1. Paused `activateManaAbility` CR 733.1 bracketing (pain land + damage choice + reversal).
  let rgSpellDef : CardDef := {
    name := "Phase14 RG Spell"
    manaCost := ⟨#[.colored .red, .colored .green]⟩
    types := #[.instant]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let painLandDef : CardDef := {
    name := "Phase14 Pain Land"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .red, .const 1)]) (damageYou := 1)]
  }
  let (gPainPaused, gPainResumed, gPainRev, painSpellId, painLandId) :=
    let g := addPermanent (addPermanent afterDraw bear opp opp) painLandDef me me
    let g := insertObject g rgSpellDef me (.hand me)
    let oppBearId := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let landId := (g.battlefield.filter (·.name == "Phase14 Pain Land"))[0]!.id
    let spellId := (g.player me).hand.back!
    let idAddMe : ReplacementId := { kind := .addNoncombatDamage, object := some oppBearId }
    let idMulMe : ReplacementId := { kind := .multiplyDamage, object := some oppBearId }
    let g := (g.createEffect (.replacement {
      id := idAddMe, source := some oppBearId, controller := some opp,
      affectedPlayer := me, kind := .addNoncombatDamage (some landId) 2
    }) (cause := some testCause)).createEffect (.replacement {
      id := idMulMe, source := some oppBearId, controller := some opp,
      affectedPlayer := me, kind := .multiplyDamage (some landId) 2
    }) (cause := some testCause)
    let g := mustApply g me (.cast spellId)
    let gPaused := mustApply g me (.tapForMana landId (.colored .red))
    let gResumed := mustApply gPaused me (.chooseReplacement idAddMe)
    let gRev := mustApply gResumed me .pay
    (gPaused, gResumed, gRev, spellId, landId)
  let painLandBracketOk :=
    (match gPainPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    openProposalActionDepth gPainPaused == 1 &&
    openProposalActionDepth gPainResumed == 0 &&
    gPainResumed.pending == .activateManaAbilities me &&
    (gPainResumed.player me).manaPool.red == 1 &&
    (gPainResumed.player me).life == 14 &&
    gPainRev.pending == .none &&
    gPainRev.proposedSpell.isNone &&
    gPainRev.proposalCheckpoint.isNone &&
    gPainRev.stack.isEmpty &&
    (gPainRev.player me).hand.contains painSpellId &&
    !(gPainRev.object! painLandId).status.tapped &&
    (gPainRev.player me).manaPool.total == 0 &&
    (gPainRev.player me).life == 20 &&
    [gPainPaused, gPainResumed, gPainRev].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 2. Multi-item `payCostPickItems` `chooseReplacement` chaining & loyalty `+N` replacement.
  let (gPickP1, gPickP2, gPickDone, pickB1, pickB2) :=
    let g := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) headHuntDef opp opp
    let b1 := (g.battlefield.filter (fun o => o.name == "Event Bear" && o.controller == some me))[0]!.id
    let b2 := (g.battlefield.filter (fun o => o.name == "Event Hero" && o.controller == some me))[0]!.id
    let headId := (g.battlefield.filter (·.name == "Phase14 Head Hunt"))[0]!.id
    let idHead : ReplacementId := { kind := .exileOppDeath, object := some headId }
    let g := g.recordPutCounters b1 .finality 1 (some me) (cause := some testCause)
    let g := g.recordPutCounters b2 .finality 1 (some me) (cause := some testCause)
    let gP1 := g.payCostPickItems me (some b1) (some b1) .sacrificeArtifactOrCreature #[b1, b2]
    let gP2 := mustApply gP1 me (.chooseReplacement idHead)
    let gD := mustApply gP2 me (.chooseReplacement idHead)
    (gP1, gP2, gD, b1, b2)
  let gLoyaltyPlus :=
    let g := addPermanent (addPermanent afterDraw samsonDef14 me me) pwPlusDef14 me me
    let pwId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plus PW"))[0]!.id
    let g := g.recordPutCounters pwId .loyalty 2 (some me) (cause := some testCause)
    mustApply g me (.activate pwId 0)
  let chandraLoyaltyAfter :=
    (gLoyaltyPlus.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plus PW"))[0]!.status.loyaltyCounters
  let costPickAndLoyaltyOk :=
    (match gPickP1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gPickP1.findObject? pickB1).any (·.isOnBattlefield) &&
    (gPickP1.findObject? pickB2).any (·.isOnBattlefield) &&
    (match gPickP2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gPickP2.findObject? pickB1).all (!·.isOnBattlefield) &&
    (gPickP2.findObject? pickB2).any (·.isOnBattlefield) &&
    (gPickDone.findObject? pickB2).all (!·.isOnBattlefield) &&
    gPickDone.pending == .none &&
    chandraLoyaltyAfter == 5 &&
    [gPickP1, gPickP2, gPickDone, gLoyaltyPlus].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 3. Irreversible `lookedAt`, `searched`, and `drawFromEmptyAttempted` across CR 733.1 reversal.
  let (gIrrevKeep, gEmptyDrawSba, libPeekId) :=
    let g0 := insertObject afterDraw rgSpellDef me (.hand me)
    let spId := (g0.player me).hand.back!
    let peekId := (g0.player me).library.back!
    let gProp := mustApply g0 me (.cast spId)
    let g1 := ((gProp.change (.beginProposalAction (.manaAbility none))).record
      (GameEvent.lookedAt gProp.turnNumber me #[peekId] (cause := some testCause))).record
      (GameEvent.searched gProp.turnNumber me me #[peekId] (cause := some testCause))
      |>.change .endProposalAction
    let gRev1 := mustApply g1 me .pay
    let g2 := ((gProp.change (.beginProposalAction (.manaAbility none))).record
      (GameEvent.drawFromEmptyAttempted gProp.turnNumber me (cause := some (.gameRule .abilityActivated))))
      |>.change .endProposalAction
    let gRev2 := (mustApply g2 me .pay).checkSBA
    (gRev1, gRev2, peekId)
  let irrevProposalEventsOk :=
    gIrrevKeep.stack.isEmpty &&
    gIrrevKeep.events.any (fun e =>
      match e.change with
      | .rules (.player (.lookedAt p ids)) => p == me && ids == #[libPeekId]
      | _ => false) &&
    gIrrevKeep.events.any (fun e =>
      match e.change with
      | .rules (.player (.searched p owner found)) => p == me && owner == me && found == #[libPeekId]
      | _ => false) &&
    gEmptyDrawSba.events.any (fun e =>
      match e.change with
      | .rules (.player (.drawFromEmptyAttempted p)) => p == me
      | _ => false) &&
    (gEmptyDrawSba.player me).lost &&
    [gIrrevKeep, gEmptyDrawSba].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 4. Face-down morph `turnFaceUp` & mid-resolution `{X}` `castExiledAsAbilityResolves`.
  let morphZeroDef : CardDef := {
    creature "Phase14 Fragile Morph" { symbols := #[.colored .blue] } #["Illusion"] 0 0 with
    keywords := #[.morph (CostSpec.ofMana ⟨#[.colored .blue]⟩)]
  }
  let islandDef : CardDef := {
    name := "Phase14 Island"
    types := #[.land]
    subtypes := #["Island"]
  }
  let redLandDef : CardDef := {
    name := "Phase14 Mountain"
    types := #[.land]
    subtypes := #["Mountain"]
  }
  let (morphGatesOk, gMorphRev, gMorphTurned, morphId0, morphLandId) :=
    let g := addPermanent (addPermanent afterDraw morphZeroDef me me) redLandDef me me
    let g := addPermanent g islandDef me me
    let mId := (g.battlefield.filter (·.name == "Phase14 Fragile Morph"))[0]!.id
    let rLand := (g.battlefield.filter (·.name == "Phase14 Mountain"))[0]!.id
    let uLand := (g.battlefield.filter (·.name == "Phase14 Island"))[0]!.id
    let g := setFaceDown g mId true
    let oppCtrlRej := (g.apply opp (.activate mId 0)).isOk == false
    let gOppPrio := mustApply g me .pass
    let noPrioRej := (gOppPrio.apply me (.activate mId 0)).isOk == false
    let gProp := mustApply g me (.activate mId 0)
    let propKindOk := gProp.proposedSpell.any (·.kind == .turnFaceUp) && gProp.pending == .activateManaAbilities me
    let gTappedWrong := mustApply gProp me (.tapForMana rLand (.colored .red))
    let gRev := mustApply gTappedWrong me .pay
    let gProp2 := mustApply gRev me (.activate mId 0)
    let gPaid := mustApply (mustApply gProp2 me (.tapForMana uLand (.colored .blue))) me .pay
    (oppCtrlRej && noPrioRej && propKindOk, gRev, gPaid, mId, rLand)
  let xBurnDef : CardDef := {
    name := "Phase14 X Burn"
    manaCost := ⟨#[.x, .colored .red]⟩
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let gResXDone :=
    let g := insertObject afterDraw xBurnDef opp .exile
    let exId := (g.objects.filter (fun o => o.name == "Phase14 X Burn" && o.zone == .exile))[0]!.id
    let g := g.addMana opp (.colored .red) 3
    let g := ((g.change (.priority opp)).change (.pushContinuationFrame {})).change
      (.pending (.mayCastExiledElseDamage opp exId 2 none))
    let g := mustApply g opp (.cast exId)
    let g := mustApply g opp (.chooseX 2)
    mustApply g opp .pay
  let morphAndResCastOk :=
    morphGatesOk &&
    (gMorphRev.object! morphId0).status.faceDown &&
    !(gMorphRev.object! morphLandId).status.tapped &&
    gMorphRev.priority == me &&
    (gMorphTurned.findObject? morphId0).all (!·.isOnBattlefield) &&
    gMorphTurned.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.turnedFaceUp snap)) => snap.id == some morphId0
      | _ => false) &&
    gResXDone.pending == .none &&
    gResXDone.continuations.isEmpty &&
    gResXDone.stack.size == 1 &&
    gResXDone.priority == me &&
    (gResXDone.player opp).manaPool.total == 0 &&
    [gMorphRev, gMorphTurned, gResXDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 5. Single-writer `entersWith`, Cursed Mirror EOT `isCopy == false`, `PendingReplacement.move`
  --    `attachedTo` preservation, replaced `ZoneVerb.discard` / `.sacrifice`,
  --    `recordPutCounters` replaced count `n'`, and CR 119.5 `setLife` life gain.
  let (gSingleWriter, swStartIdx, swNewId) :=
    let g := addPermanent afterDraw samsonDef14 me me
    let g := insertObject g pwPlusDef14 me (.hand me)
    let cid := (g.player me).hand.back!
    let preIdx := g.events.size
    let (g1, nid) := g.putOntoBattlefield cid me (cause := some testCause)
    let g1 := g1.afterPermanentEnters (g1.object! nid)
    (g1, preIdx, nid)
  let swSlice := gSingleWriter.events.extract swStartIdx gSingleWriter.events.size
  let swHasLoyalty5 :=
    swSlice.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ _ .battlefield _ _ ew _)) => ew.contains (.loyalty, 5)
      | _ => false)
  let swZeroCounterEvents :=
    !swSlice.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters ..)) => true
      | _ => false)
  let mirrorDef14 : CardDef := {
    name := "Phase14 Cursed Mirror"
    types := #[.artifact]
    staticAbilities := #[.asEntersMayCopyCreatureHasteUntilEot]
  }
  let (gMirrorCopy14, gMirrorClean14, mirrorPermId) :=
    let g0 := addPermanent afterDraw hero opp opp
    let hId := (g0.battlefield.filter (fun (o : GameObject) => o.name == hero.name))[0]!.id
    let g0 := insertObject g0 mirrorDef14 me (.hand me)
    let mHand := (g0.player me).hand.back!
    let (g1, _) := g0.putOntoBattlefield mHand me (cause := some testCause)
    let rid :=
      match g1.pending with
      | .chooseReplacement _ cs =>
        (cs.find? (fun (c : ReplacementId) => c.kind == ReplacementEffectKind.entersAsCopyCreatureUntilEot hId)).get!
      | _ => panic! "expected mirror replacement choice"
    let gCopy := mustApply g1 me (.chooseReplacement rid)
    let mPerm := (gCopy.battlefield.filter (fun (o : GameObject) => o.printed.name == "Phase14 Cursed Mirror"))[0]!.id
    let gClean := gCopy.clearEOT
    (gCopy, gClean, mPerm)
  let auraOddEvenDef : CardDef := {
    name := "Phase14 Parity Aura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.asEntersChooseOddEven]
  }
  let (gAuraPaused, gAuraAttached, auraHostId, auraPermId) :=
    let g0 := addPermanent afterDraw bear me me
    let hostId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g0 := insertObject g0 auraOddEvenDef me (.hand me)
    let aHand := (g0.player me).hand.back!
    let (gP, _) := g0.move aHand .battlefield (some me) (attachedTo := some hostId) (cause := some testCause)
    let gA := mustApply gP me (.chooseMode 1)
    let aPerm := (gA.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Parity Aura"))[0]!.id
    (gP, gA, hostId, aPerm)
  let discardVerbPreserved :=
    let gD0 := insertObject afterDraw bear me (.hand me)
    let hid := ((gD0.player me).hand.filter (fun id => (gD0.object! id).name == bear.name))[0]!
    let gD0 := gD0.createEffect
      (.replacement { id := { kind := .finalityCounterExile, object := some hid },
                      affectedPlayer := me, kind := .exileInsteadOfGraveyard (some hid) false } .untilEndOfTurn)
    let (gD1, _) := gD0.move hid (.graveyard me) none (verb := some .discard) (cause := some testCause)
    gD1.events.any (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ (.hand _) .exile ZoneVerb.discard _ _ _)) => true
      | _ => false)
  let (gSacExile, sacExileVerbOk) :=
    let g0 := addPermanent afterDraw bear me me
    let bid := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g0 := g0.recordPutCounters bid .finality 1 (some me) (cause := some testCause)
    let preIdx := g0.events.size
    let g1 := g0.sacrificeToGraveyard (g0.object! bid) "sacrifice bear" (cause := some testCause)
    let ok :=
      (g1.events.extract preIdx g1.events.size).any (fun e =>
        match e.change with
        | .rules (.zone (.moved _ _ .battlefield .exile ZoneVerb.sacrifice _ _ _)) => true
        | _ => false)
    (g1, ok)
  let (gCountersAndLife, countersAndLifeSubOk) :=
    let g0 := addPermanent (addPermanent afterDraw samsonDef14 me me) bear me me
    let bid := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g1 := g0.applyPermanentAction (g0.object! bid) .tapAndStun
    let g2 := (g1.empowerJace me 2).empowerJace me 2
    let jaceLoyalty :=
      ((g2.battlefield.filter (fun (o : GameObject) => g2.hasSubtype o .jace))[0]!).status.loyaltyCounters
    let g3 := g2.setLife me 25 "set life to 25" (cause := some testCause)
    let ok :=
      (g3.object! bid).status.stun == 2 &&
      jaceLoyalty == 6 &&
      (g3.player me).life == 25 &&
      g3.loggedLifeGained me == 5
    (g3, ok)
  let singleWriterAndMirrorOk :=
    (gSingleWriter.object! swNewId).status.loyaltyCounters == 5 &&
    swHasLoyalty5 && swZeroCounterEvents &&
    (gMirrorCopy14.snapshot (gMirrorCopy14.object! mirrorPermId)).isCopy &&
    gMirrorCopy14.name (gMirrorCopy14.object! mirrorPermId) == hero.name &&
    !(gMirrorClean14.snapshot (gMirrorClean14.object! mirrorPermId)).isCopy &&
    gMirrorClean14.name (gMirrorClean14.object! mirrorPermId) == "Phase14 Cursed Mirror" &&
    (match gAuraPaused.pending with | Pending.chooseReplacement p _ => p == me | _ => false) &&
    (gAuraAttached.object! auraPermId).attachedTo == some auraHostId &&
    (gAuraAttached.object! auraPermId).status.chosenOdd == some true &&
    discardVerbPreserved && sacExileVerbOk && countersAndLifeSubOk &&
    [gSingleWriter, gMirrorCopy14, gMirrorClean14, gAuraPaused, gAuraAttached, gSacExile, gCountersAndLife].all
      (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 6. Combat `replaceDamage` CR 616.1 chooser, `DamageEvent.prevented`, and planeswalker shield + loyalty.
  let (gCbtPrompt, gCbtResolved, cbtBlkId, idShieldCbt, cbtPrev6Ok) :=
    let g0 := addPermanent (addPermanent afterDraw { bear with power := some 3 } me me) { hero with toughness := some 4 } opp opp
    let atkId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let blkId := (g0.battlefield.filter (fun (o : GameObject) => o.name == hero.name))[0]!.id
    let g0 := g0.recordPutCounters blkId .shield 1 (some opp) (cause := some testCause)
    let idShield : ReplacementId := { kind := .shieldCounterPreventDamage, object := some blkId }
    let idMul : ReplacementId := { kind := .multiplyDamage, object := some atkId }
    let g1 := ((g0.createEffect
      (.replacement {
        id := idMul, source := some atkId, controller := some me,
        affectedPlayer := me, kind := .multiplyDamage (some atkId) 2
      }) (cause := some testCause)).record
      (GameEvent.attackersDeclared g0.turnNumber me #[(g0.snapshot (g0.object! atkId), .player opp)])).record
      (GameEvent.combatDamageAssigned g0.turnNumber true #[{ source := atkId, toCreatures := #[(blkId, 3)], toPlayer := 0 }])
    let preIdx := g1.events.size
    let gP := g1.dealAssignedCombatDamage
    let gR := mustApply gP opp (.chooseReplacement idMul)
    let prev6 :=
      (gR.events.extract preIdx gR.events.size).any (fun e =>
        match e.change with
        | .rules (.damage (.prevented _ (.permanent snap) 6)) => snap.id == some blkId
        | _ => false)
    (gP, gR, blkId, idShield, prev6)
  let (gPrevEv, prevEvOk) :=
    let protDef : CardDef := { bear with name := "Phase14 Protected Bear", staticAbilities := #[.preventAllDamageToThis] }
    let g0 := addPermanent (addPermanent afterDraw bear me me) protDef opp opp
    let src := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some me))[0]!
    let tgt := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Protected Bear"))[0]!
    let preIdx := g0.events.size
    let g1 := g0.dealDamageFrom "Event Bear" tgt 3 (source := some src) (cause := some testCause)
    let ok :=
      (g1.object! tgt.id).status.damage == 0 &&
      (g1.events.extract preIdx g1.events.size).any (fun e =>
        match e.change with
        | .rules (.damage (.prevented _ _ 3)) => true
        | _ => false)
    (g1, ok)
  let (gPwShield, pwShieldOk) :=
    let g0 := addPermanent (addPermanent afterDraw bear me me) pwPlusDef14 opp opp
    let src := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some me))[0]!
    let pwId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plus PW"))[0]!.id
    let g0 := g0.recordPutCounters pwId .loyalty 4 (some opp) (cause := some testCause)
    let g0 := g0.recordPutCounters pwId .shield 1 (some opp) (cause := some testCause)
    let g1 := g0.markDamageOn (g0.object! pwId) 2 "Event Bear deals 2 damage"
      (source := some (g0.snapshot src)) (sourceObj := some src)
      (unpreventable := true) (cause := some testCause)
    let pwAfter := g1.object! pwId
    (g1, pwAfter.status.shield == 0 && pwAfter.status.loyaltyCounters == 2)
  let combatDmgAndShieldPwOk :=
    (match gCbtPrompt.pending with | Pending.chooseReplacement p cs => p == opp && cs.contains idShieldCbt | _ => false) &&
    (gCbtResolved.object! cbtBlkId).status.shield == 0 &&
    (gCbtResolved.object! cbtBlkId).status.damage == 0 &&
    cbtPrev6Ok && prevEvOk && pwShieldOk &&
    [gCbtPrompt, gCbtResolved, gPrevEv, gPwShield].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 7. Simultaneous batch `preBattlefield` look-back, `.attackPumpPerPlains` `DelayedTrigger`
  --    & CR 608.2b fizzle, reflexive trigger CR 608.2b fizzle, and flicker `followMovedToZone?`.
  let diesWatcherDef : CardDef := {
    bear with
    name := "Phase14 Dies Watcher"
    triggeredAbilities := #[
      TriggeredAbility.ofPattern .anotherCreatureOrPlaneswalkerYouControlDies
        "Whenever another creature or planeswalker you control dies, you gain 1 life."
        (.gainLife 1)
    ]
  }
  let (gSimDies, simDiesOk) :=
    let g0 := addPermanent (addPermanent afterDraw diesWatcherDef me me) diesWatcherDef me me
    let w1 := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Dies Watcher"))[0]!.id
    let w2 := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Dies Watcher"))[1]!.id
    let preBf := g0.battlefield
    let g1 := g0.withBatch (some testCause) fun g =>
      let g := g.destroyPermanent (g.object! w1) (cause := some testCause) (preBattlefield := some preBf)
      g.destroyPermanent (g.object! w2) (cause := some testCause) (preBattlefield := some preBf)
    (g1, g1.waitingTriggers.size == 2)
  let (gDtFizzle, gDtLki, dtFizzleOk) :=
    let g0 := addPermanent afterDraw bear me me
    let card0Present := (g0.findObject? ⟨0⟩).isSome
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let g1 := g0.attackPumpPerPlains me
    let regOk := g1.delayedTriggers.any (fun (dt : DelayedTrigger) =>
      dt.kind == DelayedTriggerKind.attackPumpPerPlains && dt.source.isNone)
    let g2 := g1.record (GameEvent.attackersDeclared g1.turnNumber me #[(g1.snapshot (g1.object! bId), .player opp)])
    let g2 := g2.receivePriority me
    let sourcelessOk :=
      card0Present &&
      (match g2.stack.back?.bind (fun se => g2.findObject? se.objectId) with
       | some stObj => stObj.sourceId.isNone && stObj.name == "Roads Go Ever, Ever On's ability"
       | none => false) &&
      g2.events.any (fun e =>
        match e.change with
        | .rules (.triggerQueue (.triggered src _ ab _)) =>
          ab == TriggeredAbility.onYouAttackPumpTargetPerPlains &&
          src.id.isNone && src.name == "Roads Go Ever, Ever On"
        | _ => false)
    let g3 := mustApply g2 me (.target (Target.permanent bId))
    let (g4, _) := g3.move bId (.graveyard me) none (cause := some testCause)
    let preRes := g4.events.size
    let g5 := g4.resolveTop
    let fizzled :=
      g5.stack.isEmpty &&
      (g5.events.extract preRes g5.events.size).any (fun e =>
        match e.change with
        | .rules (.stackObject (.removedOnResolution _)) => true
        | _ => false)
    -- Also verify stored Saga LKI (`dt.source == some sagaLki`) preserves `sourceId == some sagaId`.
    let sagaPlaceholderDef : CardDef := {
      name := "Roads Go Ever, Ever On"
      types := #[.enchantment]
      subtypes := #["Saga"]
    }
    let gS0 := addPermanent (addPermanent afterDraw bear me me) sagaPlaceholderDef me me
    let sbId := (gS0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let sagaId := (gS0.battlefield.filter (fun (o : GameObject) => o.name == "Roads Go Ever, Ever On"))[0]!.id
    let (gS1, _) := gS0.move sagaId (.graveyard me) none (cause := some testCause)
    let (gS1, dtCauseS) := gS1.allocDelayedCause (some me) (some sagaId)
    let gS1 := gS1.registerDelayedTrigger {
      controller := me
      source := gS1.damageSourceById? sagaId
      kind := .attackPumpPerPlains
      cause := dtCauseS
    }
    let gS2 := (gS1.record (GameEvent.attackersDeclared gS1.turnNumber me
      #[(gS1.snapshot (gS1.object! sbId), .player opp)])).receivePriority me
    let lkiSourceOk :=
      match gS2.stack.back?.bind (fun se => gS2.findObject? se.objectId) with
      | some stObj => stObj.sourceId == some sagaId && stObj.name == "Roads Go Ever, Ever On's ability"
      | none => false
    (g5, gS2, regOk && sourcelessOk && fizzled && lkiSourceOk)
  let (gReflFizzle, reflFizzleOk) :=
    let g0 := addPermanent (addPermanent afterDraw planDef14 me me) bear opp opp
    let planId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Plan"))[0]!.id
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.controller == some opp))[0]!.id
    let g1 := mustApply (g0.queueModeledReflexive me (some planId) .divideSevenDamage) me
      (.divideDamage #[(Target.permanent bId, 7)])
    let (g2, _) := g1.move bId .exile none (cause := some testCause)
    let preRes := g2.events.size
    let g3 := g2.resolveTop
    let fizzled :=
      g3.stack.isEmpty &&
      (g3.events.extract preRes g3.events.size).any (fun e =>
        match e.change with
        | .rules (.stackObject (.removedOnResolution _)) => true
        | _ => false)
    (g3, fizzled)
  let (gFlickerIso, flickerIsoOk) :=
    let g0 := addPermanent afterDraw bear me me
    let origId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let (g1, exId) := g0.move origId .exile none (cause := some testCause)
    let (g2, handId) := g1.move exId (.hand me) none (cause := some testCause)
    let ok :=
      (g1.followMovedToZone? origId (fun (z : Zone) => z == Zone.exile)).map (fun (o : GameObject) => o.id) == some exId &&
      (g2.followMovedToZone? origId (fun (z : Zone) => z == Zone.exile)).isNone &&
      (g2.followMovedToZone? exId (fun (z : Zone) => z == Zone.hand me)).map (fun (o : GameObject) => o.id) == some handId
    (g2, ok)
  let batchLookbackAndFlickerOk :=
    simDiesOk && dtFizzleOk && reflFizzleOk && flickerIsoOk &&
    [gSimDies, gDtFizzle, gDtLki, gReflFizzle, gFlickerIso].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 8. CR 800.4a/c/d/i/j multiplayer `concede` cleanup & replay determinism.
  let (gConcedeAfter, concedeSubOk) :=
    let p0 : PlayerId := ⟨0⟩
    let p1 : PlayerId := ⟨1⟩
    let p2 : PlayerId := ⟨2⟩
    let g0 : Game :=
      match Start.start {
        seats := #[
          { name := "Chandra", deck := testRedDeck },
          { name := "Nissa", deck := testGreenDeck },
          { name := "Liliana", deck := testRedDeck }
        ]
        format := .constructed
        seed := 3
        startingPlayer := some 0
      } with
      | .ok g => keepOpeningHands g 16
      | .error e => panic! e
    let g := addPermanent (addPermanent (addPermanent g0 bear p1 p1) hero p0 p0) { bear with name := "Phase14 Bribed Bear" } p2 p1
    let p1OwnId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear" && o.owner == p1))[0]!.id
    let p0HeroId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Event Hero" && o.owner == p0))[0]!.id
    let p2BribedId := (g.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Bribed Bear"))[0]!.id
    let g := g.createEffect (.control p0HeroId p1 (untilSourceLeaves := some p1OwnId)) (cause := some testCause)
    let g := g.registerDelayedTrigger { controller := p1, source := none, kind := .attackPumpPerPlains, cause := testCause }
    let gAfter := mustApply g p1 .concede
    let ok :=
      (gAfter.player p1).lost &&
      (gAfter.player p1).leftTheGame &&
      !gAfter.over &&
      (gAfter.findObject? p1OwnId).all (fun (o : GameObject) => !o.isOnBattlefield) &&
      (gAfter.findObject? p0HeroId).any (fun (o : GameObject) => o.isOnBattlefield && gAfter.controllerOf o == some p0) &&
      (gAfter.findObject? (gAfter.followMoved p2BribedId)).any (fun (o : GameObject) => o.zone == Zone.exile) &&
      !gAfter.delayedTriggers.any (fun (dt : DelayedTrigger) => dt.controller == p1)
    (gAfter, ok)
  let concedeCleanupOk :=
    concedeSubOk &&
    Game.replayEvents gConcedeAfter.events == gConcedeAfter &&
    allRulesEventsClassified gConcedeAfter

  -- 9. Multi-kind `proliferateTarget` CR 616.1 pause chaining & deferred `.proliferated` event.
  let prolifWatcherDef : CardDef := {
    bear with
    name := "Phase14 Prolif Watcher"
    triggeredAbilities := #[
      TriggeredAbility.ofPattern (.playerAction .you .proliferate)
        "Whenever you proliferate, you gain 1 life."
        (.gainLife 1)
    ]
  }
  let (gProlifP1, gProlifP2, gProlifDone, prolifSubOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) samsonDef14 me me) prolifWatcherDef me me
    let bId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Event Bear"))[0]!.id
    let docId := (g0.battlefield.filter (fun (o : GameObject) => o.name == "Phase14 Doc Samson"))[0]!.id
    let g0 := g0.record (GameEvent.counters g0.turnNumber (some me) (g0.snapshot (g0.object! bId)) .plusOnePlusOne 1 (cause := testCause))
    let g0 := g0.record (GameEvent.counters g0.turnNumber (some me) (g0.snapshot (g0.object! bId)) .shield 1 (cause := testCause))
    let idDocPlus : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
    let idDbl : ReplacementId := { kind := .multiplyCountersPut, object := some docId }
    let dblSpec : ReplacementSpec := {
      id := idDbl
      source := some docId
      controller := some me
      affectedPlayer := me
      kind := .modifyCountersPut (some bId) none 0 2
    }
    let g0 := g0.createEffect (.replacement dblSpec) (cause := some testCause)
    let preEvIdx := g0.events.size
    let hasProlifSince (g : Game) : Bool :=
      (g.events.extract preEvIdx g.events.size).any (fun e =>
        match e.change with
        | .rules (.player (.proliferated ..)) => true
        | _ => false)
    let gP1 := g0.proliferateTarget me #[Target.permanent bId]
    -- Prompt 1 (+1/+1): choose Doc Samson (+1) first, then *2 => (1 + 1) * 2 = 4 added (total 5).
    let gP2 := mustApply gP1 me (.chooseReplacement idDocPlus)
    -- Prompt 2 (.shield): choose *2 first, then Doc Samson (+1) => (1 * 2) + 1 = 3 added (total 4).
    let gDone := mustApply gP2 me (.chooseReplacement idDbl)
    let ok :=
      (match gP1.pending with | Pending.chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      !hasProlifSince gP1 &&
      gP1.waitingTriggers.isEmpty &&
      gP1.stack.isEmpty &&
      (gP1.object! bId).status.plusOnePlusOne == 1 &&
      (gP1.object! bId).status.shield == 1 &&
      (match gP2.pending with | Pending.chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      !hasProlifSince gP2 &&
      gP2.waitingTriggers.isEmpty &&
      gP2.stack.isEmpty &&
      (gP2.object! bId).status.plusOnePlusOne == 5 &&
      (gP2.object! bId).status.shield == 1 &&
      gDone.pending == .none &&
      hasProlifSince gDone &&
      (gDone.object! bId).status.plusOnePlusOne == 5 &&
      (gDone.object! bId).status.shield == 4 &&
      gDone.stack.size == 1
    (gP1, gP2, gDone, ok)
  let proliferateTargetPauseOk :=
    prolifSubOk &&
    [gProlifP1, gProlifP2, gProlifDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  let mustHold14 (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 14 guard failed: {label}"

  [ mustHold14 "painLandBracketOk" painLandBracketOk,
    mustHold14 "costPickAndLoyaltyOk" costPickAndLoyaltyOk,
    mustHold14 "irrevProposalEventsOk" irrevProposalEventsOk,
    mustHold14 "morphAndResCastOk" morphAndResCastOk,
    mustHold14 "singleWriterAndMirrorOk" singleWriterAndMirrorOk,
    mustHold14 "combatDmgAndShieldPwOk" combatDmgAndShieldPwOk,
    mustHold14 "batchLookbackAndFlickerOk" batchLookbackAndFlickerOk,
    mustHold14 "concedeCleanupOk" concedeCleanupOk,
    mustHold14 "proliferateTargetPauseOk" proliferateTargetPauseOk ].all id

/- Phase 15 isolation & replay tests:
   1. Pause-safe `.sequence` resolution across interactive `Pending` + multi-object
      CR 616.1 `chooseReplacement` loops, plus `mayThen` replacement pause safety.
   2. CR 117.3c standalone mana-ability SBAs & non-active `pendingPriority`
      retention across SBA/trigger prompts.
   3. CR 601.2b/f/h teamwork tap ordering (untapped until 601.2h, CR 733.1
      reversal if tapped for mana during 601.2g) & paid `.mayCastCards` /
      `.mayCastFromGraveyard` CR 601.2g mana-ability unlock.
   4. CR 603.3b shared-source distinct trigger ordering (index-based
      `Action.stackTriggers`) vs. truly identical trigger auto-stacking.
   5. `openBatchStack` Ward `newlyTargeted` across batch close & nested
      `ProposalCheckpoint` (`outerProposalCheckpoints`) deterministic replay.
   6. Simultaneous-batch `moved.before` LKI + pre-batch `hasIndestructible` &
      multi-pass CR 704.3 / 704.8 SBAs.
   7. CR 510.4 / 122.1c / 702.19b–f / 802.5 / 506.4 combat alignment
      (first-strike/double-strike eligibility, simultaneous shield-counter
      prevention vs. lifelink/deathtouch, `.creatureYouControlDealtDamage`
      batch deduplication, tramplers vs. departed planeswalkers, APNAP
      multi-defender blocker combat damage assignment, CR 506.4 control change).
   8. CR 514.2 cleanup expiry (`"until end of turn"` ability grants & phased-out
      marked damage clearing).
   9. CR 800.4f/j leave-game combat/ward transitions (skip `.declareAttackers`
      when active player left, `.declareBlockers` `remainedUnblocked` when
      defender leaves, `.payOrLetCounter` / `.payWard` when caster leaves).
   10. Layer-7c `chosenCreatureType` scoping & `lastKnownBefore?` single-life LKI.
   11. `ObjectId ⟨0⟩` parity & `EngineChange.stackEntry` deterministic replay. -/
#guard
  let opp : PlayerId := ⟨1⟩
  let headHuntDef : CardDef :=
    { bear with name := "Phase15 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }

  -- 1. Pause-safe `.sequence` (scry -> multi-creature `destroyAllCreatures` with 2 CR 616.1 pauses -> draw 1)
  --    and `mayThen` replacement pause safety.
  let seqWipeSpellDef : CardDef := {
    name := "Phase15 Scry Wipe Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      resolution := .sequence [.scry (.fixed 1), .destroyAllCreatures, .draw (.fixed 1)]
      phrase := "Scry 1. Destroy all creatures. Draw a card."
    }
  }
  let (gSeqP1, gSeqP2, gSeqP3, gSeqDone, seqPauseOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) headHuntDef opp opp
    let b1 := (g0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
    let b2 := (g0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
    let hOpp := (g0.battlefield.filter (·.name == "Phase15 Head Hunt"))[0]!.id
    let g0 := (g0.recordPutCounters b1 .finality 1 (some me) (cause := some testCause)).recordPutCounters
      b2 .finality 1 (some me) (cause := some testCause)
    let g0 := g0.recordPutCounters hOpp .indestructible 1 (some opp) (cause := some testCause)
    let g0 := insertObject g0 seqWipeSpellDef me (.hand me)
    let spId := (g0.player me).hand.back!
    let gCast := mustApply g0 me (.cast spId)
    let handBeforeResolve := (gCast.player me).hand.size
    let g1 := gCast.resolveTop
    let topLib := (g1.player me).library.back!
    let g2 := mustApply g1 me (.scry #[topLib] #[])
    let pickFin1 : ReplacementId := { kind := .finalityCounterExile, object := some b1 }
    let pickFin2 : ReplacementId := { kind := .finalityCounterExile, object := some b2 }
    let g3 := mustApply g2 me (.chooseReplacement pickFin1)
    let g4 := mustApply g3 me (.chooseReplacement pickFin2)
    let ok :=
      (match g1.pending with | .scry p _ _ => p == me | _ => false) &&
      (g1.player me).hand.size == handBeforeResolve &&
      (match g2.pending with | .chooseReplacement p cs => p == me && cs.contains pickFin1 | _ => false) &&
      (g2.player me).hand.size == handBeforeResolve &&
      (match g3.pending with | .chooseReplacement p cs => p == me && cs.contains pickFin2 | _ => false) &&
      (g3.player me).hand.size == handBeforeResolve &&
      g4.pending == .none &&
      g4.stack.isEmpty &&
      (g4.player me).hand.size == handBeforeResolve + 1 &&
      !(g4.battlefield.any (fun o => o.id == b1 || o.id == b2))
    (g1, g2, g3, g4, ok)
  let (gMayP1, gMayP2, gMayDone, mayThenPauseOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) headHuntDef opp opp
    let srcId := (g0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
    let vicId := (g0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
    let g0 := g0.recordPutCounters vicId .finality 1 (some me) (cause := some testCause)
    let handPre := (g0.player me).hand.size
    let abObjId : ObjectId := ⟨g0.nextObjectId⟩
    let g0 := g0.record (GameEvent.triggerPutOnStack g0.turnNumber abObjId (g0.snapshot (g0.object! srcId)) me
      (spec := { sourceId := some srcId }))
    let g0 := g0.change (.pushContinuationFrame { resolvingAbility := some abObjId })
    let gP1 := g0.applyTriggeredAbility me (.onEnterDraw 1) (some srcId) #[] #[] none none "Hero"
      (some (.may (.pay CostSpec.sacrificeAnotherCreature) (.draw (.fixed 1)) .ifYouDo))
    let gP2 := mustApply gP1 me (.choosePermanents #[vicId])
    let pickFinV : ReplacementId := { kind := .finalityCounterExile, object := some vicId }
    let gDone := mustApply gP2 me (.chooseReplacement pickFinV)
    let ok :=
      (match gP1.pending with | .fraChoice p (.maySacrificeAnotherCreatureForPower _) => p == me | _ => false) &&
      (gP1.player me).hand.size == handPre &&
      (match gP2.pending with | .chooseReplacement p cs => p == me && cs.contains pickFinV | _ => false) &&
      (gP2.player me).hand.size == handPre &&
      gDone.pending == .none &&
      (gDone.player me).hand.size == handPre + 1
    (gP1, gP2, gDone, ok)
  let seqAndMayThenOk :=
    seqPauseOk && mayThenPauseOk &&
    [gSeqP1, gSeqP2, gSeqP3, gSeqDone, gMayP1, gMayP2, gMayDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 2. CR 117.3c standalone mana-ability SBAs & non-active `pendingPriority` retention across trigger prompts.
  let targetedDiesDef : CardDef := {
    bear with
    name := "Phase15 Targeted Dies"
    triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature]
  }
  let (gStandaloneMana, gNonActivePrompt, gNonActiveRetained, manaAndPrioOk) :=
    let gBase := mustApply (addPermanent (addPermanent (addPermanent afterDraw forest opp opp) bear opp opp) targetedDiesDef me me) me .pass
    let fIdB := (gBase.battlefield.filter (fun o => o.name == "Forest" && o.controller == some opp))[0]!.id
    let oppTgtB := (gBase.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
    let dIdB := (gBase.battlefield.filter (·.name == "Phase15 Targeted Dies"))[0]!.id
    let gDamaged := gBase.markDamageOn (gBase.object! dIdB) 2 "lethal while opp has priority" (cause := some testCause)
    -- Standalone `tapForMana` by `opp` runs `receivePriority opp`: SBA destroys `dIdB`, `me` is prompted to target
    -- the dies trigger, and once `me` chooses target `oppTgtB`, `pendingPriority` returns priority to `opp`!
    let gPrompt := mustApply gDamaged opp (.tapForMana fIdB (.colored .green))
    let gAfterTarget := mustApply gPrompt me (.target (.permanent oppTgtB))
    -- Pure standalone untargeted check: lethal Bear dies immediately on standalone `tapForMana` and `opp` keeps priority.
    let gBase2 := mustApply (addPermanent (addPermanent afterDraw forest opp opp) bear me me) me .pass
    let fId2 := (gBase2.battlefield.filter (fun o => o.name == "Forest" && o.controller == some opp))[0]!.id
    let bId2 := (gBase2.battlefield.filter (·.name == bear.name))[0]!.id
    let gDam2 := gBase2.markDamageOn (gBase2.object! bId2) 2 "lethal" (cause := some testCause)
    let gManaSba := mustApply gDam2 opp (.tapForMana fId2 (.colored .green))
    let ok :=
      !(gManaSba.battlefield.any (·.id == bId2)) &&
      gManaSba.priority == opp &&
      (gManaSba.player opp).manaPool.green == 1 &&
      !(gPrompt.battlefield.any (·.id == dIdB)) &&
      gPrompt.pending == .chooseTargets me &&
      gPrompt.pendingPriority == some opp &&
      gAfterTarget.pending == .none &&
      gAfterTarget.stack.size == 1 &&
      gAfterTarget.priority == opp &&
      gAfterTarget.pendingPriority.isNone
    (gManaSba, gPrompt, gAfterTarget, ok)
  let standaloneManaAndPrioOk :=
    manaAndPrioOk &&
    [gStandaloneMana, gNonActivePrompt, gNonActiveRetained].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 3. CR 601.2b/f/h teamwork tap ordering & paid `.mayCastCards` / `.mayCastFromGraveyard` CR 601.2g mana unlock.
  let whiteDorkDef : CardDef := {
    name := "Phase15 White Dork"
    manaCost := ManaCost.empty
    types := #[.creature]
    subtypes := #["Human", "Druid"]
    power := some 2
    toughness := some 2
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .white, .const 1)])]
  }
  let wDrawDef : CardDef := {
    name := "Phase15 Paid Draw"
    manaCost := ⟨#[.colored .white]⟩
    types := #[.instant]
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let teamworkStrikeDef : CardDef := {
    lightningBolt with
    name := "Phase15 Teamwork Strike"
    manaCost := ⟨#[.colored .white]⟩
    keywords := #[.teamwork 2]
  }
  let (gTwTarget, gTwReverted, gPaidCardsDone, gPaidGyDone, teamworkAndPaidCastOk) :=
    let g0 := addPermanent afterDraw whiteDorkDef me me
    let dorkId := (g0.battlefield.filter (·.name == "Phase15 White Dork"))[0]!.id
    let g0 := insertObject g0 bear opp .battlefield (some opp) { attacking := true, summoningSick := false }
    let ogreId := (g0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
    let g0 := insertObject g0 teamworkStrikeDef me (.hand me)
    let hsId := (g0.player me).hand.back!
    let gPreCast := g0
    let g1 := mustApply g0 me (.cast hsId)
    let g2 := mustApply g1 me (.announceTeamwork true)
    let g3 := mustApply g2 me (.choosePermanents #[dorkId])
    let g4 := mustApply g3 me (.target (.permanent ogreId))
    -- At CR 601.2b (`g3`) and CR 601.2c (`g4`), `dorkId` is STILL untapped on the battlefield,
    -- yet `tapForMana` rejects tapping `dorkId` because it is already chosen for teamwork!
    -- With 0 `{W}`, `.pay` reverses the proposal via CR 733.1 (`hsId` back in hand, `dorkId` untapped);
    -- with `{W}` in pool, `.pay` taps `dorkId` at CR 601.2h!
    let tapDorkRejected :=
      match g4.applyAction me (.tapForMana dorkId (.colored .white)) with
      | .error _ => true
      | .ok _ => false
    let gRev := mustApply g4 me .pay
    let gTwPaid := mustApply (g4.addMana me (.colored .white) 1) me .pay
    -- Paid `.mayCastCards` (`withoutPaying := false`) unlocks `tapForMana` during CR 601.2g:
    let gMc0 := addPermanent (insertObject afterDraw wDrawDef me .exile) plains me me
    let pId1 := (gMc0.battlefield.filter (·.name == "Plains"))[0]!.id
    let exCardId := (gMc0.objects.filter (fun o => o.name == "Phase15 Paid Draw" && o.zone == .exile))[0]!.id
    let gMc1 := (gMc0.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice me (.mayCastCards #[exCardId] false false)))
    let gMc2 := mustApply gMc1 me (.cast exCardId)
    let gMc3 := mustApply gMc2 me (.tapForMana pId1 (.colored .white))
    let gMc4 := mustApply gMc3 me .pay
    -- Paid `.mayCastFromGraveyard` unlocks `tapForMana` during CR 601.2g:
    let gGy0 := addPermanent (insertObject afterDraw wDrawDef me (.graveyard me)) plains me me
    let pId2 := (gGy0.battlefield.filter (·.name == "Plains"))[0]!.id
    let gyCardId := ((gGy0.player me).graveyard.filter (fun id => (gGy0.object! id).name == "Phase15 Paid Draw"))[0]!
    let gGy1 := (gGy0.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice me (.mayCastFromGraveyard #[gyCardId])))
    let gGy2 := mustApply gGy1 me (.cast gyCardId)
    let gGy3 := mustApply gGy2 me (.tapForMana pId2 (.colored .white))
    let gGy4 := mustApply gGy3 me .pay
    let ok :=
      !(g3.object! dorkId).status.tapped &&
      !(g4.object! dorkId).status.tapped &&
      tapDorkRejected &&
      !(gRev.object! dorkId).status.tapped &&
      (gRev.player me).manaPool.white == (gPreCast.player me).manaPool.white &&
      (gRev.player me).hand.contains hsId &&
      (gTwPaid.object! dorkId).status.tapped &&
      gTwPaid.stack.size == 1 &&
      gMc4.pending == .none &&
      gMc4.stack.size == 1 &&
      (gMc4.object! pId1).status.tapped &&
      gGy4.pending == .none &&
      gGy4.stack.size == 1 &&
      (gGy4.object! pId2).status.tapped
    (gTwPaid, gRev, gMc4, gGy4, ok)
  let twAndPaidAllOk :=
    teamworkAndPaidCastOk &&
    [gTwTarget, gTwReverted, gPaidCardsDone, gPaidGyDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 4. CR 603.3b shared-source distinct trigger ordering vs. truly identical auto-stacking.
  let dualEtbDef : CardDef := {
    bear with
    name := "Phase15 Dual ETB"
    triggeredAbilities := #[.onEnterDraw 1, .onEnterGainLife 3]
  }
  let identEtbDef : CardDef := {
    bear with
    name := "Phase15 Identical ETB"
    triggeredAbilities := #[.onEnterDraw 1, .onEnterDraw 1]
  }
  let (gDualPrompt, gDualOrdered, gDualFirstRes, gIdentAuto, cr6033bOk) :=
    let g0 := insertObject afterDraw dualEtbDef me (.hand me)
    let cId := (g0.player me).hand.back!
    let gCast := mustApply g0 me (.cast cId)
    let gRes := mustApply (mustApply gCast me .pass) opp .pass
    -- `[0]` is `.onEnterDraw 1`, `[1]` is `.onEnterGainLife 3`.
    -- `stackTriggers #[1, 0]` puts `[1]` on bottom and `[0]` on top, so resolving top draws first before life gain!
    let lifePre := (gRes.player me).life
    let handPre := (gRes.player me).hand.size
    let gOrd := mustApply gRes me (.stackTriggers #[1, 0])
    let gTop := mustApply (mustApply gOrd me .pass) opp .pass
    -- Identical triggers on the same source auto-stack without prompting `chooseTriggerToStack`:
    let gI0 := insertObject afterDraw identEtbDef me (.hand me)
    let icId := (gI0.player me).hand.back!
    let gICast := mustApply gI0 me (.cast icId)
    let gIRes := mustApply (mustApply gICast me .pass) opp .pass
    let ok :=
      gRes.pending == .chooseTriggerToStack me &&
      gRes.waitingTriggers.size == 2 &&
      gOrd.pending == .none &&
      gOrd.stack.size == 2 &&
      (gTop.player me).hand.size == handPre + 1 &&
      (gTop.player me).life == lifePre &&
      gIRes.pending == .none &&
      gIRes.waitingTriggers.isEmpty &&
      gIRes.stack.size == 2
    (gRes, gOrd, gTop, gIRes, ok)
  let triggerOrderingAllOk :=
    cr6033bOk &&
    [gDualPrompt, gDualOrdered, gDualFirstRes, gIdentAuto].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 5. `openBatchStack` Ward `newlyTargeted` across batch close & nested `ProposalCheckpoint` replay.
  let wardBearDef : CardDef := {
    bear with
    name := "Phase15 Ward Bear"
    keywords := #[.ward (CostSpec.ofGeneric 2)]
  }
  let pingAnyDef : CardDef := {
    lightningBolt with
    name := "Phase15 Ping"
    manaCost := ManaCost.empty
  }
  let painManaLandDef : CardDef := {
    name := "Phase15 Pain Land"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .white, .const 1)]) (damageYou := 1)]
  }
  let (gWardRetarget, gNestedInnerRev, gNestedOuterRev, batchStackAndNestedCpOk) :=
    -- Retarget a stack spell onto a Ward permanent inside an enclosing `withBatch`:
    -- `openBatchStack` preserves the pre-batch stack so `newlyTargeted` queues Ward when the batch closes!
    let g0 := addPermanent (addPermanent afterDraw bear opp opp) wardBearDef opp opp
    let plainOpp := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let wardOpp := (g0.battlefield.filter (·.name == "Phase15 Ward Bear"))[0]!.id
    let g0 := insertObject g0 pingAnyDef me (.hand me)
    let pingH := (g0.player me).hand.back!
    let gCast := mustApply (mustApply g0 me (.cast pingH)) me (.target (.permanent plainOpp))
    let spStackId := gCast.stack.back!.objectId
    let gRet := gCast.withBatch (some testCause) (fun g =>
      g.setStackEntryTargets spStackId #[.permanent wardOpp] #[])
    let gRetPrio := gRet.receivePriority me
    let gRetWardPrompt := mustApply (mustApply gRetPrio me .pass) opp .pass
    -- Nested `ProposalCheckpoint`: outer `saveProposalCheckpoint` (#1) + inner `castAsPartOfResolution`
    -- `saveProposalCheckpoint` (#2 -> `outerProposalCheckpoints.size == 1`); reversing inner `{W}` cast via `.pay`
    -- restores `exId` to `.exile` while popping checkpoint #1 back into `proposalCheckpoint`!
    let _ := painManaLandDef
    let gN0 := insertObject afterDraw wDrawDef me .exile
    let exId := (gN0.objects.filter (fun o => o.name == "Phase15 Paid Draw" && o.zone == .exile))[0]!.id
    let gN1 := (gN0.change .saveProposalCheckpoint).change (.pushContinuationFrame {})
    let gNPaused := gN1.castAsPartOfResolution me exId (withoutManaCost := false)
    let gNInnerRev := mustApply gNPaused me .pay
    let gNOuterCleared := (gNInnerRev.change .clearProposalCheckpoint).change .popContinuationFrame
    let ok :=
      gRetPrio.stack.size == 2 &&
      (match gRetWardPrompt.pending with | .payWard p _ cost _ => (p == me) && cost.soleGenericMana? == some 2 | _ => false) &&
      gNPaused.pending == .activateManaAbilities me &&
      gNPaused.outerProposalCheckpoints.size == 1 &&
      gNInnerRev.outerProposalCheckpoints.isEmpty &&
      gNInnerRev.proposalCheckpoint.isSome &&
      (gNInnerRev.objects.any (fun o => o.id == exId && o.zone == .exile)) &&
      gNOuterCleared.proposalCheckpoint.isNone
    (gRetWardPrompt, gNPaused, gNOuterCleared, ok)
  let wardAndNestedAllOk :=
    batchStackAndNestedCpOk &&
    [gWardRetarget, gNestedInnerRev, gNestedOuterRev].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 6. Simultaneous-batch `moved.before` LKI + pre-batch `hasIndestructible` & multi-pass CR 704.3 / 704.8 SBAs.
  let bearLordDef : CardDef := {
    bear with
    name := "Phase15 Bear Lord"
    staticAbilities := #[.otherCreaturesGet #[.bear] 1 1]
  }
  let planGrantorDef : CardDef := {
    name := "Phase15 Artifact Creature"
    manaCost := ManaCost.empty
    types := #[.artifact, .creature]
    subtypes := #["Construct"]
    power := some 2
    toughness := some 2
  }
  let condIndestDef : CardDef := {
    bear with
    name := "Phase15 Conditional Indestructible"
    staticAbilities := #[.indestructibleIfArtifactCreatureOrPlan]
  }
  let (gSimBatch, gMultiSba, batchLkiAndMultiSbaOk) :=
    -- Simultaneous `destroyAllCreatures`:
    -- (a) `Bear Lord` (2/2) + `Event Bear` (2/2, boosted to 3/3 by Lord) both die; `Event Bear`'s `moved.before`
    --     snapshot and `lastKnownPowerOf?` see pre-batch power 3 even though `Bear Lord` was destroyed first!
    -- (b) `Phase15 Artifact Creature` + `Phase15 Conditional Indestructible` face `destroyAllCreatures`;
    --     pre-batch `hasIndestructible` keeps `Phase15 Conditional Indestructible` alive even though the artifact
    --     creature is destroyed earlier in the same loop!
    let g0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw bearLordDef me me) bear me me)
      planGrantorDef me me) condIndestDef me me
    let lordId := (g0.battlefield.filter (·.name == "Phase15 Bear Lord"))[0]!.id
    let subBearId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let artCrId := (g0.battlefield.filter (·.name == "Phase15 Artifact Creature"))[0]!.id
    let indCrId := (g0.battlefield.filter (·.name == "Phase15 Conditional Indestructible"))[0]!.id
    let gWiped := g0.applyUnified me { resolution := .destroyAllCreatures, phrase := "Destroy all creatures" } #[]
    let lkiPowerOk := gWiped.lastKnownPowerOf? subBearId == some 3
    let indSurvived :=
      !(gWiped.battlefield.any (fun o => o.id == lordId || o.id == subBearId || o.id == artCrId)) &&
      gWiped.battlefield.any (·.id == indCrId)
    -- Multi-pass CR 704.3 SBA:
    -- Pass 1 destroys `Bear Lord` (2/2 with 2 damage) while a 1/1 Bear (`tinyBear`) has 1 damage (currently 2/2).
    -- Pass 2 sees `tinyBear` is now 1/1 with 1 marked damage and destroys it in the same `checkSBA` call!
    let tinyBearDef : CardDef := { bear with name := "Phase15 Tiny Bear", power := some 1, toughness := some 1 }
    let gS0 := addPermanent (addPermanent afterDraw bearLordDef me me) tinyBearDef me me
    let sLordId := (gS0.battlefield.filter (·.name == "Phase15 Bear Lord"))[0]!.id
    let sTinyId := (gS0.battlefield.filter (·.name == "Phase15 Tiny Bear"))[0]!.id
    let gS1 := (gS0.markDamageOn (gS0.object! sLordId) 2 "lethal lord" (cause := some testCause)).markDamageOn
      (gS0.object! sTinyId) 1 "1 dmg tiny" (cause := some testCause)
    let gS2 := gS1.checkSBA
    let multiSbaOk :=
      !(gS2.battlefield.any (fun o => o.id == sLordId || o.id == sTinyId))
    (gWiped, gS2, lkiPowerOk && indSurvived && multiSbaOk)
  let lkiAndMultiSbaAllOk :=
    batchLkiAndMultiSbaOk &&
    [gSimBatch, gMultiSba].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 7. CR 510.4 / 122.1c / 702.19b–f / 802.5 / 506.4 combat alignment.
  let fsBearDef : CardDef := { bear with name := "Phase15 FS Bear", keywords := #[Keyword.firstStrike] }
  let dtLifeDef : CardDef := {
    bear with
    name := "Phase15 DT Lifelinker"
    keywords := #[Keyword.deathtouch, Keyword.lifelink]
  }
  let trampler4Def : CardDef := {
    bear with
    name := "Phase15 Trampler"
    power := some 4
    toughness := some 4
    keywords := #[Keyword.trample]
  }
  let pwVictimDef : CardDef := {
    name := "Phase15 Target PW"
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 3
  }
  let dmgOnceWatcherDef : CardDef := {
    name := "Phase15 Batch Damage Watcher"
    manaCost := ManaCost.empty
    types := #[.enchantment]
    triggeredAbilities := #[SharedTrigger.watch .sheHulkRedirectOnce |>.toTriggeredAbility]
  }
  -- 7a. CR 510.4: first-strike attacker deals 2 in FS step; granting `Event Bear` first strike AFTER FS step does NOT
  --     exclude `Event Bear` from regular combat damage, while granting `FS Bear` double strike AFTER FS step lets `FS Bear`
  --     deal regular combat damage too!
  let (gCbt5104, cbt5104Ok) :=
    let g0 := addPermanent (addPermanent afterDraw fsBearDef me me) bear me me
    let fsId := (g0.battlefield.filter (·.name == "Phase15 FS Bear"))[0]!.id
    let brId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let g1 := g0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 me (.declareAttackers #[fsId, brId] none #[] #[])
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 opp (.declareBlockers #[])
    let gFs := mustApply (mustApply g1 me .pass) opp .pass
    -- After FS step (`opp` at 18): grant `fsId` double strike and `brId` first strike, then advance to regular combat damage:
    -- `fsId` (now double strike) deals 2 AND `brId` (didn't have FS at FS step) deals 2 => `opp` at 14!
    let gGrant := (gFs.createEffect (.keywordsUntilEot fsId #[Keyword.doubleStrike]) (cause := some testCause)).createEffect
      (.keywordsUntilEot brId #[Keyword.firstStrike]) (cause := some testCause)
    let gReg := mustApply (mustApply gGrant me .pass) opp .pass
    (gReg, (gFs.player opp).life == 18 && (gReg.player opp).life == 14)
  -- 7b. CR 122.1c simultaneous shield counter in combat vs. TWO deathtouch+lifelink blockers +
  --     `.creatureYouControlDealtDamage` single trigger on simultaneous combat damage to two creatures.
  let (gShieldSim, gBatchDmgTrig, shieldAndBatchTrigOk) :=
    let g0 := addPermanent (addPermanent (addPermanent afterDraw bear me me) dtLifeDef opp opp)
      { dtLifeDef with name := "Phase15 DT Lifelinker 2" } opp opp
    let atkId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let blk1 := (g0.battlefield.filter (·.name == "Phase15 DT Lifelinker"))[0]!.id
    let blk2 := (g0.battlefield.filter (·.name == "Phase15 DT Lifelinker 2"))[0]!.id
    let g0 := g0.recordPutCounters atkId .shield 1 (some me) (cause := some testCause)
    let oppLifePre := (g0.player opp).life
    let g1 := g0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 me (.declareAttackers #[atkId] none #[] #[])
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let g1 := mustApply g1 opp (.declareBlockers #[(blk1, atkId), (blk2, atkId)])
    let g1 := mustApply (mustApply g1 me .pass) opp .pass
    let gDmg := mustApply g1 me (.assignCombatDamage #[{ source := atkId, toCreatures := #[(blk1, 2)], toPlayer := 0 }])
    let shieldOk :=
      gDmg.battlefield.any (·.id == atkId) &&
      (gDmg.object! atkId).status.shield == 0 &&
      (gDmg.object! atkId).status.damage == 0 &&
      (gDmg.player opp).life == oppLifePre
    -- Simultaneous combat damage to TWO creatures controlled by `opp` under `dmgOnceWatcherDef`:
    let gW0 := addPermanent (addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me)
      { bear with name := "Opp Wall 1", toughness := some 4 } opp opp)
      { bear with name := "Opp Wall 2", toughness := some 4 } opp opp) dmgOnceWatcherDef opp opp
    let a1 := (gW0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
    let a2 := (gW0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
    let w1 := (gW0.battlefield.filter (·.name == "Opp Wall 1"))[0]!.id
    let w2 := (gW0.battlefield.filter (·.name == "Opp Wall 2"))[0]!.id
    let gW1 := gW0.beginStep .beginningOfCombat
    let gW1 := mustApply (mustApply gW1 me .pass) opp .pass
    let gW1 := mustApply gW1 me (.declareAttackers #[a1, a2] none #[] #[])
    let gW1 := mustApply (mustApply gW1 me .pass) opp .pass
    let gW1 := mustApply gW1 opp (.declareBlockers #[(w1, a1), (w2, a2)])
    let gWDmg := mustApply (mustApply gW1 me .pass) opp .pass
    -- Two creatures dealt damage triggers `watchSheHulkRedirectOnce` twice; under CR 603.3b–d,
    -- the first copy is placed on `g.stack` and prompts `opp` for targets while the second stays
    -- in `waitingTriggers` (`ordered := true`) until `opp` announces the first copy's target.
    let gWDmg2 := mustApply gWDmg opp (.target (Target.player me))
    -- Single creature dealt simultaneous combat damage by two blockers triggers ONCE with summed `batchTotal == 4` (MSH 512):
    let gS0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw
      { bear with name := "Phase15 Big Attacker", toughness := some 5 } me me)
      dmgOnceWatcherDef me me) bear opp opp) hero opp opp
    let sAtk := (gS0.battlefield.filter (·.name == "Phase15 Big Attacker"))[0]!.id
    let sb1 := (gS0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
    let sb2 := (gS0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
    let gS1 := gS0.beginStep .beginningOfCombat
    let gS1 := mustApply (mustApply gS1 me .pass) opp .pass
    let gS1 := mustApply gS1 me (.declareAttackers #[sAtk] none #[] #[])
    let gS1 := mustApply (mustApply gS1 me .pass) opp .pass
    let gS1 := mustApply gS1 opp (.declareBlockers #[(sb1, sAtk), (sb2, sAtk)])
    let gS1 := mustApply (mustApply gS1 me .pass) opp .pass
    let gSDmg := mustApply gS1 me (.assignCombatDamage #[{ source := sAtk, toCreatures := #[(sb1, 2)], toPlayer := 0 }])
    let batchTrigOk :=
      gWDmg.pending == .chooseTargets opp &&
      gWDmg.stack.size == 1 &&
      gWDmg.waitingTriggers.size == 1 &&
      gWDmg.waitingTriggers[0]!.ordered &&
      gWDmg2.pending == .chooseTargets opp &&
      gWDmg2.stack.size == 2 &&
      gWDmg2.waitingTriggers.isEmpty &&
      gSDmg.pending == .chooseTargets me &&
      gSDmg.stack.size == 1 &&
      gSDmg.waitingTriggers.isEmpty &&
      gSDmg.stack[0]!.lastKnownPower == some 4 &&
      Game.replayEvents gWDmg2.events == gWDmg2 && allRulesEventsClassified gWDmg2 &&
      Game.replayEvents gSDmg.events == gSDmg && allRulesEventsClassified gSDmg
    (gDmg, gWDmg, shieldOk && batchTrigOk)
  -- 7c. CR 702.19b / 702.19f: unblocked & blocked tramplers attacking a planeswalker that left combat deal 0 to defending player;
  --     plus CR 506.4 control change removes creature from combat, and CR 802.5 APNAP multi-defender blocker assignment.
  let (gTrUnblk, gTrBlk, gCtrlRem, gMultiBlkDone, trampleCtrlAndApnapBlkOk) :=
    let mkPwCombat (blocked : Bool) : Game :=
      let g0 := addPermanent (addPermanent afterDraw trampler4Def me me) pwVictimDef opp opp
      let g0 := if blocked then addPermanent g0 bear opp opp else g0
      let trId := (g0.battlefield.filter (·.name == "Phase15 Trampler"))[0]!.id
      let pwId := (g0.battlefield.filter (·.name == "Phase15 Target PW"))[0]!.id
      let g0 := g0.recordPutCounters pwId .loyalty 3 (some opp) (cause := some testCause)
      let g1 := g0.beginStep .beginningOfCombat
      let g1 := mustApply (mustApply g1 me .pass) opp .pass
      let g1 := mustApply g1 me (.declareAttackers #[trId] none #[] #[some pwId])
      let g1 := mustApply (mustApply g1 me .pass) opp .pass
      let g1 :=
        if blocked then
          let blkId := (g1.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
          let gB := mustApply g1 opp (.declareBlockers #[(blkId, trId)])
          let (gB, _) := gB.move blkId .exile none (cause := some testCause)
          gB
        else
          mustApply g1 opp (.declareBlockers #[])
      let (g2, _) := g1.move pwId .exile none (cause := some testCause)
      mustApply (mustApply g2 me .pass) opp .pass
    let gU := mkPwCombat false
    let gB := mkPwCombat true
    -- CR 506.4: gaining control of an attacking creature removes it from combat.
    let gC0 := addPermanent afterDraw bear me me
    let cAtk := (gC0.battlefield.filter (·.name == bear.name))[0]!.id
    let gC1 := gC0.beginStep .beginningOfCombat
    let gC1 := mustApply (mustApply gC1 me .pass) opp .pass
    let gC1 := mustApply gC1 me (.declareAttackers #[cAtk] none #[] #[])
    let gC2 := gC1.createEffect (.layered (.objects #[cAtk]) (.control opp) .untilEndOfTurn) (cause := some testCause)
    -- CR 802.5: 3-player game where defenders `⟨1⟩` and `⟨2⟩` each control a 3/3 blocker blocking 2 attackers;
    -- combat damage prompts `⟨1⟩` then `⟨2⟩` in APNAP order!
    let threeCfg15 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 15
      startingPlayer := some 0
    }
    let g3Base :=
      match Start.start threeCfg15 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    let bigBlkDef : CardDef := { bear with name := "Phase15 Multi Blocker", power := some 3, toughness := some 5 }
    let gM0 :=
      addPermanent (addPermanent (addPermanent (addPermanent (addPermanent (addPermanent g3Base
        bear ⟨0⟩ ⟨0⟩) { bear with name := "Atk1B" } ⟨0⟩ ⟨0⟩)
        { bear with name := "Atk2A" } ⟨0⟩ ⟨0⟩) { bear with name := "Atk2B" } ⟨0⟩ ⟨0⟩)
        bigBlkDef ⟨1⟩ ⟨1⟩) { bigBlkDef with name := "Phase15 Multi Blocker 2" } ⟨2⟩ ⟨2⟩
    let a1a := (gM0.battlefield.filter (fun o => o.name == bear.name && o.controller == some ⟨0⟩))[0]!.id
    let a1b := (gM0.battlefield.filter (·.name == "Atk1B"))[0]!.id
    let a2a := (gM0.battlefield.filter (·.name == "Atk2A"))[0]!.id
    let a2b := (gM0.battlefield.filter (·.name == "Atk2B"))[0]!.id
    let mb1 := (gM0.battlefield.filter (·.name == "Phase15 Multi Blocker"))[0]!.id
    let mb2 := (gM0.battlefield.filter (·.name == "Phase15 Multi Blocker 2"))[0]!.id
    let gM1 :=
      (((gM0.record (GameEvent.attackersDeclared gM0.turnNumber ⟨0⟩
        #[(gM0.snapshot (gM0.object! a1a), .player ⟨1⟩),
          (gM0.snapshot (gM0.object! a1b), .player ⟨1⟩),
          (gM0.snapshot (gM0.object! a2a), .player ⟨2⟩),
          (gM0.snapshot (gM0.object! a2b), .player ⟨2⟩)]
        (cause := some (.turnBased .declareAttackers)))).record
        (GameEvent.blockersDeclared gM0.turnNumber ⟨1⟩
          #[(gM0.snapshot (gM0.object! mb1), a1a), (gM0.snapshot (gM0.object! mb1), a1b)]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM0.turnNumber (gM0.snapshot (gM0.object! a1a)) #[mb1]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM0.turnNumber (gM0.snapshot (gM0.object! a1b)) #[mb1]
          (cause := some (.turnBased .declareBlockers)))
    let gM1 :=
      ((gM1.record
        (GameEvent.blockersDeclared gM1.turnNumber ⟨2⟩
          #[(gM1.snapshot (gM1.object! mb2), a2a), (gM1.snapshot (gM1.object! mb2), a2b)]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM1.turnNumber (gM1.snapshot (gM1.object! a2a)) #[mb2]
          (cause := some (.turnBased .declareBlockers)))).record
        (GameEvent.becameBlocked gM1.turnNumber (gM1.snapshot (gM1.object! a2b)) #[mb2]
          (cause := some (.turnBased .declareBlockers)))
    let gMStart := gM1.combatDamage
    let gMAfter1 := mustApply gMStart ⟨1⟩ (.assignCombatDamage #[{ source := mb1, toCreatures := #[(a1a, 2), (a1b, 1)], toPlayer := 0 }])
    let gMAfter2 := mustApply gMAfter1 ⟨2⟩ (.assignCombatDamage #[{ source := mb2, toCreatures := #[(a2a, 1), (a2b, 2)], toPlayer := 0 }])
    let ok :=
      (gU.player opp).life == 20 &&
      (gB.player opp).life == 20 &&
      !(gC2.object! cAtk).status.attacking &&
      gC2.events.any (fun e => match e.change with | .rules (.combat (.removedFromCombat eo)) => eo.id == some cAtk | _ => false) &&
      gMStart.pending == .assignCombatDamage ⟨1⟩ false &&
      gMAfter1.pending == .assignCombatDamage ⟨2⟩ false &&
      gMAfter2.pending == .none &&
      !(gMAfter2.battlefield.any (·.id == a1a)) &&
      gMAfter2.battlefield.any (·.id == a1b) &&
      gMAfter2.battlefield.any (·.id == a2a) &&
      !(gMAfter2.battlefield.any (·.id == a2b))
    (gU, gB, gC2, gMAfter2, ok)
  let combatAlignmentAllOk :=
    cbt5104Ok && shieldAndBatchTrigOk && trampleCtrlAndApnapBlkOk &&
    [gCbt5104, gShieldSim, gBatchDmgTrig, gTrUnblk, gTrBlk, gCtrlRem, gMultiBlkDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 8. CR 514.2 cleanup expiry (`"until end of turn"` ability grants & phased-out marked damage clearing).
  let (gCleanEot, cleanupPhasedAndAbOk) :=
    let g0 := addPermanent (addPermanent afterDraw bear me me) hero me me
    let phId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let abId := (g0.battlefield.filter (·.name == hero.name))[0]!.id
    let g1 := g0.markDamageOn (g0.object! phId) 1 "1 dmg before phase out" (cause := some testCause)
    let g1 := g1.record (GameEvent.phasedOut g1.turnNumber (g1.snapshot (g1.object! phId)) false (cause := testCause))
    let g1 := (g1.createEffect
      (.layered (.objects #[abId]) (.abilities { triggeredAbilities := #[.onEnterDraw 1] } .none) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[abId]) (.abilities { keywords := #[Keyword.flying] } .all) .untilEndOfTurn)
      (cause := some testCause)
    let hadFlyPre := g1.hasFlying (g1.object! abId)
    let g2 := g1.clearEOT
    let ok :=
      hadFlyPre &&
      (g2.object! phId).status.phasedOut &&
      (g2.object! phId).status.damage == 0 &&
      !g2.hasFlying (g2.object! abId) &&
      (g2.triggeredAbilities (g2.object! abId)).isEmpty
    (g2, ok)
  let cleanupAllOk :=
    cleanupPhasedAndAbOk &&
    Game.replayEvents gCleanEot.events == gCleanEot &&
    allRulesEventsClassified gCleanEot

  -- 9. CR 800.4f/j leave-game combat/ward transitions (3-player).
  let (gSkipDeclAtk, gBlkLeftUnblocked, gWardCasterLeft, leaveGameTransitionsOk) :=
    let threeCfg9 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 9
      startingPlayer := some 0
    }
    let g3 :=
      match Start.start threeCfg9 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    -- 9a. Active player `⟨0⟩` concedes during `.beginningOfCombat`: `.declareAttackers` skips `Pending.declareAttackers`
    --     (`gA1.pending == .none`), and passing priority skips `.declareBlockers` / `.combatDamage` to `.endOfCombat`!
    let gA0 := (g3.beginStep .beginningOfCombat).concede ⟨0⟩
    let gA1 := mustApply (mustApply gA0 ⟨1⟩ .pass) ⟨2⟩ .pass
    let gA2 := mustApply (mustApply gA1 ⟨1⟩ .pass) ⟨2⟩ .pass
    -- 9b. `⟨0⟩` attacks `⟨1⟩` and `⟨2⟩`; during `Pending.declareBlockers` for `⟨1⟩`, `⟨1⟩` concedes and `⟨2⟩` declares `#[]`:
    --     attacker against `⟨2⟩` still receives `CombatEvent.remainedUnblocked`!
    let gB0 := addPermanent (addPermanent g3 bear ⟨0⟩ ⟨0⟩) hero ⟨0⟩ ⟨0⟩
    let atk1 := (gB0.battlefield.filter (·.name == bear.name))[0]!.id
    let atk2 := (gB0.battlefield.filter (·.name == hero.name))[0]!.id
    let gB1 := gB0.beginStep .beginningOfCombat
    let gB1 := mustApply (mustApply (mustApply gB1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let gB1 := mustApply gB1 ⟨0⟩ (.declareAttackers #[atk1, atk2] none #[some ⟨1⟩, some ⟨2⟩] #[])
    let gB1 := mustApply (mustApply (mustApply gB1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let gBLeft := gB1.concede ⟨1⟩
    let gBBlk2 := mustApply gBLeft ⟨2⟩ (.declareBlockers #[])
    -- 9c. `⟨1⟩` casts a spell targeting `⟨2⟩`'s Ward creature; once Ward resolves into `Pending.payWard`,
    --     `⟨1⟩` conceding counters/cleans up the spell and clears `Pending.payWard`!
    let gW0 := addPermanent (mustApply g3 ⟨0⟩ .pass) wardBearDef ⟨2⟩ ⟨2⟩
    let wId := (gW0.battlefield.filter (·.name == "Phase15 Ward Bear"))[0]!.id
    let gW0 := insertObject gW0 pingAnyDef ⟨1⟩ (.hand ⟨1⟩)
    let pH := (gW0.player ⟨1⟩).hand.back!
    let gWCast := mustApply (mustApply gW0 ⟨1⟩ (.cast pH)) ⟨1⟩ (.target (.permanent wId))
    let gWPrompt := mustApply (mustApply (mustApply gWCast ⟨1⟩ .pass) ⟨2⟩ .pass) ⟨0⟩ .pass
    let gWConcede := gWPrompt.concede ⟨1⟩
    let ok :=
      gA1.step == .declareAttackers &&
      gA1.pending == .none &&
      gA2.step == .endOfCombat &&
      gBLeft.pending == .declareBlockers &&
      gBLeft.currentBlockersPlayer == ⟨2⟩ &&
      gBBlk2.pending == .none &&
      gBBlk2.events.any (fun e =>
        match e.change with
        | .rules (.combat (.remainedUnblocked eo)) => eo.id == some atk2
        | _ => false) &&
      (match gWPrompt.pending with | .payWard p _ cost _ => (p == ⟨1⟩) && cost.soleGenericMana? == some 2 | _ => false) &&
      gWConcede.pending == .none &&
      gWConcede.stack.isEmpty
    (gA2, gBBlk2, gWConcede, ok)
  let leaveTransitionsAllOk :=
    leaveGameTransitionsOk &&
    [gSkipDeclAtk, gBlkLeftUnblocked, gWardCasterLeft].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 10. Layer-7c `chosenCreatureType` scoping (`lordPump?`) & `lastKnownBefore?` single-life LKI.
  let bannerDef15 : CardDef := {
    name := "Phase15 Banner"
    manaCost := ManaCost.empty
    types := #[.artifact]
    staticAbilities := #[.asEntersChooseCreatureType, .chosenTypeCreaturesGet 1 1]
  }
  let elfDef15 : CardDef := creature "Phase15 Elf" ManaCost.empty #["Elf"] 1 1
  let gobDef15 : CardDef := creature "Phase15 Goblin" ManaCost.empty #["Goblin"] 2 2
  let (gBanners, gSingleLifeLki, bannerAndLkiOk) :=
    let g0 := addPermanent (addPermanent afterDraw elfDef15 me me) gobDef15 me me
    let elfId := (g0.battlefield.filter (·.name == "Phase15 Elf"))[0]!.id
    let gobId := (g0.battlefield.filter (·.name == "Phase15 Goblin"))[0]!.id
    let g0 := insertObject (insertObject g0 bannerDef15 me (.hand me))
      { bannerDef15 with name := "Phase15 Banner 2" } opp (.hand opp)
    let b1H := ((g0.player me).hand.filter (fun id => (g0.object! id).name == "Phase15 Banner"))[0]!
    let b2H := ((g0.player opp).hand.filter (fun id => (g0.object! id).name == "Phase15 Banner 2"))[0]!
    let (g1, _) := g0.putOntoBattlefield b1H me (cause := some testCause)
    let g1 := mustApply g1 me (.chooseName "Elf")
    let (g2, _) := g1.putOntoBattlefield b2H me (cause := some testCause)
    let g2 := mustApply g2 me (.chooseName "Goblin")
    -- Also place a 3rd banner on `me` choosing Elf so Elf gets +2/+2 (3/3) while Goblin only gets +1/+1 (3/3, not +3/+3)!
    let g2 := insertObject g2 { bannerDef15 with name := "Phase15 Banner 3" } me (.hand me)
    let b3H := (g2.player me).hand.back!
    let (g3, _) := g2.putOntoBattlefield b3H me (cause := some testCause)
    let g3 := mustApply g3 me (.chooseName "Elf")
    let bannerOk :=
      g3.power (g3.object! elfId) == 3 &&
      g3.toughness (g3.object! elfId) == 3 &&
      g3.power (g3.object! gobId) == 3 &&
      g3.toughness (g3.object! gobId) == 3
    -- Single-life `lastKnownBefore?`: battlefield (`elfId` at 3/3) -> graveyard (`gyId` at 1/1) -> hand (`hId`).
    let (g4, gyId) := g3.move elfId (.graveyard me) none (cause := some testCause)
    let (g5, hId) := g4.move gyId (.hand me) none (cause := some testCause)
    let lkiOk :=
      g5.lastKnownPowerOf? elfId == some 3 &&
      (g4.lastKnownPowerOf? gyId).isNone &&
      g5.lastKnownPowerOf? gyId == some 1 &&
      (g5.lastKnownPowerOf? hId).isNone
    (g3, g5, bannerOk && lkiOk)
  let chosenTypeAndLkiAllOk :=
    bannerAndLkiOk &&
    [gBanners, gSingleLifeLki].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)

  -- 11. `ObjectId ⟨0⟩` parity & `EngineChange.stackEntry` deterministic replay.
  let (gZeroIdAndStack, zeroIdParityOk) :=
    let g0 := afterDraw
    let zeroId : ObjectId := ⟨0⟩
    let obj0Present := (g0.findObject? zeroId).isSome
    -- Verify `ObjectId ⟨0⟩` is never matched by `none` source triggers and IS matched only by `some ⟨0⟩`!
    let zeroMoveEv := GameEvent.moved 1
      { id := some zeroId, controller := some me, owner := me, types := #[.creature] } .battlefield (.graveyard me)
      (cause := testCause)
    let otherMoveEv := GameEvent.moved 1
      { id := some ⟨7⟩, controller := some me, owner := me, types := #[.creature] } .battlefield (.graveyard me)
      (cause := testCause)
    let triggerZeroOk :=
      zeroMoveEv.matchesTriggerPattern me (some zeroId) .thisDies &&
      !zeroMoveEv.matchesTriggerPattern me none .thisDies &&
      !otherMoveEv.matchesTriggerPattern me (some zeroId) .thisDies &&
      !otherMoveEv.matchesTriggerPattern me none .thisDies
    let c0 := g0.object! zeroId
    let otherLibId := ((g0.player me).library.filter (· != zeroId))[0]!
    let gZ1 := g0.createEffect
      (.replacement { id := { kind := .finalityCounterExile, object := some zeroId },
                      affectedPlayer := c0.owner, kind := .exileInsteadOfGraveyard (some zeroId) false } .untilEndOfTurn)
      (cause := some testCause)
    let (gZ2, movedOther) := gZ1.move otherLibId (.graveyard me) none (verb := some .mill) (cause := some testCause)
    let (gZ3, movedZero) := gZ2.move zeroId (.graveyard c0.owner) none (verb := some .mill) (cause := some testCause)
    -- `EngineChange.stackEntry` mutation & deterministic replay:
    let gSt0 := addPermanent (addPermanent gZ3 bear opp opp) hero opp opp
    let t1 := (gSt0.battlefield.filter (fun (o : GameObject) => o.name == bear.name))[0]!.id
    let t2 := (gSt0.battlefield.filter (fun (o : GameObject) => o.name == hero.name))[0]!.id
    let gSt0 := insertObject gSt0 pingAnyDef me (.hand me)
    let pId := (gSt0.player me).hand.back!
    let gSt1 := mustApply (mustApply gSt0 me (.cast pId)) me (.target (.permanent t1))
    let stObjId := gSt1.stack.back!.objectId
    let gSt2 := (gSt1.setStackEntryTargets stObjId #[Target.permanent t2] #[]).markTargetsAnnounced stObjId true
    let ok :=
      obj0Present &&
      triggerZeroOk &&
      (gZ3.object! movedOther).zone == Zone.graveyard me &&
      (gZ3.object! movedZero).zone == Zone.exile &&
      (gSt2.stackEntry? stObjId).map (fun (se : StackEntry) => se.targets) == some #[Target.permanent t2]
    (gSt2, ok)
  let zeroParityAndStackAllOk :=
    zeroIdParityOk &&
    Game.replayEvents gZeroIdAndStack.events == gZeroIdAndStack &&
    allRulesEventsClassified gZeroIdAndStack

  -- ==========================================================================
  -- 12. `wasPermanentDestroyed` / `destroyPermanentsLoop` tally (CR 701.8a-c,
  --     CR 800.4c non-destroy exile exclusion, WotC Ruling 80 `ZoneVerb.destroy`
  --     preservation across graveyard-redirect replacements)
  -- ==========================================================================
  let destroyedTallyAllOk : Bool := Id.run do
    let threeCfg12 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 12
      startingPlayer := some 0
    }
    let g0 :=
      match Start.start threeCfg12 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    let indRelicDef : CardDef :=
      { name := "Phase15 Indestructible Relic", manaCost := ManaCost.empty,
        types := #[.artifact], keywords := #[Keyword.indestructible] }
    let shdRelicDef : CardDef :=
      { name := "Phase15 Shield Relic", manaCost := ManaCost.empty, types := #[.artifact] }
    let finRelicDef : CardDef :=
      { name := "Phase15 Finality Relic", manaCost := ManaCost.empty, types := #[.artifact] }
    let g0 := addPermanent g0 bear ⟨1⟩ ⟨1⟩
    let ctrlSrcId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let g0 := addPermanent g0 hero ⟨2⟩ ⟨2⟩
    let stolenId := (g0.battlefield.filter (·.name == hero.name))[0]!.id
    let g0 := g0.changeControl (g0.object! stolenId) ⟨1⟩ (untilSourceLeaves := some ctrlSrcId) (cause := some testCause)
    let g0 := g0.concede ⟨2⟩
    let g0 := addPermanent g0 indRelicDef ⟨1⟩ ⟨1⟩
    let indId := (g0.battlefield.filter (·.name == "Phase15 Indestructible Relic"))[0]!.id
    let g0 := addPermanent g0 shdRelicDef ⟨1⟩ ⟨1⟩
    let shdId := (g0.battlefield.filter (·.name == "Phase15 Shield Relic"))[0]!.id
    let g0 := g0.recordPutCounters shdId .shield 1 (some ⟨1⟩) (cause := some testCause)
    let g0 := addPermanent g0 finRelicDef ⟨1⟩ ⟨1⟩
    let finId := (g0.battlefield.filter (·.name == "Phase15 Finality Relic"))[0]!.id
    let g0 := g0.recordPutCounters finId .finality 1 (some ⟨1⟩) (cause := some testCause)
    let cands := #[ctrlSrcId, stolenId, indId, shdId, finId]
    let gOut :=
      g0.withContinuationFrame fun g =>
        g.withBatch (some testCause) fun g =>
          g.destroyPermanentsLoop cands (allCandidates := cands) (countNote := true)
            (obGainLifeFor := some ⟨0⟩) (preBattlefield := some g.battlefield) (cause := some testCause)
    gOut.wasPermanentDestroyed ctrlSrcId &&
    !gOut.wasPermanentDestroyed stolenId &&
    !gOut.wasPermanentDestroyed indId &&
    !gOut.wasPermanentDestroyed shdId &&
    gOut.wasPermanentDestroyed finId &&
    (gOut.player ⟨0⟩).life == 22 &&
    !(gOut.findObject? stolenId).any (·.isOnBattlefield) &&
    (gOut.findObject? indId).any (·.isOnBattlefield) &&
    (gOut.findObject? shdId).any (fun o => o.isOnBattlefield && o.status.shield == 0) &&
    gOut.objects.any (fun o => o.name == "Phase15 Finality Relic" && o.zone == .exile) &&
    Game.replayEvents gOut.events == gOut &&
    allRulesEventsClassified gOut

  let mustHold15 (label : String) (ok : Bool) : Bool :=
    if ok then true else panic! s!"Phase 15 guard failed: {label}"

  [ mustHold15 "seqAndMayThenOk" seqAndMayThenOk,
    mustHold15 "standaloneManaAndPrioOk" standaloneManaAndPrioOk,
    mustHold15 "twAndPaidAllOk" twAndPaidAllOk,
    mustHold15 "triggerOrderingAllOk" triggerOrderingAllOk,
    mustHold15 "wardAndNestedAllOk" wardAndNestedAllOk,
    mustHold15 "lkiAndMultiSbaAllOk" lkiAndMultiSbaAllOk,
    mustHold15 "combatAlignmentAllOk" combatAlignmentAllOk,
    mustHold15 "cleanupAllOk" cleanupAllOk,
    mustHold15 "leaveTransitionsAllOk" leaveTransitionsAllOk,
    mustHold15 "chosenTypeAndLkiAllOk" chosenTypeAndLkiAllOk,
    mustHold15 "zeroParityAndStackAllOk" zeroParityAndStackAllOk,
    mustHold15 "destroyedTallyAllOk" destroyedTallyAllOk ].all id

end Mtg.Engine.EventTests
