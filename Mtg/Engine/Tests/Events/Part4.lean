import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase21EventAlignment

def opp21 : PlayerId := ⟨1⟩

def mustHold21 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 21 guard failed: {label}"

def mkThreePlayer21 (seed : UInt64 := 21) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 24).advanceStep
  | .error e => panic! e

def mkTwoHeadedGiant21 (seed : UInt64 := 221) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 30).advanceStep
  | .error e => panic! e

-- 1. Concede `.restorePending` ordering after post-leave `checkSBA`, multi-teammate departure
--    pause chaining (`concedePlayersLoop`), and `flushUnlessPays` outer continuation preservation.
#guard
  let headWolf21 : CardDef := {
    bear with
    name := "Phase21 Head Wolf"
    staticAbilities := #[.exileOppDeathCreateWolf]
  }
  -- 1a. 3-player game: `⟨0⟩` is paused on `.scry ⟨0⟩ 1` while `⟨1⟩` concedes; `⟨1⟩` held temporary
  --     control of `⟨2⟩`'s lethal-damaged creature with `.finality` + `headWolf21` on `⟨0⟩`, so
  --     post-leave `checkSBA` pauses on `.chooseReplacement ⟨2⟩` BEFORE `.scry ⟨0⟩ 1` is restored!
  let g3p0 : Game :=
    let g := addPermanent (addPermanent mkThreePlayer21 headWolf21 ⟨0⟩ ⟨0⟩) bear ⟨2⟩ ⟨2⟩
    let victimId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.recordPutCounters victimId .finality 1 (some ⟨2⟩) (cause := some testCause)
    let g := setMarkedDamage g victimId 2
    let g := g.createEffect (.layered (.objects #[victimId]) (.control ⟨1⟩) .untilEndOfTurn) (cause := some testCause)
    g.change (.pending (.scry ⟨0⟩ 1))
  let victim3pId := (g3p0.battlefield.filter (·.name == bear.name))[0]!.id
  let fin3pId : ReplacementId := { kind := .finalityCounterExile, object := some victim3pId }
  let g3pConcede : Game := mustApply g3p0 ⟨1⟩ .concede
  let sbaPausedBeforeRestore : Bool :=
    match g3pConcede.pending with
    | .chooseReplacement p cs => p == ⟨2⟩ && cs.contains fin3pId
    | _ => false
  let g3pAfterSba : Game := mustApply g3pConcede ⟨2⟩ (.chooseReplacement fin3pId)
  let restoreAfterSbaOk : Bool :=
    sbaPausedBeforeRestore &&
    (g3pConcede.player ⟨1⟩).leftTheGame &&
    g3pAfterSba.pending == .scry ⟨0⟩ 1

  -- 1b. 2HG (`mkTwoHeadedGiant21`): Team A (`⟨0⟩, ⟨1⟩`) concedes -> both teammates leave;
  --     and in a 4-seat game with paired teammates (`⟨0⟩, ⟨1⟩`) vs `⟨2⟩` vs `⟨3⟩`, post-leave `checkSBA`
  --     pauses across BOTH returned lethal creatures before `.scry ⟨2⟩ 1` is restored!
  let g2hCon0 : Game := mkTwoHeadedGiant21
  let g2hCon1 : Game := mustApply g2hCon0 ⟨0⟩ .concede
  let teamBothLeftOk : Bool :=
    (g2hCon1.player ⟨0⟩).lost &&
    (g2hCon1.player ⟨1⟩).lost &&
    g2hCon1.over
  let g3pLoop0 : Game :=
    let cfg : StartConfig := {
      seats := #[
        { name := "P0", deck := testRedDeck, teammate := some ⟨1⟩ },
        { name := "P1", deck := testGreenDeck, teammate := some ⟨0⟩ },
        { name := "P2", deck := testRedDeck },
        { name := "P3", deck := testGreenDeck }
      ]
      format := .constructed
      seed := 222
      startingPlayer := some 0
    }
    let base :=
      match Start.start cfg with
      | .ok g => (keepOpeningHands g 30).advanceStep
      | .error e => panic! e
    let g := addPermanent (addPermanent (addPermanent base headWolf21 ⟨3⟩ ⟨3⟩) bear ⟨2⟩ ⟨2⟩) hero ⟨2⟩ ⟨2⟩
    let vA := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let vB := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let g := (g.recordPutCounters vA .finality 1 (some ⟨2⟩) (cause := some testCause)).recordPutCounters
      vB .finality 1 (some ⟨2⟩) (cause := some testCause)
    let g := setMarkedDamage (setMarkedDamage g vA 2) vB 2
    let g := (g.createEffect (.layered (.objects #[vA]) (.control ⟨0⟩) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[vB]) (.control ⟨1⟩) .untilEndOfTurn) (cause := some testCause)
    g.change (.pending (.scry ⟨2⟩ 1))
  let vLoopA := (g3pLoop0.battlefield.filter (·.name == bear.name))[0]!.id
  let vLoopB := (g3pLoop0.battlefield.filter (·.name == hero.name))[0]!.id
  let finLoopA : ReplacementId := { kind := .finalityCounterExile, object := some vLoopA }
  let finLoopB : ReplacementId := { kind := .finalityCounterExile, object := some vLoopB }
  let gLoop1 : Game := mustApply g3pLoop0 ⟨0⟩ .concede
  let gLoop2 : Game := mustApply gLoop1 ⟨2⟩ (.chooseReplacement finLoopA)
  let gLoop3 : Game := mustApply gLoop2 ⟨2⟩ (.chooseReplacement finLoopB)
  let multiDepartChainOk : Bool :=
    teamBothLeftOk &&
    (gLoop1.player ⟨0⟩).leftTheGame &&
    (gLoop1.player ⟨1⟩).leftTheGame &&
    (match gLoop1.pending with | .chooseReplacement p cs => p == ⟨2⟩ && cs.contains finLoopA | _ => false) &&
    (match gLoop2.pending with | .chooseReplacement p cs => p == ⟨2⟩ && cs.contains finLoopB | _ => false) &&
    gLoop3.pending == .scry ⟨2⟩ 1

  -- 1c. `flushUnlessPays` preserves outer `pendingReplacement` (`PendingReplacement.restorePending`).
  let gFlush0 : Game :=
    ((afterDraw.change (.pushContinuationFrame {})).changes #[
      .continuation (.unlessPaysDue true),
      .continuation (.unlessPaysController me),
      .continuation (.unlessPaysInstead (some (.draw 1))),
      .continuation (.pendingReplacement (some (.restorePending (.scry me 1) false)))
    ])
  let handBeforeFlush := (gFlush0.player me).hand.size
  let gFlush1 : Game := gFlush0.flushUnlessPays
  let flushPreservesContOk : Bool :=
    (gFlush1.player me).hand.size == handBeforeFlush + 1 &&
    gFlush1.pending == .scry me 1

  mustHold21 "1a.restoreAfterSbaOk" restoreAfterSbaOk &&
  mustHold21 "1b.multiDepartChainOk" multiDepartChainOk &&
  mustHold21 "1c.flushPreservesContOk" flushPreservesContOk &&
  mustHold21 "1.replay" ([g3pConcede, g3pAfterSba, g2hCon1, gLoop1, gLoop2, gLoop3, gFlush1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. CR 702.26g indirectly phased-out attachment unattach & non-self phase-in, plus
--    CR 701.3a–b / 301.5c attachment legality and no-op re-attach timestamp preservation (CR 613.7e).
#guard
  let eqDef21 : CardDef := {
    name := "Phase21 Blade"
    types := #[.artifact]
    subtypes := #["Equipment"]
    manaCost := ManaCost.ofColor .white
  }
  let proWhiteBear21 : CardDef := {
    bear with
    name := "Phase21 ProWhite Bear"
    protectionFromColors := #[.white]
  }
  let relic21 : CardDef := { name := "Phase21 Noncreature Relic", types := #[.artifact] }
  let gPh0 : Game :=
    addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear me me) eqDef21 me me) proWhiteBear21 me me) relic21 me me
  let hostId := (gPh0.battlefield.filter (·.name == bear.name))[0]!.id
  let eqId := (gPh0.battlefield.filter (·.name == "Phase21 Blade"))[0]!.id
  let proId := (gPh0.battlefield.filter (·.name == "Phase21 ProWhite Bear"))[0]!.id
  let relicId := (gPh0.battlefield.filter (·.name == "Phase21 Noncreature Relic"))[0]!.id
  -- 2a. Attach `eqId` to `hostId`; check no-op re-attach preserves `PermanentEvent.attached` count and timestamp!
  let gAtt1 : Game := gPh0.attachSourceTo (gPh0.object! eqId) (gPh0.object! hostId)
  let attCount1 := gAtt1.events.filter (fun e => match e.change with | .rules (.permanent (.attached ..)) => true | _ => false) |>.size
  let eqTs1 := gAtt1.objectEntryTimestamp (gAtt1.object! eqId)
  let gAttNoop : Game := gAtt1.attachSourceTo (gAtt1.object! eqId) (gAtt1.object! hostId)
  let attCount2 := gAttNoop.events.filter (fun e => match e.change with | .rules (.permanent (.attached ..)) => true | _ => false) |>.size
  -- Check `canAttachEquipmentTo` rejects noncreature, protection, self, and creature-Equipment (CR 301.5c):
  let gAnimEq : Game := gAtt1.createEffect (.additionalCreature eqId (untilEot := true)) (cause := some testCause)
  let attachLegalityOk : Bool :=
    attCount1 == 1 && attCount2 == 1 &&
    gAttNoop.objectEntryTimestamp (gAttNoop.object! eqId) == eqTs1 &&
    !gPh0.canAttachEquipmentTo (gPh0.object! eqId) (gPh0.object! relicId) &&
    !gPh0.canAttachEquipmentTo (gPh0.object! eqId) (gPh0.object! proId) &&
    !gAnimEq.canAttachEquipmentTo (gAnimEq.object! eqId) (gAnimEq.object! hostId)
  -- 2b. Phase out `oppHostId` (with `eqId` attached) -> `eqId` phases out indirectly (`phasedWith == some oppHostId`).
  --     `phaseInControlled me` does NOT phase `eqId` in while `oppHostId` is still phased out on `.battlefield` (CR 702.26g);
  --     once `oppHostId` leaves `.battlefield` (exiled), `eqId` unattaches (`attachedTo == none`), stays phased out
  --     immediately (`gHostExiled`), and phases in directly on `phaseInControlled me` (CR 702.26h)!
  let gPhOpp0 : Game := addPermanent gAtt1 bear opp21 opp21
  let oppHostId := (gPhOpp0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp21))[0]!.id
  let gAttOpp : Game := gPhOpp0.attachSourceTo (gPhOpp0.object! eqId) (gPhOpp0.object! oppHostId)
  let gPhased : Game := gAttOpp.phaseOut (gAttOpp.object! oppHostId) (cause := some testCause)
  let gTrySelfIn : Game := gPhased.phaseInControlled me
  let (gHostExiled, _) := gPhased.move oppHostId .exile none (cause := some testCause)
  let gEqAfterIn : Game := gHostExiled.phaseInControlled me
  let indirectPhaseOk : Bool :=
    (gPhased.object! eqId).status.phasedOut &&
    (gPhased.object! eqId).status.phasedWith == some oppHostId &&
    (gTrySelfIn.object! eqId).status.phasedOut &&
    (gHostExiled.object! eqId).attachedTo == none &&
    (gHostExiled.object! eqId).status.phasedOut &&
    !(gEqAfterIn.object! eqId).status.phasedOut &&
    (gEqAfterIn.object! eqId).status.phasedWith.isNone &&
    (gEqAfterIn.object! eqId).attachedTo == none

  mustHold21 "2a.attachLegalityOk" attachLegalityOk &&
  mustHold21 "2b.indirectPhaseOk" indirectPhaseOk &&
  mustHold21 "2.replay" ([gAtt1, gAttNoop, gAnimEq, gAttOpp, gPhased, gTrySelfIn, gHostExiled, gEqAfterIn].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. CR 608.2b target revalidation (`.venserPerm`, `applyDestroy` `.forAmass`, `applyExile` `.copyAndHost`),
--    `.eaglesBirds` departed-player guard, and deferred post-replacement logs (`putCountersDeferredLog`).
#guard
  -- 3a. Target revalidation: `opp21`'s creature targeted by `.venserPerm` and `.forAmass` gains hexproof before resolution -> fizzles!
  let gVal0 : Game := addPermanent afterDraw bear opp21 opp21
  let oppBearId := (gVal0.battlefield.filter (·.name == bear.name))[0]!.id
  let gHex : Game := gVal0.createEffect (.keywordsUntilEot oppBearId Keyword.hexproof) (cause := some testCause)
  let gVenserFizzle : Game := gHex.applyFrc me default .venserPerm #[Target.permanent oppBearId] none
  let gAmassFizzle : Game := gHex.applyUnified me { resolution := .destroy .target .forAmass, targeting := .of .creature } #[Target.permanent oppBearId]
  let targetRevalOk : Bool :=
    (gVenserFizzle.permanentsOf me).isEmpty &&
    (gAmassFizzle.object! oppBearId).isOnBattlefield &&
    !gAmassFizzle.destroyedForAmassThisWay
  -- 3b. `.eaglesBirds` in 3-player where `⟨2⟩` has left the game does NOT create tokens for departed `⟨2⟩`!
  let gEagles0 : Game := mustApply mkThreePlayer21 ⟨2⟩ .concede
  let gEaglesLive : Game := gEagles0.resolveDelayedTrigger ⟨0⟩ (.eaglesBirds 2) testCause
  let gEaglesDeparted : Game := gEaglesLive.resolveDelayedTrigger ⟨2⟩ (.eaglesBirds 2) testCause
  let eaglesDepartedGuardOk : Bool :=
    (gEaglesDeparted.permanentsOf ⟨0⟩).size == 2 &&
    (gEaglesDeparted.permanentsOf ⟨2⟩).isEmpty
  -- 3c. `putCountersDeferredLog` logs modified post-replacement count (1 -> 2 under `modifyCountersPut`).
  let gLog0 : Game := addPermanent afterDraw bear me me
  let lbId := (gLog0.battlefield.filter (·.name == bear.name))[0]!.id
  let idDblCtr : ReplacementId := { kind := .multiplyCountersPut, object := some lbId }
  let gLog1 : Game := gLog0.createEffect (.replacement {
    id := idDblCtr, source := some lbId, controller := some me,
    affectedPlayer := me, kind := .modifyCountersPut (some lbId) (some .hone) (add := 0) (mult := 2)
  }) (cause := some testCause)
  let gLog2 : Game := gLog1.putCountersDeferredLog lbId .hone 1 (some me) .getsCount (cause := some testCause)
  let deferredLogOk : Bool :=
    (gLog2.object! lbId).status.hone == 2 &&
    gLog2.log.any (·.contains "gets 2 hone counter(s)") &&
    !gLog2.log.any (·.contains "gets 1 hone counter(s)")

  mustHold21 "3a.targetRevalOk" targetRevalOk &&
  mustHold21 "3b.eaglesDepartedGuardOk" eaglesDepartedGuardOk &&
  mustHold21 "3c.deferredLogOk" deferredLogOk &&
  mustHold21 "3.replay" ([gHex, gVenserFizzle, gAmassFizzle, gEagles0, gEaglesLive, gEaglesDeparted, gLog2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 101.2 `cantCastSpellsThisTurn`, flash/`canCast` parity (`ignoreTiming`, `castOnlyIfGraveyardAtLeast`),
--    CR 601.2b,f,h caster-identity Thalia & `announceAdditionalCost` reduction order, *Countersculpt* behold
--    deferred to 601.2h, Morph / Impending `applyKickerToProposed` (no Thalia tax, `anyMana`), and CR 602.2b / 733.1 non-cancellation.
#guard
  -- 4a. CR 101.2 `cantCastSpellsThisTurn` blocks `canCast`, `castSpell`, `castFreeCopy`, and `castExiledAsAbilityResolves`.
  let freeShock21 : CardDef := { shock with name := "Phase21 Free Shock", manaCost := ManaCost.empty }
  let gSilence0 : Game :=
    let g := insertObject (insertObject afterDraw freeShock21 me (.hand me)) freeShock21 me .exile
    g.createEffect (.playerRule me .cantCastSpells .untilEndOfTurn) (cause := some testCause)
  let hShock := (gSilence0.player me).hand.back!
  let exShock := (gSilence0.objects.filter (fun o => o.name == "Phase21 Free Shock" && o.zone == .exile))[0]!.id
  let gSilenceEx : Game := gSilence0.change (.pending (.mayCastExiledElseDamage me exShock 2 none))
  let gSilenceCopy : Game := gSilence0.change (.pending (.fraChoice me (.castCopiesFree #[exShock] 1 1)))
  let silenceBlocksAllOk : Bool :=
    !gSilence0.canCast me (gSilence0.object! hShock) &&
    !(gSilence0.castSpell me hShock).isOk &&
    !(gSilenceEx.apply me (.cast exShock)).isOk &&
    !(gSilenceCopy.apply me (.cast exShock)).isOk

  -- 4b. `canCast` parity: `PlayPermission.ignoreTiming` allows sorcery on opponent's turn; `castOnlyIfGraveyardAtLeast` excludes self in graveyard!
  let sorc21 : CardDef := { name := "Phase21 Sorcery", manaCost := ManaCost.empty, types := #[.sorcery], spellEffect := some (Effect.draw 1) }
  let gyThresholdSorc21 : CardDef := {
    sorc21 with
    name := "Phase21 Threshold Sorc"
    castOnlyIfGraveyardAtLeast := some 2
  }
  let gOppTurn0 : Game :=
    let g := ((afterDraw.record (GameEvent.turnBegan (afterDraw.turnNumber + 1) opp21)).record
      (GameEvent.stepBegan (afterDraw.turnNumber + 1) .precombatMain opp21)).change (.priority me)
    let g := insertObject g sorc21 me .exile
    let exId := (g.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
    g.createEffect (.playPermission exId { player := me, withoutManaCost := true, ignoreTiming := true }
      (d := .untilEndOfTurn)) (cause := some testCause)
  let exSorcId := (gOppTurn0.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
  let gGyThresh0 : Game :=
    let g := insertObject (insertObject afterDraw gyThresholdSorc21 me (.graveyard me)) bear me (.graveyard me)
    let gyId := (g.objects.filter (·.name == "Phase21 Threshold Sorc"))[0]!.id
    g.createEffect (.playPermission gyId { player := me, withoutManaCost := true } (d := .untilEndOfTurn))
      (cause := some testCause)
  let gyThreshId := (gGyThresh0.objects.filter (·.name == "Phase21 Threshold Sorc"))[0]!.id
  let canCastParityOk : Bool :=
    gOppTurn0.canCast me (gOppTurn0.object! exSorcId) &&
    !gGyThresh0.canCast me (gGyThresh0.object! gyThreshId) &&
    !(gGyThresh0.castSpell me gyThreshId).isOk

  -- 4c. Non-owner caster Thalia tax, `announceAdditionalCost` reduction order, and *Countersculpt* behold deferred to 601.2h!
  let thalia21 : CardDef := { bear with name := "Phase21 Thalia", staticAbilities := #[.fra .opponentsNoncreatureSpellsCostMore] }
  let bilbo21 : CardDef := { bear with name := "Phase21 Bilbo", costReductionNotFromHand := 1 }
  let beholdInst21 : CardDef := {
    name := "Phase21 Behold Instant"
    manaCost := { symbols := #[.colored .blue, .colored .blue] }
    types := #[.instant]
    additionalCostBeholdOrPay := some (.jace, 1)
  }
  let jaceCard21 : CardDef := {
    name := "Phase21 Hand Jace"
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 3
  }
  -- Non-owner caster Thalia: `opp21`'s exiled 0-cost noncreature spell cast by `me` under Thalia costs `{1}`!
  let gThaliaEx0 : Game :=
    let g := addPermanent (insertObject afterDraw sorc21 opp21 .exile) thalia21 opp21 opp21
    let exId := (g.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
    g.createEffect (.playPermission exId { player := me, withoutManaCost := true } (d := .untilEndOfTurn))
      (cause := some testCause)
  let oppExSorcId := (gThaliaEx0.objects.filter (fun o => o.name == "Phase21 Sorcery" && o.zone == .exile))[0]!.id
  let gThaliaProp : Game := mustApply gThaliaEx0 me (.cast oppExSorcId)
  let thaliaNonOwnerTaxOk : Bool := gThaliaProp.proposedSpell.map (·.cost) == some (ManaCost.ofGeneric 1)
  -- `announceAdditionalCost true` from exile with `costReductionNotFromHand := 1`: `{U}{U} + {1} - {1} == {U}{U}`!
  let gBeholdEx0 : Game :=
    let g := addPermanent (insertObject (insertObject afterDraw beholdInst21 me .exile) jaceCard21 me (.hand me)) bilbo21 me me
    let exId := (g.objects.filter (fun o => o.name == "Phase21 Behold Instant" && o.zone == .exile))[0]!.id
    (g.createEffect (.playPermission exId { player := me } (d := .untilEndOfTurn))
      (cause := some testCause)).addMana me (.colored .blue) 2
  let exBehId := (gBeholdEx0.objects.filter (fun o => o.name == "Phase21 Behold Instant" && o.zone == .exile))[0]!.id
  let jaceHandId := (gBeholdEx0.objects.filter (·.name == "Phase21 Hand Jace"))[0]!.id
  let gBehPayGen : Game := mustApply (mustApply gBeholdEx0 me (.cast exBehId)) me (.chooseAdditionalCost true)
  let addCostReducedOk : Bool :=
    gBehPayGen.proposedSpell.map (·.cost) == some ({ symbols := #[.colored .blue, .colored .blue] } : ManaCost)
  -- Choosing behold (`chooseAdditionalCost false`) does NOT reveal at 601.2b; reveals at 601.2h (`pay`), and reverses if Jace leaves hand before `pay`!
  let gBehChoose : Game := mustApply (mustApply gBeholdEx0 me (.cast exBehId)) me (.chooseAdditionalCost false)
  let notRevealedAt6012b : Bool :=
    !gBehChoose.events.any (fun e => match e.change with | .rules (.player (.revealed ..)) => true | _ => false)
  let gBehPaid : Game := mustApply gBehChoose me .pay
  let revealedAt6012h : Bool :=
    gBehPaid.events.any (fun e => match e.change with | .rules (.player (.revealed p ids)) => p == me && ids == #[jaceHandId] | _ => false)
  let (gBehLostJace, _) := gBehChoose.move jaceHandId .exile none (cause := some testCause)
  let gBehReversed : Game := mustApply gBehLostJace me .pay
  let beholdTimingOk : Bool :=
    thaliaNonOwnerTaxOk && addCostReducedOk && notRevealedAt6012b && revealedAt6012h &&
    gBehReversed.stack.isEmpty && gBehReversed.proposedSpell.isNone

  -- 4d. Morph face-down cast under Thalia costs `{3}` (not `{4}`), and colored Impending under `PlayPermission.anyMana` becomes generic `{2}`!
  let morphNoncrDef21 : CardDef := {
    name := "Phase21 Morph Enchantment"
    manaCost := { symbols := #[.colored .blue] }
    types := #[.enchantment]
    morph := some (ManaCost.ofGeneric 2)
  }
  let impColoredDef21 : CardDef := {
    bear with
    name := "Phase21 Colored Impending"
    impending := some (2, { symbols := #[.colored .blue, .colored .blue] })
  }
  let gMorphThalia0 : Game :=
    let g := addPermanent (insertObject (insertObject afterDraw morphNoncrDef21 me .exile) impColoredDef21 me .exile) thalia21 opp21 opp21
    let exM := (g.objects.filter (fun o => o.name == "Phase21 Morph Enchantment" && o.zone == .exile))[0]!.id
    let exI := (g.objects.filter (fun o => o.name == "Phase21 Colored Impending" && o.zone == .exile))[0]!.id
    (g.createEffect (.playPermission exM { player := me, anyMana := true } (d := .untilEndOfTurn))
      (cause := some testCause)).createEffect (.playPermission exI { player := me, anyMana := true } (d := .untilEndOfTurn))
      (cause := some testCause)
  let exMorphId := (gMorphThalia0.objects.filter (fun o => o.name == "Phase21 Morph Enchantment" && o.zone == .exile))[0]!.id
  let exImpAnyId := (gMorphThalia0.objects.filter (fun o => o.name == "Phase21 Colored Impending" && o.zone == .exile))[0]!.id
  let gMorphProp : Game := mustApply (mustApply gMorphThalia0 me (.cast exMorphId)) me (.announceKicker true)
  let gImpAnyProp : Game := mustApply (mustApply gMorphThalia0 me (.cast exImpAnyId)) me (.announceKicker true)
  let morphCostOk : Bool :=
    gMorphProp.proposedSpell.map (·.cost) == some (ManaCost.ofGeneric 3) &&
    gImpAnyProp.proposedSpell.map (·.cost) == some (ManaCost.ofGeneric 2)

  -- 4e. CR 602.2b / 733.1 partial-payment non-cancellation: once `{1}` mana is paid on `{1}, Sacrifice another creature:`, `.decline` is blocked while a creature exists!
  let sacAbDef21 : CardDef := {
    name := "Phase21 Altar"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 1, sacrificeAnotherCreature := true }
      effect := Effect.draw 1
    }]
  }
  let gSacAb0 : Game := (addPermanent (addPermanent afterDraw sacAbDef21 me me) bear me me).addMana me .colorless 1
  let altarId := (gSacAb0.battlefield.filter (·.name == "Phase21 Altar"))[0]!.id
  let sacBearId := (gSacAb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSacAbPaidMana : Game := mustApply (mustApply gSacAb0 me (.activate altarId 0)) me .pay
  let declineBlockedAfterMana : Bool := !(gSacAbPaidMana.apply me .decline).isOk
  let (gSacAbNoCreature, _) := gSacAbPaidMana.move sacBearId .exile none (cause := some testCause)
  let gSacAbRev : Game := mustApply gSacAbNoCreature me .decline
  let partialPaymentNonCancelOk : Bool :=
    declineBlockedAfterMana &&
    gSacAbRev.stack.isEmpty &&
    gSacAbRev.proposedSpell.isNone &&
    (gSacAbRev.player me).manaPool.total == 1

  mustHold21 "4a.silenceBlocksAllOk" silenceBlocksAllOk &&
  mustHold21 "4b.canCastParityOk" canCastParityOk &&
  mustHold21 "4c.beholdTimingOk" beholdTimingOk &&
  mustHold21 "4d.morphCostOk" morphCostOk &&
  mustHold21 "4e.partialPaymentNonCancelOk" partialPaymentNonCancelOk &&
  mustHold21 "4.replay" ([gSilence0, gOppTurn0, gGyThresh0, gThaliaProp, gBehPayGen, gBehPaid, gBehReversed, gMorphProp, gImpAnyProp, gSacAbPaidMana, gSacAbRev].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. Modal `chooseBothIfTeamwork` gating, CR 110.1 / 115.1c / 115.10a `.youTargetSomething`
--    player/permanent filter, CR 707.10 vs CR 707.12 copy cast semantics, and Impending / face-down Morph stack copies.
#guard
  -- 5a. Modal `chooseBothIfTeamwork`: only chooses both modes when ALL modes have legal targets!
  let twModalDef21 : CardDef := {
    name := "Phase21 Teamwork Command"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    teamwork := some 2
    chooseBothIfTeamwork := true
    spellModes := #[
      Effect.canonicalDestroy .creature,
      Effect.canonicalDestroy .artifact
    ]
  }
  let relicTw21 : CardDef := { name := "Phase21 Target Artifact", types := #[.artifact] }
  let gTwOne0 : Game := insertObject (addPermanent afterDraw bear me me) twModalDef21 me (.hand me)
  let twBearId := (gTwOne0.battlefield.filter (·.name == bear.name))[0]!.id
  let twCard1 := (gTwOne0.player me).hand.back!
  let gTwOne1 : Game :=
    mustApply (mustApply (mustApply (mustApply gTwOne0 me (.cast twCard1)) me (.chooseMode 0)) me (.announceTeamwork true)) me (.choosePermanents #[twBearId])
  let gTwBoth0 : Game := addPermanent gTwOne0 relicTw21 opp21 opp21
  let gTwBoth1 : Game :=
    mustApply (mustApply (mustApply (mustApply gTwBoth0 me (.cast twCard1)) me (.chooseMode 0)) me (.announceTeamwork true)) me (.choosePermanents #[twBearId])
  let teamworkModalOk : Bool :=
    gTwOne1.chosenModesOf (gTwOne1.object! gTwOne1.proposedSpell.get!.spellId) == #[0] &&
    gTwBoth1.chosenModesOf (gTwBoth1.object! gTwBoth1.proposedSpell.get!.spellId) == #[0, 1]

  -- 5b. CR 110.1 / 115.1c / 115.10a `.youTargetSomething` fires on `.player` / `.permanent`, NOT `.card` (graveyard or stack)!
  let youTargetTrig21 : TriggeredAbility :=
    .triggered .fromEffect (Effect.ofTrigger (.watch .youTargetDrawOnce))
  let watcher21 : CardDef := {
    name := "Phase21 Target Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[youTargetTrig21]
  }
  let targeterArt21 : CardDef := {
    name := "Phase21 Targeter"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := {}, effect := Effect.returnCreatureFromGyThenAmass 0 },
      { cost := {}, effect := Effect.counterSpell },
      { cost := {}, effect := shock.spellEffect.get! }
    ]
  }
  let dummySorc21 : CardDef := {
    name := "Phase21 Stack Dummy"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some (Effect.draw 1)
  }
  let gYtBase : Game :=
    insertObject (insertObject (addPermanent (addPermanent (addPermanent afterDraw watcher21 me me) targeterArt21 me me) bear opp21 opp21) bear me (.graveyard me)) dummySorc21 me (.hand me)
  let targeterId := (gYtBase.battlefield.filter (·.name == "Phase21 Targeter"))[0]!.id
  let gyBearId := (gYtBase.objects.filter (fun o => o.name == bear.name && o.zone == .graveyard me))[0]!.id
  let dummySpId := (gYtBase.objects.filter (fun o => o.name == "Phase21 Stack Dummy" && o.zone == .hand me))[0]!.id
  let gYtWithSpell : Game := mustApply gYtBase me (.cast dummySpId)
  let stackSpellTargetId := gYtWithSpell.stack[0]!.objectId
  let gYtGy : Game := mustApply (mustApply gYtWithSpell me (.activate targeterId 0)) me (.target (.card gyBearId))
  let gyDidNotTrigger : Bool := gYtGy.stack.size == 2
  let gYtStack : Game := mustApply (mustApply gYtGy me (.activate targeterId 1)) me (.target (.card stackSpellTargetId))
  let stackSpellDidNotTrigger : Bool := gYtStack.stack.size == 3
  let gYtPing : Game := mustApply (mustApply gYtStack me (.activate targeterId 2)) me (.target (.player opp21))
  let playerDidTrigger : Bool := gYtPing.stack.size == 5
  let youTargetCheckOk : Bool := gyDidNotTrigger && stackSpellDidNotTrigger && playerDidTrigger

  -- 5c. CR 707.10 stack copies (`wasCast == false`, Impending & face-down Morph stack copies) vs CR 707.12 `createPreparedCopy` (`isCopy == true`, cast)!
  let impCopyDef21 : CardDef := { bear with name := "Phase21 Impending Copy", impending := some (2, ManaCost.empty) }
  let gImp0 : Game := insertObject afterDraw impCopyDef21 me (.hand me)
  let impCardId := (gImp0.player me).hand.back!
  let gImpStack : Game := mustApply (mustApply gImp0 me (.cast impCardId)) me (.announceKicker true)
  let origImpStackId := gImpStack.stack.back!.objectId
  let gImpCopied : Game := gImpStack.copyStackSpell (gImpStack.object! origImpStackId) me
  let copyImpStackId := gImpCopied.stack.back!.objectId
  let gImpCopyRes : Game := gImpCopied.resolveTop
  let copyImpPerm := (gImpCopyRes.battlefield.filter (·.name == "Phase21 Impending Copy"))[0]!
  let morphCopyDef21 : CardDef := { bear with name := "Phase21 Morph Copy", power := some 5, toughness := some 5, morph := some (ManaCost.ofGeneric 2) }
  let gMph0 : Game := (insertObject afterDraw morphCopyDef21 me (.hand me)).addMana me .colorless 3
  let mphCardId := (gMph0.player me).hand.back!
  let gMphStack : Game := mustApply (mustApply (mustApply gMph0 me (.cast mphCardId)) me (.announceKicker true)) me .pay
  let gMphCopied : Game := gMphStack.copyStackSpell (gMphStack.object! gMphStack.stack.back!.objectId) me
  let mphCopyStackObj := gMphCopied.object! gMphCopied.stack.back!.objectId
  let gMphCopyRes : Game := gMphCopied.resolveTop
  let mphCopyPerm := (gMphCopyRes.battlefield.filter (·.printed.isToken))[0]!
  -- CR 707.12 `createPreparedCopy`: `isCopy == true` in `.exile`, survives SBA while prepared (ruling 736),
  -- casting emits `CastEvent.announced`, and copy ceases to exist after resolving!
  let prepFace21 : AdventureFace := { name := "Phase21 Prepared Bolt", manaCost := ManaCost.empty, types := #[.instant], spellEffect := some (Effect.draw 1) }
  let prepHostDef21 : CardDef := { bear with name := "Phase21 Prepared Host", prepareFace := some prepFace21 }
  let gPrep0 : Game := addPermanent afterDraw prepHostDef21 me me
  let prepHost := (gPrep0.battlefield.filter (·.name == "Phase21 Prepared Host"))[0]!
  let gPrep1 : Game := gPrep0.becomePrepared prepHost (cause := some testCause)
  let prepCopyObj := (gPrep1.objects.filter (fun o => o.name == "Phase21 Prepared Bolt" && o.zone == .exile))[0]!
  let gPrepSba : Game := gPrep1.checkSBA
  let gPrepCast : Game := (mustApply gPrep1 me (.cast prepCopyObj.id)).resolveTop
  let copySemanticsOk : Bool :=
    !gImpCopied.wasCast copyImpStackId &&
    copyImpPerm.printed.isToken &&
    copyImpPerm.status.time == 2 &&
    !gImpCopyRes.isCreature copyImpPerm &&
    mphCopyStackObj.status.faceDown &&
    mphCopyPerm.printed.isToken &&
    mphCopyPerm.status.faceDown &&
    gMphCopyRes.name mphCopyPerm == "" &&
    gMphCopyRes.power mphCopyPerm == 2 &&
    gMphCopyRes.toughness mphCopyPerm == 2 &&
    prepCopyObj.isCopy &&
    (gPrepSba.objects.filter (fun o => o.name == "Phase21 Prepared Bolt" && o.zone == .exile)).size == 1 &&
    !(gPrepCast.player me).graveyard.any (fun id => (gPrepCast.object! id).name == "Phase21 Prepared Bolt") &&
    gPrepCast.events.any (fun e => match e.change with | .rules (.cast (.spellCast ..)) => true | _ => false)

  mustHold21 "5a.teamworkModalOk" teamworkModalOk &&
  mustHold21 "5b.youTargetCheckOk" youTargetCheckOk &&
  mustHold21 "5c.copySemanticsOk" copySemanticsOk &&
  mustHold21 "5.replay" ([gTwOne1, gTwBoth1, gYtGy, gYtStack, gYtPing, gImpCopied, gImpCopyRes, gMphCopied, gMphCopyRes, gPrep1, gPrepCast].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. Two-Headed Giant CR 810.8d 15-poison team SBA, CR 805.10d–e / 810.7 shared team blocking &
--    `legalBlockerCount`, CR 500.4 / 514.2 / 723.1 / 805.4 / 810.2 mid-shared-turn `playerControl` &
--    `.untilNextTurnOf` expiry & 2HG opponent filters, and simultaneous `withBatch` invariants.
#guard
  -- 6a. CR 810.8d: 10 + 4 = 14 poison survives in 2HG, whereas 10 + 5 = 15 loses!
  let gPsn14 : Game :=
    ((mkTwoHeadedGiant21.record
      (GameEvent.poisoned mkTwoHeadedGiant21.turnNumber ⟨0⟩ 10 (cause := testCause))).record
      (GameEvent.poisoned mkTwoHeadedGiant21.turnNumber ⟨1⟩ 4 (cause := testCause))).checkSBA
  let gPsn15 : Game :=
    (gPsn14.record
      (GameEvent.poisoned gPsn14.turnNumber ⟨1⟩ 1 (cause := testCause))).checkSBA
  let poison2hgOk : Bool :=
    !gPsn14.over &&
    !(gPsn14.player ⟨0⟩).lost &&
    gPsn15.over &&
    (gPsn15.player ⟨0⟩).lost &&
    (gPsn15.player ⟨1⟩).lost

  -- 6b. CR 805.10d–e / 810.7: menace attacker blocked jointly by `⟨2⟩`'s creature + teammate `⟨3⟩`'s creature!
  let menaceAtk21 : CardDef := { bear with name := "Phase21 Menace", keywords := { menace := true, haste := true } }
  let gBlk2h0 : Game :=
    let g := addPermanent (addPermanent (addPermanent mkTwoHeadedGiant21 bear ⟨2⟩ ⟨2⟩) hero ⟨3⟩ ⟨3⟩) menaceAtk21 ⟨0⟩ ⟨0⟩
    g.beginStep .declareAttackers
  let mAtkId := (gBlk2h0.battlefield.filter (·.name == "Phase21 Menace"))[0]!.id
  let b2Id := (gBlk2h0.battlefield.filter (·.name == bear.name))[0]!.id
  let b3Id := (gBlk2h0.battlefield.filter (·.name == hero.name))[0]!.id
  let gBlk2hAtk : Game := mustApply gBlk2h0 ⟨0⟩ (.declareAttackers #[mAtkId] (some ⟨2⟩) #[] #[])
  let gBlk2hStep : Game := gBlk2hAtk.advanceStep
  let blkChooser := gBlk2hStep.currentBlockersPlayer
  let singleBlkRejected : Bool := !(gBlk2hStep.declareBlockers blkChooser #[(b2Id, mAtkId)]).isOk
  let gBlk2hJoint : Game := mustApply gBlk2hStep blkChooser (.declareBlockers #[(b2Id, mAtkId), (b3Id, mAtkId)])
  let sharedBlockingOk : Bool :=
    gBlk2hStep.legalBlockerCount (gBlk2hStep.object! mAtkId) 2 &&
    !gBlk2hStep.legalBlockerCount (gBlk2hStep.object! mAtkId) 1 &&
    singleBlkRejected &&
    (gBlk2hJoint.object! mAtkId).status.blocked &&
    (gBlk2hJoint.blockersOf mAtkId).size == 2

  -- 6c. Mid-shared-turn `playerControl` (`onNextTurn := true`) & `.untilNextTurnOf` wait for the NEXT shared turn,
  --     and `costReductionEqualOppArtifacts` ignores teammate artifacts in 2HG!
  let oppArtSpell21 : CardDef := {
    name := "Phase21 Opp Art Spell"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
    costReductionEqualOppArtifacts := true
  }
  let art21 : CardDef := { name := "Phase21 Art", types := #[.artifact] }
  let g2hArt0 : Game :=
    insertObject (addPermanent (addPermanent (addPermanent mkTwoHeadedGiant21 art21 ⟨1⟩ ⟨1⟩) art21 ⟨1⟩ ⟨1⟩) art21 ⟨2⟩ ⟨2⟩) oppArtSpell21 ⟨0⟩ (.hand ⟨0⟩)
  let artSpellObj := g2hArt0.object! (g2hArt0.player ⟨0⟩).hand.back!
  -- Teammate `⟨1⟩` has 2 artifacts (ignored!), opponent `⟨2⟩` has 1 artifact -> `{3}` reduced by 1 = `{2}`!
  let oppArtFilterOk : Bool := g2hArt0.playManaCost artSpellObj oppArtSpell21 == ManaCost.ofGeneric 2
  -- Start on Team B seat 1 (`⟨2⟩`, two seat advances from `⟨0⟩` -> `⟨1⟩` -> `⟨2⟩`), then grant `⟨0⟩` `playerControl ⟨0⟩ ⟨2⟩ true` and `.untilNextTurnOf ⟨2⟩`:
  let gMidTeamB1 : Game :=
    let g := mkTwoHeadedGiant21.startNextTurnAndBegin.startNextTurnAndBegin -- activePlayer == ⟨2⟩ (seat 1 of Team B's shared turn)
    let g := g.withResolvingContext none ⟨0⟩ fun g => g.setPlayerControl ⟨0⟩ ⟨2⟩ (onNextTurn := true)
    g.createEffect (.playerRule ⟨0⟩ (.additionalLands 1) (.untilNextTurnOf ⟨2⟩)) (cause := some testCause)
  let gMidTeamB2 : Game := gMidTeamB1.startNextTurnAndBegin -- activePlayer == ⟨3⟩ (seat 2 of SAME shared turn!)
  let gNextTeamA1 : Game := gMidTeamB2.startNextTurnAndBegin -- ⟨0⟩
  let gNextTeamA2 : Game := gNextTeamA1.startNextTurnAndBegin -- ⟨1⟩
  let gNextTeamB1 : Game := gNextTeamA2.startNextTurnAndBegin -- NEXT shared turn of Team B (`⟨2⟩`)!
  let gNextTeamB2 : Game := gNextTeamB1.startNextTurnAndBegin -- seat 2 (`⟨3⟩`) of Team B's NEXT shared turn!
  let gAfterNextTeamB : Game := gNextTeamB2.startNextTurnAndBegin -- back to `⟨0⟩` -> expires!
  let midSharedTurnOk : Bool :=
    oppArtFilterOk &&
    gMidTeamB1.activePlayer == ⟨2⟩ &&
    !gMidTeamB1.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    gMidTeamB1.additionalLandsThisTurn ⟨0⟩ == 1 &&
    gMidTeamB2.activePlayer == ⟨3⟩ &&
    !gMidTeamB2.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    !gMidTeamB2.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    gMidTeamB2.additionalLandsThisTurn ⟨0⟩ == 1 &&
    gNextTeamB1.activePlayer == ⟨2⟩ &&
    gNextTeamB1.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    gNextTeamB1.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    gNextTeamB1.additionalLandsThisTurn ⟨0⟩ == 0 &&
    gNextTeamB2.activePlayer == ⟨3⟩ &&
    gNextTeamB2.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    gNextTeamB2.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    !gAfterNextTeamB.controlsPlayer ⟨0⟩ ⟨2⟩

  -- 6d. Simultaneous `withBatch`: `emptyManaPools`, `setRingBearer`, and two-batch `finishFrcRestBottom` (`applyDackOnHits`)!
  let gPool0 : Game := (afterDraw.addMana me (.colored .red) 1).addMana opp21 (.colored .green) 1
  let prePoolIdx := gPool0.events.size
  let gPool1 : Game := gPool0.emptyManaPools
  let poolBatches := (gPool1.events.extract prePoolIdx gPool1.events.size).filterMap fun e =>
    match e.change with | .rules (.player (.manaEmptied ..)) => some e.batch | _ => none
  let gRb0 : Game := addPermanent (addPermanent afterDraw bear me me) hero me me
  let rb1 := (gRb0.battlefield.filter (·.name == bear.name))[0]!.id
  let rb2 := (gRb0.battlefield.filter (·.name == hero.name))[0]!.id
  let gRb1 : Game := gRb0.setRingBearer me (some rb1) (cause := some testCause)
  let preRbIdx := gRb1.events.size
  let gRb2 : Game := gRb1.setRingBearer me (some rb2) (cause := some testCause)
  let rbBatches := (gRb2.events.extract preRbIdx gRb2.events.size).filterMap fun e =>
    match e.change with | .rules (.permanent (.designation _ .ringBearer _)) => some e.batch | _ => none
  let gDack0 : Game := addPermanent (addPermanent mkThreePlayer21 bear ⟨0⟩ ⟨0⟩) hero ⟨0⟩ ⟨0⟩
  let dHit1 := (gDack0.battlefield.filter (·.name == bear.name))[0]!.id
  let dHit2 := (gDack0.battlefield.filter (·.name == hero.name))[0]!.id
  let preDackIdx := gDack0.events.size
  let gDack1 : Game := gDack0.finishFrcRestBottom ⟨0⟩ #[] false (cause := some testCause) (dackTargets := #[dHit1, dHit2])
  let goadBatches := (gDack1.events.extract preDackIdx gDack1.events.size).filterMap fun e =>
    match e.change with | .rules (.permanent (.designation _ (.goaded ..) true)) => some e.batch | _ => none
  let ctrlBatches := (gDack1.events.extract preDackIdx gDack1.events.size).filterMap fun e =>
    match e.change with | .rules (.continuousEffect (.created _ (.layered _ (.control _) _))) => some e.batch | _ => none
  let batchInvariantsOk : Bool :=
    poolBatches.size == 2 && poolBatches[0]!.isSome && poolBatches[0]! == poolBatches[1]! &&
    rbBatches.size == 2 && rbBatches[0]!.isSome && rbBatches[0]! == rbBatches[1]! &&
    goadBatches.size == 2 && goadBatches[0]!.isSome && goadBatches[0]! == goadBatches[1]! &&
    ctrlBatches.size == 2 && ctrlBatches[0]!.isSome && ctrlBatches[0]! == ctrlBatches[1]! &&
    goadBatches[0]! != ctrlBatches[0]!

  mustHold21 "6a.poison2hgOk" poison2hgOk &&
  mustHold21 "6b.sharedBlockingOk" sharedBlockingOk &&
  mustHold21 "6c.midSharedTurnOk" midSharedTurnOk &&
  mustHold21 "6d.batchInvariantsOk" batchInvariantsOk &&
  mustHold21 "6.replay" ([gPsn14, gPsn15, gBlk2hJoint, g2hArt0, gMidTeamB1, gMidTeamB2, gNextTeamB1, gNextTeamB2, gAfterNextTeamB, gPool1, gRb2, gDack1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase21EventAlignment

section Phase22EventAlignment

def opp22 : PlayerId := ⟨1⟩

def mustHold22 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 22 guard failed: {label}"

-- 1. Typed `TriggerReflexiveKind` / `KeywordChoice` / `TriggerExileMode`, non-smuggled
--    `fraCauseId` / `fraCauseController` / `chosenMode` trigger reads, and sentinel-free
--    `Option ObjectId := none` prompts.
#guard
  -- 1a. Typed `TriggerReflexiveKind` (`.dealTwoDamage`, `.divideSevenDamage`) & `KeywordChoice`:
  let gRef2 : Game :=
    let g := addPermanent afterDraw bear opp22 opp22
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.queueModeledReflexive me none .dealTwoDamage
    let g := mustApply g me (.target (Target.permanent bId))
    g.resolveTop
  let bAfterRef2 := (gRef2.battlefield.filter (·.name == bear.name))[0]!
  let gKw0 : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    g.change (.pending (.fraChoice me (.chooseKeyword bId #[.trample, .hexproof])))
  let gKw1 : Game := mustApply gKw0 me (.chooseMode 0)
  let kwBear := (gKw1.battlefield.filter (·.name == bear.name))[0]!
  let typedKindKwOk : Bool :=
    bAfterRef2.status.damage == 2 &&
    gKw1.pending == .none &&
    (gKw1.effectiveKeywords kwBear).trample &&
    !(gKw1.effectiveKeywords kwBear).hexproof &&
    TriggerExileMode.playUntilNextTurn != TriggerExileMode.playThisTurn

  -- 1b. Non-smuggled `fraCauseController`, `fraCauseId` (`.forestsExceptCause`, `villainConniveTarget?`),
  --     and `StackEntry.chosenMode` (`resolvingModes` on `.stepHydeChoose`):
  let gMillCtrl : Game :=
    let g := afterDraw
    let abId : ObjectId := ⟨g.nextObjectId⟩
    let snap : EventObject := { owner := me, controller := some me, name := "Phase22 Mill Src", zone := .battlefield }
    let ab : TriggeredAbility := .onPlayerLosesLifeMillThatMany
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId snap me
      (spec := { triggeredAbility := some ab, lastKnownPower := some 2, fraCauseController := some opp22 }))
    let preLib := (g.player opp22).library.size
    let g := g.resolveTop
    if (g.player opp22).library.size == preLib - 2 then g else panic! "mill count mismatch"
  let forest22 : CardDef := { name := "Phase22 Forest", types := #[.land], supertypes := #[.basic], subtypes := #["Forest"] }
  let gFor0 : Game := addPermanent (addPermanent (addPermanent afterDraw forest22 me me) forest22 me me) forest22 me me
  let fIds := (gFor0.battlefield.filter (·.name == "Phase22 Forest")).map (·.id)
  let abForId : ObjectId := ⟨gFor0.nextObjectId⟩
  let gFor1 : Game :=
    let g := gFor0.record (GameEvent.triggerPutOnStack gFor0.turnNumber abForId (gFor0.snapshot (gFor0.object! fIds[0]!)) me
      (spec := { sourceId := some fIds[0]!, fraCauseId := some fIds[0]! }))
    g.changes #[.popStack, .pushContinuationFrame { resolvingAbility := some abForId }]
  let (_, twoOtherForestsOk) := gFor1.triggerIfHolds me (.onEnterDraw 1) (some fIds[0]!) #[] none
    (.atLeast (.count .forestsExceptCause) (.fixed 2))
  let (_, threeOtherForestsOk) := gFor1.triggerIfHolds me (.onEnterDraw 1) (some fIds[0]!) #[] none
    (.atLeast (.count .forestsExceptCause) (.fixed 3))
  let villain22 : CardDef := { bear with name := "Phase22 Villain", subtypes := #["Villain"] }
  let gVil0 : Game := addPermanent (addPermanent afterDraw villain22 me me) bear me me
  let vilId := (gVil0.battlefield.filter (·.name == "Phase22 Villain"))[0]!.id
  let srcBearId := (gVil0.battlefield.filter (·.name == bear.name))[0]!.id
  let abVilId : ObjectId := ⟨gVil0.nextObjectId⟩
  let gVil1 : Game :=
    let g := gVil0.record (GameEvent.triggerPutOnStack gVil0.turnNumber abVilId (gVil0.snapshot (gVil0.object! srcBearId)) me
      (spec := { sourceId := some srcBearId, fraCauseId := some vilId }))
    g.changes #[.popStack, .pushContinuationFrame { resolvingAbility := some abVilId }]
  let vilTargetOk : Bool := gVil1.villainConniveTarget? me srcBearId #[] == some vilId
  let hydeAb : TriggeredAbility := .onStep Effect.stepHydeChoose
  let gHyde0 : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let abId : ObjectId := ⟨g.nextObjectId⟩
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId (g.snapshot (g.object! bId)) me
      (spec := { triggeredAbility := some hydeAb, sourceId := some bId }))
    let g := g.record (GameEvent.announced g.turnNumber abId (modes := #[0]))
    g.resolveTop
  let hydeBear := (gHyde0.battlefield.filter (·.name == bear.name))[0]!
  let nonSmuggledOk : Bool :=
    twoOtherForestsOk && !threeOtherForestsOk && vilTargetOk &&
    hydeBear.status.plusOnePlusOne == 1

  -- 1c. Sentinel-free `Option ObjectId := none` prompts:
  let gPlace0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).changes #[
      .continuation (.spellOr #[{ resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }]),
      .continuation (.spellOrController me),
      .pending (.chooseLibraryPlacement me none)]
  let gPlace1 : Game := mustApply gPlace0 me .chooseTop
  let gWardNone0 : Game :=
    let g := (afterDraw.change (.pushContinuationFrame {})).changes #[
      .continuation (.unlessPaysDue true),
      .continuation (.unlessPaysController me),
      .continuation (.unlessPaysInstead (some (.draw 1))),
      .pending (.payOrLetCounter me 2 none)]
    mustApply g me .decline
  let art22 : CardDef := { name := "Phase22 Art", types := #[.artifact] }
  let gPutArt0 : Game :=
    let g := insertObject afterDraw art22 me (.hand me)
    g.change (.pending (.mayPutArtifactFromHand me none))
  let gPutArt1 : Game := mustApply gPutArt0 me .decline
  let gHydeNone0 : Game :=
    afterDraw.change (.pending (.fraChoice me (.hydeMode none)))
  let gHydeNone1 : Game := mustApply gHydeNone0 me (.chooseMode 0)
  let gPickNone0 : Game :=
    let g := addPermanent afterDraw art22 me me
    g.change (.pending (.fraChoice me (.mayPayPickThen .sacrificeAnotherArtifact .searchBasicLandTapped none)))
  let artPermId := (gPickNone0.battlefield.filter (·.name == "Phase22 Art"))[0]!.id
  let gPickNone1 : Game := mustApply gPickNone0 me (.choosePermanents #[artPermId])
  let sentinelFreeOk : Bool :=
    gPlace1.pending == .none &&
    (gWardNone0.player me).hand.size == (afterDraw.player me).hand.size + 1 &&
    gPutArt1.pending == .none &&
    gHydeNone1.pending == .none &&
    !gPickNone1.battlefield.any (·.name == "Phase22 Art")

  mustHold22 "1a.typedKindKwOk" typedKindKwOk &&
  mustHold22 "1b.nonSmuggledOk" nonSmuggledOk &&
  mustHold22 "1c.sentinelFreeOk" sentinelFreeOk &&
  mustHold22 "1.replay" ([gRef2, gKw1, gMillCtrl, gFor1, gVil1, gHyde0, gPlace1, gWardNone0, gPutArt1, gHydeNone1, gPickNone1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. Pause-safe library-exile loops (`exileLibraryUntilNonlandLoop`, `resolveCascade`,
--    `grimaExileUntilInstantOrSorcery`) and `requestOrderInto` when entered under
--    `Pending.chooseReplacement` without spinning infinitely or clobbering `.chooseReplacement`.
#guard
  let idExA : ReplacementId := { kind := .exileOppDeath, object := some ⟨920⟩ }
  let idExB : ReplacementId := { kind := .exileOppDeath, object := some ⟨921⟩ }
  let land22 : CardDef := { name := "Phase22 Land", types := #[.land] }
  let bolt22 : CardDef := {
    name := "Phase22 Bolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let mkPausedGyMove (base : Game) : Game :=
    let g := (base.createEffect
      (.replacement { id := idExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)).createEffect
      (.replacement { id := idExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
    let hId := (g.player me).hand.back!
    (g.move hId (.graveyard me) none (cause := some testCause)).1

  -- 2a. `exileLibraryUntilNonlandLoop` entered while `g.pending == .chooseReplacement`:
  let gNonland0 : Game :=
    let g := emptyLibrary afterDraw opp22
    let g := insertObject (insertObject g bolt22 opp22 (.library opp22)) land22 opp22 (.library opp22)
    let g := mkPausedGyMove g
    g.exileLibraryUntilNonlandLoop opp22 me none (some testCause)
  let nonlandPaused :=
    match gNonland0.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2 && (gNonland0.player opp22).library.size == 2
    | _ => false
  let gNonland1 : Game := mustApply gNonland0 me (.chooseReplacement idExA)
  let nonlandDoneOk : Bool :=
    nonlandPaused &&
    (gNonland1.player opp22).library.isEmpty &&
    gNonland1.objects.any (fun o => o.name == "Phase22 Bolt" && o.zone == .exile && (gNonland1.playPermission o).isSome)

  -- 2b. `resolveCascade` entered while `g.pending == .chooseReplacement`:
  let gCas0 : Game :=
    let g := emptyLibrary afterDraw me
    let g := insertObject (insertObject g bolt22 me (.library me)) land22 me (.library me)
    let g := mkPausedGyMove g
    g.resolveCascade me 3
  let casPaused :=
    match gCas0.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2 && (gCas0.player me).library.size == 2
    | _ => false
  let gCas1 : Game := mustApply gCas0 me (.chooseReplacement idExA)
  let gCas2 : Game := mustApply gCas1 me .decline
  let cascadeDoneOk : Bool :=
    casPaused &&
    (match gCas1.pending with | .fraChoice _ (.mayCastCascade ..) => true | _ => false) &&
    gCas2.pending == .none &&
    (gCas2.player me).library.size == 2

  -- 2c. `grimaExileUntilInstantOrSorcery` & `requestOrderInto` entered under `Pending.chooseReplacement`:
  let gGrima0 : Game :=
    let g := emptyLibrary afterDraw opp22
    let g := insertObject (insertObject g bolt22 opp22 (.library opp22)) land22 opp22 (.library opp22)
    let g := mkPausedGyMove g
    g.grimaExileUntilInstantOrSorcery me opp22 false
  let grimaPaused :=
    match gGrima0.pending with
    | .chooseReplacement p cs => p == me && cs.size == 2 && (gGrima0.player opp22).library.size == 2
    | _ => false
  let gGrima1 : Game := mustApply gGrima0 me (.chooseReplacement idExA)
  let gOrd0 : Game :=
    let g := insertObject (insertObject afterDraw bear opp22 .exile) hero opp22 .exile
    let exIds := (g.objects.filter (fun o => o.zone == .exile && o.owner == opp22)).map (·.id)
    let g := mkPausedGyMove g
    g.requestOrderInto exIds (.library opp22) "Phase22 order" (cause := some testCause)
  let ordPaused :=
    match gOrd0.pending with
    | .chooseReplacement p _ =>
      p == me && (gOrd0.objects.filter (fun o => o.zone == .exile && o.owner == opp22)).size == 2
    | _ => false
  let gOrd1 : Game := mustApply gOrd0 me (.chooseReplacement idExA)
  let grimaAndOrderOk : Bool :=
    grimaPaused &&
    gGrima1.pending == .none &&
    (gGrima1.player opp22).library.size == 2 &&
    ordPaused &&
    gOrd1.pending == .none &&
    (gOrd1.objects.filter (fun o => o.zone == .exile && o.owner == opp22)).isEmpty

  mustHold22 "2a.nonlandDoneOk" nonlandDoneOk &&
  mustHold22 "2b.cascadeDoneOk" cascadeDoneOk &&
  mustHold22 "2c.grimaAndOrderOk" grimaAndOrderOk &&
  mustHold22 "2.replay" ([gNonland0, gNonland1, gCas0, gCas1, gCas2, gGrima0, gGrima1, gOrd0, gOrd1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. `outerCont?` preservation in `.sarumanExileCopyMayCast`, `.fblthpSearch`, &
--    `castExiledAsAbilityResolves`, plus post-move `followMovedToZone?` in
--    `.exileReturnBrieflyIfMvAtMost`, `.exileFlicker`, and `.exileFromRevealedHand`.
#guard
  let boltDraw22 : CardDef := {
    name := "Phase22 Copy Bolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  -- 3a. `.sarumanExileCopyMayCast` preserves `outerCont?` across both decline and accept:
  let gSar0 : Game :=
    let g := insertObject afterDraw boltDraw22 opp22 (.graveyard opp22)
    let bId := (g.player opp22).graveyard.back!
    let g := (g.change (.pushContinuationFrame {})).change
      (.continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))))
    g.applyFraAbility me { targeting := .of (.ofDomain (.object .anyGraveyard (.isKind .card))), resolution := .sarumanExileCopyMayCast }
      .sarumanExileCopyMayCast #[Target.card bId] none
  let gSarDeclined : Game := mustApply gSar0 me .decline
  let gSarAccepted : Game := mustApply gSar0 me .accept
  let sarOuterOk : Bool :=
    gSarDeclined.pending == .scry me 1 &&
    gSarAccepted.pending == .scry me 1 &&
    gSarAccepted.stack.size == 1

  -- 3b. `.fblthpSearch` preserves `outerCont?`:
  let forestBasic22 : CardDef := { name := "Forest", types := #[.land], supertypes := #[.basic], subtypes := #["Forest"] }
  let gFbl0 : Game :=
    let g := addPermanent (insertObject (emptyLibrary afterDraw me) forestBasic22 me (.library me)) bear me me
    let srcId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.record (GameEvent.announced g.turnNumber srcId (x := some 1))
    let g := (g.change (.pushContinuationFrame {})).change
      (.continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))))
    (g.applyFra me { resolution := .fblthpSearch } .fblthpSearch #[] (some srcId)).finishAndGrantPriority
  let fblOuterOk : Bool :=
    gFbl0.pending == .scry me 1 &&
    (gFbl0.player me).hand.any (fun id => (gFbl0.object! id).name == "Forest")

  -- 3c. `castExiledAsAbilityResolves` preserves `outerCont?` on cast AND on cost-reversal + decline:
  let gCastExBase : Game :=
    let g := insertObject afterDraw boltDraw22 me .exile
    let exId := (g.objects.filter (fun o => o.name == "Phase22 Copy Bolt" && o.zone == .exile))[0]!.id
    (g.change (.pushContinuationFrame {})).changes #[
      .continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))),
      .pending (.mayCastExiledElseDamage me exId 2 none)]
  let exBoltId := (gCastExBase.objects.filter (fun o => o.name == "Phase22 Copy Bolt" && o.zone == .exile))[0]!.id
  let gCastExOk : Game :=
    let g := gCastExBase.addMana me (.colored .red) 1
    let g := mustApply g me (.cast exBoltId)
    mustApply g me .pay
  let gCastExCancel1 : Game :=
    let g := mustApply gCastExBase me (.cast exBoltId)
    mustApply g me .pay
  let gCastExCancel2 : Game := mustApply gCastExCancel1 me .decline
  let castExOuterOk : Bool :=
    gCastExOk.pending == .scry me 1 &&
    gCastExOk.stack.size == 1 &&
    (match gCastExCancel1.pending with | .mayCastExiledElseDamage .. => true | _ => false) &&
    gCastExCancel2.pending == .scry me 1 &&
    (gCastExCancel2.player opp22).life == (afterDraw.player opp22).life - 2

  -- 3d. Post-move `followMovedToZone?` in `.exileReturnBrieflyIfMvAtMost`, `.exileFlicker`, & `.exileFromRevealedHand`:
  let gBrief : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    g.applyFra me { targeting := .of .creature, resolution := .exileReturnBrieflyIfMvAtMost 3 }
      (.exileReturnBrieflyIfMvAtMost 3) #[Target.permanent bId] none
  let briefBear := (gBrief.battlefield.filter (·.name == bear.name))[0]!
  let gFlicker : Game :=
    let g := addPermanent afterDraw bear me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    g.applyModeledTrigger me (.onCasting (Effect.ofTrigger (.casting .exileFlicker))) none #[Target.permanent bId] "Flicker"
  let exiledBear? := gFlicker.objects.find? (fun o => o.name == bear.name && o.zone == .exile)
  let gRevHand0 : Game :=
    let g := addPermanent (insertObject afterDraw boltDraw22 opp22 (.hand opp22)) bear me me
    let srcId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let hId := (g.player opp22).hand.back!
    let g := g.change (.pending (.fraChoice me (.exileFromRevealedHand opp22 (some srcId))))
    mustApply g me (.choosePermanents #[hId])
  let revSrcId := (gRevHand0.battlefield.filter (·.name == bear.name))[0]!.id
  let exiledHandBolt? := gRevHand0.objects.find? (fun o => o.name == "Phase22 Copy Bolt" && o.zone == .exile)
  let followPostMoveOk : Bool :=
    briefBear.status.tapped &&
    exiledBear?.any (fun ex => ex.id != ⟨0⟩ && gFlicker.delayedTriggers.any (fun dt =>
      match dt.kind with | .endStepReturn oid => oid == ex.id | _ => false)) &&
    exiledHandBolt?.any (fun ex => ex.exiledBy == some revSrcId)

  mustHold22 "3a.sarOuterOk" sarOuterOk &&
  mustHold22 "3b.fblOuterOk" fblOuterOk &&
  mustHold22 "3c.castExOuterOk" castExOuterOk &&
  mustHold22 "3d.followPostMoveOk" followPostMoveOk &&
  mustHold22 "3.replay" ([gSarDeclined, gSarAccepted, gFbl0, gCastExOk, gCastExCancel1, gCastExCancel2, gBrief, gFlicker, gRevHand0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. Sequential `putCountersDeferredLog`, deferred post-replacement logs (`moveToOwnerGraveyard`,
--    `surveilMoveLoop`), and CR 614.6 arrival-zone checks (`sacrificedCreaturePower`).
#guard
  -- 4a. Sequential `putCountersDeferredLog` chains across `Pending.chooseReplacement` so the second
  --     counter-put reads `before` AFTER the first counter-put resolves (logging 4 and 4, never 8!):
  let idAddCtr22 : ReplacementId := { kind := .addCountersPut, object := some ⟨941⟩ }
  let idMulCtr22 : ReplacementId := { kind := .multiplyCountersPut, object := some ⟨942⟩ }
  let gSeq0 : Game :=
    let g := addPermanent afterDraw hero me me
    let hId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    let g := (g.createEffect
      (.replacement { id := idAddCtr22, affectedPlayer := me, kind := .modifyCountersPut (some hId) (some .plusOnePlusOne) (add := 1) (mult := 1) })
      (cause := some testCause)).createEffect
      (.replacement { id := idMulCtr22, affectedPlayer := me, kind := .modifyCountersPut (some hId) (some .plusOnePlusOne) (add := 0) (mult := 2) })
      (cause := some testCause)
    let g := g.putCountersDeferredLog hId .plusOnePlusOne 1 (some me) (.playerPutsOn me) (cause := some testCause)
    g.putCountersDeferredLog hId .plusOnePlusOne 1 (some me) (.playerPutsOn me) (cause := some testCause)
  let gSeq1 : Game := mustApply gSeq0 me (.chooseReplacement idAddCtr22)
  let gSeq2 : Game := mustApply gSeq1 me (.chooseReplacement idAddCtr22)
  let heroAfterSeq := (gSeq2.battlefield.filter (·.name == hero.name))[0]!
  let seqLogsOk : Bool :=
    (match gSeq0.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (match gSeq1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gSeq2.pending == .none &&
    heroAfterSeq.status.plusOnePlusOne == 8 &&
    !gSeq2.log.any (fun s => s.contains "8 +1/+1") &&
    (gSeq2.log.filter (fun s => s.contains "4 +1/+1")).size == 2

  -- 4b. Deferred post-replacement logs (`moveToOwnerGraveyard` & `surveilMoveLoop`) when replaced to `.exile`,
  --     plus CR 614.6 sacrifice-power check when sacrifice is exiled instead of put into graveyard:
  let idExA22 : ReplacementId := { kind := .exileOppDeath, object := some ⟨940⟩ }
  let gExOnly0 : Game :=
    afterDraw.createEffect
      (.replacement { id := idExA22, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let handCardId := (gExOnly0.player me).hand.back!
  let gMoveGyReplaced : Game :=
    gExOnly0.moveToOwnerGraveyard (gExOnly0.object! handCardId) "Card is put into its owner's graveyard" (cause := some testCause)
  let topLibId := (gExOnly0.player me).library.back!
  let gSurvReplaced : Game :=
    let g := (gExOnly0.change (.pushContinuationFrame {})).change (.continuation (.surveilReturnMvAtMost (some 10)))
    g.surveilMoveLoop me #[topLibId] (some testCause)
  let big44 : CardDef := { bear with name := "Phase22 Big 4/4", power := some 4, toughness := some 4 }
  let gSacPow0 : Game :=
    let g := addPermanent (addPermanent gExOnly0 big44 me me) bear me me
    let bigId := (g.battlefield.filter (·.name == "Phase22 Big 4/4"))[0]!.id
    let srcId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := (g.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice me (.maySacrificeAnotherCreatureForPower srcId)))
    mustApply g me (.choosePermanents #[bigId])
  let deferredAndArrivalOk : Bool :=
    !gMoveGyReplaced.log.any (fun s => s.contains "owner's graveyard") &&
    (gMoveGyReplaced.followMovedToZone? handCardId (· == .exile)).isSome &&
    !gSurvReplaced.log.any (fun s => s.contains "(surveil)") &&
    !(gSurvReplaced.player me).hand.any (fun id => id == topLibId) &&
    (gSurvReplaced.followMovedToZone? topLibId (· == .exile)).isSome &&
    gSacPow0.objects.any (fun o => o.name == "Phase22 Big 4/4" && o.zone == .exile) &&
    (gSacPow0.battlefield.filter (·.name == bear.name))[0]!.status.plusOnePlusOne == 4

  mustHold22 "4a.seqLogsOk" seqLogsOk &&
  mustHold22 "4b.deferredAndArrivalOk" deferredAndArrivalOk &&
  mustHold22 "4.replay" ([gSeq0, gSeq1, gSeq2, gMoveGyReplaced, gSurvReplaced, gSacPow0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. `finishProposedSpellCosts` `outerCont?` preservation, CR 733.1 post-prior-cost reversal
--    (`paySneak` returning the caster's only creature before `additionalCostSacrificeCreature`),
--    and `Action.decline` reversal on `.sacrificePermanent` / `.discardForAdditionalCost` only
--    when zero legal choices remain.
#guard
  -- 5a. `finishProposedSpell` (`Action.pay`) preserves `outerCont?`:
  let oneInstant22 : CardDef := {
    name := "Phase22 One Instant"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let zeroInstant22 : CardDef := {
    name := "Phase22 Zero Instant"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { resolution := .ofSpell (.draw (.fixed 1) .you), phrase := "Draw a card" }
  }
  let gPropOuterCast : Game :=
    let g := (insertObject afterDraw oneInstant22 me (.hand me)).addMana me (.colored .red) 1
    let spId := (g.player me).hand.back!
    let g := mustApply g me (.cast spId)
    let g := (g.change (.pushContinuationFrame {})).change
      (.continuation (.pendingReplacement (some (.restorePending (.scry me 1) false))))
    mustApply g me .pay
  let propOuterOk : Bool :=
    gPropOuterCast.pending == .scry me 1 &&
    gPropOuterCast.stack.size == 1

  -- 5b. Sneak + `additionalCostSacrificeCreature` when the unblocked attacker is `me`'s ONLY creature:
  --     `paySneak` returns that attacker to hand, leaving 0 creatures to sacrifice, so `.finalize`
  --     reverses the entire proposed spell per CR 733.1 (attacker is back on `.battlefield`, sneak spell in `.hand`!):
  let sneakSacCreature22 : CardDef := {
    bear with
    name := "Phase22 Sneak Sac"
    manaCost := ManaCost.ofGeneric 4
    additionalCostSacrificeCreature := true
    staticAbilities := #[.sneak ManaCost.empty]
  }
  let gSneak0 : Game :=
    let g := addPermanent (insertObject afterDraw sneakSacCreature22 me (.hand me)) bear me me
    let atkId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := g.beginStep .declareAttackers
    let g := mustApply g me (.declareAttackers #[atkId] none #[] #[])
    g.advanceStep
  let gSneakUnblocked : Game := mustApply gSneak0 opp22 (.declareBlockers #[])
  let sneakCardId := ((gSneakUnblocked.player me).hand.filter (fun id => (gSneakUnblocked.object! id).name == "Phase22 Sneak Sac"))[0]!
  let atkBearId := (gSneakUnblocked.battlefield.filter (·.name == bear.name))[0]!.id
  let sneakReversedOrRejected : Bool :=
    match (gSneakUnblocked.apply me (.castWithSneak sneakCardId atkBearId)).bind (fun g => g.apply me .pay) with
    | .error _ => false
    | .ok gAfter =>
      gAfter.proposedSpell.isNone &&
      gAfter.battlefield.any (·.name == bear.name) &&
      (gAfter.player me).hand.any (fun id => (gAfter.object! id).name == "Phase22 Sneak Sac")
  let gSneakWithExtra : Game :=
    let g := addPermanent gSneakUnblocked hero me me
    let g := mustApply g me (.castWithSneak sneakCardId atkBearId)
    mustApply g me .pay
  let sneakExtraPromptsSacOk : Bool :=
    (match gSneakWithExtra.pending with | .sacrificePermanent q _ => q == me | _ => false) &&
    !(gSneakWithExtra.apply me .decline).isOk

  -- 5c. `.sacrificePermanent` / `.discardForAdditionalCost` allow `Action.decline` reversal when 0 choices remain:
  let gZeroSac0 : Game :=
    let g := insertObject afterDraw sneakSacCreature22 me (.hand me)
    let spId := (g.player me).hand.back!
    let orig := g.object! spId
    let g := g.change .saveProposalCheckpoint
    let (g, newSpId) := g.move spId .stack (some me) (verb := some .cast) (actor := some me)
    g.changes #[
      .proposedSpell (some { caster := me, spellId := newSpId, original := orig, cost := ManaCost.empty, needsSacrificeOther := true }),
      .pending (.sacrificePermanent me newSpId)]
  let gZeroSacRev : Game := mustApply gZeroSac0 me .decline
  let gZeroDisc0 : Game :=
    let g := emptyHand afterDraw me
    let g := insertObject g zeroInstant22 me (.hand me)
    let spId := (g.player me).hand.back!
    let orig := g.object! spId
    let g := g.change .saveProposalCheckpoint
    let (g, newSpId) := g.move spId .stack (some me) (verb := some .cast) (actor := some me)
    g.changes #[
      .proposedSpell (some { caster := me, spellId := newSpId, original := orig, cost := ManaCost.empty, needsDiscardCard := true }),
      .pending (.discardForAdditionalCost me)]
  let gZeroDiscRev : Game := mustApply gZeroDisc0 me .decline
  let zeroChoiceDeclineRevOk : Bool :=
    sneakReversedOrRejected &&
    sneakExtraPromptsSacOk &&
    gZeroSacRev.pending == .none &&
    gZeroSacRev.proposedSpell.isNone &&
    (gZeroSacRev.player me).hand.any (fun id => (gZeroSacRev.object! id).name == "Phase22 Sneak Sac") &&
    gZeroDiscRev.pending == .none &&
    gZeroDiscRev.proposedSpell.isNone &&
    (gZeroDiscRev.player me).hand.any (fun id => (gZeroDiscRev.object! id).name == "Phase22 Zero Instant")

  mustHold22 "5a.propOuterOk" propOuterOk &&
  mustHold22 "5b_c.zeroChoiceDeclineRevOk" zeroChoiceDeclineRevOk &&
  mustHold22 "5.replay" ([gPropOuterCast, gSneakUnblocked, gSneakWithExtra, gZeroSacRev, gZeroDiscRev].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 614.12 simultaneous `preBfOk` (`selfEntersTapped`, `entersWithHopePerCreature`,
--    `replaceCountersPutChoice` `entersWith`) when `g.currentBatch.isNone`, plus unbatched
--    `Movement.move` sharing one arrival `BatchId` with `.entersUntappedPayLife`.
#guard
  let leg22 : CardDef := { bear with name := "Phase22 CoLegend", supertypes := #[.legendary] }
  let checkLand22 : CardDef := { name := "Phase22 CheckLand", types := #[.land], entersTappedUnlessLegendary := true }
  let hopeCr22 : CardDef := { bear with name := "Phase22 HopeCr", entersWithHopePerCreature := true }
  let doc22 : CardDef := { bear with name := "Phase22 CoDoc", staticAbilities := #[.extraCounterOnPermanents] }
  let plusCr22 : CardDef := { bear with name := "Phase22 PlusCr", entersWithPlusOneCounters := 1 }

  -- 6a. Simultaneous entry via `putToBattlefieldLoop` (`g.currentBatch == none`, `preBattlefield := some preBf`):
  --     none of the co-entering permanents were on `preBf`, so `CheckLand` enters tapped, `HopeCr` gets 1 hope
  --     (counting only itself, excluding co-entering `CoLegend` and `CoDoc`), and `PlusCr` gets 1 (NOT 2!) +1/+1 counter!
  let gSim0 : Game :=
    insertObject (insertObject (insertObject (insertObject (insertObject afterDraw
      leg22 me (.hand me))
      checkLand22 me (.hand me))
      hopeCr22 me (.hand me))
      doc22 me (.hand me))
      plusCr22 me (.hand me)
  let preBf22 := gSim0.battlefield
  let handTail := (gSim0.player me).hand.extract ((gSim0.player me).hand.size - 5) (gSim0.player me).hand.size
  let gSimDone : Game :=
    gSim0.putToBattlefieldLoop me handTail #[] false false false false false .none (some testCause) (some preBf22)
  let simLand := (gSimDone.battlefield.filter (·.name == "Phase22 CheckLand"))[0]!
  let simHope := (gSimDone.battlefield.filter (·.name == "Phase22 HopeCr"))[0]!
  let simPlus := (gSimDone.battlefield.filter (·.name == "Phase22 PlusCr"))[0]!
  -- Control check: when `CoDoc` and `CoLegend` ARE already on `preBattlefield`, `CheckLand` enters untapped,
  -- `HopeCr` gets 4 hope counters (2 pre-existing creatures + 1 self + 1 from `CoDoc`), and `PlusCr` gets 2 +1/+1 counters!
  let gSeqCtrl0 : Game :=
    insertObject (insertObject (insertObject (addPermanent (addPermanent afterDraw leg22 me me) doc22 me me)
      checkLand22 me (.hand me))
      hopeCr22 me (.hand me))
      plusCr22 me (.hand me)
  let ctrlTail := (gSeqCtrl0.player me).hand.extract ((gSeqCtrl0.player me).hand.size - 3) (gSeqCtrl0.player me).hand.size
  let gSeqCtrlDone : Game :=
    gSeqCtrl0.putToBattlefieldLoop me ctrlTail #[] false false false false false .none (some testCause) (some gSeqCtrl0.battlefield)
  let ctrlLand := (gSeqCtrlDone.battlefield.filter (·.name == "Phase22 CheckLand"))[0]!
  let ctrlHope := (gSeqCtrlDone.battlefield.filter (·.name == "Phase22 HopeCr"))[0]!
  let ctrlPlus := (gSeqCtrlDone.battlefield.filter (·.name == "Phase22 PlusCr"))[0]!
  let simultaneousPreBfOk : Bool :=
    simLand.status.tapped &&
    simHope.status.hope == 1 &&
    simPlus.status.plusOnePlusOne == 1 &&
    !ctrlLand.status.tapped &&
    ctrlHope.status.hope == 4 &&
    ctrlPlus.status.plusOnePlusOne == 2

  -- 6b. Unbatched `putOntoBattlefield` of a shock land (`entersTappedUnlessPayLife := some 2`):
  --     accepting `.entersUntappedPayLife 2` records `.life (.lost ...)` and `.zone (.moved ... .battlefield)`
  --     under the SAME non-`none` arrival `BatchId`!
  let shockLand22 : CardDef := { name := "Phase22 ShockLand", types := #[.land], entersTappedUnlessPayLife := some 2 }
  let gShock0 : Game := insertObject afterDraw shockLand22 me (.hand me)
  let shockId := (gShock0.player me).hand.back!
  let preShockIdx := gShock0.events.size
  let (gShockPrompt, _) := gShock0.putOntoBattlefield shockId me (cause := some testCause)
  let payLifeRid : ReplacementId :=
    match gShockPrompt.pending with
    | .chooseReplacement _ cs => (cs.find? (fun r => r.kind == .entersUntappedPayLife 2)).getD cs[0]!
    | _ => { kind := .entersUntappedPayLife 2 }
  let gShockPaid : Game := mustApply gShockPrompt me (.chooseReplacement payLifeRid)
  let shockSlice := gShockPaid.events.extract preShockIdx gShockPaid.events.size
  let lifeBatch? := shockSlice.findSome? fun e =>
    match e.change with | .rules (.life (.lost ..)) => some e.batch | _ => none
  let enterBatch? := shockSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ _ .battlefield ..)) => some e.batch | _ => none
  let shockBatchOk : Bool :=
    lifeBatch?.any Option.isSome &&
    lifeBatch? == enterBatch? &&
    !(gShockPaid.battlefield.filter (·.name == "Phase22 ShockLand"))[0]!.status.tapped

  mustHold22 "6a.simultaneousPreBfOk" simultaneousPreBfOk &&
  mustHold22 "6b.shockBatchOk" shockBatchOk &&
  mustHold22 "6.replay" ([gSimDone, gSeqCtrlDone, gShockPrompt, gShockPaid].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 614.6 / 701.47a `finishFreshAmass` choice under `tokenDoubling`, `createdTokensThisWay`
--    across multiplied token creation (`.createAlienPerInvasion`), and CR 616.1
--    `enterWithPlusOnes` preserving unrelated `replacementOrder` entries.
#guard
  let doubler22 : CardDef := { bear with name := "Phase22 Doubler", tokenDoubling := true }
  -- 7a. `finishFreshAmass` under `tokenDoubling` prompts `.chooseCards` across the 2 fresh 0/0 Armies:
  let gAmass0 : Game := (addPermanent afterDraw doubler22 me me).amassGoblins me 3
  let amassPromptIds : Array ObjectId :=
    match gAmass0.pending with
    | .fraChoice q (.chooseCards ids 1 (.amassArmy .goblin 3 none)) =>
      if q == me && ids.size == 2 then ids else #[]
    | _ => #[]
  let chosenArmyId := amassPromptIds[1]!
  let gAmass1 : Game := mustApply gAmass0 me (.choosePermanents #[chosenArmyId])
  let survivingArmies := gAmass1.battlefield.filter (·.name == "Goblin Army")
  let freshAmassChoiceOk : Bool :=
    amassPromptIds.size == 2 &&
    survivingArmies.size == 1 &&
    survivingArmies[0]!.id == chosenArmyId &&
    survivingArmies[0]!.status.plusOnePlusOne == 3

  -- 7b. `createdTokensThisWay` across multiplied token creation (`.createAlienPerInvasion`):
  --     with 2 invasion counters and `tokenDoubling`, BOTH created Alien tokens get 2 +1/+1 counters!
  let gAlien0 : Game :=
    let g := addPermanent afterDraw doubler22 me me
    let dId := (g.battlefield.filter (·.name == "Phase22 Doubler"))[0]!.id
    let g := g.recordPutCounters dId .invasion 2 (some me) (cause := some testCause)
    g.applyTriggeredAbility me (.onCombatCreateAlienPerInvasion) (some dId)
  let aliens := gAlien0.battlefield.filter (fun o => o.printed.isToken && gAlien0.hasSubtype o .alien)
  let multipliedCreatedTokensOk : Bool :=
    aliens.size == 2 &&
    aliens.all (·.status.plusOnePlusOne == 2)

  -- 7c. CR 616.1 `enterWithPlusOnes` consumes ONLY applied counter-replacement IDs from `replacementOrder`,
  --     preserving unrelated queued `ReplacementId` entries!
  let docOrd22 : CardDef := { bear with name := "Phase22 OrdDoc", staticAbilities := #[.extraCounterOnPermanents] }
  let plusOne22 : CardDef := { bear with name := "Phase22 OrdPlus", entersWithPlusOneCounters := 1 }
  let unrelatedRid : ReplacementId := { kind := .exileOppDeath, object := some ⟨970⟩ }
  let gOrdKeep0 : Game :=
    let g := insertObject (addPermanent afterDraw docOrd22 me me) plusOne22 me (.hand me)
    let docId := (g.battlefield.filter (·.name == "Phase22 OrdDoc"))[0]!.id
    let docRid : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
    let g := (g.change (.pushContinuationFrame {})).change (.replacementOrder #[docRid, unrelatedRid])
    let pId := (g.player me).hand.back!
    (g.putOntoBattlefield pId me (cause := some testCause)).1
  let ordPlusPerm := (gOrdKeep0.battlefield.filter (·.name == "Phase22 OrdPlus"))[0]!
  let replacementOrderPreservedOk : Bool :=
    ordPlusPerm.status.plusOnePlusOne == 2 &&
    gOrdKeep0.replacementOrder == #[unrelatedRid]

  mustHold22 "7a.freshAmassChoiceOk" freshAmassChoiceOk &&
  mustHold22 "7b.multipliedCreatedTokensOk" multipliedCreatedTokensOk &&
  mustHold22 "7c.replacementOrderPreservedOk" replacementOrderPreservedOk &&
  mustHold22 "7.replay" ([gAmass0, gAmass1, gAlien0, gOrdKeep0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase22EventAlignment

section Phase23EventAlignment

def opp23 : PlayerId := ⟨1⟩

def mustHold23 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 23 guard failed: {label}"

-- 1. Pause-safe continuation & library ordering: `drainPendingContinuations`
--    `triggerSequenceRest`-before-`outerPendingReplacements`, non-mana `payWard`
--    `.afterWardResolved`-before-`outerCont?`, `beginResolutionCastTargets`
--    post-`becomeCast` pause chaining, `moveIdsInOrder` `.fromTop` offsets, and
--    `.lootLandEntersTapped` graveyard-only check.
#guard
  -- 1a. `drainPendingContinuations` drains `triggerSequenceRest` BEFORE `outerPendingReplacements`:
  let dummyTrig : TriggeredAbility := .triggered .enter (Effect.gainLife 1)
  let seqRest : TriggerSequenceRest := {
    controller := me
    ability := dummyTrig
    steps := [.gainLife 3]
  }
  let gDrain0 : Game :=
    afterDraw.change (.pushContinuationFrame {
      resolvingContext := some (none, me)
      triggerSequenceRest := some seqRest
      outerPendingReplacements := #[.restorePending (.scry me 1)]
    })
  let gDrain1 : Game := gDrain0.drainPendingContinuations
  let drainOrderOk : Bool :=
    (gDrain1.player me).life == (afterDraw.player me).life + 3 &&
    gDrain1.pending == .scry me 1 &&
    gDrain1.outerPendingReplacements.isEmpty

  -- 1b. Non-mana `payWard` (`.discardCard` & `.fivePoison`) runs `outerCont?` BEFORE `.afterWardResolved` (Phase 33 Item 1):
  let gWard0 : Game :=
    let g := insertObject (insertObject afterDraw bear me (.hand me)) hero me .stack (some me)
    let spId := (g.objects.filter (fun o => o.name == hero.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    (g.changes #[
      .pushContinuationFrame {
        resolvingContext := some (none, opp23)
        pendingReplacement := some (.restorePending (.scry me 1))
      },
      .pending (.payWard me spId .discardCard)
    ])
  let handCardId := (gWard0.player me).hand.back!
  let gWardDisc : Game := mustApply gWard0 me (.discard handCardId)
  let gWardPsn0 : Game :=
    let spId := gWard0.stack[0]!.objectId
    gWard0.change (.pending (.payWard me spId .fivePoison))
  let gWardPsn : Game := mustApply gWardPsn0 me .pay
  let wardOrderOk : Bool :=
    gWardDisc.pending == .scry me 1 &&
    gWardDisc.pendingReplacement == some .afterWardResolved &&
    gWardPsn.pending == .scry me 1 &&
    gWardPsn.pendingReplacement == some .afterWardResolved &&
    (gWardPsn.player me).poison == 5

  -- 1c. `beginResolutionCastTargets`: 0-mana untargeted exiled creature cast via `.mayCastExiledElseDamage`
  --     chains outer continuation after `becomeCast` without losing the outer continuation!
  let gResCast0 : Game :=
    let g := insertObject afterDraw { bear with manaCost := ManaCost.empty } me .exile
    let exId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
    g.changes #[
      .pushContinuationFrame {
        resolvingContext := some (none, me)
        pendingReplacement := some (.restorePending (.scry me 1))
      },
      .pending (.mayCastExiledElseDamage me exId 2 none)
    ]
  let exCastId := (gResCast0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let gResCast1 : Game := mustApply gResCast0 me (.cast exCastId)
  let resCastChainOk : Bool :=
    gResCast1.stack.size == 1 &&
    gResCast1.pending == .scry me 1

  -- 1d. `moveIdsInOrder` / `moveIdsInOrderLoop` `.fromTop` offsets preserve bottom-group ordering across pauses:
  let cTop : CardDef := { bear with name := "Phase23 Top" }
  let cBot : CardDef := { bear with name := "Phase23 Bot" }
  let cIns1 : CardDef := { bear with name := "Phase23 Ins1" }
  let cIns2 : CardDef := { bear with name := "Phase23 Ins2" }
  let gLib0 : Game :=
    insertObject (insertObject (insertObject (insertObject afterDraw cBot me (.library me)) cTop me (.library me)) cIns1 me (.graveyard me)) cIns2 me (.graveyard me)
  let ins1Id := (gLib0.objects.filter (·.name == "Phase23 Ins1"))[0]!.id
  let ins2Id := (gLib0.objects.filter (·.name == "Phase23 Ins2"))[0]!.id
  let gLibSync : Game := gLib0.moveIdsInOrder #[ins1Id, ins2Id] (.library me) (cause := some testCause)
  let libNames := (gLibSync.player me).library.map (fun id => (gLibSync.object! id).name)
  -- Bottom of library is `[0]!`: `Ins1` is `[0]!`, `Ins2` is `[1]!` (`fromTop (libSize - 1)`).
  let libHead := libNames.extract 0 2
  -- Resumed `moveIdsInOrderLoop` when `ins1Id` entered `.library me` vs when `ins1Id` was exiled instead:
  let gLibResumed : Game :=
    let (g1, _) := gLib0.move ins1Id (.library me) none (libraryPosition := some .bottom) (cause := some testCause)
    g1.moveIdsInOrderLoop #[ins2Id] (.library me) "" (some testCause) 0 (some (ins1Id, .library me))
  let resumedHead := ((gLibResumed.player me).library.map (fun id => (gLibResumed.object! id).name)).extract 0 2
  let gLibRedirected : Game :=
    let (g1, _) := gLib0.move ins1Id .exile none (cause := some testCause)
    g1.moveIdsInOrderLoop #[ins2Id] (.library me) "" (some testCause) 0 (some (ins1Id, .library me))
  let redirectedBottom := (gLibRedirected.object! (gLibRedirected.player me).library[0]!).name
  let fromTopOffsetOk : Bool :=
    libHead == #["Phase23 Ins1", "Phase23 Ins2"] &&
    resumedHead == #["Phase23 Ins1", "Phase23 Ins2"] &&
    redirectedBottom == "Phase23 Ins2"

  -- 1e. `.lootLandEntersTapped`: exiled discard (`.exileInsteadOfGraveyard`) does NOT put the land onto `.battlefield`!
  let lootLandDef : CardDef := { forest with name := "Phase23 Loot Forest" }
  let gLoot0 : Game :=
    let g := afterDraw
    let g := (g.player me).hand.foldl (fun acc hid => (acc.move hid .exile none (cause := some testCause)).1) g
    let g := insertObject (insertObject g bear me (.library me)) lootLandDef me (.library me)
    g.createEffect (.replacement {
      id := { kind := .exileOppDeath }
      source := none, controller := some opp23, affectedPlayer := me
      kind := .exileInsteadOfGraveyard none }) (cause := some testCause)
  let gLoot1 : Game := gLoot0.applyTriggeredAbility me (.triggered .enter (Effect.ofTrigger .lootLandEntersTapped)) none
  let lootHandLand := ((gLoot1.player me).hand.filter (fun id => (gLoot1.object! id).name == "Phase23 Loot Forest"))[0]!
  let gLoot2 : Game := mustApply gLoot1 me (.discard lootHandLand)
  let lootGyOnlyOk : Bool :=
    !(gLoot2.battlefield.any (·.name == "Phase23 Loot Forest")) &&
    gLoot2.objects.any (fun o => o.name == "Phase23 Loot Forest" && o.zone == .exile)

  mustHold23 "1a.drainOrderOk" drainOrderOk &&
  mustHold23 "1b.wardOrderOk" wardOrderOk &&
  mustHold23 "1c.resCastChainOk" resCastChainOk &&
  mustHold23 "1d.fromTopOffsetOk" fromTopOffsetOk &&
  mustHold23 "1e.lootGyOnlyOk" lootGyOnlyOk &&
  mustHold23 "1.replay" ([gDrain1, gWardDisc, gWardPsn, gResCast1, gLibSync, gLibResumed, gLibRedirected, gLoot2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. Sequential multi-target CR 608.2b legality across replacement pauses & CR 615.6 deferred damage logs.
#guard
  -- 2a. Multi-target `countersOnCreatureTargetsLoop` pauses on target 0's replacement choice BEFORE putting counters on target 1:
  let gSeqTgt0 : Game :=
    let g := addPermanent (addPermanent afterDraw bear me me) hero me me
    let bId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let rAdd : ReplacementId := { kind := .addCountersPut, object := some ⟨981⟩ }
    let rMul : ReplacementId := { kind := .multiplyCountersPut, object := some ⟨982⟩ }
    let g := g.createEffect (.replacement {
      id := rAdd, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut (some bId) (some .plusOnePlusOne) (add := 1) (mult := 1) }) (cause := some testCause)
    g.createEffect (.replacement {
      id := rMul, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut (some bId) (some .plusOnePlusOne) (add := 0) (mult := 2) }) (cause := some testCause)
  let t0Id := (gSeqTgt0.battlefield.filter (·.name == bear.name))[0]!.id
  let t1Id := (gSeqTgt0.battlefield.filter (·.name == hero.name))[0]!.id
  let rAdd23 : ReplacementId := { kind := .addCountersPut, object := some ⟨981⟩ }
  let gSeqPaused : Game :=
    gSeqTgt0.withBatch (some testCause) fun g =>
      g.countersOnCreatureTargetsLoop me #[.permanent t0Id, .permanent t1Id] .plusOnePlusOne 1 none
  let pausedBeforeSecond : Bool :=
    (match gSeqPaused.pending with | .chooseReplacement p _ => p == me | _ => false) &&
    (gSeqPaused.object! t1Id).status.plusOnePlusOne == 0
  let gSeqDone : Game := mustApply gSeqPaused me (.chooseReplacement rAdd23)
  let seqTargetsOk : Bool :=
    pausedBeforeSecond &&
    gSeqDone.pending == .none &&
    (gSeqDone.object! t0Id).status.plusOnePlusOne == 4 &&
    (gSeqDone.object! t1Id).status.plusOnePlusOne == 1

  -- 2b. CR 615.6 prevented damage (`dealt == 0`) suppresses damage logs in `dealDamageLoseIndestructibleExileTo`
  --     and `causeDealsDamageToOpponentsLoop`!
  let gPrev0 : Game :=
    let g := addPermanent afterDraw bear opp23 opp23
    let oppBearId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let prevSpec : PreventionSpec := {
      id := { kind := .preventAllDamageToPermanent, object := some oppBearId }
      source := some oppBearId, controller := some opp23, affectedPlayer := opp23
      kind := .preventAllDamageToPermanent oppBearId }
    (g.createEffect (.prevention prevSpec) (cause := some testCause)).createEffect
      (.protectionFromEverything opp23) (cause := some testCause)
  let oppBearId23 := (gPrev0.battlefield.filter (·.name == bear.name))[0]!.id
  let prePermLog := gPrev0.log.size
  let gSmitePrev : Game :=
    gPrev0.dealDamageLoseIndestructibleExileTo (gPrev0.object! oppBearId23) 2
      (gPrev0.snapshot (gPrev0.object! oppBearId23))
  let preOppLog := gPrev0.log.size
  let gOppDmgPrev : Game := gPrev0.causeDealsDamageToOpponentsLoop #[opp23] 2 "Phase23 Source" none (some testCause)
  let smiteLogs := gSmitePrev.log.extract prePermLog gSmitePrev.log.size
  let oppDmgLogs := gOppDmgPrev.log.extract preOppLog gOppDmgPrev.log.size
  let preventedNoSideEffectOk : Bool :=
    smiteLogs.any (·.contains "loses indestructible") &&
    !(smiteLogs.any (·.contains "is dealt")) &&
    !(oppDmgLogs.any (·.contains "Phase23 Source deals"))

  -- 2c. CR 614.6 arrival gating on Clash of Elements (`.topOrBottomDamage` / `.topOrBottomDamageFollowup`)
  --     and `FrcResolve` `handDiscard` / `.logHandDiscard` when replaced to `.exile`:
  let gTopExiled : Game :=
    let g := addPermanent afterDraw bear opp23 opp23
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let (g, _) := g.move bid .exile none (cause := some testCause)
    g.runPostStep (.topOrBottomDamageFollowup bid opp23 bear.name true 2 none)
  let clashShockDef23 : CardDef := {
    forest with
    name := "Phase23 Clash Linked Shock"
    entersTappedUnlessPayLife := some 2
  }
  let gTopPaused0 : Game :=
    let g := addPermanent (insertObject afterDraw clashShockDef23 me .exile) bear opp23 opp23
    let bid := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let exId := (g.objects.filter (fun o => o.name == "Phase23 Clash Linked Shock" && o.zone == .exile))[0]!.id
    let g := (g.change (.object bid (.pushLinkedExile exId))).change (.pushContinuationFrame {})
    let g := g.change (.pending (.fraChoice opp23 (.topOrBottomDamage bid 2 none)))
    mustApply g opp23 .chooseTop
  let gTopPausedDone : Game :=
    match gTopPaused0.pending with
    | .chooseReplacement p cs => mustApply gTopPaused0 p (.chooseReplacement cs[0]!)
    | _ => gTopPaused0
  let idHdExA : ReplacementId := { kind := .exileOppDeath, object := some ⟨988⟩ }
  let idHdExB : ReplacementId := { kind := .exileOppDeath, object := some ⟨989⟩ }
  let gHdSync0 : Game :=
    afterDraw.createEffect
      (.replacement { id := idHdExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let preHdSyncLog := gHdSync0.log.size
  let hdSyncCard := (gHdSync0.player me).hand.back!
  let gHdSync1 : Game := gHdSync0.runFrcPostStep (.discardHand me)
  let gHdPause0 : Game :=
    gHdSync0.createEffect
      (.replacement { id := idHdExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let preHdPauseLog := gHdPause0.log.size
  let hdPauseCard := (gHdPause0.player me).hand.back!
  let gHdPause1 : Game := gHdPause0.runFrcPostStep (.discardHand me)
  let gHdPause2 : Game := mustApply gHdPause1 me (.chooseReplacement idHdExA)
  let preHdNormLog := afterDraw.log.size
  let gHdNorm : Game := afterDraw.runFrcPostStep (.discardHand me)
  let dfhSyncCard := (gHdSync0.player me).hand.back!
  let preDfhSyncLog := gHdSync0.log.size
  let gDfhSync : Game := gHdSync0.discardFromHand me dfhSyncCard
  let dpcPauseCard := (gHdPause0.player me).hand.back!
  let gDpcPause0 : Game := gHdPause0.change (.pending (.chooseDiscardCard me #[]))
  let preDpcPauseLog := gDpcPause0.log.size
  let gDpcPause1 : Game := mustApply gDpcPause0 me (.discard dpcPauseCard)
  let gDpcPause2 : Game := mustApply gDpcPause1 me (.chooseReplacement idHdExA)
  let gSacChSync0 : Game := addPermanent gHdSync0 bear me me
  let sacChSyncId := (gSacChSync0.battlefield.filter (·.name == bear.name))[0]!.id
  let preSacChSyncLog := gSacChSync0.log.size
  let gSacChSync1 : Game :=
    gSacChSync0.sacrificeChosenOrGone #[.player me, .permanent sacChSyncId]
  let gSacChPause0 : Game := addPermanent gHdPause0 bear me me
  let sacChPauseId := (gSacChPause0.battlefield.filter (·.name == bear.name))[0]!.id
  let preSacChPauseLog := gSacChPause0.log.size
  let gSacChPause1 : Game :=
    gSacChPause0.sacrificeChosenOrGone #[.player me, .permanent sacChPauseId]
  let gSacChPause2 : Game := mustApply gSacChPause1 me (.chooseReplacement idHdExA)
  let gSacChNorm0 : Game := addPermanent afterDraw bear me me
  let sacChNormId := (gSacChNorm0.battlefield.filter (·.name == bear.name))[0]!.id
  let preSacChNormLog := gSacChNorm0.log.size
  let gSacChNorm1 : Game :=
    gSacChNorm0.sacrificeChosenOrGone #[.player me, .permanent sacChNormId]
  let clashAndHandDiscardArrivalOk : Bool :=
    (gTopExiled.player opp23).life == 20 &&
    !gTopExiled.log.any (·.contains "on top of their library") &&
    (gTopPaused0.player opp23).life == 20 &&
    (gTopPausedDone.player opp23).life == 18 &&
    gTopPausedDone.log.any (·.contains "on top of their library") &&
    (gHdSync1.followMovedToZone? hdSyncCard (· == .exile)).isSome &&
    !(gHdSync1.log.extract preHdSyncLog gHdSync1.log.size).any (·.contains "discards ") &&
    (match gHdPause1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gHdPause2.followMovedToZone? hdPauseCard (· == .exile)).isSome &&
    !(gHdPause2.log.extract preHdPauseLog gHdPause2.log.size).any (·.contains "discards ") &&
    (gHdNorm.log.extract preHdNormLog gHdNorm.log.size).any (·.contains "discards ") &&
    (gDfhSync.followMovedToZone? dfhSyncCard (· == .exile)).isSome &&
    !(gDfhSync.log.extract preDfhSyncLog gDfhSync.log.size).any (·.contains "discards ") &&
    (gDpcPause2.followMovedToZone? dpcPauseCard (· == .exile)).isSome &&
    !(gDpcPause2.log.extract preDpcPauseLog gDpcPause2.log.size).any (·.contains "discards ") &&
    (gSacChSync1.followMovedToZone? sacChSyncId (· == .exile)).isSome &&
    !(gSacChSync1.log.extract preSacChSyncLog gSacChSync1.log.size).any (·.contains "is sacrificed") &&
    (gSacChPause2.followMovedToZone? sacChPauseId (· == .exile)).isSome &&
    !(gSacChPause2.log.extract preSacChPauseLog gSacChPause2.log.size).any (·.contains "is sacrificed") &&
    (gSacChNorm1.log.extract preSacChNormLog gSacChNorm1.log.size).any (·.contains "is sacrificed")

  mustHold23 "2a.seqTargetsOk" seqTargetsOk &&
  mustHold23 "2b.preventedNoSideEffectOk" preventedNoSideEffectOk &&
  mustHold23 "2c.clashAndHandDiscardArrivalOk" clashAndHandDiscardArrivalOk &&
  mustHold23 "2.replay" ([gSeqPaused, gSeqDone, gSmitePrev, gOppDmgPrev,
      gTopExiled, gTopPaused0, gTopPausedDone, gHdSync1, gHdPause1, gHdPause2, gHdNorm,
      gDfhSync, gDpcPause1, gDpcPause2, gSacChSync1, gSacChPause1, gSacChPause2, gSacChNorm1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. 0-mana `sneakAttacker` bounce, reduced-`{0}` `activateAbility` `CastEvent.announced`,
--    spell-sacrifice `CastEvent.announced`, CR 106.6 `fromTreasure` & `.cantNonartifact`, and
--    `payWard` / `payOrLetCounter` `manaSpentOn` provenance.
#guard
  -- 3a. 0-mana `sneakAttacker` returns the unblocked attacker to hand and records `costs := #[.sneak atkId ...]`:
  let zeroSneakDef : CardDef := {
    bear with
    name := "Phase23 Zero Sneak"
    staticAbilities := #[.sneak ManaCost.empty]
  }
  let gSnk0 : Game :=
    let g := insertObject (addPermanent afterDraw { bear with keywords := Keyword.haste } me me) zeroSneakDef me (.hand me)
    let atkId := (g.battlefield.filter (·.name == bear.name))[0]!.id
    let g := mustApply (mustApply (g.beginStep .beginningOfCombat) me .pass) opp23 .pass
    let g := mustApply g me (.declareAttackers #[atkId] none #[] #[])
    let g := mustApply (mustApply g me .pass) opp23 .pass
    mustApply g opp23 (.declareBlockers #[])
  let snkAtkId := (gSnk0.battlefield.filter (·.name == bear.name))[0]!.id
  let snkCardId := (gSnk0.objects.filter (fun o => o.name == "Phase23 Zero Sneak" && o.zone == .hand me))[0]!.id
  let preSnkIdx := gSnk0.events.size
  let gSnk1 : Game := mustApply (mustApply gSnk0 me (.castWithSneak snkCardId snkAtkId)) me .pay
  let zeroSneakOk : Bool :=
    (gSnk1.player me).hand.any (fun id => (gSnk1.object! id).name == bear.name) &&
    !(gSnk1.battlefield.any (·.id == snkAtkId)) &&
    (gSnk1.events.extract preSnkIdx gSnk1.events.size).any (fun e =>
      match e.change with
      | .rules (.cast (.announced _ _ _ costs)) =>
        costs == #[.sneak snkAtkId (some (.player opp23))]
      | _ => false)

  -- 3b. Activated ability reduced from `{1}` to `{0}` (with no tap cost) finishes immediately and records `CastEvent.announced`!
  let oneManaArt23 : CardDef := {
    name := "Phase23 Zeroed Activator"
    types := #[.artifact]
    subtypes := #["Equipment"]
    activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 1 }
      costReductionPerEquipment := 1
      effect := Effect.draw 1
    }]
  }
  let gRedAb0 : Game := addPermanent afterDraw oneManaArt23 me me
  let actArtId := (gRedAb0.battlefield.filter (·.name == "Phase23 Zeroed Activator"))[0]!.id
  let preRedAbIdx := gRedAb0.events.size
  let gRedAb1 : Game := mustApply gRedAb0 me (.activate actArtId 0)
  let reducedActivateAnnouncedOk : Bool :=
    gRedAb1.pending == .none &&
    gRedAb1.stack.size == 1 &&
    (gRedAb1.events.extract preRedAbIdx gRedAb1.events.size).any (fun e =>
      match e.change with | .rules (.cast (.abilityActivated ..)) => true | _ => false)

  -- 3c. Spell with `additionalCostSacrificeCreature` records `CastEvent.announced` `costs := #[.sacrifice sacId]`!
  let sacSpellDef23 : CardDef := {
    name := "Phase23 Sac Sorcery"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    additionalCostSacrificeCreature := true
    spellEffect := some (Effect.draw 1)
  }
  let gSacSp0 : Game := insertObject (addPermanent afterDraw bear me me) sacSpellDef23 me (.hand me)
  let sacVictimId := (gSacSp0.battlefield.filter (·.name == bear.name))[0]!.id
  let sacSpCardId := (gSacSp0.player me).hand.back!
  let preSacSpIdx := gSacSp0.events.size
  let gSacSp1 : Game :=
    mustApply (mustApply (mustApply gSacSp0 me (.cast sacSpCardId)) me .pay) me (.sacrifice sacVictimId)
  let sacSpellAnnouncedOk : Bool :=
    (gSacSp1.events.extract preSacSpIdx gSacSp1.events.size).any (fun e =>
      match e.change with
      | .rules (.cast (.announced _ _ _ costs)) => costs == #[.sacrifice sacVictimId]
      | _ => false)

  -- 3d. CR 106.6 `fromTreasure` provenance does NOT preempt `.elf`, `.cantNonartifact` pays Ward/counter but NOT non-artifact spell,
  --     and `payWard` / `payOrLetCounter` do NOT credit `manaSpentOn` to the targeted `spellId`!
  let poolTreasureAndElf : ManaPool :=
    (({} : ManaPool).addUnits #[
      { mana := .colored .red, fromTreasure := true },
      { mana := .colored .green, restriction := some .elf }
    ])
  let afterElfGeneric := poolTreasureAndElf.pay? (ManaCost.ofGeneric 1) (allowElfRestricted := true)
  let poolCantNonart : ManaPool :=
    ({} : ManaPool).addUnits #[{ mana := .colored .blue, restriction := some .cantNonartifact }]
  let manaPriorityAndRestrOk : Bool :=
    afterElfGeneric.any (fun p => p.units.size == 1 && p.units[0]!.fromTreasure && p.units[0]!.restriction.isNone) &&
    !poolCantNonart.canPay (ManaCost.ofGeneric 1) &&
    poolCantNonart.canPay (ManaCost.ofGeneric 1) (allowCantNonartifact := true)

  let gWardMana0 : Game :=
    let g := insertObject afterDraw bear me .stack (some me)
    let targetSpId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
    let wardPermG := addPermanent (g.putStackEntry me targetSpId) hero opp23 opp23
    let wardPermId := (wardPermG.battlefield.filter (·.name == hero.name))[0]!.id
    let wardPermG := wardPermG.addManaUnits me #[{ mana := .colored .blue, restriction := some .cantNonartifact }]
      (cause := testCause)
    wardPermG.changes #[
      .pushContinuationFrame { resolvingContext := some (some wardPermId, opp23) },
      .pending (.payWard me targetSpId (.genericMana 1))
    ]
  let targetSpId23 := gWardMana0.stack[0]!.objectId
  let gWardMana1 : Game := mustApply gWardMana0 me .payGeneric
  let wardManaProvenanceOk : Bool :=
    manaPriorityAndRestrOk &&
    GameEvent.manaSpentOn gWardMana1.events targetSpId23 == 0

  mustHold23 "3a.zeroSneakOk" zeroSneakOk &&
  mustHold23 "3b.reducedActivateAnnouncedOk" reducedActivateAnnouncedOk &&
  mustHold23 "3c.sacSpellAnnouncedOk" sacSpellAnnouncedOk &&
  mustHold23 "3d.wardManaProvenanceOk" wardManaProvenanceOk &&
  mustHold23 "3.replay" ([gSnk1, gRedAb1, gSacSp1, gWardMana1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. `equipWorthy` / `equipSubtype` per-ability target fidelity, face-down Morph casting &
--    special-action Layer-6 ability indexing, face-up stack-copy `copiable`, and self-dies triggers.
#guard
  -- 4a. Equipment with both `equipWorthyAbility` (idx 0) and `equipAbility` (idx 1):
  --     idx 1 equips non-worthy Bear; idx 0 targets worthy Hero, and fizzles at CR 608.2b if Hero becomes Villain!
  let dualEquipDef : CardDef := {
    name := "Phase23 Hammer"
    types := #[.artifact]
    subtypes := #["Equipment"]
    activatedAbilities := #[
      equipWorthyAbility ManaCost.empty,
      equipAbility ManaCost.empty
    ]
  }
  let worthyHeroDef : CardDef := {
    hero with
    name := "Phase23 Worthy Hero"
    manaCost := ManaCost.ofColor .white
    supertypes := #[.legendary]
  }
  let gEq0 : Game := addPermanent (addPermanent (addPermanent afterDraw dualEquipDef me me) bear me me) worthyHeroDef me me
  let hammerId := (gEq0.battlefield.filter (·.name == "Phase23 Hammer"))[0]!.id
  let eqBearId := (gEq0.battlefield.filter (·.name == bear.name))[0]!.id
  let eqWorthyId := (gEq0.battlefield.filter (·.name == "Phase23 Worthy Hero"))[0]!.id
  let worthyRejectsBear : Bool := !(mustApply gEq0 me (.activate hammerId 0) |>.apply me (.target (.permanent eqBearId))).isOk
  let gPlainEq : Game := (mustApply (mustApply gEq0 me (.activate hammerId 1)) me (.target (.permanent eqBearId))).resolveTop
  let gWorthyStack : Game := mustApply (mustApply gEq0 me (.activate hammerId 0)) me (.target (.permanent eqWorthyId))
  -- Make `eqWorthyId` Villain in Layer 4 before `equipWorthy` resolves -> no longer worthy -> fizzles!
  let gWorthyVillain : Game :=
    (gWorthyStack.createEffect (.layered (.objects #[eqWorthyId]) (.types .add #[] #[.villain] #[]) .untilEndOfTurn)
      (cause := some testCause)).resolveTop
  let equipFidelityOk : Bool :=
    worthyRejectsBear &&
    (gPlainEq.object! hammerId).attachedTo == some eqBearId &&
    (gWorthyVillain.object! hammerId).attachedTo.isNone

  -- 4b. Face-down Morph casting when front face is a targetless Sorcery, plus Layer-6 ability + CR 702.61b turn-face-up on face-down permanent!
  let morphSorcDef : CardDef := {
    name := "Phase23 Morph Sorcery"
    manaCost := ManaCost.ofColor .blue
    types := #[.sorcery]
    morph := some ManaCost.empty
    spellEffect := some (Effect.canonicalDestroy .creature) -- no creatures in play!
  }
  let elfLooterDef : CardDef := {
    bear with
    name := "Phase23 Gy Elf"
    subtypes := #["Elf"]
    activatedAbilities := #[{ cost := {}, effect := Effect.draw 1 }]
  }
  let splitEnablerDef : CardDef := {
    bear with
    name := "Phase23 Split Enabler"
    staticAbilities := #[.instantSorcerySplitSecond]
  }
  let gMphCast0 : Game := (insertObject afterDraw morphSorcDef me (.hand me)).addMana me .colorless 3
  let mphSorcId := (gMphCast0.player me).hand.back!
  let gMphProposed : Game := mustApply gMphCast0 me (.cast mphSorcId)
  let frontFaceRejected : Bool := !(gMphProposed.apply me (.announceKicker false)).isOk
  let gMphOnBf : Game := (mustApply (mustApply gMphProposed me (.announceKicker true)) me .pay).resolveTop
  let fdPermId := (gMphOnBf.battlefield.filter (·.status.faceDown))[0]!.id
  -- Grant `.copyActivatedFromGySubtype .elf` in Layer 6 with `elfLooterDef` in graveyard -> `[morphAb, drawAb]`!
  let gFdLayer6 : Game :=
    let g := insertObject gMphOnBf elfLooterDef me (.graveyard me)
    g.createEffect (.layered (.objects #[fdPermId])
      (.abilities { staticAbilities := #[.copyActivatedFromGySubtype .elf] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let fdAbs := gFdLayer6.activatedAbilitiesOf (gFdLayer6.object! fdPermId)
  -- Activate index 1 (Layer-6 granted `draw 1`) while face down -> goes on stack!
  let gFdAct1 : Game := mustApply gFdLayer6 me (.activate fdPermId 1)
  -- Put a split-second instant on the stack: index 0 (`turnFaceUp` special action) is STILL legal (CR 702.61b)!
  let gFdSplit : Game :=
    let g := addPermanent (insertObject gFdLayer6 shock me .stack (some me)) splitEnablerDef me me
    let spId := (g.objects.filter (fun o => o.name == shock.name && o.zone == .stack))[0]!.id
    g.putStackEntry me spId
  let morphSpecialAllowedUnderSplit : Bool :=
    gFdSplit.splitSecondOnStack &&
    gFdSplit.canActivate me (gFdSplit.object! fdPermId) fdAbs[0]! &&
    !gFdSplit.canActivate me (gFdSplit.object! fdPermId) fdAbs[1]!
  let morphAndLayer6Ok : Bool :=
    frontFaceRejected &&
    fdAbs.size == 2 &&
    gFdAct1.stack.size == 1 &&
    (gFdAct1.object! fdPermId).status.faceDown &&
    morphSpecialAllowedUnderSplit

  -- 4c. Face-up `copyStackSpell` preserves `printed`, and non-`"another"` `.creatureYouControlDies` self-triggers!
  let gCopyFace0 : Game :=
    let g := insertObject afterDraw shock me .stack (some me)
    let sid := (g.objects.filter (fun o => o.name == shock.name && o.zone == .stack))[0]!.id
    (g.putStackEntry me sid).setStackEntryTargets sid #[.player opp23]
  let origShockId := gCopyFace0.stack[0]!.objectId
  let gCopyFace1 : Game := gCopyFace0.copyStackSpell (gCopyFace0.object! origShockId) me
  let copyShockObj := gCopyFace1.object! gCopyFace1.stack.back!.objectId
  let selfDiesDef : CardDef := {
    bear with
    name := "Phase23 Self Dies"
    triggeredAbilities := #[
      .triggered .creatureYouControlDies { resolution := .gainLife (.fixed 2), phrase := "You gain 2 life." } {}
    ]
  }
  let gSelfDies0 : Game := addPermanent afterDraw selfDiesDef me me
  let sdId := (gSelfDies0.battlefield.filter (·.name == "Phase23 Self Dies"))[0]!.id
  let gSelfDies1 : Game := gSelfDies0.destroyPermanent (gSelfDies0.object! sdId)
  let copyAndSelfDiesOk : Bool :=
    copyShockObj.printed.name == shock.name &&
    gSelfDies1.waitingTriggers.size == 1 &&
    gSelfDies1.waitingTriggers[0]!.source.id == sdId

  mustHold23 "4a.equipFidelityOk" equipFidelityOk &&
  mustHold23 "4b.morphAndLayer6Ok" morphAndLayer6Ok &&
  mustHold23 "4c.copyAndSelfDiesOk" copyAndSelfDiesOk &&
  mustHold23 "4.replay" ([gPlainEq, gWorthyVillain, gMphOnBf, gFdAct1, gCopyFace1, gSelfDies1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. Shockland `n ≤ life < 2 * n` CR 616.1 re-entry, CR 616.1c->616.1e Clone copying `entersTapped`,
--    unified CR 616.1g ETB counter evaluation, CR 614.12 simultaneous lord isolation, and
--    single-prompt batched `replaceTokenCreationChoice`.
#guard
  -- 5a. Shockland (`entersTappedUnlessPayLife := some 2`) at `life == 3` (`2 ≤ life < 4`) alongside competing ETB effect:
  --     paying 2 life drops `life` to 1, and CR 616.1 loop re-entry does NOT re-offer `entersTappedSelf`!
  let shockLand23 : CardDef := { forest with name := "Phase23 Shock", entersTappedUnlessPayLife := some 2 }
  let gShk0 : Game :=
    let g := insertObject (afterDraw.loseLife me 17 (cause := some testCause)) shockLand23 me (.hand me)
    g.createEffect (.replacement {
      id := { kind := .entersWithExtraCounters }
      source := none, controller := some me, affectedPlayer := me
      kind := .entersWithExtraCounters none .charge 1 }) (cause := some testCause)
  let shkHandId := (gShk0.player me).hand.back!
  let gShk1 : Game := mustApply gShk0 me (.playLand shkHandId)
  let gShk2 : Game :=
    match gShk1.pending with
    | .chooseReplacement _ cs =>
      match cs.find? (fun r => r.kind == .entersUntappedPayLife 2) with
      | some payRid => mustApply gShk1 me (.chooseReplacement payRid)
      | none => gShk1
    | _ => gShk1
  let shkPerm := (gShk2.battlefield.filter (·.name == "Phase23 Shock"))[0]!
  let shockReentryOk : Bool :=
    (gShk2.player me).life == 1 &&
    !shkPerm.status.tapped &&
    shkPerm.status.counterCount .charge == 1

  -- 5b. CR 616.1c -> 616.1e: untapped card entering as a copy of a tapped-entering creature enters TAPPED!
  let tappedTargetDef : CardDef := { bear with name := "Phase23 Tapped Template", entersTapped := true }
  let untappedCloneCard : CardDef := { hero with name := "Phase23 Untapped Clone", entersTapped := false }
  let gCln0 : Game :=
    let g := insertObject afterDraw untappedCloneCard me (.hand me)
    let cid := (g.player me).hand.back!
    let g := g.createEffect (.replacement {
      id := { kind := .entersAsCopy }, source := none, controller := some me, affectedPlayer := me
      kind := .entersAsCopy none tappedTargetDef }) (cause := some testCause)
    (g.putOntoBattlefield cid me (cause := some testCause)).1
  let clnPerm := (gCln0.battlefield.filter (·.name == "Phase23 Tapped Template"))[0]!
  let cloneTappedTierOk : Bool := clnPerm.status.tapped

  -- 5c. Unified CR 616.1g ETB counter evaluation (`1` printed + `1` extra under `+1` `modifyCountersPut` => `3`, NOT `4`)
  --     AND CR 614.12 simultaneous batch isolation (`Doc Samson` co-entering with `1`-counter creature => `1`, NOT `2`)!
  let oneCounterBear : CardDef := { bear with name := "Phase23 Counter Bear", entersWithPlusOneCounters := 1 }
  let gUnif0 : Game :=
    let g := insertObject afterDraw oneCounterBear me (.hand me)
    let cid := (g.player me).hand.back!
    let g := g.createEffect (.replacement {
      id := { kind := .entersWithExtraCounters }, source := none, controller := some me, affectedPlayer := me
      kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)
    let g := g.createEffect (.replacement {
      id := { kind := .addCountersPut }, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut none (some .plusOnePlusOne) (add := 1) (mult := 1) }) (cause := some testCause)
    (g.putOntoBattlefield cid me (cause := some testCause)).1
  let unifCounters := (gUnif0.battlefield.filter (·.name == "Phase23 Counter Bear"))[0]!.status.plusOnePlusOne
  let docLord23 : CardDef := { bear with name := "Phase23 CoEntering Doc", staticAbilities := #[.extraCounterOnPermanents] }
  let gSimEtb0 : Game :=
    let g := insertObject (insertObject afterDraw docLord23 me (.hand me)) oneCounterBear me (.hand me)
    let h := (g.player me).hand
    let docH := h[h.size - 2]!
    let bearH := h[h.size - 1]!
    g.withBatch (some testCause) fun g =>
      let (g, _) := g.putOntoBattlefield docH me (cause := some testCause)
      (g.putOntoBattlefield bearH me (cause := some testCause)).1
  let simBearCounters := (gSimEtb0.battlefield.filter (·.name == "Phase23 Counter Bear"))[0]!.status.plusOnePlusOne
  let etbCountersAndIsoOk : Bool :=
    unifCounters == 3 &&
    simBearCounters == 1

  -- 5d. Batched multi-token `createKindTokens me .food 2` with two non-commuting token replacements prompts ONCE!
  let rBecomeDragon : ReplacementId := { kind := .artifactTokensBecomeDragons, object := some ⟨991⟩ }
  let rExtraFood : ReplacementId := { kind := .foodAlsoCreatesTreasure, object := some ⟨992⟩ }
  let gTok0 : Game :=
    let g := afterDraw.createEffect (.replacement {
      id := rBecomeDragon, source := none, controller := some me, affectedPlayer := me
      kind := .artifactTokensBecome me Game.dragon55flyingToken }) (cause := some testCause)
    g.createEffect (.replacement {
      id := rExtraFood, source := none, controller := some me, affectedPlayer := me
      kind := .createExtraTokenWithFood me treasureToken }) (cause := some testCause)
  let gTokPaused : Game := gTok0.createKindTokens me .food 2 (cause := some testCause)
  let gTokDone : Game := mustApply gTokPaused me (.chooseReplacement rExtraFood)
  let gTokDoneAlt : Game := mustApply gTokPaused me (.chooseReplacement rBecomeDragon)
  let batchedMultiTokenOk : Bool :=
    (match gTokPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gTokDone.pending == .none &&
    (gTokDone.battlefield.filter (·.name == "Dragon")).size == 4 &&
    gTokDoneAlt.pending == .none &&
    (gTokDoneAlt.battlefield.filter (·.name == "Dragon")).size == 2

  mustHold23 "5a.shockReentryOk" shockReentryOk &&
  mustHold23 "5b.cloneTappedTierOk" cloneTappedTierOk &&
  mustHold23 "5c.etbCountersAndIsoOk" etbCountersAndIsoOk &&
  mustHold23 "5d.batchedMultiTokenOk" batchedMultiTokenOk &&
  mustHold23 "5.replay" ([gShk2, gCln0, gUnif0, gSimEtb0, gTokPaused, gTokDone, gTokDoneAlt].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 702.26g–h nested & direct+indirect phasing, batched Saga lore counters, CR 121.2c APNAP
--    `twoPlayersEachDraw`, CR 810 2HG shared life / first-turn draw skip / shared poison,
--    simultaneous CR 704.3 SBA before `pl.lost`, and `EventObject.blockingIds` LKI reconstruction.
#guard
  -- 6a. CR 702.26g–h: direct+indirect collapse (`#[host, eq]` -> `eq.status.phasedWith == some host`) & nested chain!
  let eqA23 : CardDef := { name := "Phase23 EqA", types := #[.artifact], subtypes := #["Equipment"] }
  let auraOnArt23 : CardDef := aura "Phase23 ArtAura" ManaCost.empty "Enchant artifact or non-Aura enchantment"
  let gPh0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) eqA23 me me) auraOnArt23 me me
  let phHost := (gPh0.battlefield.filter (·.name == bear.name))[0]!.id
  let phEq := (gPh0.battlefield.filter (·.name == "Phase23 EqA"))[0]!.id
  let phAura := (gPh0.battlefield.filter (·.name == "Phase23 ArtAura"))[0]!.id
  let gPh1 : Game := (gPh0.attachSourceTo (gPh0.object! phEq) (gPh0.object! phHost)).attachSourceTo
    (gPh0.object! phAura) (gPh0.object! phEq)
  let gPhOut : Game := gPh1.phaseOutPermanents #[gPh1.object! phHost, gPh1.object! phEq] (cause := some testCause)
  let gPhIn : Game := gPhOut.phaseInControlled me
  let phasingNestedAndCollapseOk : Bool :=
    (gPhOut.object! phHost).status.phasedOut &&
    (gPhOut.object! phHost).status.phasedWith.isNone &&
    (gPhOut.object! phEq).status.phasedOut &&
    (gPhOut.object! phEq).status.phasedWith == some phHost &&
    (gPhOut.object! phAura).status.phasedOut &&
    (gPhOut.object! phAura).status.phasedWith == some phEq &&
    !(gPhIn.object! phHost).status.phasedOut &&
    !(gPhIn.object! phEq).status.phasedOut &&
    !(gPhIn.object! phAura).status.phasedOut &&
    (gPhIn.object! phEq).attachedTo == some phHost &&
    (gPhIn.object! phAura).attachedTo == some phEq

  -- 6b. Batched `addLoreAfterDrawStep` across 2 Sagas & CR 121.2c APNAP `twoPlayersEachDraw opp23 me`!
  let sagaDef23 : CardDef :=
    saga "Phase23 Saga" ManaCost.empty "" "I" #[chapter "I" "You gain 1 life." (Effect.gainLife 1)]
  let gSg0 : Game := addPermanent (addPermanent afterDraw sagaDef23 me me) sagaDef23 me me
  let preSgIdx := gSg0.events.size
  let gSg1 : Game := gSg0.addLoreAfterDrawStep
  let sgBatches := (gSg1.events.extract preSgIdx gSg1.events.size).filterMap fun e =>
    match e.change with | .rules (.permanent (.counters _ .lore (.put 1) _)) => some e.batch | _ => none
  let preDrawIdx := afterDraw.events.size
  let gTwoDraw : Game :=
    match afterDraw.twoPlayersEachDraw opp23 me with
    | .ok g => g
    | .error e => panic! e
  let drawPlayers := (gTwoDraw.events.extract preDrawIdx gTwoDraw.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) (.hand p) (.draw _) ..)) => some p
    | _ => none
  let sagaBatchAndApnapDrawOk : Bool :=
    sgBatches.size == 2 && sgBatches[0]!.isSome && sgBatches[0]! == sgBatches[1]! &&
    drawPlayers == #[me, opp23]

  -- 6c. CR 810 2HG: starting life 30, both starting teammates skip first-turn draw, shared life sync,
  --     poison `.removed` spill across teammates, and team-once poison proliferate!
  let g2hStart : Game :=
    match Start.start {
      seats := #[
        { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
        { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
        { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
        { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
      ]
      format := .constructed
      seed := 223
      startingPlayer := some 0
    } with
    | .ok g => keepOpeningHands g 30
    | .error e => panic! e
  let start30Ok : Bool := g2hStart.players.all (·.life == 30)
  let skipSeat0 : Bool := g2hStart.skipsFirstDraw
  let g2hSeat1 : Game := g2hStart.startNextTurnAndBegin
  let skipSeat1 : Bool := g2hSeat1.activePlayer == ⟨1⟩ && g2hSeat1.skipsFirstDraw
  let g2hSeat2 : Game := g2hSeat1.startNextTurnAndBegin
  let noSkipSeat2 : Bool := g2hSeat2.activePlayer == ⟨2⟩ && !g2hSeat2.skipsFirstDraw
  let pre2hLifeIdx := g2hSeat2.events.size
  let g2hLost4 : Game := g2hSeat2.loseLife ⟨0⟩ 4 (cause := some testCause)
  let lifeLostEvts := (g2hLost4.events.extract pre2hLifeIdx g2hLost4.events.size).filter fun e =>
    match e.change with | .rules (.life (.lost ..)) => true | _ => false
  let g2hPsn0 : Game := g2hLost4.record (GameEvent.poisoned g2hLost4.turnNumber ⟨0⟩ 3 (cause := testCause))
  let g2hPsnSpill : Game := g2hPsn0.record
    (GameEvent.playerCounters g2hPsn0.turnNumber ⟨1⟩ .poison (.removed 2) (cause := testCause))
  let g2hProlif0 : Game := g2hPsnSpill.change (.pending (.chooseProliferate ⟨2⟩ 1))
  let g2hProlif1 : Game := mustApply g2hProlif0 ⟨2⟩ (.targets #[.player ⟨0⟩, .player ⟨1⟩])
  let twoHgAllOk : Bool :=
    start30Ok && skipSeat0 && skipSeat1 && noSkipSeat2 &&
    (g2hLost4.player ⟨0⟩).life == 26 && (g2hLost4.player ⟨1⟩).life == 26 &&
    lifeLostEvts.size == 1 &&
    g2hPsnSpill.teamPoison ⟨0⟩ == 1 &&
    g2hProlif1.teamPoison ⟨0⟩ == 2

  -- 6d. Simultaneous CR 704.3 SBA before `pl.lost` (in 3-player game so game continues) & `EventObject.blockingIds` LKI!
  let zeroSpirit23 : CardDef := { creature "Phase23 0/0 Spirit" ManaCost.empty #["Spirit"] 0 0 with }
  let watcherAnyDies23 : CardDef := {
    bear with
    name := "Phase23 Watcher"
    triggeredAbilities := #[
      .triggered .creatureYouControlDies { resolution := .gainLife (.fixed 1), phrase := "Gain 1." } {}
    ]
  }
  let g3pSba0 : Game :=
    let g := addPermanent (addPermanent mkThreePlayer21 watcherAnyDies23 ⟨2⟩ ⟨2⟩) zeroSpirit23 ⟨2⟩ ⟨2⟩
    g.loseLife ⟨1⟩ 20 (cause := some testCause)
  let g3pSba1 : Game := g3pSba0.checkSBA
  let sbaSimultaneousOk : Bool :=
    (g3pSba1.player ⟨1⟩).lost &&
    (g3pSba1.player ⟨1⟩).leftTheGame &&
    !(g3pSba1.battlefield.any (·.name == "Phase23 0/0 Spirit")) &&
    g3pSba1.waitingTriggers.size == 1

  let gBlkLki0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) bear opp23 opp23
  let atkA := (gBlkLki0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
  let atkB := (gBlkLki0.battlefield.filter (fun o => o.name == hero.name && o.controller == some me))[0]!.id
  let blkC := (gBlkLki0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp23))[0]!.id
  let blkSnapPre := gBlkLki0.snapshot (gBlkLki0.object! blkC)
  let gBlkLki1 : Game := gBlkLki0.record
    (GameEvent.blockersDeclared gBlkLki0.turnNumber opp23 #[(blkSnapPre, atkA), (blkSnapPre, atkB)])
  let blkSnap := gBlkLki1.snapshot (gBlkLki1.object! blkC)
  let blkReconstructed := Game.damageSourceObjectFromLki blkSnap
  let blockingIdsLkiOk : Bool :=
    blkSnap.blockingIds == #[atkA, atkB] &&
    blkReconstructed.status.blocking == #[atkA, atkB]

  mustHold23 "6a.phasingNestedAndCollapseOk" phasingNestedAndCollapseOk &&
  mustHold23 "6b.sagaBatchAndApnapDrawOk" sagaBatchAndApnapDrawOk &&
  mustHold23 "6c.twoHgAllOk" twoHgAllOk &&
  mustHold23 "6d.sbaSimultaneousOk" sbaSimultaneousOk &&
  mustHold23 "6e.blockingIdsLkiOk" blockingIdsLkiOk &&
  mustHold23 "6.replay" ([gPhOut, gPhIn, gSg1, gTwoDraw, g2hStart, g2hSeat1, g2hSeat2, g2hLost4, g2hPsnSpill, g2hProlif1, g3pSba1, gBlkLki1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase23EventAlignment

section Phase24Item1EventAlignment

def opp24i1 : PlayerId := ⟨1⟩

def mustHold24i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 24 item 1 guard failed: {label}"

def exA24i1 : ReplacementId := { kind := .exileOppDeath, object := some ⟨1981⟩ }
def exB24i1 : ReplacementId := { kind := .exileOppDeath, object := some ⟨1982⟩ }

/-- Add one (or, with `twice`, two competing) `.exileInsteadOfGraveyard` replacements;
two force a CR 616.1 `Pending.chooseReplacement` pause on a graveyard-bound move. -/
def withGyExile24i1 (g : Game) (twice : Bool) : Game :=
  let g := g.createEffect
    (.replacement { id := exA24i1, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
    (cause := some testCause)
  if twice then
    g.createEffect
      (.replacement { id := exB24i1, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  else g

def rAdd24i1 : ReplacementId := { kind := .addCountersPut, object := some ⟨1985⟩ }
def rMul24i1 : ReplacementId := { kind := .multiplyCountersPut, object := some ⟨1986⟩ }

/-- With `twice`, two competing counter-put replacements on `oid` (add 1, double) that
pause on `Pending.chooseReplacement`; otherwise a single `mult := 0` replacement
that leaves no counters placed (CR 122.1 / 614.6 / 616.1). -/
def withCounterReps24i1 (g : Game) (oid : ObjectId) (kind : CounterKind) (twice : Bool) : Game :=
  if twice then
    let g := g.createEffect (.replacement {
      id := rAdd24i1, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut (some oid) (some kind) (add := 1) (mult := 1) }) (cause := some testCause)
    g.createEffect (.replacement {
      id := rMul24i1, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut (some oid) (some kind) (add := 0) (mult := 2) }) (cause := some testCause)
  else
    g.createEffect (.replacement {
      id := rMul24i1, source := none, controller := some me, affectedPlayer := me
      kind := .modifyCountersPut (some oid) (some kind) (add := 0) (mult := 0) }) (cause := some testCause)

def newLogs24i1 (g0 g : Game) : Array String := g.log.extract g0.log.size g.log.size

def paused24i1 (g : Game) : Bool :=
  match g.pending with | .chooseReplacement .. => true | _ => false

/-- Answer a pending replacement choice with its first option. -/
def resolveChoice24i1 (g : Game) : Game :=
  match g.pending with
  | .chooseReplacement p cs => mustApply g p (.chooseReplacement cs[0]!)
  | _ => g

def replayOk24i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. Pause-safe `.toHand` (CR 400.3 owner's hand / 614.6 arrival logs), no mid-resolution
--    priority/SBAs in `.eachOppDiscardThenPlusOne` (CR 117.3b / 608.2c,n / 704.4), and
--    deferred counter logs (CR 122.1 / 614.6 / 616.1).
#guard
  -- 1a. `.toHand` puts an opponent-owned card into its OWNER's hand and logs accordingly:
  let gTH0 : Game :=
    insertObject (insertObject afterDraw bear opp24i1 (.graveyard opp24i1)) hero me (.graveyard me)
  let thOppId := (gTH0.objects.filter (fun o => o.name == bear.name && o.zone == .graveyard opp24i1))[0]!.id
  let thMyId := (gTH0.objects.filter (fun o => o.name == hero.name && o.zone == .graveyard me))[0]!.id
  let gTH1 : Game := gTH0.finishChooseCards me #[thOppId, thMyId] (.toHand false)
  let thLogs := newLogs24i1 gTH0 gTH1
  let ownerHandOk : Bool :=
    (gTH1.followMovedToZone? thOppId (· == .hand opp24i1)).isSome &&
    (gTH1.followMovedToZone? thMyId (· == .hand me)).isSome &&
    thLogs.any (·.contains s!"puts {bear.name} into {(gTH1.player opp24i1).name}'s hand") &&
    thLogs.any (·.contains s!"puts {hero.name} into their hand")

  -- 1b. A stack-leave replacement choice on the first chosen card pauses BEFORE the second
  --     card moves; the exiled card logs no hand move, the second card logs on arrival:
  let stA : ReplacementId := { kind := .flashbackExile, object := some ⟨1983⟩ }
  let stB : ReplacementId := { kind := .flashbackExile, object := some ⟨1984⟩ }
  let gTHP0 : Game :=
    let g := insertObject (insertObject afterDraw bear me .stack (some me)) hero me (.graveyard me)
    let spId := (g.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    let g := g.createEffect (.replacement {
      id := stA, affectedPlayer := me, kind := .exileInsteadOfStackLeave none }) (cause := some testCause)
    g.createEffect (.replacement {
      id := stB, affectedPlayer := me, kind := .exileInsteadOfStackLeave none }) (cause := some testCause)
  let thSpId := (gTHP0.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
  let thGyId := (gTHP0.objects.filter (fun o => o.name == hero.name && o.zone == .graveyard me))[0]!.id
  let gTHP1 : Game := gTHP0.finishChooseCards me #[thSpId, thGyId] (.toHand false)
  let gTHP2 : Game := resolveChoice24i1 gTHP1
  let thpLogs := newLogs24i1 gTHP0 gTHP2
  let toHandPauseOk : Bool :=
    paused24i1 gTHP1 &&
    (gTHP1.findObject? thGyId).any (·.zone == .graveyard me) &&
    !(newLogs24i1 gTHP0 gTHP1).any (·.contains "into their hand") &&
    !paused24i1 gTHP2 &&
    (gTHP2.followMovedToZone? thSpId (· == .exile)).isSome &&
    (gTHP2.followMovedToZone? thGyId (· == .hand me)).isSome &&
    !thpLogs.any (·.contains s!"puts {bear.name} into") &&
    thpLogs.any (·.contains s!"puts {hero.name} into their hand") &&
    thpLogs.any (·.contains s!"{bear.name} is exiled instead of leaving the stack (CR 614.6)")

  -- 1c. `.eachOppDiscardThenPlusOne` with empty-handed opponents: +1/+1 on the source but
  --     no SBA check mid-resolution (a lethally damaged creature stays on the battlefield):
  let gEO0 : Game :=
    let g := (afterDraw.player opp24i1).hand.foldl (fun acc hid =>
      (acc.move hid .exile none (cause := some testCause)).1) afterDraw
    let g := addPermanent (addPermanent g bear me me) hero opp24i1 opp24i1
    let heroId := (g.battlefield.filter (·.name == hero.name))[0]!.id
    setMarkedDamage g heroId 5
  let eoSrcId := (gEO0.battlefield.filter (·.name == bear.name))[0]!.id
  let eoHeroId := (gEO0.battlefield.filter (·.name == hero.name))[0]!.id
  let gEO1 : Game := gEO0.applyUnifiedAbility me Effect.eachOppDiscardThenPlusOne #[] (some eoSrcId)
  let noMidResolutionSbaOk : Bool :=
    (gEO1.player opp24i1).hand.isEmpty &&
    (gEO1.object! eoSrcId).status.plusOnePlusOne == 1 &&
    (gEO1.findObject? eoHeroId).any (·.isOnBattlefield)

  -- 1d. `.putCauseCountersOnSource`: no log when replacements leave no counters; across a
  --     counter-put replacement pause the log is deferred until the counters land:
  let fraCause (g : Game) (srcId : ObjectId) : Game :=
    let abId : ObjectId := ⟨g.nextObjectId⟩
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId (g.snapshot (g.object! srcId)) me
      (spec := {
        sourceId := some srcId
        fraCauseId := some ⟨1990⟩
        fraCauseStatus := some { counters := #[(.plusOnePlusOne, 2)] } }))
    g.changes #[.pushContinuationFrame {}, .resolvingAbility (some abId)]
  let gPC0 : Game := addPermanent afterDraw bear me me
  let pcSrcId := (gPC0.battlefield.filter (·.name == bear.name))[0]!.id
  let gPCZero0 : Game := fraCause (withCounterReps24i1 gPC0 pcSrcId .plusOnePlusOne false) pcSrcId
  let gPCZero1 : Game :=
    gPCZero0.applyFraAbility me Effect.eachOppDiscardThenPlusOne .putCauseCountersOnSource #[] (some pcSrcId)
  let gPCPause0 : Game := fraCause (withCounterReps24i1 gPC0 pcSrcId .plusOnePlusOne true) pcSrcId
  let gPCPause1 : Game :=
    gPCPause0.applyFraAbility me Effect.eachOppDiscardThenPlusOne .putCauseCountersOnSource #[] (some pcSrcId)
  let gPCPause2 : Game := resolveChoice24i1 gPCPause1
  let gPCNorm0 : Game := fraCause gPC0 pcSrcId
  let gPCNorm1 : Game :=
    gPCNorm0.applyFraAbility me Effect.eachOppDiscardThenPlusOne .putCauseCountersOnSource #[] (some pcSrcId)
  let causeCountersLogOk : Bool :=
    (gPCZero1.object! pcSrcId).status.plusOnePlusOne == 0 &&
    !(newLogs24i1 gPCZero0 gPCZero1).any (·.contains "Counters are put on") &&
    paused24i1 gPCPause1 &&
    !(newLogs24i1 gPCPause0 gPCPause1).any (·.contains "Counters are put on") &&
    (gPCPause2.object! pcSrcId).status.plusOnePlusOne > 0 &&
    (newLogs24i1 gPCPause0 gPCPause2).any (·.contains "Counters are put on") &&
    (gPCNorm1.object! pcSrcId).status.plusOnePlusOne == 2 &&
    (newLogs24i1 gPCNorm0 gPCNorm1).any (·.contains "Counters are put on")

  -- 1e. `.mayMoveAllCounters` accept: the same gating / deferral for "All counters move":
  let gMv0 : Game :=
    let g := insertObject afterDraw bear me .battlefield (some me)
      (status := { counters := #[(.plusOnePlusOne, 2)] })
    addPermanent g hero me me
  let mvSrcId := (gMv0.battlefield.filter (·.name == bear.name))[0]!.id
  let mvDstId := (gMv0.battlefield.filter (·.name == hero.name))[0]!.id
  let askMove (g : Game) : Game :=
    g.changes #[.pushContinuationFrame {}, .pending (.fraChoice me (.mayMoveAllCounters mvSrcId mvDstId))]
  let gMvZero0 : Game := askMove (withCounterReps24i1 gMv0 mvDstId .plusOnePlusOne false)
  let gMvZero1 : Game := mustApply gMvZero0 me .accept
  let gMvPause0 : Game := askMove (withCounterReps24i1 gMv0 mvDstId .plusOnePlusOne true)
  let gMvPause1 : Game := mustApply gMvPause0 me .accept
  let gMvPause2 : Game := resolveChoice24i1 gMvPause1
  let gMvNorm0 : Game := askMove gMv0
  let gMvNorm1 : Game := mustApply gMvNorm0 me .accept
  let moveCountersLogOk : Bool :=
    (gMvZero1.object! mvDstId).status.plusOnePlusOne == 0 &&
    !(newLogs24i1 gMvZero0 gMvZero1).any (·.contains "All counters move") &&
    paused24i1 gMvPause1 &&
    !(newLogs24i1 gMvPause0 gMvPause1).any (·.contains "All counters move") &&
    (gMvPause2.object! mvDstId).status.plusOnePlusOne > 0 &&
    (newLogs24i1 gMvPause0 gMvPause2).any (·.contains "All counters move") &&
    (gMvNorm1.object! mvDstId).status.plusOnePlusOne == 2 &&
    (newLogs24i1 gMvNorm0 gMvNorm1).any (·.contains "All counters move")

  mustHold24i1 "1a.ownerHandOk" ownerHandOk &&
  mustHold24i1 "1b.toHandPauseOk" toHandPauseOk &&
  mustHold24i1 "1c.noMidResolutionSbaOk" noMidResolutionSbaOk &&
  mustHold24i1 "1d.causeCountersLogOk" causeCountersLogOk &&
  mustHold24i1 "1e.moveCountersLogOk" moveCountersLogOk &&
  mustHold24i1 "1.replay" (replayOk24i1 #[gTH1, gTHP1, gTHP2, gEO1, gPCZero1, gPCPause1, gPCPause2,
    gPCNorm1, gMvZero1, gMvPause1, gMvPause2, gMvNorm1])

-- 2. `Leaving.redirectPendingAfterLeave` preserves the outer `pendingReplacement` across a
--    graveyard replacement choice in all six branches (CR 616.1 / 800.4a,f–h).
#guard
  let base : Game :=
    let g := insertObject (addPermanent afterDraw bear me me) hero me .stack (some me)
    let spId := (g.objects.filter (fun o => o.name == hero.name && o.zone == .stack))[0]!.id
    let g := g.putStackEntry me spId
    let g := withGyExile24i1 g true
    g.change (.pushContinuationFrame { pendingReplacement := some (.restorePending (.scry me 1)) })
  let bearId := (base.battlefield.filter (·.name == bear.name))[0]!.id
  let spId := (base.objects.filter (fun o => o.name == hero.name && o.zone == .stack))[0]!.id
  let run (pending : Pending) (movedId : ObjectId) : Game × Game × Bool :=
    let (g1, _) := (base.change (.pending pending)).redirectPendingAfterLeave opp24i1
    let g2 := resolveChoice24i1 g1
    (g1, g2,
      paused24i1 g1 && g2.pending == .scry me 1 &&
        (g2.followMovedToZone? movedId (· == .exile)).isSome)
  let (gC1, gC2, counterOk) := run (.payOrLetCounter opp24i1 2 (some spId)) spId
  let (gW1, gW2, wardOk) := run (.payWard opp24i1 spId .discardCard) spId
  let (gS1, gS2, chooseSacOk) := run (.chooseSacrificeCreature opp24i1 #[bearId] #[]) bearId
  let (gE1, gE2, eachOk) := run (.fraChoice opp24i1 (.sacrificeCreatureEach me #[] #[bearId])) bearId
  let (gN1, gN2, nontokenOk) := run (.fraChoice opp24i1 (.sacrificeNontokenEach #[] #[bearId])) bearId
  let (gD1, gD2, damagerOk) := run (.fraChoice opp24i1 (.sacrificeDamager #[] #[] me #[(me, bearId)])) bearId
  mustHold24i1 "2.payOrLetCounter" counterOk &&
  mustHold24i1 "2.payWard" wardOk &&
  mustHold24i1 "2.chooseSacrificeCreature" chooseSacOk &&
  mustHold24i1 "2.sacrificeCreatureEach" eachOk &&
  mustHold24i1 "2.sacrificeNontokenEach" nontokenOk &&
  mustHold24i1 "2.sacrificeDamager" damagerOk &&
  mustHold24i1 "2.replay" (replayOk24i1 #[gC1, gC2, gW1, gW2, gS1, gS2, gE1, gE2, gN1, gN2, gD1, gD2])

-- 3. Discards and sacrifices log only on arrival in the owner's graveyard
--    (CR 400.3 / 614.6 / 701.9a / 701.21a).
#guard
  let gSync : Game := withGyExile24i1 afterDraw false
  let gPause : Game := withGyExile24i1 afterDraw true
  let handCard (g : Game) : ObjectId := (g.player me).hand.back!
  let unwrap (g : Game) (r : Except String Game) : Game :=
    match r with | .ok g' => g' | .error _ => g
  let check (g0 : Game) (f : Game → ObjectId → Game) (needle : String) (exiled : Bool) :
      Game × Bool :=
    let cid := handCard g0
    let g1 := resolveChoice24i1 (f g0 cid)
    let logs := newLogs24i1 g0 g1
    let ok :=
      if exiled then
        (g1.followMovedToZone? cid (· == .exile)).isSome && !logs.any (·.contains needle)
      else
        (g1.followMovedToZone? cid (· == .graveyard me)).isSome && logs.any (·.contains needle)
    (g1, ok)
  -- 3a. Cost discard (`payCostPickItems`):
  let costDisc (g : Game) (cid : ObjectId) : Game := g.payCostPickItems me none none .discardACard #[cid]
  let (gCd1, cdSyncOk) := check gSync costDisc " discards " true
  let (gCd2, cdPauseOk) := check gPause costDisc " discards " true
  let (gCd3, cdNormOk) := check afterDraw costDisc " discards " false
  -- 3b. `discardSource` activation cost:
  let srcDisc (g : Game) (cid : ObjectId) : Game :=
    unwrap g (g.payActivationExtraCosts me cid false false (discardSource := true))
  let (gSd1, sdSyncOk) := check gSync srcDisc " discards " true
  let (gSd2, sdPauseOk) := check gPause srcDisc " discards " true
  let (gSd3, sdNormOk) := check afterDraw srcDisc " discards " false
  -- 3c. `discardHandIdsLoop` with `logEach`:
  let loopDisc (g : Game) (cid : ObjectId) : Game := g.discardHandIdsLoop me #[cid] (logEach := true)
  let (gLd1, ldSyncOk) := check gSync loopDisc " discards " true
  let (gLd2, ldPauseOk) := check gPause loopDisc " discards " true
  let (gLd3, ldNormOk) := check afterDraw loopDisc " discards " false
  -- 3d. `discardFromHandRandomly`: neither line logs when the card is exiled instead:
  let randDisc (g : Game) (cid : ObjectId) : Game := g.discardFromHandRandomly me cid
  let (gRd1, rdSyncOk) := check gSync randDisc "discards" true
  let (gRd2, rdPauseOk) := check gPause randDisc "discards" true
  let (gRd3, rdNormOk) := check afterDraw randDisc "discards a card at random" false
  -- 3e. `discardNonlandFrom` delegates to `discardFromHand` (chooser line gated too):
  let nonlandSetup (g : Game) : Game :=
    let g := (g.player me).hand.foldl (fun acc hid =>
      (acc.move hid .exile none (cause := some testCause)).1) g
    insertObject g bear me (.hand me)
  let nlDisc (g : Game) (_ : ObjectId) : Game := g.discardNonlandFrom opp24i1 me
  let (gNl1, nlSyncOk) := check (nonlandSetup gSync) nlDisc "discards it" true
  let (gNl2, nlPauseOk) := check (nonlandSetup gPause) nlDisc "discards it" true
  let (gNl3, nlNormOk) := check (nonlandSetup afterDraw) nlDisc "discards it" false
  -- 3f. Cleanup discard of an opponent-owned card goes to its OWNER's graveyard (CR 400.3):
  let gCl0 : Game := insertObject afterDraw bear opp24i1 (.hand me)
  let clId := (gCl0.player me).hand.back!
  let gCl1 : Game := gCl0.discardCleanupIds me #[clId]
  let gClEx0 : Game := withGyExile24i1 gCl0 true
  let gClEx1 : Game := gClEx0.discardCleanupIds me #[clId]
  let gClEx2 : Game := resolveChoice24i1 gClEx1
  let cleanupOk : Bool :=
    (gCl1.followMovedToZone? clId (· == .graveyard opp24i1)).isSome &&
    (newLogs24i1 gCl0 gCl1).any (·.contains s!"discards {bear.name} (cleanup)") &&
    paused24i1 gClEx1 &&
    (gClEx2.followMovedToZone? clId (· == .exile)).isSome &&
    !(newLogs24i1 gClEx0 gClEx2).any (·.contains "(cleanup)")
  -- 3g. Sacrifices: `sacrificeToGraveyard` and `.movedAsSacrificed`:
  let sacCheck (g0 : Game) (f : Game → ObjectId → Game) (needle : String) (exiled : Bool) :
      Game × Bool :=
    let g0 := addPermanent g0 bear me me
    let bid := (g0.battlefield.filter (·.name == bear.name))[0]!.id
    let g1 := resolveChoice24i1 (f g0 bid)
    let logs := newLogs24i1 g0 g1
    let ok :=
      if exiled then
        (g1.followMovedToZone? bid (· == .exile)).isSome && !logs.any (·.contains needle) &&
          logs.any (·.contains s!"{bear.name} is exiled instead of dying (CR 614.6)")
      else
        (g1.followMovedToZone? bid (· == .graveyard me)).isSome && logs.any (·.contains needle)
    (g1, ok)
  let sacToGy (g : Game) (bid : ObjectId) : Game :=
    g.sacrificeToGraveyard (g.object! bid) s!"P24 sacrifices {bear.name}"
  let (gSt1, stSyncOk) := sacCheck gSync sacToGy "P24 sacrifices" true
  let (gSt2, stPauseOk) := sacCheck gPause sacToGy "P24 sacrifices" true
  let (gSt3, stNormOk) := sacCheck afterDraw sacToGy "P24 sacrifices" false
  let dummyAb : TriggeredAbility := .triggered .enter (Effect.gainLife 1)
  let movedSac (g : Game) (bid : ObjectId) : Game :=
    g.applySacrifice me dummyAb (some bid) #[] (.sacrificedSource .movedAsSacrificed) .none
  let (gMs1, msSyncOk) := sacCheck gSync movedSac "is sacrificed" true
  let (gMs2, msPauseOk) := sacCheck gPause movedSac "is sacrificed" true
  let (gMs3, msNormOk) := sacCheck afterDraw movedSac "is sacrificed" false
  mustHold24i1 "3a.costDiscard" (cdSyncOk && cdPauseOk && cdNormOk) &&
  mustHold24i1 "3b.discardSource" (sdSyncOk && sdPauseOk && sdNormOk) &&
  mustHold24i1 "3c.discardHandIdsLoop" (ldSyncOk && ldPauseOk && ldNormOk) &&
  mustHold24i1 "3d.discardRandomly" (rdSyncOk && rdPauseOk && rdNormOk) &&
  mustHold24i1 "3e.discardNonlandFrom" (nlSyncOk && nlPauseOk && nlNormOk) &&
  mustHold24i1 "3f.cleanupOk" cleanupOk &&
  mustHold24i1 "3g.sacrificeToGraveyard" (stSyncOk && stPauseOk && stNormOk) &&
  mustHold24i1 "3g.movedAsSacrificed" (msSyncOk && msPauseOk && msNormOk) &&
  mustHold24i1 "3.replay" (replayOk24i1 #[gCd1, gCd2, gCd3, gSd1, gSd2, gSd3, gLd1, gLd2, gLd3,
    gRd1, gRd2, gRd3, gNl1, gNl2, gNl3, gCl1, gClEx1, gClEx2, gSt1, gSt2, gSt3, gMs1, gMs2, gMs3])

-- 4. CR 303.4g stack-Aura graveyard log gated on arrival, non-battlefield `exileInstead`
--    wording (CR 614.6 / 700.4), and Palantír influence log gated on counter delta (CR 122.1).
#guard
  let auraDef : CardDef := aura "P24 Hostless Aura" ManaCost.empty "Enchant creature"
  let auraOnStack (g : Game) : Game × ObjectId :=
    let g := insertObject g auraDef me .stack (some me)
    let aid := (g.objects.filter (fun o => o.name == auraDef.name && o.zone == .stack))[0]!.id
    (g.putStackEntry me aid, aid)
  let auraRun (g0 : Game) : Game × Game × ObjectId :=
    let (g0, aid) := auraOnStack g0
    let g1 := (g0.move aid .battlefield none (cause := some testCause)).1
    (g0, resolveChoice24i1 g1, aid)
  let goesLog := "goes to the graveyard (can't be attached legally; CR 303.4g)"
  let (gA0, gA1, aNormId) := auraRun afterDraw
  let (gAS0, gAS1, aSyncId) := auraRun (withGyExile24i1 afterDraw false)
  let (gAP0, gAP1, aPauseId) := auraRun (withGyExile24i1 afterDraw true)
  let aura303Ok : Bool :=
    (gA1.followMovedToZone? aNormId (· == .graveyard me)).isSome &&
    (newLogs24i1 gA0 gA1).any (·.contains goesLog) &&
    (gAS1.followMovedToZone? aSyncId (· == .exile)).isSome &&
    !(newLogs24i1 gAS0 gAS1).any (·.contains goesLog) &&
    (newLogs24i1 gAS0 gAS1).any (·.contains s!"{auraDef.name} is exiled instead of going to a graveyard (CR 614.6)") &&
    !(newLogs24i1 gAS0 gAS1).any (·.contains "instead of dying") &&
    (gAP1.followMovedToZone? aPauseId (· == .exile)).isSome &&
    !(newLogs24i1 gAP0 gAP1).any (·.contains goesLog)

  -- Palantír: `mult := 0` leaves no influence counter (no log, still scries); a paused
  -- counter-put replacement defers the log until the counter lands:
  let gPl0 : Game := addPermanent afterDraw bear me me
  let plId := (gPl0.battlefield.filter (·.name == bear.name))[0]!.id
  let gPlZero0 : Game := withCounterReps24i1 gPl0 plId .influence false
  let gPlZero1 : Game := gPlZero0.applyPalantir plId (some opp24i1)
  let gPlPause0 : Game := withCounterReps24i1 gPl0 plId .influence true
  let gPlPause1 : Game := gPlPause0.applyPalantir plId (some opp24i1)
  let gPlPause2 : Game := resolveChoice24i1 gPlPause1
  let gPlNorm1 : Game := gPl0.applyPalantir plId (some opp24i1)
  let isScry (g : Game) : Bool := match g.pending with | .scry p 2 => p == me | _ => false
  let palantirOk : Bool :=
    (gPlZero1.object! plId).status.influence == 0 &&
    !(newLogs24i1 gPlZero0 gPlZero1).any (·.contains "gets an influence counter") &&
    isScry gPlZero1 &&
    paused24i1 gPlPause1 &&
    !(newLogs24i1 gPlPause0 gPlPause1).any (·.contains "gets an influence counter") &&
    (gPlPause2.object! plId).status.influence > 0 &&
    (newLogs24i1 gPlPause0 gPlPause2).any (·.contains "gets an influence counter") &&
    isScry gPlPause2 &&
    (newLogs24i1 gPl0 gPlNorm1).any (·.contains "gets an influence counter")
  mustHold24i1 "4a.aura303Ok" aura303Ok &&
  mustHold24i1 "4b.palantirOk" palantirOk &&
  mustHold24i1 "4.replay" (replayOk24i1 #[gA1, gAS1, gAP1, gPlZero1, gPlPause1, gPlPause2, gPlNorm1])

end Phase24Item1EventAlignment

section Phase24Item2EventAlignment

def opp24i2 : PlayerId := ⟨1⟩

def mustHold24i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 24 item 2 guard failed: {label}"

def newLogs24i2 (g0 g : Game) : Array String := g.log.extract g0.log.size g.log.size

def replayOk24i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

def isErr24i2 (r : Except String Game) : Bool :=
  match r with
  | .error _ => true
  | .ok _ => false

/-- A sorcery with mana cost `{1}` and flashback `{3}` (CR 702.34a). -/
def fbDraw24i2 : CardDef := {
  name := "P24i2 Flashback Draw"
  manaCost := ManaCost.ofGeneric 1
  types := #[.sorcery]
  flashback := some (ManaCost.ofGeneric 3)
  spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
}

def freeDraw24i2 : CardDef := {
  name := "P24i2 Free Draw"
  manaCost := ManaCost.empty
  types := #[.sorcery]
  spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
}

/-- A creature with a `{2}` sorcery Adventure (CR 715.2). -/
def adventurer24i2 : CardDef := {
  bear with
  name := "P24i2 Adventurer"
  adventure := some {
    name := "P24i2 Side Quest"
    manaCost := ManaCost.ofGeneric 2
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" } }
}

/-- *Galadriel's Dismissal* (HOC; `Mtg.Engine.Catalog.galadrielSDismissal`, not imported
here): `{W}` instant, kicker `{2}{W}`, "Target creature phases out. If this spell was kicked,
each creature target player controls phases out instead." (`Effect.phaseOutKicker`). -/
def dismissal24i2 : CardDef := {
  name := "Galadriel's Dismissal"
  manaCost := ManaCost.ofColor .white
  types := #[.instant]
  kicker := some (ManaCost.ofGenericAndColor 2 .white)
  spellEffect := some Effect.phaseOutKicker
}

/-- *Iron Hills Stalwart*'s ETB (`Mtg.Engine.Catalog.ironHillsStalwart`, not imported here):
"attach target Equipment you control to up to one target creature you control". -/
def stalwart24i2 : CardDef := {
  bear with
  name := "P24i2 Stalwart"
  triggeredAbilities := #[TriggeredAbility.onEnterAttachTargetEquipment]
}

def gyId24i2 (g : Game) (name : String) : ObjectId :=
  ((g.player me).graveyard.filter (fun id => (g.object! id).name == name))[0]!

def stackId24i2 (g : Game) (name : String) : ObjectId :=
  (g.objects.filter (fun o => o.name == name && o.zone == .stack))[0]!.id

/-- No zone change was replaced by the CR 702.34a flashback exile replacement. -/
def noFlashbackExile24i2 (g : Game) : Bool :=
  !g.events.any (fun e =>
    match e.cause? with
    | some (.replaced rep _) => rep.kind == .flashbackExile
    | _ => false)

-- 1. CR 106.6 / 118.9 / 400.7 / 601.2b,f / 611.2a / 702.34a Flashback cost & exile scoping,
--    active-duration `hasFlashbackPermission`, and `canPayAnnouncedAdditional` restriction flags.
#guard
  -- 1a. A real Flashback cast pays the flashback cost and is exiled as it leaves the stack:
  let gFb0 : Game := (insertObject afterDraw fbDraw24i2 me (.graveyard me)).addMana me .colorless 3
  let fbGyId := gyId24i2 gFb0 fbDraw24i2.name
  let gFbProp : Game := mustApply gFb0 me (.cast fbGyId)
  let gFbCast : Game := mustApply gFbProp me .pay
  let fbSpId := stackId24i2 gFbCast fbDraw24i2.name
  let (gFbMoved, fbMovedId) := gFbCast.move fbSpId (.graveyard me) none
  let realFlashbackOk :=
    gFbProp.proposedSpell.any (·.cost.manaValue == 3) &&
    gFbCast.stack.size == 1 &&
    gFbCast.castViaFlashback (gFbCast.object! fbSpId) &&
    (gFbMoved.object! fbMovedId).zone == .exile &&
    !noFlashbackExile24i2 gFbMoved

  -- 1b. *Bilbo, Thief in the Night*-style `mayCastFromGraveyard` of the same card is NOT a
  --     Flashback cast: it pays the `{1}` mana cost, and leaving the stack applies only the
  --     card's own "exile it instead" replacement (no CR 616.1 choice against flashback exile):
  let gBb0 : Game := (insertObject afterDraw fbDraw24i2 me (.graveyard me)).addMana me .colorless 1
  let bbGyId := gyId24i2 gBb0 fbDraw24i2.name
  let gBb1 : Game := (gBb0.change (.pushContinuationFrame {})).change
    (.pending (.fraChoice me (.mayCastFromGraveyard #[bbGyId])))
  let gBbProp : Game := mustApply gBb1 me (.cast bbGyId)
  let gBbCast : Game := mustApply gBbProp me .pay
  let bbSpId := stackId24i2 gBbCast fbDraw24i2.name
  let (gBbMoved, bbMovedId) := gBbCast.move bbSpId (.graveyard me) none
  let bilboNotFlashbackOk :=
    gBbProp.proposedSpell.any (·.cost.manaValue == 1) &&
    gBbCast.stack.size == 1 &&
    !gBbCast.castViaFlashback (gBbCast.object! bbSpId) &&
    !(match gBbMoved.pending with | .chooseReplacement .. => true | _ => false) &&
    (gBbMoved.object! bbMovedId).zone == .exile &&
    noFlashbackExile24i2 gBbMoved &&
    gBbCast.playCostStart (gBbCast.object! bbSpId) fbDraw24i2 == fbDraw24i2.manaCost

  -- 1c. `hasFlashbackPermission` reads the grant only while its duration is active: a grant that
  --     expired for another reason (an earlier cleanup) no longer matches once the card moved:
  let gPm0 : Game := insertObject afterDraw bear me (.graveyard me)
  let pmGyId := gyId24i2 gPm0 bear.name
  let gPmLive : Game := gPm0.createEffect (.flashbackUntilEot pmGyId) (cause := some testCause)
  let gPmExp : Game := gPmLive.expireEffect (.flashbackUntilEot pmGyId)
  let (gPmLiveSt, liveStId) := gPmLive.move pmGyId .stack (some me)
  let (gPmExpSt, expStId) := gPmExp.move pmGyId .stack (some me)
  let permDurationOk :=
    gPmLive.hasFlashbackPermission (gPmLive.object! pmGyId) &&
    !gPmExp.hasFlashbackPermission (gPmExp.object! pmGyId) &&
    gPmLiveSt.hasFlashbackPermission (gPmLiveSt.object! liveStId) &&
    !gPmExpSt.hasFlashbackPermission (gPmExpSt.object! expStId)

  -- 1d. `canPayAnnouncedAdditional` honours every CR 106.6 restriction flag for the spell:
  let addl (nm : String) (tys : Array CardType) (subs : Array Subtype) : CardDef :=
    { name := nm, manaCost := ManaCost.ofGeneric 1, types := tys, subtypes := subs
      additionalCostOrPayGeneric := some 2 }
  let instDef := addl "P24i2 Addl Instant" #[.instant] #[]
  let heroDef := addl "P24i2 Addl Hero" #[.creature] #["Hero"]
  let villDef := addl "P24i2 Addl Villain" #[.creature] #["Villain"]
  let artDef := addl "P24i2 Addl Artifact" #[.artifact] #[]
  let plainDef := addl "P24i2 Addl Plain" #[.creature] #[]
  let payWith (d : CardDef) (pool : ManaPool) : Bool :=
    let g := insertObject afterDraw d me (.hand me)
    g.canPayAnnouncedAdditional me (g.object! (g.player me).hand.back!) pool
  let pInst := ManaPool.empty.add .colorless 3 (instRestricted := true)
  let pHero := ManaPool.empty.add .colorless 3 (heroRestricted := true)
  let pVill := ManaPool.empty.add .colorless 3 (villainRestricted := true)
  let pCant := ManaPool.empty.add .colorless 3 (cantNonartifact := true)
  let pCreat := ManaPool.empty.add .colorless 3 (creatureRestricted := true)
  let pFree := ManaPool.empty.add .colorless 3
  let restrictionFlagsOk :=
    payWith instDef pInst && !payWith plainDef pInst &&
    payWith heroDef pHero && !payWith plainDef pHero &&
    payWith villDef pVill && !payWith plainDef pVill &&
    payWith artDef pCant && !payWith plainDef pCant &&
    !payWith plainDef pCreat && payWith plainDef pFree
  mustHold24i2 "1a.realFlashbackOk" realFlashbackOk &&
  mustHold24i2 "1b.bilboNotFlashbackOk" bilboNotFlashbackOk &&
  mustHold24i2 "1c.permDurationOk" permDurationOk &&
  mustHold24i2 "1d.restrictionFlagsOk" restrictionFlagsOk &&
  mustHold24i2 "1.replay" (replayOk24i2 #[gFbProp, gFbCast, gFbMoved, gBbProp, gBbCast, gBbMoved])

-- 2. CR 601.2b–c / 702.33a,d,g / 733.1 target-replacing Kicker (*Galadriel's Dismissal*).
#guard
  -- With no creature anywhere only the kicked "target player" is legal: the spell may still be
  -- proposed; kicking proceeds to player targets, declining the kicker reverses the proposal.
  let gGd0 : Game :=
    (insertObject afterDraw dismissal24i2 me (.hand me)).addMana me (.colored .white) 4
  let gdId := (gGd0.player me).hand.back!
  let gGdProp : Game := mustApply gGd0 me (.cast gdId)
  let gGdKick : Game := mustApply gGdProp me (.announceKicker true)
  let gdKickSpell := gGdKick.object! gGdKick.stack.back!.objectId
  let gGdTgt : Game := mustApply gGdKick me (.target (.player opp24i2))
  let gGdPaid : Game := mustApply gGdTgt me .pay
  let gGdNoKick : Game := mustApply gGdProp me (.announceKicker false)
  let kickerOk :=
    !gGd0.battlefield.any (fun o => gGd0.isCreature o) &&
    gGd0.canCast me (gGd0.object! gdId) &&
    dismissal24i2.kicker.isSome &&
    gGdProp.pending == .chooseKicker me &&
    gGdKick.pending == .chooseTargets me &&
    (gGdKick.legalProposedTargets me gdKickSpell).contains (.player opp24i2) &&
    gGdPaid.stack.size == 1 &&
    gGdPaid.wasKicked gGdPaid.stack.back!.objectId &&
    gGdNoKick.proposedSpell.isNone &&
    gGdNoKick.stack.isEmpty &&
    (gGdNoKick.player me).hand.contains gdId &&
    (newLogs24i2 gGd0 gGdNoKick).any (·.contains "has no legal target and can't be cast")
  mustHold24i2 "2.kickerOk" kickerOk &&
  mustHold24i2 "2.replay" (replayOk24i2 #[gGdProp, gGdKick, gGdTgt, gGdPaid, gGdNoKick])

-- 3. CR 601.3e / 715.3a–b Adventure library-top & life payment, and CR 608.2d / 733.1
--    *Cosmic Cube* `Pending.mayCastFromLooked` legality & checkpoint.
#guard
  -- 3a. A creature-only library-top permission can't cast the (sorcery) Adventure half:
  let topCasterDef : CardDef := { bear with name := "P24i2 Top Caster", mayCastCreaturesFromTop := true }
  let gTop0 : Game := insertObject (addPermanent afterDraw topCasterDef me me) adventurer24i2 me (.library me)
  let topAdvId := (gTop0.player me).library.back!
  let topAdventureOk :=
    !gTop0.canCastAdventure me (gTop0.object! topAdvId) &&
    isErr24i2 (gTop0.apply me (.castAdventure topAdvId)) &&
    gTop0.canCast me (gTop0.object! topAdvId)

  -- 3b. "Pay life equal to its mana value" reads the Adventure spell (MV 2), not the creature (MV 0):
  let gLf0 : Game := insertObject afterDraw adventurer24i2 me .exile
  let lfId := (gLf0.objects.filter (fun o => o.name == adventurer24i2.name && o.zone == .exile))[0]!.id
  let gLf1 : Game := gLf0.createEffect
    (.playPermission lfId { player := me, whileExiled := true, payLifeEqualManaValue := true })
    (cause := some testCause)
  let gLfProp : Game := mustApply gLf1 me (.castAdventure lfId)
  let gLfPaid : Game := mustApply gLfProp me .pay
  let lifeAdventureOk :=
    gLfProp.proposedSpell.any (·.payLife == 2) &&
    gLfPaid.stack.size == 1 &&
    (gLfPaid.player me).life + 2 == (gLf1.player me).life

  -- 3c. Cosmic Cube rejects a looked-at card with no legal target or an unpayable mandatory
  --     sacrifice, but accepts a castable one:
  let remDef : CardDef := {
    name := "P24i2 Removal", manaCost := ManaCost.empty, types := #[.sorcery]
    spellEffect := some { targeting := .of .creature, resolution := .destroyTarget, phrase := "Destroy target creature" } }
  let sacDef : CardDef := { freeDraw24i2 with name := "P24i2 Sac Draw", additionalCostSacrificeCreature := true }
  let gCc0 : Game :=
    insertObject (insertObject (insertObject afterDraw freeDraw24i2 me (.library me)) sacDef me (.library me))
      remDef me (.library me)
  let ccLib := (gCc0.player me).library
  let ccRemId := ccLib.back!
  let ccSacId := ccLib[ccLib.size - 2]!
  let ccDrawId := ccLib[ccLib.size - 3]!
  let gCcAsk : Game := gCc0.change (.pending (.mayCastFromLooked me #[ccRemId, ccSacId, ccDrawId] 10))
  let cubeLegalityOk :=
    isErr24i2 (gCcAsk.apply me (.cast ccRemId)) &&
    isErr24i2 (gCcAsk.apply me (.cast ccSacId)) &&
    !isErr24i2 (gCcAsk.apply me (.cast ccDrawId))

  -- 3d. A proposal from the looked-at cards that is reversed (declining *Galadriel's
  --     Dismissal*'s kicker with no creature) restores `Pending.mayCastFromLooked` with the cards
  --     still on top; declining afterwards bottoms them:
  let gCg0 : Game := insertObject (insertObject afterDraw freeDraw24i2 me (.library me)) dismissal24i2 me (.library me)
  let cgLib := (gCg0.player me).library
  let cgGdId := cgLib.back!
  let cgDrawId := cgLib[cgLib.size - 2]!
  let cgIds := #[cgGdId, cgDrawId]
  let gCgAsk : Game := gCg0.change (.pending (.mayCastFromLooked me cgIds 10))
  let gCgProp : Game := mustApply gCgAsk me (.cast cgGdId)
  let gCgRev : Game := mustApply gCgProp me (.announceKicker false)
  let gCgDec : Game := mustApply gCgRev me .decline
  let cubeCheckpointOk :=
    gCgProp.pending == .chooseKicker me &&
    gCgRev.pending == .mayCastFromLooked me cgIds 10 &&
    gCgRev.proposedSpell.isNone &&
    gCgRev.stack.isEmpty &&
    gCgRev.postCastCleanup.isNone &&
    (gCgRev.player me).library.back? == some cgGdId &&
    (gCgRev.player me).library[(gCgRev.player me).library.size - 2]? == some cgDrawId &&
    gCgDec.pending == .none &&
    (gCgDec.player me).library.back? != some cgGdId &&
    (gCgDec.player me).library.back? != some cgDrawId
  mustHold24i2 "3a.topAdventureOk" topAdventureOk &&
  mustHold24i2 "3b.lifeAdventureOk" lifeAdventureOk &&
  mustHold24i2 "3c.cubeLegalityOk" cubeLegalityOk &&
  mustHold24i2 "3d.cubeCheckpointOk" cubeCheckpointOk &&
  mustHold24i2 "3.replay" (replayOk24i2 #[gLfProp, gLfPaid, gCgProp, gCgRev, gCgDec])

-- 4. CR 115.1a–d / 115.3 / 601.2c / 603.3c–d multi-slot legality, `targetCount` minimums, and
--    *Iron Hills Stalwart*'s mandatory Equipment slot.
#guard
  -- 4a. "Target artifact you control and a second target artifact you control" needs two
  --     different artifacts (CR 115.3):
  let trinket : CardDef := { name := "P24i2 Trinket", types := #[.artifact] }
  let gArt1 : Game := addPermanent afterDraw trinket me me
  let gArt2 : Game := addPermanent gArt1 trinket me me
  let twoArtifactsOk :=
    (gArt1.legalTargetsForSpec me .twoArtifactsYouControl).isEmpty &&
    (gArt2.legalTargetsForSpec me .twoArtifactsYouControl).size == 4 &&
    (afterDraw.legalTargetsForSpec me .twoPlayers).size == 2

  -- 4b. "Two target nonland permanents that share a card type" needs such a pair (CR 205.2a):
  let gSh1 : Game := addPermanent (addPermanent afterDraw bear me me) trinket opp24i2 opp24i2
  let gSh2 : Game := addPermanent gSh1 hero opp24i2 opp24i2
  let sharingTypeOk :=
    (gSh1.legalTargetsForSpec me .twoNonlandsSharingType).isEmpty &&
    !(gSh2.legalTargetsForSpec me .twoNonlandsSharingType).isEmpty

  -- 4c. A single "target" announcing two targets needs two distinct legal targets unless it
  --     allows zero (spell modes and triggers alike):
  let twoEff : Effect := {
    targeting := .of (.ofDomain .creature (.exact 2))
    resolution := .destroyTarget
    phrase := "Destroy two target creatures" }
  let twoTrig : TriggeredAbility := .triggered .enter twoEff
  let gTc1 : Game := addPermanent afterDraw bear me me
  let gTc2 : Game := addPermanent gTc1 hero opp24i2 opp24i2
  let tcSrc := (gTc1.battlefield.filter (·.name == bear.name))[0]!.id
  let targetCountOk :=
    !gTc1.spellModeIsChoosable me twoEff &&
    gTc2.spellModeIsChoosable me twoEff &&
    gTc1.spellModeIsChoosable me { twoEff with allowsZeroTargets := true } &&
    gTc1.triggerHasNoLegalTarget me twoTrig tcSrc &&
    !gTc2.triggerHasNoLegalTarget me twoTrig tcSrc

  -- 4d. *Iron Hills Stalwart*: the Equipment slot is required, only the creature slot is
  --     "up to one", so the trigger has no legal target without an Equipment:
  let stalwartAb := stalwart24i2.triggeredAbilities[0]!
  let blade : CardDef := { name := "P24i2 Blade", types := #[.artifact], subtypes := #["Equipment"] }
  let gSt0 : Game := addPermanent afterDraw stalwart24i2 me me
  let stId := (gSt0.battlefield.filter (·.name == stalwart24i2.name))[0]!.id
  let gSt1 : Game := addPermanent gSt0 blade me me
  let stalwartOk :=
    !stalwartAb.allowsZeroTargets &&
    !TargetSpec.isOptionalSlot .equipmentYouControlThenCreatureYouControl 0 &&
    TargetSpec.isOptionalSlot .equipmentYouControlThenCreatureYouControl 1 &&
    gSt0.triggerHasNoLegalTarget me stalwartAb stId &&
    !gSt1.triggerHasNoLegalTarget me stalwartAb stId
  mustHold24i2 "4a.twoArtifactsOk" twoArtifactsOk &&
  mustHold24i2 "4b.sharingTypeOk" sharingTypeOk &&
  mustHold24i2 "4c.targetCountOk" targetCountOk &&
  mustHold24i2 "4d.stalwartOk" stalwartOk

end Phase24Item2EventAlignment

/-! ### Phase 24 Item 3 Event Alignment Tests -/
section Phase24Item3EventAlignment

def opp24i3 : PlayerId := ⟨1⟩

def mustHold24i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase24Item3EventAlignment failed: {label}"

def replayOk24i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

def startThreePlayer24i3 : Game :=
  match Start.start {
    seats := #[
      { name := "P0", deck := testRedDeck },
      { name := "P1", deck := testRedDeck },
      { name := "P2", deck := testRedDeck }
    ]
    startingPlayer := some 0
    seed := 24
  } with
  | .ok g => keepOpeningHands g 16
  | .error e => panic! e

-- 1. CR 614.12 general-subset counter modifiers exclude the entering permanent itself (`o.id != ent.id`).
#guard
  -- 1a. Doc Samson (`.extraCounterOnPermanents`) entering with +1/+1 counters does not modify its own
  --     counters on entry, while a subsequent permanent entering afterward gets +1 counter:
  let samsonEnteringDef : CardDef := {
    bear with
    name := "P24i3 Doc Samson"
    entersWithPlusOneCounters := 2
    staticAbilities := #[.extraCounterOnPermanents]
  }
  let followerDef : CardDef := {
    bear with
    name := "P24i3 Follower"
    entersWithPlusOneCounters := 1
  }
  let gSam0 :=
    insertObject (insertObject afterDraw samsonEnteringDef me (.hand me)) followerDef me (.hand me)
  let samCardId := ((gSam0.player me).hand.filter (fun id => (gSam0.object! id).name == samsonEnteringDef.name))[0]!
  let folCardId := ((gSam0.player me).hand.filter (fun id => (gSam0.object! id).name == followerDef.name))[0]!
  let cSam : EventCause := .oneShotEffect (some ⟨24301⟩) none (some me)
  let (gSam1, samPermId) := gSam0.putOntoBattlefield samCardId me (cause := some cSam)
  let (gSam2, folPermId) := gSam1.putOntoBattlefield folCardId me (cause := some cSam)
  let samsonSelfExcludedOk :=
    (gSam1.object! samPermId).status.plusOnePlusOne == 2 &&
    (gSam2.object! folPermId).status.plusOnePlusOne == 2

  -- 1b. The Golden Gear (`.fra .extraPlusOneCounter`) entering as a creature with +1/+1 counters
  --     does not modify its own counters on entry, while a subsequent creature entering afterward gets +1:
  let gearEnteringDef : CardDef := {
    bear with
    name := "P24i3 Golden Gear Creature"
    types := #[.artifact, .creature]
    entersWithPlusOneCounters := 2
    staticAbilities := #[.fra .extraPlusOneCounter]
  }
  let gGear0 :=
    insertObject (insertObject afterDraw gearEnteringDef me (.hand me)) followerDef me (.hand me)
  let gearCardId := ((gGear0.player me).hand.filter (fun id => (gGear0.object! id).name == gearEnteringDef.name))[0]!
  let gearFolId := ((gGear0.player me).hand.filter (fun id => (gGear0.object! id).name == followerDef.name))[0]!
  let cGear : EventCause := .oneShotEffect (some ⟨24302⟩) none (some me)
  let (gGear1, gearPermId) := gGear0.putOntoBattlefield gearCardId me (cause := some cGear)
  let (gGear2, gearFolPermId) := gGear1.putOntoBattlefield gearFolId me (cause := some cGear)
  let gearSelfExcludedOk :=
    (gGear1.object! gearPermId).status.plusOnePlusOne == 2 &&
    (gGear2.object! gearFolPermId).status.plusOnePlusOne == 2

  mustHold24i3 "1a.samsonSelfExcludedOk" samsonSelfExcludedOk &&
  mustHold24i3 "1b.gearSelfExcludedOk" gearSelfExcludedOk &&
  mustHold24i3 "1.replay" (replayOk24i3 #[gSam1, gSam2, gGear1, gGear2])

-- 2. Wildcard `.modifyCountersPut` (`counterKind := none`) stamps `counterKind := some kind` per
--    `CounterKind` so multi-kind ETB counter bags modify every counter kind and resolve both
--    unstamped and stamped `ReplacementId` preferences/actions without stalling.
#guard
  let multiCounterDef : CardDef := {
    bear with
    name := "P24i3 Multi-Counter Bear"
    entersWithPlusOneCounters := 1
    entersWithShield := 1
  }
  -- 2a. Single wildcard `.modifyCountersPut` (`+1`) modifies both `.plusOnePlusOne` and `.shield`:
  let gW0 := insertObject afterDraw multiCounterDef me (.hand me)
  let wCardId := ((gW0.player me).hand.filter (fun id => (gW0.object! id).name == multiCounterDef.name))[0]!
  let idWildSingle : ReplacementId := { kind := .extraCounterOnPermanents }
  let specWildSingle : ReplacementSpec := {
    id := idWildSingle
    source := none
    controller := some me
    affectedPlayer := me
    kind := .modifyCountersPut none none 1 1
  }
  let cWild : EventCause := .oneShotEffect (some ⟨24303⟩) none (some me)
  let gW1 := gW0.createEffect (.replacement specWildSingle) (cause := some cWild)
  let (gW2, wPermId) := gW1.putOntoBattlefield wCardId me (cause := some cWild)
  let singleWildcardMultiKindOk :=
    (gW2.object! wPermId).status.plusOnePlusOne == 2 &&
    (gW2.object! wPermId).status.shield == 2

  -- 2b. Competing non-commuting wildcard `.modifyCountersPut` (`+1` vs `*2`) prompt once per
  --     `CounterKind` with `counterKind`-stamped choices, accept unstamped and stamped
  --     `Action.chooseReplacement` IDs, and honor pre-supplied unstamped `replacementOrder`:
  let gWC0 := insertObject afterDraw bear me (.hand me)
  let wcCardId := ((gWC0.player me).hand.filter (fun id => (gWC0.object! id).name == bear.name))[0]!
  let idWildAdd : ReplacementId := { kind := .extraCounterOnPermanents, player := some me }
  let idWildMul : ReplacementId := { kind := .extraPlusOneCounter, player := some me }
  let specWildAdd : ReplacementSpec := {
    id := idWildAdd, source := none, controller := some me, affectedPlayer := me,
    kind := .modifyCountersPut none none 1 1
  }
  let specWildMul : ReplacementSpec := {
    id := idWildMul, source := none, controller := some me, affectedPlayer := me,
    kind := .modifyCountersPut none none 0 2
  }
  let cWildComp : EventCause := .oneShotEffect (some ⟨24304⟩) none (some me)
  let gWC1 :=
    (gWC0.createEffect (.replacement specWildAdd) (cause := some cWildComp)).createEffect
      (.replacement specWildMul) (cause := some cWildComp)
  let (gWCPaused1, _) :=
    gWC1.putOntoBattlefield wcCardId me
      (extraEntersWith := #[(.plusOnePlusOne, 2), (.shield, 3)]) (cause := some cWildComp)
  let plusAddStamped : ReplacementId := { idWildAdd with counterKind := some .plusOnePlusOne }
  let plusMulStamped : ReplacementId := { idWildMul with counterKind := some .plusOnePlusOne }
  let shdAddStamped : ReplacementId := { idWildAdd with counterKind := some .shield }
  let shdMulStamped : ReplacementId := { idWildMul with counterKind := some .shield }
  -- Answer first kind (`.plusOnePlusOne`) with UNSTAMPED `idWildAdd`: (2 + 1) * 2 = 6
  let gWCPaused2 := mustApply gWCPaused1 me (.chooseReplacement idWildAdd)
  -- Answer second kind (`.shield`) with STAMPED `shdMulStamped`: (3 * 2) + 1 = 7
  let gWCDone := mustApply gWCPaused2 me (.chooseReplacement shdMulStamped)
  let wcEntered := (gWCDone.battlefield.filter (·.name == bear.name))[0]!
  -- Pre-supplied unstamped `replacementOrder #[idWildAdd]` resolves `.plusOnePlusOne` to 6 without prompting on `.plusOnePlusOne`:
  let gWCPre := gWC1.change (.replacementOrder #[idWildAdd])
  let (gWCPreAfter, _) :=
    gWCPre.putOntoBattlefield wcCardId me
      (extraEntersWith := #[(.plusOnePlusOne, 2), (.shield, 3)]) (cause := some cWildComp)
  let competingWildcardOk :=
    gWCPaused1.pending == .chooseReplacement me #[plusAddStamped, plusMulStamped] &&
    gWCPaused2.pending == .chooseReplacement me #[shdAddStamped, shdMulStamped] &&
    gWCDone.pending == .none &&
    wcEntered.status.plusOnePlusOne == 6 &&
    wcEntered.status.shield == 7 &&
    gWCPreAfter.pending == .chooseReplacement me #[shdAddStamped, shdMulStamped]

  mustHold24i3 "2a.singleWildcardMultiKindOk" singleWildcardMultiKindOk &&
  mustHold24i3 "2b.competingWildcardOk" competingWildcardOk &&
  mustHold24i3 "2.replay" (replayOk24i3 #[gW2, gWCPaused1, gWCPaused2, gWCDone, gWCPreAfter])

-- 3. CR 616.1a–e tier placement for printed ETB & Flashback `.exileInsteadOfStackLeave`,
--    ordering after `616.1b–d`, and already-tapped `entersTappedUnless*` prompts.
#guard
  let dummyOid : ObjectId := ⟨9001⟩
  -- 3a. Printed ETB `ReplacementKind`s and `.exileInsteadOfStackLeave` have tier `.other` (`616.1e`):
  let tierCheckOk :=
    (ReplacementKind.entersTappedSelf dummyOid).tier == .other &&
    (ReplacementKind.entersUntappedPayLife dummyOid 2).tier == .other &&
    (ReplacementKind.entersTappedDeclinePayLife dummyOid).tier == .other &&
    (ReplacementKind.entersUntappedBehold dummyOid dummyOid .villain).tier == .other &&
    (ReplacementKind.entersTappedDeclineBehold dummyOid).tier == .other &&
    (ReplacementKind.asEntersChooseColor dummyOid .red).tier == .other &&
    (ReplacementKind.asEntersChooseCreatureType dummyOid .elf).tier == .other &&
    (ReplacementKind.asEntersChooseOdd dummyOid true).tier == .other &&
    (ReplacementKind.asEntersChooseCardName dummyOid "Bear").tier == .other &&
    (ReplacementKind.asEntersChooseCardType dummyOid .creature).tier == .other &&
    (ReplacementKind.asEntersChooseAnchor dummyOid "Mardu").tier == .other &&
    (ReplacementKind.entersWithCountersSelf dummyOid .plusOnePlusOne 1).tier == .other &&
    (ReplacementKind.exileInsteadOfStackLeave (some dummyOid)).tier == .other &&
    (ReplacementKind.entersUnderControl none me).tier == .control &&
    (ReplacementKind.entersAsCopy none bear).tier == .copy &&
    (ReplacementKind.entersAsCopyCreatureUntilEot dummyOid dummyOid).tier == .copy &&
    (ReplacementKind.declineEntersAsCopy dummyOid).tier == .copy &&
    (ReplacementKind.entersBackFaceUp none).tier == .backFaceUp

  -- 3b. `616.1c` Cursed Mirror (`asEntersMayCopyCreatureHasteUntilEot`) prompts copy BEFORE
  --     `616.1e` `asEntersChooseColor`, and an external `616.1c` `.entersAsCopy` overrides a
  --     printed shockland BEFORE `616.1e` runs:
  let colorCreatureDef : CardDef := {
    bear with
    name := "P24i3 Color Bear"
    staticAbilities := #[.fra .entersTappedChooseColor]
  }
  let mirrorDef : CardDef := {
    name := "P24i3 Cursed Mirror"
    types := #[.artifact]
    asEntersMayCopyCreatureHasteUntilEot := true
  }
  let shockDef : CardDef := {
    name := "P24i3 Shockland"
    types := #[.land]
    entersTappedUnlessPayLife := some 2
  }
  let gMir0 :=
    insertObject (addPermanent afterDraw colorCreatureDef me me) mirrorDef me (.hand me)
  let colorCreatureId := (gMir0.battlefield.filter (·.name == colorCreatureDef.name))[0]!.id
  let mirCardId := ((gMir0.player me).hand.filter (fun id => (gMir0.object! id).name == mirrorDef.name))[0]!
  let mirCandId : ObjectId := ⟨gMir0.nextObjectId⟩
  let cMir : EventCause := .oneShotEffect (some ⟨24305⟩) none (some me)
  let (gMirStep1, _) := gMir0.putOntoBattlefield mirCardId me (cause := some cMir)
  let idCopyCreature : ReplacementId := {
    kind := .entersAsCopyCreatureUntilEot colorCreatureId, object := some mirCandId, player := some me
  }
  let idDeclineCopy : ReplacementId := {
    kind := .declineEntersAsCopy, object := some mirCandId, player := some me
  }
  let gMirStep2 := mustApply gMirStep1 me (.chooseReplacement idCopyCreature)
  let idChooseBlue : ReplacementId := {
    kind := .asEntersChooseColor .blue, object := some mirCandId, player := some me
  }
  let gMirDone := mustApply gMirStep2 me (.chooseReplacement idChooseBlue)

  let gShk0 := insertObject afterDraw shockDef me (.hand me)
  let shkCardId := ((gShk0.player me).hand.filter (fun id => (gShk0.object! id).name == shockDef.name))[0]!
  let specExtCopy : ReplacementSpec := {
    id := { kind := .entersAsCopy }, source := none, controller := some me, affectedPlayer := me,
    kind := .entersAsCopy none bear
  }
  let gShk1 := gShk0.createEffect (.replacement specExtCopy) (cause := some cMir)
  let (gShk2, shkPermId) := gShk1.putOntoBattlefield shkCardId me (cause := some cMir)
  let tierBefore616eOk :=
    gMirStep1.pending == .chooseReplacement me #[idCopyCreature, idDeclineCopy] &&
    (match gMirStep2.pending with
     | .chooseReplacement p choices => p == me && choices.contains idChooseBlue
     | _ => false) &&
    gMirDone.pending == .none &&
    (gMirDone.object! mirCandId).status.chosenColor == some .blue &&
    gShk2.pending == .none &&
    (gShk2.object! shkPermId).name == bear.name &&
    (gShk2.player me).life == (gShk1.player me).life

  -- 3c. Flashback's `.exileInsteadOfStackLeave` competes in `616.1e` alongside another `616.1e`
  --     stack-to-graveyard exile replacement (`createsWolf := true`) rather than preempting in `616.1a`:
  let fbSpellDef : CardDef := {
    name := "P24i3 Flashback Sorcery"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    flashback := some (ManaCost.ofGeneric 1)
    spellEffect := some { resolution := .draw 1, phrase := "Draw a card" }
  }
  let gFb0 :=
    (addPermanent (insertObject afterDraw fbSpellDef me (.graveyard me)) bear opp24i3 opp24i3).addMana me .colorless 1
  let fbCardId := ((gFb0.player me).graveyard.filter (fun id => (gFb0.object! id).name == fbSpellDef.name))[0]!
  let wolfSrcId := (gFb0.battlefield.filter (·.name == bear.name))[0]!.id
  let idWolfExile : ReplacementId := { kind := .exileOppDeath, object := some wolfSrcId }
  let specWolfExile : ReplacementSpec := {
    id := idWolfExile
    source := some wolfSrcId
    controller := some opp24i3
    affectedPlayer := me
    kind := .exileInsteadOfGraveyard none true
  }
  let cFb : EventCause := .oneShotEffect (some ⟨24306⟩) none (some me)
  let gFb1 := gFb0.createEffect (.replacement specWolfExile) (cause := some cFb)
  let gFbProp := mustApply gFb1 me (.cast fbCardId)
  let gFbCast := mustApply gFbProp me .pay
  let stackSpellId := (gFbCast.objects.filter (fun o => o.name == fbSpellDef.name && o.zone == .stack))[0]!.id
  let idFbExile : ReplacementId := { kind := .flashbackExile, object := some stackSpellId }
  let (gFbPaused, _) := gFbCast.move stackSpellId (.graveyard me) none (cause := some cFb)
  let gFbChoseWolf := mustApply gFbPaused me (.chooseReplacement idWolfExile)
  let gFbChoseFb := mustApply gFbPaused me (.chooseReplacement idFbExile)
  let movedWolfCauseOk :=
    (gFbChoseWolf.events.extract gFbPaused.events.size gFbChoseWolf.events.size).any (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause? == some (.replaced idWolfExile cFb)
      | _ => false)
  let movedFbCauseOk :=
    (gFbChoseFb.events.extract gFbPaused.events.size gFbChoseFb.events.size).any (fun e =>
      match e.change with
      | .rules (.zone (.moved ..)) => e.cause? == some (.replaced idFbExile cFb)
      | _ => false)
  let flashbackTier616eOk :=
    gFbPaused.pending == .chooseReplacement me #[idFbExile, idWolfExile] &&
    gFbChoseWolf.objects.any (fun o => o.zone == .exile && o.name == fbSpellDef.name) &&
    movedWolfCauseOk &&
    gFbChoseFb.objects.any (fun o => o.zone == .exile && o.name == fbSpellDef.name) &&
    movedFbCauseOk

  -- 3d. *The Black Gate* (`entersTappedUnlessPayLife`) and *Theorist's Sanctum*
  --     (`entersTappedUnlessBehold`) entering ALREADY tapped (`tapped := true`) still prompt at `616.1e`:
  let blackGateDef : CardDef := {
    name := "P24i3 Black Gate"
    types := #[.land]
    entersTappedUnlessPayLife := some 3
  }
  let sanctumDef : CardDef := {
    name := "P24i3 Theorist's Sanctum"
    types := #[.land]
    entersTappedUnlessBehold := some .villain
  }
  let villainDef : CardDef := {
    bear with
    name := "P24i3 Villain"
    subtypes := #["Villain"]
  }
  let gTap0 :=
    insertObject
      (insertObject (addPermanent afterDraw villainDef me me) blackGateDef me (.hand me))
      sanctumDef me (.hand me)
  let vilId := (gTap0.battlefield.filter (·.name == villainDef.name))[0]!.id
  let bgCardId := ((gTap0.player me).hand.filter (fun id => (gTap0.object! id).name == blackGateDef.name))[0]!
  let snCardId := ((gTap0.player me).hand.filter (fun id => (gTap0.object! id).name == sanctumDef.name))[0]!
  let cTap : EventCause := .oneShotEffect (some ⟨24307⟩) none (some me)
  let bgCandId : ObjectId := ⟨gTap0.nextObjectId⟩
  let (gBgPaused, _) := gTap0.putOntoBattlefield bgCardId me (tapped := true) (cause := some cTap)
  let idBgPay : ReplacementId := { kind := .entersUntappedPayLife 3, object := some bgCandId, player := some me }
  let idBgDec : ReplacementId := { kind := .entersTappedDeclinePayLife, object := some bgCandId, player := some me }
  let gBgPaid := mustApply gBgPaused me (.chooseReplacement idBgPay)
  let snCandId : ObjectId := ⟨gTap0.nextObjectId⟩
  let (gSnPaused, _) := gTap0.putOntoBattlefield snCardId me (tapped := true) (cause := some cTap)
  let idSnBehold : ReplacementId := { kind := .entersUntappedBehold vilId .villain, object := some snCandId, player := some me }
  let idSnDec : ReplacementId := { kind := .entersTappedDeclineBehold, object := some snCandId, player := some me }
  let gSnBeheld := mustApply gSnPaused me (.chooseReplacement idSnBehold)
  let alreadyTappedPromptsOk :=
    gBgPaused.pending == .chooseReplacement me #[idBgPay, idBgDec] &&
    (gBgPaid.player me).life + 3 == (gTap0.player me).life &&
    (gBgPaid.object! bgCandId).status.tapped &&
    gSnPaused.pending == .chooseReplacement me #[idSnBehold, idSnDec] &&
    (gSnBeheld.beheldQualities me).contains .villain &&
    (gSnBeheld.object! snCandId).status.tapped

  mustHold24i3 "3a.tierCheckOk" tierCheckOk &&
  mustHold24i3 "3b.tierBefore616eOk" tierBefore616eOk &&
  mustHold24i3 "3c.flashbackTier616eOk" flashbackTier616eOk &&
  mustHold24i3 "3d.alreadyTappedPromptsOk" alreadyTappedPromptsOk &&
  mustHold24i3 "3.replay" (replayOk24i3 #[
    gMirStep1, gMirStep2, gMirDone, gShk2, gFbPaused, gFbChoseWolf, gFbChoseFb,
    gBgPaused, gBgPaid, gSnPaused, gSnBeheld
  ])

-- 4. CR 616.1 unified multi-token replacement batching (`copyNontokenCreaturesYouControl`,
--    `.copyEachCreatureOfTargetPlayer`, `createAndMarkTokensAttacking` / `commitEnteringAttackItems`)
--    and `.createExtraTokenWithFood` rider propagation (`attacking`, `attackingTarget`,
--    `extraCounters`, `recentTokenIds`, and CR 508.4a noncreature suppression).
#guard
  let tinBearDef : CardDef := { bear with name := "P24i3 Tin Bear", types := #[.artifact, .creature] }
  let tinHeroDef : CardDef := { hero with name := "P24i3 Tin Hero", types := #[.artifact, .creature] }
  let dragonTokDef : CardDef := { bear with name := "P24i3 Dragon Token", isToken := true }
  let golemTokDef : CardDef := { hero with name := "P24i3 Golem Token", isToken := true }
  let cTok : EventCause := .oneShotEffect (some ⟨24308⟩) none (some me)

  -- 4a. Multi-creature copy (`copyNontokenCreaturesYouControl` and `.copyEachCreatureOfTargetPlayer`)
  --     evaluates competing token replacements ONCE across all copied creatures:
  let gCopy0 := addPermanent (addPermanent afterDraw tinBearDef me me) tinHeroDef me me
  let idAsDragon : ReplacementId := { kind := .artifactTokensBecome, player := some me }
  let idAsGolem : ReplacementId := { kind := .artifactTokensBecomeDragons, player := some me }
  let specAsDragon : ReplacementSpec := {
    id := idAsDragon, source := none, controller := some me, affectedPlayer := me,
    kind := .artifactTokensBecome me dragonTokDef
  }
  let specAsGolem : ReplacementSpec := {
    id := idAsGolem, source := none, controller := some me, affectedPlayer := me,
    kind := .artifactTokensBecome me golemTokDef
  }
  let gCopy1 :=
    (gCopy0.createEffect (.replacement specAsDragon) (cause := some cTok)).createEffect
      (.replacement specAsGolem) (cause := some cTok)
  let gYouPaused := gCopy1.copyNontokenCreaturesYouControl me
  let gYouDone := mustApply gYouPaused me (.chooseReplacement idAsDragon)
  let gEachPaused := gCopy1.applyEffect me Effect.copyEachCreatureOfTargetPlayer #[.player me]
  let gEachDone := mustApply gEachPaused me (.chooseReplacement idAsGolem)
  let multiCopySingleChoiceOk :=
    gYouPaused.pending == .chooseReplacement me #[idAsDragon, idAsGolem] &&
    gYouDone.pending == .none &&
    (gYouDone.battlefield.filter (·.name == dragonTokDef.name)).size == 2 &&
    gEachPaused.pending == .chooseReplacement me #[idAsDragon, idAsGolem] &&
    gEachDone.pending == .none &&
    (gEachDone.battlefield.filter (·.name == golemTokDef.name)).size == 2

  -- 4b. `createAndMarkTokensAttacking` -> `commitEnteringAttackItems` in a 3-player game runs
  --     competing token replacements (`specExtraCreature` vs `specAsDragon` on `.food`) ONCE before
  --     attack-target selection, prompts attack targets for each resulting creature token, and commits
  --     both in a single batch without double-applying token replacements:
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let bonusBearTokDef : CardDef := { bear with name := "P24i3 Bonus Bear", isToken := true }
  let idExtraBear : ReplacementId := { kind := .foodAlsoCreatesTreasure, player := some me }
  let specExtraBear : ReplacementSpec := {
    id := idExtraBear, source := none, controller := some me, affectedPlayer := me,
    kind := .createExtraTokenWithFood me bonusBearTokDef
  }
  let gAtk3p0 :=
    (startThreePlayer24i3.createEffect (.replacement specExtraBear) (cause := some cTok)).createEffect
      (.replacement specAsDragon) (cause := some cTok)
  let gAtkRepPaused := gAtk3p0.createAndMarkTokensAttacking me .food 1 false true (cause := some cTok)
  -- Choosing `idExtraBear` first turns 1 Food into (Food + Bonus Bear) -> (Dragon Token + Bonus Bear):
  let gAtkChoose1 := mustApply gAtkRepPaused me (.chooseReplacement idExtraBear)
  let gAtkChoose2 := mustApply gAtkChoose1 me (.chooseMode 0)
  let gAtkDone := mustApply gAtkChoose2 me (.chooseMode 1)
  let createdDragons := gAtkDone.battlefield.filter (·.name == dragonTokDef.name)
  let createdBonusBears := gAtkDone.battlefield.filter (·.name == bonusBearTokDef.name)
  let atkCreatedEvts := (gAtkDone.events.extract gAtk3p0.events.size gAtkDone.events.size).filter (fun e =>
    match e.change with | .rules (.zone (.created ..)) => true | _ => false)
  let recordedBothRecent := (gAtkDone.events.extract gAtk3p0.events.size gAtkDone.events.size).any (fun e =>
    match e.change with
    | .engine (.continuation (.recentTokenIds ids)) =>
      createdDragons.size == 1 && createdBonusBears.size == 1 &&
      ids.contains createdDragons[0]!.id && ids.contains createdBonusBears[0]!.id
    | _ => false)
  let enteringAttackUnifiedOk :=
    gAtkRepPaused.pending == .chooseReplacement me #[idExtraBear, idAsDragon] &&
    (match gAtkChoose1.pending with | .fraChoice p (.chooseEnteringAttackTarget ..) => p == me | _ => false) &&
    (match gAtkChoose2.pending with | .fraChoice p (.chooseEnteringAttackTarget ..) => p == me | _ => false) &&
    gAtkChoose1.log.any (·.contains "chooses what P24i3 Dragon Token enters attacking") &&
    !gAtkChoose1.log.any (·.contains "chooses what Food enters attacking") &&
    gAtkChoose2.log.any (·.contains "chooses P1 for P24i3 Dragon Token to attack") &&
    gAtkChoose2.log.any (·.contains "chooses what P24i3 Bonus Bear enters attacking") &&
    gAtkDone.pending == .none &&
    gAtkDone.log.any (·.contains "creates an attacking P24i3 Dragon Token token and an attacking P24i3 Bonus Bear token") &&
    !gAtkDone.log.any (·.contains "Spirit") &&
    createdDragons.size == 1 &&
    createdBonusBears.size == 1 &&
    atkCreatedEvts.size == 2 &&
    atkCreatedEvts[0]!.batch.isSome &&
    atkCreatedEvts[0]!.batch == atkCreatedEvts[1]!.batch &&
    createdDragons[0]!.status.attacking &&
    createdDragons[0]!.status.attackingTarget == some (.player p1) &&
    createdBonusBears[0]!.status.attacking &&
    createdBonusBears[0]!.status.attackingTarget == some (.player p2) &&
    recordedBothRecent

  -- 4c. `.createExtraTokenWithFood` propagates `attacking`, `attackingTarget`, `extraCounters`, and
  --     `recentTokenIds` to creature bonus tokens, while CR 508.4a suppresses `attacking` /
  --     `attackingTarget` (and 3-player attack-target prompts) on noncreature `treasureToken` bonuses:
  let creatureFoodDef : CardDef := {
    foodToken with
    name := "P24i3 Gingerbread Food"
    types := #[.artifact, .creature]
    power := some 1
    toughness := some 1
  }
  let bilboDef : CardDef := { bear with name := "P24i3 Bilbo", foodAlsoCreatesTreasure := true }
  let gRiderCreature0 :=
    (afterDraw.createEffect (.replacement specExtraBear) (cause := some cTok)).change
      (.pushContinuationFrame {})
  let (gRiderCreature1, primaryFoodObj) :=
    gRiderCreature0.createToken me creatureFoodDef
      (tapped := true) (attacking := true) (attackingTarget := some (.player opp24i3))
      (extraCounters := #[(.shield, 1)]) (recordRecent := true) (cause := some cTok)
  let bonusBearObj := (gRiderCreature1.battlefield.filter (·.name == bonusBearTokDef.name))[0]!
  let gRiderTreasure0 := addPermanent startThreePlayer24i3 bilboDef me me
  let gRiderTreasureAtk := gRiderTreasure0.createAndMarkTokensAttacking me .food 1 true true (cause := some cTok)
  let (gRiderTreasure1, _) :=
    ((addPermanent afterDraw bilboDef me me).change (.pushContinuationFrame {})).createToken me creatureFoodDef
      (tapped := true) (attacking := true) (attackingTarget := some (.player opp24i3))
      (extraCounters := #[(.shield, 1)]) (recordRecent := true) (cause := some cTok)
  let bonusTreasureObj := (gRiderTreasure1.battlefield.filter (·.name == treasureToken.name))[0]!
  let foodRiderPropagationOk :=
    primaryFoodObj.name == creatureFoodDef.name &&
    bonusBearObj.status.tapped &&
    bonusBearObj.status.attacking &&
    bonusBearObj.status.attackingTarget == some (.player opp24i3) &&
    bonusBearObj.status.shield == 1 &&
    gRiderCreature1.recentTokenIds.size == 2 &&
    gRiderCreature1.recentTokenIds.contains primaryFoodObj.id &&
    gRiderCreature1.recentTokenIds.contains bonusBearObj.id &&
    -- Noncreature Food + noncreature Treasure in 3p `createAndMarkTokensAttacking` opens NO attack-target prompt
    -- and logs the actual tapped Food + tapped Treasure tokens rather than Spirit tokens:
    gRiderTreasureAtk.pending == .none &&
    gRiderTreasureAtk.log.any (·.contains "creates a tapped Food token and a tapped Treasure token") &&
    !gRiderTreasureAtk.log.any (·.contains "Spirit") &&
    (gRiderTreasureAtk.battlefield.filter (·.name == treasureToken.name)).all (fun o => !o.status.attacking && o.status.attackingTarget.isNone) &&
    bonusTreasureObj.status.tapped &&
    !bonusTreasureObj.status.attacking &&
    bonusTreasureObj.status.attackingTarget.isNone &&
    bonusTreasureObj.status.shield == 1 &&
    gRiderTreasure1.recentTokenIds.contains bonusTreasureObj.id

  -- 4d. Standard Andúril 2-Spirit creation, unstaged fallback, and ETB replacement-pause continuation
  --     all log the actual created token summary via `logCreatedTokensSummary`:
  let gSpiritStd := afterDraw.createAndMarkTokensAttacking me .spirit 2 true true (cause := some cTok)
  let prismDragonTokDef : CardDef := {
    bear with
    name := "P24i3 Prism Dragon"
    types := #[.artifact, .creature]
    staticAbilities := #[.fra .entersTappedChooseColor]
    isToken := true
  }
  let specAsPrismDragon : ReplacementSpec := {
    id := idAsDragon, source := none, controller := some me, affectedPlayer := me,
    kind := .artifactTokensBecome me prismDragonTokDef
  }
  let gPrism0 := afterDraw.createEffect (.replacement specAsPrismDragon) (cause := some cTok)
  let prismCandId : ObjectId := ⟨gPrism0.nextObjectId⟩
  let gPrismPaused := gPrism0.createAndMarkTokensAttacking me .food 1 false true (cause := some cTok)
  let idPrismRed : ReplacementId := {
    kind := .asEntersChooseColor .red, object := some prismCandId, player := some me
  }
  let gPrismDone := mustApply gPrismPaused me (.chooseReplacement idPrismRed)
  let gUnstagedFallback :=
    (afterDraw.createEffect (.replacement specAsDragon) (cause := some cTok)).promptEnteringAttackItems
      #[.token me .food false #[.player opp24i3]] (cause := some cTok)
  let summaryLogsOk :=
    gSpiritStd.log.any (·.contains "creates two tapped and attacking Spirit tokens") &&
    (match gPrismPaused.pending with | .chooseReplacement q cs => q == me && cs.contains idPrismRed | _ => false) &&
    !gPrismPaused.log.any (·.contains "creates a tapped and attacking P24i3 Prism Dragon token") &&
    gPrismDone.pending == .none &&
    gPrismDone.log.any (·.contains "creates a tapped and attacking P24i3 Prism Dragon token") &&
    !gPrismDone.log.any (·.contains "Spirit") &&
    gUnstagedFallback.log.any (·.contains "creates an attacking P24i3 Dragon Token token") &&
    !gUnstagedFallback.log.any (·.contains "Spirit")

  mustHold24i3 "4a.multiCopySingleChoiceOk" multiCopySingleChoiceOk &&
  mustHold24i3 "4b.enteringAttackUnifiedOk" enteringAttackUnifiedOk &&
  mustHold24i3 "4c.foodRiderPropagationOk" foodRiderPropagationOk &&
  mustHold24i3 "4d.summaryLogsOk" summaryLogsOk &&
  mustHold24i3 "4.replay" (replayOk24i3 #[
    gYouPaused, gYouDone, gEachPaused, gEachDone,
    gAtkRepPaused, gAtkChoose1, gAtkChoose2, gAtkDone,
    gRiderCreature1, gRiderTreasureAtk, gRiderTreasure1,
    gSpiritStd, gPrismPaused, gPrismDone, gUnstagedFallback
  ])

-- 5. CR 701.14a,c self-fight single `2 * power` event and mutual fight upfront power snapshots.
#guard
  -- 5a. Self-fight (`fightCreatures c c` on a 3/10 creature) deals ONE `2 * 3 = 6` damage event:
  --     `+2` noncombat damage yields `6 + 2 = 8` (not `(3 + 2) + (3 + 2) = 10`), and 1 shield counter
  --     prevents all 6 damage:
  let tough310Def : CardDef := { bear with name := "P24i3 Self Fighter", power := some 3, toughness := some 10 }
  let cFight : EventCause := .oneShotEffect (some ⟨24309⟩) none (some me)
  let gSelf0 := addPermanent afterDraw tough310Def me me
  let sfObj := (gSelf0.battlefield.filter (·.name == tough310Def.name))[0]!
  let specPlus2 : ReplacementSpec := {
    id := { kind := .addNoncombatDamage, object := some sfObj.id }
    source := some sfObj.id
    controller := some me
    affectedPlayer := me
    kind := .addNoncombatDamage (some sfObj.id) 2
  }
  let gSelfPlus := gSelf0.createEffect (.replacement specPlus2) (cause := some cFight)
  let preEvCount := gSelfPlus.events.size
  let gSelfPlusAfter := gSelfPlus.fightCreatures (gSelfPlus.object! sfObj.id) (gSelfPlus.object! sfObj.id) (cause := some cFight)
  let dmgEvts := (gSelfPlusAfter.events.extract preEvCount gSelfPlusAfter.events.size).filter (fun e =>
    match e.change with | .rules (.damage (.dealt _)) => true | _ => false)
  let gSelfShield0 := gSelf0.recordPutCounters sfObj.id .shield 1 (some me) (cause := some cFight)
  let gSelfShieldAfter := gSelfShield0.fightCreatures (gSelfShield0.object! sfObj.id) (gSelfShield0.object! sfObj.id) (cause := some cFight)
  let selfFightOk :=
    dmgEvts.size == 1 &&
    (gSelfPlusAfter.object! sfObj.id).status.damage == 8 &&
    (gSelfShieldAfter.object! sfObj.id).status.shield == 0 &&
    (gSelfShieldAfter.object! sfObj.id).status.damage == 0

  -- 5b. Mutual fight snapshots both creatures' powers upfront (CR 701.14a): when `fighterA -> fighterB`
  --     pauses on `Pending.chooseReplacement` and `p1` concedes mid-pause (removing `p1`'s 7-card
  --     graveyard so `fighterB`'s `.powerPerFatGraveyard 2` drops live power from 4 to 2), `fighterB`
  --     still deals its upfront-snapshotted 4 damage to `fighterA`:
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let fighterADef : CardDef := { bear with name := "P24i3 Fighter A", power := some 2, toughness := some 6 }
  let fighterBDef : CardDef := {
    bear with
    name := "P24i3 Fighter B"
    power := some 2
    toughness := some 10
    staticAbilities := #[.powerPerFatGraveyard 2]
  }
  let gMut0 :=
    Id.run do
      let mut g := addPermanent (addPermanent startThreePlayer24i3 fighterADef me me) fighterBDef p2 p2
      for _ in [0:7] do
        g := insertObject g bear p1 (.graveyard p1)
      return g
  let fA := (gMut0.battlefield.filter (·.name == fighterADef.name))[0]!
  let fB := (gMut0.battlefield.filter (·.name == fighterBDef.name))[0]!
  let idAddF : ReplacementId := { kind := .addNoncombatDamage, object := some fA.id }
  let idMulF : ReplacementId := { kind := .multiplyDamage, object := some fA.id }
  let specAddF : ReplacementSpec := {
    id := idAddF, source := some fA.id, controller := some me, affectedPlayer := p2,
    kind := .addNoncombatDamage (some fA.id) 1
  }
  let specMulF : ReplacementSpec := {
    id := idMulF, source := some fA.id, controller := some me, affectedPlayer := p2,
    kind := .multiplyDamage (some fA.id) 2
  }
  let gMut1 :=
    (gMut0.createEffect (.replacement specAddF) (cause := some cFight)).createEffect
      (.replacement specMulF) (cause := some cFight)
  let powerBBefore := gMut1.power (gMut1.object! fB.id)
  let gMutPaused := gMut1.fightCreatures (gMut1.object! fA.id) (gMut1.object! fB.id) (cause := some cFight)
  let gMutConceded := mustApply gMutPaused p1 .concede
  let powerBAfterConcede := gMutConceded.power (gMutConceded.object! fB.id)
  let gMutDone := mustApply gMutConceded p2 (.chooseReplacement idAddF)
  let mutualFightSnapshotOk :=
    powerBBefore == 4 &&
    gMutPaused.pending == .chooseReplacement p2 #[idAddF, idMulF] &&
    powerBAfterConcede == 2 &&
    gMutDone.pending == .none &&
    (gMutDone.object! fB.id).status.damage == 6 &&
    (gMutDone.object! fA.id).status.damage == 4

  mustHold24i3 "5a.selfFightOk" selfFightOk &&
  mustHold24i3 "5b.mutualFightSnapshotOk" mutualFightSnapshotOk &&
  mustHold24i3 "5.replay" (replayOk24i3 #[gSelfPlusAfter, gSelfShieldAfter, gMutPaused, gMutConceded, gMutDone])

-- 6. CR 119.9 / 120.3f / 603.2c / 616.1 / 702.15b aggregated noncombat multi-recipient lifelink
--    (`dealDamageToPlayers`, `dealDamageToEachCreatureMatching`, `divideSevenDamageLoop`).
#guard
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let lifelinkerDef : CardDef := {
    bear with
    name := "P24i3 Lifelinker"
    keywords := Keyword.lifelink
    triggeredAbilities := #[.triggered .youGainLife (Effect.ofTrigger (.onSource (.plusOne 1)))]
  }
  let cLife : EventCause := .oneShotEffect (some ⟨24310⟩) none (some me)
  let countLifeGainEvents (g0 g1 : Game) : Nat :=
    (g1.events.extract g0.events.size g1.events.size).filter (fun e =>
      match e.change with | .rules (.life (.gained p _)) => p == me | _ => false) |>.size
  let youGainLifeQueued (g : Game) : Nat :=
    (g.waitingTriggers.filter (·.event == .youGainLife)).size + g.stack.size

  -- 6a. `dealDamageToPlayers #[p1, p2]` with competing damage replacements pauses per player
  --     and emits ONE aggregated `LifeEvent.gained` (and ONE `.youGainLife` trigger) after both players take damage:
  let gDp0 := addPermanent startThreePlayer24i3 lifelinkerDef me me
  let llSrc := (gDp0.battlefield.filter (·.name == lifelinkerDef.name))[0]!
  let idAddP2 : ReplacementId := { kind := .addNoncombatDamage, player := some p2 }
  let idMulP2 : ReplacementId := { kind := .multiplyDamage, player := some p2 }
  let specAddP2 : ReplacementSpec := {
    id := idAddP2, source := some llSrc.id, controller := some me, affectedPlayer := p2,
    kind := .addNoncombatDamage (some llSrc.id) 1
  }
  let specMulP2 : ReplacementSpec := {
    id := idMulP2, source := some llSrc.id, controller := some me, affectedPlayer := p2,
    kind := .multiplyDamage (some llSrc.id) 2
  }
  let gDpSync := gDp0.dealDamageToPlayers #[p1, p2] 3 (source := some llSrc) (cause := some cLife)
  let gDpComp0 :=
    (gDp0.createEffect (.replacement specAddP2) (cause := some cLife)).createEffect
      (.replacement specMulP2) (cause := some cLife)
  let gDpPause1 := gDpComp0.dealDamageToPlayers #[p1, p2] 3 (source := some (gDpComp0.object! llSrc.id)) (cause := some cLife)
  let gDpPause2 := mustApply gDpPause1 p1 (.chooseReplacement idAddP2)
  let gDpCompDone := mustApply gDpPause2 p2 (.chooseReplacement idMulP2)
  let playersLifelinkOk :=
    (gDpSync.player me).life == (gDp0.player me).life + 6 &&
    countLifeGainEvents gDp0 gDpSync == 1 &&
    youGainLifeQueued gDpSync == 1 &&
    countLifeGainEvents gDpComp0 gDpPause2 == 0 &&
    (gDpCompDone.player me).life == (gDpComp0.player me).life + 15 &&
    countLifeGainEvents gDpComp0 gDpCompDone == 1 &&
    youGainLifeQueued gDpCompDone == 1

  -- 6b. `dealDamageToEachCreatureMatching` across 2 opponent creatures emits ONE `LifeEvent.gained`:
  let toughOppDef : CardDef := { bear with name := "P24i3 Tough Target", toughness := some 5 }
  let gDc0 :=
    addPermanent (addPermanent (addPermanent afterDraw lifelinkerDef me me) toughOppDef opp24i3 opp24i3)
      toughOppDef opp24i3 opp24i3
  let llSrc2 := (gDc0.battlefield.filter (·.name == lifelinkerDef.name))[0]!
  let gDcDone :=
    gDc0.dealDamageToEachCreatureMatching 2 (fun o => o.controller == some opp24i3)
      (source := some (gDc0.snapshotDamageSource llSrc2)) (cause := some cLife)
  let creaturesLifelinkOk :=
    (gDcDone.player me).life == (gDc0.player me).life + 4 &&
    countLifeGainEvents gDc0 gDcDone == 1 &&
    youGainLifeQueued gDcDone == 1

  -- 6c. `divideSevenDamageLoop` across 2 targets emits ONE `LifeEvent.gained`:
  let oppTargets := gDc0.battlefield.filter (·.name == toughOppDef.name)
  let remTargets : Array (Nat × Target) := #[(0, .permanent oppTargets[0]!.id), (1, .permanent oppTargets[1]!.id)]
  let gDivDone := gDc0.divideSevenDamageLoop me .creature remTargets #[3, 4] (some llSrc2.id)
  let divideLifelinkOk :=
    (gDivDone.player me).life == (gDc0.player me).life + 7 &&
    countLifeGainEvents gDc0 gDivDone == 1 &&
    youGainLifeQueued gDivDone == 1

  mustHold24i3 "6a.playersLifelinkOk" playersLifelinkOk &&
  mustHold24i3 "6b.creaturesLifelinkOk" creaturesLifelinkOk &&
  mustHold24i3 "6c.divideLifelinkOk" divideLifelinkOk &&
  mustHold24i3 "6.replay" (replayOk24i3 #[gDpSync, gDpPause1, gDpPause2, gDpCompDone, gDcDone, gDivDone])

-- 7. Shared `withBatch` + `EventCause` for `.dealDamageToEachNonSubtypeAndOpponents` & `extortDrain`,
--    and unbatched per-action `BatchId`s with shared `.oneShotEffect` `EventCause` in `drawThenLoseLife`.
#guard
  -- 7a. `Chapters.applyChapterEffect` `.dealDamageToEachNonSubtypeAndOpponents` shares ONE `BatchId`
  --     and ONE `.oneShotEffect` `EventCause` across creature damage, opponent damage, and lifelink:
  let lifelinkSagaDef : CardDef := {
    name := "P24i3 Lifelink Saga"
    types := #[.enchantment]
    subtypes := #["Saga"]
    keywords := Keyword.lifelink
  }
  let toughBearDef : CardDef := { bear with name := "P24i3 Non-Dragon", toughness := some 5 }
  let gCh0 := addPermanent (addPermanent afterDraw lifelinkSagaDef me me) toughBearDef opp24i3 opp24i3
  let sagaId := (gCh0.battlefield.filter (·.name == lifelinkSagaDef.name))[0]!.id
  let chEff : Effect := Effect.ofChapter (.dealDamageToEachNonSubtypeAndOpponents 2 .dragon)
  let gCh1 := gCh0.applyChapterEffect me chEff (some sagaId) #[]
  let chRulesEvts := (gCh1.events.extract gCh0.events.size gCh1.events.size).filter (fun e =>
    match e.change with
    | .rules (.damage (.dealt _)) | .rules (.life (.lost ..)) | .rules (.life (.gained ..)) => true
    | _ => false)
  let chFirstBatch := chRulesEvts[0]!.batch
  let chFirstCause := chRulesEvts[0]!.cause?
  let chapterBatchOk :=
    chRulesEvts.size == 4 && -- creature damage, opp damage, opp life lost, controller lifelink gained
    chFirstBatch.isSome &&
    (match chFirstCause with | some (.oneShotEffect (some _) ..) => true | _ => false) &&
    chRulesEvts.all (fun e => e.batch == chFirstBatch && e.cause? == chFirstCause) &&
    (gCh1.player me).life == (gCh0.player me).life + 4

  -- 7b. `extortDrain` shares ONE `BatchId` and ONE `.oneShotEffect` `EventCause` across opponent life
  --     loss and controller life gain:
  let gEx0 := startThreePlayer24i3
  let gEx1 := gEx0.extortDrain me
  let exLifeEvts := (gEx1.events.extract gEx0.events.size gEx1.events.size).filter (fun e =>
    match e.change with | .rules (.life _) => true | _ => false)
  let exBatch := exLifeEvts[0]!.batch
  let exCause := exLifeEvts[0]!.cause?
  let extortBatchOk :=
    exLifeEvts.size == 3 && -- 2 opponents lose 1 life each + controller gains 2 life
    exBatch.isSome &&
    (match exCause with | some (.oneShotEffect (some _) ..) => true | _ => false) &&
    exLifeEvts.all (fun e => e.batch == exBatch && e.cause? == exCause) &&
    (gEx1.player me).life == (gEx0.player me).life + 2

  -- 7c. `drawThenLoseLife me 2 2` (CR 121.2) emits 2 individual draw `.moved` events and 1
  --     `LifeEvent.lost` event in 3 DISTINCT `BatchId`s while sharing the SAME `.oneShotEffect` cause:
  let gDl0 := afterDraw
  let gDl1 := gDl0.drawThenLoseLife me 2 2
  let dlEvts := (gDl1.events.extract gDl0.events.size gDl1.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) (.hand _) ..)) | .rules (.life (.lost ..)) => true
    | _ => false)
  let dlCause := dlEvts[0]!.cause?
  let drawLoseUnbatchedOk :=
    dlEvts.size == 3 &&
    dlEvts[0]!.batch.isSome &&
    dlEvts[1]!.batch.isSome &&
    dlEvts[2]!.batch.isSome &&
    dlEvts[0]!.batch != dlEvts[1]!.batch &&
    dlEvts[1]!.batch != dlEvts[2]!.batch &&
    dlEvts[0]!.batch != dlEvts[2]!.batch &&
    (match dlCause with | some (.oneShotEffect (some _) ..) => true | _ => false) &&
    dlEvts.all (fun e => e.cause? == dlCause)

  mustHold24i3 "7a.chapterBatchOk" chapterBatchOk &&
  mustHold24i3 "7b.extortBatchOk" extortBatchOk &&
  mustHold24i3 "7c.drawLoseUnbatchedOk" drawLoseUnbatchedOk &&
  mustHold24i3 "7.replay" (replayOk24i3 #[gCh1, gEx1, gDl1])

-- 8. Multi-player `count > 1` batched discards (`beginDiscardCards #[me, opp] 2`):
--    preserves `count == 2` for subsequent players, moves each chosen card immediately, and keeps
--    one shared `BatchId` open across all 4 discards so batch triggers fire once per batch/player.
#guard
  let playerDiscardWatcherDef : CardDef := {
    bear with
    name := "P24i3 Player Discard Watcher"
    triggeredAbilities := #[
      TriggeredAbility.fra (.fra .playerDiscards)
        "Whenever a player discards one or more cards, draw a card." (.draw 1)
    ]
  }
  let creatureGyWatcherDef : CardDef := {
    bear with
    name := "P24i3 Creature GY Watcher"
    triggeredAbilities := #[
      TriggeredAbility.fra .creatureCardsPutIntoYourGy
        "Whenever one or more creature cards are put into your graveyard from anywhere, draw a card." (.draw 1)
    ]
  }
  let mkDiscardSetup (watcher : CardDef) : Game × ObjectId × ObjectId × ObjectId × ObjectId :=
    let g :=
      insertObject
        (insertObject
          (insertObject
            (insertObject (addPermanent afterDraw watcher me me) bear me (.hand me))
            hero me (.hand me))
          bear opp24i3 (.hand opp24i3))
        hero opp24i3 (.hand opp24i3)
    let m1 := ((g.player me).hand.filter (fun id => (g.object! id).name == bear.name))[0]!
    let m2 := ((g.player me).hand.filter (fun id => (g.object! id).name == hero.name))[0]!
    let o1 := ((g.player opp24i3).hand.filter (fun id => (g.object! id).name == bear.name))[0]!
    let o2 := ((g.player opp24i3).hand.filter (fun id => (g.object! id).name == hero.name))[0]!
    (g, m1, m2, o1, o2)

  let (gDis0, meBear1, meHero2, oppBear1, oppHero2) := mkDiscardSetup playerDiscardWatcherDef
  let gDisStart := gDis0.beginDiscardCards #[me, opp24i3] 2
  let gDis1 := mustApply gDisStart me (.discard meBear1)
  let gDis2 := mustApply gDis1 me (.discard meHero2)
  let gDis3 := mustApply gDis2 opp24i3 (.discard oppBear1)
  let gDis4 := mustApply gDis3 opp24i3 (.discard oppHero2)

  let (gGy0, gyM1, gyM2, gyO1, gyO2) := mkDiscardSetup creatureGyWatcherDef
  let gGyDone :=
    mustApply
      (mustApply
        (mustApply
          (mustApply (gGy0.beginDiscardCards #[me, opp24i3] 2) me (.discard gyM1))
          me (.discard gyM2))
        opp24i3 (.discard gyO1))
      opp24i3 (.discard gyO2)

  let discardMoves := (gDis4.events.extract gDis0.events.size gDis4.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
    | _ => false)
  let disBatch := discardMoves[0]!.batch

  let multiDiscardBatchOk :=
    -- `me` gets 2 discards (`2 -> 1`), then `opp` ALSO gets 2 discards (`2 -> 1`), moving each card immediately:
    gDisStart.pending == .chooseDiscardCard me #[opp24i3] &&
    gDisStart.pendingDiscardsLeft == 2 &&
    gDis1.pending == .chooseDiscardCard me #[opp24i3] &&
    gDis1.pendingDiscardsLeft == 1 &&
    ((gDis1.player me).graveyard.any (fun id => (gDis1.object! id).name == bear.name)) &&
    gDis2.pending == .chooseDiscardCard opp24i3 #[] &&
    gDis2.pendingDiscardsLeft == 2 &&
    ((gDis2.player me).graveyard.any (fun id => (gDis2.object! id).name == hero.name)) &&
    gDis3.pending == .chooseDiscardCard opp24i3 #[] &&
    gDis3.pendingDiscardsLeft == 1 &&
    ((gDis3.player opp24i3).graveyard.any (fun id => (gDis3.object! id).name == bear.name)) &&
    gDis4.pending == .none &&
    ((gDis4.player opp24i3).graveyard.any (fun id => (gDis4.object! id).name == hero.name)) &&
    gDis4.discardBatch.isNone &&
    gDis4.discardCountPerPlayer == 0 &&
    -- All 4 discards share ONE `BatchId`, firing `.playerDiscards` once per player (2) and
    -- `.creatureCardsPutIntoYourGy` once for `me`'s 2 creature cards (1):
    discardMoves.size == 4 &&
    disBatch.isSome &&
    discardMoves.all (fun e => e.batch == disBatch) &&
    (gDis4.waitingTriggers.size + gDis4.stack.size) == 2 &&
    (gGyDone.waitingTriggers.size + gGyDone.stack.size) == 1

  -- 8b. Mid-`beginDiscardCards` departure that pauses on `Pending.chooseReplacement` (CR 610.3
  --     `linkedExile` return with `.entersTappedChooseColor`) returns the exiled permanent in its
  --     own batch, chains `.restorePausedDiscardBatch`, and restores `dbBid` so remaining discards
  --     still share `dbBid` and batch triggers fire once per batch/player:
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let jailerDef : CardDef := { name := "P24i3 Jailer", types := #[.enchantment] }
  let colorPrisonerDef : CardDef := {
    bear with
    name := "P24i3 Color Prisoner"
    staticAbilities := #[.fra .entersTappedChooseColor]
  }
  let gLvBase :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent startThreePlayer24i3 playerDiscardWatcherDef me me)
          creatureGyWatcherDef me me)
        jailerDef p1 p1)
      colorPrisonerDef p2 .exile
  let lvJailerId := (gLvBase.battlefield.filter (·.name == jailerDef.name))[0]!.id
  let lvPrisonerId := (gLvBase.objects.filter (fun o => o.name == colorPrisonerDef.name && o.zone == .exile))[0]!.id
  let gLv0 :=
    insertObject
      (insertObject
        (insertObject
          (insertObject (gLvBase.changeObject lvJailerId (.pushLinkedExile lvPrisonerId)) bear me (.hand me))
          hero me (.hand me))
        bear p2 (.hand p2))
      hero p2 (.hand p2)
  let lvM1 := ((gLv0.player me).hand.filter (fun id => (gLv0.object! id).name == bear.name))[0]!
  let lvM2 := ((gLv0.player me).hand.filter (fun id => (gLv0.object! id).name == hero.name))[0]!
  let lvP2_1 := ((gLv0.player p2).hand.filter (fun id => (gLv0.object! id).name == bear.name))[0]!
  let lvP2_2 := ((gLv0.player p2).hand.filter (fun id => (gLv0.object! id).name == hero.name))[0]!
  let gLvStart := gLv0.beginDiscardCards #[me, p1, p2] 2
  let lvDbBid := gLvStart.discardBatch.map Prod.fst
  let gLv1 := mustApply gLvStart me (.discard lvM1)
  let gLvConceded := mustApply gLv1 p1 .concede
  let lvRepChoices := match gLvConceded.pending with | .chooseReplacement _ cs => cs | _ => #[]
  let gLvResumed := mustApply gLvConceded p2 (.chooseReplacement lvRepChoices[0]!)
  let gLv2 := mustApply gLvResumed me (.discard lvM2)
  let gLv3 := mustApply gLv2 p2 (.discard lvP2_1)
  let gLvDone := mustApply gLv3 p2 (.discard lvP2_2)
  let lvDiscardMoves := (gLvDone.events.extract gLv0.events.size gLvDone.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
    | _ => false)
  let lvReturnMoves := (gLvDone.events.extract gLv0.events.size gLvDone.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .exile .battlefield ..)) => true
    | _ => false)
  let pausedLeaveKeepsDiscardBatchOk :=
    lvDbBid.isSome &&
    (match gLvConceded.pending with | .chooseReplacement q cs => q == p2 && !cs.isEmpty | _ => false) &&
    (match gLvConceded.currentBatch with | none => false | some (bid, _) => gLvConceded.discardBatch.map Prod.fst != some bid) &&
    gLvResumed.pending == .chooseDiscardCard me #[p2] &&
    gLvResumed.pendingDiscardsLeft == 1 &&
    gLvResumed.currentBatch.map Prod.fst == lvDbBid &&
    (gLvResumed.permanentsOf p2).any (·.name == colorPrisonerDef.name) &&
    lvReturnMoves.size == 1 &&
    lvReturnMoves[0]!.batch.isSome &&
    lvReturnMoves[0]!.batch != lvDbBid &&
    lvDiscardMoves.size == 4 &&
    lvDiscardMoves.all (fun e => e.batch == lvDbBid) &&
    gLvDone.pending == .chooseTriggerToStack me &&
    gLvDone.discardBatch.isNone &&
    gLvDone.currentBatch.isNone &&
    -- 2 `.playerDiscards` (`me` and `p2`) + 1 `.creatureCardsPutIntoYourGy` (`me`'s 2 creatures) = 3:
    (gLvDone.waitingTriggers.size + gLvDone.stack.size) == 3

  -- 8c. Mid-`beginDiscardCards` departure that ENDS the `.chooseDiscardCard` prompt while pausing
  --     on `Pending.chooseReplacement` closes `dbBid` once the replacement finishes and stacks
  --     batch triggers onto `stack`:
  let gEndBase :=
    insertObject
      (addPermanent
        (addPermanent startThreePlayer24i3 playerDiscardWatcherDef me me)
        jailerDef p1 p1)
      colorPrisonerDef p2 .exile
  let endJailerId := (gEndBase.battlefield.filter (·.name == jailerDef.name))[0]!.id
  let endPrisonerId := (gEndBase.objects.filter (fun o => o.name == colorPrisonerDef.name && o.zone == .exile))[0]!.id
  let gEnd0 := gEndBase.changeObject endJailerId (.pushLinkedExile endPrisonerId)
  let meEndCard := (gEnd0.player me).hand[0]!
  let gEndStart := gEnd0.beginDiscardCards #[me, p1] 1
  let gEnd1 := mustApply gEndStart me (.discard meEndCard)
  let gEndConceded := mustApply gEnd1 p1 .concede
  let endRepChoices := match gEndConceded.pending with | .chooseReplacement _ cs => cs | _ => #[]
  let gEndDone := mustApply gEndConceded p2 (.chooseReplacement endRepChoices[0]!)
  let pausedLeaveEndsDiscardBatchOk :=
    gEnd1.pending == .chooseDiscardCard p1 #[] &&
    (match gEndConceded.pending with | .chooseReplacement q cs => q == p2 && !cs.isEmpty | _ => false) &&
    gEndConceded.discardBatch.isNone &&
    gEndDone.pending == .none &&
    gEndDone.discardBatch.isNone &&
    gEndDone.currentBatch.isNone &&
    gEndDone.continuations.isEmpty &&
    (gEndDone.permanentsOf p2).any (·.name == colorPrisonerDef.name) &&
    gEndDone.stack.size == 1

  mustHold24i3 "8a.multiDiscardBatchOk" multiDiscardBatchOk &&
  mustHold24i3 "8b.pausedLeaveKeepsDiscardBatchOk" pausedLeaveKeepsDiscardBatchOk &&
  mustHold24i3 "8c.pausedLeaveEndsDiscardBatchOk" pausedLeaveEndsDiscardBatchOk &&
  mustHold24i3 "8.replay" (replayOk24i3 #[
    gDisStart, gDis1, gDis2, gDis3, gDis4, gGyDone,
    gLvStart, gLv1, gLvConceded, gLvResumed, gLv2, gLv3, gLvDone,
    gEndStart, gEnd1, gEndConceded, gEndDone
  ])

end Phase24Item3EventAlignment

end Mtg.Engine.EventTests
