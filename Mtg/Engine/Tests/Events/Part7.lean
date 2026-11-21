import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-! ### Phase 36 Item 1: Live `Pending.chooseLegend` batch-pause preservation, non-rewind dismissed paused-batch flushing without closing live cost/mana batches, `chainRestoreAfterOpenBatch` ordering, and pending Pass-1 loser CR 800.4a departure before Pass 2 in `checkSBACountedWithLeavesCore` -/
section Phase36Item1EventAlignment

private def mustHold36i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase36Item1EventAlignment failed: {label}"

private def replayOk36i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 1a. Live `Pending.chooseLegend` batch-pause preservation across unrelated departures
  --     (`batchPausePromptValid`, `batchPausePromptGoneOrInvalid`, `concedePlayersLoop`, `leavePlayersWhoLostCore`):
  let leg0Def : CardDef := { bear with name := "P36i1 Legend P0", supertypes := #[.legendary] }
  let leg1Def : CardDef := { bear with name := "P36i1 Legend P1", supertypes := #[.legendary] }
  let leg2Def : CardDef := { bear with name := "P36i1 Legend P2", supertypes := #[.legendary] }
  let gLeg0 :=
    addPermanent (addPermanent (addPermanent (addPermanent g4 leg0Def p0 p0) leg0Def p0 p0) leg2Def p2 p2) leg2Def p2 p2
  let leg0Ids := (gLeg0.permanentsOf p0).filter (·.name == leg0Def.name) |>.map (·.id)
  let leg2Ids := (gLeg0.permanentsOf p2).filter (·.name == leg2Def.name) |>.map (·.id)
  let gLegPaused := gLeg0.checkSBA
  let sbaBid? := gLegPaused.currentBatch.map Prod.fst
  let pausePredicatesOk :=
    gLegPaused.batchPausePromptValid gLegPaused.pending &&
    !gLegPaused.batchPausePromptGoneOrInvalid gLegPaused.pending &&
    !gLegPaused.batchPausePromptGoneOrInvalid (.chooseX p0) &&
    gLegPaused.batchPausePromptGoneOrInvalid .none &&
    gLegPaused.batchPausePromptGoneOrInvalid (.chooseLegend p0 leg0Def.name #[leg0Ids[0]!])
  let gLegAfterConcedeP1 := mustApply gLegPaused p1 .concede
  let gLegAfterP0 := mustApply gLegAfterConcedeP1 p0 (.keepLegend leg0Ids[0]!)
  let gLegAfterP2 := mustApply gLegAfterP0 p2 (.keepLegend leg2Ids[0]!)
  let legendBatchPreservedOk :=
    sbaBid?.isSome &&
    pausePredicatesOk &&
    (gLegAfterConcedeP1.player p1).leftTheGame &&
    gLegAfterConcedeP1.currentBatch.map Prod.fst == sbaBid? &&
    gLegAfterConcedeP1.pending == .chooseLegend p0 leg0Def.name leg0Ids &&
    gLegAfterP0.currentBatch.map Prod.fst == sbaBid? &&
    gLegAfterP0.pending == .chooseLegend p2 leg2Def.name leg2Ids &&
    gLegAfterP2.currentBatch.isNone &&
    gLegAfterP2.pending == .none

  -- Multi-seat `concedePlayersLoop #[p1, p3]` & `leavePlayersWhoLostCore`: `p1`'s `.chooseLegend p1`
  -- is dismissed when `p1` leaves, then `flushDismissedPausedBatch` runs `.finishSbaSweep` and pauses
  -- on `p2`'s `.chooseLegend p2` BEFORE `p3` leaves, keeping `sbaBid2` open until `p2` chooses!
  let gP1P2Leg0 :=
    addPermanent (addPermanent (addPermanent (addPermanent g4 leg1Def p1 p1) leg1Def p1 p1) leg2Def p2 p2) leg2Def p2 p2
  let p1P2Leg2Ids := (gP1P2Leg0.permanentsOf p2).filter (·.name == leg2Def.name) |>.map (·.id)
  let gP1P2LegPaused := gP1P2Leg0.checkSBA
  let sbaBid2? := gP1P2LegPaused.currentBatch.map Prod.fst
  let gMultiConcedePaused := gP1P2LegPaused.concedePlayersLoop #[p1, p3] false true false none
  let gMultiConcedeDone := mustApply gMultiConcedePaused p2 (.keepLegend p1P2Leg2Ids[0]!)
  let multiConcedeLegendPauseOk :=
    sbaBid2?.isSome &&
    (gMultiConcedePaused.player p1).leftTheGame &&
    !(gMultiConcedePaused.player p3).leftTheGame &&
    gMultiConcedePaused.currentBatch.map Prod.fst == sbaBid2? &&
    gMultiConcedePaused.pending == .chooseLegend p2 leg2Def.name p1P2Leg2Ids &&
    (gMultiConcedeDone.player p3).leftTheGame &&
    gMultiConcedeDone.currentBatch.isNone &&
    gMultiConcedeDone.pending == .none

  -- 1b. Non-rewind (`rewindProposal == none`) dismissed paused-batch flushing:
  --     (i) `playerLeavesGame p3` closes dismissed `origBid` BEFORE opening post-cleanup
  --         `Pending.resolveRandom (.orderInto ...)`:
  let leyA : CardDef := { name := "P36i1 LeyA", types := #[.enchantment] }
  let leyB : CardDef := { name := "P36i1 LeyB", types := #[.enchantment] }
  let gFlush0 :=
    insertObject
      (insertObject
        (insertObject
          (addPermanent (addPermanent (addPermanent g4 bear p3 p3) leyA p0 p0) leyB p0 p0)
          bear p3 .exile)
        bear p0 .exile)
      bear p0 .exile
  let p3Bear := (gFlush0.permanentsOf p3)[0]!
  let leyAId := (gFlush0.permanentsOf p0).find? (·.name == leyA.name) |>.get!.id
  let leyBId := (gFlush0.permanentsOf p0).find? (·.name == leyB.name) |>.get!.id
  let exObjs := gFlush0.objects.filter (·.zone == .exile)
  let p3ExCard := exObjs.find? (·.owner == p3) |>.get!
  let p0CascCards := exObjs.filter (·.owner == p0) |>.map (·.id)
  let ridA : ReplacementId := { kind := .exileOppDeath, object := some leyAId }
  let ridB : ReplacementId := { kind := .exileOppDeath, object := some leyBId }
  let gFlush1 :=
    (gFlush0.createEffect (.replacement {
      id := ridA, source := some leyAId, controller := some p0, affectedPlayer := p3,
      kind := .exileInsteadOfGraveyard (some p3Bear.id) false }) (cause := some testCause)).createEffect
      (.replacement {
      id := ridB, source := some leyBId, controller := some p0, affectedPlayer := p3,
      kind := .exileInsteadOfGraveyard (some p3Bear.id) false }) (cause := some testCause)
  let gFlushPaused :=
    gFlush1.withBatch (some testCause) fun g =>
      g.destroyPermanent (g.object! p3Bear.id) (cause := some testCause)
  let (gFlushStack, p3StackObj) := gFlushPaused.allocObject bear p3 .stack (some p0)
  let nonRewindProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := p3StackObj.id
    original := p3ExCard, originalSnapshot := gFlushStack.snapshot p3ExCard, kind := .spell
  }
  let gFlushReady :=
    gFlushStack.changes #[
      .pushContinuationFrame {
        postCastCleanup := some (.cascadeBottom p0 p0CascCards[0]! #[p0CascCards[1]!])
      },
      .proposedSpell (some nonRewindProp) ]
  let gFlushAfterP3 := gFlushReady.playerLeavesGame p3
  let nonRewindFlushOk :=
    gFlushReady.currentBatch.isSome &&
    gFlushReady.proposalCheckpoint.isNone &&
    (gFlushAfterP3.player p3).leftTheGame &&
    gFlushAfterP3.currentBatch.isNone &&
    (match gFlushAfterP3.pending with | .resolveRandom (.orderInto ..) => true | _ => false)

  --     (ii) Live mana batch (`finishActivateManaAbilityPostSac`) is NOT closed prematurely on
  --          ordinary `.restorePending (.activateManaAbilities p0)`:
  let petalDef : CardDef := { name := "P36i1 Petal", types := #[.artifact], activatedAbilities := #[ActivatedAbility.manaTapSacrificeAnyColor] }
  let greenSpellDef : CardDef := {
    name := "P36i1 Green Instant", manaCost := ManaCost.ofColor .green, types := #[.instant]
    spellEffect := some (Effect.gainLife 1)
  }
  let gMana0 :=
    insertObject (addPermanent (addPermanent (addPermanent g4 petalDef p0 p0) leyA p0 p0) leyB p0 p0)
      greenSpellDef p0 (.hand p0)
  let petalId := (gMana0.permanentsOf p0).find? (·.name == petalDef.name) |>.get!.id
  let mLeyA := (gMana0.permanentsOf p0).find? (·.name == leyA.name) |>.get!.id
  let mLeyB := (gMana0.permanentsOf p0).find? (·.name == leyB.name) |>.get!.id
  let mRidA : ReplacementId := { kind := .exileOppDeath, object := some mLeyA }
  let mRidB : ReplacementId := { kind := .exileOppDeath, object := some mLeyB }
  let gMana1 :=
    (gMana0.createEffect (.replacement {
      id := mRidA, source := some mLeyA, controller := some p0, affectedPlayer := p0,
      kind := .exileInsteadOfGraveyard (some petalId) false }) (cause := some testCause)).createEffect
      (.replacement {
      id := mRidB, source := some mLeyB, controller := some p0, affectedPlayer := p0,
      kind := .exileInsteadOfGraveyard (some petalId) false }) (cause := some testCause)
  let gSpellId := (gMana1.player p0).hand.back!
  let gManaCast := mustApply gMana1 p0 (.cast gSpellId)
  let gManaPaused := mustApply gManaCast p0 (.tapForMana petalId (.colored .green))
  let gManaDone := mustApply gManaPaused p0 (.chooseReplacement mRidA)
  let liveManaBatchOk :=
    gManaPaused.currentBatch.isSome &&
    gManaDone.currentBatch.isNone &&
    gManaDone.pending == .activateManaAbilities p0 &&
    (gManaDone.player p0).manaPool.green == 1

  -- 1c. `chainRestoreAfterOpenBatch`: when `oldP` (`p0`'s `.scry`) was already saved on `p1`'s departure
  --     and `p1`'s departure opened a paused replacement batch (`curBid`) on `p3`'s returning exiled card,
  --     `p2`'s departure (`saved? == some oldP`, `newlySaved? == some (.chooseReplacement p3 _)`) orders
  --     `restoreOld` AFTER `curBid`'s `.closeBatch` prefix so when `p3` also leaves, `curBid` closes
  --     before `.scry p0 1` opens and `saved?` is NOT dropped:
  let p4 : PlayerId := ⟨4⟩
  let g5 := g4.change (.addPlayer { id := p4, name := "Chandra" })
  let gChain0 :=
    addPermanent (addPermanent (addPermanent (addPermanent g5 bear p1 p1) bear p3 p3) leyA p0 p0) leyB p0 p0
  let p1Jailer := (gChain0.permanentsOf p1)[0]!
  let p3ExVictim := (gChain0.permanentsOf p3)[0]!
  let cLeyA := (gChain0.permanentsOf p0).find? (·.name == leyA.name) |>.get!.id
  let cLeyB := (gChain0.permanentsOf p0).find? (·.name == leyB.name) |>.get!.id
  let gChainExiled := gChain0.exileUntilSourceLeaves (some p1Jailer.id) p3ExVictim (cause := some testCause)
  let cRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some cLeyA, counterKind := some .plusOnePlusOne }
  let cRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some cLeyB, counterKind := some .plusOnePlusOne }
  let gChain1 :=
    (((gChainExiled.logLookAtTop p0 1 (looked := gChainExiled.scryLookedIds p0 1)).createEffect
      (.replacement {
        id := cRidA, source := some cLeyA, controller := some p0, affectedPlayer := p3,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := cRidB, source := some cLeyB, controller := some p0, affectedPlayer := p3,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pending (.scry p0 1) ]
  let gChainDone := gChain1.concedePlayersLoop #[p1, p2, p3] false true false none
  let chainRestoreOrderOk :=
    (gChainDone.player p1).leftTheGame &&
    (gChainDone.player p2).leftTheGame &&
    (gChainDone.player p3).leftTheGame &&
    !gChainDone.over &&
    gChainDone.currentBatch.isNone &&
    gChainDone.pending == .scry p0 1

  -- 1d. `checkSBACountedWithLeavesCore` `hasPendingLosers`: Pass 1 marks `p1.lost = true` and pauses on
  --     `p0`'s `.chooseLegend`; keeping `leg0Ids[0]!` puts `leg0Ids[1]!` (which buffed `p1`'s 2-damage 2/2
  --     bear to 3/3) into the graveyard, and resuming finishes `p1`'s CR 800.4a departure BEFORE Pass 2
  --     runs `checkSBACounted`, so `p1`'s bear leaves the game instead of dying in Pass 2!
  let gLoser0 :=
    addPermanent (addPermanent (addPermanent g4 leg0Def p0 p0) leg0Def p0 p0) bear p1 p1
  let loserLegIds := (gLoser0.permanentsOf p0).filter (·.name == leg0Def.name) |>.map (·.id)
  let p1DamagedBear := (gLoser0.permanentsOf p1)[0]!
  let gLoser1 :=
    (((gLoser0.createEffect
      (.layered (.objects #[p1DamagedBear.id]) (.ptModify 1 1) (.whileSourceOnBattlefield loserLegIds[1]!))
      (cause := some testCause)).dealDamageToPermanent p1DamagedBear 2 (cause := some testCause)).loseLife p1 20
      (cause := some testCause))
  let preLoserIdx := gLoser1.events.size
  let gLoserPaused := gLoser1.checkSBA
  let gLoserDone := mustApply gLoserPaused p0 (.keepLegend loserLegIds[0]!)
  let p1BearDiedToGy :=
    (gLoserDone.events.extract preLoserIdx gLoserDone.events.size).any fun e =>
      match e.change with
      | .rules (.zone (.moved prev _ .battlefield (.graveyard _) ..)) => prev.id == some p1DamagedBear.id
      | _ => false
  let pendingLoserBeforePass2Ok :=
    (gLoserPaused.player p1).lost &&
    !(gLoserPaused.player p1).leftTheGame &&
    gLoserPaused.pending == .chooseLegend p0 leg0Def.name loserLegIds &&
    (gLoserDone.player p1).leftTheGame &&
    (gLoserDone.findObject? p1DamagedBear.id).isNone &&
    !p1BearDiedToGy

  mustHold36i1 "1a.legendBatchPreserved" legendBatchPreservedOk &&
  mustHold36i1 "1a.multiConcedeLegendPause" multiConcedeLegendPauseOk &&
  mustHold36i1 "1b.nonRewindFlush" nonRewindFlushOk &&
  mustHold36i1 "1b.liveManaBatch" liveManaBatchOk &&
  mustHold36i1 "1c.chainRestoreOrder" chainRestoreOrderOk &&
  mustHold36i1 "1d.pendingLoserBeforePass2" pendingLoserBeforePass2Ok &&
  mustHold36i1 "1.replay"
    (replayOk36i1 #[gLegPaused, gLegAfterConcedeP1, gLegAfterP0, gLegAfterP2,
      gP1P2LegPaused, gMultiConcedePaused, gMultiConcedeDone,
      gFlushAfterP3, gManaPaused, gManaDone, gChainDone, gLoserPaused, gLoserDone])

end Phase36Item1EventAlignment

/-! ### Phase 36 Item 2: Continuation preservation, wrapper stripping, and checkpoint-replay batch handling across proposal rewinds -/
section Phase36Item2EventAlignment

private def mustHold36i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase36Item2EventAlignment failed: {label}"

private def replayOk36i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def lifeGainsSince36i2 (g : Game) (startIdx : Nat) (p : PlayerId) : Array Nat :=
  (g.events.extract startIdx g.events.size).filterMap fun e =>
    match e.change with
    | .rules (.life (.gained q amt)) => if q == p then some amt else none
    | _ => none

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let auraDef : CardDef := { name := "P36i2 Aura", types := #[.enchantment] }
  let gBase :=
    addPermanent (addPermanent (addPermanent g4 bear p3 p3) auraDef p1 p1) auraDef p2 p2
  let p3Bear := (gBase.permanentsOf p3)[0]!
  let p1Aura := (gBase.permanentsOf p1)[0]!
  let p2Aura := (gBase.permanentsOf p2)[0]!

  -- 2a(i). Compound `ckptOrigCont? = some (.seq (+2) (+3))` (`dropCkptPrefix` `cur == target`) runs ONCE:
  let gComp0 :=
    (gBase.createEffect (.layered (.objects #[p3Bear.id]) (.control p0) (.whileSourceOnBattlefield p1Aura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.gainLife p0 2 (some testCause)) (.gainLife p0 3 (some testCause)))),
      .saveProposalCheckpoint ]
  let (gComp1, compAb) := gComp0.putStackAbility p3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let compProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := compAb.id, original := compAb
    originalSnapshot := gComp1.snapshot compAb, kind := .activatedAbility, sourceId := some p3Bear.id
  }
  let gCompReady := gComp1.changes #[.proposedSpell (some compProp), .pending (.chooseX p0)]
  let compStartIdx := gCompReady.events.size
  let gCompRewound := gCompReady.concede p1
  let dropCkptCompoundOk :=
    gCompRewound.proposedSpell.isNone &&
    lifeGainsSince36i2 gCompRewound compStartIdx p0 == #[2, 3]

  -- 2a(ii). Immediate rewind path (`playerLeavesGame p1`, `deferRestore = false`) pops `pushedOuterCont?`
  --         without double-executing it:
  let gImm0 :=
    (gBase.createEffect (.layered (.objects #[p3Bear.id]) (.control p0) (.whileSourceOnBattlefield p1Aura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .saveProposalCheckpoint ]
  let (gImm1, immAb) := gImm0.putStackAbility p3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let immProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := immAb.id, original := immAb
    originalSnapshot := gImm1.snapshot immAb, kind := .activatedAbility, sourceId := some p3Bear.id
  }
  let gImmReady :=
    gImm1.changes #[
      .proposedSpell (some immProp),
      .pending (.chooseX p0),
      .pendingReplacement (some (.gainLife p0 4 (some testCause))) ]
  let immStartIdx := gImmReady.events.size
  let gImmLeft := (gImmReady.playerLeavesGame p1).drainPendingContinuations
  let immediatePopOuterOk :=
    gImmLeft.proposedSpell.isNone &&
    lifeGainsSince36i2 gImmLeft immStartIdx p0 == #[4]

  -- 2a(iii). `extraDepartureOuters` preserved across `restoreProposalCheckpoint` AND LIFO ordering
  --          when `ckptMovedToOuter && !extraDepartureOuters.isEmpty`:
  --          `pushedOuterCont? (+1)` -> `extraDepartureOuters (+3)` -> `keepOrigCont? (+7)` -> `ckptOuters (+11)`!
  let gLifo0 :=
    (gBase.createEffect (.layered (.objects #[p3Bear.id]) (.control p0) (.whileSourceOnBattlefield p2Aura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 11 (some testCause)),
      .pendingReplacement (some (.gainLife p0 7 (some testCause))),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement (.gainLife p0 7 (some testCause)),
      .pendingReplacement none ]
  let (gLifo1, lifoAb) := gLifo0.putStackAbility p3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let lifoProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := lifoAb.id, original := lifoAb
    originalSnapshot := gLifo1.snapshot lifoAb, kind := .activatedAbility
    sourceId := some p3Bear.id, resolutionCast := true
  }
  let gLifo2 :=
    gLifo1.changes #[
      .proposedSpell (some lifoProp),
      .pending (.chooseX p0),
      .pendingReplacement (some (.gainLife p0 3 (some testCause))) ]
  let (gLifoAfterP1, savedAfterP1?, _, _) :=
    gLifo2.playerLeavesGameCore p1 (deferRestore := true) (departedIn := #[])
  let gLifoBeforeP2 :=
    gLifoAfterP1.changes #[
      .pending (savedAfterP1?.getD .none),
      .pendingReplacement (some (.gainLife p0 1 (some testCause))) ]
  let (gLifoAfterP2, _, popAfterP2, rwAfterP2) :=
    gLifoBeforeP2.playerLeavesGameCore p2 (deferRestore := true) (departedIn := #[p1])
  let lifoStartIdx := gLifoAfterP2.events.size
  let gLifoDrained :=
    (gLifoAfterP2.restoreSavedPostLeave none popAfterP2 (departed := #[p1, p2]) (rewindProposal := rwAfterP2)).drainPendingContinuations
  let lifoMovedOrderOk :=
    gLifoDrained.proposedSpell.isNone &&
    gLifoDrained.proposalCheckpoint.isNone &&
    lifeGainsSince36i2 gLifoAfterP2 0 p0 == #[] &&
    lifeGainsSince36i2 gLifoDrained lifoStartIdx p0 == #[1, 3, 7, 11]

  -- 2a(iv). Non-moved `!ckptMovedToOuter && !extraDepartureOuters.isEmpty`:
  --         `keepOrigCont? (+2)` drains BEFORE `extraDepartureOuters (+5)` (`#[2, 5]`):
  let gUnmoved0 :=
    (gBase.createEffect (.layered (.objects #[p3Bear.id]) (.control p0) (.whileSourceOnBattlefield p2Aura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 2 (some testCause))),
      .saveProposalCheckpoint ]
  let (gUnmoved1, unmovedAb) := gUnmoved0.putStackAbility p3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let unmovedProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := unmovedAb.id, original := unmovedAb
    originalSnapshot := gUnmoved1.snapshot unmovedAb, kind := .activatedAbility, sourceId := some p3Bear.id
  }
  let gUnmoved2 :=
    gUnmoved1.changes #[
      .proposedSpell (some unmovedProp),
      .pending (.chooseX p0),
      .pushOuterPendingReplacement (.gainLife p0 5 (some testCause)) ]
  let unmovedStartIdx := gUnmoved2.events.size
  let gUnmovedDone := gUnmoved2.concede p2
  let lifoUnmovedOrderOk :=
    gUnmovedDone.proposedSpell.isNone &&
    lifeGainsSince36i2 gUnmovedDone unmovedStartIdx p0 == #[2, 5]

  -- 2b. `isProposalBoundaryStep` post-leave `.restorePending` wrapper does NOT falsely dismiss
  --     `p2`'s unrelated `.chooseReplacement`, `clearAbortedSavedInCont` clears `.chooseX p0` inside
  --     `.restorePending` and `.concedePlayersLoop`, and `reverseOrResumePopped` preserves `popped` + `ckpt`:
  let leyA2 : CardDef := { name := "P36i2 LeyA", types := #[.enchantment] }
  let leyB2 : CardDef := { name := "P36i2 LeyB", types := #[.enchantment] }
  let gBound0 :=
    addPermanent (addPermanent (addPermanent gBase bear p2 p2) leyA2 p0 p0) leyB2 p0 p0
  let p2OwnBear := (gBound0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let bLeyA := (gBound0.permanentsOf p0).find? (·.name == leyA2.name) |>.get!.id
  let bLeyB := (gBound0.permanentsOf p0).find? (·.name == leyB2.name) |>.get!.id
  let bRidA : ReplacementId := { kind := .exileOppDeath, object := some bLeyA }
  let bRidB : ReplacementId := { kind := .exileOppDeath, object := some bLeyB }
  let gBound1 :=
    (((gBound0.createEffect (.layered (.objects #[p3Bear.id]) (.control p0) (.whileSourceOnBattlefield p1Aura.id))
      (cause := some testCause)).createEffect
      (.replacement {
        id := bRidA, source := some bLeyA, controller := some p0, affectedPlayer := p2,
        kind := .exileInsteadOfGraveyard (some p2OwnBear.id) false }) (cause := some testCause)).createEffect
      (.replacement {
        id := bRidB, source := some bLeyB, controller := some p0, affectedPlayer := p2,
        kind := .exileInsteadOfGraveyard (some p2OwnBear.id) false }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let (gBound2, boundAb) := gBound1.putStackAbility p3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let boundProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := boundAb.id, original := boundAb
    originalSnapshot := gBound2.snapshot boundAb, kind := .activatedAbility, sourceId := some p3Bear.id
  }
  let gBoundPaused :=
    (gBound2.destroyPermanent (gBound2.object! p2OwnBear.id) (cause := some testCause)).changes #[
      .proposedSpell (some boundProp) ]
  let gBoundWithWrapper :=
    gBoundPaused.chainPendingReplacement (.restorePending (.chooseX p0) false none #[p3] none)
  let gBoundAfterP1 := mustApply gBoundWithWrapper p1 .concede
  let gBoundAfterP2Choice := mustApply gBoundAfterP1 p2 (.chooseReplacement bRidA)
  let boundaryAndClearOk :=
    (gBoundAfterP1.player p1).leftTheGame &&
    gBoundAfterP1.pending == .chooseReplacement p2 #[bRidA, bRidB] &&
    gBoundAfterP2Choice.proposedSpell.isNone &&
    gBoundAfterP2Choice.pending != .chooseX p0

  -- `reverseOrResumePopped`: `popped (+3)` runs BEFORE restored `ckpt` `pendingReplacement (+7)` (`#[3, 7]`):
  let gRevPopBase := addPermanent g4 bear p0 p0
  let revSrcBear := (gRevPopBase.permanentsOf p0)[0]!
  let gRevPop0 :=
    gRevPopBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 7 (some testCause))),
      .saveProposalCheckpoint ]
  let (gRevPop1', tAb) :=
    (gRevPop0.change (.beginProposalAction .costAction)).putStackAbility revSrcBear p0
      (abilityEffect := some (Effect.gainLife 1))
  let tProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := tAb.id, original := tAb
    originalSnapshot := gRevPop1'.snapshot tAb, kind := .activatedAbility
    sourceId := some revSrcBear.id, tapSource := true
  }
  let gRevPop1 := (gRevPop1'.change (.proposedSpell (some tProp))).change .endProposalAction
  let gRevPop2 :=
    (gRevPop1.becomeTapped (gRevPop1.object! revSrcBear.id) (cause := some testCause)).change
      (.pushOuterPendingReplacement (.gainLife p0 3 (some testCause)))
  let revPopStartIdx := gRevPop0.events.size
  let gRevPopDone :=
    ((gRevPop2.resumePendingReplacement (.restorePending (.chooseX p0) true none #[p1] none)).drainPendingContinuations).popEmptyContinuationFrames
  let reverseOrResumePoppedOk :=
    gRevPopDone.proposedSpell.isNone &&
    gRevPopDone.proposalCheckpoint.isNone &&
    lifeGainsSince36i2 gRevPopDone revPopStartIdx p0 == #[3, 7]

  -- `reverseOrResumePopped` with `sbaPaused == true` and `followedByFinishFra := true`:
  -- (i) open `.chooseReplacement` left by `reverseToProposalCheckpoint?` (`flushQueuedLinkedExile`) AND
  -- (ii) open `.chooseLegend` where `ckpt`'s continuation remains in `pendingReplacement`:
  -- neither resumes early while paused, and answering sequences `popped (+3)` BEFORE restored `ckpt (+7)`
  -- and then `.finishFraChoice` (`+2` from `ckpt`'s `outerPendingReplacements`) -> `#[3, 7, 2]`:
  let revSrcDef := creature "P36i2 RevSrc" ManaCost.empty #["Bear"] 2 2
  let gRr0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent (addPermanent g4 bear p1 p1) bear p0 p0) revSrcDef p0 p0) leyA2 p0 p0)
      leyB2 p0 p0
  let rrJail := (gRr0.permanentsOf p1)[0]!
  let rrVictim := (gRr0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let rrSrc := (gRr0.permanentsOf p0).find? (·.name == revSrcDef.name) |>.get!
  let rrLeyA := (gRr0.permanentsOf p0).find? (·.name == leyA2.name) |>.get!.id
  let rrLeyB := (gRr0.permanentsOf p0).find? (·.name == leyB2.name) |>.get!.id
  let gRrEx := gRr0.exileUntilSourceLeaves (some rrJail.id) rrVictim (cause := some testCause)
  let rrRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some rrLeyA, counterKind := some .plusOnePlusOne }
  let rrRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some rrLeyB, counterKind := some .plusOnePlusOne }
  let gRrCkpt :=
    ((gRrEx.createEffect
      (.replacement {
        id := rrRidA, source := some rrLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := rrRidB, source := some rrLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)),
      .pendingReplacement (some (.gainLife p0 7 (some testCause))),
      .saveProposalCheckpoint ]
  let rrCkptIdx := gRrCkpt.events.size
  let (gRrProp', rrAb) :=
    (gRrCkpt.change (.beginProposalAction .costAction)).putStackAbility rrSrc p0
      (abilityEffect := some (Effect.gainLife 1))
  let rrProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := rrAb.id, original := rrAb
    originalSnapshot := gRrProp'.snapshot rrAb, kind := .activatedAbility
    sourceId := some rrSrc.id, tapSource := true
  }
  let gRrProp :=
    (gRrProp'.changes #[.proposedSpell (some rrProp), .pending (.chooseX p0)]).change .endProposalAction
  let gRrAfterLeave := mustApply gRrProp p1 .concede
  let gRrTapped :=
    (gRrAfterLeave.becomeTapped (gRrAfterLeave.object! rrSrc.id) (cause := some testCause)).change
      (.pushOuterPendingReplacement (.gainLife p0 3 (some testCause)))
  let gRrMid :=
    gRrTapped.resumePendingReplacement
      (.seq (.restorePending (.chooseX p0) true none #[p1] none) .finishFraChoice)
  let gRrDone := mustApply gRrMid p0 (.chooseReplacement rrRidA)
  let reverseOrResumePoppedReplOk :=
    gRrMid.sbaPaused &&
    gRrMid.pending == .chooseReplacement p0 #[rrRidA, rrRidB] &&
    (lifeGainsSince36i2 gRrMid rrCkptIdx p0).isEmpty &&
    gRrDone.proposedSpell.isNone &&
    gRrDone.proposalCheckpoint.isNone &&
    gRrDone.continuations.isEmpty &&
    lifeGainsSince36i2 gRrDone rrCkptIdx p0 == #[3, 7, 2]

  let legDef : CardDef := { (creature "P36i2 Legend" ManaCost.empty #["Bear"] 3 3) with supertypes := #[.legendary] }
  let gLegBase := addPermanent (addPermanent (addPermanent g4 legDef p0 p0) legDef p0 p0) revSrcDef p0 p0
  let legs := (gLegBase.permanentsOf p0).filter (fun o => o.name == legDef.name)
  let leg1 := legs[0]!
  let leg2 := legs[1]!
  let legSrc := (gLegBase.permanentsOf p0).find? (fun o => o.name == revSrcDef.name) |>.get!
  let gLegCkpt :=
    gLegBase.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)),
      .pending (.chooseLegend p0 legDef.name #[leg1.id, leg2.id]),
      .pendingReplacement (some (.gainLife p0 7 (some testCause))),
      .saveProposalCheckpoint ]
  let legCkptIdx := gLegCkpt.events.size
  let (gLegProp', legAb) :=
    (gLegCkpt.change (.beginProposalAction .costAction)).putStackAbility legSrc p0
      (abilityEffect := some (Effect.gainLife 1))
  let legProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := legAb.id, original := legAb
    originalSnapshot := gLegProp'.snapshot legAb, kind := .activatedAbility
    sourceId := some legSrc.id, tapSource := true
  }
  let gLegProp := (gLegProp'.change (.proposedSpell (some legProp))).change .endProposalAction
  let gLegTapped :=
    (gLegProp.becomeTapped (gLegProp.object! legSrc.id) (cause := some testCause)).change
      (.pushOuterPendingReplacement (.gainLife p0 3 (some testCause)))
  let gLegMid :=
    gLegTapped.resumePendingReplacement
      (.seq (.restorePending (.chooseX p0) true none #[p1] none) .finishFraChoice)
  let gLegDone := mustApply gLegMid p0 (.keepLegend leg1.id)
  let reverseOrResumePoppedLegendOk :=
    gLegMid.sbaPaused &&
    gLegMid.pending == .chooseLegend p0 legDef.name #[leg1.id, leg2.id] &&
    (lifeGainsSince36i2 gLegMid legCkptIdx p0).isEmpty &&
    gLegDone.proposedSpell.isNone &&
    gLegDone.proposalCheckpoint.isNone &&
    gLegDone.continuations.isEmpty &&
    lifeGainsSince36i2 gLegDone legCkptIdx p0 == #[3, 7, 2]

  -- 2c(i). `Core.reverseToProposalCheckpointCore?` `preDepBatches`: mana-ability sacrifice batch paused on
  --        `.chooseReplacement` before unrelated `p3` departs STILL reverses its sacrifice & wipes `.manaAdded`:
  let petal2Def : CardDef := { name := "P36i2 Petal", types := #[.artifact], activatedAbilities := #[ActivatedAbility.manaTapSacrificeAnyColor] }
  let rgSpellDef : CardDef := {
    name := "P36i2 RG Instant", manaCost := ⟨#[.colored .red, .colored .green]⟩, types := #[.instant]
    spellEffect := some (Effect.gainLife 1)
  }
  let gPreDep0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent g4 petal2Def p0 p0) leyA2 p0 p0) leyB2 p0 p0)
      rgSpellDef p1 .exile
  let pet2Id := (gPreDep0.permanentsOf p0).find? (·.name == petal2Def.name) |>.get!.id
  let pdLeyA := (gPreDep0.permanentsOf p0).find? (·.name == leyA2.name) |>.get!.id
  let pdLeyB := (gPreDep0.permanentsOf p0).find? (·.name == leyB2.name) |>.get!.id
  let p1ExRgId := (gPreDep0.objects.filter (fun o => o.zone == .exile && o.owner == p1))[0]!.id
  let pdRidA : ReplacementId := { kind := .exileOppDeath, object := some pdLeyA }
  let pdRidB : ReplacementId := { kind := .exileOppDeath, object := some pdLeyB }
  let gPreDep1 :=
    (((gPreDep0.createEffect (.permission p0 (.playFromExile p1ExRgId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.replacement {
        id := pdRidA, source := some pdLeyA, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some pet2Id) false }) (cause := some testCause)).createEffect
      (.replacement {
        id := pdRidB, source := some pdLeyB, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some pet2Id) false }) (cause := some testCause))
  let gPreDepCast := mustApply gPreDep1 p0 (.cast p1ExRgId)
  let gPreDepManaPaused := mustApply gPreDepCast p0 (.tapForMana pet2Id (.colored .red))
  let gPreDepAfterP3 := mustApply gPreDepManaPaused p3 .concede
  let gPreDepManaFinished := mustApply gPreDepAfterP3 p0 (.chooseReplacement pdRidA)
  let gPreDepAborted := mustApply gPreDepManaFinished p1 .concede
  let preDepManaReversedOk :=
    (gPreDepManaFinished.player p0).manaPool.red == 1 &&
    (gPreDepAborted.player p3).leftTheGame &&
    (gPreDepAborted.player p1).leftTheGame &&
    gPreDepAborted.proposedSpell.isNone &&
    gPreDepAborted.proposalCheckpoint.isNone &&
    (gPreDepAborted.player p0).manaPool.total == 0 &&
    (gPreDepAborted.permanentsOf p0).any (fun o => o.id == pet2Id && !o.status.tapped)

  -- 2c(ii). `Movement.reverseToProposalCheckpoint?` post-replay `flushQueuedLinkedExile`:
  --         when `p1` departs (pausing `p1Jail`'s `linkedExile` return on `lkRidA`/`lkRidB`) and `p2`
  --         then departs (aborting `lkProp` with deferred rewind), finishing the pre-rewind choice runs
  --         `reverseToProposalCheckpoint?`, which replays `p1`'s and `p2`'s departure batches separately
  --         via `withBatchCore` and flushes `queuedLinkedExile` once at the end in its own batch:
  let gLink0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent (addPermanent g4 bear p1 p1) bear p0 p0) bear p2 p2) leyA2 p0 p0)
      leyB2 p0 p0
  let p1Jail := (gLink0.permanentsOf p1)[0]!
  let p0LinkVictim := (gLink0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let p2SrcBear := (gLink0.permanentsOf p2)[0]!
  let lkLeyA := (gLink0.permanentsOf p0).find? (·.name == leyA2.name) |>.get!.id
  let lkLeyB := (gLink0.permanentsOf p0).find? (·.name == leyB2.name) |>.get!.id
  let gLinkEx := gLink0.exileUntilSourceLeaves (some p1Jail.id) p0LinkVictim (cause := some testCause)
  let lkRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some lkLeyA, counterKind := some .plusOnePlusOne }
  let lkRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some lkLeyB, counterKind := some .plusOnePlusOne }
  let gLink1 :=
    (((gLinkEx.createEffect (.control p2SrcBear.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := lkRidA, source := some lkLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := lkRidB, source := some lkLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let lkCkptIdx := gLink1.events.size
  let (gLink2', lkAb) :=
    (gLink1.change (.beginProposalAction .costAction)).putStackAbility p2SrcBear p0
      (abilityEffect := some (Effect.gainLife 1))
  let lkProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := lkAb.id, original := lkAb
    originalSnapshot := gLink2'.snapshot lkAb, kind := .activatedAbility, sourceId := some p2SrcBear.id
  }
  let gLink2 :=
    (gLink2'.changes #[.proposedSpell (some lkProp), .pending (.chooseX p0)]).change .endProposalAction
  let gLinkAfterP1 := mustApply gLink2 p1 .concede
  let gLinkAfterP2 := mustApply gLinkAfterP1 p2 .concede
  let gLinkAllDone := mustApply gLinkAfterP2 p0 (.chooseReplacement lkRidA)
  let postSlice := gLinkAllDone.events.extract lkCkptIdx gLinkAllDone.events.size
  let p1Batch? :=
    (postSlice.find? (fun e =>
      match e.change with | .rules (.player (.leftGame q)) => q == p1 | _ => false)).bind (·.batch)
  let p2Batch? :=
    (postSlice.find? (fun e =>
      match e.change with | .rules (.player (.leftGame q)) => q == p2 | _ => false)).bind (·.batch)
  let returnBatch? :=
    (postSlice.find? (fun e =>
      match e.change with
      | .rules (.zone (.moved _ _ .exile .battlefield ..)) => true
      | _ => false)).bind (·.batch)
  let postReplayLinkedExileOk :=
    p1Batch?.isSome && p2Batch?.isSome && returnBatch?.isSome &&
    p1Batch? != p2Batch? && returnBatch? != p1Batch? && returnBatch? != p2Batch? &&
    gLinkAllDone.currentBatch.isNone &&
    gLinkAllDone.proposedSpell.isNone &&
    (gLinkAllDone.permanentsOf p0).any (fun o => o.name == bear.name && o.status.plusOnePlusOne == 3)

  mustHold36i2 "2a.dropCkptCompound" dropCkptCompoundOk &&
  mustHold36i2 "2a.immediatePopOuter" immediatePopOuterOk &&
  mustHold36i2 "2a.lifoMovedOrder" lifoMovedOrderOk &&
  mustHold36i2 "2a.lifoUnmovedOrder" lifoUnmovedOrderOk &&
  mustHold36i2 "2b.boundaryAndClear" boundaryAndClearOk &&
  mustHold36i2 "2b.reverseOrResumePopped" reverseOrResumePoppedOk &&
  mustHold36i2 "2b.reverseOrResumePoppedRepl" reverseOrResumePoppedReplOk &&
  mustHold36i2 "2b.reverseOrResumePoppedLegend" reverseOrResumePoppedLegendOk &&
  mustHold36i2 "2c.preDepManaReversed" preDepManaReversedOk &&
  mustHold36i2 "2c.postReplayLinkedExile" postReplayLinkedExileOk &&
  mustHold36i2 "2.replay"
    (replayOk36i2 #[gCompRewound, gImmLeft, gLifoDrained, gUnmovedDone,
      gBoundAfterP1, gBoundAfterP2Choice, gRevPopDone,
      gRrMid, gRrDone, gLegMid, gLegDone,
      gPreDepManaPaused, gPreDepAfterP3, gPreDepManaFinished, gPreDepAborted,
      gLinkAfterP1, gLinkAfterP2, gLinkAllDone])

end Phase36Item2EventAlignment

/-! ### Phase 36 Item 3: Post-departure proposal-prompt & `CastSpell.announceX` source payability and `.leftTheGame`-gated cascaded / prior-departed CR 800.4a / 800.4c control-loss handling -/
section Phase36Item3EventAlignment

private def mustHold36i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase36Item3EventAlignment failed: {label}"

private def replayOk36i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 3a(i). Post-departure `.restorePending` reverses `.chooseX` when stolen duplicate legendary
  --        planeswalker `L2` returns to `p0` and `p0` keeps `L2` so `L1` dies in post-concede SBAs:
  let legPwDef : CardDef := {
    name := "P36i3 Jace", supertypes := #[.legendary], types := #[.planeswalker], loyalty := some 3
  }
  let gPw0 := addPermanent (addPermanent g4 legPwDef p0 p0) legPwDef p0 p0
  let pwIds := (gPw0.permanentsOf p0).filter (·.name == legPwDef.name) |>.map (·.id)
  let l1Id := pwIds[0]!
  let l2Id := pwIds[1]!
  let gPw1 :=
    (((gPw0.recordPutCounters l1Id .loyalty 3 (some p0) (cause := some testCause)).recordPutCounters
      l2Id .loyalty 3 (some p0) (cause := some testCause)).changeControl
      (gPw0.object! l2Id) p1 (untilEot := true) (cause := some testCause)).change
      .saveProposalCheckpoint
  let minusXAb : ActivatedAbility := { cost := CostSpec.ofItems #[.loyalty .minusX], effect := Effect.gainLife 1 }
  let (gPw2, l1AbObj) := gPw1.putStackAbility (gPw1.object! l1Id) p0 (abilityEffect := some (Effect.gainLife 1))
  let l1Prop : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := l1AbObj.id, original := l1AbObj
    originalSnapshot := gPw2.snapshot l1AbObj, kind := .activatedAbility
    sourceId := some l1Id, activation := some minusXAb, loyaltyX := true
  }
  let gPwAtX := gPw2.changes #[.proposedSpell (some l1Prop), .pending (.chooseX p0)]
  let gPwConcedePaused := mustApply gPwAtX p1 .concede
  let gPwKeepL2 := mustApply gPwConcedePaused p0 (.keepLegend l2Id)
  -- Also test `.activateManaAbilities`, `.chooseKicker`, and `.seq` `checkReversal` when `l1Id` is stolen:
  let gPwStolen := (gPw2.createEffect (.control l1Id p2) (cause := some testCause)).change (.proposedSpell (some l1Prop))
  let gRestMana := gPwStolen.resumePendingReplacement (.restorePending (.activateManaAbilities p0) false none #[p1] none)
  let gPwStolen2 := (gPw2.createEffect (.control l1Id p2) (cause := some testCause)).change (.proposedSpell (some l1Prop))
  let gRestKicker := gPwStolen2.resumePendingReplacement (.restorePending (.chooseKicker p0) false none #[p1] none)
  let gPwStolen3 := (gPw2.createEffect (.control l1Id p2) (cause := some testCause)).change (.proposedSpell (some l1Prop))
  let gSeqHalted :=
    gPwStolen3.resumePendingReplacement
      (.seq (.restorePending (.chooseX p0) false none #[p1] none)
            (.restorePending (.activateManaAbilities p0) false none #[p1] none))

  -- 3a(ii). `CastSpell.announceX` reverses before recording `GameEvent.announced` when `!sourceStillPayable`,
  --         while still throwing when `src` is payable at `x = 0` and `x > loyaltyCounters`:
  let gAnnStolen :=
    (gPw2.createEffect (.control l1Id p2) (cause := some testCause)).changes #[
      .proposedSpell (some l1Prop), .pending (.chooseX p0) ]
  let annPreIdx := gAnnStolen.events.size
  let annRevOk :=
    match gAnnStolen.announceX p0 1 with
    | .ok gRev =>
      gRev.proposedSpell.isNone &&
      !(gRev.events.extract annPreIdx gRev.events.size).any (fun e =>
        match e.change with | .rules (.cast (.announced ..)) => true | _ => false)
    | .error _ => false
  let annTooHighThrows := (gPwAtX.announceX p0 4).toOption.isNone
  let annLegalOk := (gPwAtX.announceX p0 2).toOption.isSome

  let postDepPromptsAndAnnounceXOk :=
    gPwConcedePaused.legendChoicePending? &&
    gPwKeepL2.proposedSpell.isNone &&
    gPwKeepL2.proposalCheckpoint.isNone &&
    gPwKeepL2.stack.isEmpty &&
    gPwKeepL2.pending != .chooseX p0 &&
    gRestMana.proposedSpell.isNone &&
    gRestKicker.proposedSpell.isNone &&
    gSeqHalted.proposedSpell.isNone && gSeqHalted.pending == .none &&
    annRevOk && annTooHighThrows && annLegalOk

  -- 3b(i). Multi-hop CR 800.4c cascade in `isProposalAbortedByLeave` & `concede`:
  --        `p1` owns `W1`; `p3`-owned `W2` (`defaultController = p1`) is controlled by `p2` via `W1`;
  --        `p3`-owned `srcBear` (`defaultController = p1`) is controlled by `p0` via `W2`:
  let wardDef : CardDef := { name := "P36i3 Ward", types := #[.enchantment] }
  let gCasc0 :=
    addPermanent (addPermanent (addPermanent g4 wardDef p1 p1) wardDef p3 p1) bear p3 p1
  let w1 := (gCasc0.battlefield.filter (fun o => o.name == wardDef.name && o.owner == p1))[0]!
  let w2 := (gCasc0.battlefield.filter (fun o => o.name == wardDef.name && o.owner == p3))[0]!
  let cascSrc := (gCasc0.battlefield.filter (·.name == bear.name))[0]!
  let gCasc1 :=
    (((gCasc0.createEffect (.layered (.objects #[w2.id]) (.control p2) (.whileSourceOnBattlefield w1.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[cascSrc.id]) (.control p0) (.whileSourceOnBattlefield w2.id))
      (cause := some testCause)).change .saveProposalCheckpoint)
  let (gCasc2, cascAb) := gCasc1.putStackAbility cascSrc p0 (abilityEffect := some (Effect.gainLife 1))
  let cascProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := cascAb.id, original := cascAb
    originalSnapshot := gCasc2.snapshot cascAb, kind := .activatedAbility, sourceId := some cascSrc.id
  }
  let gCascReady := gCasc2.changes #[.proposedSpell (some cascProp), .pending (.chooseX p0)]
  let gCascConceded := gCascReady.concede p1
  let multiHopCascadeOk :=
    gCascReady.isProposalAbortedByLeave p1 &&
    gCascConceded.proposedSpell.isNone &&
    gCascConceded.proposalCheckpoint.isNone &&
    (gCascConceded.followMovedToZone? w2.id (· == .exile)).isSome &&
    (gCascConceded.followMovedToZone? cascSrc.id (· == .exile)).isSome

  -- 3b(ii). Prior-departed `defaultController` (`p1` already left on an earlier turn; `p3`-owned `relic`
  --         put onto battlefield by `p1` and stolen by `p2`): exiles `relic` when `p2` leaves, when `p2`'s
  --         battlefield source leaves via `Movement.move`, and when `p2`'s hand source leaves via
  --         `Movement.move` or `objectLeavesTheGame` (`old.zone != .battlefield`):
  let relicDef : CardDef := { name := "P36i3 Relic", types := #[.artifact] }
  let gPrior0 :=
    insertObject (addPermanent (addPermanent g4 relicDef p3 p1) wardDef p2 p2) wardDef p2 (.hand p2)
  let relicObj := (gPrior0.battlefield.filter (·.name == relicDef.name))[0]!
  let p2BfSrc := (gPrior0.battlefield.filter (·.name == wardDef.name))[0]!
  let p2HandSrcId := (gPrior0.player p2).hand.back!
  -- Subcase A: `p2` concedes after `p1` already conceded:
  let gPriorIndef := (gPrior0.createEffect (.control relicObj.id p2) (cause := some testCause)).concede p1
  let gPriorAfterP2 := gPriorIndef.concede p2
  -- Subcase B: `p2BfSrc` destroyed via `Movement.move` after `p1` already conceded:
  let gPriorBfSrc :=
    (gPrior0.createEffect (.layered (.objects #[relicObj.id]) (.control p2) (.whileSourceOnBattlefield p2BfSrc.id))
      (cause := some testCause)).concede p1
  let (gPriorBfMoved, _) := gPriorBfSrc.move p2BfSrc.id (.graveyard p2) none (cause := some testCause)
  -- Subcase C: `p2HandSrcId` moved from `.hand p2` to `.graveyard p2` (`old.zone != .battlefield`) AND
  --            via `p2` leaving (`objectLeavesTheGame` with `o.zone != .battlefield`):
  let gPriorHandSrc :=
    (gPrior0.createEffect (.layered (.objects #[relicObj.id]) (.control p2) (.whileInZone p2HandSrcId (.hand p2)))
      (cause := some testCause)).concede p1
  let (gPriorHandMoved, _) := gPriorHandSrc.move p2HandSrcId (.graveyard p2) none (cause := some testCause)
  let gPriorHandLeaveObj := gPriorHandSrc.objectLeavesTheGame (gPriorHandSrc.object! p2HandSrcId) p2
  let priorDepartedExileOk :=
    (gPriorIndef.permanentsOf p2).any (·.id == relicObj.id) &&
    (gPriorAfterP2.followMovedToZone? relicObj.id (· == .exile)).isSome &&
    (gPriorBfMoved.followMovedToZone? relicObj.id (· == .exile)).isSome &&
    (gPriorHandMoved.followMovedToZone? relicObj.id (· == .exile)).isSome &&
    (gPriorHandLeaveObj.followMovedToZone? relicObj.id (· == .exile)).isSome

  -- 3b(iii). Pending simultaneous loser (`lost && !leftTheGame`) isolation:
  --          `p1` and `p2` both lost simultaneously in Pass 1 (`!leftTheGame`); `p2`'s permanent stolen
  --          by `p1` returns to `p2` (NOT exiled!) when `p1` leaves first, and `isProposalAbortedByLeave p1`
  --          does NOT delete `p2`'s permanents while `!leftTheGame`:
  let gSimul0 := addPermanent (addPermanent g4 bear p2 p2) bear p2 p2
  let p2Bears := gSimul0.permanentsOf p2
  let p2StolenByP1 := p2Bears[0]!
  let p2StolenByP0 := p2Bears[1]!
  let gSimul1 :=
    ((((gSimul0.createEffect (.control p2StolenByP1.id p1) (cause := some testCause)).createEffect
      (.control p2StolenByP0.id p0) (cause := some testCause)).record
      (GameEvent.playerLost gSimul0.turnNumber p1 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).record
      (GameEvent.playerLost gSimul0.turnNumber p2 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).change
      .saveProposalCheckpoint
  let (gSimul2, simAb) := gSimul1.putStackAbility p2StolenByP0 p0 (abilityEffect := some (Effect.gainLife 1))
  let simProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := simAb.id, original := simAb
    originalSnapshot := gSimul2.snapshot simAb, kind := .activatedAbility, sourceId := some p2StolenByP0.id
  }
  let gSimulProp := gSimul2.changes #[.proposedSpell (some simProp), .pending (.chooseX p0)]
  let (gSimulAfterP1Only, _, _, _) := gSimulProp.playerLeavesGameCore p1 (deferRestore := true)
  let simultaneousLoserIsolatedOk :=
    (gSimulProp.player p2).lost && !(gSimulProp.player p2).leftTheGame &&
    !gSimulProp.isProposalAbortedByLeave p1 &&
    (gSimulAfterP1Only.player p1).leftTheGame &&
    !(gSimulAfterP1Only.player p2).leftTheGame &&
    (gSimulAfterP1Only.findObject? p2StolenByP1.id).any (fun o =>
      o.isOnBattlefield && gSimulAfterP1Only.controllerOf o == some p2)

  mustHold36i3 "3a.postDepPromptsAndAnnounceX" postDepPromptsAndAnnounceXOk &&
  mustHold36i3 "3b.multiHopCascade" multiHopCascadeOk &&
  mustHold36i3 "3b.priorDepartedExile" priorDepartedExileOk &&
  mustHold36i3 "3b.simultaneousLoserIsolated" simultaneousLoserIsolatedOk &&
  mustHold36i3 "3.replay"
    (replayOk36i3 #[gPwConcedePaused, gPwKeepL2, gRestMana, gRestKicker, gSeqHalted,
      gCascConceded, gPriorIndef, gPriorAfterP2, gPriorBfMoved, gPriorHandMoved,
      gPriorHandLeaveObj, gSimulAfterP1Only])

end Phase36Item3EventAlignment

/-! ### Phase 36 Item 4: `Choices.sourceStillPayable` (`sneakAttacker`, CR 702.37e morph copiable values, ability-zone guards) and `CostPick` self-use exclusion, `{T}`-before-self-sacrifice payment, multi-pick disjointness, and `canPayLife` -/
section Phase36Item4EventAlignment

private def mustHold36i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase36Item4EventAlignment failed: {label}"

private def replayOk36i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 4a(i). `sneakAttacker` in `sourceStillPayable`, `finishProposedSpell`, `proposalCostPromptStillPayable`,
  --        `.resumeChooseModeAfterLeave`, and `isProposalAbortedByLeave`:
  let sneakSpellDef : CardDef := {
    bear with
    name := "P36i4 Sneak Ninja"
    keywords := #[.sneak (CostSpec.ofGeneric 1)]
  }
  let auraDef4 : CardDef := { name := "P36i4 Aura", types := #[.enchantment] }
  let gSnkSetup :=
    insertObject
      (addPermanent (addPermanent g3 { bear with keywords := #[Keyword.haste] } p0 p0) auraDef4 p1 p1)
      sneakSpellDef p0 (.hand p0)
  let atkInitId := (gSnkSetup.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let p1SnkAuraId := (gSnkSetup.permanentsOf p1)[0]!.id
  let snkHandId := (gSnkSetup.player p0).hand.back!
  let gSnkCombat :=
    let g := mustApply (mustApply (mustApply (gSnkSetup.beginStep .beginningOfCombat) p0 .pass) p1 .pass) p2 .pass
    let g := mustApply g p0 (.declareAttackers #[atkInitId] none #[] #[])
    let g := mustApply (mustApply (mustApply g p0 .pass) p1 .pass) p2 .pass
    mustApply g p1 (.declareBlockers #[])
  let gSnkProposed := mustApply (gSnkCombat.addMana p0 .colorless 1) p0 (.castWithSneak snkHandId atkInitId)
  let snkProp := gSnkProposed.proposedSpell.get!
  let gSnkStolen := gSnkProposed.createEffect (.control atkInitId p2) (cause := some testCause)
  let gSnkNonCreature :=
    gSnkProposed.createEffect (.layered (.objects #[atkInitId]) (.types .set #[.artifact] #[] #[]) .untilEndOfTurn)
      (cause := some testCause)
  let gSnkPaidEvt :=
    (gSnkStolen.record (GameEvent.announced gSnkStolen.turnNumber snkProp.spellId
      (costs := #[.sneak atkInitId (some (.player p1))])
      (cause := some (.costPayment .returnToHand p0 (some snkProp.spellId)))))
  let gSnkFinishStolen :=
    match gSnkStolen.finishProposedSpell with
    | .ok g => g
    | .error e => panic! e
  let gSnkViaP1Aura :=
    ((gSnkProposed.createEffect (.control atkInitId p2) (cause := some testCause)).createEffect
      (.layered (.objects #[atkInitId]) (.control p0) (.whileSourceOnBattlefield p1SnkAuraId))
      (cause := some testCause))
  let gSnkViaP1Paid :=
    gSnkViaP1Aura.record (GameEvent.announced gSnkViaP1Aura.turnNumber snkProp.spellId
      (costs := #[.sneak atkInitId (some (.player p1))])
      (cause := some (.costPayment .returnToHand p0 (some snkProp.spellId))))
  let gSnkModeStolen :=
    (gSnkStolen.change (.pending (.chooseMode p0))).runPostStep (.resumeChooseModeAfterLeave p0)
  let sneakPayabilityOk :=
    gSnkProposed.sourceStillPayable snkProp &&
    !gSnkStolen.sourceStillPayable snkProp &&
    !gSnkNonCreature.sourceStillPayable snkProp &&
    gSnkPaidEvt.sourceStillPayable snkProp &&
    !gSnkStolen.proposalCostPromptStillPayable p0 (.discardForAdditionalCost p0) &&
    gSnkFinishStolen.proposedSpell.isNone &&
    (gSnkFinishStolen.player p0).manaPool.colorless == 1 &&
    gSnkModeStolen.proposedSpell.isNone &&
    gSnkViaP1Aura.isProposalAbortedByLeave p1 &&
    !gSnkViaP1Paid.isProposalAbortedByLeave p1

  -- 4a(ii). CR 702.37e morph copiable values (`(g.unmaskedCopiableValues src).morph.isSome`):
  --         granted morph makes `turnFaceUp` payable while active, losing morph before payment reverses,
  --         `isProposalAbortedByLeave` detects losing morph on `p1`'s departure, AND sacrificing the
  --         morph-granting artifact *as* the morph cost still completes `completeTurnFaceUp`!
  let plainDef : CardDef := creature "P36i4 Plain" ManaCost.empty #["Bear"] 2 2
  let morphGrantFace : CardDef := {
    creature "P36i4 Morph Copy" ManaCost.empty #["Shapeshifter"] 3 3 with
    keywords := #[.morph CostSpec.empty]
  }
  let granterArtDef : CardDef := { name := "P36i4 Morph Lens", types := #[.artifact] }
  let gMorphBase0 :=
    addPermanent (addPermanent (addPermanent g3 plainDef p0 p0) granterArtDef p1 p1) granterArtDef p0 p0
  let plainInitId := (gMorphBase0.permanentsOf p0).find? (·.name == plainDef.name) |>.get!.id
  let p1LensId := (gMorphBase0.permanentsOf p1)[0]!.id
  let p0LensId := (gMorphBase0.permanentsOf p0).find? (·.name == granterArtDef.name) |>.get!.id
  let gMorphFd0 := setFaceDown gMorphBase0 plainInitId true
  let fdObj := (gMorphFd0.permanentsOf p0).find? (·.status.faceDown) |>.get!
  let fdProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := fdObj.id, sourceId := some fdObj.id
    original := fdObj, originalSnapshot := gMorphFd0.snapshot fdObj, kind := .turnFaceUp
    needsSacrificeOther := true
  }
  let gFdNoMorph := gMorphFd0.change (.proposedSpell (some fdProp))
  let gFdGrantedByP1 :=
    (gMorphFd0.createEffect (.layered (.objects #[fdObj.id]) (.copy morphGrantFace) (.whileSourceOnBattlefield p1LensId))
      (cause := some testCause)).change (.proposedSpell (some fdProp))
  let gFdGrantedByP0 :=
    ((gMorphFd0.createEffect (.layered (.objects #[fdObj.id]) (.copy morphGrantFace) (.whileSourceOnBattlefield p0LensId))
      (cause := some testCause)).changes #[
      .saveProposalCheckpoint,
      .proposedSpell (some fdProp),
      .pending (.sacrificePermanent p0 fdObj.id) ])
  let gFdSacGranterAsCost := mustApply gFdGrantedByP0 p0 (.sacrifice p0LensId)
  let morphCopiableOk :=
    !gFdNoMorph.sourceStillPayable fdProp &&
    gFdGrantedByP1.sourceStillPayable fdProp &&
    gFdGrantedByP1.isProposalAbortedByLeave p1 &&
    !(gFdSacGranterAsCost.object! fdObj.id).status.faceDown &&
    gFdSacGranterAsCost.proposedSpell.isNone

  -- 4a(iii). `.activatedAbility` zone guards (`activeZones` graveyard / hand):
  let bfOnlyAb : ActivatedAbility := { cost := CostSpec.empty, effect := Effect.gainLife 1 }
  let gyOnlyAb : ActivatedAbility := { cost := CostSpec.empty, activeZones := #[.graveyard], effect := Effect.gainLife 1 }
  let handOnlyAb : ActivatedAbility := { cost := CostSpec.empty, activeZones := #[.hand], effect := Effect.gainLife 1 }
  let gZone0 :=
    insertObject (insertObject (addPermanent g3 bear p0 p0) bear p0 (.graveyard p0)) bear p0 (.hand p0)
  let zBfObj := (gZone0.permanentsOf p0)[0]!
  let zGyObj := gZone0.object! (gZone0.player p0).graveyard.back!
  let zHandObj := gZone0.object! (gZone0.player p0).hand.back!
  let (gZone1, zStackAb) := gZone0.putStackAbility zBfObj p0 (abilityEffect := some (Effect.gainLife 1))
  let mkZoneProp (src : GameObject) (ab? : Option ActivatedAbility) : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := zStackAb.id, original := zStackAb
    originalSnapshot := gZone1.snapshot zStackAb, kind := .activatedAbility
    sourceId := some src.id, activation := ab?
  }
  let abilityZoneGuardsOk :=
    gZone1.sourceStillPayable (mkZoneProp zBfObj (some bfOnlyAb)) &&
    !gZone1.sourceStillPayable (mkZoneProp zGyObj (some bfOnlyAb)) &&
    !gZone1.sourceStillPayable (mkZoneProp zGyObj none) &&
    !gZone1.sourceStillPayable (mkZoneProp zHandObj (some bfOnlyAb)) &&
    gZone1.sourceStillPayable (mkZoneProp zGyObj (some gyOnlyAb)) &&
    !gZone1.sourceStillPayable (mkZoneProp zBfObj (some gyOnlyAb)) &&
    gZone1.sourceStillPayable (mkZoneProp zHandObj (some handOnlyAb)) &&
    !gZone1.sourceStillPayable (mkZoneProp zBfObj (some handOnlyAb)) &&
    (gZone1.payActivationExtraCosts p0 zGyObj.id false false (ab := some bfOnlyAb)).toOption.isNone &&
    (gZone1.payActivationExtraCosts p0 zGyObj.id false false (ab := none)).toOption.isNone

  -- 4b(i). `CostPick` self-use exclusion (`tapSource`, `sacrificeOrExileSource`, `discardOrExileHandSource`):
  let legArtCreatureDef : CardDef := {
    name := "P36i4 Golem", supertypes := #[.legendary], types := #[.artifact, .creature]
    power := some 2, toughness := some 2, keywords := #[Keyword.haste]
  }
  let gSelf0 :=
    insertObject
      (addPermanent ({ g3 with players := g3.players.map (fun pl => if pl.id == p0 then { pl with hand := #[] } else pl) } |> quiet)
        legArtCreatureDef p0 p0)
      legArtCreatureDef p0 (.hand p0)
  let selfPerm := (gSelf0.permanentsOf p0)[0]!
  let selfHand := gSelf0.object! (gSelf0.player p0).hand[0]!
  let tapOtherCrAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.tapSelf, .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 1
  }
  let tapTwoArtFraAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.tapSelf, .tapObjects (.exact 2) (.all #[.hasType .artifact, .tapped false, .controlledBy .you])], effect := Effect.gainLife 1
  }
  let sacSelfAndLegArtAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.sacrifice (.exact 1) .self, .sacrifice (.exact 1) (.filter (.all #[.hasSupertype .legendary, .hasType .artifact]))], effect := Effect.gainLife 1
  }
  let sacSelfAndArtOrLandFraAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.sacrifice (.exact 1) .self, .sacrifice (.exact 1) (.filter (.any #[.hasType .artifact, .hasType .land]))], effect := Effect.gainLife 1
  }
  let discSelfAndLegHandFraAb : ActivatedAbility := {
    activeZones := #[.hand]
    cost := CostSpec.ofItems #[.discard (.exact 1) .self, .discard (.exact 1) (.matching (.hasSupertype .legendary))], effect := Effect.gainLife 1
  }
  let selfExclusionOk :=
    gSelf0.costPickAllows p0 (some selfPerm.id) .tapUntappedCreature selfPerm (tapSource := false) &&
    !gSelf0.costPickAllows p0 (some selfPerm.id) .tapUntappedCreature selfPerm (tapSource := true) &&
    !gSelf0.costPickAllows p0 (some selfPerm.id) .tapTwoUntappedArtifacts selfPerm (tapSource := true) &&
    !gSelf0.canPayActivationNonManaCost p0 selfPerm tapTwoArtFraAb &&
    (gSelf0.validateActivation p0 selfPerm tapOtherCrAb).toOption.isNone &&
    gSelf0.costPickAllows p0 (some selfPerm.id) .sacrificeArtifact selfPerm (sacrificeOrExileSource := false) &&
    !gSelf0.costPickAllows p0 (some selfPerm.id) .sacrificeArtifact selfPerm (sacrificeOrExileSource := true) &&
    !gSelf0.costPickAllows p0 (some selfPerm.id) .sacrificeLegendaryArtifact selfPerm (sacrificeOrExileSource := true) &&
    !gSelf0.costPickAllows p0 (some selfPerm.id) .sacrificeArtifactOrCreature selfPerm (sacrificeOrExileSource := true) &&
    !gSelf0.costPickAllows p0 (some selfPerm.id) .sacrificeArtifactOrLand selfPerm (sacrificeOrExileSource := true) &&
    !gSelf0.canPayActivationNonManaCost p0 selfPerm sacSelfAndArtOrLandFraAb &&
    (gSelf0.validateActivation p0 selfPerm sacSelfAndLegArtAb).toOption.isNone &&
    gSelf0.costPickAllows p0 (some selfHand.id) .discardACard selfHand (discardOrExileHandSource := false) &&
    !gSelf0.costPickAllows p0 (some selfHand.id) .discardACard selfHand (discardOrExileHandSource := true) &&
    !gSelf0.costPickAllows p0 (some selfHand.id) .discardNonland selfHand (discardOrExileHandSource := true) &&
    !gSelf0.costPickAllows p0 (some selfHand.id) .discardLegendaryCard selfHand (discardOrExileHandSource := true) &&
    !gSelf0.costPickAllows p0 (some selfHand.id) .discardLegendarySameName selfHand (discardOrExileHandSource := true) &&
    !gSelf0.costPickAllows p0 (some selfHand.id) .sacrificeArtifactOrDiscardNonland selfHand (discardOrExileHandSource := true) &&
    !gSelf0.canPayActivationNonManaCost p0 selfHand discSelfAndLegHandFraAb

  -- 4b(ii). `{T}`-before-self-sacrifice payment when `!sacrificeOrExileSource` (both non-mana ability
  --         with `payLife` + 2nd pick AND mana ability):
  let selfSacAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.tapSelf, .payLife (.const 2), .sacrifice (.exact 1) (.filter (.hasType .artifact)), .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
    effect := Effect.gainLife 1
  }
  let selfSacArtDef : CardDef := {
    name := "P36i4 Censer", types := #[.artifact], activatedAbilities := #[selfSacAb]
  }
  let manaSelfSacArtDef : CardDef := {
    name := "P36i4 Mana Censer", types := #[.artifact]
    activatedAbilities := #[{ cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) (.filter (.hasType .artifact))], effect := { resolution := .addMana #[.colorless] } }]
  }
  let gTapSac0 := addPermanent (addPermanent g3 selfSacArtDef p0 p0) bear p0 p0
  let censer := (gTapSac0.permanentsOf p0).find? (·.name == selfSacArtDef.name) |>.get!
  let helperBear := (gTapSac0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let baseLife4 := (gTapSac0.player p0).life
  let preTapSacIdx := gTapSac0.events.size
  let gTapSacStarted := mustApply gTapSac0 p0 (.activate censer.id 0)
  let gTapSacAfterPick0 :=
    match gTapSacStarted.answerFraChoice p0 (.objects #[censer.id]) with
    | .ok g => g
    | .error e => panic! e
  let midPromptPayable :=
    gTapSacAfterPick0.proposalCostPromptStillPayable p0 gTapSacAfterPick0.pending
  let gTapSacFinished :=
    match gTapSacAfterPick0.answerFraChoice p0 (.objects #[helperBear.id]) with
    | .ok g => g
    | .error e => panic! e
  let tapBeforeSacEvents (g : Game) (startIdx : Nat) (oid : ObjectId) : Bool :=
    let slice := g.events.extract startIdx g.events.size
    let tapIdx? := slice.findIdx? (fun e =>
      match e.change with
      | .rules (.permanent (.tapped snap _)) => snap.id == some oid
      | _ => false)
    let sacIdx? := slice.findIdx? (fun e =>
      match e.change with
      | .rules (.zone (.moved prev _ .battlefield (.graveyard _) ..)) => prev.id == some oid
      | _ => false)
    match tapIdx?, sacIdx? with
    | some ti, some si => ti < si
    | _, _ => false

  let gManaTapSac0 := addPermanent g3 manaSelfSacArtDef p0 p0
  let manaCenser := (gManaTapSac0.permanentsOf p0)[0]!
  let preManaTapSacIdx := gManaTapSac0.events.size
  let gManaTapSacDone :=
    match gManaTapSac0.activateManaAbility p0 manaCenser.id 0 #[.colorless] #[manaCenser.id] with
    | .ok g => g
    | .error e => panic! e
  let tapBeforeSelfSacOk :=
    (gTapSac0.validateActivation p0 censer selfSacAb).isOk &&
    midPromptPayable &&
    tapBeforeSacEvents gTapSacFinished preTapSacIdx censer.id &&
    (gTapSacFinished.player p0).life == baseLife4 - 2 &&
    gTapSacFinished.proposedSpell.isNone &&
    gTapSacFinished.stack.size == 1 &&
    tapBeforeSacEvents gManaTapSacDone preManaTapSacIdx manaCenser.id &&
    (gManaTapSacDone.player p0).manaPool.colorless == 1

  -- 4b(iii). Multi-pick disjointness (`costPicksPayable`, `firstPayableCostPickSlice?`, `answerFraChoice`)
  --          and pre-`completeActivation` `canPayLife` on `.costPicks`, `.crew`, `.zemoBoastExile`:
  let disjointAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.any #[.hasType .artifact, .hasType .creature])), .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
    effect := Effect.gainLife 1
  }
  let disjointFraAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.hasType .artifact)), .tapObjects (.exact 2) (.all #[.hasType .artifact, .tapped false, .controlledBy .you])]
    effect := Effect.gainLife 1
  }
  let crTokDef : CardDef := { bear with name := "P36i4 Cr Token", isToken := true }
  let plainArt2Def : CardDef := {
    name := "P36i4 MV2 Art", manaCost := ManaCost.ofGeneric 2, types := #[.artifact]
  }
  let activatorDef : CardDef := {
    name := "P36i4 Altar", types := #[.enchantment], activatedAbilities := #[disjointAb]
  }
  let gDisjOne := addPermanent (addPermanent g3 crTokDef p0 p0) activatorDef p0 p0
  let altarOne := (gDisjOne.permanentsOf p0).find? (·.name == activatorDef.name) |>.get!
  let gDisjTwo := addPermanent gDisjOne plainArt2Def p0 p0
  let crTokObj := (gDisjTwo.permanentsOf p0).find? (·.name == crTokDef.name) |>.get!
  let plainArtObj := (gDisjTwo.permanentsOf p0).find? (·.name == plainArt2Def.name) |>.get!
  let altarTwo := (gDisjTwo.permanentsOf p0).find? (·.name == activatorDef.name) |>.get!
  let gDisjFraTwo := addPermanent gDisjTwo plainArt2Def p0 p0
  let gDisjFraThree := addPermanent gDisjFraTwo plainArt2Def p0 p0
  let picks2 : Array CostPick := #[.sacrificeArtifactOrCreature, .tapUntappedCreature]
  let gDisjStarted := mustApply gDisjTwo p0 (.activate altarTwo.id 0)
  let gDisjGreedy :=
    match gDisjStarted.answerFraChoice p0 (.objects #[crTokObj.id]) with
    | .ok g => g
    | .error e => panic! e
  let greedyStarves :=
    gDisjGreedy.proposedSpell.isNone &&
    gDisjGreedy.stack.isEmpty &&
    (gDisjGreedy.permanentsOf p0).any (·.id == crTokObj.id)
  let gDisjPick0Ok :=
    match gDisjStarted.answerFraChoice p0 (.objects #[plainArtObj.id]) with
    | .ok g => g
    | .error e => panic! e
  let gDisjDone :=
    match gDisjPick0Ok.answerFraChoice p0 (.objects #[crTokObj.id]) with
    | .ok g => g
    | .error e => panic! e

  -- Pre-`completeActivation` `canPayLife` across `.costPicks`, `.crew`, and `.zemoBoastExile`:
  let vehDef4 : CardDef := {
    name := "P36i4 Skiff", types := #[.artifact], subtypes := #["Vehicle"], power := some 4, toughness := some 4
  }
  let black15Def : CardDef :=
    creature "P36i4 Black15" { symbols := Array.replicate 15 (.colored .black) } #["Horror"] 2 2
  let gLife0 :=
    insertObject (addPermanent (addPermanent g3 bear p0 p0) vehDef4 p0 p0) black15Def p0 (.graveyard p0)
  let lBear := (gLife0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let lVeh := (gLife0.permanentsOf p0).find? (·.name == vehDef4.name) |>.get!
  let (gLife1, lBearAb) := gLife0.putStackAbility lBear p0 (abilityEffect := some (Effect.gainLife 1))
  let (gLife2, lVehAb) := gLife1.putStackAbility lVeh p0 (abilityEffect := some (Effect.gainLife 1))
  let bearLife5Prop : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := lBearAb.id, original := lBearAb
    originalSnapshot := gLife2.snapshot lBearAb, kind := .activatedAbility
    sourceId := some lBear.id, payLife := 5
  }
  let vehLife5Prop : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := lVehAb.id, original := lVehAb
    originalSnapshot := gLife2.snapshot lVehAb, kind := .activatedAbility
    sourceId := some lVeh.id, payLife := 5
  }
  let gBearLife20 := gLife2.change (.proposedSpell (some bearLife5Prop))
  let gBearLife4 := (gBearLife20.loseLife p0 16 (cause := some testCause))
  let gVehLife20 := gLife2.change (.proposedSpell (some vehLife5Prop))
  let gVehLife4 := (gVehLife20.loseLife p0 16 (cause := some testCause))
  let cpPrompt4 : Pending := .fraChoice p0 (.costPicks lBear.id #[.discardACard] false)
  let crewPrompt4 : Pending := .fraChoice p0 (.crew lVehAb.id lVeh.id 2)
  let zemoPrompt4 : Pending := .fraChoice p0 (.zemoBoastExile lBearAb.id lBear.id)
  let disjointAndCanPayLifeOk :=
    !gDisjOne.costPicksPayable p0 (some altarOne.id) picks2 &&
    (gDisjOne.validateActivation p0 altarOne disjointAb).toOption.isNone &&
    !gDisjFraTwo.canPayActivationNonManaCost p0 altarTwo disjointFraAb &&
    gDisjFraThree.canPayActivationNonManaCost p0 altarTwo disjointFraAb &&
    gDisjTwo.costPicksPayable p0 (some altarTwo.id) picks2 &&
    (gDisjTwo.costPickCandidates p0 (some altarTwo.id) .sacrificeArtifactOrCreature)[0]? == some crTokObj.id &&
    gDisjTwo.firstPayableCostPickSlice? p0 (some altarTwo.id) picks2 == some #[plainArtObj.id] &&
    greedyStarves &&
    gDisjDone.proposedSpell.isNone && gDisjDone.stack.size == 1 &&
    gBearLife20.proposalCostPromptStillPayable p0 cpPrompt4 &&
    !gBearLife4.proposalCostPromptStillPayable p0 cpPrompt4 &&
    gVehLife20.proposalCostPromptStillPayable p0 crewPrompt4 &&
    !gVehLife4.proposalCostPromptStillPayable p0 crewPrompt4 &&
    gBearLife20.proposalCostPromptStillPayable p0 zemoPrompt4 &&
    !gBearLife4.proposalCostPromptStillPayable p0 zemoPrompt4

  mustHold36i4 "4a.sneakPayability" sneakPayabilityOk &&
  mustHold36i4 "4a.morphCopiable" morphCopiableOk &&
  mustHold36i4 "4a.abilityZoneGuards" abilityZoneGuardsOk &&
  mustHold36i4 "4b.selfExclusion" selfExclusionOk &&
  mustHold36i4 "4b.tapBeforeSelfSac" tapBeforeSelfSacOk &&
  mustHold36i4 "4b.disjointAndCanPayLife" disjointAndCanPayLifeOk &&
  mustHold36i4 "4.replay"
    (replayOk36i4 #[gSnkCombat, gSnkProposed, gSnkFinishStolen, gSnkModeStolen,
      gFdSacGranterAsCost, gTapSacStarted, gTapSacAfterPick0, gTapSacFinished,
      gManaTapSacDone, gDisjStarted, gDisjGreedy, gDisjPick0Ok, gDisjDone, gBearLife4, gVehLife4])

end Phase36Item4EventAlignment

/-! ### Phase 37 Item 1: Checkpoint-replay continuation/batch isolation, per-batch CR 610.3 `queuedLinkedExile` chronology, `runPostCastCleanup` ordering, `dropCkptTarget`, and dynamic `nonDepBatches` tracking -/
section Phase37Item1EventAlignment

private def mustHold37i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase37Item1EventAlignment failed: {label}"

private def replayOk37i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def lifeGainsSince37i1 (g : Game) (startIdx : Nat) (p : PlayerId) : Array Nat :=
  (g.events.extract startIdx g.events.size).filterMap fun e =>
    match e.change with
    | .rules (.life (.gained q amt)) => if q == p then some amt else none
    | _ => none

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let auraDef : CardDef := { name := "P37i1 Aura", types := #[.enchantment] }
  let leyADef : CardDef := { name := "P37i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P37i1 LeyB", types := #[.enchantment] }

  -- 1a. `ckpt` continuation (`ckptCont? = some (.seq (+5) (.closeBatch origBid ...))`), paused batch (`origBid`),
  --     and `queuedLinkedExile` isolation during multi-departure `keptStream` replay + `restorePausedBatch (closeIfOrphaned := false)`:
  let gIso00 :=
    addPermanent (addPermanent (addPermanent (addPermanent g4 bear p3 p3) auraDef p2 p2) bear p0 p0) bear p0 p0
  let p3IsoBear := (gIso00.permanentsOf p3)[0]!
  let p2IsoAura := (gIso00.permanentsOf p2)[0]!
  let p0ExSrc := (gIso00.permanentsOf p0)[0]!
  let p0ExTarget := (gIso00.permanentsOf p0)[1]!
  let gIso0 := gIso00.exileUntilSourceLeaves (some p0ExSrc.id) p0ExTarget (cause := some testCause)
  let preExId := (gIso0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!.id
  let origBid : BatchId := ⟨900⟩
  let origStartIdx := gIso0.events.size
  let gIso1 :=
    ((gIso0.logLookAtTop p0 1 (looked := gIso0.scryLookedIds p0 1)).createEffect
      (.layered (.objects #[p3IsoBear.id]) (.control p0) (.whileSourceOnBattlefield p2IsoAura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pauseBatch origBid (some testCause) gIso0.objects gIso0.players gIso0.activeEffects (.scry p0 1) gIso0.stack,
      .queueLinkedExile #[preExId],
      .pending (.scry p0 1),
      .pendingReplacement (some (.seq (.gainLife p0 5 (some testCause)) (.closeBatch origBid origStartIdx))),
      .saveProposalCheckpoint ]
  let isoCkptIdx := gIso1.events.size
  let (gIso2, isoAb) := gIso1.putStackAbility p3IsoBear p0 (abilityEffect := some (Effect.gainLife 1))
  let isoProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := isoAb.id, original := isoAb
    originalSnapshot := gIso2.snapshot isoAb, kind := .activatedAbility
    sourceId := some p3IsoBear.id, resolutionCast := true
  }
  let gIso3 :=
    gIso2.changes #[
      .pushOuterPendingReplacement (.seq (.gainLife p0 5 (some testCause)) (.closeBatch origBid origStartIdx)),
      .pendingReplacement none,
      .proposedSpell (some isoProp),
      .pending (.chooseX p0) ]
  let gIsoAfterP1 := mustApply gIso3 p1 .concede
  let gIsoAfterP2 := mustApply gIsoAfterP1 p2 .concede
  let isoSlice := gIsoAfterP2.events.extract isoCkptIdx gIsoAfterP2.events.size
  let isoP1Batch? :=
    (isoSlice.find? (fun e =>
      match e.change with | .rules (.player (.leftGame q)) => q == p1 | _ => false)).bind (·.batch)
  let isoP2Batch? :=
    (isoSlice.find? (fun e =>
      match e.change with | .rules (.player (.leftGame q)) => q == p2 | _ => false)).bind (·.batch)
  let scryId := (gIso0.scryLookedIds p0 1)[0]!
  let gIsoScryDone := mustApply gIsoAfterP2 p0 (.scry #[scryId] #[])
  let ckptIsolationOk :=
    isoP1Batch?.isSome && isoP2Batch?.isSome &&
    isoP1Batch? != some origBid && isoP2Batch? != some origBid && isoP1Batch? != isoP2Batch? &&
    gIsoAfterP2.proposedSpell.isNone &&
    gIsoAfterP2.pending == .scry p0 1 &&
    -- `preExId` from `ckpt.queuedLinkedExile` was NOT prematurely returned by `p1`/`p2`'s batches:
    (gIsoAfterP2.findObject? preExId).any (·.zone == .exile) &&
    gIsoAfterP2.queuedLinkedExile == #[preExId] &&
    gIsoAfterP2.currentBatch.map Prod.fst == some origBid &&
    -- Once `.scry p0 1` finishes, `.seq (+5) (.closeBatch origBid ...)` runs `+5`, closes `origBid`, and returns `preExId`!
    gIsoScryDone.currentBatch.isNone &&
    (gIsoScryDone.followMovedToZone? preExId (· == .battlefield)).isSome &&
    lifeGainsSince37i1 gIsoScryDone isoCkptIdx p0 == #[5]

  -- 1b. Per-batch CR 610.3 `queuedLinkedExile` chronology (`[B1, return(L), B2]`),
  --     `.continueCheckpointReplay` pause chaining, and `dropCkptTarget` stripping tail `origCont` once:
  let sacArtAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.hasType .artifact))], effect := Effect.gainLife 1
  }
  let altarDef : CardDef := {
    name := "P37i1 Altar", types := #[.enchantment], activatedAbilities := #[sacArtAb]
  }
  let cageDef : CardDef := { name := "P37i1 Cage", types := #[.artifact] }
  let gChr0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent (addPermanent g4 cageDef p1 p1) bear p2 p2) altarDef p2 p2)
          leyADef p0 p0)
        leyBDef p0 p0)
      bear p0 p0
  let p1Cage := (gChr0.permanentsOf p1)[0]!
  let p2Linked := (gChr0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let twoPickAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.hasType .artifact)), .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 1
  }
  let altar2Def : CardDef := {
    name := "P37i1 Altar2", types := #[.enchantment], activatedAbilities := #[twoPickAb]
  }
  let gChrSync0 :=
    ((addPermanent (gChr0.exileUntilSourceLeaves (some p1Cage.id) p2Linked (cause := some testCause)) altar2Def p2 p2).createEffect
      (.control p1Cage.id p0) (cause := some testCause))
  let p2Altar2 := (gChrSync0.permanentsOf p2).find? (·.name == altar2Def.name) |>.get!
  let gChrSync1 := gChrSync0.createEffect (.control p2Altar2.id p0) (cause := some testCause)
  let gChrStarted := mustApply gChrSync1 p0 (.activate p2Altar2.id 0)
  let ckptSyncIdx := gChrStarted.proposalCheckpoint.get!.eventsSize
  let gChrAfterPick0 :=
    match gChrStarted.answerFraChoice p0 (.objects #[p1Cage.id]) with
    | .ok g => g
    | .error e => panic! e
  let gChrAfterP1 := mustApply gChrAfterPick0 p1 .concede
  let gChrAfterP2 := mustApply gChrAfterP1 p2 .concede
  let syncSlice := gChrAfterP2.events.extract ckptSyncIdx gChrAfterP2.events.size
  let b1Idx? := syncSlice.findIdx? (fun e =>
    match e.change with | .rules (.player (.leftGame q)) => q == p1 | _ => false)
  let retIdx? := syncSlice.findIdx? (fun e =>
    match e.change with
    | .rules (.zone (.moved prev _ .exile .battlefield ..)) => prev.name == bear.name && prev.owner == p2
    | _ => false)
  let b2Idx? := syncSlice.findIdx? (fun e =>
    match e.change with | .rules (.player (.leftGame q)) => q == p2 | _ => false)
  let b2RemovedFromBf := syncSlice.any (fun e =>
    match e.change with
    | .rules (.zone (.ceasedToExist obj)) => obj.name == bear.name && obj.owner == p2 && obj.zone == .battlefield
    | _ => false)
  let syncChronologyOk :=
    match b1Idx?, retIdx?, b2Idx? with
    | some i1, some ir, some i2 =>
      i1 < ir && ir < i2 && b2RemovedFromBf && gChrAfterP2.proposedSpell.isNone
    | _, _, _ => false

  -- Paused `.continueCheckpointReplay` + `dropCkptTarget` tail stripping (`ckptOrigCont? = some (+9)`):
  let gPauseBase0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent (addPermanent g4 cageDef p1 p1) altar2Def p2 p2) leyADef p0 p0)
        leyBDef p0 p0)
      bear p0 p0
  let p1PauseCage := (gPauseBase0.permanentsOf p1)[0]!
  let p2PauseAltar := (gPauseBase0.permanentsOf p2)[0]!
  let p0Victim := (gPauseBase0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let chrLeyA := (gPauseBase0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let chrLeyB := (gPauseBase0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let cRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some chrLeyA, counterKind := some .plusOnePlusOne }
  let cRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some chrLeyB, counterKind := some .plusOnePlusOne }
  let gPause0 :=
    ((((((gPauseBase0.exileUntilSourceLeaves (some p1PauseCage.id) p0Victim (cause := some testCause)).createEffect
      (.control p1PauseCage.id p0) (cause := some testCause)).createEffect
      (.control p2PauseAltar.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := cRidA, source := some chrLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := cRidB, source := some chrLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 9 (some testCause))),
      .saveProposalCheckpoint ])
  let pauseCkptIdx := gPause0.events.size
  let gPause1 :=
    gPause0.changes #[
      .pushOuterPendingReplacement (.gainLife p0 9 (some testCause)),
      .pendingReplacement none,
      .beginProposalAction .costAction ]
  let (gPause2, pauseAb) := gPause1.putStackAbility p2PauseAltar p0 (abilityEffect := some (Effect.gainLife 1))
  let sacCause := some (EventCause.costPayment .sacrifice p0 (some pauseAb.id))
  -- Sacrifice `p1PauseCage` inside `.costAction` batch so `queuedLinkedExile` flushes and pauses on `cRidA`/`cRidB`:
  let gPauseSac :=
    gPause2.withBatch sacCause fun g =>
      g.sacrificeToGraveyard (g.object! p1PauseCage.id) "sac" (cause := sacCause)
  let gPauseRet := mustApply gPauseSac p0 (.chooseReplacement cRidA)
  let pauseProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := pauseAb.id, original := pauseAb
    originalSnapshot := gPauseRet.snapshot pauseAb, kind := .activatedAbility
    sourceId := some p2PauseAltar.id, resolutionCast := true
  }
  let gPauseReady :=
    (gPauseRet.changes #[.proposedSpell (some pauseProp), .pending (.chooseX p0)]).change .endProposalAction
  let gPauseP1 := mustApply gPauseReady p1 .concede
  let gPauseP2 := mustApply gPauseP1 p2 .concede
  let pausedBeforeB2 :=
    gPauseP2.sbaPaused &&
    !(gPauseP2.events.extract pauseCkptIdx gPauseP2.events.size).any (fun e =>
      match e.change with | .rules (.player (.leftGame q)) => q == p2 | _ => false)
  let gPauseDone := mustApply gPauseP2 p0 (.chooseReplacement cRidB)
  let pSlice := gPauseDone.events.extract pauseCkptIdx gPauseDone.events.size
  let pb1? := pSlice.findIdx? (fun e =>
    match e.change with | .rules (.player (.leftGame q)) => q == p1 | _ => false)
  let pret? := pSlice.findIdx? (fun e =>
    match e.change with
    | .rules (.zone (.moved prev _ .exile .battlefield ..)) => prev.owner == p0 && prev.name == bear.name
    | _ => false)
  let pb2? := pSlice.findIdx? (fun e =>
    match e.change with | .rules (.player (.leftGame q)) => q == p2 | _ => false)
  let pauseReplayAndDropOk :=
    pausedBeforeB2 &&
    (match pb1?, pret?, pb2? with
     | some i1, some ir, some i2 => i1 < ir && ir < i2
     | _, _, _ => false) &&
    gPauseDone.proposedSpell.isNone &&
    (gPauseDone.permanentsOf p0).any (fun o => o.name == bear.name && o.status.plusOnePlusOne == 3) &&
    lifeGainsSince37i1 gPauseDone pauseCkptIdx p0 == #[9]

  -- 1c. `runPostCastCleanup` runs BEFORE `ckptPending` on reversal so multi-card
  --     `.cascadeBottom` opens `Pending.resolveRandom (.orderInto ...)` and chains `.restorePending ckptPending`:
  let gClean00 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent (addPermanent g4 bear p3 p3) auraDef p1 p1) bear p0 p0)
          bear p0 p0)
        bear p0 p0)
      bear p0 .exile
  let cOuterCard := (gClean00.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!
  let p0Bears := gClean00.permanentsOf p0
  let (gClean0a, cCardId) := gClean00.move p0Bears[0]!.id .exile (cause := some testCause)
  let (gClean0b, cOther1) := gClean0a.move p0Bears[1]!.id .exile (cause := some testCause)
  let (gClean0, cOther2) := gClean0b.move p0Bears[2]!.id .exile (cause := some testCause)
  let p3CleanBear := (gClean0.permanentsOf p3)[0]!
  let p1CleanAura := (gClean0.permanentsOf p1)[0]!
  let outerPrompt : Pending := .fraChoice p0 (.mayCastCards #[cOuterCard.id] true false)
  let gClean1 :=
    (gClean0.createEffect (.layered (.objects #[p3CleanBear.id]) (.control p0) (.whileSourceOnBattlefield p1CleanAura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pending outerPrompt,
      .postCastCleanup (some (.cascadeBottom p0 cCardId #[cOther1, cOther2])),
      .saveProposalCheckpoint ]
  let (gClean2, cleanAb) := gClean1.putStackAbility p3CleanBear p0 (abilityEffect := some (Effect.gainLife 1))
  let cleanProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := cleanAb.id, original := cleanAb
    originalSnapshot := gClean2.snapshot cleanAb, kind := .activatedAbility
    sourceId := some p3CleanBear.id, resolutionCast := true
  }
  let gCleanReady := gClean2.changes #[.proposedSpell (some cleanProp), .pending (.chooseX p0)]
  let gCleanAborted :=
    match gCleanReady.apply p1 .concede with
    | .ok g => g
    | .error e => panic! e
  let orderOpenedFirst :=
    match gCleanAborted.pending with
    | .resolveRandom (.orderInto ids (.library q) _) => q == p0 && ids.size == 3
    | _ => false
  let gCleanOrdered := mustApply gCleanAborted p0 (.supplyOrder #[cCardId, cOther1, cOther2])
  let postCastCleanupBeforePendingOk :=
    orderOpenedFirst &&
    gCleanOrdered.pending == outerPrompt

  -- 1d. Inter-departure `nonDepBatches`: `p1` departs -> `p0` opens reversible mana batch pausing on
  --     `.chooseReplacement` -> `p2` departs -> `p0` finishes `.chooseReplacement` -> `p3` departs (aborting):
  let petalDef : CardDef := { name := "P37i1 Petal", types := #[.artifact], activatedAbilities := #[ActivatedAbility.manaTapSacrificeAnyColor] }
  let rgInstDef : CardDef := {
    name := "P37i1 RG Instant", manaCost := ⟨#[.colored .red, .colored .green]⟩, types := #[.instant]
    spellEffect := some (Effect.gainLife 1)
  }
  let p4 : PlayerId := ⟨4⟩
  let g5 := g4.change (.addPlayer { id := p4, name := "Chandra" })
  let gInter0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent g5 petalDef p0 p0) leyADef p0 p0) leyBDef p0 p0)
      rgInstDef p3 .exile
  let iPetId := (gInter0.permanentsOf p0).find? (·.name == petalDef.name) |>.get!.id
  let iLeyA := (gInter0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let iLeyB := (gInter0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let p3SpellId := (gInter0.objects.filter (fun o => o.zone == .exile && o.owner == p3))[0]!.id
  let iRidA : ReplacementId := { kind := .exileOppDeath, object := some iLeyA }
  let iRidB : ReplacementId := { kind := .exileOppDeath, object := some iLeyB }
  let gInter1 :=
    (((gInter0.createEffect (.permission p0 (.playFromExile p3SpellId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.replacement {
        id := iRidA, source := some iLeyA, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some iPetId) false }) (cause := some testCause)).createEffect
      (.replacement {
        id := iRidB, source := some iLeyB, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some iPetId) false }) (cause := some testCause))
  let gInterCast := mustApply gInter1 p0 (.cast p3SpellId)
  let gInterAfterP1 := mustApply gInterCast p1 .concede
  let gInterManaPaused := mustApply gInterAfterP1 p0 (.tapForMana iPetId (.colored .red))
  let gInterAfterP2 := mustApply gInterManaPaused p2 .concede
  let gInterManaDone := mustApply gInterAfterP2 p0 (.chooseReplacement iRidA)
  let gInterAborted := mustApply gInterManaDone p3 .concede
  let interDepManaReversedOk :=
    (gInterManaDone.player p0).manaPool.red == 1 &&
    (gInterAborted.player p1).leftTheGame &&
    (gInterAborted.player p2).leftTheGame &&
    (gInterAborted.player p3).leftTheGame &&
    gInterAborted.proposedSpell.isNone &&
    gInterAborted.proposalCheckpoint.isNone &&
    (gInterAborted.player p0).manaPool.total == 0 &&
    (gInterAborted.permanentsOf p0).any (fun o => o.id == iPetId && !o.status.tapped)

  mustHold37i1 "1a.ckptIsolation" ckptIsolationOk &&
  mustHold37i1 "1b.syncChronology" syncChronologyOk &&
  mustHold37i1 "1b.pauseReplayAndDrop" pauseReplayAndDropOk &&
  mustHold37i1 "1c.postCastCleanupBeforePending" postCastCleanupBeforePendingOk &&
  mustHold37i1 "1d.interDepManaReversed" interDepManaReversedOk &&
  mustHold37i1 "1.replay"
    (replayOk37i1 #[gIsoAfterP1, gIsoAfterP2, gIsoScryDone, gChrAfterP1, gChrAfterP2,
      gPauseP1, gPauseP2, gPauseDone, gCleanAborted, gCleanOrdered,
      gInterAfterP1, gInterManaPaused, gInterAfterP2, gInterManaDone, gInterAborted])

end Phase37Item1EventAlignment

/-! ### Phase 37 Item 2: `Decisions.reverseOrResumePopped` alignment, `.restorePending` `shouldSplitBatch` LIFO split, multi-departure `saved?` clearing, and `.chooseLegend` / pre-SBA flush continuations -/
section Phase37Item2EventAlignment

private def mustHold37i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase37Item2EventAlignment failed: {label}"

private def replayOk37i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def lifeGainsSince37i2 (g : Game) (startIdx : Nat) (p : PlayerId) : Array Nat :=
  (g.events.extract startIdx g.events.size).filterMap fun e =>
    match e.change with
    | .rules (.life (.gained q amt)) => if q == p then some amt else none
    | _ => none

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let auraDef : CardDef := { name := "P37i2 Aura", types := #[.enchantment] }
  let leyADef : CardDef := { name := "P37i2 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P37i2 LeyB", types := #[.enchantment] }
  let morphDef2 : CardDef := {
    creature "P37i2 Morph" ManaCost.empty #["Human"] 2 2 with keywords := #[.morph CostSpec.empty]
  }

  -- 2a(i). `reverseOrResumePopped` (`| some popped =>`): preserves `extraDepartureOuters (+3)`,
  --        clears already-consumed `ckptOrigCont? (+99)`, and sequences `ckptPending` (`.mayCastCards`)
  --        AFTER `popped (+4)` and BEFORE `restored? (+8)`:
  let gRr00 := insertObject (addPermanent (addPermanent g4 morphDef2 p0 p0) bear p0 p0) bear p0 .exile
  let rrMorphInitId := (gRr00.permanentsOf p0).find? (fun (o : GameObject) => o.name == morphDef2.name) |>.get!.id
  let gRr0 := setFaceDown gRr00 rrMorphInitId true
  let rrMorph := gRr0.object! rrMorphInitId
  let rrExCard := (gRr0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!
  let rrOuterPrompt : Pending := .fraChoice p0 (.mayCastCards #[rrExCard.id] true false)
  let gRr1 :=
    gRr0.changes #[
      .pushContinuationFrame {},
      .pending rrOuterPrompt,
      .pendingReplacement (some (.gainLife p0 99 (some testCause))),
      .saveProposalCheckpoint,
      -- Consume `ckptOrigCont? (+99)` during the proposal BEFORE any departure:
      .pendingReplacement none ]
  let rrProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := rrMorph.id, original := rrMorph
    originalSnapshot := gRr1.snapshot rrMorph, kind := .turnFaceUp
    sourceId := some rrMorph.id, resolutionCast := true
  }
  let gRr3 :=
    ((gRr1.record (GameEvent.playerLeftGame gRr1.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).changes #[
      .proposedSpell (some rrProp),
      .pending (.fraChoice p0 (.costPicks rrMorph.id #[.tapUntappedCreature] false)),
      -- Earlier non-aborting departure `p1` pushed `+3` onto `outerPendingReplacements`:
      .pushOuterPendingReplacement (.gainLife p0 3 (some testCause)),
      -- Current departure `p2` pushed `popped = +4` on top of `outerPendingReplacements`,
      -- and stole `rrMorph` so `.restorePending` sees `!sourceStillPayable` and reverses via `reverseOrResumePopped`:
      .pushOuterPendingReplacement (.gainLife p0 4 (some testCause)) ]).record
      (GameEvent.playerLeftGame gRr1.turnNumber p2 (cause := some (.gameRule .playerLeftGame)))
  let gRrStolen := gRr3.createEffect (.control rrMorph.id p2) (cause := some testCause)
  let gRrResumed :=
    (gRrStolen.resumePendingReplacement
      (.seq
        (.restorePending (.fraChoice p0 (.costPicks rrMorph.id #[.tapUntappedCreature] false)) true none #[p1, p2] none)
        (.gainLife p0 88 (some testCause)))).drainPendingContinuations
  -- `popped (+4)` ran BEFORE `rrOuterPrompt` reopened; `extraDepartureOuters (+3)` waits behind `rrOuterPrompt`;
  -- and neither consumed `+99` nor aborted proposal-tail `+88` ran!
  let rrBeforeDeclineOk :=
    gRrResumed.proposedSpell.isNone &&
    gRrResumed.pending == rrOuterPrompt &&
    lifeGainsSince37i2 gRrResumed 0 p0 == #[4]
  let gRrFinished := (mustApply gRrResumed p0 .decline).drainPendingContinuations
  -- Also verify unconsumed `ckptOrigCont? = some (+8)` (`restored?`): `popped (+4)` -> `rrOuterPrompt` -> `restored (+8)`:
  let gRrUncons1 :=
    gRr0.changes #[
      .pushContinuationFrame {},
      .pending rrOuterPrompt,
      .pendingReplacement (some (.gainLife p0 8 (some testCause))),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement (.gainLife p0 8 (some testCause)),
      .pendingReplacement none ]
  let rrUnconsProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := rrMorph.id, original := rrMorph
    originalSnapshot := gRrUncons1.snapshot rrMorph, kind := .turnFaceUp
    sourceId := some rrMorph.id, resolutionCast := true
  }
  let gRrUnconsStolen :=
    (((gRrUncons1.changes #[
      .proposedSpell (some rrUnconsProp),
      .pending (.fraChoice p0 (.costPicks rrMorph.id #[.tapUntappedCreature] false)),
      .pushOuterPendingReplacement (.gainLife p0 4 (some testCause)) ]).record
      (GameEvent.playerLeftGame gRrUncons1.turnNumber p2 (cause := some (.gameRule .playerLeftGame)))).createEffect
      (.control rrMorph.id p2) (cause := some testCause))
  let gRrUnconsResumed :=
    (gRrUnconsStolen.resumePendingReplacement
      (.restorePending (.fraChoice p0 (.costPicks rrMorph.id #[.tapUntappedCreature] false)) true none #[p2] none)).drainPendingContinuations
  let gRrUnconsFinished := (mustApply gRrUnconsResumed p0 .decline).drainPendingContinuations
  let reverseOrResumeSomeOk :=
    rrBeforeDeclineOk &&
    lifeGainsSince37i2 gRrFinished 0 p0 == #[4, 3] &&
    gRrUnconsResumed.pending == rrOuterPrompt &&
    lifeGainsSince37i2 gRrUnconsResumed 0 p0 == #[4] &&
    lifeGainsSince37i2 gRrUnconsFinished 0 p0 == #[4, 8] &&
    replayOk37i2 #[gRrUnconsResumed, gRrUnconsFinished]

  -- 2a(ii). `reverseOrResumePopped` (`| none =>`): clears consumed `ckptOrigCont? (+77)`,
  --         preserves `extraDepartureOuters (+5)`, validates `ckptPending` against `departed`,
  --         and grants priority when clearing consumed `ckptOrigCont?` empties `continuations`:
  let gRn00 := addPermanent (addPermanent g4 morphDef2 p0 p0) bear p0 p0
  let rnMorphInitId := (gRn00.permanentsOf p0).find? (fun (o : GameObject) => o.name == morphDef2.name) |>.get!.id
  let gRn0 := setFaceDown gRn00 rnMorphInitId true
  let rnMorph := gRn0.object! rnMorphInitId
  let gRn1 :=
    gRn0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 77 (some testCause))),
      .saveProposalCheckpoint,
      .pendingReplacement none ]
  let rnProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := rnMorph.id, original := rnMorph
    originalSnapshot := gRn1.snapshot rnMorph, kind := .turnFaceUp
    sourceId := some rnMorph.id, resolutionCast := true
  }
  let gRn3 :=
    (((gRn1.record (GameEvent.playerLeftGame gRn1.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).createEffect
      (.control rnMorph.id p2) (cause := some testCause)).changes #[
      .proposedSpell (some rnProp),
      .pushOuterPendingReplacement (.gainLife p0 5 (some testCause)) ])
  let gRnDone :=
    (gRn3.resumePendingReplacement
      (.restorePending (.fraChoice p0 (.costPicks rnMorph.id #[.tapUntappedCreature] false)) false none #[p1] none)).drainPendingContinuations
  let reverseOrResumeNoneOk :=
    gRnDone.proposedSpell.isNone &&
    lifeGainsSince37i2 gRnDone 0 p0 == #[5]

  -- 2b. `.restorePending` `shouldSplitBatch` LIFO `outerPendingReplacements` split when `rewindProposal.isSome`:
  let gSp0 := addPermanent (addPermanent g4 bear p3 p3) auraDef p2 p2
  let spBear := (gSp0.permanentsOf p3)[0]!
  let spAura := (gSp0.permanentsOf p2)[0]!
  let gSp1 :=
    (gSp0.createEffect (.layered (.objects #[spBear.id]) (.control p0) (.whileSourceOnBattlefield spAura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 9 (some testCause))),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement (.gainLife p0 9 (some testCause)),
      .pendingReplacement none ]
  let (gSp2, spAb) := gSp1.putStackAbility spBear p0 (abilityEffect := some (Effect.gainLife 1))
  let spProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := spAb.id, original := spAb
    originalSnapshot := gSp2.snapshot spAb, kind := .activatedAbility
    sourceId := some spBear.id, resolutionCast := true
  }
  let splitBid : BatchId := ⟨910⟩
  let (gSpAfterP2, _, _, _) :=
    (gSp2.changes #[.proposedSpell (some spProp), .pending (.chooseX p0)]).playerLeavesGameCore p2
      (deferRestore := true) (rewindProposalIn := some false)
  let gSpSplitReady :=
    gSpAfterP2.changes #[
      .pauseBatch splitBid (some testCause) gSpAfterP2.objects gSpAfterP2.players gSpAfterP2.activeEffects .none gSpAfterP2.stack ]
  let gSpDrained :=
    (gSpSplitReady.resumePendingReplacement
      (.seq
        (.closeBatch splitBid gSpSplitReady.events.size)
        (.seq
          (.restorePending .none false none #[p2] (some true))
          (.gainLife p0 6 (some testCause))))).drainPendingContinuations
  let shouldSplitLifoOk :=
    gSpDrained.proposedSpell.isNone &&
    gSpDrained.currentBatch.isNone &&
    lifeGainsSince37i2 gSpDrained 0 p0 == #[6, 9]

  -- 2c. Multi-departure loop (`leavePlayersWhoLostCore`) clearing `saved?` proposal prompt when subsequent
  --     departing player aborts `p0`'s proposal:
  let gMd0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent (addPermanent g4 bear p3 p3) auraDef p2 p2) bear p1 p1)
        leyADef p0 p0)
      leyBDef p0 p0
  let mdBear := (gMd0.permanentsOf p3)[0]!
  let mdAura := (gMd0.permanentsOf p2)[0]!
  let mdP1Perm := (gMd0.permanentsOf p1)[0]!
  let mdLeyA := (gMd0.permanentsOf p0).find? (fun (o : GameObject) => o.name == leyADef.name) |>.get!.id
  let mdLeyB := (gMd0.permanentsOf p0).find? (fun (o : GameObject) => o.name == leyBDef.name) |>.get!.id
  let mdRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some mdLeyA, counterKind := some .plusOnePlusOne }
  let mdRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some mdLeyB, counterKind := some .plusOnePlusOne }
  let p0Link := addPermanent gMd0 bear p0 p0
  let p0LinkBear := (p0Link.permanentsOf p0).find? (fun (o : GameObject) => o.name == bear.name) |>.get!
  let gMd1 :=
    ((((p0Link.exileUntilSourceLeaves (some mdP1Perm.id) p0LinkBear (cause := some testCause)).createEffect
      (.layered (.objects #[mdBear.id]) (.control p0) (.whileSourceOnBattlefield mdAura.id))
      (cause := some testCause)).createEffect
      (.replacement {
        id := mdRidA, source := some mdLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := mdRidB, source := some mdLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let (gMd2, mdAb) := gMd1.putStackAbility mdBear p0 (abilityEffect := some (Effect.gainLife 1))
  let mdProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := mdAb.id, original := mdAb
    originalSnapshot := gMd2.snapshot mdAb, kind := .activatedAbility, sourceId := some mdBear.id
  }
  -- `p2` is at 0 life while `p1` concedes: `p1` leaves first (stashing `saved? = some (.chooseX p0)` and
  -- pausing on `mdRidA`/`mdRidB`), then once `mdRidA` is chosen `checkSBACountedWithLeaves` processes `p2` at 0 life
  -- via `leavePlayersWhoLostCore (savedIn := some (.chooseX p0))`, where `p2`'s departure aborts `mdProp` and clears `saved?`:
  let gMdZeroP2 :=
    (gMd2.changes #[.proposedSpell (some mdProp), .pending (.chooseX p0)]).loseLife p2 20 (cause := some testCause)
  let gMdSbaPaused := mustApply gMdZeroP2 p1 .concede
  let gMdResolved := mustApply gMdSbaPaused p0 (.chooseReplacement mdRidA)
  let multiDepSavedClearOk :=
    gMdSbaPaused.sbaPaused &&
    (gMdResolved.player p1).leftTheGame &&
    (gMdResolved.player p2).leftTheGame &&
    gMdResolved.proposedSpell.isNone &&
    gMdResolved.proposalCheckpoint.isNone &&
    gMdResolved.pending == Pending.none

  -- 2d. Pre-SBA flush `.checkSBA` chaining, `finishAndGrantPriority` `.chooseLegend` `pendingPriority`,
  --     and `afterWardResolved` `.chooseLegend` chaining:
  -- 2d(i) `checkSBA` flushes dismissed paused batch that opens `.chooseReplacement`, chaining `.checkSBA`
  --       so 0-toughness creature dies once `.chooseReplacement` is answered:
  let zeroDef : CardDef := creature "P37i2 Zero" ManaCost.empty #["Spirit"] 0 0
  let gFl0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent g4 bear p1 p1) bear p0 p0) leyADef p0 p0)
      leyBDef p0 p0
  let flJail := (gFl0.permanentsOf p1)[0]!
  let flVic := (gFl0.permanentsOf p0).find? (fun (o : GameObject) => o.name == bear.name) |>.get!
  let flLeyA := (gFl0.permanentsOf p0).find? (fun (o : GameObject) => o.name == leyADef.name) |>.get!.id
  let flLeyB := (gFl0.permanentsOf p0).find? (fun (o : GameObject) => o.name == leyBDef.name) |>.get!.id
  let flRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some flLeyA, counterKind := some .plusOnePlusOne }
  let flRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some flLeyB, counterKind := some .plusOnePlusOne }
  let flBid : BatchId := ⟨920⟩
  let gFlBase :=
    addPermanent
      (((gFl0.exileUntilSourceLeaves (some flJail.id) flVic (cause := some testCause)).createEffect
        (.replacement {
          id := flRidA, source := some flLeyA, controller := some p0, affectedPlayer := p0,
          kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
        (.replacement {
          id := flRidB, source := some flLeyB, controller := some p0, affectedPlayer := p0,
          kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
      zeroDef p0 p0
  let gFlLeft := gFlBase.record (GameEvent.playerLeftGame gFlBase.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))
  let flExiledId := (gFlLeft.objects.filter (fun (o : GameObject) => o.zone == .exile && o.owner == p0))[0]!.id
  let gFlPaused :=
    gFlLeft.changes #[
      .pushContinuationFrame {},
      .pauseBatch flBid (some testCause) gFlLeft.objects gFlLeft.players gFlLeft.activeEffects
        (.chooseReplacement p1 #[]) gFlLeft.stack,
      .queueLinkedExile #[flExiledId],
      .pendingReplacement (some (.closeBatch flBid gFlLeft.events.size)) ]
  let gFlSba1 := gFlPaused.checkSBA
  let gFlSbaDone := mustApply gFlSba1 p0 (.chooseReplacement flRidA)
  let preSbaFlushChainsCheckSbaOk :=
    gFlSba1.sbaPaused &&
    (gFlSba1.permanentsOf p0).any (fun (o : GameObject) => o.name == zeroDef.name) &&
    !(gFlSbaDone.permanentsOf p0).any (fun (o : GameObject) => o.name == zeroDef.name)

  -- 2d(ii) `finishAndGrantPriority p1` stashes `pendingPriority = some p1` when drain opens `.chooseLegend`:
  let legDef : CardDef := { bear with name := "P37i2 Legend", supertypes := #[.legendary] }
  let gFg0 := addPermanent (addPermanent g4 legDef p0 p0) legDef p0 p0
  let legs := gFg0.permanentsOf p0
  let gFg1 :=
    (gFg0.changes #[
      .pushContinuationFrame {},
      .pendingPriority (some p2),
      .pendingReplacement (some .checkSBA) ]).finishAndGrantPriority p1
  let gFgKept := mustApply gFg1 p0 (.keepLegend legs[0]!.id)
  let finishGrantLegendPrioOk :=
    (match gFg1.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
    gFg1.pendingPriority == some p1 &&
    gFgKept.priority == p1

  -- 2d(iii) `afterWardResolved` chains `.afterWardResolved` when draining opens `.chooseLegend`:
  let gWd0 := addPermanent (addPermanent g4 legDef p0 p0) legDef p0 p0
  let wdLegs := gWd0.permanentsOf p0
  let gWd1 :=
    (gWd0.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 4 (some testCause)),
      .pushOuterPendingReplacement .checkSBA ]).afterWardResolved.drainPendingContinuations
  let gWdKept := mustApply gWd1 p0 (.keepLegend wdLegs[0]!.id)
  let afterWardLegendOk :=
    (match gWd1.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
    gWdKept.pending == Pending.none &&
    (gWdKept.player p0).life == (24 : Int)

  mustHold37i2 "2a.reverseOrResumeSome" reverseOrResumeSomeOk &&
  mustHold37i2 "2a.reverseOrResumeNone" reverseOrResumeNoneOk &&
  mustHold37i2 "2b.shouldSplitLifo" shouldSplitLifoOk &&
  mustHold37i2 "2c.multiDepSavedClear" multiDepSavedClearOk &&
  mustHold37i2 "2d.preSbaFlushChainsCheckSba" preSbaFlushChainsCheckSbaOk &&
  mustHold37i2 "2d.finishGrantLegendPrio" finishGrantLegendPrioOk &&
  mustHold37i2 "2d.afterWardLegend" afterWardLegendOk &&
  mustHold37i2 "2.replay"
    (replayOk37i2 #[gRrResumed, gRrFinished, gRnDone, gSpDrained,
      gMdSbaPaused, gMdResolved, gFlSba1, gFlSbaDone, gFg1, gFgKept, gWd1, gWdKept])

end Phase37Item2EventAlignment

/-! ### Phase 37 Item 3: `reconcileControlAfterTransition` CR 800.4c exile, CR 506.4 combat removal, `.ringBearer` loss, paused `phaseOutPermanents` / `.teferi` / `completeTurnFaceUp`, and accurate CR 800.4b/c logs -/
section Phase37Item3EventAlignment

private def mustHold37i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase37Item3EventAlignment failed: {label}"

private def replayOk37i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let leyADef : CardDef := { name := "P37i3 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P37i3 LeyB", types := #[.enchantment] }

  -- Helper: `p3`-owned `p1Bear0` put onto `.battlefield` under `p1`'s control (`defaultController = some p1`),
  -- stolen by `p0` before `p1` leaves so `p1Bear0` stays on `.battlefield` until `p0`'s control effect ends (CR 800.4c):
  let auraDef : CardDef := { name := "P37i3 Anchor", types := #[.enchantment] }
  let tokDef : CardDef := { bear with name := "P37i3 Token", isToken := true }
  let gBase0 :=
    addPermanent (addPermanent (addPermanent g4 bear p3 p1) auraDef p0 p0) tokDef p0 p0
  let p1Bear0 := (gBase0.permanentsOf p1)[0]!
  let p0Anchor := (gBase0.permanentsOf p0).find? (·.name == auraDef.name) |>.get!
  let p0Tok := (gBase0.permanentsOf p0).find? (·.name == tokDef.name) |>.get!

  -- 3a(i). `Attachments.ceaseToExist` (token outside `.battlefield` whose `.whileInZone` control effect kept
  --        `p1Bear0` on `.battlefield`) + `.fraEmblem` expiry reconcile CR 800.4c exile, CR 506.4, and `.ringBearer`:
  let gTokAnchored :=
    (gBase0.createEffect (.layered (.objects #[p1Bear0.id]) (.control p0) (.whileSourceOnBattlefield p0Anchor.id))
      (cause := some testCause)).concede p1
  let (gTokMoved, tokInGyId) := gTokAnchored.move p0Tok.id (.graveyard p0) (cause := some testCause)
  let gTokWithGyCtrl :=
    gTokMoved.createEffect (.layered (.objects #[p1Bear0.id]) (.control p0) (.whileInZone tokInGyId (.graveyard p0)))
      (cause := some testCause)
  let (gTokAnchorGone, _) := gTokWithGyCtrl.move p0Anchor.id .exile (cause := some testCause)
  -- Now `p1Bear0` is controlled ONLY by `.whileInZone tokInGyId (.graveyard p0)`! Mark it attacking & ring-bearer:
  let gTokCombat :=
    (gTokAnchorGone.record (GameEvent.becameAttacking gTokAnchorGone.turnNumber
      (gTokAnchorGone.snapshot (gTokAnchorGone.object! p1Bear0.id)) (.player p2) (cause := testCause))).record
      (GameEvent.ringTempted gTokAnchorGone.turnNumber p0 (some p1Bear0.id) 1 (cause := some testCause))
  let gTokCeased := gTokCombat.ceaseToExist tokInGyId (cause := some (.stateBased .tokenOutsideBattlefield))
  let ceaseReconcileOk :=
    (gTokCombat.controllerOf (gTokCombat.object! p1Bear0.id)) == some p0 &&
    (gTokCeased.player p0).ringBearerId.isNone &&
    (gTokCeased.followMovedToZone? p1Bear0.id (· == .exile)).isSome &&
    gTokCeased.events.any (fun e =>
      match e.change with
      | .rules (.combat (.removedFromCombat eo)) => eo.id == some p1Bear0.id
      | _ => false)

  -- Temporary `.fraEmblem` expiry reconciling CR 800.4c exile:
  let embDef : CardDef := { name := "P37i3 Emblem", types := #[] }
  let gEmb0 := insertObject (gBase0.createEffect
    (.layered (.objects #[p1Bear0.id]) (.control p0) (.whileSourceOnBattlefield p0Anchor.id))
    (cause := some testCause) |>.concede p1) embDef p0 .command
  let embId := (gEmb0.objects.filter (fun o => o.zone == .command && o.name == embDef.name))[0]!.id
  let embEffId : EffectId := ⟨1500⟩
  let gEmb1 :=
    (gEmb0.record (GameEvent.effectCreated gEmb0.turnNumber embEffId (.fraEmblemUntilTurnOf embId p2) testCause)).createEffect
      (.layered (.objects #[p1Bear0.id]) (.control p0) (.whileInZone embId .command))
      (cause := some testCause)
  let (gEmb2, _) := gEmb1.move p0Anchor.id .exile (cause := some testCause)
  let gEmbExpired := gEmb2.expireEffectById embEffId (cause := some (.turnBased .expireAtStepBegin))
  let emblemReconcileOk :=
    (gEmbExpired.findObject? embId).isNone &&
    (gEmbExpired.followMovedToZone? p1Bear0.id (· == .exile)).isSome

  -- 3a(ii). `Phasing.phaseOut` CR 800.4c exile and `Phasing.phaseIn` combat removal + `.ringBearer` loss:
  let gPh0 :=
    (gBase0.createEffect (.layered (.objects #[p1Bear0.id]) (.control p0) (.whileSourceOnBattlefield p0Anchor.id))
      (cause := some testCause)).concede p1
  let gPhOut := gPh0.phaseOut (gPh0.object! p0Anchor.id) (cause := some testCause)
  let gPhIn0 := addPermanent (addPermanent g4 bear p2 p2) auraDef p0 p0
  let p2PhBear := (gPhIn0.permanentsOf p2)[0]!
  let p0PhSrc := (gPhIn0.permanentsOf p0)[0]!
  let gPhIn1 :=
    (gPhIn0.createEffect (.layered (.objects #[p2PhBear.id]) (.control p0) (.whileSourceOnBattlefield p0PhSrc.id))
      (cause := some testCause)).phaseOut (gPhIn0.object! p0PhSrc.id) (cause := some testCause)
  let gPhIn2 :=
    (gPhIn1.record (GameEvent.becameAttacking gPhIn1.turnNumber
      (gPhIn1.snapshot (gPhIn1.object! p2PhBear.id)) (.player p0) (cause := testCause))).record
      (GameEvent.ringTempted gPhIn1.turnNumber p2 (some p2PhBear.id) 1 (cause := some testCause))
  let gPhInDone := gPhIn2.phaseIn (gPhIn2.object! p0PhSrc.id) (cause := some testCause)
  let phaseReconcileOk :=
    (gPhOut.followMovedToZone? p1Bear0.id (· == .exile)).isSome &&
    gPhInDone.controllerOf (gPhInDone.object! p2PhBear.id) == some p0 &&
    !(gPhInDone.object! p2PhBear.id).status.attacking &&
    (gPhInDone.player p2).ringBearerId.isNone

  -- 3b(i). `phaseOutPermanents`, `phaseOutPermanentsLoop`, and `.teferi` (`FrcPostStep.teferiExileSpell`):
  let gPop0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent (addPermanent g4 bear p3 p1) forest p3 p1) auraDef p2 p2)
          bear p2 p2)
        leyADef p0 p0)
      leyBDef p0 p0
  let popP1Bear := (gPop0.permanentsOf p1).find? (·.name == bear.name) |>.get!
  let popP1Land := (gPop0.permanentsOf p1).find? (·.name == forest.name) |>.get!
  let popP2Anchor := (gPop0.permanentsOf p2).find? (·.name == auraDef.name) |>.get!
  let popP2Second := (gPop0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let teferiDef : CardDef := {
    name := "P37i3 Protection", manaCost := ManaCost.empty, types := #[.instant]
    spellEffect := some {
      targeting := { spec := .player, prefer := .opponent }, maxTargets := 1
      resolution := .frc .teferi
    }
  }
  let gTef0 :=
    insertObject
      (gPop0.createEffect (.layered (.objects #[popP1Bear.id, popP1Land.id]) (.control p2) (.whileSourceOnBattlefield popP2Anchor.id))
        (cause := some testCause) |>.concede p1)
      teferiDef p0 (.hand p0)
  let tefCardId := (gTef0.player p0).hand.find? (fun id => (gTef0.object! id).name == teferiDef.name) |>.get!
  let gTefCast := mustApply (mustApply gTef0 p0 (.cast tefCardId)) p0 (.targets #[.player p2])
  let tefStackId := gTefCast.stack[0]!.objectId
  let gTefResolved := gTefCast.resolveTop
  -- Also verify `phaseOutPermanentsLoop` resuming after a mid-batch pause inside the same `BatchId`:
  let popPauseBid : BatchId := ⟨930⟩
  let gPopLoop0 := addPermanent (addPermanent g4 bear p2 p2) auraDef p2 p2
  let popA := (gPopLoop0.permanentsOf p2)[0]!
  let popB := (gPopLoop0.permanentsOf p2)[1]!
  let gPopLoop1 :=
    (gPopLoop0.changes #[
      .pauseBatch popPauseBid (some testCause) gPopLoop0.objects gPopLoop0.players gPopLoop0.activeEffects
        (.chooseReplacement p0 #[]) gPopLoop0.stack ]).phaseOut popA (cause := some testCause)
  let gPopLoopResumed :=
    gPopLoop1.resumePendingReplacement
      (.seq (.phaseOutPermanentsLoop #[popB.id] (some testCause)) (.closeBatch popPauseBid gPopLoop0.events.size))
  let popPhasedBatches :=
    gPopLoopResumed.events.filterMap fun e =>
      match e.change with
      | .rules (.permanent (.phasedOut _ _)) => some e.batch
      | _ => none
  let teferiAndPhaseOutOk :=
    (gTefResolved.object! popP2Anchor.id).status.phasedOut &&
    (gTefResolved.object! popP2Second.id).status.phasedOut &&
    (gTefResolved.object! popP1Bear.id).status.phasedOut &&
    (gTefResolved.followMovedToZone? popP1Land.id (· == .exile)).isSome &&
    (gTefResolved.followMovedToZone? tefStackId (· == .exile)).isSome &&
    (gPopLoopResumed.object! popA.id).status.phasedOut &&
    (gPopLoopResumed.object! popB.id).status.phasedOut &&
    popPhasedBatches == #[some popPauseBid, some popPauseBid] &&
    gPopLoopResumed.currentBatch.isNone

  -- Also test `FrcPostStep.teferiExileSpell` directly across a paused `.chooseReplacement` so the deferred post-step path is proven:
  let gTefPause0 :=
    insertObject
      (addPermanent (addPermanent g4 leyADef p0 p0) leyBDef p0 p0)
      teferiDef p0 .stack
  let tefStackObj := (gTefPause0.objects.filter (fun o => o.zone == .stack && o.name == teferiDef.name))[0]!
  let tpLeyA := (gTefPause0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let tpLeyB := (gTefPause0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let tpRidA : ReplacementId := { kind := .exileOppDeath, object := some tpLeyA }
  let tpRidB : ReplacementId := { kind := .exileOppDeath, object := some tpLeyB }
  let gTefPause1 :=
    gTefPause0.changes #[
      .pushStack { objectId := tefStackObj.id, controller := p0, targets := #[.player p2] },
      .pushContinuationFrame {
        resolvingSpell := some tefStackObj.id
        resolutionFinish := some (.spell { objectId := tefStackObj.id, controller := p0, targets := #[.player p2] }
          (gTefPause0.snapshot tefStackObj) false) },
      .pending (.chooseReplacement p0 #[tpRidA, tpRidB]),
      .pendingReplacement (some (.finishFrcPostStep .teferiExileSpell)) ]
  let gTefPostDone :=
    ((gTefPause1.changes #[.pending Pending.none, .pendingReplacement none]).resumePendingReplacement
      (.finishFrcPostStep .teferiExileSpell)).completeActiveResolutions
  let teferiPostStepPausedOk :=
    (gTefPostDone.followMovedToZone? tefStackObj.id (· == .exile)).isSome

  -- 3b(ii). Scoped Layer 2 `.control` (`creaturesWithout Keyword.flying`) across Layer 1 `.copy`,
  --         `completeTurnFaceUp`, and `transformPermanent`:
  let flyerDef : CardDef := {
    creature "P37i3 Flyer" ManaCost.empty #["Bird"] 2 2 with
    keywords := #[Keyword.flying, .morph CostSpec.empty]
  }
  let dfcDef : CardDef := {
    creature "P37i3 WalkerFront" ManaCost.empty #["Human"] 2 2 with
    otherFace := some flyerDef
  }
  let gL10 := addPermanent (addPermanent g4 flyerDef p3 p1) auraDef p0 p0
  let p1Flyer := (gL10.permanentsOf p1)[0]!
  let p0L1Src := (gL10.permanentsOf p0)[0]!
  -- Face-down `p1Flyer` has NO flying in Layer 1, so `.creaturesWithout #[Keyword.flying]` gives `p0` control!
  let gL1Fd :=
    (setFaceDown gL10 p1Flyer.id true).createEffect
      (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) (.whileSourceOnBattlefield p0L1Src.id))
      (cause := some testCause)
  let gL1Left := gL1Fd.concede p1
  -- Turning `p1Flyer` face up via `completeTurnFaceUp` restores `flying := true` in Layer 1, ending the scoped
  -- Layer 2 `.control p0` effect onto departed `p1` -> exiled under CR 800.4c AND priority granted to `p0`!
  let gL1TurnedUp := (gL1Left.completeTurnFaceUp p0 p1Flyer.id).1
  -- `transformPermanent` into back face `flyerDef` (`flying := true`) also ends `.creaturesWithout #[Keyword.flying]` control!
  let gTr0 := addPermanent (addPermanent g4 dfcDef p3 p1) auraDef p0 p0
  let trDfcId := (gTr0.permanentsOf p1)[0]!.id
  let trSrcId := (gTr0.permanentsOf p0)[0]!.id
  let gTrLeft :=
    (gTr0.createEffect (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) (.whileSourceOnBattlefield trSrcId))
      (cause := some testCause)).concede p1
  let gTrDone := gTrLeft.transformPermanent p0 (some trDfcId) (cause := some testCause)
  -- Layer 1 `.copy` granting flying to `p3`-owned, `p1`-defaultControlled non-flying `bear`:
  let gCpSetup := addPermanent (addPermanent g4 bear p3 p1) auraDef p0 p0
  let cpBearId := (gCpSetup.permanentsOf p1)[0]!.id
  let cpSrcId := (gCpSetup.permanentsOf p0)[0]!.id
  let gCp0 :=
    (gCpSetup.createEffect
      (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) (.whileSourceOnBattlefield cpSrcId))
      (cause := some testCause)).concede p1
  let gCpCopied := gCp0.createEffect (.copy cpBearId flyerDef (untilEot := true)) (cause := some testCause)
  -- Layer 1 `.copy` EXPIRY restoring `flying` on `p3`-owned, `p1`-defaultControlled flyer:
  let gCpExp0 := addPermanent (addPermanent g4 flyerDef p3 p1) auraDef p0 p0
  let expFlyerId := (gCpExp0.permanentsOf p1)[0]!.id
  let expSrcId := (gCpExp0.permanentsOf p0)[0]!.id
  let gCpExp1 :=
    ((gCpExp0.createEffect (.copy expFlyerId bear (untilEot := true)) (cause := some testCause)).createEffect
      (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) (.whileSourceOnBattlefield expSrcId))
      (cause := some testCause)).concede p1
  let copyEffId := (gCpExp1.activeEffects.find? (fun (_, s) =>
    match s with | .layered _ (.copy _) _ => true | _ => false)).get!.1
  let gCpExpired := gCpExp1.expireEffectById copyEffId (cause := some testCause)
  let layer1ControlReconcileOk :=
    (gL1TurnedUp.followMovedToZone? p1Flyer.id (· == .exile)).isSome &&
    gL1TurnedUp.priority == p0 &&
    (gTrDone.followMovedToZone? trDfcId (· == .exile)).isSome &&
    (gCpCopied.followMovedToZone? cpBearId (· == .exile)).isSome &&
    (gCpExpired.followMovedToZone? expFlyerId (· == .exile)).isSome

  -- 3c. `restoreControlUntilSourceLeaves`: no false `"does not change control (CR 800.4b)"` log when fallback left,
  --     `.ringBearer` cleared on both singleton and non-singleton arms, and `endControlExileLoop` suppresses
  --     `"is exiled (CR 800.4c)"` log if target already left before its deferred step runs:
  let gRc0 :=
    ((gBase0.createEffect (.layered (.objects #[p1Bear0.id]) (.control p0) (.untilSourceLeaves p0Anchor.id))
      (cause := some testCause)).concede p1).record
      (GameEvent.ringTempted gBase0.turnNumber p0 (some p1Bear0.id) 1 (cause := some testCause))
  let (gRcMoved, _) := gRc0.move p0Anchor.id .exile (cause := some testCause)
  let gNs0 := addPermanent (addPermanent g4 bear p2 p2) auraDef p0 p0
  let nsBear := (gNs0.permanentsOf p2)[0]!
  let nsSrc := (gNs0.permanentsOf p0)[0]!
  let gNs1 :=
    (gNs0.createEffect (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) (.whileSourceOnBattlefield nsSrc.id))
      (cause := some testCause)).record
      (GameEvent.ringTempted gNs0.turnNumber p0 (some nsBear.id) 1 (cause := some testCause))
  let gNsRestored := gNs1.restoreControlUntilSourceLeaves nsSrc.id (cause := some testCause)
  let gNoExLog :=
    g4.resumePendingReplacement
      (.endControlExileLoop #[] (some (.gameRule .playerLeftGame))
        (some (⟨9999⟩, "Ghost is exiled (CR 800.4c)")))
  let restoreLogsAndRingOk :=
    (gRcMoved.followMovedToZone? p1Bear0.id (· == .exile)).isSome &&
    (gRcMoved.player p0).ringBearerId.isNone &&
    !gRcMoved.log.any (fun s => (s.splitOn "CR 800.4b").length > 1) &&
    (gNsRestored.player p0).ringBearerId.isNone &&
    !gNoExLog.log.any (fun s => (s.splitOn "CR 800.4c").length > 1)

  mustHold37i3 "3a.ceaseReconcile" ceaseReconcileOk &&
  mustHold37i3 "3a.emblemReconcile" emblemReconcileOk &&
  mustHold37i3 "3a.phaseReconcile" phaseReconcileOk &&
  mustHold37i3 "3b.teferiAndPhaseOut" teferiAndPhaseOutOk &&
  mustHold37i3 "3b.teferiPostStepPaused" teferiPostStepPausedOk &&
  mustHold37i3 "3b.layer1ControlReconcile" layer1ControlReconcileOk &&
  mustHold37i3 "3c.restoreLogsAndRing" restoreLogsAndRingOk &&
  mustHold37i3 "3.replay"
    (replayOk37i3 #[gTokCeased, gEmbExpired, gPhOut, gPhInDone,
      gTefResolved, gPopLoopResumed, gTefPostDone, gL1TurnedUp, gTrDone, gCpCopied, gCpExpired, gRcMoved, gNoExLog])

end Phase37Item3EventAlignment

/-! ### Phase 37 Item 4: `activateFromHand` / `sourceDiscardedFromHandForCost`, paused `ManaAbilities` continuations, and mid-proposal payability / `decline` / loyalty / `completeTurnFaceUp` reversals -/
section Phase37Item4EventAlignment

private def mustHold37i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase37Item4EventAlignment failed: {label}"

private def replayOk37i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let leyADef : CardDef := { name := "P37i4 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P37i4 LeyB", types := #[.enchantment] }

  -- 4a. `payActivationExtraCosts` + `sourceStillPayable` `activateFromHand` (source stays in hand AND
  --     `sourceDiscardedFromHandForCost` across multi-pick `CostPick`):
  let keepInHandAb : ActivatedAbility := {
    activeZones := #[.hand], cost := CostSpec.ofItems #[.payLife (.const 2)], effect := Effect.gainLife 5
  }
  let selfDiscMultiAb : ActivatedAbility := {
    activeZones := #[.hand]
    cost := CostSpec.ofItems #[.payLife (.const 2), .discard (.exact 1) .hand, .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
    effect := Effect.gainLife 5
  }
  let handKeepDef : CardDef := {
    name := "P37i4 HandChannel", types := #[.creature], power := some 2, toughness := some 2
    activatedAbilities := #[keepInHandAb]
  }
  let handMultiDef : CardDef := {
    name := "P37i4 HandMulti", types := #[.creature], power := some 2, toughness := some 2
    activatedAbilities := #[selfDiscMultiAb]
  }
  let gFh0 :=
    insertObject
      (insertObject (addPermanent g3 bear p0 p0) handKeepDef p0 (.hand p0))
      handMultiDef p0 (.hand p0)
  let fhBear := (gFh0.permanentsOf p0)[0]!
  let fhKeepId := (gFh0.player p0).hand.find? (fun id => (gFh0.object! id).name == handKeepDef.name) |>.get!
  let fhMultiId := (gFh0.player p0).hand.find? (fun id => (gFh0.object! id).name == handMultiDef.name) |>.get!
  let gFhKeepActivated := mustApply gFh0 p0 (.activate fhKeepId 0)
  let gFhMultiStarted := mustApply gFh0 p0 (.activate fhMultiId 0)
  let gFhMultiPick0 :=
    match gFhMultiStarted.answerFraChoice p0 (.objects #[fhMultiId]) with
    | .ok g => g
    | .error e => panic! e
  let gFhMultiDone :=
    match gFhMultiPick0.answerFraChoice p0 (.objects #[fhBear.id]) with
    | .ok g => g
    | .error e => panic! e
  let activateFromHandOk :=
    (gFhKeepActivated.player p0).hand.contains fhKeepId &&
    (gFhKeepActivated.player p0).life == (18 : Int) &&
    gFhKeepActivated.stack.size == 1 &&
    gFhMultiPick0.sourceDiscardedFromHandForCost fhMultiId (some gFhMultiPick0.proposedSpell.get!.spellId) &&
    gFhMultiPick0.proposalCostPromptStillPayable p0 gFhMultiPick0.pending &&
    (gFhMultiDone.player p0).life == (18 : Int) &&
    gFhMultiDone.proposedSpell.isNone &&
    gFhMultiDone.stack.size == 1

  -- 4b. Departed-player and `.restorePending`-validated paused `ManaAbilities` continuations:
  let painPetalDef : CardDef := {
    name := "P37i4 PainPetal", types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self]
      effect := { resolution := .addMana #[.colored .red] }
    }]
  }
  -- Test 1: `p0` activates `PainPetal` at priority (`prevPending = .none`), pausing on `leyA`/`leyB`;
  --         `p0` concedes; `finishActivateManaAbilityPostSac` skips `abilityActivated`/`manaAdded` and grants priority to `p1`!
  let gMa0 :=
    addPermanent (addPermanent (addPermanent g3 painPetalDef p0 p0) leyADef p0 p0) leyBDef p0 p0
  let maPet := (gMa0.permanentsOf p0).find? (·.name == painPetalDef.name) |>.get!
  let maLeyA := (gMa0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let maLeyB := (gMa0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let maRidA : ReplacementId := { kind := .exileOppDeath, object := some maLeyA }
  let maRidB : ReplacementId := { kind := .exileOppDeath, object := some maLeyB }
  let gMa1 :=
    (gMa0.createEffect
      (.replacement {
        id := maRidA, source := some maLeyA, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some maPet.id) false }) (cause := some testCause)).createEffect
      (.replacement {
        id := maRidB, source := some maLeyB, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some maPet.id) false }) (cause := some testCause)
  let gMaPaused :=
    match gMa1.activateManaAbility p0 maPet.id 0 #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gMaConceded := mustApply gMaPaused p0 .concede
  -- Test 2: living `p0` controls `p2`'s face-down morph creature `maMorph` ONLY via `.whileSourceOnBattlefield maPet.id`,
  --         and opens `.activateManaAbilities p0` on `.turnFaceUp` (`cost := ManaCost.ofGeneric 1`).
  --         When `p0` sacrifices `maPet` for mana (pausing on `maRidA`/`maRidB` with `prevPending = .activateManaAbilities p0`)
  --         and chooses `maRidA`, `maPet` leaves `.battlefield`, `maMorph` returns to `p2`, and `finishActivateManaAbilityPostSac`
  --         routes `prevPending` through `.restorePending`, which sees `!sourceStillPayable` and reverses cleanly!
  let maMorphDef : CardDef := {
    creature "P37i4 ManaMorph" ManaCost.empty #["Human"] 3 3 with keywords := #[.morph (CostSpec.ofGeneric 1)]
  }
  let gMaVal0 := addPermanent gMa1 maMorphDef p2 p2
  let maMorphId := (gMaVal0.permanentsOf p2)[0]!.id
  let gMaVal1 :=
    (setFaceDown gMaVal0 maMorphId true).createEffect
      (.layered (.objects #[maMorphId]) (.control p0) (.whileSourceOnBattlefield maPet.id))
      (cause := some testCause)
  let maMorphObj := gMaVal1.object! maMorphId
  let maMorphProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := maMorphId, sourceId := some maMorphId
    original := maMorphObj, originalSnapshot := gMaVal1.snapshot maMorphObj, kind := .turnFaceUp
  }
  let gMaValPrompt :=
    gMaVal1.changes #[
      .saveProposalCheckpoint,
      .proposedSpell (some maMorphProp),
      .pending (.activateManaAbilities p0) ]
  let gMaValPaused :=
    match gMaValPrompt.activateManaAbility p0 maPet.id 0 #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gMaValResolved := mustApply gMaValPaused p0 (.chooseReplacement maRidA)
  let manaAbilityGuardsOk :=
    (gMaConceded.player p0).leftTheGame &&
    (gMaConceded.player p0).manaPool.total == 0 &&
    gMaConceded.priority == p1 &&
    gMaValResolved.proposedSpell.isNone &&
    gMaValResolved.pending == Pending.none &&
    (gMaValResolved.player p0).manaPool.total == 0 &&
    (gMaValResolved.permanentsOf p0).any (·.id == maPet.id) &&
    (gMaValResolved.object! maMorphId).status.faceDown

  -- 4c. Mid-proposal `announceMode`, multi-pick `CostPick` (`sourceStillPayable` + `canPayLife`),
  --     `.discardForAdditionalCost`, `.sacrificePermanent`, `completeTurnFaceUp` (control loss vs morph-granter),
  --     post-sacrifice loyalty `becomeActivated`, and unpayable-prompt `decline`:
  -- (i) `announceMode` reverses when `sourceStillPayable` is false:
  let modalAbDef : CardDef := {
    name := "P37i4 ModalRod", types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := Effect.gainLife 1
      otherModes := #[Effect.gainLife 2]
    }]
  }
  let gAm0 := addPermanent g3 modalAbDef p0 p0
  let rodId := (gAm0.permanentsOf p0)[0]!.id
  let gAmStarted := mustApply gAm0 p0 (.activate rodId 0)
  let gAmStolen := gAmStarted.createEffect (.control rodId p2) (cause := some testCause)
  let gAmReversed := mustApply gAmStolen p0 (.chooseMode 0)
  let announceModeReversalOk :=
    gAmStarted.pending == .chooseMode p0 &&
    gAmReversed.proposedSpell.isNone &&
    gAmReversed.stack.isEmpty

  -- (ii) Multi-pick `CostPick` reverses on lost `canPayLife` before pick 1, AND `FraAnswer.decline` on `paid := true`
  --      reverses when `!proposalCostPromptStillPayable`:
  let lifeMultiAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.payLife (.const 5), .sacrifice (.exact 1) (.filter (.hasType .artifact)), .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
    effect := Effect.gainLife 1
  }
  let lifeMultiArtDef : CardDef := {
    name := "P37i4 LifeAltar", types := #[.artifact], activatedAbilities := #[lifeMultiAb]
  }
  let lmBaubleDef : CardDef := { name := "P37i4 SacBauble", types := #[.artifact] }
  let gLm0 := addPermanent (addPermanent (addPermanent g3 lifeMultiArtDef p0 p0) lmBaubleDef p0 p0) bear p0 p0
  let lmArtId := (gLm0.permanentsOf p0).find? (·.name == lifeMultiArtDef.name) |>.get!.id
  let lmBaubleId := (gLm0.permanentsOf p0).find? (·.name == lmBaubleDef.name) |>.get!.id
  let lmBearId := (gLm0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gLmStarted := mustApply gLm0 p0 (.activate lmArtId 0)
  -- Pay pick 0 (`sacrificeArtifact` on `lmBaubleId`, setting `paid := true`):
  let gLmPick0 :=
    match gLmStarted.answerFraChoice p0 (.objects #[lmBaubleId]) with
    | .ok g => g
    | .error e => panic! e
  let gLmLowLife := gLmPick0.loseLife p0 17 (cause := some testCause)
  let gLmPick1Reversed :=
    match gLmLowLife.answerFraChoice p0 (.objects #[lmBearId]) with
    | .ok g => g
    | .error e => panic! e
  let gLmDeclineReversed :=
    match gLmLowLife.answerFraChoice p0 .decline with
    | .ok g => g
    | .error e => panic! e
  let costPickAndDeclineOk :=
    (gLmPick1Reversed.permanentsOf p0).any (·.id == lmBaubleId) &&
    gLmPick1Reversed.proposedSpell.isNone &&
    (gLmDeclineReversed.permanentsOf p0).any (·.id == lmBaubleId) &&
    gLmDeclineReversed.proposedSpell.isNone

  -- Shared `.turnFaceUp` setup for (iii) and (iv): `p0` controls `p2`'s face-down morph creature `p2MorphId`
  -- via `.whileSourceOnBattlefield p0HelmId`:
  let morphCrDef : CardDef := {
    creature "P37i4 MorphSpy" ManaCost.empty #["Human"] 3 3 with keywords := #[.morph CostSpec.empty]
  }
  let ctrlRelicDef : CardDef := { name := "P37i4 Helm", types := #[.artifact] }
  let gTf0 := addPermanent (addPermanent g3 morphCrDef p2 p2) ctrlRelicDef p0 p0
  let p2MorphId := (gTf0.permanentsOf p2)[0]!.id
  let p0HelmId := (gTf0.permanentsOf p0)[0]!.id
  let gTf1 :=
    (setFaceDown gTf0 p2MorphId true).createEffect
      (.layered (.objects #[p2MorphId]) (.control p0) (.whileSourceOnBattlefield p0HelmId))
      (cause := some testCause)
  let mSnapObj := gTf1.object! p2MorphId
  let tfProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := p2MorphId, sourceId := some p2MorphId
    original := mSnapObj, originalSnapshot := gTf1.snapshot mSnapObj
    kind := .turnFaceUp, needsSacrificeOther := true
  }

  -- (iii) `.discardForAdditionalCost` and `.sacrificePermanent` reverse (on BOTH answer and `Action.decline`)
  --       when `!proposalCostPromptStillPayable`:
  let gUnpayBase :=
    (addPermanent gTf1 lmBaubleDef p0 p0).changes #[.saveProposalCheckpoint, .proposedSpell (some tfProp)]
  let gUnpayStolen := gUnpayBase.createEffect (.control p2MorphId p2) (cause := some testCause)
  let gDiscUnpay := gUnpayStolen.change (.pending (.discardForAdditionalCost p0))
  let h0Id := (gDiscUnpay.player p0).hand[0]!
  let gDiscRev := mustApply gDiscUnpay p0 (.discard h0Id)
  let gDiscDeclineRev := mustApply gDiscUnpay p0 .decline
  let gSacUnpay := gUnpayStolen.change (.pending (.sacrificePermanent p0 p2MorphId))
  let sacCandId := (gSacUnpay.permanentsOf p0).find? (fun (o : GameObject) => o.name == lmBaubleDef.name) |>.get!.id
  let gSacRev := mustApply gSacUnpay p0 (.sacrifice sacCandId)
  let gSacDeclineRev := mustApply gSacUnpay p0 .decline
  let discardAndSacGuardOk :=
    !gDiscUnpay.proposalCostPromptStillPayable p0 gDiscUnpay.pending &&
    !gSacUnpay.proposalCostPromptStillPayable p0 gSacUnpay.pending &&
    gDiscRev.proposedSpell.isNone &&
    (gDiscRev.player p0).hand.contains h0Id &&
    gDiscDeclineRev.proposedSpell.isNone &&
    (gDiscDeclineRev.player p0).hand.contains h0Id &&
    gSacRev.proposedSpell.isNone &&
    (gSacRev.permanentsOf p0).any (·.id == sacCandId) &&
    gSacDeclineRev.proposedSpell.isNone &&
    (gSacDeclineRev.permanentsOf p0).any (·.id == sacCandId)

  -- (iv) `completeTurnFaceUp` reverses when sacrificing the morph-cost permanent loses control of `spellId`:
  let gTfPrompt :=
    gTf1.changes #[.saveProposalCheckpoint, .proposedSpell (some tfProp), .pending (.sacrificePermanent p0 p2MorphId)]
  -- Sacrificing `p0HelmId` returns `p2MorphId` to `p2`, so `completeTurnFaceUp` reverses (restoring `p0HelmId`
  -- to `.battlefield` and keeping `p2MorphId` face-down)!
  let gTfReversed := mustApply gTfPrompt p0 (.sacrifice p0HelmId)
  let turnFaceUpControlLossReversesOk :=
    gTfReversed.proposedSpell.isNone &&
    (gTfReversed.permanentsOf p0).any (·.id == p0HelmId) &&
    (gTfReversed.object! p2MorphId).status.faceDown

  -- (v) Post-sacrifice loyalty `becomeActivated`: sacrificing the permanent granting control of planeswalker `src`
  --     reverses via `becomeActivated` instead of activating an opponent's planeswalker!
  let pwSacAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty (.minus 2)]
    effect := Effect.gainLife 3
  }
  let pwDef : CardDef := {
    name := "P37i4 Walker", types := #[.planeswalker], loyalty := some 3
    activatedAbilities := #[pwSacAb]
  }
  let gPw0 := addPermanent (addPermanent g3 pwDef p2 p2) ctrlRelicDef p0 p0
  let pwId := (gPw0.permanentsOf p2)[0]!.id
  let pwHelmId := (gPw0.permanentsOf p0)[0]!.id
  let gPw1 :=
    (gPw0.recordPutCounters pwId .loyalty 3 (some p2) (cause := some testCause)).createEffect
      (.layered (.objects #[pwId]) (.control p0) (.whileSourceOnBattlefield pwHelmId))
      (cause := some testCause)
  let gPwCkpt := gPw1.change .saveProposalCheckpoint
  let (gPw2, pwStackAb) := gPwCkpt.putStackAbility (gPwCkpt.object! pwId) p0 (abilityEffect := some (Effect.gainLife 3))
  let pwProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := pwStackAb.id, original := pwStackAb
    originalSnapshot := gPw2.snapshot pwStackAb, kind := .activatedAbility
    sourceId := some pwId, activation := some pwSacAb, needsSacrificeOther := true
  }
  let gPwPrompt :=
    gPw2.changes #[.proposedSpell (some pwProp), .pending (.sacrificePermanent p0 pwId)]
  let gPwReversed := mustApply gPwPrompt p0 (.sacrifice pwHelmId)
  -- And when `p0` sacrifices an unrelated artifact (keeping control & 3 loyalty >= 2), loyalty IS paid and ability stays on stack!
  let extraArtDef : CardDef := { name := "P37i4 Bauble", types := #[.artifact] }
  let gPwOk0 := addPermanent gPw1 extraArtDef p0 p0
  let baubleId := (gPwOk0.permanentsOf p0).find? (·.name == extraArtDef.name) |>.get!.id
  let gPwOkCkpt := gPwOk0.change .saveProposalCheckpoint
  let (gPwOk2, pwOkStackAb) := gPwOkCkpt.putStackAbility (gPwOkCkpt.object! pwId) p0 (abilityEffect := some (Effect.gainLife 3))
  let pwOkProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := pwOkStackAb.id, original := pwOkStackAb
    originalSnapshot := gPwOk2.snapshot pwOkStackAb, kind := .activatedAbility
    sourceId := some pwId, activation := some pwSacAb, needsSacrificeOther := true
  }
  let gPwOkPrompt :=
    gPwOk2.changes #[.proposedSpell (some pwOkProp), .pending (.sacrificePermanent p0 pwId)]
  let gPwSucceeded := mustApply gPwOkPrompt p0 (.sacrifice baubleId)
  let loyaltyPostSacOk :=
    gPwReversed.proposedSpell.isNone &&
    gPwReversed.stack.isEmpty &&
    (gPwReversed.permanentsOf p0).any (·.id == pwHelmId) &&
    (gPwReversed.object! pwId).status.loyaltyCounters == 3 &&
    gPwSucceeded.proposedSpell.isNone &&
    gPwSucceeded.stack.size == 1 &&
    (gPwSucceeded.object! pwId).status.loyaltyCounters == 1

  mustHold37i4 "4a.activateFromHand" activateFromHandOk &&
  mustHold37i4 "4b.manaAbilityGuards" manaAbilityGuardsOk &&
  mustHold37i4 "4c.announceModeReversal" announceModeReversalOk &&
  mustHold37i4 "4c.costPickAndDecline" costPickAndDeclineOk &&
  mustHold37i4 "4c.discardAndSacGuard" discardAndSacGuardOk &&
  mustHold37i4 "4c.turnFaceUpControlLossReverses" turnFaceUpControlLossReversesOk &&
  mustHold37i4 "4c.loyaltyPostSac" loyaltyPostSacOk &&
  mustHold37i4 "4.replay"
    (replayOk37i4 #[gFhKeepActivated, gFhMultiStarted, gFhMultiPick0, gFhMultiDone,
      gMaPaused, gMaConceded, gMaValPaused, gMaValResolved,
      gAmStarted, gAmReversed, gLmStarted, gLmPick0, gLmPick1Reversed, gLmDeclineReversed,
      gDiscRev, gDiscDeclineRev, gSacRev, gSacDeclineRev, gTfReversed, gPwReversed, gPwSucceeded])

end Phase37Item4EventAlignment

/-! ### Phase 38 Item 1: `Core.replayKeptStreamCore` `ObjectId`/`EffectId` collision remapping, raw-battlefield `queueUnreturnedLinked`, multi-hop `followMoved`, `g.over` finality, and mid-`.continueCheckpointReplay` departure invariants -/
section Phase38Item1EventAlignment

private def mustHold38i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase38Item1EventAlignment failed: {label}"

private def replayOk38i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let cageDef : CardDef := { name := "P38i1 Cage", types := #[.enchantment] }
  let altarDef : CardDef := { name := "P38i1 Altar", types := #[.artifact] }
  let leyADef : CardDef := { name := "P38i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P38i1 LeyB", types := #[.enchantment] }
  let tokDef : CardDef := { bear with name := "P38i1 Token", isToken := true }

  -- 1a & 1b. `Core.replayKeptStreamCore` `ObjectId` + `EffectId` collision remapping across live CR 610.3
  --          returns (`ZoneEvent.created`, multi-hop `ZoneEvent.moved` + `followMoved`, `TriggerQueueEvent.putOnStack`,
  --          `CastEvent.abilityActivated`, and `ContinuousEffectEvent.created`), plus `queueUnreturnedLinked`
  --          raw-battlefield cross-batch scoping:
  let gColBase0 :=
    insertObject
      (addPermanent
        (addPermanent (addPermanent (addPermanent g4 cageDef p1 p1) altarDef p2 p2) bear p0 p0)
        bear p3 p3)
      bear p0 (.hand p0)
  let p1Cage := (gColBase0.permanentsOf p1)[0]!
  let p2Altar := (gColBase0.permanentsOf p2)[0]!
  let p0Victim := (gColBase0.permanentsOf p0)[0]!
  let p3CloneTarget := (gColBase0.permanentsOf p3)[0]!
  let p0HandCard := (gColBase0.player p0).hand.back!
  let copyChoiceId : ReplacementId := {
    kind := .entersAsCopyCreatureUntilEot p3CloneTarget.id
    object := none
  }
  -- Give `p0`'s exiled `p0Victim` a mandatory `.entersAsCopyCreatureUntilEot p3CloneTarget.id` replacement so
  -- its live CR 610.3 return allocates BOTH a new `ObjectId` AND a new `EffectId` (`.copy ...`) at the end of `B_1`:
  let gCol0 :=
    ((((gColBase0.exileUntilSourceLeaves (some p1Cage.id) p0Victim (cause := some testCause)).phaseOut
      (gColBase0.object! p1Cage.id) (cause := some testCause)).createEffect
      (.control p2Altar.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := copyChoiceId, source := some p3CloneTarget.id, controller := some p0, affectedPlayer := p0,
        kind := .entersAsCopyCreatureUntilEot p0Victim.id p3CloneTarget.id }) (cause := some testCause))
  let exVictimId := (gCol0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!.id
  -- Update the replacement spec to target the actual exiled `exVictimId`:
  let copyExId : ReplacementId := {
    kind := .entersAsCopyCreatureUntilEot p3CloneTarget.id
    object := some exVictimId
  }
  let gColCkpt0 :=
    (gCol0.createEffect
      (.replacement {
        id := copyExId, source := some p3CloneTarget.id, controller := some p0, affectedPlayer := p0,
        kind := .entersAsCopyCreatureUntilEot exVictimId p3CloneTarget.id }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let (gCol1, colPropAb) := gColCkpt0.putStackAbility p2Altar p0 (abilityEffect := some (Effect.gainLife 1))
  let colProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := colPropAb.id, original := colPropAb
    originalSnapshot := gCol1.snapshot colPropAb, kind := .activatedAbility, sourceId := some p2Altar.id
  }
  let gCol2 := gCol1.changes #[.proposedSpell (some colProp), .pending (.chooseX p0)]
  -- Batch `B_1` (using `withBatchCore` so `queuedLinkedExile` is NOT flushed yet in the original stream,
  -- leaving phased-out `p1Cage` on raw `.battlefield` before `B_1` with unreturned `exVictimId` for `queueUnreturnedLinked`!):
  let depCause := some (EventCause.gameRule .playerLeftGame)
  let gColAfterB1 :=
    gCol2.withBatchCore depCause fun g =>
      let g := g.record (GameEvent.playerLeftGame g.turnNumber p1 (cause := depCause))
      g.objectLeavesTheGame (g.object! p1Cage.id) p1
  -- Clear `queuedLinkedExile` in the synthetic pre-reversal stream so `B_2` allocates the EXACT `ObjectId` and `EffectId`
  -- slots that `B_1`'s live CR 610.3 return will allocate during `replayKeptStreamCore`!
  let gColPreB2 := gColAfterB1.change .clearQueuedLinkedExile
  let gColAfterB2 :=
    gColPreB2.withBatch (some testCause) fun g =>
      -- (i) `ZoneEvent.created`: token gets raw `ObjectId` colliding with `exVictimId`'s live return!
      let (g, createdTok) := g.createOneToken p0 tokDef (cause := some testCause)
      -- (ii) Multi-hop `ZoneEvent.moved`: `p0HandCard` -> `.exile` -> `.graveyard p0`!
      let (g, hop1Id) := g.move p0HandCard .exile (cause := some testCause)
      let (g, _hop2Id) := g.move hop1Id (.graveyard p0) (cause := some testCause)
      -- (iii) `ContinuousEffectEvent.created`: allocates raw `EffectId` colliding with `.entersAsCopyCreatureUntilEot`'s effect!
      let g := g.createEffect (.layered (.objects #[createdTok.id]) (.ptModify 1 1) .untilEndOfTurn) (cause := some testCause)
      -- (iv) `TriggerQueueEvent.putOnStack`: stack a trigger whose `stackObj` collides!
      let g :=
        g.putQueuedTrigger p0 (g.object! createdTok.id)
          (TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 2)) .thisEnters (some 2) (some 2)
          (eventCause := some testCause)
      -- (v) `CastEvent.abilityActivated`: materialize and record a non-mana ability activation on `createdTok`!
      let (g, keptAbObj) := g.putStackAbility (g.object! createdTok.id) p0 (abilityEffect := some (Effect.gainLife 1))
      g.record (GameEvent.abilityActivated g.turnNumber keptAbObj.id (g.snapshot (g.object! createdTok.id)) p0
        (.nonMana none false false false none false) (cause := some testCause))
  -- Now `p2` concedes, aborting `colProp` and running `reverseToProposalCheckpoint?` across `[B_1, B_2]`!
  let gColReversed := mustApply gColAfterB2 p2 .concede
  let allObjIds := gColReversed.objects.map (·.id)
  let allEffIds := gColReversed.activeEffects.map Prod.fst
  let returnedClones :=
    gColReversed.permanentsOf p0 |>.filter (fun o => !o.printed.isToken && o.id != p0Victim.id)
  let keptTokens :=
    gColReversed.permanentsOf p0 |>.filter (fun o => o.printed.isToken && o.name == tokDef.name)
  let multiHopResolved := gColReversed.followMoved p0HandCard
  let collisionRemapOk :=
    gColReversed.proposedSpell.isNone &&
    allObjIds.toList.eraseDups.length == allObjIds.size &&
    allEffIds.toList.eraseDups.length == allEffIds.size &&
    returnedClones.size == 1 &&
    keptTokens.size == 1 &&
    -- The remapped `+1/+1` effect targets the remapped `keptTokens[0]!`, NOT `returnedClones[0]!`:
    gColReversed.power keptTokens[0]! == 3 &&
    -- Multi-hop `followMoved` resolves `p0HandCard` all the way to its final remapped `.graveyard p0` object:
    (gColReversed.findObject? multiHopResolved).any (·.zone == .graveyard p0) &&
    -- Both the remapped trigger and remapped activated ability remain on `.stack` with distinct valid objects:
    gColReversed.stack.size == 2 &&
    gColReversed.stack.all (fun se => (gColReversed.findObject? se.objectId).any (·.zone == .stack))

  -- 1c. `g.over == true` proposal-reversal finality (`suppressInteractiveReplay` suppresses interactive
  --     `Pending.chooseReplacement` pauses on CR 610.3 return when `reverseProposedSpell` runs at `g.over == true`):
  let g3p := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gOver0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent (addPermanent g3p cageDef p1 p1) altarDef p2 p2) bear p0 p0)
        leyADef p0 p0)
      leyBDef p0 p0
  let ovCage := (gOver0.permanentsOf p1)[0]!
  let ovAltar := (gOver0.permanentsOf p2)[0]!
  let ovBear := (gOver0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let ovLeyA := (gOver0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let ovLeyB := (gOver0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let ovRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some ovLeyA, counterKind := some .plusOnePlusOne }
  let ovRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some ovLeyB, counterKind := some .plusOnePlusOne }
  let gOverCkpt :=
    (((((gOver0.exileUntilSourceLeaves (some ovCage.id) ovBear (cause := some testCause)).createEffect
      (.control ovCage.id p0) (cause := some testCause)).createEffect
      (.control ovAltar.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := ovRidA, source := some ovLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := ovRidB, source := some ovLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let gOverAct0 := gOverCkpt.change (.beginProposalAction .costAction)
  let (gOverAct1, ovAb) := gOverAct0.putStackAbility ovAltar p0 (abilityEffect := some (Effect.gainLife 1))
  let ovSacCause := some (EventCause.costPayment .sacrifice p0 (some ovAb.id))
  let gOverSac :=
    gOverAct1.withBatch ovSacCause fun g =>
      g.sacrificeToGraveyard (g.object! ovCage.id) "sac" (cause := ovSacCause)
  let gOverRet := mustApply gOverSac p0 (.chooseReplacement ovRidA)
  let ovProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := ovAb.id, original := ovAb
    originalSnapshot := gOverRet.snapshot ovAb, kind := .activatedAbility, sourceId := some ovAltar.id
  }
  let gOverReady :=
    (gOverRet.changes #[.proposedSpell (some ovProp), .pending (.chooseX p0)]).change .endProposalAction
  let gOverAfterP1 := mustApply gOverReady p1 .concede
  let gOverEnded :=
    (gOverAfterP1.ceaseToExist ovAb.id (cause := some testCause) (reconcileControl := false)).record
      (GameEvent.gameEnded gOverAfterP1.turnNumber (.won p0) (cause := some testCause))
  let gOverReversed := gOverEnded.afterTriggerTargetsChosen
  let gameOverFinalityOk :=
    gOverReversed.over &&
    gOverReversed.pending == Pending.none &&
    gOverReversed.proposedSpell.isNone &&
    gOverReversed.proposalCheckpoint.isNone &&
    (gOverReversed.permanentsOf p0).any (·.name == bear.name)

  -- 1d. Mid-`.continueCheckpointReplay` 3rd-player departure CR 104.2a / CR 725.4 / CR 800.4c invariants:
  --     (i) 5-player game (`p0..p4`, `activePlayer := p3`): `p2` is monarch and controls `p0`-owned,
  --         `p3`-defaultControlled `midOrph` via `.whileSourceOnBattlefield midAltar.id`. `p1` concedes (`B1`),
  --         then `p2` concedes (`B2`, making `activePlayer` `p3` monarch and expiring `.control p2` onto `p3`),
  --         which aborts `p0`'s proposal on `midAltar` and pauses `.continueCheckpointReplay` on `B1`'s CR 610.3
  --         return (`mRidA`/`mRidB`) BEFORE `B2` replays. During that pause, **3rd player `p3` concedes**!
  --         When `p0` answers `mRidA`, `B2` replays: `becameMonarch p3` redirects to `p4` (`nextLiving p3`, CR 725.4)
  --         and `midOrph` (now lacking any living controller) is exiled via `orphanExiles` (CR 800.4c)!
  --     (ii) 4-player game (`p0..p3`): same mid-`.continueCheckpointReplay` pause after `p1` (`B1`) + `p2` (`B2`),
  --          then **3rd player `p3` concedes during the pause**; when `p0` answers `mRidA`, replaying `B2` leaves
  --          only `p0` in the game and ends the game immediately (`gMid4Done.over == true`, CR 104.2a)!
  let p4 : PlayerId := ⟨4⟩
  let g5Base := g4.change (.addPlayer { id := p4, name := "Chandra" })
  let g5 := g5Base.record (GameEvent.turnBegan g5Base.turnNumber p3 false)
  let gMid5Base :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent (addPermanent g5 cageDef p1 p1) altarDef p2 p2) bear p0 p3)
          leyADef p0 p0)
        leyBDef p0 p0)
      bear p0 p0
  let mid5Cage := (gMid5Base.permanentsOf p1)[0]!
  let mid5Orph := (gMid5Base.permanentsOf p3).find? (·.name == bear.name) |>.get!
  let mid5Altar := (gMid5Base.permanentsOf p2)[0]!
  let mid5Vic := (gMid5Base.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let mid5LeyA := (gMid5Base.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let mid5LeyB := (gMid5Base.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let m5RidA : ReplacementId := { kind := .entersWithExtraCounters, object := some mid5LeyA, counterKind := some .plusOnePlusOne }
  let m5RidB : ReplacementId := { kind := .entersWithExtraCounters, object := some mid5LeyB, counterKind := some .plusOnePlusOne }
  let gMid5Ckpt :=
    (((((((gMid5Base.record (GameEvent.becameMonarch gMid5Base.turnNumber p2 none (cause := some testCause))).exileUntilSourceLeaves
      (some mid5Cage.id) mid5Vic (cause := some testCause)).createEffect
      (.layered (.objects #[mid5Orph.id]) (.control p2) (.whileSourceOnBattlefield mid5Altar.id))
      (cause := some testCause)).createEffect
      (.control mid5Cage.id p0) (cause := some testCause)).createEffect
      (.control mid5Altar.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := m5RidA, source := some mid5LeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := m5RidB, source := some mid5LeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let gMid5Act1 := gMid5Ckpt.change (.beginProposalAction .costAction)
  let (gMid5Act2, mid5Ab) := gMid5Act1.putStackAbility mid5Altar p0 (abilityEffect := some (Effect.gainLife 1))
  let sacMid5Cause := some (EventCause.costPayment .sacrifice p0 (some mid5Ab.id))
  let gMid5Sac :=
    gMid5Act2.withBatch sacMid5Cause fun g =>
      g.sacrificeToGraveyard (g.object! mid5Cage.id) "sac" (cause := sacMid5Cause)
  let gMid5Ret := mustApply gMid5Sac p0 (.chooseReplacement m5RidA)
  let mid5Prop : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := mid5Ab.id, original := mid5Ab
    originalSnapshot := gMid5Ret.snapshot mid5Ab, kind := .activatedAbility, sourceId := some mid5Altar.id
  }
  let gMid5Ready :=
    (gMid5Ret.changes #[.proposedSpell (some mid5Prop), .pending (.chooseX p0)]).change .endProposalAction
  let gMid5P1 := mustApply gMid5Ready p1 .concede
  let gMid5Paused := mustApply gMid5P1 p2 .concede
  let gMid5AfterP3 := mustApply gMid5Paused p3 .concede
  let gMid5Done := mustApply gMid5AfterP3 p0 (.chooseReplacement m5RidA)

  let gMid4Base :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 cageDef p1 p1) altarDef p2 p2)
          leyADef p0 p0)
        leyBDef p0 p0)
      bear p0 p0
  let mid4Cage := (gMid4Base.permanentsOf p1)[0]!
  let mid4Altar := (gMid4Base.permanentsOf p2)[0]!
  let mid4Vic := (gMid4Base.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let mid4LeyA := (gMid4Base.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let mid4LeyB := (gMid4Base.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let m4RidA : ReplacementId := { kind := .entersWithExtraCounters, object := some mid4LeyA, counterKind := some .plusOnePlusOne }
  let m4RidB : ReplacementId := { kind := .entersWithExtraCounters, object := some mid4LeyB, counterKind := some .plusOnePlusOne }
  let gMid4Ckpt :=
    (((((gMid4Base.exileUntilSourceLeaves (some mid4Cage.id) mid4Vic (cause := some testCause)).createEffect
      (.control mid4Cage.id p0) (cause := some testCause)).createEffect
      (.control mid4Altar.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := m4RidA, source := some mid4LeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := m4RidB, source := some mid4LeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let gMid4Act1 := gMid4Ckpt.change (.beginProposalAction .costAction)
  let (gMid4Act2, mid4Ab) := gMid4Act1.putStackAbility mid4Altar p0 (abilityEffect := some (Effect.gainLife 1))
  let sacMid4Cause := some (EventCause.costPayment .sacrifice p0 (some mid4Ab.id))
  let gMid4Sac :=
    gMid4Act2.withBatch sacMid4Cause fun g =>
      g.sacrificeToGraveyard (g.object! mid4Cage.id) "sac" (cause := sacMid4Cause)
  let gMid4Ret := mustApply gMid4Sac p0 (.chooseReplacement m4RidA)
  let mid4Prop : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := mid4Ab.id, original := mid4Ab
    originalSnapshot := gMid4Ret.snapshot mid4Ab, kind := .activatedAbility, sourceId := some mid4Altar.id
  }
  let gMid4Ready :=
    (gMid4Ret.changes #[.proposedSpell (some mid4Prop), .pending (.chooseX p0)]).change .endProposalAction
  let gMid4P1 := mustApply gMid4Ready p1 .concede
  let gMid4Paused := mustApply gMid4P1 p2 .concede
  let gMid4AfterP3 := mustApply gMid4Paused p3 .concede
  let gMid4Done := mustApply gMid4AfterP3 p0 (.chooseReplacement m4RidA)

  mustHold38i1 "1ab.collisionRemapAndLinked" collisionRemapOk &&
  mustHold38i1 "1c.gameOverFinality" gameOverFinalityOk &&
  mustHold38i1 "1d.5pPaused" (gMid5Paused.sbaPaused && !gMid5Paused.over && !gMid5AfterP3.over) &&
  mustHold38i1 "1d.5pMonarch" (!(gMid5Done.player p3).isMonarch && (gMid5Done.player p4).isMonarch) &&
  mustHold38i1 "1d.5pOrphanExiled" (gMid5Done.followMovedToZone? mid5Orph.id (· == .exile)).isSome &&
  mustHold38i1 "1d.4pOver"
    (gMid4Paused.sbaPaused && !gMid4AfterP3.over && gMid4Done.over &&
     gMid4Done.result == some (.won p0) && gMid4Done.pending == Pending.none) &&
  mustHold38i1 "1.replay"
    (replayOk38i1 #[gColReversed, gOverReversed, gMid5Paused, gMid5AfterP3, gMid5Done, gMid4Paused, gMid4AfterP3, gMid4Done])

end Phase38Item1EventAlignment

/-! ### Phase 38 Item 2: `playersDepartedSinceCheckpoint` + outer `ckptPending`/`ckptOrigCont?` ordering, `Pending.chooseLegend` CR 704.5j characteristic re-validation, and `finishAndGrantPriority` / `endsWithPriorityGrant` priority-recipient fixes -/
section Phase38Item2EventAlignment

private def mustHold38i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase38Item2EventAlignment failed: {label}"

private def replayOk38i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def lifeGainsSince38i2 (g : Game) (startIdx : Nat) (p : PlayerId) : Array Nat :=
  (g.events.extract startIdx g.events.size).filterMap fun e =>
    match e.change with
    | .rules (.life (.gained q amt)) => if q == p then some amt else none
    | _ => none

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let auraDef : CardDef := { name := "P38i2 Aura", types := #[.enchantment] }
  let morphDef : CardDef := {
    creature "P38i2 Morph" ManaCost.empty #["Human"] 2 2 with keywords := #[.morph CostSpec.empty]
  }

  -- 2a. `playersDepartedSinceCheckpoint` + outer `ckptPending` BEFORE `ckptOrigCont?` ordering across:
  --     (i) `Leaving.rewindAbortedProposalOnLeave`,
  --     (ii) `Decisions.reverseOrResumePopped`, and
  --     (iii) standalone `Casting.reverseProposedSpellCore?`:
  let gOrd00 :=
    insertObject
      (addPermanent (addPermanent (addPermanent g4 bear p3 p3) auraDef p2 p2) morphDef p0 p0)
      bear p0 .exile
  let ordP3Bear := (gOrd00.permanentsOf p3)[0]!
  let ordP2Aura := (gOrd00.permanentsOf p2)[0]!
  let ordMorphId := (gOrd00.permanentsOf p0).find? (·.name == morphDef.name) |>.get!.id
  let gOrd0 := setFaceDown gOrd00 ordMorphId true
  let ordMorph := gOrd0.object! ordMorphId
  let ordExCard := (gOrd0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!
  let ordOuterPrompt : Pending := .mayCastExiledElseDamage p0 ordExCard.id 0 none
  let ordStartIdx := gOrd0.events.size
  -- `ckpt` has `pending = ordOuterPrompt` AND `ckptOrigCont? = .seq (.restorePending (.scry p1 1) false) (.gainLife p0 7 ...)`:
  let origTail : PendingReplacement :=
    .seq (.restorePending (.scry p1 1) false) (.gainLife p0 7 (some testCause))
  let gOrdCkpt :=
    (gOrd0.createEffect (.layered (.objects #[ordP3Bear.id]) (.control p0) (.whileSourceOnBattlefield ordP2Aura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pending ordOuterPrompt,
      .pendingReplacement (some origTail),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement origTail,
      .pendingReplacement none ]

  -- Path (i): `Leaving.rewindAbortedProposalOnLeave` (`p1` concedes first, then `p2` concedes aborting `ordAb`):
  let (gLeave1, ordAb) := gOrdCkpt.putStackAbility ordP3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let leaveProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := ordAb.id, original := ordAb
    originalSnapshot := gLeave1.snapshot ordAb, kind := .activatedAbility
    sourceId := some ordP3Bear.id, resolutionCast := true
  }
  let gLeaveReady := gLeave1.changes #[.proposedSpell (some leaveProp), .pending (.chooseX p0)]
  let gLeaveAfterP1 := mustApply gLeaveReady p1 .concede
  let gLeaveRewound := mustApply gLeaveAfterP1 p2 .concede
  let leaveBeforeDeclineOk :=
    mustHold38i2 s!"2a.i.prePend:{reprStr gLeaveRewound.pending}" (gLeaveRewound.pending == ordOuterPrompt) &&
    mustHold38i2 s!"2a.i.preLife:{reprStr (lifeGainsSince38i2 gLeaveRewound ordStartIdx p0)}"
      (lifeGainsSince38i2 gLeaveRewound ordStartIdx p0 == #[])
  let gLeaveDrained := (mustApply gLeaveRewound p0 .decline).drainPendingContinuations

  -- Path (ii): `Decisions.reverseOrResumePopped` (`p1` already departed since `ckpt`, while `.restorePending` only passes `departed := #[p3]`!):
  let popProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := ordMorph.id, original := ordMorph
    originalSnapshot := gOrdCkpt.snapshot ordMorph, kind := .turnFaceUp
    sourceId := some ordMorph.id, resolutionCast := true
  }
  let gPopSteal :=
    (((gOrdCkpt.record (GameEvent.playerLeftGame gOrdCkpt.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).record
      (GameEvent.playerLeftGame gOrdCkpt.turnNumber p3 (cause := some (.gameRule .playerLeftGame)))).createEffect
      (.control ordMorph.id p2) (cause := some testCause)).changes #[
      .proposedSpell (some popProp),
      .pushOuterPendingReplacement (.gainLife p0 4 (some testCause)) ]
  let gPopRewound :=
    (gPopSteal.resumePendingReplacement
      (.restorePending (.fraChoice p0 (.costPicks ordMorph.id #[.tapUntappedCreature] false)) true none #[p3] none)).drainPendingContinuations
  let popBeforeDeclineOk :=
    mustHold38i2 s!"2a.ii.prePend:{reprStr gPopRewound.pending}" (gPopRewound.pending == ordOuterPrompt) &&
    mustHold38i2 s!"2a.ii.preLife:{reprStr (lifeGainsSince38i2 gPopRewound ordStartIdx p0)}"
      (lifeGainsSince38i2 gPopRewound ordStartIdx p0 == #[4])
  let gPopDrained := (mustApply gPopRewound p0 .decline).drainPendingContinuations

  -- Path (iii): Standalone `Casting.reverseProposedSpellCore?` (`p1` departed mid-proposal, then `p0` reverses standalone via `pay` with `{1}` unpaid!):
  let standProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := ordMorph.id, original := ordMorph
    originalSnapshot := gOrdCkpt.snapshot ordMorph, kind := .turnFaceUp
    sourceId := some ordMorph.id, resolutionCast := true
  }
  let gStandAfterP1 :=
    mustApply (gOrdCkpt.changes #[.proposedSpell (some standProp), .pending (.activateManaAbilities p0)]) p1 .concede
  let gStandRewound := mustApply gStandAfterP1 p0 .pay
  let standBeforeDeclineOk :=
    mustHold38i2 s!"2a.iii.prePend:{reprStr gStandRewound.pending}" (gStandRewound.pending == ordOuterPrompt) &&
    mustHold38i2 s!"2a.iii.preLife:{reprStr (lifeGainsSince38i2 gStandRewound ordStartIdx p0)}"
      (lifeGainsSince38i2 gStandRewound ordStartIdx p0 == #[])
  let gStandDrained := (mustApply gStandRewound p0 .decline).drainPendingContinuations

  -- Also verify `scrubDepartedFromContinuations allDeparted` clears departed `p1`'s `afterRandom := .draw p1 1`:
  let gArCkpt :=
    gOrd0.changes #[
      .pushContinuationFrame { afterRandom := .draw p1 1 },
      .pending (.resolveRandom (.shuffleLibrary p1)),
      .saveProposalCheckpoint ]
  let gArPostLeave :=
    (gArCkpt.record (GameEvent.playerLeftGame gArCkpt.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).changes #[
      .proposedSpell (some standProp),
      .pending (.activateManaAbilities p0) ]
  let gArScrubbed := mustApply gArPostLeave p0 .pay

  let ckptDepartedAndOrderingOk :=
    leaveBeforeDeclineOk &&
    mustHold38i2 s!"2a.i.postLife:{reprStr (lifeGainsSince38i2 gLeaveDrained ordStartIdx p0)}"
      (lifeGainsSince38i2 gLeaveDrained ordStartIdx p0 == #[7]) &&
    popBeforeDeclineOk &&
    mustHold38i2 s!"2a.ii.postLife:{reprStr (lifeGainsSince38i2 gPopDrained ordStartIdx p0)}"
      (lifeGainsSince38i2 gPopDrained ordStartIdx p0 == #[4, 7]) &&
    standBeforeDeclineOk &&
    mustHold38i2 s!"2a.iii.postLife:{reprStr (lifeGainsSince38i2 gStandDrained ordStartIdx p0)}"
      (lifeGainsSince38i2 gStandDrained ordStartIdx p0 == #[7]) &&
    mustHold38i2 s!"2a.ar:{reprStr gArScrubbed.afterRandom}" (gArScrubbed.afterRandom == .none)


  -- 2b. `Pending.chooseLegend` CR 704.5j characteristic re-validation across `Leaving`,
  --     `Decisions.resumePendingReplacement` (`.restorePending`), `StateBasedActions.checkSBACounted`, and `Decisions.keepLegend`:
  let gLeg0 := addPermanent (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0) bear p0 p0
  let bIds := (gLeg0.permanentsOf p0).map (·.id)
  let gLegAll :=
    gLeg0.createEffect (.layered (.objects bIds) (.types .add #[] #[] #[.legendary]) .indefinite)
      (cause := some testCause)
  let legEffId := gLegAll.activeEffects.back!.1
  -- Rename `bIds[2]!` so only `bIds[0]!` and `bIds[1]!` match `bear.name`:
  let renamedDef : CardDef := { bear with name := "Renamed Cub", supertypes := #[.legendary] }
  let gLegTwoMatch :=
    (gLegAll.createEffect (.copy bIds[2]! renamedDef) (cause := some testCause)).change
      (.pending (.chooseLegend p0 bear.name bIds))
  -- Pre-`sbaPaused` `checkSBACounted` narrows `bIds` (size 3 -> size 2) and returns `(g, false)`:
  let (gLegNarrowed, sbaDidNarrow) := gLegTwoMatch.checkSBACounted
  -- `keepLegend` rejects keeping non-matching `bIds[2]!`, and keeping `bIds[0]!` buries ONLY `bIds[1]!` (leaving `bIds[2]!` on `.battlefield`!):
  let keepNonMatchRejected :=
    match gLegTwoMatch.keepLegend p0 bIds[2]! with
    | .error _ => true
    | .ok _ => false
  let gLegKept := mustApply gLegTwoMatch p0 (.keepLegend bIds[0]!)
  -- Now expire `legEffId` AFTER `checkSBA` opened `.chooseLegend` (even with `currentBatch.isSome`!):
  let gSbaLegendOpen := (gLeg0.createEffect
    (.layered (.objects #[bIds[0]!, bIds[1]!]) (.types .add #[] #[] #[.legendary]) .indefinite)
    (cause := some testCause)).checkSBA
  let openLegEffId := gSbaLegendOpen.activeEffects.back!.1
  let gSbaLegendExpired := gSbaLegendOpen.expireEffectById openLegEffId (cause := some testCause)
  -- `keepLegend` sees post-prompt effect expiry -> `liveIds.size == 0 < 2` -> dismisses prompt without burying either bear!
  let gSbaLegendDismissed := mustApply gSbaLegendExpired p0 (.keepLegend bIds[0]!)
  -- And on unbatched `gUnbatchedStale`, `batchPausePromptValid`, `redirectPendingAfterLeave`, `.restorePending`, and `checkSBACounted` all clear it:
  let gUnbatchedStale :=
    (gLegAll.expireEffectById legEffId (cause := some testCause)).change
      (.pending (.chooseLegend p0 bear.name #[bIds[0]!, bIds[1]!]))
  let (_, redirOut) := gUnbatchedStale.redirectPendingAfterLeave p3 (pending := gUnbatchedStale.pending)
  let gRestoreStale :=
    (gUnbatchedStale.change (.pending .none)).resumePendingReplacement
      (.restorePending (.chooseLegend p0 bear.name #[bIds[0]!, bIds[1]!]) false)
  let (gSbaClearedStale, _) := gUnbatchedStale.checkSBACounted
  let chooseLegendRevalidationOk :=
    !sbaDidNarrow &&
    gLegNarrowed.pending == .chooseLegend p0 bear.name #[bIds[0]!, bIds[1]!] &&
    keepNonMatchRejected &&
    (gLegKept.permanentsOf p0).any (·.id == bIds[0]!) &&
    !(gLegKept.permanentsOf p0).any (·.id == bIds[1]!) &&
    (gLegKept.permanentsOf p0).any (·.id == bIds[2]!) &&
    (gSbaLegendDismissed.permanentsOf p0).size == 3 &&
    gSbaLegendDismissed.pending == Pending.none &&
    !gUnbatchedStale.batchPausePromptValid gUnbatchedStale.pending &&
    redirOut == Pending.none &&
    gRestoreStale.pending == Pending.none &&
    gSbaClearedStale.pending == Pending.none

  -- 2c. `finishAndGrantPriority` default `pendingPriority` fallback + `endsWithPriorityGrant` activation / face-up arms:
  let gDefPrio := (g4.change (.pendingPriority (some p2))).finishAndGrantPriority
  let endsWithPrioArmsOk :=
    gDefPrio.priority == p2 &&
    (PendingReplacement.completeActivation false false).endsWithPriorityGrant &&
    !(PendingReplacement.completeActivation true false).endsWithPriorityGrant &&
    (PendingReplacement.finishBecomeActivated p2 "Src" none none none none none false false).endsWithPriorityGrant &&
    !(PendingReplacement.finishBecomeActivated p2 "Src" none none none none none true false).endsWithPriorityGrant &&
    (PendingReplacement.finishPostLoyaltyActivated p2 "Src" none none none none none false false).endsWithPriorityGrant &&
    (PendingReplacement.finishTurnFaceUp p2 ordMorph.id false).endsWithPriorityGrant &&
    !(PendingReplacement.finishTurnFaceUp p2 ordMorph.id true).endsWithPriorityGrant

  mustHold38i2 "2a.ckptDepartedAndOrdering" ckptDepartedAndOrderingOk &&
  mustHold38i2 "2b.chooseLegendRevalidation" chooseLegendRevalidationOk &&
  mustHold38i2 "2c.endsWithPrioArms" endsWithPrioArmsOk &&
  mustHold38i2 "2.replay"
    (replayOk38i2 #[gLeaveRewound, gLeaveDrained, gPopRewound, gPopDrained,
      gStandRewound, gStandDrained, gArScrubbed, gLegNarrowed, gLegKept,
      gSbaLegendOpen, gSbaLegendDismissed, gRestoreStale, gSbaClearedStale, gDefPrio])

end Phase38Item2EventAlignment

/-! ### Phase 38 Item 3: Pre-mutation `pre` control snapshots, phased-out Layer 1/2 scopes + CR 502.1 `phaseInControlled` & `phaseInControlledLoop`, `flushQueuedLinkedExileFwd`, and pause-safe `afterTriggerTargetsChosen` / `finishOneResolution` -/
section Phase38Item3EventAlignment

private def mustHold38i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase38Item3EventAlignment failed: {label}"

private def replayOk38i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let hostDef : CardDef := { name := "P38i3 Host", types := #[.artifact] }
  let leyADef : CardDef := { name := "P38i3 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P38i3 LeyB", types := #[.enchantment] }
  let flyerDef : CardDef := {
    creature "P38i3 Flyer" ManaCost.empty #["Bird"] 2 2 with keywords := #[Keyword.flying]
  }

  -- 3a. Pre-mutation `pre` snapshots on:
  --     (i) `recordRemoveCounters` (`1 -> 0` `.whileSourceHasCounter` exiles CR 800.4c permanent & removes from combat),
  --     (ii) `recordPutCounters` (`0 -> 1` `.whileSourceHasCounter` steals attacking creature & removes from combat),
  --     (iii) `addPlusOnePlusOneTo` (`0 -> 1` `.whileSourceHasCounter` steals attacking creature & removes from combat),
  --     (iv) `Movement.move` (moving card out of `.graveyard` ends `.whileInZone` control -> CR 800.4c exile), and
  --     (v) `objectLeavesTheGame` (`p2` conceding removes card in `.graveyard p2`, ending `.whileInZone` -> CR 800.4c exile):
  let gPre0 :=
    insertObject
      (insertObject
        (addPermanent (addPermanent (addPermanent (addPermanent g4 bear p3 p1) bear p2 p2) hostDef p0 p0) hostDef p0 p0)
        bear p0 (.graveyard p0))
      bear p2 (.graveyard p2)
  let p1Orph := (gPre0.permanentsOf p1)[0]!
  let p2Atk := (gPre0.permanentsOf p2)[0]!
  let p0Hosts := (gPre0.permanentsOf p0).filter (·.name == hostDef.name)
  let hostA := p0Hosts[0]!
  let hostB := p0Hosts[1]!
  let p0GyId := (gPre0.player p0).graveyard.back!
  let p2GyId := (gPre0.player p2).graveyard.back!

  -- (i) `recordRemoveCounters`:
  let gRem0 :=
    (((gPre0.recordPutCounters hostA.id .plusOnePlusOne 1 (some p0) (cause := some testCause)).createEffect
      (.layered (.objects #[p1Orph.id]) (.control p0) (.whileSourceHasCounter hostA.id .plusOnePlusOne))
      (cause := some testCause)).concede p1).record
      (GameEvent.becameAttacking gPre0.turnNumber (gPre0.snapshot p1Orph) (.player p2) (cause := testCause))
  let gRemDone := gRem0.recordRemoveCounters hostA.id .plusOnePlusOne 1 (byPlayer := some p0) (cause := some testCause)

  -- (ii) `recordPutCounters` (`0 -> 1`):
  let gPut0 :=
    (gPre0.createEffect
      (.layered (.objects #[p2Atk.id]) (.control p0) (.whileSourceHasCounter hostA.id .charge))
      (cause := some testCause)).record
      (GameEvent.becameAttacking gPre0.turnNumber (gPre0.snapshot p2Atk) (.player p0) (cause := testCause))
  let gPutDone := gPut0.recordPutCounters hostA.id .charge 1 (some p0) (cause := some testCause)

  -- (iii) `addPlusOnePlusOneTo` (`0 -> 1`):
  let gAddP10 :=
    (gPre0.createEffect
      (.layered (.objects #[p2Atk.id]) (.control p0) (.whileSourceHasCounter hostB.id .plusOnePlusOne))
      (cause := some testCause)).record
      (GameEvent.becameAttacking gPre0.turnNumber (gPre0.snapshot p2Atk) (.player p0) (cause := testCause))
  let gAddP1Done := gAddP10.addPlusOnePlusOneTo (gAddP10.object! hostB.id) 1 (cause := some testCause)

  -- (iv) `Movement.move`:
  let gMv0 :=
    (gPre0.createEffect
      (.layered (.objects #[p1Orph.id]) (.control p0) (.whileInZone p0GyId (.graveyard p0)))
      (cause := some testCause)).concede p1
  let (gMvDone, _) := gMv0.move p0GyId .exile (cause := some testCause)

  -- (v) `objectLeavesTheGame`:
  let gOlg0 :=
    (gPre0.createEffect
      (.layered (.objects #[p1Orph.id]) (.control p0) (.whileInZone p2GyId (.graveyard p2)))
      (cause := some testCause)).concede p1
  let gOlgDone := gOlg0.concede p2

  let preSnapshotsOk :=
    (gRemDone.followMovedToZone? p1Orph.id (· == .exile)).isSome &&
    gRemDone.events.any (fun e =>
      match e.change with | .rules (.combat (.removedFromCombat eo)) => eo.id == some p1Orph.id | _ => false) &&
    gPutDone.controllerOf (gPutDone.object! p2Atk.id) == some p0 &&
    !(gPutDone.object! p2Atk.id).status.attacking &&
    gAddP1Done.controllerOf (gAddP1Done.object! p2Atk.id) == some p0 &&
    !(gAddP1Done.object! p2Atk.id).status.attacking &&
    (gMvDone.followMovedToZone? p1Orph.id (· == .exile)).isSome &&
    (gOlgDone.followMovedToZone? p1Orph.id (· == .exile)).isSome

  -- 3b. Phased-out Layer 1/2 scope preservation (`scopeMatchesL1`/`scopeMatchesL2` keep `.creaturesWithout #[Keyword.flying]`
  --     `.control p0` active on phased-out `p1Orph` so it isn't exiled!), CR 502.1 `phaseInControlled` phase-out controller lookup,
  --     and pause-safe `phaseInControlledLoop`:
  let gPhScope0 :=
    (gPre0.createEffect (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) .indefinite)
      (cause := some testCause)).concede p1
  let gPhScopedOut := gPhScope0.phaseOut (gPhScope0.object! p1Orph.id) (cause := some testCause)
  -- CR 502.1: `p2Atk` is stolen by `p0` `.untilEndOfTurn`, phases out under `p0`'s control, then `.untilEndOfTurn` expires:
  let gCr502Steal :=
    gPre0.createEffect (.layered (.objects #[p2Atk.id]) (.control p0) .untilEndOfTurn) (cause := some testCause)
  let cr502EffId := gCr502Steal.activeEffects.back!.1
  let gCr5020 :=
    (gCr502Steal.phaseOut (gCr502Steal.object! p2Atk.id) (cause := some testCause)).expireEffectById
      cr502EffId (cause := some testCause)
  let gAfterP2PhaseIn := gCr5020.phaseInControlled p2
  let gAfterP0PhaseIn := gAfterP2PhaseIn.phaseInControlled p0
  -- Pause-safe `phaseInControlledLoop`: `ph1` and `ph2` both phase in for `p0`; `ph1` phasing in activates
  -- `.whileSourceOnBattlefield ph1.id` granting flying to `p1Jail`, ending `.creaturesWithout #[Keyword.flying]`
  -- `.control p0` on `p1Jail` (exiled under CR 800.4c), whose `linkedExile` returns `p0`'s bear into `leyA`/`leyB`
  -- (`Pending.chooseReplacement`), deferring `ph2`'s phase-in via `.phaseInControlledLoop` until chosen!
  let gLoopBase :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent (addPermanent g4 bear p3 p1) bear p0 p0) hostDef p0 p0)
          hostDef p0 p0)
        leyADef p0 p0)
      leyBDef p0 p0
  let lpJail := (gLoopBase.permanentsOf p1)[0]!
  let lpVic := (gLoopBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let lpPhs := (gLoopBase.permanentsOf p0).filter (·.name == hostDef.name)
  let ph1 := lpPhs[0]!
  let ph2 := lpPhs[1]!
  let lpLeyA := (gLoopBase.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let lpLeyB := (gLoopBase.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let lpRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some lpLeyA, counterKind := some .plusOnePlusOne }
  let lpRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some lpLeyB, counterKind := some .plusOnePlusOne }
  let gLoop0 :=
    (((((((gLoopBase.exileUntilSourceLeaves (some lpJail.id) lpVic (cause := some testCause)).createEffect
      (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) .indefinite)
      (cause := some testCause)).concede p1).phaseOut ph1 (cause := some testCause)).phaseOut
      ph2 (cause := some testCause)).createEffect
      (.layered (.objects #[lpJail.id]) (.copy flyerDef) (.whileSourceOnBattlefield ph1.id))
      (cause := some testCause)).createEffect
      (.replacement {
        id := lpRidA, source := some lpLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := lpRidB, source := some lpLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)
  let gLoopPaused := gLoop0.phaseInControlled p0
  let gLoopDone := (mustApply gLoopPaused p0 (.chooseReplacement lpRidA)).drainPendingContinuations
  -- Also verify `PendingReplacement.phaseInControlledLoop` resuming inside the enclosing `BatchId` across a mid-batch pause:
  let pinPauseBid : BatchId := ⟨981⟩
  let gPinLoop0 := ((addPermanent (addPermanent g4 hostDef p0 p0) hostDef p0 p0))
  let pinA := (gPinLoop0.permanentsOf p0)[0]!
  let pinB := (gPinLoop0.permanentsOf p0)[1]!
  let gPinOut := (gPinLoop0.phaseOut pinA (cause := some testCause)).phaseOut pinB (cause := some testCause)
  let pinStartIdx := gPinOut.events.size
  let gPinLoop1 :=
    (gPinOut.changes #[
      .pauseBatch pinPauseBid (some (.turnBased .phaseInOut)) gPinOut.objects gPinOut.players gPinOut.activeEffects
        (.chooseReplacement p0 #[]) gPinOut.stack ]).phaseIn (gPinOut.object! pinA.id) (cause := some (.turnBased .phaseInOut))
  let gPinLoopResumed :=
    gPinLoop1.resumePendingReplacement
      (.seq (.phaseInControlledLoop #[pinB.id] (some (.turnBased .phaseInOut))) (.closeBatch pinPauseBid pinStartIdx))
  let pinBatches :=
    (gPinLoopResumed.events.extract pinStartIdx gPinLoopResumed.events.size).filterMap fun e =>
      match e.change with
      | .rules (.permanent (.phasedIn _ _)) => some e.batch
      | _ => none
  let phasingAndLoopOk :=
    (gPhScopedOut.object! p1Orph.id).status.phasedOut &&
    gPhScopedOut.controllerOf (gPhScopedOut.object! p1Orph.id) == some p0 &&
    (gCr5020.controllerOf (gCr5020.object! p2Atk.id)) == some p2 &&
    (gAfterP2PhaseIn.object! p2Atk.id).status.phasedOut &&
    !(gAfterP0PhaseIn.object! p2Atk.id).status.phasedOut &&
    gLoopPaused.sbaPaused &&
    !(gLoopPaused.object! ph1.id).status.phasedOut &&
    !(gLoopPaused.object! ph2.id).status.phasedOut &&
    (gLoopDone.permanentsOf p0).any (fun o => o.name == bear.name && o.status.plusOnePlusOne == 3) &&
    !(gPinLoopResumed.object! pinA.id).status.phasedOut &&
    !(gPinLoopResumed.object! pinB.id).status.phasedOut &&
    pinBatches == #[some pinPauseBid, some pinPauseBid] &&
    gPinLoopResumed.currentBatch.isNone

  -- 3c. `flushQueuedLinkedExileFwd` after `Phasing.phaseOut`, `Core.createEffects`, and `Leaving.removeAllCountersFrom`:
  let mkLinkedOrphan : Game × ObjectId × ObjectId :=
    let g0 := addPermanent (addPermanent (addPermanent g4 bear p3 p1) bear p0 p0) hostDef p0 p0
    let jail := (g0.permanentsOf p1)[0]!
    let vic := (g0.permanentsOf p0).find? (·.name == bear.name) |>.get!
    let anchor := (g0.permanentsOf p0).find? (·.name == hostDef.name) |>.get!
    let g1 := g0.exileUntilSourceLeaves (some jail.id) vic (cause := some testCause)
    (g1, jail.id, anchor.id)
  let (gFlBase, flJailId, flAnchorId) := mkLinkedOrphan
  -- (i) `Phasing.phaseOut`:
  let gFlPhOut :=
    ((gFlBase.createEffect (.layered (.objects #[flJailId]) (.control p0) (.whileSourceOnBattlefield flAnchorId))
      (cause := some testCause)).concede p1).phaseOut (gFlBase.object! flAnchorId) (cause := some testCause)
  -- (ii) `Core.createEffects` (`effs.size > 1`):
  let gFlCe0 :=
    (gFlBase.createEffect (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) .indefinite)
      (cause := some testCause)).concede p1
  let gFlCeDone :=
    gFlCe0.createEffects #[
      .copy flJailId flyerDef (untilEot := true),
      .layered (.objects #[flAnchorId]) (.types .add #[.creature] #[] #[]) .untilEndOfTurn
    ] (cause := some testCause)
  -- (iii) `Leaving.removeAllCountersFrom`:
  let gFlRc0 :=
    (((gFlBase.recordPutCounters flAnchorId .plusOnePlusOne 2 (some p0) (cause := some testCause)).createEffect
      (.layered (.objects #[flJailId]) (.control p0) (.whileSourceHasCounter flAnchorId .plusOnePlusOne))
      (cause := some testCause)).concede p1)
  let gFlRcDone := gFlRc0.removeAllCountersFrom flAnchorId (cause := some testCause)
  let flushLinkedExileOk :=
    gFlPhOut.queuedLinkedExile.isEmpty &&
    (gFlPhOut.permanentsOf p0).any (·.name == bear.name) &&
    gFlCeDone.queuedLinkedExile.isEmpty &&
    (gFlCeDone.permanentsOf p0).any (·.name == bear.name) &&
    gFlRcDone.queuedLinkedExile.isEmpty &&
    (gFlRcDone.permanentsOf p0).any (·.name == bear.name)

  -- 3d. Pause-safe `Entering.finishOneResolution` (`.ability`), `PostStep.afterTriggerTargetsChosen`,
  --     and game-over `completeActiveResolutions` quiet `ceaseToExist`:
  let gFin0 :=
    (gFlBase.createEffect
      (.replacement {
        id := { kind := .entersWithExtraCounters, object := some flAnchorId, counterKind := some .plusOnePlusOne }
        source := some flAnchorId, controller := some p0, affectedPlayer := p0
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := { kind := .addCountersPut, object := some flAnchorId, counterKind := some .plusOnePlusOne }
        source := some flAnchorId, controller := some p0, affectedPlayer := p0
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)
  let (gFin1, finAbObj) := gFin0.putStackAbility (gFin0.object! flAnchorId) p0 (abilityEffect := some (Effect.gainLife 1))
  let gFin2 :=
    (gFin1.createEffect (.layered (.objects #[flJailId]) (.control p0) (.whileInZone finAbObj.id .stack))
      (cause := some testCause)).concede p1
  let finSnap := gFin2.snapshot (gFin2.object! finAbObj.id)
  let gFinPaused := gFin2.finishOneResolution (.ability finAbObj.id finSnap p0 (some flAnchorId) none)
  let notResolvedYet :=
    !gFinPaused.events.any (fun e =>
      match e.change with | .rules (.stackObject (.resolved eo ..)) => eo.id == some finAbObj.id | _ => false)
  let finFirstChoice :=
    match gFinPaused.pending with
    | .chooseReplacement _ chs => chs[0]!
    | _ => panic! "expected chooseReplacement"
  let gFinCompleted := (mustApply gFinPaused p0 (.chooseReplacement finFirstChoice)).drainPendingContinuations
  -- Pause-safe `afterTriggerTargetsChosen` (`PostStep.afterTriggerTargetsChosen`):
  let gAttcPaused :=
    (gFinPaused.putQueuedTrigger p0 (gFinPaused.object! flAnchorId)
      (TriggeredAbility.mkTrigger .thisEnters (Effect.dealDamage 1)) .thisEnters (some 1) (some 1)
      (eventCause := some testCause)).afterTriggerTargetsChosen
  let gAttcResumed := (mustApply gAttcPaused p0 (.chooseReplacement finFirstChoice)).drainPendingContinuations
  -- Game-over `completeActiveResolutions` quiet `ceaseToExist` (`reconcileControl := false` when `g.over`):
  let gGoRes0 :=
    (gFin2.changes #[
      .pushContinuationFrame {
        resolvingAbility := some finAbObj.id
        resolutionFinish := some (.ability finAbObj.id finSnap p0 (some flAnchorId) none) }
    ]).record (GameEvent.gameEnded gFin2.turnNumber (.won p0) (cause := some testCause))
  let gGoResDone := gGoRes0.completeActiveResolutions
  let pauseResolutionAndGameOverOk :=
    gFinPaused.sbaPaused &&
    notResolvedYet &&
    gFinCompleted.events.any (fun e =>
      match e.change with | .rules (.stackObject (.resolved eo ..)) => eo.id == some finAbObj.id | _ => false) &&
    gAttcPaused.sbaPaused &&
    gAttcResumed.pending == .chooseTargets p0 &&
    gGoResDone.over &&
    gGoResDone.pending == Pending.none &&
    gGoResDone.continuations.isEmpty &&
    (gGoResDone.findObject? finAbObj.id).isNone

  mustHold38i3 "3a.preSnapshots" preSnapshotsOk &&
  mustHold38i3 "3b.phasingAndLoop" phasingAndLoopOk &&
  mustHold38i3 "3c.flushLinkedExile" flushLinkedExileOk &&
  mustHold38i3 "3d.pauseResolutionAndGameOver" pauseResolutionAndGameOverOk &&
  mustHold38i3 "3.replay"
    (replayOk38i3 #[gRemDone, gPutDone, gAddP1Done, gMvDone, gOlgDone,
      gPhScopedOut, gAfterP2PhaseIn, gAfterP0PhaseIn, gLoopPaused, gLoopDone, gPinLoopResumed,
      gFlPhOut, gFlCeDone, gFlRcDone, gFinPaused, gFinCompleted,
      gAttcPaused, gAttcResumed, gGoResDone])

end Phase38Item3EventAlignment

/-! ### Phase 38 Item 4: Pre-sacrifice `payLoyaltyCost` + `ProposedSpell.loyaltyPaid` + `!exileSource` guards, live `proposedSpell` across final cost replacement pauses, departed `ManaAbilities` continuations, and `.crew`/`.zemoBoastExile`/`payTeamworkCreatures`/`.chooseMode` reversals -/
section Phase38Item4EventAlignment

private def mustHold38i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase38Item4EventAlignment failed: {label}"

private def replayOk38i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let leyADef : CardDef := { name := "P38i4 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P38i4 LeyB", types := #[.enchantment] }
  let baubleDef : CardDef := { name := "P38i4 Bauble", types := #[.artifact] }

  -- 4a. Upstream `payLoyaltyCost` pre-sacrifice loyalty payment (including `.stunAndSacrifice` replacement pause),
  --     `ProposedSpell.loyaltyPaid` `[0]`/`[-0]` tracking + `[+X]` payability, and `!exileSource` graveyard/hand guards:
  let pwPlusStunSacAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty (.plus 2), .putCounters (.const 1) .stun .self, .sacrifice (.exact 1) .self]
    effect := Effect.gainLife 4
  }
  let pwZeroMultiPickAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty .zero, .sacrifice (.exact 1) (.filter (.hasType .artifact)), .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .hasType .artifact]))]
    effect := Effect.gainLife 2
  }
  let pwMinusZeroSacAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty (.minus 0), .sacrifice (.exact 1) .self]
    effect := Effect.gainLife 1
  }
  let pwPlusXAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty .plusX, .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))]
    effect := Effect.gainLife 1
  }
  let pwDef : CardDef := {
    name := "P38i4 Walker", types := #[.artifact, .planeswalker], loyalty := some 3
    activatedAbilities := #[pwPlusStunSacAb, pwZeroMultiPickAb, pwMinusZeroSacAb, pwPlusXAb]
  }
  let gPw0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent (addPermanent g3 pwDef p0 p0) baubleDef p0 p0) baubleDef p0 p0) leyADef p0 p0)
      leyBDef p0 p0
  let pwId := (gPw0.permanentsOf p0).find? (·.name == pwDef.name) |>.get!.id
  let pwBaubleIds := (gPw0.permanentsOf p0).filter (·.name == baubleDef.name) |>.map (·.id)
  let pwLeyA := (gPw0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let pwLeyB := (gPw0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let cAddId : ReplacementId := { kind := .addCountersPut, object := some pwLeyA }
  let cMulId : ReplacementId := { kind := .multiplyCountersPut, object := some pwLeyB }
  let gPwRepl :=
    ((gPw0.recordPutCounters pwId .loyalty 3 (some p0) (cause := some testCause)).createEffect
      (.replacement {
        id := cAddId, source := some pwLeyA, controller := some p0, affectedPlayer := p0,
        kind := .modifyCountersPut (some pwId) none (add := 1) (mult := 1) }) (cause := some testCause)).createEffect
      (.replacement {
        id := cMulId, source := some pwLeyB, controller := some p0, affectedPlayer := p0,
        kind := .modifyCountersPut (some pwId) none (add := 0) (mult := 2) }) (cause := some testCause)
  -- Activate `[+2]` + stun + sacrificeSource: pauses on loyalty counter replacement first, then stun replacement, then sacrifices!
  let gPwPause1 := mustApply gPwRepl p0 (.activate pwId 0)
  let pwStillOnBfDuringLoyalty := (gPwPause1.findObject? pwId).any (·.isOnBattlefield)
  let gPwPause2 := mustApply gPwPause1 p0 (.chooseReplacement cAddId)
  let pwStillOnBfDuringStun :=
    (gPwPause2.findObject? pwId).any (fun o =>
      o.isOnBattlefield && o.status.loyaltyCounters == (gPwRepl.object! pwId).status.loyaltyCounters + 6) &&
    gPwPause2.proposedSpell.any (·.loyaltyPaid)
  let gPwSacDone := mustApply gPwPause2 p0 (.chooseReplacement cAddId)
  -- `[0]` loyalty (`pwZeroMultiPickAb`): sacrificing `pwId` itself on pick 1 (`sacrificeArtifact`) sets
  -- `ProposedSpell.loyaltyPaid == true` (while `sourceCounterCostPaidFor == false` per CR 118.11), keeping
  -- `sourceStillPayable`, `proposalCostPromptStillPayable`, and `becomeActivated` valid across pick 2 (`sacrificeAnotherArtifact`)!
  let gPwZero0 := gPw0.recordPutCounters pwId .loyalty 3 (some p0) (cause := some testCause)
  let gPwZeroStarted := mustApply (mustApply gPwZero0 p0 (.activate pwId 1)) p0 (.choosePermanents #[pwId])
  let zeroSpellId := gPwZeroStarted.proposedSpell.get!.spellId
  let zeroNoCounterEv := !gPwZeroStarted.sourceCounterCostPaidFor pwId (some zeroSpellId) .loyalty
  let zeroStillPayable :=
    gPwZeroStarted.sourceStillPayable gPwZeroStarted.proposedSpell.get! &&
    gPwZeroStarted.proposalCostPromptStillPayable p0 gPwZeroStarted.pending
  let gPwZeroFinished := mustApply gPwZeroStarted p0 (.choosePermanents #[pwBaubleIds[0]!])
  -- `[-0]` + `sacrificeSource` (`pwMinusZeroSacAb`) and `[+X]` (`pwPlusXAb` with `chosenX = 10 > loyaltyCounters`):
  let gPwMinusZeroDone := mustApply gPwZero0 p0 (.activate pwId 2)
  let (gPxStack, pxAb) := gPw0.putStackAbility (gPw0.object! pwId) p0 (abilityEffect := some (Effect.gainLife 1))
  let gPxAnnounced :=
    gPxStack.record (GameEvent.announced gPxStack.turnNumber pxAb.id #[] (some 10) #[] (cause := some testCause))
  let pxAbObj := gPxAnnounced.object! pxAb.id
  let pxProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := pxAb.id, original := pxAbObj
    originalSnapshot := gPxAnnounced.snapshot pxAbObj, kind := .activatedAbility
    sourceId := some pwId, activation := some pwPlusXAb
  }
  let gPxSet := gPxAnnounced.change (.proposedSpell (some pxProp))
  let plusXPayableOk :=
    gPxSet.sourceStillPayable pxProp &&
    gPxSet.proposalCostPromptStillPayable p0 (.sacrificePermanent p0 pwId)
  -- `!exileSource` graveyard/hand guards:
  let badGyExileAb : ActivatedAbility := {
    activeZones := #[.graveyard], cost := CostSpec.ofItems #[.exile (.exact 1) .battlefield .self], effect := Effect.gainLife 1
  }
  let badHandExileAb : ActivatedAbility := {
    activeZones := #[.hand], cost := CostSpec.ofItems #[.exile (.exact 1) .battlefield .self], effect := Effect.gainLife 1
  }
  let gExGuard0 := insertObject (insertObject g3 bear p0 (.graveyard p0)) bear p0 (.hand p0)
  let badGyCard := gExGuard0.object! (gExGuard0.player p0).graveyard.back!
  let badHandCard := gExGuard0.object! (gExGuard0.player p0).hand.back!
  let badGyProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := badGyCard.id, original := badGyCard
    originalSnapshot := gExGuard0.snapshot badGyCard, kind := .activatedAbility
    sourceId := some badGyCard.id, activation := some badGyExileAb
  }
  let badHandProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := badHandCard.id, original := badHandCard
    originalSnapshot := gExGuard0.snapshot badHandCard, kind := .activatedAbility
    sourceId := some badHandCard.id, activation := some badHandExileAb
  }
  let gyPayErr :=
    match gExGuard0.payActivationExtraCosts p0 badGyCard.id false false 0 false (some badGyExileAb) 0 with
    | .error _ => true | .ok _ => false
  let handPayErr :=
    match gExGuard0.payActivationExtraCosts p0 badHandCard.id false false 0 false (some badHandExileAb) 0 with
    | .error _ => true | .ok _ => false
  let loyaltyAndExileGuardsOk :=
    mustHold38i4 "4a.pwPause1" pwStillOnBfDuringLoyalty &&
    mustHold38i4 "4a.pwPause2" pwStillOnBfDuringStun &&
    mustHold38i4 "4a.pwSacDone"
      ((gPwSacDone.followMovedToZone? pwId (· == .graveyard p0)).isSome &&
       gPwSacDone.proposedSpell.isNone && gPwSacDone.stack.size == 1) &&
    mustHold38i4 "4a.zeroPick1"
      (gPwZeroStarted.proposedSpell.any (·.loyaltyPaid) && zeroNoCounterEv && zeroStillPayable) &&
    mustHold38i4 "4a.zeroDone" (gPwZeroFinished.proposedSpell.isNone && gPwZeroFinished.stack.size == 1) &&
    mustHold38i4 "4a.minusZeroDone" (gPwMinusZeroDone.proposedSpell.isNone && gPwMinusZeroDone.stack.size == 1) &&
    mustHold38i4 "4a.plusX" plusXPayableOk &&
    mustHold38i4 "4a.exileGuards"
      (!gExGuard0.sourceStillPayable badGyProp && !gExGuard0.sourceStillPayable badHandProp &&
       gyPayErr && handPayErr)

  -- 4b. Live `proposedSpell` retention across final cost-payment replacement pauses into `becomeCast` /
  --     `finishPostLoyaltyActivated` (card/control owner `p2` OR caster `p0` conceding during final sacrifice
  --     replacement pause aborts and rewinds the proposal cleanly without emitting `spellCast` / `abilityActivated`!):
  let sacBoltDef : CardDef := {
    name := "P38i4 SacBolt", manaCost := ManaCost.empty, types := #[.sorcery]
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeArtifactOrCreature]
    spellEffect := some (Effect.dealDamage 3)
  }
  let sacPingArtDef : CardDef := {
    name := "P38i4 SacCannon", types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.sacrifice (.exact 1) .self]
      effect := Effect.dealDamage 2
    }]
  }
  let p2GrantAuraDef : CardDef := { name := "P38i4 GrantAura", types := #[.enchantment] }
  let gRet0 :=
    insertObject
      (addPermanent
        (addPermanent (addPermanent (addPermanent (addPermanent g3 sacPingArtDef p1 p1) p2GrantAuraDef p2 p2) baubleDef p0 p0) leyADef p0 p0)
        leyBDef p0 p0)
      sacBoltDef p2 .exile
  let retCannonId := (gRet0.permanentsOf p1).find? (·.name == sacPingArtDef.name) |>.get!.id
  let retP2AuraId := (gRet0.permanentsOf p2).find? (·.name == p2GrantAuraDef.name) |>.get!.id
  let retBaubleId := (gRet0.permanentsOf p0).find? (·.name == baubleDef.name) |>.get!.id
  let retLeyA := (gRet0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let retLeyB := (gRet0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let retBoltId := (gRet0.objects.filter (fun o => o.zone == .exile && o.name == sacBoltDef.name))[0]!.id
  let sRidA : ReplacementId := { kind := .exileOppDeath, object := some retLeyA }
  let sRidB : ReplacementId := { kind := .exileOppDeath, object := some retLeyB }
  let gRet1 :=
    ((((gRet0.createEffect
      (.permission (some p0) (.playFromExile retBoltId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[retCannonId]) (.control p0) (.whileSourceOnBattlefield retP2AuraId))
      (cause := some testCause)).createEffect
      (.replacement {
        id := sRidA, source := some retLeyA, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard none false }) (cause := some testCause)).createEffect
      (.replacement {
        id := sRidB, source := some retLeyB, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard none false }) (cause := some testCause))
  -- Spell cast: `p0` casts `p2`-owned `retBoltId` targeting `p1`, `.pay`, sacrifices `retBaubleId` ->
  -- pauses on `sRidA`/`sRidB` with `proposedSpell.isSome`!
  let gSpPause :=
    mustApply (mustApply (mustApply (mustApply gRet1 p0 (.cast retBoltId)) p0 (.targets #[.player p1])) p0 .pay) p0 (.sacrifice retBaubleId)
  let spellPropRetainedAtPause := gSpPause.proposedSpell.isSome && gSpPause.proposalCheckpoint.isSome
  let gSpTargetConceded := mustApply gSpPause p2 .concede
  let gSpAfterChoice :=
    match gSpTargetConceded.pending with
    | .chooseReplacement q chs => mustApply gSpTargetConceded q (.chooseReplacement chs[0]!)
    | _ => gSpTargetConceded
  let gSpCasterConceded := mustApply gSpPause p0 .concede
  -- Activated ability: `p0` activates `p1`-owned `retCannonId` (controlled via `p2`'s `retP2AuraId`) targeting `p1`,
  -- sacrificing `retCannonId` pauses on `sRidA`/`sRidB` with `proposedSpell.isSome`!
  let gAbPause :=
    mustApply (mustApply gRet1 p0 (.activate retCannonId 0)) p0 (.targets #[.player p1])
  let abPropRetainedAtPause := gAbPause.proposedSpell.isSome && gAbPause.proposalCheckpoint.isSome
  let gAbTargetConceded := mustApply gAbPause p2 .concede
  let gAbAfterChoice :=
    match gAbTargetConceded.pending with
    | .chooseReplacement q chs => mustApply gAbTargetConceded q (.chooseReplacement chs[0]!)
    | _ => gAbTargetConceded
  let gAbCasterConceded := mustApply gAbPause p0 .concede
  let hasSpellCastEv (g : Game) : Bool :=
    g.events.any (fun e => match e.change with | .rules (.cast (.spellCast ..)) => true | _ => false)
  let hasAbActEv (g : Game) : Bool :=
    g.events.any (fun e => match e.change with | .rules (.cast (.abilityActivated ..)) => true | _ => false)
  let liveProposedRetentionOk :=
    spellPropRetainedAtPause &&
    gSpAfterChoice.proposedSpell.isNone &&
    (gSpAfterChoice.permanentsOf p0).any (·.id == retBaubleId) &&
    !hasSpellCastEv gSpAfterChoice &&
    gSpCasterConceded.proposedSpell.isNone &&
    !hasSpellCastEv gSpCasterConceded &&
    abPropRetainedAtPause &&
    gAbAfterChoice.proposedSpell.isNone &&
    (gAbAfterChoice.permanentsOf p1).any (·.id == retCannonId) &&
    !hasAbActEv gAbAfterChoice &&
    gAbCasterConceded.proposedSpell.isNone &&
    !hasAbActEv gAbCasterConceded

  -- 4c. Departed-player `finishManaAbilityMountainTrigger` & `abortDepartedManaAbilityCont` priority handoff:
  let painMtnDef : CardDef := {
    name := "P38i4 PainPeak", types := #[.land], subtypes := #["Mountain"]
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.oneOf (.explicit #[.colored .red, .colored .green]) (.const 1)) (damageYou := 1)]
  }
  let gPm0 :=
    (addPermanent (addPermanent (addPermanent g3 painMtnDef p0 p0) leyADef p0 p0) leyBDef p0 p0).createEffect
      (.mountainExtraRedThisTurn p0 1) (cause := some testCause)
  let pmId := (gPm0.permanentsOf p0).find? (·.name == painMtnDef.name) |>.get!.id
  let pmLeyA := (gPm0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let pmLeyB := (gPm0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let dRidA : ReplacementId := { kind := .addNoncombatDamage, object := some pmLeyA }
  let dRidB : ReplacementId := { kind := .multiplyDamage, object := some pmLeyB }
  let gPm1 :=
    (gPm0.createEffect
      (.replacement {
        id := dRidA, source := some pmLeyA, controller := some p0, affectedPlayer := p0,
        kind := .addNoncombatDamage none 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := dRidB, source := some pmLeyB, controller := some p0, affectedPlayer := p0,
        kind := .multiplyDamage none 2 }) (cause := some testCause)
  let pmIdx := (gPm1.manaAbilityDefs (gPm1.object! pmId)).findIdx? (fun d => d.damageYou > 0) |>.get!
  let gPmPaused :=
    match gPm1.activateManaAbility p0 pmId pmIdx #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gPmConceded := mustApply gPmPaused p0 .concede
  -- `abortDepartedManaAbilityCont`: `prevPending = .mayPayGeneric p0 1` belongs to `p0`; when `p0` sacrifices
  -- a mana artifact (`sRidA`/`sRidB` pause) and concedes, `.restorePending` clears `.mayPayGeneric p0 1` to `.none`
  -- and the fall-through `g.receivePriority p0` grants priority to `p1`!
  let sacManaDef : CardDef := { name := "P38i4 ManaLotus", types := #[.artifact], activatedAbilities := #[ActivatedAbility.manaTapSacrificeAnyColor] }
  let gAbMaBase := addPermanent (addPermanent (addPermanent g3 sacManaDef p0 p0) leyADef p0 p0) leyBDef p0 p0
  let abMaLeyA := (gAbMaBase.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let abMaLeyB := (gAbMaBase.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let mSRidA : ReplacementId := { kind := .exileOppDeath, object := some abMaLeyA }
  let mSRidB : ReplacementId := { kind := .exileOppDeath, object := some abMaLeyB }
  let gAbMa0 :=
    (((gAbMaBase.createEffect
      (.replacement {
        id := mSRidA, source := some abMaLeyA, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard none false }) (cause := some testCause)).createEffect
      (.replacement {
        id := mSRidB, source := some abMaLeyB, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard none false }) (cause := some testCause)).change
      (.pending (.mayPayGeneric p0 1)))
  let lotusId := (gAbMa0.permanentsOf p0).find? (·.name == sacManaDef.name) |>.get!.id
  let gAbMaPaused :=
    match gAbMa0.activateManaAbility p0 lotusId 0 #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gAbMaConceded := mustApply gAbMaPaused p0 .concede
  let manaDepartedEdgeOk :=
    mustHold38i4 "4c.pmPaused" gPmPaused.sbaPaused &&
    mustHold38i4 "4c.pmConceded"
      ((gPmConceded.player p0).leftTheGame && (gPmConceded.player p0).manaPool.total == 0 &&
       gPmConceded.priority == p1) &&
    mustHold38i4 "4c.abMaConceded"
      ((gAbMaConceded.player p0).leftTheGame && gAbMaConceded.pending == Pending.none &&
       gAbMaConceded.priority == p1)

  -- 4d. Mid-proposal payability reversals on `.crew`, `.zemoBoastExile`, `payTeamworkCreatures` (`canPayLife`),
  --     and `.chooseMode` `decline`:
  let vehDef : CardDef := {
    name := "P38i4 Skiff", types := #[.artifact], subtypes := #["Vehicle"]
    power := some 4, toughness := some 4, keywords := #[.crew 2]
  }
  let blackFuelDef : CardDef := {
    bear with name := "P38i4 BlackFuel", manaCost := { symbols := Array.replicate 15 (.colored .black) }
  }
  let zemoDef : CardDef := {
    creature "P38i4 Zemo" ManaCost.empty #["Human", "Villain"] 3 3 with
    activatedAbilities := #[ActivatedAbility.zemoBoastAbility]
  }
  let twLifeSpellDef : CardDef := {
    name := "P38i4 TeamStrike", manaCost := ManaCost.empty, types := #[.sorcery]
    keywords := #[.teamwork 2], spellEffect := some (Effect.gainLife 3)
  }
  let modalRodDef : CardDef := {
    name := "P38i4 ModalRod", types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf], effect := Effect.gainLife 1, otherModes := #[Effect.gainLife 2]
    }]
  }
  let gMidRev0 :=
    insertObject
      (insertObject
        (addPermanent
          (addPermanent (addPermanent (addPermanent g3 vehDef p0 p0) zemoDef p0 p0) modalRodDef p0 p0)
          bear p0 p0)
        blackFuelDef p0 (.graveyard p0))
      twLifeSpellDef p0 (.hand p0)
  let skiffId := (gMidRev0.permanentsOf p0).find? (·.name == vehDef.name) |>.get!.id
  let zemoId := (gMidRev0.permanentsOf p0).find? (·.name == zemoDef.name) |>.get!.id
  let mRodId := (gMidRev0.permanentsOf p0).find? (·.name == modalRodDef.name) |>.get!.id
  let crewBearId := (gMidRev0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let fuelGyId := (gMidRev0.player p0).graveyard.back!
  let twSpellId := (gMidRev0.player p0).hand.find? (fun id => (gMidRev0.object! id).name == twLifeSpellDef.name) |>.get!

  -- (i) `.crew` reverses without tapping `crewBearId` when `skiffId` was stolen:
  let (gCrStack, crAb) := (gMidRev0.change .saveProposalCheckpoint).putStackAbility (gMidRev0.object! skiffId) p0
    (abilityEffect := some (Effect.gainLife 1))
  let crProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := crAb.id, original := crAb
    originalSnapshot := gCrStack.snapshot crAb, kind := .activatedAbility, sourceId := some skiffId
  }
  let gCrStolen :=
    (gCrStack.changes #[.proposedSpell (some crProp), .pending (.fraChoice p0 (.crew crAb.id skiffId 2))]).createEffect
      (.control skiffId p2) (cause := some testCause)
  let gCrReversed := mustApply gCrStolen p0 (.choosePermanents #[crewBearId])

  -- (ii) `.zemoBoastExile` reverses without exiling `fuelGyId` when `zemoId` was stolen:
  let (gZmStack, zmAb) := (gMidRev0.change .saveProposalCheckpoint).putStackAbility (gMidRev0.object! zemoId) p0
    (abilityEffect := some ActivatedAbility.zemoBoastAbility.effect)
  let zmProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := zmAb.id, original := zmAb
    originalSnapshot := gZmStack.snapshot zmAb, kind := .activatedAbility
    sourceId := some zemoId, activation := some ActivatedAbility.zemoBoastAbility
  }
  let gZmStolen :=
    (gZmStack.changes #[.proposedSpell (some zmProp), .pending (.fraChoice p0 (.zemoBoastExile zmAb.id zemoId))]).createEffect
      (.control zemoId p2) (cause := some testCause)
  let gZmReversed := mustApply gZmStolen p0 (.choosePermanents #[fuelGyId])

  -- (iii) `payTeamworkCreatures` reverses without tapping `crewBearId` when `!canPayLife`:
  let gTwStarted :=
    ((mustApply (mustApply gMidRev0 p0 (.cast twSpellId)) p0 (.announceTeamwork true)).changeProposal (.payLife 5)).loseLife
      p0 17 (cause := some testCause)
  let gTwAnswerRev := mustApply gTwStarted p0 (.choosePermanents #[crewBearId])
  let gTwDeclineRev := mustApply gTwStarted p0 .decline

  -- (iv) `.chooseMode` `decline` reverses when `!sourceStillPayable`:
  let gModeStarted := mustApply gMidRev0 p0 (.activate mRodId 0)
  let gModeStolen := gModeStarted.createEffect (.control mRodId p2) (cause := some testCause)
  let gModeDeclineRev := mustApply gModeStolen p0 .decline

  let midProposalReversalsOk :=
    gCrReversed.proposedSpell.isNone &&
    !(gCrReversed.object! crewBearId).status.tapped &&
    gZmReversed.proposedSpell.isNone &&
    (gZmReversed.player p0).graveyard.contains fuelGyId &&
    gTwAnswerRev.proposedSpell.isNone &&
    !(gTwAnswerRev.object! crewBearId).status.tapped &&
    gTwDeclineRev.proposedSpell.isNone &&
    gModeDeclineRev.proposedSpell.isNone &&
    gModeDeclineRev.stack.isEmpty

  mustHold38i4 "4a.loyaltyAndExileGuards" loyaltyAndExileGuardsOk &&
  mustHold38i4 "4b.liveProposedRetention" liveProposedRetentionOk &&
  mustHold38i4 "4c.manaDepartedEdge" manaDepartedEdgeOk &&
  mustHold38i4 "4d.midProposalReversals" midProposalReversalsOk &&
  mustHold38i4 "4.replay"
    (replayOk38i4 #[gPwPause1, gPwPause2, gPwSacDone, gPwZeroStarted, gPwZeroFinished, gPwMinusZeroDone,
      gSpPause, gSpTargetConceded, gSpAfterChoice, gSpCasterConceded,
      gAbPause, gAbTargetConceded, gAbAfterChoice, gAbCasterConceded,
      gPmPaused, gPmConceded, gAbMaPaused, gAbMaConceded,
      gCrReversed, gZmReversed, gTwAnswerRev, gTwDeclineRev, gModeDeclineRev])

end Phase38Item4EventAlignment

end Mtg.Engine.EventTests
