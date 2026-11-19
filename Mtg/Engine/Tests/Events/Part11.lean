import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase45Item1EventAlignment

private def mustHold45i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase45Item1EventAlignment failed: {label}"

private def replayOk45i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with supertypes := #[.legendary] }
  let legHeroDef : CardDef := { hero with supertypes := #[.legendary] }
  let leyADef : CardDef := { name := "P45i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P45i1 LeyB", types := #[.enchantment] }
  let p2AnchorDef : CardDef := { name := "P45i1 P2Anchor", types := #[.artifact] }

  -- 1a(i). `rewriteRepausedPostCloseBatch` `flushedFromPending && !deferRestore`
  --        preserves `O_0 >> outerTail >> O_caller` ordering (30 -> 40 -> 47):
  let gTwoGrp0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
        legHeroDef p0 p0)
      legHeroDef p0 p0
  let gTwoPaused0 := gTwoGrp0.checkSBA
  let oldBid1 := (gTwoPaused0.currentBatch.map Prod.fst).get!
  let (closePrefix1, _) := (gTwoPaused0.pendingReplacement.bind (Game.splitAfterCloseBatchFor? oldBid1)).get!
  let grp1CopyId := match gTwoPaused0.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999999⟩
  let o0Cont := PendingReplacement.setLife p0 30 "o0" (some testCause)
  let tailCont := PendingReplacement.setLife p0 40 "tail" (some testCause)
  let oCallerCont := PendingReplacement.gainLife p0 7 (some testCause)
  let (gOrd1Inv, _) :=
    (gTwoPaused0.changes #[
      .pendingReplacement (some (.seq closePrefix1
        (.seq (.leavePlayersWhoLost none true #[] none) tailCont))),
      .pushOuterPendingReplacement o0Cont,
      .pushOuterPendingReplacement oCallerCont ]).move grp1CopyId .exile none (cause := some testCause)
  let (gOrd1Mid, _, _, _, _, _) :=
    gOrd1Inv.checkSBACountedWithLeavesCore (popOuterIn := true) (deferRestore := false)
  let grp2KeepId := match gOrd1Mid.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999998⟩
  let gOrd1Done := (mustApply gOrd1Mid p0 (.keepLegend grp2KeepId)).drainPendingContinuations

  -- 1a(ii). `rewriteRepausedPostCloseBatch` `!flushedFromPending && !deferRestore`
  --         sequences `throughClose >> O_0 >> remTail` (ret2 enters -> 40 -> 47) when a repaused
  --         linked-exile return opens a new batch `newBid`:
  let gInner0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
          leyADef p0 p0)
        leyBDef p0 p0)
      bear p0 p0
  let inLeyA := (gInner0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let inLeyB := (gInner0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let inRidA : ReplacementId :=
    { kind := .entersWithExtraCounters, object := some inLeyA, counterKind := some .plusOnePlusOne }
  let inRidB : ReplacementId :=
    { kind := .entersWithExtraCounters, object := some inLeyB, counterKind := some .plusOnePlusOne }
  let gInner1 :=
    insertObject
      (insertObject
        ((gInner0.createEffect
          (.replacement {
            id := inRidA, source := some inLeyA, controller := some p0, affectedPlayer := p0,
            kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
          (.replacement {
            id := inRidB, source := some inLeyB, controller := some p0, affectedPlayer := p0,
            kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
        bear p0 .exile)
      hero p0 .exile
  let exRetIds := (gInner1.objects.filter (·.zone == .exile)).map (·.id)
  let ret1Id := exRetIds[0]!
  let ret2Id := exRetIds[1]!
  let gInnerPaused := gInner1.checkSBA
  let oldBid2 := (gInnerPaused.currentBatch.map Prod.fst).get!
  let (closeOld2, _) := (gInnerPaused.pendingReplacement.bind (Game.splitAfterCloseBatchFor? oldBid2)).get!
  let inGrpCopy := match gInnerPaused.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999997⟩
  let inPausedWithLink :=
    PendingReplacement.seq closeOld2
      (.seq (.finishLinkedExileMove #[ret1Id, ret2Id])
        (.seq (.leavePlayersWhoLost none true #[] none) (.gainLife p0 7 (some testCause))))
  let (gInnerInv, _) :=
    (gInnerPaused.changes #[
      .pendingReplacement none,
      .pushOuterPendingReplacement (.setLife p0 40 "o0_2" (some testCause)),
      .pushOuterPendingReplacement inPausedWithLink ]).move inGrpCopy .exile none (cause := some testCause)
  let (gInnerMid, _, _, _, _, _) :=
    gInnerInv.checkSBACountedWithLeavesCore (popOuterIn := true) (deferRestore := false)
  let gInnerAfter1 := mustApply gInnerMid p0 (.chooseReplacement inRidA)
  let gInnerAfter2 := (mustApply gInnerAfter1 p0 (.chooseReplacement inRidA)).drainPendingContinuations
  let ret2MovedIdx? := gInnerAfter2.events.findIdx? fun ev =>
    match ev.change with
    | .rules (.zone (.moved before _ .exile .battlefield ..)) => before.id == some ret2Id
    | _ => false
  let o0Life40Idx? := gInnerAfter2.events.findIdx? fun ev =>
    ev.change == .engine (.logMsg "o0_2")

  -- 1a(iii). `checkSBACountedWithLeavesCore` non-SBA flushed `some pr` pushed ahead of `O_caller`,
  --          plus direct `checkSBACounted` (`!fromLeavesLoop`) chaining `savedIn`:
  let oldFlushBid : BatchId := ⟨9451⟩
  let gNonSba0 :=
    insertObject
      (insertObject (addPermanent (addPermanent g4 legHeroDef p0 p0) legHeroDef p0 p0) bear p0 .exile)
      bear p0 .exile
  let deadPromptIds := (gNonSba0.objects.filter (·.zone == .exile)).map (·.id)
  let gNonSbaOpen :=
    gNonSba0.changes #[
      .pauseBatch oldFlushBid (some testCause) gNonSba0.objects gNonSba0.players gNonSba0.activeEffects
        (.chooseLegend p0 bear.name deadPromptIds) gNonSba0.stack,
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 5 (some testCause)),
      .pendingReplacement (some (.seq (.closeBatch oldFlushBid gNonSba0.events.size)
        (.setLife p0 30 "nonSbaPr" (some testCause)))) ]
  let (gNonSbaPaused, _, _, _, _, _) :=
    gNonSbaOpen.checkSBACountedWithLeavesCore (popOuterIn := true) (deferRestore := false)
  let nonSbaHeroKeep := match gNonSbaPaused.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999996⟩
  let gNonSbaDone := (mustApply gNonSbaPaused p0 (.keepLegend nonSbaHeroKeep)).drainPendingContinuations
  let (gDirectSba, _) := g4.checkSBACounted (savedIn := some (.mayPayGeneric p0 2))
  let gDirectDrained := gDirectSba.drainPendingContinuations

  -- 1a(iv). `openBatchAwaitedPausePrompt` protects an open resolving batch `preCkptBid` across
  --         both seats of a 2HG team concede (`p2` + `p3`), preventing premature `.closeBatch`
  --         and CR 704.3 mid-resolution SBA sweeps after `p2` clears `proposalCheckpoint`:
  let cfg2hg1 : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "C0", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "C1", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed := 451
    startingPlayer := some 0
  }
  let g2hgBase : Game :=
    match Start.start cfg2hg1 with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  let zeroToughDef : CardDef := creature "P45i1 ZeroWisp" ManaCost.empty #["Spirit"] 0 0
  let g2hgRes0 :=
    addPermanent
      (addPermanent (addPermanent g2hgBase zeroToughDef ⟨0⟩ ⟨0⟩) bear ⟨4⟩ ⟨4⟩)
      p2AnchorDef ⟨2⟩ ⟨2⟩
  let wispId := (g2hgRes0.permanentsOf ⟨0⟩).find? (·.name == zeroToughDef.name) |>.get!.id
  let c0Bear := (g2hgRes0.permanentsOf ⟨4⟩)[0]!
  let b0Anc := (g2hgRes0.permanentsOf ⟨2⟩)[0]!
  let g2hgRes1 :=
    g2hgRes0.createEffect
      (.layered (.objects #[c0Bear.id]) (.control ⟨0⟩) (.whileSourceOnBattlefield b0Anc.id))
      (cause := some testCause)
  let resBid : BatchId := ⟨9452⟩
  let resClose :=
    PendingReplacement.seq (.gainLife ⟨0⟩ 6 (some testCause)) (.closeBatch resBid g2hgRes1.events.size)
  let g2hgResOpen :=
    g2hgRes1.changes #[
      .pauseBatch resBid (some testCause) g2hgRes1.objects g2hgRes1.players g2hgRes1.activeEffects
        .none g2hgRes1.stack,
      .pushContinuationFrame {},
      .pendingReplacement (some resClose),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement resClose,
      .pendingReplacement none ]
  let (g2hgRes2, resAb) := g2hgResOpen.putStackAbility c0Bear ⟨0⟩ (abilityEffect := some (Effect.gainLife 1))
  let resProp : ProposedSpell := {
    caster := ⟨0⟩, cost := ManaCost.empty, spellId := resAb.id, original := resAb
    originalSnapshot := g2hgRes2.snapshot resAb, kind := .activatedAbility
    sourceId := some c0Bear.id, resolutionCast := true
  }
  let g2hgProposed := g2hgRes2.changes #[.proposedSpell (some resProp), .pending (.chooseX ⟨0⟩)]
  let preConcedeIdx := g2hgProposed.events.size
  let g2hgAfterTeamB := mustApply g2hgProposed ⟨2⟩ .concede
  let postConcedeSlice := g2hgAfterTeamB.events.extract preConcedeIdx g2hgAfterTeamB.events.size
  let p3LeftPos? := postConcedeSlice.findIdx? fun ev =>
    ev.change == .rules (.player (.leftGame ⟨3⟩))
  let gain6Pos? := postConcedeSlice.findIdx? fun ev =>
    ev.change == .rules (.life (.gained ⟨0⟩ 6)) && ev.batch == some resBid
  let wispMovePos? := postConcedeSlice.findIdx? fun ev =>
    match ev.change with
    | .rules (.zone (.moved before _ .battlefield _ ..)) => before.id == some wispId
    | _ => false
  let resBidProtectedAcrossTeamB : Bool :=
    (match p3LeftPos?, gain6Pos? with | some lPos, some gPos => decide (lPos < gPos) | _, _ => false) &&
    wispMovePos?.all (fun wPos => gain6Pos?.any (fun gPos => decide (gPos < wPos)))
  let wisp4pDef : CardDef := creature "P45i1 Wisp4p" ManaCost.empty #[] 0 0
  let gPriorReplBase := addPermanent g4 wisp4pDef p0 p0
  let wisp4pId := (gPriorReplBase.permanentsOf p0).back!.id
  let priorRid : ReplacementId := { kind := .entersWithExtraCounters, object := some wisp4pId, counterKind := some .plusOnePlusOne }
  let gAfterSyncRepl :=
    gPriorReplBase.changes #[
      .pending (.chooseReplacement p0 #[priorRid]),
      .pending .none ]
  let freshResBid : BatchId := ⟨9465⟩
  let gFreshRes :=
    (gAfterSyncRepl.change (.pauseBatch freshResBid (some testCause)
      gAfterSyncRepl.objects gAfterSyncRepl.players gAfterSyncRepl.activeEffects .none gAfterSyncRepl.stack)).gainLife
      p0 2 (cause := some testCause)
  let (gFreshAfterSba, _) := gFreshRes.checkSBACountedWithLeavesCore
  let freshResSkipOk : Bool :=
    !gFreshRes.openBatchAwaitedPausePrompt &&
    gFreshAfterSba.currentBatch.map Prod.fst == some freshResBid &&
    (gFreshAfterSba.findObject? wisp4pId).any (·.isOnBattlefield)

  -- 1a(v). `!rewindAbortedProposal` preserves `pendingMayCastFromExile` and `pendingFreeCopies`
  --        when a third party `p2` departs and rewinds `p0`'s proposal (and does not rebuild a
  --        decremented prompt when `ckpt` did not carry that stash):
  let drawDivDef : CardDef := {
    name := "P45i1 DrawTwo"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    spellEffect := some { resolution := .draw 2, phrase := "Draw two cards." }
  }
  let gMayEx0 :=
    (insertObject (insertObject g4 shock p2 .exile) drawDivDef p0 .exile).changes #[
      .pushContinuationFrame {} ]
  let p2ExId := (gMayEx0.objects.filter (fun o => o.zone == .exile && o.owner == p2))[0]!.id
  let p0ExId := (gMayEx0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!.id
  let gMayExPrompt :=
    gMayEx0.change (.pending (.fraChoice p0 (.mayCastUpToFromExile #[p2ExId, p0ExId] 2)))
  let gMayExProposed := mustApply gMayExPrompt p0 (.choosePermanents #[p2ExId])
  let gMayExAfterP2 := mustApply gMayExProposed p2 .concede

  let gNoStashBase :=
    (gMayEx0.createEffect (.permission p0 (.playFromExile p2ExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause))
  let gNoStashMay :=
    (mustApply gNoStashBase p0 (.cast p2ExId)).change
      (.continuation (.pendingMayCastFromExile (some (p0, #[p2ExId, p0ExId], 1))))
  let gNoStashMayAfterP2 := mustApply gNoStashMay p2 .concede
  let gNoStashCp :=
    (mustApply gNoStashBase p0 (.cast p2ExId)).change
      (.continuation (.pendingFreeCopies (some (p0, #[p2ExId, p0ExId], 5, 1))))
  let gNoStashCpAfterP2 := mustApply gNoStashCp p2 .concede

  let gCp0 := insertObject (insertObject g4 shock p2 .exile) drawDivDef p0 .exile
  let cpP2Id := (gCp0.objects.filter (fun o => o.zone == .exile && o.owner == p2))[0]!.id
  let cpP0Id := (gCp0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!.id
  let gCp2 :=
    gCp0.changes #[
      .pushContinuationFrame {},
      .pending (.fraChoice p0 (.castCopiesFree #[cpP2Id, cpP0Id] 5 1)) ]
  let gCpProposed := mustApply gCp2 p0 (.cast cpP2Id)
  let gCpAfterP2 := mustApply gCpProposed p2 .concede

  let item1aOk :=
    mustHold45i1 "1a_i" ((gOrd1Done.player p0).life == 47) &&
    mustHold45i1 "1a_ii"
      ((gInnerAfter2.player p0).life == 47 &&
       (match ret2MovedIdx?, o0Life40Idx? with | some rIdx, some oIdx => rIdx < oIdx | _, _ => false)) &&
    mustHold45i1 "1a_iii"
      ((gNonSbaDone.player p0).life == 35 && gDirectDrained.pending == .mayPayGeneric p0 2) &&
    mustHold45i1 "1a_iv"
      ((g2hgAfterTeamB.player ⟨2⟩).leftTheGame &&
       (g2hgAfterTeamB.player ⟨3⟩).leftTheGame &&
       resBidProtectedAcrossTeamB &&
       freshResSkipOk) &&
    mustHold45i1 "1a_v_mayEx"
      (gMayExProposed.pendingMayCastFromExile == some (p0, #[p0ExId], 1) &&
       gMayExAfterP2.pending == .fraChoice p0 (.mayCastUpToFromExile #[p0ExId] 2) &&
       gNoStashMayAfterP2.pending == .none) &&
    mustHold45i1 "1a_v_freeCp"
      ((gCpAfterP2.findObject? cpP0Id).any (·.zone == .exile) &&
       gCpAfterP2.pending == .fraChoice p0 (.castCopiesFree #[cpP2Id, cpP0Id] 5 1) &&
       gNoStashCpAfterP2.pending == .none)

  -- 1b. `Leaving.preBatchLegendSnapshotValid`:
  --     (i) `depBid?` excludes post-departure CR 610.3 `returnLinkedExileMoves` batch (`retBid != depBid`);
  --     (ii) `to_ != .battlefield` rejects battlefield-entering zone moves;
  --     (iii) multi-chooser `effCtrls` catches `.legendRuleOff` expiry for a second chooser `p1`:
  let gDepBoundary0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0) legBearDef p0 p0)
      p2AnchorDef p2 p2
  let p2Banisher := (gDepBoundary0.permanentsOf p2)[0]!
  let p0Banished := ((gDepBoundary0.permanentsOf p0).filter (·.name == legBearDef.name))[2]!
  let gDepBoundary1 :=
    (gDepBoundary0.exileUntilSourceLeaves (some p2Banisher.id) p0Banished (cause := some testCause)).checkSBA
  let gDepBoundaryAfterP2 := mustApply gDepBoundary1 p2 .concede
  -- Direct isolated checks on `depBid?` (`retBid1b != depBid1b` even with `to_ == .graveyard p0`)
  -- and `to_ != .battlefield` (even inside `depBid1b` with `cause == .gameRule .playerLeftGame`):
  let legBid1b := (gDepBoundary1.currentBatch.map Prod.fst).get!
  let depBid1b : BatchId := ⟨legBid1b.raw + 49⟩
  let retBid1b : BatchId := ⟨legBid1b.raw + 50⟩
  let exCard1b := (gDepBoundary1.objects.filter (·.zone == .exile))[0]!
  let eoEx1b := gDepBoundary1.snapshot exCard1b
  let gFakePostDepReturn :=
    (gDepBoundary1.replayEvent ((GameEvent.playerLeftGame gDepBoundary1.turnNumber p2).withBatch depBid1b)).replayEvent
      ((GameEvent.moved gDepBoundary1.turnNumber eoEx1b .exile (.graveyard p0)
        (after := some { eoEx1b with zone := .graveyard p0 })
        (cause := .gameRule .staticAbility)).withBatch retBid1b)
  let gFakeSameBatchBfEnter :=
    (gDepBoundary1.replayEvent ((GameEvent.playerLeftGame gDepBoundary1.turnNumber p2).withBatch depBid1b)).replayEvent
      ((GameEvent.moved gDepBoundary1.turnNumber eoEx1b .exile .battlefield
        (after := some { eoEx1b with zone := .battlefield, controller := some p0, defaultController := some p0 })
        (cause := .gameRule .playerLeftGame)).withBatch depBid1b)

  -- Multi-chooser `effCtrls` (`p0` prompted first, `p1` also recorded in-batch; `p1`'s `.legendRuleOff` expires):
  let gMultiLeg0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
          legHeroDef p1 p1)
        legHeroDef p1 p1)
      p2AnchorDef p2 p2
  let p1LegIds := ((gMultiLeg0.permanentsOf p1).filter (·.name == legHeroDef.name)).map (·.id)
  let p0LegIds := ((gMultiLeg0.permanentsOf p0).filter (·.name == legBearDef.name)).map (·.id)
  let p2MirrorSrc := (gMultiLeg0.permanentsOf p2)[0]!
  let gMultiLeg1 :=
    gMultiLeg0.createEffect
      (.playerRule p1 .legendRuleOff (.whileSourceOnBattlefield p2MirrorSrc.id))
      (cause := some testCause)
  let multiBid : BatchId := ⟨9459⟩
  let multiStartIdx := gMultiLeg1.events.size
  let gMultiLegPaused :=
    gMultiLeg1.changes #[
      .pushContinuationFrame {},
      .pauseBatch multiBid (some testCause) gMultiLeg1.objects gMultiLeg1.players gMultiLeg1.activeEffects
        (.chooseLegend p0 legBearDef.name p0LegIds) gMultiLeg1.stack,
      .pendingReplacement (some (.closeBatch multiBid multiStartIdx)),
      .pending (.chooseLegend p1 legHeroDef.name p1LegIds),
      .pending (.chooseLegend p0 legBearDef.name p0LegIds) ]
  let gMultiAfterP2 := mustApply gMultiLegPaused p2 .concede

  let item1bOk :=
    mustHold45i1 "1b_i_retBatch"
      (gDepBoundary1.preBatchLegendSnapshotValid &&
       gDepBoundaryAfterP2.currentBatch.isSome &&
       !gDepBoundaryAfterP2.preBatchLegendSnapshotValid &&
       !gFakePostDepReturn.preBatchLegendSnapshotValid) &&
    mustHold45i1 "1b_ii_toBf"
      (!gFakeSameBatchBfEnter.preBatchLegendSnapshotValid) &&
    mustHold45i1 "1b_iii_effCtrls"
      (gMultiLegPaused.preBatchLegendSnapshotValid &&
       gMultiAfterP2.currentBatch.isSome &&
       !gMultiAfterP2.preBatchLegendSnapshotValid)

  -- 1c. Explicit priority preservation across `finishAndGrantPriority`, `resumePendingReplacementCore`
  --     (`.finishPostCast` & `reverseOrResumePopped`), `finishFraChoice`, and `Actions.applyAction` sacrifice:
  let gEntryExp0 :=
    (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.receivePriority p3)) ]
  let gEntryExpPaused := gEntryExp0.finishAndGrantPriority p0
  let expBearKeep := match gEntryExpPaused.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999995⟩
  let gEntryExpDone := mustApply gEntryExpPaused p0 (.keepLegend expBearKeep)

  let gPostCastExp :=
    (g4.changes #[.pushContinuationFrame {}]).resumePendingReplacement
      (.seq (.finishPostCast p0 false false false)
        (.seq (.gainLife p0 4 (some testCause)) (.receivePriority p3)))

  -- Illegal resolution-cast reversal inside `.seq (.restorePending (.sacrificePermanent p0 revStackId) false) ...`:
  let revSacSpellDef : CardDef := {
    name := "P45i1 UnpayableSac"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    additionalCostSacrificeCreature := true
    spellEffect := some { resolution := .gainLife 1, phrase := "Gain 1 life." }
  }
  let gRevExp0 := insertObject g4 revSacSpellDef p0 .exile
  let revSpellObj := (gRevExp0.objects.filter (·.zone == .exile))[0]!
  let gRevExpCkpt :=
    gRevExp0.changes #[
      .pushContinuationFrame {},
      .saveProposalCheckpoint ]
  let (gRevExpMoved, revStackId) := gRevExpCkpt.move revSpellObj.id .stack (some p0) (verb := some .cast)
    (cause := some testCause)
  let gRevExpOnStack := gRevExpMoved.putStackEntry p0 revStackId
  let revProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := revStackId
    original := revSpellObj, originalSnapshot := gRevExp0.snapshot revSpellObj
    needsSacrificeOther := true, resolutionCast := true
  }
  let gRevExp1 :=
    (gRevExpOnStack.change (.proposedSpell (some revProp))).resumePendingReplacement
      (.seq (.restorePending (.sacrificePermanent p0 revStackId) false)
        (.seq (.gainLife p0 9 (some testCause)) (.receivePriority p3)))

  -- `finishFraChoice` & resolution-cast sacrifice respecting `outerPendingReplacements` `.receivePriority p3`:
  let gOuterFra :=
    (g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p3) ]).finishFraChoice
  let sacCastDef : CardDef := {
    name := "P45i1 AltarRite"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    additionalCostSacrificeArtifactOrCreature := true
    spellEffect := some { resolution := .gainLife 1, phrase := "Gain 1 life." }
  }
  let gSacRes0 :=
    (insertObject (addPermanent g4 bear p0 p0) sacCastDef p0 .exile).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p3) ]
  let sacFodder := (gSacRes0.permanentsOf p0)[0]!.id
  let sacExSpell := (gSacRes0.objects.filter (·.zone == .exile))[0]!.id
  let gSacRes1 := gSacRes0.castAsPartOfResolution p0 sacExSpell
  let gSacRes2 := mustApply (mustApply gSacRes1 p0 .pay) p0 (.sacrifice sacFodder)

  let item1cOk :=
    mustHold45i1 "1c_i_entryExp"
      (gEntryExpPaused.pendingPriority == some p3 && gEntryExpDone.priority == p3) &&
    mustHold45i1 "1c_ii_postCast"
      ((gPostCastExp.player p0).life == 24 && gPostCastExp.priority == p3) &&
    mustHold45i1 "1c_ii_revExp"
      (gRevExp1.proposedSpell.isNone &&
       (gRevExp1.player p0).life == 20 &&
       gRevExp1.priority == p3) &&
    mustHold45i1 "1c_iii_outerFraAndSac"
      (gOuterFra.priority == p3 &&
       gSacRes2.stack.size == 1 &&
       gSacRes2.priority == p3)

  mustHold45i1 "1a.continuationOrderAndOpenBatchGuards" item1aOk &&
  mustHold45i1 "1b.preBatchLegendSnapshotValid" item1bOk &&
  mustHold45i1 "1c.explicitPriorityPreservation" item1cOk &&
  mustHold45i1 "1.replay"
    (replayOk45i1 #[gOrd1Done, gInnerAfter2, gNonSbaDone, gDirectDrained,
      g2hgAfterTeamB, gFreshAfterSba, gMayExAfterP2, gNoStashMayAfterP2,
      gCpAfterP2, gNoStashCpAfterP2, gDepBoundaryAfterP2, gMultiAfterP2,
      gEntryExpDone, gPostCastExp, gRevExp1, gOuterFra, gSacRes2])

end Phase45Item1EventAlignment

section Phase45Item2EventAlignment

private def mustHold45i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase45Item2EventAlignment failed: {label}"

private def replayOk45i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 2a. `!seatsExtra` CR 500.7 regular-turn ring resumption after a departed extra-turn team
  --     AND back-to-back 2HG departed-teammate CR 800.4i expiry:
  let cfg2hg2 : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "C0", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "C1", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed := 452
    startingPlayer := some 0
  }
  let g2hg0 : Game :=
    match Start.start cfg2hg2 with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  let gRing0 := addPermanent (addPermanent g2hg0 bear ⟨0⟩ ⟨0⟩) hero ⟨0⟩ ⟨0⟩
  let ringBuffId := (gRing0.permanentsOf ⟨0⟩).find? (·.name == bear.name) |>.get!.id
  let ringPhasedId := (gRing0.permanentsOf ⟨0⟩).find? (·.name == hero.name) |>.get!.id
  -- Advance across Team A's regular turn (`⟨0⟩ -> ⟨1⟩`) into Team B's EXTRA turn (`⟨2⟩`, `lastRegularTurnSeat == ⟨1⟩`):
  let gTeamBExtra0 :=
    (gRing0.record (GameEvent.extraTurnAdded gRing0.turnNumber ⟨2⟩ (cause := testCause))).startNextTurnAndBegin.startNextTurnAndBegin
  let gTeamBExtra1 :=
    ((gTeamBExtra0.createEffect
        (.layered (.objects #[ringBuffId]) (.ptModify 2 2) (.untilNextTurnOf ⟨2⟩))
        (cause := some testCause)).createEffect
      (.layered (.objects #[ringPhasedId]) (.control ⟨2⟩) .indefinite)
      (cause := some testCause))
  let gTeamBExtraPhased := gTeamBExtra1.phaseOut (gTeamBExtra1.object! ringPhasedId) (cause := some testCause)
  let gTeamBGoneInExtra := mustApply gTeamBExtraPhased ⟨2⟩ .concede
  -- Resuming regular turns from `lastRegularTurnSeat == ⟨1⟩` skips departed Team B (`⟨2⟩, ⟨3⟩`) on the way to `⟨4⟩`:
  -- `!seatsExtra` ensures `.untilNextTurnOf ⟨2⟩` expires AND `ringPhasedId` phases in!
  let gAtTeamC := gTeamBGoneInExtra.startNextTurnAndBegin

  -- Back-to-back 2HG turns (`!sameShared`, Regular -> Extra) for surviving `⟨0⟩` after teammate `⟨1⟩` departed:
  let gBack0 := addPermanent g2hg0 bear ⟨0⟩ ⟨0⟩
  let backBearId := (gBack0.permanentsOf ⟨0⟩)[0]!.id
  let (gA1Gone, _, _, _) :=
    (gBack0.record (GameEvent.playerLost gBack0.turnNumber ⟨1⟩ .lifeZeroOrLess)).playerLeavesGameCore ⟨1⟩
  let gBack1 :=
    (gA1Gone.createEffect
      (.layered (.objects #[backBearId]) (.ptModify 3 3) (.untilNextTurnOf ⟨1⟩))
      (cause := some testCause)).record
      (GameEvent.extraTurnAdded gA1Gone.turnNumber ⟨0⟩ (cause := testCause))
  let gBackExtra := gBack1.startNextTurnAndBegin

  let item2aOk :=
    gTeamBExtra0.activePlayer == ⟨2⟩ &&
    gTeamBExtra0.lastRegularTurnSeat == ⟨1⟩ &&
    gAtTeamC.activePlayer == ⟨4⟩ &&
    !(gAtTeamC.object! ringPhasedId).status.phasedOut &&
    gAtTeamC.power (gAtTeamC.object! ringBuffId) == 2 &&
    gBackExtra.activePlayer == ⟨0⟩ &&
    gBackExtra.power (gBackExtra.object! backBearId) == 2

  -- 2b. Cease-first `Core.expireWhileSourceEffects` `.fraEmblem` ordering & `skipLogIds`,
  --     `pre.name` in `Attachments.ceaseEndingFraEmblemsWhere`, and emblem-chain + exile-path `coDepartingIds`:
  let eqDef2 : CardDef := { name := "P45i2 Eq", types := #[.artifact], subtypes := #["Equipment"] }
  let embDef2 : CardDef := { name := "P45i2 RawEmblem", types := #[] }
  let maskedEmbDef2 : CardDef := { name := "P45i2 MaskedEmblem", types := #[] }
  let gCeaseFirst0 :=
    insertObject (addPermanent (addPermanent g4 eqDef2 p0 p0) bear p1 p1) embDef2 p0 .command (some p0)
  let cfAnchor := (gCeaseFirst0.permanentsOf p0).find? (·.name == eqDef2.name) |>.get!
  let cfStolen := (gCeaseFirst0.permanentsOf p1)[0]!
  let cfEmb := (gCeaseFirst0.objects.filter (·.zone == .command))[0]!
  let gCeaseFirst1 :=
    ((gCeaseFirst0.createEffect
      (.gameRule (.fraEmblem cfEmb.id) (.whileSourceOnBattlefield cfAnchor.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[cfStolen.id]) (.control p0) (.whileSourceOnBattlefield cfAnchor.id))
      (cause := some testCause))
  let preCfIdx := gCeaseFirst1.events.size
  let (gCeaseFirstAfter, _) := gCeaseFirst1.move cfAnchor.id .exile none (cause := some testCause)
  let cfSlice := gCeaseFirstAfter.events.extract preCfIdx gCeaseFirstAfter.events.size
  let cfEmbCeasedPos? := cfSlice.findIdx? fun ev =>
    match ev.change with | .rules (.zone (.ceasedToExist eo)) => eo.id == some cfEmb.id | _ => false
  let cfCtrlExpPos? := cfSlice.findIdx? fun ev =>
    match ev.change with
    | .rules (.continuousEffect (.expired _ (some (.layered _ (.control _) _)))) => true
    | _ => false

  let gPreName0 := insertObject g4 embDef2 p0 .command (some p0)
  let pnEmb := (gPreName0.objects.filter (·.zone == .command))[0]!
  let gPreName1 :=
    ((gPreName0.createEffect
      (.gameRule (.fraEmblem pnEmb.id) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[pnEmb.id]) (.copy maskedEmbDef2) .untilEndOfTurn)
      (cause := some testCause))
  let prePnLog := gPreName1.log.size
  let gPreNameAfter := gPreName1.clearEOT
  let pnLogs := gPreNameAfter.log.extract prePnLog gPreNameAfter.log.size

  -- Emblem-chain + exile-path `coDepartingIds`: `srcB` -> `.fraEmblem embChain` -> `.whileInZone embChain .command` on `coEqC`:
  let gP3Gone2 := mustApply g4 p3 .concede
  let anchorBDef : CardDef := { name := "P45i2 SrcHost", types := #[.creature], power := some 2, toughness := some 2 }
  let gChain0 :=
    insertObject
      (addPermanent (addPermanent gP3Gone2 anchorBDef p0 p3) eqDef2 p0 p3)
      embDef2 p0 .command (some p0)
  let srcB := (gChain0.objects.filter (fun o => o.zone == .battlefield && o.name == anchorBDef.name))[0]!
  let coEqC := (gChain0.objects.filter (fun o => o.zone == .battlefield && o.name == eqDef2.name))[0]!
  let embChain := (gChain0.objects.filter (·.zone == .command))[0]!
  let gChain1 :=
    (((((gChain0.createEffect
        (.layered (.objects #[srcB.id]) (.control p0) .untilEndOfTurn)
        (cause := some testCause)).createEffect
        (.gameRule (.fraEmblem embChain.id) (.whileSourceOnBattlefield srcB.id))
        (cause := some testCause)).createEffect
        (.layered (.objects #[coEqC.id]) (.control p0) (.whileInZone embChain.id .command))
        (cause := some testCause)).record
        (GameEvent.attached gChain0.turnNumber (gChain0.snapshot coEqC) srcB.id (cause := testCause))).createEffect
        (.layered (.objects #[coEqC.id]) (.copy hero) (.whileSourceOnBattlefield srcB.id))
        (cause := some testCause))
  let preChainLog := gChain1.log.size
  let gChainAfter := gChain1.clearEOT
  let chainLogs := gChainAfter.log.extract preChainLog gChainAfter.log.size

  let item2bOk :=
    mustHold45i2 "2b_i"
      (match cfEmbCeasedPos?, cfCtrlExpPos? with | some cIdx, some eIdx => cIdx < eIdx | _, _ => false) &&
    mustHold45i2 "2b_ii"
      (pnLogs.any (· == s!"{maskedEmbDef2.name} ends") &&
       !pnLogs.any (· == s!"{embDef2.name} ends")) &&
    mustHold45i2 "2b_iii"
      ((gChainAfter.followMovedToZone? srcB.id (· == .exile)).isSome &&
       (gChainAfter.followMovedToZone? coEqC.id (· == .exile)).isSome &&
       !chainLogs.any (fun s => s.contains "is no longer a copy") &&
       !chainLogs.any (fun s => s.contains "becomes unattached"))

  -- 2c. Owned-not-controlled `.command` emblem departure + CR 506.4 / CR 701.54a cease-pass reconciliation,
  --     CR 114.3 `"Elspeth emblem"`, and non-expired multi-entry `.playFromExile` permissions:
  let gOwnCmd0 :=
    insertObject (addPermanent g4 bear p1 p1) embDef2 p2 .command (some p0)
  let ringAtkBear := (gOwnCmd0.permanentsOf p1)[0]!
  let ownEmb := (gOwnCmd0.objects.filter (·.zone == .command))[0]!
  let gOwnCmd1 :=
    (((gOwnCmd0.createEffect
      (.layered (.objects #[ringAtkBear.id]) (.control p0) (.whileInZone ownEmb.id .command))
      (cause := some testCause)).record
      (GameEvent.attacked gOwnCmd0.turnNumber p0 (gOwnCmd0.snapshot ringAtkBear) p1)).record
      (GameEvent.ringTempted gOwnCmd0.turnNumber p0 (some ringAtkBear.id) 1 (cause := some testCause)))
  let gOwnCmdAfterP2 := mustApply gOwnCmd1 p2 .concede

  -- CR 114.3 `"Elspeth emblem"` (`types == #[]`):
  let gElsSrc := addPermanent g4 eqDef2 p0 p0
  let elspethAbSrc := (gElsSrc.permanentsOf p0).back!
  let (gEls0, _) :=
    gElsSrc.putStackAbility elspethAbSrc p0
      (abilityEffect := some { resolution := .frc .elspethEmblem, phrase := "You get an emblem." })
  let gElsResolved := mustApply (mustApply (mustApply (mustApply gEls0 p0 .pass) p1 .pass) p2 .pass) p3 .pass
  let elsEmb? := gElsResolved.objects.find? (fun o => o.zone == .command && o.name == "Elspeth emblem")

  -- Multi-entry `.playFromExile` (`p0` free `.untilNextTurnOf p0` + later `p1` non-free `.untilEndOfTurn`):
  let gMultiPerm0 := insertObject g4 bear p1 .exile
  let sharedExId := (gMultiPerm0.objects.filter (·.zone == .exile))[0]!.id
  let gMultiPerm1 :=
    ((gMultiPerm0.createEffect
      (.permission (some p0) (.playFromExile sharedExId { player := p0, withoutManaCost := true }) (.untilNextTurnOf p0))
      (cause := some testCause)).createEffect
      (.permission (some p1) (.playFromExile sharedExId { player := p1 }) .untilEndOfTurn)
      (cause := some testCause))
  let bothPlayersPermitted :=
    gMultiPerm1.mayPlayFromExile p0 (gMultiPerm1.object! sharedExId) &&
    gMultiPerm1.mayPlayFromExile p1 (gMultiPerm1.object! sharedExId) &&
    (gMultiPerm1.playPermissionFor? p0 (gMultiPerm1.object! sharedExId)).any (·.withoutManaCost) &&
    (gMultiPerm1.playPermissionFor? p1 (gMultiPerm1.object! sharedExId)).all (!·.withoutManaCost)
  let preEotPermLog := gMultiPerm1.log.size
  let gMultiPermAfterEot := gMultiPerm1.clearEOT
  let eotPermLogs := gMultiPermAfterEot.log.extract preEotPermLog gMultiPermAfterEot.log.size
  let preNextTurnPermLog := gMultiPermAfterEot.log.size
  let gMultiPermAllExpired := gMultiPermAfterEot.expireFraUntilTurnEffects p0
  let nextTurnPermLogs := gMultiPermAllExpired.log.extract preNextTurnPermLog gMultiPermAllExpired.log.size

  -- Off-zone `(g.findObject? id).isNone` fallback excludes `.expired` permission entries:
  let gOffPerm0 :=
    ((gMultiPerm0.createEffect
      (.permission (some p0) (.playFromExile sharedExId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)).clearEOT).createEffect
      (.permission (some p0) (.playFromExile sharedExId { player := p0, withoutManaCost := false }) (.untilNextTurnOf p0))
      (cause := some testCause)
  let (gOffPermMoved, _) := gOffPerm0.move sharedExId (.hand p1) none (cause := some testCause)

  let item2cOk :=
    (gOwnCmdAfterP2.findObject? ownEmb.id).isNone &&
    gOwnCmdAfterP2.controllerOf (gOwnCmdAfterP2.object! ringAtkBear.id) == some p1 &&
    !(gOwnCmdAfterP2.object! ringAtkBear.id).status.attacking &&
    (gOwnCmdAfterP2.player p0).ringBearerId == none &&
    elsEmb?.any (fun emb => emb.printed.types.isEmpty && !Game.representedByCard emb) &&
    bothPlayersPermitted &&
    gMultiPermAfterEot.mayPlayFromExile p0 (gMultiPermAfterEot.object! sharedExId) &&
    !gMultiPermAfterEot.mayPlayFromExile p1 (gMultiPermAfterEot.object! sharedExId) &&
    !eotPermLogs.any (· == s!"{bear.name} can no longer be played from exile") &&
    nextTurnPermLogs.any (· == s!"{bear.name} can no longer be played from exile") &&
    (gOffPermMoved.playPermissionEntriesOf sharedExId).size == 1 &&
    (gOffPermMoved.playPermissionEntriesOf sharedExId).all (fun (_, _, perm, _) => !perm.withoutManaCost)

  mustHold45i2 "2a.seatsExtraAndBackToBack2hg" item2aOk &&
  mustHold45i2 "2b.ceaseFirstEmblemAndCoDepartingChain" item2bOk &&
  mustHold45i2 "2c.ownedCommandElspethAndMultiPlayPerm" item2cOk &&
  mustHold45i2 "2.replay"
    (replayOk45i2 #[gAtTeamC, gBackExtra, gCeaseFirstAfter, gPreNameAfter, gChainAfter,
      gOwnCmdAfterP2, gElsResolved, gMultiPermAllExpired, gOffPermMoved])

end Phase45Item2EventAlignment

section Phase45Item3EventAlignment

private def mustHold45i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase45Item3EventAlignment failed: {label}"

private def replayOk45i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 3a. `Core.isInitialMaterialize`:
  --     (i) unmaterialized ETB replacement lookahead `ReplacementId.object` (`⟨99999⟩`) does NOT poison later `addPermanent`;
  --     (ii) `.payWard` `.sacrificePermanents` `chosen`, `.surveilMoveLoop` `remainingGy`, and `PendingReplacement` `gameChangeMaxTs`:
  let lookRid : ReplacementId := { kind := .entersWithExtraCounters, object := some ⟨99999⟩ }
  let gLook0 :=
    g3.changes #[
      .replacementOrder #[lookRid],
      .pending (.chooseReplacement p0 #[lookRid]),
      .pending .none,
      .replacementOrder #[] ]
  let preLookIdx := gLook0.events.size
  let gLook1 := addPermanent gLook0 bear p0 p0
  let freshAfterLookId := (gLook1.permanentsOf p0)[0]!.id

  let gWardRef0 := quiet (addPermanent g3 bear p0 p0)
  let wardObj := (gWardRef0.permanentsOf p0)[0]!
  let gWardRef1 :=
    (gWardRef0.changes #[
      .pending (.payWard p0 ⟨1⟩ (.sacrificePermanents 1 1 #[wardObj.id])),
      .pending .none ]).change (.materializeObject wardObj)

  let gSurvRef0 := quiet g3
  let survLibId := (gSurvRef0.player p0).library[0]!
  let survLibObj := gSurvRef0.object! survLibId
  let gSurvRef1 :=
    (gSurvRef0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.surveilMoveLoop p0 #[survLibId] (some testCause))),
      .pendingReplacement none ]).change (.materializeObject survLibObj)

  let gMaxTs0 := quiet (addPermanent g3 bear p0 p0)
  let tsPerm := (gMaxTs0.permanentsOf p0)[0]!
  let hiTsSnapObj : GameObject := {
    id := ⟨1⟩, printed := bear, owner := p0, zone := .battlefield, timestamp := tsPerm.timestamp + 500
  }
  let gMaxTs1 :=
    (gMaxTs0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.destroyPermanent ⟨1⟩ (some testCause) (some #[hiTsSnapObj]))),
      .pendingReplacement none ]).change (.materializeObject tsPerm)

  let item3aOk :=
    gLook1.objectZoneAndPhasedOutAt? freshAfterLookId preLookIdx == none &&
    gWardRef1.objectZoneAndPhasedOutAt? wardObj.id 0 == some (.battlefield, false) &&
    gSurvRef1.objectZoneAndPhasedOutAt? survLibId 0 == some (.library p0, false) &&
    gMaxTs1.objectZoneAndPhasedOutAt? tsPerm.id 0 == some (.battlefield, false)

  -- 3b. Post-`bound` `eventObjectIsLiveSubject` guards, `EventObject.defaultController` preservation,
  --     and `.created` / `missingObjs` `adjustTokenCardDef` & `toCardDef` parity:
  let (gDeadTok0, deadTok) := g3.createOneToken p0 bear (extraCounters := #[(.plusOnePlusOne, 3)]) (cause := some testCause)
  let deadSnapWithCounters := gDeadTok0.snapshot (gDeadTok0.object! deadTok.id)
  let gDeadTokGone := gDeadTok0.ceaseToExist deadTok.id (cause := some testCause)
  let deadBoundIdx := gDeadTokGone.events.size
  let gDeadTokPostTrig :=
    gDeadTokGone.record
      (GameEvent.rules gDeadTokGone.turnNumber
        (.triggerQueue (.triggered deadSnapWithCounters p0 default ⟨1⟩))
        testCause)

  -- `EventObject.defaultController` preserved across temporary `.control p1`:
  let gDefCtrl0 := addPermanent g3 bear p0 p0
  let dcBear := (gDefCtrl0.permanentsOf p0)[0]!
  let preCtrlEffIdx := gDefCtrl0.events.size
  let gDefCtrlStolen :=
    gDefCtrl0.createEffect (.layered (.objects #[dcBear.id]) (.control p1) .untilEndOfTurn)
      (cause := some testCause)
  let stolenSnap := gDefCtrlStolen.snapshot (gDefCtrlStolen.object! dcBear.id)
  let (gDefCtrlExiled, _) := gDefCtrlStolen.move dcBear.id .exile none (cause := some testCause)
  let gDefCtrlAfterEot := gDefCtrlExiled.clearEOT
  let lkiAfterEotObj := Game.damageSourceObjectFromLki stolenSnap
  let histAtPreCtrl := gDefCtrlAfterEot.mkHistoricalGameAt preCtrlEffIdx

  -- `.created` with non-token `bear` (`adjustTokenCardDef`) + `printed := none` `toCardDef` fallback:
  let (gTokCard0, tokFromBear) := g3.createOneToken p0 bear (cause := some testCause)
  let replayedTokCard := Game.replayEvents gTokCard0.events
  let synthId : ObjectId := ⟨gTokCard0.nextObjectId + 10⟩
  let synthEo : EventObject := {
    id := some synthId
    name := "P45i3 SynthSpirit"
    owner := p0
    controller := some p0
    defaultController := some p0
    zone := .battlefield
    token := true
    types := #[.creature]
    power := some 3
    toughness := some 3
    printed := none
  }
  let gSynthCreated :=
    gTokCard0.record (GameEvent.created gTokCard0.turnNumber p0 synthEo (cause := testCause))
  let postSynthCreateIdx := gSynthCreated.events.size
  let gSynthCeased := gSynthCreated.ceaseToExist synthId (cause := some testCause)
  let histAtSynth := gSynthCeased.mkHistoricalGameAt postSynthCreateIdx

  let item3bOk :=
    gDeadTokPostTrig.objectZoneAndPhasedOutAt? deadTok.id deadBoundIdx == none &&
    gDeadTokPostTrig.objectCounterCountAt deadTok.id .plusOnePlusOne deadBoundIdx == 0 &&
    ((gDeadTokPostTrig.mkHistoricalGameAt deadBoundIdx).findObject? deadTok.id).isNone &&
    stolenSnap.controller == some p1 &&
    stolenSnap.defaultController == some p0 &&
    lkiAfterEotObj.defaultController == some p0 &&
    gDefCtrlAfterEot.controllerOf lkiAfterEotObj == some p1 &&
    (histAtPreCtrl.findObject? dcBear.id).any (fun o => histAtPreCtrl.controllerOf o == some p0) &&
    (replayedTokCard.object! tokFromBear.id).printed.isToken &&
    (gTokCard0.mkHistoricalGameAt gTokCard0.events.size |>.object! tokFromBear.id).printed.isToken &&
    (histAtSynth.findObject? synthId).any (fun o =>
      o.name == "P45i3 SynthSpirit" && o.printed.isToken && histAtSynth.isCreature o)

  -- 3c. Batch-end `Phasing.phaseOutPermanentsLoop` CR 800.4c / CR 702.26b reconciliation,
  --     hoisted general `phaseOutBatchStartIdx` across non-phasing rules events,
  --     and pre-log `.powerUpsForbidden` + inverted `extraTurns` reconstruction:
  let gP2Gone3 := mustApply g3 p2 .concede
  let srcArtDef : CardDef := { name := "P45i3 Anchor", types := #[.artifact] }
  let gPhCo0 := addPermanent (addPermanent gP2Gone3 srcArtDef p0 p0) bear p0 p2
  let phAnchorA := (gPhCo0.permanentsOf p0).find? (·.name == srcArtDef.name) |>.get!
  let phDepB := (gPhCo0.objects.filter (fun o => o.zone == .battlefield && o.name == bear.name))[0]!
  let gPhCo1 :=
    gPhCo0.createEffect
      (.layered (.objects #[phDepB.id]) (.control p0) (.whileSourceOnBattlefield phAnchorA.id))
      (cause := some testCause)
  -- Simultaneous phase-out of `[phAnchorA, phDepB]`: both stay phased out on `.battlefield`!
  let gPhBothOut :=
    gPhCo1.phaseOutPermanents #[gPhCo1.object! phAnchorA.id, gPhCo1.object! phDepB.id] (cause := some testCause)
  -- Also if `phDepB` is ALREADY phased out and `phAnchorA` leaves `.battlefield`, CR 702.26b keeps `phDepB` phased out!
  let gPhAlreadyB := gPhCo1.phaseOut (gPhCo1.object! phDepB.id) (cause := some testCause)
  let (gPhAfterAnchorExile, _) := gPhAlreadyB.move phAnchorA.id .exile none (cause := some testCause)

  -- Hoisted `phaseOutBatchStartIdx` stepping back across an earlier same-batch `.continuousEffect (.expired ..)` event:
  let gBatchIdx0 := addPermanent g3 bear p1 p1
  let biStolen := (gBatchIdx0.permanentsOf p1)[0]!
  let gBatchIdx1 :=
    gBatchIdx0.createEffect
      (.layered (.objects #[biStolen.id]) (.control p0) .untilEndOfTurn)
      (cause := some testCause)
  let ctrlEid := gBatchIdx1.activeEffects.back!.1
  let gBatchIdxOut :=
    gBatchIdx1.withBatch (some testCause) fun g =>
      let g := g.expireEffectById ctrlEid (reconcileControl := false) (cause := some testCause)
      g.phaseOut (g.object! biStolen.id) (cause := some testCause) (reconcile := false)
  let gBatchIdxAfterP1 := gBatchIdxOut.phaseInControlled p1
  let gBatchIdxAfterP0 := gBatchIdxAfterP1.phaseInControlled p0

  -- Pre-log `.powerUpsForbidden` solo extra turn + inverted `.extraTurnAdded`:
  let gSoloEx0 := addPermanent gP2Gone3 bear p0 p0
  let soloPhId := (gSoloEx0.permanentsOf p0)[0]!.id
  let gSoloEx1 :=
    ((gSoloEx0.createEffect (.layered (.objects #[soloPhId]) (.control p2) .indefinite)
        (cause := some testCause)).phaseOut (gSoloEx0.object! soloPhId) (cause := some testCause)).record
      (GameEvent.extraTurnAdded gSoloEx0.turnNumber p1 (cause := testCause))
  -- Advance onto `p1`'s extra turn (`lastRegularTurnSeat == p0`, `powerUpsForbidden == true`, `extraTurns == #[]`):
  let gInP1SoloExtra := gSoloEx1.startNextTurnAndBegin
  -- Wipe pre-log events (`quiet`), add an extra turn for `p0` post-`quiet`, then end `p1`'s pre-log extra turn ->
  -- `p0` takes the post-`quiet` extra turn while `soloPhId` (`p2`-controlled) stays phased out because `p1`'s turn was EXTRA!
  let gQuietPreExtra :=
    (((quiet gInP1SoloExtra).record (GameEvent.stepBegan gInP1SoloExtra.turnNumber .precombatMain p1)).record
      (GameEvent.extraTurnAdded gInP1SoloExtra.turnNumber p0 (cause := testCause))).startNextTurnAndBegin
  -- After `p0`'s extra turn ends, regular turns resume from `lastRegularTurnSeat == p0` -> `p1`'s REGULAR turn!
  let gAfterP0ExtraToP1Reg := gQuietPreExtra.startNextTurnAndBegin
  -- After `p1`'s regular turn ends, `p1 -> p2 (departed!) -> p0` phases in `soloPhId`!
  let gAfterP1RegToP0 := gAfterP0ExtraToP1Reg.startNextTurnAndBegin

  let item3cOk :=
    (gPhBothOut.object! phAnchorA.id).status.phasedOut &&
    (gPhBothOut.object! phDepB.id).zone == .battlefield &&
    (gPhBothOut.object! phDepB.id).status.phasedOut &&
    (gPhAfterAnchorExile.object! phDepB.id).zone == .battlefield &&
    (gPhAfterAnchorExile.object! phDepB.id).status.phasedOut &&
    (gBatchIdxAfterP1.object! biStolen.id).status.phasedOut &&
    !(gBatchIdxAfterP0.object! biStolen.id).status.phasedOut &&
    gQuietPreExtra.activePlayer == p0 &&
    (gQuietPreExtra.object! soloPhId).status.phasedOut &&
    gAfterP0ExtraToP1Reg.activePlayer == p1 &&
    (gAfterP0ExtraToP1Reg.object! soloPhId).status.phasedOut &&
    gAfterP1RegToP0.activePlayer == p0 &&
    !(gAfterP1RegToP0.object! soloPhId).status.phasedOut

  mustHold45i3 "3a.isInitialMaterializeLookaheadAndPayloads" item3aOk &&
  mustHold45i3 "3b.liveSubjectDefaultCtrlAndCreatedToken" item3bOk &&
  mustHold45i3 "3c.batchEndPhasingAndPreLogExtraTurns" item3cOk &&
  mustHold45i3 "3.replay"
    (replayOk45i3 #[gLook1, gDeadTokPostTrig, gDefCtrlAfterEot, gTokCard0, gSynthCeased,
      gPhBothOut, gPhAfterAnchorExile, gBatchIdxAfterP0, gInP1SoloExtra])

end Phase45Item3EventAlignment

section Phase45Item4EventAlignment

private def mustHold45i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase45Item4EventAlignment failed: {label}"

private def replayOk45i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 4a. CR 601.2h `Casting.preferredManaTap` tap-cost reservation & CR 302.6 live tap-mana partitioning:
  let dork22Def : CardDef := {
    creature "P45i4 ElfDork" ManaCost.empty #["Elf", "Druid"] 2 2 with
    tapAddMana := #[.colored .green]
  }
  let crew1ManaVehDef : CardDef := {
    name := "P45i4 ManaSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    activatedAbilities := #[
      { cost := { mana := ManaCost.ofGeneric 1, fra := .crew 2 }, effect := Effect.gainLife 2 },
      { cost := { fra := .crew 2 }, effect := Effect.gainLife 1 }
    ]
  }
  -- `dork22Def` added BEFORE `forest` (`dork22Def` is first in `manaSourcesForProposed`, and SOLE crew-2 pilot):
  -- `preferredManaTap` / `Agent.choose` MUST tap `forest` so `dork22Def` remains untapped for `Crew 2`!
  let gPref0 := addPermanent (addPermanent (addPermanent g3 crew1ManaVehDef p0 p0) dork22Def p0 p0) forest p0 p0
  let prefVehId := (gPref0.permanentsOf p0).find? (·.name == crew1ManaVehDef.name) |>.get!.id
  let prefDorkId := (gPref0.permanentsOf p0).find? (·.name == dork22Def.name) |>.get!.id
  let prefForestId := (gPref0.permanentsOf p0).find? (·.name == forest.name) |>.get!.id
  let gPrefProp := mustApply gPref0 p0 (.activate prefVehId 0)
  let agentPreservesPilot :=
    match Agent.choose gPrefProp p0 with
    | some (.tapForMana id (.colored .green)) => id == prefForestId
    | _ => false
  let gPrefDone :=
    mustApply
      (mustApply (mustApply gPrefProp p0 (.tapForMana prefForestId (.colored .green))) p0 .pay)
      p0 (.choosePermanents #[prefDorkId])

  -- Summoning-sick `dork22Def` (`!canTapForPlainMana`) prioritized ahead of live `dork22Def` (`canTapForPlainMana`) for `Crew 2`:
  let gSickPart0 := addSickPermanent (addPermanent (addPermanent g3 crew1ManaVehDef p0 p0) dork22Def p0 p0) dork22Def p0 p0
  let spVehId := (gSickPart0.permanentsOf p0).find? (·.name == crew1ManaVehDef.name) |>.get!.id
  let spDorks := (gSickPart0.permanentsOf p0).filter (·.name == dork22Def.name)
  let liveDork := spDorks[0]!
  let sickDork := spDorks[1]!
  let gSickCrewProp := mustApply gSickPart0 p0 (.activate spVehId 1)
  let defaultPicksSickDork :=
    match gSickCrewProp.defaultFraAction p0 (.crew gSickCrewProp.proposedSpell.get!.spellId spVehId 2) with
    | .choosePermanents ids => ids == #[sickDork.id]
    | _ => false
  let gSickCrewDone := mustApply gSickCrewProp p0 (.choosePermanents #[sickDork.id])

  -- Under-powered (`1/1` for `Crew 2`) and under-sized (`1` artifact for `.tapTwoUntappedArtifacts`) rejected by `Agent.chooseActivate`:
  let tiny11Def : CardDef := creature "P45i4 Tiny11" ManaCost.empty #["Scout"] 1 1
  let tapTwoArtDef : CardDef := {
    name := "P45i4 TwoArtEngine"
    types := #[.enchantment]
    activatedAbilities := #[
      { cost := { fra := .tapTwoUntappedArtifacts }, effect := Effect.gainLife 2 }
    ]
  }
  let loneArtDef : CardDef := { name := "P45i4 LoneCog", types := #[.artifact] }
  let gUnderCrew := mustApply (mustApply (addPermanent (addPermanent g3 crew1ManaVehDef p0 p0) tiny11Def p0 p0) p0 .pass) p1 .pass
  let gUnderTapTwo := mustApply (mustApply (addPermanent (addPermanent g3 tapTwoArtDef p0 p0) loneArtDef p0 p0) p0 .pass) p1 .pass
  let underRejected :=
    (match Agent.choose gUnderCrew p0 with | some (.activate _ _) => false | _ => true) &&
    (match Agent.choose gUnderTapTwo p0 with | some (.activate _ _) => false | _ => true)

  let item4aOk :=
    agentPreservesPilot &&
    gPrefDone.stack.size == 1 &&
    gSickPart0.canTapForPlainMana p0 liveDork &&
    !gSickPart0.canTapForPlainMana p0 sickDork &&
    defaultPicksSickDork &&
    gSickCrewDone.stack.size == 1 &&
    underRejected

  -- 4b. Stack-resolved permanent & stack-copy `Event.castEventBound == 0`,
  --     nested mana `targetProposalCheckpoint?`, and nested-stack `.clearProposalCheckpoint` abort cleanup:
  let treasureTokDef4 : CardDef := {
    name := "Treasure"
    types := #[.artifact]
    subtypes := #["Treasure"]
    isToken := true
    activatedAbilities := #[{
      cost := { tap := true, sacrificeSource := true }
      effect := { resolution := .addMana #[.colorless], phrase := "Add {C}." }
    }]
  }
  let morphDef4 : CardDef := { bear with name := "P45i4 MorphBear", morph := some (ManaCost.ofGeneric 1) }
  let gMorphCast0 :=
    ((insertObject (addPermanent (addPermanent g3 treasureTokDef4 p0 p0) treasureTokDef4 p0 p0)
        morphDef4 p0 (.hand p0)).addMana p0 .colorless 2)
  let trs4 := (gMorphCast0.permanentsOf p0).filter (·.name == treasureTokDef4.name)
  let handMorphId := (gMorphCast0.player p0).hand.back!
  -- Cast `morphDef4` face-down spending Treasure #0 (`{3}` morph cast cost = `{2}` in pool + `{C}` from Treasure #0):
  let gMorphCast1 := mustApply (mustApply gMorphCast0 p0 (.cast handMorphId)) p0 (.announceKicker true)
  let stackMorphId := gMorphCast1.proposedSpell.get!.spellId
  let gMorphCast2 : Game :=
    match gMorphCast1.activateManaAbility p0 trs4[0]!.id 0 #[.colorless] with
    | .ok g => g
    | .error e => panic! e
  let gMorphOnStack := mustApply gMorphCast2 p0 .pay
  let gMorphResolved := mustApply (mustApply (mustApply gMorphOnStack p0 .pass) p1 .pass) p2 .pass
  let bfMorphObj := (gMorphResolved.permanentsOf p0).find? (·.status.faceDown) |>.get!
  -- Copy a spell on the stack (`StackObjectEvent.copied`) -> `castEventBound == 0`:
  let copySnapEo : EventObject := {
    id := some ⟨gMorphResolved.nextObjectId + 20⟩
    name := shock.name, owner := p0, controller := some p0, zone := .stack
    isCopy := true, types := #[.instant], printed := some shock
  }
  let gWithStackCopy :=
    gMorphResolved.record
      (GameEvent.rules gMorphResolved.turnNumber
        (.stackObject (.copied stackMorphId copySnapEo p0))
        testCause)

  -- Nested mana `targetProposalCheckpoint?` & nested-stack no-rewind abort cleanup + third-party `rewindAbortedProp`:
  let sacSelfAbDef : CardDef := {
    name := "P45i4 SacPod"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := { mana := ManaCost.ofGeneric 1 }, effect := Effect.gainLife 2 }
    ]
  }
  let pickManaDef : CardDef := {
    name := "P45i4 SacOtherMana"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := { sacrificeAnotherCreatureOrArtifact := true }
        effect := { resolution := .addMana #[.colorless], phrase := "Add {C}." } }
    ]
  }
  let gNested0 := addPermanent (addPermanent (addPermanent g3 sacSelfAbDef p0 p0) pickManaDef p0 p0) bear p0 p0
  let sacPodId := (gNested0.permanentsOf p0).find? (·.name == sacSelfAbDef.name) |>.get!.id
  let pickManaId := (gNested0.permanentsOf p0).find? (·.name == pickManaDef.name) |>.get!.id
  let gNestedOuter := mustApply gNested0 p0 (.activate sacPodId 0)
  let outerCkptEvSize := (gNestedOuter.proposalCheckpoint.map (·.eventsSize)).getD 999999
  let (gNestedSacMoved, _) :=
    gNestedOuter.move sacPodId (.graveyard p0) none (verb := some .sacrifice)
      (actor := some p0) (cause := some (.costPayment .sacrifice p0 (some pickManaId)))
  let gNestedManaOpen :=
    gNestedSacMoved.changes #[
      .saveProposalCheckpoint,
      .beginProposalAction (.manaAbility (some pickManaId)) ]
  let nestedUsesOuterCkpt :=
    gNestedManaOpen.isNestedManaProposalCheckpoint &&
    (gNestedManaOpen.targetProposalCheckpoint?.map (·.eventsSize)) == some outerCkptEvSize &&
    gNestedManaOpen.sourceRemovedByCostSince p0 sacPodId outerCkptEvSize &&
    gNestedManaOpen.sourceStillPayable gNestedManaOpen.proposedSpell.get!
  let gNestedAbortedByP0 := mustApply gNestedManaOpen p0 .concede

  -- Third-party `p2` departure while `p0` is at `.chooseAdditionalCost p0` (formerly shadowed `clearProp` arm):
  let altSacSpellDef : CardDef := {
    name := "P45i4 AltCostBolt"
    manaCost := ManaCost.ofColor .red
    types := #[.sorcery]
    additionalCostSacrificeArtifactOrCreature := true
    additionalCostOrPayGeneric := some 2
    spellEffect := some { resolution := .gainLife 2, phrase := "Gain 2 life." }
  }
  let gAltRew00 := insertObject (addPermanent g3 bear p0 p0) altSacSpellDef p2 .exile
  let altExId := (gAltRew00.objects.filter (·.zone == .exile))[0]!.id
  let gAltRew0 :=
    gAltRew00.createEffect
      (.permission (some p0) (.playFromExile altExId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gAltProposed := mustApply gAltRew0 p0 (.cast altExId)
  let atChooseAltCost := gAltProposed.pending == .chooseAdditionalCost p0
  let gAltAfterP2 := mustApply gAltProposed p2 .concede

  let item4bOk :=
    mustHold45i4 "4b_i"
      (bfMorphObj.id != stackMorphId &&
       GameEvent.castEventBound gMorphResolved.events stackMorphId < gMorphResolved.events.size &&
       GameEvent.castEventBound gMorphResolved.events bfMorphObj.id == 0 &&
       GameEvent.castEventBound gWithStackCopy.events copySnapEo.id.get! == 0) &&
    mustHold45i4 "4b_ii"
      (nestedUsesOuterCkpt &&
       gNestedAbortedByP0.proposalCheckpoint.isNone &&
       gNestedAbortedByP0.outerProposalCheckpoints.isEmpty) &&
    mustHold45i4 "4b_iii"
      (atChooseAltCost &&
       gAltAfterP2.proposedSpell.isNone &&
       gAltAfterP2.proposalCheckpoint.isNone &&
       gAltAfterP2.stack.isEmpty)

  -- 4c. Disjoint combined activation costs (`needsSacrificeOther`, `.crew`, `.sacrificeEquipmentAttachedToSource`)
  --     and stack-resolved `ManaRestriction` parity in `EffectResolution`:
  let sacComboEnchDef : CardDef := {
    name := "P45i4 DoubleSacEnch"
    types := #[.enchantment]
    activatedAbilities := #[
      { cost := { sacrificeAnotherCreatureOrArtifact := true, sacrificeAnotherCreature := true }
        effect := Effect.gainLife 2 }
    ]
  }
  let gDoubleSacOne := addPermanent (addPermanent g3 sacComboEnchDef p0 p0) bear p0 p0
  let dsEnchObj1 := (gDoubleSacOne.permanentsOf p0).find? (·.name == sacComboEnchDef.name) |>.get!
  let oneCreatureRejected :=
    !gDoubleSacOne.canActivate p0 dsEnchObj1 dsEnchObj1.printed.activatedAbilities[0]! (idx? := some 0)
  let gDoubleSacTwo := addPermanent gDoubleSacOne hero p0 p0
  let dsEnchId := dsEnchObj1.id
  let dsBearId := (gDoubleSacTwo.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let dsHeroId := (gDoubleSacTwo.permanentsOf p0).find? (·.name == hero.name) |>.get!.id
  let gDsStep1 := mustApply (mustApply gDoubleSacTwo p0 (.activate dsEnchId 0)) p0 .pay
  let gDsStep2 := mustApply gDsStep1 p0 (.choosePermanents #[dsBearId])
  let gDsStep3 := mustApply gDsStep2 p0 (.sacrifice dsHeroId)

  -- `.crew 2` + `.tapUntappedCreature` joint satisfiability:
  let crewPlusTapVehDef : CardDef := {
    name := "P45i4 CrewTapSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    activatedAbilities := #[
      { cost := { tapAnUntappedCreatureYouControl := true, fra := .crew 2 }, effect := Effect.gainLife 2 }
    ]
  }
  let gCtOne := addPermanent (addPermanent g3 crewPlusTapVehDef p0 p0) bear p0 p0
  let ctVehObj1 := (gCtOne.permanentsOf p0).find? (·.name == crewPlusTapVehDef.name) |>.get!
  let onePilotCrewTapRejected :=
    !gCtOne.canActivate p0 ctVehObj1 ctVehObj1.printed.activatedAbilities[0]! (idx? := some 0)
  let gCtTwo := addPermanent gCtOne hero p0 p0
  let ctBearId := (gCtTwo.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let ctHeroId := (gCtTwo.permanentsOf p0).find? (·.name == hero.name) |>.get!.id
  let gCtDone :=
    mustApply
      (mustApply (mustApply gCtTwo p0 (.activate ctVehObj1.id 0)) p0 (.choosePermanents #[ctBearId]))
      p0 (.choosePermanents #[ctHeroId])

  -- `sacrificeEquipmentAttachedToSource`: `needsBattlefieldSource` reservation + `laterSacAttachedEquip` disjointness:
  let eqDef4 : CardDef := { name := "P45i4 Blade", types := #[.artifact], subtypes := #["Equipment"] }
  let armedArtHeroDef : CardDef := {
    name := "P45i4 ArmedConstruct"
    types := #[.artifact, .creature]
    power := some 2
    toughness := some 2
    staticAbilities := #[.fra .tapSacrificeAddThreeOfOneColor]
    activatedAbilities := #[
      { cost := { mana := ManaCost.ofGeneric 1, sacrificeEquipmentAttachedToSource := true }
        effect := Effect.gainLife 2 },
      { cost := { sacrificeEquipmentAttachedToSource := true, sacrificeArtifact := true }
        effect := Effect.gainLife 3 }
    ]
  }
  let gArmed00 := addPermanent (addPermanent g3 armedArtHeroDef p0 p0) eqDef4 p0 p0
  let armedObj0 := (gArmed00.permanentsOf p0).find? (·.name == armedArtHeroDef.name) |>.get!
  let bladeObj0 := (gArmed00.permanentsOf p0).find? (·.name == eqDef4.name) |>.get!
  let gArmed0 :=
    gArmed00.record (GameEvent.attached gArmed00.turnNumber (gArmed00.snapshot bladeObj0) armedObj0.id (cause := testCause))
  let gArmedManaProp := mustApply gArmed0 p0 (.activate armedObj0.id 0)
  let armedReservedAtMana :=
    gArmedManaProp.proposedNeedsBattlefieldSource gArmedManaProp.proposedSpell.get! &&
    (gArmedManaProp.activateManaAbility p0 armedObj0.id 0 #[.colored .red, .colored .red, .colored .red]).toOption.isNone
  let armedNoSpareRejected :=
    !gArmed0.canActivate p0 (gArmed0.object! armedObj0.id) armedArtHeroDef.activatedAbilities[1]! (idx? := some 1)
  let gArmedSpare := addPermanent gArmed0 loneArtDef p0 p0
  let spareId := (gArmedSpare.permanentsOf p0).find? (·.name == loneArtDef.name) |>.get!.id
  let gArmedAb1Step1 := mustApply gArmedSpare p0 (.activate armedObj0.id 1)
  let defaultPicksSpare :=
    match gArmedAb1Step1.defaultFraAction p0 (.costPicks armedObj0.id #[.sacrificeArtifact, .sacrificeEquipmentAttachedToSource] false) with
    | .choosePermanents ids => ids == #[spareId]
    | _ => false
  let gArmedAb1Done :=
    mustApply (mustApply gArmedAb1Step1 p0 (.choosePermanents #[spareId])) p0 (.choosePermanents #[bladeObj0.id])

  -- `Agent.choose` (`chooseActivate`) allows a lone 2/2 to satisfy both `.crew` and `sacrificeAnotherCreature`
  -- (CR 601.2h), while still rejecting non-disjoint `.crew` + `tapAnUntappedCreatureYouControl` on a lone 2/2:
  let crewSacVehDef : CardDef := {
    name := "P45i4 SacSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    activatedAbilities := #[{
      cost := { fra := .crew 2, sacrificeAnotherCreature := true }
      effect := Effect.gainLife 3
    }]
  }
  let crewTapVehDef : CardDef := {
    name := "P45i4 TapSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    activatedAbilities := #[{
      cost := { fra := .crew 2, tapAnUntappedCreatureYouControl := true }
      effect := Effect.gainLife 3
    }]
  }
  let gCrewSacOne :=
    mustApply (mustApply (mustApply (addPermanent (addPermanent g3 crewSacVehDef p0 p0) bear p0 p0) p0 .pass) p1 .pass) p2 .pass
  let crewSacVehId := (gCrewSacOne.permanentsOf p0).find? (·.name == crewSacVehDef.name) |>.get!.id
  let gCrewTapOne :=
    mustApply (mustApply (mustApply (addPermanent (addPermanent g3 crewTapVehDef p0 p0) bear p0 p0) p0 .pass) p1 .pass) p2 .pass
  let crewTapVehId := (gCrewTapOne.permanentsOf p0).find? (·.name == crewTapVehDef.name) |>.get!.id
  let gCrewTapTwo := addPermanent gCrewTapOne bear p0 p0
  let agentCrewSacDisjointOk :=
    (match Agent.choose gCrewSacOne p0 with | some (.activate id idx) => id == crewSacVehId && idx == 0 | _ => false) &&
    (match Agent.choose gCrewTapOne p0 with | some (.activate _ _) => false | _ => true) &&
    (match Agent.choose gCrewTapTwo p0 with | some (.activate id idx) => id == crewTapVehId && idx == 0 | _ => false)

  -- Stack-resolved `.addAnyColorSpendOnlyArtifactSpell` & `.addTwoAnyColorEquipment`:
  let anchor4 := (addPermanent g3 loneArtDef p0 p0).permanentsOf p0 |>.back!
  let (gArtMana0, _) :=
    (addPermanent g3 loneArtDef p0 p0).putStackAbility anchor4 p0
      (abilityEffect := some { resolution := .addAnyColorSpendOnlyArtifactSpell, phrase := "Add one mana for artifact spell." })
  let gArtManaRes := mustApply (mustApply (mustApply gArtMana0 p0 .pass) p1 .pass) p2 .pass
  let artPool := (gArtManaRes.player p0).manaPool
  let (gEqMana0, _) :=
    (addPermanent g3 loneArtDef p0 p0).putStackAbility anchor4 p0
      (abilityEffect := some { resolution := .addTwoAnyColorEquipment, phrase := "Add two mana for Equipment or equip." })
  let gEqManaRes := mustApply (mustApply (mustApply gEqMana0 p0 .pass) p1 .pass) p2 .pass
  let eqPool := (gEqManaRes.player p0).manaPool

  let item4cOk :=
    oneCreatureRejected &&
    gDsStep3.stack.size == 1 &&
    onePilotCrewTapRejected &&
    gCtDone.stack.size == 1 &&
    agentCrewSacDisjointOk &&
    armedReservedAtMana &&
    armedNoSpareRejected &&
    defaultPicksSpare &&
    gArmedAb1Done.stack.size == 1 &&
    artPool.fraRestricted == #[(.colored .white, .artifactSpell)] &&
    artPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, types := #[.artifact] }) &&
    !artPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, types := #[.creature] }) &&
    eqPool.fraRestricted == #[(.colored .white, .equipmentOrEquip), (.colored .white, .equipmentOrEquip)] &&
    eqPool.canPay (ManaCost.ofGeneric 2) (spend := { equip := true }) &&
    !eqPool.canPay (ManaCost.ofGeneric 2) (spend := { spell := true, types := #[.artifact] })

  mustHold45i4 "4a.preferredManaTapAndLiveSickPartition" item4aOk &&
  mustHold45i4 "4b.castEventBoundAndNestedCheckpoints" item4bOk &&
  mustHold45i4 "4c.disjointCombinedCostsAndStackManaRestr" item4cOk &&
  mustHold45i4 "4.replay"
    (replayOk45i4 #[gPrefDone, gSickCrewDone, gMorphResolved, gWithStackCopy,
      gNestedAbortedByP0, gAltAfterP2, gDsStep3, gCtDone, gArmedAb1Done, gArtManaRes, gEqManaRes])

end Phase45Item4EventAlignment

end Mtg.Engine.EventTests
