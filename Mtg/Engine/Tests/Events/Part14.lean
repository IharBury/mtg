import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase48Item1EventAlignment

private def mustHold48i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase48Item1EventAlignment failed: {label}"

private def replayOk48i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let zeroInstDef : CardDef := {
    name := "P48i1 ZeroBolt"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellEffect := some (Effect.gainLife 1)
  }
  let bigSorcDef : CardDef := {
    name := "P48i1 HugeSorc"
    manaCost := ManaCost.ofGeneric 6
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 1)
  }
  let legBearDef : CardDef := { bear with name := "P48i1 LegBear", supertypes := #[.legendary] }

  -- 1a(i). `Entering.completeActiveResolutions` preserves `continuations` when `mayThenResume`
  --        or `proposedSpell.isNone && (pendingMayCastFromExile.isSome || pendingFreeCopies.isSome)` holds:
  let gEx0 := insertObject g4 zeroInstDef p0 .exile
  let exCardId := (gEx0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let frameWithCtx : ContinuationFrame := { resolvingContext := some (none, p0) }
  let gMayThenHold :=
    (gEx0.changes #[.pushContinuationFrame frameWithCtx, .continuation (.mayThenResume true)]).completeActiveResolutions
  let gDefExHold :=
    (gEx0.changes #[
      .pushContinuationFrame frameWithCtx,
      .continuation (.pendingMayCastFromExile (some (p0, #[exCardId], 1))) ]).completeActiveResolutions
  let gDefCopyHold :=
    (gEx0.changes #[
      .pushContinuationFrame frameWithCtx,
      .continuation (.pendingFreeCopies (some (p0, #[exCardId], 3, 1))) ]).completeActiveResolutions

  -- 1a(ii). `Leaving.playerLeavesGameCore` `ensureDeferredExileReopen` when `!wasAbortedProposal`
  --         and outer continuation is non-`finishFraChoice` (`.receivePriority p0`):
  let gLeaveNonFra0 :=
    gEx0.changes #[
      .pushContinuationFrame {},
      .continuation (.pendingMayCastFromExile (some (p0, #[exCardId], 1))),
      .pendingReplacement (some (.receivePriority p0)),
      .pending (.mayPayGeneric p2 1) ]
  let gLeaveNonFraReopened := mustApply gLeaveNonFra0 p2 .concede

  -- 1a(iii). `finishAndGrantPriority`, `finishFraChoice`, `afterWardResolved`, `chooseReplacement`,
  --          `afterTriggerTargetsChosen`, and `receivePriority` reopen deferred exile/copy prompts
  --          AHEAD of `triggerNeedingTargets`, and cease uncast `pendingFreeCopies` (`castsLeft == 0`):
  let gAnchorBase := addPermanent gEx0 ({ name := "P48i1 Anchor", types := #[.artifact] }) p0 p0
  let tgtAnchor := (gAnchorBase.permanentsOf p0).back!
  let tgtTrigAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.gainLife .you)
      { targeting := .of .player, resolution? := some (.gainLife (.fixed 1)), phrase := "Target player gains 1 life." }
  let gExAndTrig :=
    gAnchorBase.putTriggeredAbilityOnStack p0 tgtAnchor tgtTrigAb "triggers" (eventCause := some testCause)

  -- `finishAndGrantPriority` & `finishFraChoice` reopen `pendingMayCastFromExile` BEFORE `triggerNeedingTargets`:
  let gFgpBeforeTrig :=
    (gExAndTrig.changes #[
      .pushContinuationFrame {},
      .continuation (.pendingMayCastFromExile (some (p0, #[exCardId], 1))) ]).finishAndGrantPriority p2
  let gFfcBeforeTrig :=
    (gExAndTrig.changes #[
      .pushContinuationFrame {},
      .continuation (.pendingMayCastFromExile (some (p0, #[exCardId], 1))) ]).finishFraChoice

  -- Exhausted `pendingFreeCopies` (`castsLeft == 0` or `budget < mv`) ceases copy in `receivePriority` AND THEN prompts trigger targets:
  let gCopyBase := insertObject gAnchorBase bigSorcDef p0 (.hand p0)
  let (gCopyEx0, copyExId) :=
    gCopyBase.move (gCopyBase.player p0).hand.back! .exile none (isCopy := some true) (cause := some testCause)
  let gCopyExAndTrig :=
    gCopyEx0.putTriggeredAbilityOnStack p0 tgtAnchor tgtTrigAb "triggers" (eventCause := some testCause)
  let gRecvCeaseThenTrig :=
    (gCopyExAndTrig.changes #[
      .pushContinuationFrame {},
      .continuation (.pendingFreeCopies (some (p0, #[copyExId], 0, 0))) ]).receivePriority p2

  -- `afterTriggerTargetsChosen` (`Action.target`) reopens `pendingMayCastFromExile`:
  let gTrigTargetReady := gExAndTrig.receivePriority p2
  let gAfterTrigTgtReopen :=
    mustApply
      (gTrigTargetReady.changes #[
        .pushContinuationFrame {},
        .continuation (.pendingMayCastFromExile (some (p0, #[exCardId], 1))) ])
      p0 (.target (.player p1))

  -- `afterWardResolved` (`Pending.payWard` declined) reopens `pendingMayCastFromExile`:
  let wardPermDef : CardDef := { bear with name := "P48i1 WardBear", keywords := #[.ward (CostSpec.ofGeneric 2)] }
  let tgtBoltDef : CardDef := {
    name := "P48i1 Bolt"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellEffect := some { targeting := .of .creature, resolution? := some (.gainLife (.fixed 1)), phrase := "Target creature." }
  }
  let gWard0 := insertObject (addPermanent gEx0 wardPermDef p1 p1) tgtBoltDef p0 (.hand p0)
  let wardCreatureId := (gWard0.permanentsOf p1)[0]!.id
  let gWardCast :=
    mustApply (mustApply gWard0 p0 (.cast (gWard0.player p0).hand.back!)) p0 (.target (.permanent wardCreatureId))
  let gWardTriggered := mustApply (mustApply (mustApply (mustApply gWardCast p0 .pass) p1 .pass) p2 .pass) p3 .pass
  let gWardAfterDecline :=
    mustApply
      (gWardTriggered.changes #[
        .pushContinuationFrame {},
        .continuation (.pendingMayCastFromExile (some (p0, #[exCardId], 1))) ])
      p0 .decline

  -- `chooseReplacement` with idle continuation reopens `pendingMayCastFromExile`:
  let oddEvenDef : CardDef := {
    name := "P48i1 OddStatue"
    types := #[.artifact]
    staticAbilities := #[.asEntersChooseOddEven]
  }
  let gRep0 := insertObject gEx0 oddEvenDef p0 (.hand p0)
  let (gRepPaused, _) := gRep0.putOntoBattlefield (gRep0.player p0).hand.back! p0 (cause := some testCause)
  let gRepReopened :=
    mustApply
      (gRepPaused.changes #[
        .pushContinuationFrame {},
        .continuation (.pendingMayCastFromExile (some (p0, #[exCardId], 1))) ])
      p0 (.chooseMode 0)

  -- 1a(iv). `afterWardResolved` with `triggerSequenceRest.isSome` + `pendingMayCastFromExile.isSome`
  --         reopens `.fraChoice` and parks `.afterWardResolved` on `outerPendingReplacements` instead of looping;
  --         `afterTriggerTargetsChosen` consumes only `.chooseTargets _` and defers reopen while `pending != .none || afterRandom != .none`:
  let trigSeqP0 : TriggerSequenceRest := {
    controller := p0
    ability := TriggeredAbility.mkTrigger .thisDies { resolution? := some (.gainLife (.fixed 4)), phrase := "You gain 4 life." }
    sourceId := some tgtAnchor.id
    sourceName := tgtAnchor.name
    steps := [.gainLife (.fixed 4)]
  }
  let gWardTrigSeqReopen :=
    mustApply
      (gWardTriggered.change (.pushContinuationFrame {
        triggerSequenceRest := some trigSeqP0
        pendingMayCastFromExile := some (p0, #[exCardId], 1)
      }))
      p0 .decline
  let gWardTrigSeqFinished := mustApply gWardTrigSeqReopen p0 .decline
  let gTrigKeepNonTargetPending :=
    (gEx0.changes #[
      .pushContinuationFrame { pendingMayCastFromExile := some (p0, #[exCardId], 1) },
      .pending (.mayPayGeneric p0 1) ]).afterTriggerTargetsChosen
  let gTrigKeepAfterRandom :=
    (gEx0.changes #[
      .pushContinuationFrame { pendingMayCastFromExile := some (p0, #[exCardId], 1) },
      .pending (.chooseTargets p0),
      .afterRandom (.gainLife p0 2) ]).afterTriggerTargetsChosen

  let item1aOk :=
    mustHold48i1 "1a_completeActiveResolutionsPreservesFrames"
      (gMayThenHold.continuations.size == 1 &&
       gDefExHold.continuations.size == 1 &&
       gDefCopyHold.continuations.size == 1) &&
    mustHold48i1 "1a_leaveNonFraReopen"
      (gLeaveNonFraReopened.pending == .fraChoice p0 (.mayCastUpToFromExile #[exCardId] 1) &&
       gLeaveNonFraReopened.pendingMayCastFromExile.isNone) &&
    mustHold48i1 "1a_reopenAheadOfTriggerTargetsAndCeaseCopies"
      (gFgpBeforeTrig.pending == .fraChoice p0 (.mayCastUpToFromExile #[exCardId] 1) &&
       gFgpBeforeTrig.pendingPriority == some p2 &&
       gFfcBeforeTrig.pending == .fraChoice p0 (.mayCastUpToFromExile #[exCardId] 1) &&
       (gRecvCeaseThenTrig.findObject? copyExId).isNone &&
       gRecvCeaseThenTrig.pending == .chooseTargets p0 &&
       gRecvCeaseThenTrig.pendingPriority == some p2 &&
       gAfterTrigTgtReopen.pending == .fraChoice p0 (.mayCastUpToFromExile #[exCardId] 1) &&
       gWardAfterDecline.pending == .fraChoice p0 (.mayCastUpToFromExile #[exCardId] 1) &&
       gRepReopened.pending == .fraChoice p0 (.mayCastUpToFromExile #[exCardId] 1)) &&
    mustHold48i1 "1a_wardTrigSeqReopenAndAfterTrigIdleGuard"
      (gWardTrigSeqReopen.pending == .fraChoice p0 (.mayCastUpToFromExile #[exCardId] 1) &&
       gWardTrigSeqReopen.pendingMayCastFromExile.isNone &&
       gWardTrigSeqReopen.triggerSequenceRest.isSome &&
       gWardTrigSeqReopen.outerPendingReplacements == #[.afterWardResolved] &&
       gWardTrigSeqFinished.pending == .none &&
       (gWardTrigSeqFinished.player p0).life == 24 &&
       gTrigKeepNonTargetPending.pending == .mayPayGeneric p0 1 &&
       gTrigKeepNonTargetPending.pendingMayCastFromExile.isSome &&
       gTrigKeepAfterRandom.pending == .none &&
       gTrigKeepAfterRandom.afterRandom == .gainLife p0 2 &&
       gTrigKeepAfterRandom.pendingMayCastFromExile.isSome)

  -- 1b. `StateBasedActions` `checkSBACounted` / `rewriteRepausedPostCloseBatch` `foldTail`
  --     (`s0.isSome && savedIn.isSome && !po0 && !popOuter`) & `Event` `wasAssigningCombatDamage` guards:
  let gLegBase := addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0
  let legIds := ((gLegBase.permanentsOf p0).filter (·.name == legBearDef.name)).map (·.id)
  -- `checkSBACounted` (not `checkSBACountedWithLeaves`) with `savedIn := some (.mayPayGeneric p0 4)` and
  -- queued `.seq (.leavePlayersWhoLost (some (.mayPayGeneric p0 2)) false #[p2] none) (.gainLife p0 9 (some testCause))`:
  let gSbaFold0 :=
    ((gLegBase.record (GameEvent.playerLost gLegBase.turnNumber p2 .lifeZeroOrLess)).record
      (GameEvent.playerLost gLegBase.turnNumber p3 .lifeZeroOrLess)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement
        (some (.seq .checkSBA
                    (.seq (.leavePlayersWhoLost (some (.mayPayGeneric p0 2)) false #[p2] none)
                          (.gainLife p0 9 (some testCause))))) ]
  let (gSbaFold1, _) :=
    gSbaFold0.checkSBACounted (savedIn := some (.mayPayGeneric p0 4)) (departedIn := #[p3])
  let gSbaFoldStep1 := mustApply gSbaFold1 p0 (.keepLegend legIds[0]!)
  let gSbaFoldStep2 := mustApply gSbaFoldStep1 p0 .decline
  let gSbaFoldDone := mustApply gSbaFoldStep2 p0 .decline

  -- Pushed-outer (`!flushedFromPending`) `rewriteRepausedPostCloseBatch` with `savedIn := none` and `popOuterIn := true`
  -- folds `outerTail?` onto `outerPendingReplacements` (`poM == true`) for `.leavePlayersWhoLost none false`, `.checkSBA`, and plain tails:
  let legHero48Def : CardDef := { hero with supertypes := #[.legendary] }
  let gTwoGrp48Base :=
    addPermanent
      (addPermanent gLegBase legHero48Def p0 p0)
      legHero48Def p0 p0
  let gTwoGrp48Paused := gTwoGrp48Base.checkSBA
  let firstGrp48Ids :=
    match gTwoGrp48Paused.pending with | .chooseLegend _ _ ids => ids | _ => #[]
  let closeOnly48 :=
    match gTwoGrp48Paused.pendingReplacement with | some (.seq cb _) => cb | _ => .checkSBA
  let mkPushedOuterRepauseInv (afterClose : PendingReplacement) : Game :=
    let (gInv, _) :=
      (gTwoGrp48Paused.changes #[
        .pendingReplacement none,
        .pushContinuationFrame {},
        .pushOuterPendingReplacement (.seq closeOnly48 afterClose)
      ]).move firstGrp48Ids[0]! .exile none (cause := some testCause)
    gInv
  let gRepOuterLeaveInv :=
    mkPushedOuterRepauseInv
      (.seq (.leavePlayersWhoLost none false #[p2] none) (.gainLife p0 5 (some testCause)))
  let (gRepOuterLeaveMid, repOuterLeaveDid, _, repOuterLeavePop, repOuterLeaveDep, _) :=
    gRepOuterLeaveInv.checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := true) (departedIn := #[]) (deferRestore := false)
  let secondKeep48Id :=
    match gRepOuterLeaveMid.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999999⟩
  let gRepOuterLeaveDone := mustApply gRepOuterLeaveMid p0 (.keepLegend secondKeep48Id)

  let gRepOuterSbaInv :=
    mkPushedOuterRepauseInv (.seq .checkSBA (.gainLife p0 6 (some testCause)))
  let (gRepOuterSbaMid, repOuterSbaDid, _, repOuterSbaPop, _, _) :=
    gRepOuterSbaInv.checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := true) (departedIn := #[]) (deferRestore := false)
  let gRepOuterSbaDone := mustApply gRepOuterSbaMid p0 (.keepLegend secondKeep48Id)

  let gRepOuterPlainInv :=
    mkPushedOuterRepauseInv (.gainLife p0 8 (some testCause))
  let (gRepOuterPlainMid, repOuterPlainDid, _, repOuterPlainPop, _, _) :=
    gRepOuterPlainInv.checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := true) (departedIn := #[p2]) (deferRestore := false)
  let gRepOuterPlainDone := mustApply gRepOuterPlainMid p0 (.keepLegend secondKeep48Id)

  -- Post-flush peel in `checkSBACountedWithLeavesCore` (`shouldFlush && currentBatch.isNone`) with `popOuterIn := false` and `savedIn := none`
  -- keeps tails sequenced on `pendingReplacement` (`popOuter == false`, `outerPendingReplacements.isEmpty`) for `.leavePlayersWhoLost none false`, `.checkSBA`, and plain `some pr`:
  let mkStaleLegendFlush (pr : PendingReplacement) : Game :=
    g4.changes #[
      .pending (.chooseLegend p0 "Stale48" #[⟨999998⟩]),
      .pushContinuationFrame {},
      .pendingReplacement (some pr) ]
  let (gFlushLeaveNoFold, _, _, flushLeavePop, flushLeaveDep, _) :=
    (mkStaleLegendFlush
      (.seq (.leavePlayersWhoLost none false #[p2] none) (.gainLife p0 5 (some testCause)))).checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := false) (departedIn := #[]) (deferRestore := false)
  let (gFlushSbaNoFold, _, _, flushSbaPop, _, _) :=
    (mkStaleLegendFlush (.seq .checkSBA (.gainLife p0 6 (some testCause)))).checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := false) (departedIn := #[]) (deferRestore := false)
  let (gFlushPlainNoFold, _, _, flushPlainPop, _, _) :=
    (mkStaleLegendFlush (.gainLife p0 8 (some testCause))).checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := false) (departedIn := #[p2]) (deferRestore := false)

  -- Combat-damage `wasAssigningCombatDamage := some true` does NOT report priority grant or clear `nextQueuedPending`:
  let fcCombat : PendingReplacement :=
    .finishConcede false none (some true) (some (.mayPayGeneric p0 1)) false #[] none
  let cplCombat : PendingReplacement :=
    .concedePlayersLoop #[p2] false false false none (some true) (some (.mayPayGeneric p0 1)) false #[] none
  let fcIdle : PendingReplacement :=
    .finishConcede false none none (some (.mayPayGeneric p0 1)) false #[] none
  let eventCombatGuardsOk :=
    !fcCombat.endsWithPriorityGrant false &&
    !fcCombat.endsWithNonProposalPriorityGrant &&
    PendingReplacement.nextQueuedPending true fcCombat &&
    !cplCombat.endsWithPriorityGrant false &&
    !cplCombat.endsWithNonProposalPriorityGrant &&
    PendingReplacement.nextQueuedPending true cplCombat &&
    fcIdle.endsWithPriorityGrant false &&
    fcIdle.endsWithNonProposalPriorityGrant &&
    !PendingReplacement.nextQueuedPending true fcIdle

  let item1bOk :=
    mustHold48i1 "1b_checkSBACountedFoldTail"
      (gSbaFoldStep1.pending == .mayPayGeneric p0 2 &&
       gSbaFoldStep2.pending == .mayPayGeneric p0 4 &&
       gSbaFoldDone.pending == .none &&
       (gSbaFoldDone.player p0).life == 29 &&
       (gSbaFoldDone.player p2).leftTheGame &&
       (gSbaFoldDone.player p3).leftTheGame) &&
    mustHold48i1 "1b_pushedOuterRepauseFoldTail"
      (repOuterLeaveDid && repOuterLeavePop && repOuterLeaveDep == #[p2] &&
       gRepOuterLeaveMid.outerPendingReplacements == #[.gainLife p0 5 (some testCause)] &&
       (gRepOuterLeaveDone.player p0).life == 25 &&
       repOuterSbaDid && repOuterSbaPop &&
       gRepOuterSbaMid.outerPendingReplacements == #[.gainLife p0 6 (some testCause)] &&
       (gRepOuterSbaDone.player p0).life == 26 &&
       repOuterPlainDid && repOuterPlainPop &&
       gRepOuterPlainMid.outerPendingReplacements == #[.gainLife p0 8 (some testCause)] &&
       (gRepOuterPlainDone.player p0).life == 28) &&
    mustHold48i1 "1b_flushPeelNoFoldWhenNoSavedOrPopOuter"
      (!flushLeavePop && flushLeaveDep == #[p2] &&
       gFlushLeaveNoFold.outerPendingReplacements.isEmpty &&
       gFlushLeaveNoFold.pendingReplacement == some (.gainLife p0 5 (some testCause)) &&
       !flushSbaPop &&
       gFlushSbaNoFold.outerPendingReplacements.isEmpty &&
       gFlushSbaNoFold.pendingReplacement == some (.gainLife p0 6 (some testCause)) &&
       !flushPlainPop &&
       gFlushPlainNoFold.outerPendingReplacements.isEmpty &&
       gFlushPlainNoFold.pendingReplacement == some (.gainLife p0 8 (some testCause))) &&
    mustHold48i1 "1b_eventCombatDamageGuards" eventCombatGuardsOk

  -- 1c(i). `Decisions` `.restorePending` outer-pop threading across nested `.restorePending _ true`
  --        and `.seq a b` (`continuationGrantsPriority`, `priorityRecipientOfContinuation?`,
  --        `stepCanReverseProposal`, and `resumePendingReplacement` `nextFollowedByFinishFra`):
  let sorc1Def : CardDef := {
    name := "P48i1 Sorc1"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 2)
  }
  let gUnpayable0 :=
    (insertObject (addPermanent (emptyHand g4 p0) forest p0 p0) sorc1Def p0 (.hand p0)).change
      (.pendingPriority (some p2))
  let tmpForestId := (gUnpayable0.permanentsOf p0)[0]!.id
  let gCastPaused := mustApply gUnpayable0 p0 (.cast (gUnpayable0.player p0).hand.back!)
  let (gNoForest, _) := gCastPaused.move tmpForestId .exile none (cause := some testCause)
  let gUnpayableProp := gNoForest.change (.pending .none)
  let revCostStep : PendingReplacement :=
    .finishPostStep (.resumeProposalCostAfterLeave p0 (.discardForAdditionalCost p0))
  let twoPopsOnly : PendingReplacement :=
    .seq (.restorePending .none true none #[] none)
         (.restorePending .none true none #[] none)
  -- Two nested `.restorePending .none true` popping `[.gainLife p0 1, .receivePriority p1]`:
  -- `continuationGrantsPriority` returns `true` and `priorityRecipientOfContinuation?` returns `some p1`!
  let gPopsGrantBase :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p1),
      .pushOuterPendingReplacement (.gainLife p0 1 (some testCause)) ]
  let nestedGrantsP1 := gPopsGrantBase.continuationGrantsPriority false twoPopsOnly
  let nestedRecip? :=
    gPopsGrantBase.priorityRecipientOfContinuation? false
      (.seq (.gainLife p0 1 (some testCause)) twoPopsOnly)
  -- Two nested `.restorePending .none true` popping `[.gainLife p0 1, revCostStep]`:
  -- `stepCanReverseProposal` tracks `outerDepth` (`2 -> 1 -> 0`) so `.seq` sees `revCostStep` and skips trailing `.gainLife p0 7`!
  let gNestedRestoreBase :=
    gUnpayableProp.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement revCostStep,
      .pushOuterPendingReplacement (.gainLife p0 1 (some testCause)) ]
  let gNestedRestoreResumed :=
    gNestedRestoreBase.resumePendingReplacement
      (.seq twoPopsOnly (.gainLife p0 7 (some testCause)))

  -- `nextFollowedByFinishFra`: `.seq revCostStep (.restorePending .none true none #[] none)` where outer top is `.finishFraChoice`
  -- reverses `gUnpayableProp` and grants `pendingPriority == p2` (whereas outer top `.receivePriority p3` grants `p3`):
  let gOuterFraResumed :=
    (gUnpayableProp.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement .finishFraChoice ]).resumePendingReplacement
      (.seq revCostStep (.restorePending .none true none #[] none))
  let gOuterP3Resumed :=
    (gUnpayableProp.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p3) ]).resumePendingReplacement
      (.seq revCostStep (.restorePending .none true none #[] none))

  -- 1c(ii). `drainProbeNonPriorityCont` `.closeBatch` + `.returnLinkedExileLoop` SBA prediction:
  --         At cleanup (`postSbaCleanup false`), if `pendingReplacement` holds `.returnLinkedExileLoop #[zeroToughId]`,
  --         the returned 0/0 creature triggers Pass-1 SBA in `postSbaCleanup`, granting priority to `activePlayer == p0`
  --         rather than advancing to `p1`'s turn!
  let zeroToughDef : CardDef := creature "P48i1 Germ" ManaCost.empty #["Germ"] 0 0
  let gGermEx0 :=
    (insertObject g4 zeroToughDef p0 .exile).record
      (GameEvent.stepBegan g4.turnNumber .cleanup p0 (cause := some testCause))
  let germExId := (gGermEx0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gProbeLinked :=
    gGermEx0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement
        (some (.seq (.returnLinkedExileLoop #[germExId] (some testCause))
                    .finishCleanupAfterClearEot)),
      .pending (.chooseReplacement p0 #[]) ]
  let gProbeEmptyLinked :=
    gGermEx0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some .finishCleanupAfterClearEot),
      .pending (.chooseReplacement p0 #[]) ]

  -- 1c(iii). `advanceProbeOnResume` walks non-pausing `.assignCombatDamage` outer pops AND departed
  --          `redirectPendingAfterLeave` `prior` continuations:
  let gAssignProbeBase :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)),
      .pushOuterPendingReplacement (.receivePriority p1),
      .pushOuterPendingReplacement (.restorePending .none true none #[] none) ]
  let assignThenPop : PendingReplacement :=
    .seq (.restorePending (.assignCombatDamage p0 true) true none #[] none)
         (.restorePending .none true none #[] none)
  let gDepPriorBase :=
    (mustApply g4 p2 .concede).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)) ]
  let depTargetThenComplete : PendingReplacement :=
    .seq (.restorePending (.chooseTargets p0) true none #[p2] none)
         (.completeActivation true false)

  let item1cOk :=
    mustHold48i1 "1c_nestedRestoreOuterPop"
      (nestedGrantsP1 &&
       nestedRecip? == some p1 &&
       gNestedRestoreResumed.proposedSpell.isNone &&
       (gNestedRestoreResumed.player p0).life == 20 &&
       gOuterFraResumed.proposedSpell.isNone &&
       gOuterFraResumed.priority == p2 &&
       gOuterP3Resumed.proposedSpell.isNone &&
       gOuterP3Resumed.priority == p3 &&
       !gAssignProbeBase.continuationGrantsPriority false assignThenPop &&
       !gDepPriorBase.continuationGrantsPriority false depTargetThenComplete) &&
    mustHold48i1 "1c_drainProbeLinkedExileSba"
      (gProbeLinked.firstContinuationPriorityGrant? == some (some p0) &&
       gProbeEmptyLinked.firstContinuationPriorityGrant? == some (some p1))

  mustHold48i1 "1a.completeActiveResAndDeferredReopen" item1aOk &&
  mustHold48i1 "1b.sbaFoldTailAndCombatGuards" item1bOk &&
  mustHold48i1 "1c.restoreOuterPopAndDrainProbeLinked" item1cOk &&
  mustHold48i1 "1.replay"
    (replayOk48i1 #[gMayThenHold, gDefExHold, gDefCopyHold, gLeaveNonFraReopened,
      gFgpBeforeTrig, gFfcBeforeTrig, gRecvCeaseThenTrig, gAfterTrigTgtReopen,
      gWardAfterDecline, gRepReopened, gWardTrigSeqFinished, gSbaFoldDone,
      gRepOuterLeaveDone, gRepOuterSbaDone, gRepOuterPlainDone,
      gNestedRestoreResumed, gOuterFraResumed, gOuterP3Resumed])

end Phase48Item1EventAlignment

section Phase48Item2EventAlignment

private def mustHold48i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase48Item2EventAlignment failed: {label}"

private def replayOk48i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 2a(i). `Costs.playManaCost` `(useImplicitPermissions := false)` & `.asAnyMana` on colored `increase`
  --        under `perm.anyMana && (perm.withoutManaCost || perm.payLifeEqualManaValue)`, plus `Agent.choose`
  --        casting via Null Summoner `anyMana` despite an unpayable `payLifeEqualManaValue` grant:
  let nullSummonerDef : CardDef := {
    bear with
    name := "P48i2 NullSummoner"
    staticAbilities := #[.castExiledWithSevenInGraveyard]
  }
  let rrSorcDef : CardDef := {
    bear with
    name := "P48i2 RedPyre"
    manaCost := { symbols := #[.colored .red, .colored .red] }
  }
  let gNull0 :=
    Id.run do
      let mut g := addPermanent (emptyHand g4 p0) nullSummonerDef p0 p0
      for _ in [0:7] do
        g := insertObject g bear p0 (.graveyard p0)
      return g
  let nullId := (gNull0.permanentsOf p0).find? (·.name == nullSummonerDef.name) |>.get!.id
  let gNullHand := insertObject gNull0 rrSorcDef p0 (.hand p0)
  let (gNullExRaw, nullExId) := gNullHand.move (gNullHand.player p0).hand.back! .exile none (cause := some testCause)
  let gNullEx := (gNullExRaw.changeObject nullExId (.exiledBy (some nullId))).loseLife p0 19
  let gNullUnpayableLife :=
    (gNullEx.createEffect
      (.permission (some p0) (.playFromExile nullExId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)).addMana p0 (.colored .green) 2
  let nullExObj := gNullUnpayableLife.object! nullExId
  let costNoImplicit :=
    gNullUnpayableLife.playManaCost { nullExObj with controller := some p0 } rrSorcDef
      (origPerm := none) (useImplicitPermissions := false)
  let costFreeAnyWithColoredTax :=
    gNullUnpayableLife.playManaCost { nullExObj with controller := some p0 } rrSorcDef
      (increase := { symbols := #[.colored .red] })
      (origPerm := some { player := p0, withoutManaCost := true, anyMana := true })
      (useImplicitPermissions := false)
  let agentPicksNullCast :=
    match Agent.choose gNullUnpayableLife p0 with | some (.cast id) => id == nullExId | _ => false
  let gNullAgentCast := mustApply (mustApply gNullUnpayableLife p0 (.cast nullExId)) p0 .pay

  -- 2a(ii). Unified timing-filtered `PlayPermission` ranking (`withoutManaCost` > payable `payLife` > `anyMana` > `ignoreTiming` > `!fromAdventure`):
  --         During main phase, `withoutManaCost := true, ignoreTiming := false` beats `withoutManaCost := false, ignoreTiming := true`;
  --         off-turn (`p1` active), `ignoreTiming := true` wins!
  let toOffTurnP1 (g : Game) : Game :=
    (g.record (GameEvent.turnBegan g.turnNumber p1 false (cause := some testCause))).change (.priority p0)
  let gRank0 := insertObject g4 rrSorcDef p0 .exile
  let rankExId := (gRank0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gRankBoth :=
    ((gRank0.createEffect
        (.permission (some p0) (.playFromExile rankExId { player := p0, ignoreTiming := true }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile rankExId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause))
  let gRankOffTurn := toOffTurnP1 gRankBoth
  -- Also CR 609.4b: off-turn resolution cast (`mayCastCards` paid) on `nullExId` does NOT splice Null Summoner's `anyMana`
  -- because Null Summoner's own permission requires sorcery timing!
  let gNullOffTurn := (toOffTurnP1 gNullEx).addMana p0 (.colored .green) 2
  let nullOffTurnPaidPerm := gNullOffTurn.paidResolutionOrigPerm? p0 (gNullOffTurn.object! nullExId)

  -- 2a(iii). CR 601.1a single-permission Morph binding in `CastExtras`:
  --          Exiled Morph creature with `{ anyMana := true, ignoreTiming := false }` AND `{ anyMana := false, ignoreTiming := true }`
  --          cast off-turn (`p1` active) selects the timing-legal `{ ignoreTiming := true, anyMana := false }` permission!
  let morphCreatureDef : CardDef := {
    bear with
    name := "P48i2 MorphStalker"
    manaCost := { symbols := #[.colored .blue, .colored .blue] }
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let gMorphSplice0 := insertObject (toOffTurnP1 g4) morphCreatureDef p0 .exile
  let morphSpliceExId := (gMorphSplice0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gMorphSplice1 :=
    ((gMorphSplice0.createEffect
        (.permission (some p0) (.playFromExile morphSpliceExId { player := p0, anyMana := true, ignoreTiming := false }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile morphSpliceExId { player := p0, anyMana := false, ignoreTiming := true }) .untilEndOfTurn)
      (cause := some testCause))
  let gMorphSpliceProp := mustApply gMorphSplice1 p0 (.cast morphSpliceExId)
  let gMorphSpliceChosen := mustApply gMorphSpliceProp p0 (.announceKicker true)

  let item2aOk :=
    mustHold48i2 "2a_noImplicitHijackColoredTaxAnyManaAndAgent"
      (costNoImplicit == rrSorcDef.manaCost &&
       (ManaPool.empty.add (.colored .green) 1).canPay costFreeAnyWithColoredTax &&
       agentPicksNullCast &&
       gNullAgentCast.stack.size == 1 &&
       (gNullAgentCast.player p0).life == 1) &&
    mustHold48i2 "2a_unifiedTimingRankingAndCr6094b"
      ((gRankBoth.playPermissionFor? p0 (gRankBoth.object! rankExId)).any (·.withoutManaCost) &&
       (gRankOffTurn.playPermissionFor? p0 (gRankOffTurn.object! rankExId)).any (fun pm => pm.ignoreTiming && !pm.withoutManaCost) &&
       nullOffTurnPaidPerm.isNone) &&
    mustHold48i2 "2a_cr6011aSingleMorphPermission"
      (gMorphSpliceProp.pending == .chooseKicker p0 &&
       gMorphSpliceChosen.proposedSpell.any (fun prop => prop.kicked && prop.cost == ManaCost.ofGeneric 3))

  -- 2b(i). `FraChoices` `.mayCastFromGraveyard`, `defaultFraAction`, and `Agent` `.mayCastExiledElseDamage`
  --        with an unrelated unpayable `payLifeEqualManaValue` permission:
  let gySorcDef : CardDef := {
    name := "P48i2 GyChant"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 3)
  }
  let gGy0 := ((insertObject g4 gySorcDef p0 (.graveyard p0)).loseLife p0 19).addMana p0 .colorless 2
  let gyCardId := (gGy0.player p0).graveyard.back!
  let gGyUnpayablePerm :=
    gGy0.createEffect
      (.permission (some p0) (.playFromExile gyCardId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gGyDefaultOk :=
    match gGyUnpayablePerm.defaultFraAction p0 (.mayCastFromGraveyard #[gyCardId]) with
    | .cast id => id == gyCardId
    | _ => false
  let gGyPrompt := gGyUnpayablePerm.change (.pending (.fraChoice p0 (.mayCastFromGraveyard #[gyCardId])))
  let gGyCastPaid := mustApply (mustApply gGyPrompt p0 (.cast gyCardId)) p0 .pay

  let gChandra0 := ((insertObject g4 gySorcDef p0 .exile).loseLife p0 19).addMana p0 .colorless 2
  let chandraExId := (gChandra0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gChandraPrompt :=
    (gChandra0.createEffect
      (.permission (some p0) (.playFromExile chandraExId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)).change
      (.pending (.mayCastExiledElseDamage p0 chandraExId 2 none))
  let chandraAgentCasts :=
    match Agent.choose gChandraPrompt p0 with | some (.cast id) => id == chandraExId | _ => false

  -- 2b(ii). `castFreeCopy` (`isForcedWithoutManaCostProposal` recognizing `.alternative "free copy"`),
  --         modal / X Morph-Impending offers under clean permission, and Flash+Morph off-turn timing:
  let gFreeCopy0 := insertObject g4 morphCreatureDef p0 (.hand p0)
  let (gFreeCopyEx, freeCopyId) :=
    gFreeCopy0.move (gFreeCopy0.player p0).hand.back! .exile none (isCopy := some true) (cause := some testCause)
  let gFreeCopyPrompt := gFreeCopyEx.change (.pending (.fraChoice p0 (.castCopiesFree #[freeCopyId] 5 1)))
  let gFreeCopyCast := mustApply gFreeCopyPrompt p0 (.cast freeCopyId)

  let modalImpDef : CardDef := {
    bear with
    name := "P48i2 ModalImpTitan"
    manaCost := ManaCost.ofGeneric 4
    spellModes := #[Effect.gainLife 1, Effect.gainLife 2]
    keywords := #[.impending 2 (CostSpec.ofGeneric 1)]
  }
  let xImpDef : CardDef := {
    bear with
    name := "P48i2 XImpTitan"
    manaCost := { symbols := #[.x, .generic 2] }
    keywords := #[.impending 2 (CostSpec.ofGeneric 1)]
  }
  let gModImp0 :=
    (insertObject (insertObject g4 modalImpDef p0 .exile) xImpDef p0 .exile).loseLife p0 19
  let exObjs2b := gModImp0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)
  let modImpId := exObjs2b[0]!.id
  let xImpId := exObjs2b[1]!.id
  let gModImp1 :=
    ((((gModImp0.createEffect
          (.permission (some p0) (.playFromExile modImpId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
          (cause := some testCause)).createEffect
        (.permission (some p0) (.playFromExile modImpId { player := p0 }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
       (.permission (some p0) (.playFromExile xImpId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
       (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile xImpId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause))
  let gModImpAfterMode := mustApply (mustApply gModImp1 p0 (.cast modImpId)) p0 (.chooseMode 0)
  let gXImpAfterX := mustApply (mustApply gModImp1 p0 (.cast xImpId)) p0 (.chooseX 0)

  -- Flash + Morph off-turn (`p1` active, `p0` has priority): front face casts via Flash without offering Morph!
  let flashMorphDef : CardDef := {
    bear with
    name := "P48i2 FlashMorpher"
    manaCost := ManaCost.zero
    keywords := #[Keyword.flash, .morph (CostSpec.ofGeneric 2)]
  }
  let gFlashMorphOff0 := insertObject (toOffTurnP1 g4) flashMorphDef p0 (.hand p0)
  let flashMorphHandId := (gFlashMorphOff0.player p0).hand.back!
  let gFlashMorphCast := mustApply gFlashMorphOff0 p0 (.cast flashMorphHandId)

  let item2bOk :=
    mustHold48i2 "2b_gyDefaultAndChandraUnpayablePerm"
      (gGyDefaultOk &&
       gGyCastPaid.stack.size == 1 &&
       (gGyCastPaid.player p0).life == 1 &&
       chandraAgentCasts) &&
    mustHold48i2 "2b_freeCopyModalXMorphAndFlashMorph"
      (gFreeCopyCast.stack.size == 1 &&
       gFreeCopyCast.pending != .chooseKicker p0 &&
       gModImpAfterMode.pending == .chooseKicker p0 &&
       gXImpAfterX.pending == .chooseKicker p0 &&
       !gFlashMorphOff0.canCastMorphFaceDown p0 (gFlashMorphOff0.object! flashMorphHandId) &&
       gFlashMorphCast.stack.size == 1 &&
       gFlashMorphCast.pending == .none)

  -- 2c(i). Non-stack `stackCtrl?` guard on synthetic `{ o with controller := some p0 }` in `.graveyard`,
  --        plus `latestExileToStackAfterController?` stopping on non-`.stack` `.exile` departure:
  let prepHostDef : CardDef := {
    bear with
    name := "P48i2 UnprepHost"
    prepareFace := some { name := "P48i2 Prep", manaCost := ManaCost.zero, types := #[.instant], spellEffect := some (Effect.gainLife 1) }
  }
  let gPrep0 := insertObject (addPermanent g4 prepHostDef p0 p0) gySorcDef p0 (.graveyard p0)
  let unprepId := (gPrep0.permanentsOf p0)[0]!.id
  let gyPrepCardId := (gPrep0.player p0).graveyard.back!
  let gPrep1 :=
    gPrep0.createEffect
      (.permission (some p0) (.playFromExile gyPrepCardId { player := p0, withoutManaCost := true, prepareSource := some unprepId }) .untilEndOfTurn)
      (cause := some testCause)
  let synthGyObj := { gPrep1.object! gyPrepCardId with controller := some p0 }
  -- Test `latestExileToStackAfterController?` via `playPermissionsFor` on `gyPrepCardId` (currently in `.graveyard p0` with `unprepId` unprepared):
  -- After `.exile -> .stack` (`after.controller == some p0`), `stackCtrl?` is `some p0` so `playPermissionsFor p0` succeeds;
  -- once a later `.exile -> .graveyard p0` (`toZ != .stack`) is recorded for `gyPrepCardId`, `latestExileToStackAfterController?` stops
  -- and returns `none`, so `playPermissionsFor p0` falls back to checking unprepared `unprepId` and returns `#[]`!
  let gyPrepBaseObj := gPrep1.object! gyPrepCardId
  let gExLog0 := insertObject (addPermanent g4 prepHostDef p0 p0) gySorcDef p0 .exile
  let unprepLogId := (gExLog0.permanentsOf p0)[0]!.id
  let exLogCardId := (gExLog0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gExLog1 :=
    gExLog0.createEffect
      (.permission (some p0) (.playFromExile exLogCardId { player := p0, withoutManaCost := true, prepareSource := some unprepLogId }) .untilEndOfTurn)
      (cause := some testCause)
  let exLogObj := gExLog1.object! exLogCardId
  let snapEx : EventObject := gExLog1.snapshot exLogObj
  let snapStackP0 : EventObject := { snapEx with id := some ⟨990001⟩, zone := .stack, controller := some p0 }
  let snapGy : EventObject := { snapEx with id := some ⟨990002⟩, zone := .graveyard p0, controller := none }
  let gExToStackLogged :=
    gExLog1.record (GameEvent.moved gExLog1.turnNumber snapEx .exile .stack (after := some snapStackP0) (cause := testCause))
  let gExToStackThenGyLogged :=
    gExToStackLogged.record (GameEvent.moved gExToStackLogged.turnNumber snapEx .exile (.graveyard p0) (after := some snapGy) (cause := testCause))
  let departedQueryObj : GameObject := { gyPrepBaseObj with id := exLogCardId }
  let zeroInst2Def : CardDef := {
    name := "P48i2 ZeroBolt"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellEffect := some (Effect.gainLife 1)
  }
  let gExStack0 := insertObject g4 zeroInst2Def p0 .exile
  let exStackId0 := (gExStack0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gExStack1 :=
    mustApply
      (gExStack0.createEffect
        (.permission (some p0) (.playFromExile exStackId0 { player := p0, withoutManaCost := true }) .untilEndOfTurn)
        (cause := some testCause))
      p0 (.cast exStackId0)
  let onStackId := gExStack1.stack.back!.objectId
  let (gBackToEx, backExId) := gExStack1.move onStackId .exile none (cause := some testCause)
  let (gExToGy, _) := gBackToEx.move backExId (.graveyard p0) none (cause := some testCause)

  -- 2c(ii). `Leaving.coDepartingIds` phased-out source-leave guard vs simultaneous EOT control expiry,
  --         `Turns` `pre` `hadPlayable` (including two same-named cards vs two permissions on one `oid`),
  --         BFS `fraEmblemEntries`, and direct `.command` emblem return-control log:
  let srcArtDef : CardDef := { name := "P48i2 CtrlRelic", types := #[.artifact] }
  let gPhSrcPre := addPermanent (addPermanent g4 srcArtDef p0 p0) bear p0 p3
  let ctrlRelicId := (gPhSrcPre.permanentsOf p0).find? (·.name == srcArtDef.name) |>.get!.id
  let phOwnedP3Id := (gPhSrcPre.permanentsOf p3).find? (·.name == bear.name) |>.get!.id
  let gPhSrcControlled :=
    ((gPhSrcPre.createEffect
        (.layered (.objects #[phOwnedP3Id]) (.control p0) (.whileSourceOnBattlefield ctrlRelicId))
        (cause := some testCause)).createEffect
       (.layered (.objects #[phOwnedP3Id]) (.copy hero) (.whileSourceOnBattlefield ctrlRelicId))
       (cause := some testCause))
  let gPhSrc0 := mustApply gPhSrcControlled p3 .concede
  let gPhSrc1 := gPhSrc0.phaseOut (gPhSrc0.object! phOwnedP3Id) (cause := some testCause)
  let prePhSrcLeaveLog := gPhSrc1.log.size
  let (gPhSrcLeft, _) := gPhSrc1.move ctrlRelicId .exile none (cause := some testCause)
  let phSrcLeaveLogs := gPhSrcLeft.log.extract prePhSrcLeaveLog gPhSrcLeft.log.size

  -- `Turns` `pre` `hadPlayable`: Elf controlled until EOT + two same-named exiled sorceries requiring `.elf`,
  -- with TWO permissions on the first `oid` and ONE on the second `oid` -> `clearEOT` logs the expiry message
  -- EXACTLY TWICE (once per distinct `oid`, NOT 0 times and NOT 3 times!):
  let gTurnsPre0 :=
    insertObject (insertObject (addPermanent g4 llanowarElves p1 p1) gySorcDef p0 .exile) gySorcDef p0 .exile
  let borrowedElfId := (gTurnsPre0.permanentsOf p1)[0]!.id
  let exPair := gTurnsPre0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)
  let exTwin1 := exPair[0]!.id
  let exTwin2 := exPair[1]!.id
  let gTurnsPre1 :=
    ((((gTurnsPre0.createEffect (.layered (.objects #[borrowedElfId]) (.control p0) .untilEndOfTurn)
          (cause := some testCause)).createEffect
        (.permission (some p0) (.playFromExile exTwin1 { player := p0, requireSubtype := some .elf }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
       (.permission (some p0) (.playFromExile exTwin1 { player := p0, withoutManaCost := true, requireSubtype := some .elf }) .untilEndOfTurn)
       (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile exTwin2 { player := p0, requireSubtype := some .elf }) .untilEndOfTurn)
      (cause := some testCause))
  let preTurnsLog := gTurnsPre1.log.size
  let gTurnsEot := gTurnsPre1.clearEOT
  let turnsExpLogs :=
    (gTurnsEot.log.extract preTurnsLog gTurnsEot.log.size).filter
      (· == s!"{gySorcDef.name} can no longer be played from exile")

  -- BFS `fraEmblemEntries` (`srcArt -> parentEmb -> childEmb` even when `childEmb`'s `.fraEmblem` was registered BEFORE `parentEmb`'s)
  -- AND direct `.command` emblem `ceaseToExist` single-target return-control log:
  let embDef : CardDef := { name := "P48i2 Emblem", types := #[] }
  let gBfs0 :=
    insertObject (insertObject (addPermanent (addPermanent g4 srcArtDef p0 p0) bear p1 p1)
      embDef p0 .command (some p0)) embDef p0 .command (some p0)
  let bfsSrcId := (gBfs0.permanentsOf p0)[0]!.id
  let bfsBearId := (gBfs0.permanentsOf p1)[0]!.id
  let bfsEmbs := gBfs0.objects.filter (fun (o : GameObject) => o.zone == Zone.command)
  let parentEmbId := bfsEmbs[0]!.id
  let childEmbId := bfsEmbs[1]!.id
  -- Register `childEmb` FIRST in `activeEffects`, then `parentEmb`:
  let gBfs1 :=
    (((gBfs0.createEffect (.gameRule (.fraEmblem childEmbId) (.whileInZone parentEmbId .command))
        (cause := some testCause)).createEffect
       (.gameRule (.fraEmblem parentEmbId) (.whileSourceOnBattlefield bfsSrcId))
       (cause := some testCause)).createEffect
      (.layered (.objects #[bfsBearId]) (.control p0) (.whileInZone childEmbId .command))
      (cause := some testCause))
  -- Direct `ceaseToExist` on `childEmbId` logs `"Event Bear returns to Chandra's control"`:
  let preDirectEmbLog := gBfs1.log.size
  let gDirectEmbCeased := gBfs1.ceaseToExist childEmbId (cause := some testCause)
  let directEmbLogs := gDirectEmbCeased.log.extract preDirectEmbLog gDirectEmbCeased.log.size
  -- Leaving `bfsSrcId` ceases `parentEmbId` BEFORE `childEmbId` in BFS order!
  let preBfsLeaveIdx := gBfs1.events.size
  let (gBfsSrcLeft, _) := gBfs1.move bfsSrcId .exile none (cause := some testCause)
  let ceasedOrder :=
    (gBfsSrcLeft.events.extract preBfsLeaveIdx gBfsSrcLeft.events.size).filterMap fun ev =>
      match ev.change with
      | .rules (.zone (.ceasedToExist snap)) => snap.id
      | _ => none

  -- `expireUntilNextTurnEffects` forwards the pre-`restoreCopiesUntilNextTurn` `preState?` into
  -- `expireFraUntilTurnEffects` (matching `beginTurn`, CR 500.4 / 611.2a / 800.4m): an exiled spell
  -- playable while an `.untilNextTurnOf p2` copy made `bear` an Elf DOES log `"can no longer be played from exile"`!
  let gDepCopy0 := insertObject (addPermanent (mustApply g4 p2 .concede) bear p0 p0) gySorcDef p0 .exile
  let depCopyBearId := (gDepCopy0.permanentsOf p0)[0]!.id
  let depExCardId := (gDepCopy0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gDepCopy1 :=
    ((gDepCopy0.createEffect
        (.layered (.objects #[depCopyBearId]) (.copy llanowarElves) (.untilNextTurnOf p2))
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile depExCardId { player := p0, requireSubtype := some .elf }) (.untilNextTurnOf p2))
      (cause := some testCause))
  let preDepExpLog := gDepCopy1.log.size
  let gDepCopyExpired := gDepCopy1.expireUntilNextTurnEffects p2
  let depCopyLogs := gDepCopyExpired.log.extract preDepExpLog gDepCopyExpired.log.size

  let item2cOk :=
    mustHold48i2 "2c_nonStackSynthCtrlAndExileStop"
      ((gPrep1.playPermissionsFor p0 synthGyObj).isEmpty &&
       (gPrep1.activePlayPermissions synthGyObj).isEmpty &&
       (gExToStackLogged.playPermissionsFor p0 departedQueryObj).size == 1 &&
       (gExToStackThenGyLogged.playPermissionsFor p0 departedQueryObj).isEmpty) &&
    mustHold48i2 "2c_phasedOutCoDepartingTurnsPreBfsAndCmdReturnLog"
      ((gPhSrcLeft.object! phOwnedP3Id).status.phasedOut &&
       phSrcLeaveLogs.any (· == s!"{bear.name} is no longer a copy of {hero.name}") &&
       turnsExpLogs.size == 2 &&
       depCopyLogs.any (· == s!"{gySorcDef.name} can no longer be played from exile") &&
       depCopyLogs.any (· == s!"{bear.name} is no longer a copy of {llanowarElves.name}") &&
       directEmbLogs.any (· == s!"{bear.name} returns to {(gBfs1.player p1).name}'s control") &&
       ceasedOrder == #[parentEmbId, childEmbId])

  mustHold48i2 "2a.noImplicitHijackRankingAndSingleMorphPerm" item2aOk &&
  mustHold48i2 "2b.gyChandraFreeCopyModalAndFlashMorph" item2bOk &&
  mustHold48i2 "2c.nonStackLkiCoDepartingTurnsBfsAndCmdLog" item2cOk &&
  mustHold48i2 "2.replay"
    (replayOk48i2 #[gNullAgentCast, gRankBoth, gMorphSpliceChosen, gGyCastPaid,
      gFreeCopyCast, gFlashMorphCast, gExToGy, gPhSrcLeft, gTurnsEot, gDepCopyExpired,
      gDirectEmbCeased, gBfsSrcLeft])

end Phase48Item2EventAlignment

section Phase48Item3EventAlignment

private def mustHold48i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase48Item3EventAlignment failed: {label}"

private def replayOk48i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 3a. Controllerless CR 800.4c `lkiCtrl` fallback attribution (`poSnapCtrl?` then `some fallback`):
  --     Permanent owned by living `p0` with `defaultController := some p2` (departed `p2`) and a `.leaving` trigger
  --     phases in with no active control effects -> CR 800.4c exiles it, attributing `lkiCtrl` to departed `p2`
  --     (`some fallback`) rather than living `cur.owner == p0`, so CR 800.4d suppresses the `.leaving` trigger!
  let ltbRelicDef : CardDef := {
    name := "P48i3 LtbRelic"
    types := #[.artifact]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .thisLeaves (Effect.gainLife 5)]
  }
  let gP2Gone := mustApply g4 p2 .concede
  let (gLkiFb0, lkiFbObj) := gP2Gone.allocObject ltbRelicDef p0 .battlefield (some p2) { phasedOut := true }
  let gLkiFbPhasedIn := gLkiFb0.phaseIn (gLkiFb0.object! lkiFbObj.id)
  -- Conversely, if it phased out under living `p0`'s control (`poSnapCtrl? == some p0`) before `p0`'s control source left,
  -- `poSnapCtrl?` attributes the CR 800.4c departure to living `p0`, so `p0`'s `.leaving` trigger DOES fire!
  let ctrlSrcDef : CardDef := { name := "P48i3 CtrlAnchor", types := #[.artifact] }
  let gLkiPo0 := addPermanent g4 ctrlSrcDef p0 p0
  let ctrlAnchorId := (gLkiPo0.permanentsOf p0)[0]!.id
  let gLkiPo1 := addPermanent gLkiPo0 ltbRelicDef p0 p2
  let lkiPoObj := (gLkiPo1.permanentsOf p2).find? (·.name == ltbRelicDef.name) |>.get!
  let gLkiPo2 :=
    (gLkiPo1.createEffect
      (.layered (.objects #[lkiPoObj.id]) (.control p0) (.whileSourceOnBattlefield ctrlAnchorId))
      (cause := some testCause)).phaseOut (gLkiPo1.object! lkiPoObj.id) (cause := some testCause)
  let gLkiPo3 := mustApply gLkiPo2 p2 .concede
  let (gLkiPo4, _) := gLkiPo3.move ctrlAnchorId .exile none (cause := some testCause)
  let gLkiPoPhasedIn := gLkiPo4.phaseIn (gLkiPo4.object! lkiPoObj.id)

  let item3aOk :=
    mustHold48i3 "3a_lkiCtrlFallbackSuppressesDepartedTrigger"
      ((gLkiFbPhasedIn.followMovedToZone? lkiFbObj.id (· == .exile)).isSome &&
       gLkiFbPhasedIn.waitingTriggers.isEmpty) &&
    mustHold48i3 "3a_poSnapCtrlPreservesLivingTrigger"
      ((gLkiPoPhasedIn.followMovedToZone? lkiPoObj.id (· == .exile)).isSome &&
       gLkiPoPhasedIn.waitingTriggers.size == 1 &&
       gLkiPoPhasedIn.waitingTriggers[0]!.controller == p0)

  -- 3b. Post-batch `Phasing` CR 800.4c reconciliation (standalone `.phasedIn` batch is distinct from CR 800.4c exile batch!)
  --     AND CR 702.26h orphaned indirect phase-in (`phasedWith == some hostId` when `hostId` left while phased out):
  let phInBatch? :=
    gLkiFbPhasedIn.events.findSome? fun ev =>
      match ev.change with
      | .rules (.permanent (.phasedIn eo _)) => if eo.id == some lkiFbObj.id then ev.batch else none
      | _ => none
  let cr800ExileBatch? :=
    gLkiFbPhasedIn.events.findSome? fun ev =>
      match ev.change with
      | .rules (.zone (.moved before _ .battlefield .exile ..)) =>
        if before.id == some lkiFbObj.id then ev.batch else none
      | _ => none

  -- CR 702.26h: Equipment attached to `hostBear` phases out indirectly with `hostBear` (`phasedWith == some hostBear.id`),
  -- then `hostBear` is exiled from `.battlefield` while phased out (`g.move hostBear.id .exile none`),
  -- leaving the Equipment phased out with `phasedWith == some hostBear.id` and `hostBear` no longer a battlefield object:
  -- `phaseInControlled p0` phases the orphaned Equipment in directly!
  let equipDef : CardDef := {
    name := "P48i3 OrphanBlade"
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  let gOrph0 := addPermanent (addPermanent g4 bear p0 p0) equipDef p0 p0
  let hostBearId := (gOrph0.permanentsOf p0).find? (fun (o : GameObject) => o.name == bear.name) |>.get!.id
  let bladeId := (gOrph0.permanentsOf p0).find? (fun (o : GameObject) => o.name == equipDef.name) |>.get!.id
  let gOrphAttached := gOrph0.attachSourceTo (gOrph0.object! bladeId) (gOrph0.object! hostBearId) (cause := some testCause)
  let gOrphPhasedOut := gOrphAttached.phaseOut (gOrphAttached.object! hostBearId) (cause := some testCause)
  let (gOrphHostGone, _) := gOrphPhasedOut.move hostBearId .exile none (cause := some testCause)
  let bladeWhileOrphaned := gOrphHostGone.object! bladeId
  let gOrphPhasedIn := gOrphHostGone.phaseInControlled p0

  let item3bOk :=
    mustHold48i3 "3b_postBatchPhasingReconcileSeparateBatches"
      (phInBatch?.isSome &&
       cr800ExileBatch?.isSome &&
       phInBatch? != cr800ExileBatch? &&
       gLkiFbPhasedIn.currentBatch.isNone) &&
    mustHold48i3 "3b_cr70226hOrphanedIndirectPhaseIn"
      (bladeWhileOrphaned.status.phasedOut &&
       bladeWhileOrphaned.status.phasedWith == some hostBearId &&
       (gOrphPhasedIn.object! bladeId).isOnBattlefield &&
       !(gOrphPhasedIn.object! bladeId).status.phasedOut)

  -- 3c(i). Complete `etbCostProspective?` forwarding across `Core.*AnyObjId` (`delayedTriggerAnyObjId`,
  --        `pendingReplacementAnyObjId`): aborted ETB `.costPayment .life` inside a `PendingReplacement.restorePausedBatch`
  --        still keeps `isInitialMaterialize == true` when `prospId` later materializes!
  let prospId : ObjectId := ⟨g4.nextObjectId⟩
  let dummyBid : BatchId := ⟨g4.nextBatchId⟩
  let gProspNested :=
    (((g4.change (.replacementOrder #[{ kind := .entersUntappedPayLife 2, object := some prospId }])).changes #[
        .pushContinuationFrame {},
        .pendingReplacement
          (some (.restorePausedBatch dummyBid 0 false (some (.costPayment .life p0 (some prospId)))
            g4.objects g4.players g4.activeEffects .none g4.stack)),
        .pendingReplacement none,
        .popContinuationFrame ])).record
      (GameEvent.life g4.turnNumber p0 2 (gained := false)
        (cause := .costPayment .life p0 (some prospId)))
  let preRealNestedIdx := gProspNested.events.size
  let gAfterNestedProsp := addPermanent gProspNested bear p0 p0
  let realNestedPerm := (gAfterNestedProsp.permanentsOf p0).back!

  -- 3c(ii). Historical counter LKI on departed `missingObjs` in `mkHistoricalGameAt`,
  --         live `counters` on `Attachments.unattachFrom`, and `count?.isNone` guard in `objectCounterCountAt`:
  let gDepCnt0 := addPermanent g4 bear p0 p0
  let depCntId := (gDepCnt0.permanentsOf p0)[0]!.id
  let gDepCnt1 := gDepCnt0.recordPutCounters depCntId .plusOnePlusOne 3 (some p0) (cause := some testCause)
  let gDepCntQuiet := (quiet gDepCnt1).ceaseToExist depCntId (cause := some testCause)
  let histDepAt0 := gDepCntQuiet.mkHistoricalGameAt 0
  let depAt0Obj? := histDepAt0.findObject? depCntId

  -- `Attachments.unattachFrom` stamps live `o.status.toCounterBag` on `snap.counters`:
  let gUnatt0 :=
    (addPermanent (addPermanent g4 bear p0 p0) equipDef p0 p0)
  let uHostId := (gUnatt0.permanentsOf p0).find? (fun (o : GameObject) => o.name == bear.name) |>.get!.id
  let uBladeId := (gUnatt0.permanentsOf p0).find? (fun (o : GameObject) => o.name == equipDef.name) |>.get!.id
  let gPreUnatt := gUnatt0.attachSourceTo (gUnatt0.object! uBladeId) (gUnatt0.object! uHostId) (cause := some testCause)
  let gUnatt1 := gPreUnatt.recordPutCounters uBladeId .charge 2 (some p0) (cause := some testCause)
  let gUnatt2 := gUnatt1.unattachFrom uHostId (preState? := some gPreUnatt)
  let unattSnapCounters? :=
    gUnatt2.events.findSomeRev? fun ev =>
      match ev.change with
      | .rules (.permanent (.unattached eo _)) => if eo.id == some uBladeId then some eo.counters else none
      | _ => none

  -- `objectCounterCountAt` `count?.isNone` guard: an exact `.counters` event at index 0 is NOT overwritten
  -- by a later pre-snapshot event (`.tapped`) before `idx`!
  let gCntGuard0 := quiet (addPermanent g4 bear p0 p0)
  let cgId := (gCntGuard0.permanentsOf p0)[0]!.id
  let gCntGuard1 :=
    (gCntGuard0.recordPutCounters cgId .charge 2 (some p0) (cause := some testCause)).record
      (GameEvent.tapped gCntGuard0.turnNumber { gCntGuard0.snapshot (gCntGuard0.object! cgId) with counters := #[(.charge, 9)] }
        (nowTapped := true) (cause := testCause))

  -- 3c(iii). `Phasing.departedNextTurnWouldHaveBegunSince` `prevClearEotExtra` guard when a non-starting
  --          player (`p1`) already had `leftTheGame == true` pre-log:
  --          `p0` (turn 1) -> `p1` (turn 2, then concedes on turn 2) -> `p2` (turn 3) -> `p3` (turn 4)!
  --          At turn 4 (`p3` active, `t == 4`, `nTeams == 3` living `[p0, p2, p3]`, `p1` departed pre-log),
  --          `(4 - 1) % 3 == 0` with `sIdx == 0` vs `aIdx == 2` (`p3`), yet turn 4 is a REGULAR turn (NOT an extra turn)!
  let gPreDepT2 := g4.startNextTurnAndBegin -- turn 2, `p1` active
  let gPreDepT2Concede := mustApply gPreDepT2 p1 .concede
  let gPreDepT3 := gPreDepT2Concede.startNextTurnAndBegin -- turn 3, `p2` active
  let gPreDepT4 := gPreDepT3.startNextTurnAndBegin -- turn 4, `p3` active (`extra == false`)
  -- On `quiet gPreDepT4` (`p3` active, turn 4, `p1` already departed pre-log), `p0`'s Bear is controlled by `p2`,
  -- phases out under `p2`, `p2` concedes on turn 4, and `clearEOT` expires `.cantCastSpells` on `p3`:
  -- when turn 5 (`p0`'s turn) begins, `p2`'s next turn after `p3` has NOT begun yet (`p3 -> p0`), so it stays phased out,
  -- and then phases in on turn 6 (`p3`'s turn, passing `[p2]` between `p0` and `p3`)!
  let gQuietT4 := quiet gPreDepT4
  let gPreDep0 :=
    ((addPermanent gQuietT4 bear p0 p0).createEffect
      (.playerRule p3 .cantCastSpells .untilEndOfTurn) (cause := some testCause))
  let preDepBearId := (gPreDep0.permanentsOf p0)[0]!.id
  let gPreDep1 :=
    mustApply
      ((gPreDep0.createEffect (.layered (.objects #[preDepBearId]) (.control p2) .indefinite)
          (cause := some testCause)).phaseOut (gPreDep0.object! preDepBearId) (cause := some testCause))
      p2 .concede
  let gPreDepEot := gPreDep1.clearEOT
  let gPreDepTurn5P0 := gPreDepEot.startNextTurnAndBegin -- turn 5, `p0` active (`p2`'s seat is AFTER `p0`, so still phased out!)
  let gPreDepTurn6P3 := gPreDepTurn5P0.startNextTurnAndBegin -- turn 6, `p3` active (`p0 -> [p2] -> p3`, so now phased in!)

  let item3cOk :=
    mustHold48i3 "3c_nestedProspectiveEtbCost"
      (realNestedPerm.id == prospId &&
       gAfterNestedProsp.objectZoneAndPhasedOutAt? prospId preRealNestedIdx == none &&
       gAfterNestedProsp.objectZoneAndPhasedOutAt? prospId gAfterNestedProsp.events.size == some (Zone.battlefield, false)) &&
    mustHold48i3 "3c_missingObjCountersUnattachAndCountGuard"
      (depAt0Obj?.any (fun (o : GameObject) => o.status.plusOnePlusOne == 3) &&
       histDepAt0.power (depAt0Obj?.get!) == 5 &&
       unattSnapCounters? == some #[(CounterKind.charge, 2)] &&
       gCntGuard1.objectCounterCountAt cgId .charge 1 == 2) &&
    mustHold48i3 "3c_preLogDepartedNonStartTeamGuard"
      (gPreDepTurn5P0.activePlayer == p0 &&
       (gPreDepTurn5P0.object! preDepBearId).status.phasedOut &&
       gPreDepTurn6P3.activePlayer == p3 &&
       !(gPreDepTurn6P3.object! preDepBearId).status.phasedOut)

  mustHold48i3 "3a.lkiCtrlFallbackAndPoSnapCtrl" item3aOk &&
  mustHold48i3 "3b.postBatchPhasingAndOrphanedPhaseIn" item3bOk &&
  mustHold48i3 "3c.prospectiveEtbCountersAndPreLogExtraGuard" item3cOk &&
  mustHold48i3 "3.replay"
    (replayOk48i3 #[gLkiPoPhasedIn, gOrphPhasedIn, gAfterNestedProsp,
      gUnatt2, gPreDepT4])

end Phase48Item3EventAlignment

section Phase48Item4EventAlignment

private def mustHold48i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase48Item4EventAlignment failed: {label}"

private def replayOk48i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustStepAgent48 (g : Game) (p : PlayerId) : Game :=
  match Agent.choose g p with
  | some act => mustApply g p act
  | none => panic! "Phase48Item4EventAlignment: Agent.choose returned none"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := emptyHand (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })) p0

  -- 4a(i). `finishManaAbilityMountainTrigger` stamps `.mountainExtraRed` effect's source `ObjectId`
  --        (not the tapped Mountain's `id`, and `fromTreasure == false` even on a Mountain Treasure!),
  --        and `mountainExtraRedThisTurn` is included in `addTapManaToPool` / `availableMana` / `canPayFromSources`:
  let flareSrcDef : CardDef := { name := "P48i4 FlareEnchantment", types := #[.enchantment] }
  let treasureMountainDef : CardDef := {
    mountain with
    name := "P48i4 TreasurePeak"
    types := #[.artifact, .land]
    subtypes := #["Mountain", "Treasure"]
  }
  let rrSpellDef : CardDef := {
    name := "P48i4 DoubleFlame"
    manaCost := { symbols := #[.colored .red, .colored .red] }
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 2)
  }
  let gMtn0 := addPermanent (addPermanent g3 flareSrcDef p0 p0) treasureMountainDef p0 p0
  let flareId := (gMtn0.permanentsOf p0).find? (·.name == flareSrcDef.name) |>.get!.id
  let peakObj := (gMtn0.permanentsOf p0).find? (·.name == treasureMountainDef.name) |>.get!
  let gMtn1 :=
    gMtn0.createEffect
      (.playerRule p0 (.mountainExtraRed 1) .untilEndOfTurn)
      (cause := some (.oneShotEffect none (some flareId) (some p0)))
  let mtnAvailPaysRR := (gMtn1.availableMana p0).canPay rrSpellDef.manaCost
  let mtnSourcesPayRR :=
    gMtn1.canPayFromSources ManaPool.empty rrSpellDef.manaCost (gMtn1.manaSources p0).toList
  let gMtnTapped := mustApply gMtn1 p0 (.tapForMana peakObj.id (.colored .red))
  let tappedUnits := (gMtnTapped.player p0).manaPool.units

  -- 4a(ii). `manaAbilityIndexFor` ranks unrestricted / higher-yield granted abilities ahead of
  --         restricted printed abilities, and `ManaOutput.combination` handles mixed-color `{U}{R}`:
  let dragonCavernDef : CardDef := {
    name := "P48i4 DragonCavern"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .red, .const 1)]) (restriction := some .dragonSpell)]
  }
  let lanternDef : CardDef := {
    name := "P48i4 ChromaticLantern"
    types := #[.artifact]
    staticAbilities := #[.grantLandsTapAnyColor]
  }
  let gShadow0 := addPermanent (addPermanent g3 dragonCavernDef p0 p0) lanternDef p0 p0
  let cavernObj := (gShadow0.permanentsOf p0).find? (·.name == dragonCavernDef.name) |>.get!
  let gShadowTapped := mustApply gShadow0 p0 (.tapForMana cavernObj.id (.colored .red))

  let urComboLandDef : CardDef := {
    name := "P48i4 CascadeBluffs"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.combination (.explicit #[.colored .blue, .colored .red]) (.const 2))]
  }
  let urSpellDef : CardDef :=
    creature "P48i4 IzzetMage" { symbols := #[.colored .blue, .colored .red] } #["Wizard"] 2 2
  let gCombo0 := insertObject (addPermanent g3 urComboLandDef p0 p0) urSpellDef p0 (.hand p0)
  let comboSourcesPayUR :=
    gCombo0.canPayFromSources ManaPool.empty urSpellDef.manaCost (gCombo0.manaSources p0).toList
  let gComboProp := mustApply gCombo0 p0 (.cast (gCombo0.player p0).hand.back!)
  let gComboDone := mustStepAgent48 (mustStepAgent48 gComboProp p0) p0

  -- 4a(iii). `Agent.choose` `.chooseX` cost-preserving Crew / tap-pick search:
  --          `solGolem` (2/2 creature with `{T}: Add {C}{C}`, added FIRST) + `bear` (2/2 non-mana creature, added SECOND)
  --          + `xTapAltar` (`{X}, Tap an untapped creature you control`):
  --          greedy first tap pick would tap `solGolem` (`X = 0`), whereas branch-and-bound reserves `bear` for the tap pick
  --          and chooses `X = 2`!
  let solGolemDef : CardDef := {
    creature "P48i4 SolGolem" ManaCost.empty #["Golem"] 2 2 with
    types := #[.artifact, .creature]
    keywords := #[Keyword.haste]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 2)])]
  }
  let xTapAltarDef : CardDef := {
    name := "P48i4 XTapAltar"
    types := #[.enchantment]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana { symbols := #[.x] }, .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.gainLife 3
    }]
  }
  let gXTap0 := addPermanent (addPermanent (addPermanent g3 solGolemDef p0 p0) bear p0 p0) xTapAltarDef p0 p0
  let xAltarId := (gXTap0.permanentsOf p0).find? (·.name == xTapAltarDef.name) |>.get!.id
  let gXTapProp := mustApply gXTap0 p0 (.activate xAltarId 0)
  let xTapChoseTwo :=
    match Agent.choose gXTapProp p0 with | some (.chooseX 2) => true | _ => false
  let gXTapPaid :=
    mustStepAgent48 (mustStepAgent48 (mustStepAgent48 (mustStepAgent48 gXTapProp p0) p0) p0) p0

  let item4aOk :=
    mustHold48i4 "4a_mountainExtraRedProvenanceAndPoolSim"
      (mtnAvailPaysRR &&
       mtnSourcesPayRR &&
       tappedUnits.size == 2 &&
       tappedUnits[0]!.source == some peakObj.id &&
       tappedUnits[0]!.fromTreasure &&
       tappedUnits[1]!.source == some flareId &&
       !tappedUnits[1]!.fromTreasure) &&
    mustHold48i4 "4a_manaAbilityRankingAndCombination"
      (gShadow0.manaAbilityIndexFor cavernObj (.colored .red) == some 1 &&
       (gShadowTapped.player p0).manaPool.red == 1 &&
       (gShadowTapped.player p0).manaPool.restrictedEntries.isEmpty &&
       comboSourcesPayUR &&
       gComboDone.stack.size == 1 &&
       gComboDone.pending == .none) &&
    mustHold48i4 "4a_agentChooseXPreservesMultiManaSource"
      (xTapChoseTwo &&
       gXTapPaid.stack.size == 1)

  -- 4b(i). Strict `Event.isTreasureManaUnit` (not fooled by stale pre-strip `abilityActivated` snapshot in `events`)
  --        & `isTreasureSourceInLog` battlefield-departure LKI (`ZoneEvent.moved` & `ZoneEvent.ceasedToExist`):
  let relicTrDef : CardDef := {
    name := "P48i4 ShiftingChest"
    types := #[.artifact]
    subtypes := #["Treasure"]
    activatedAbilities := #[ActivatedAbility.manaAbility (.oneOf .anyColor (.const 1))]
  }
  let gShift0 := addPermanent g3 relicTrDef p0 p0
  let chestId := (gShift0.permanentsOf p0)[0]!.id
  let gShiftAct1 := mustApply gShift0 p0 (.tapForMana chestId (.colored .red))
  let gShiftUntapped :=
    (gShiftAct1.untapPermanent (gShiftAct1.object! chestId) (cause := some testCause)).createEffect
      (.layered (.objects #[chestId]) (.types .set #[.enchantment] #[] #[]) .untilEndOfTurn)
      (cause := some testCause)
  let gShiftAfterStrip := gShiftUntapped.addMana p0 (.colored .green) 1 (source := some chestId)
  let shiftUnits := (gShiftAfterStrip.player p0).manaPool.units
  let dummySpellTr : ObjectId := ⟨880001⟩
  let dummySpellNonTr : ObjectId := ⟨880002⟩
  let gShiftSpentCheck :=
    (gShiftAfterStrip.record (GameEvent.manaSpent gShiftAfterStrip.turnNumber p0 #[shiftUnits[0]!] (forObject := some dummySpellTr))).record
      (GameEvent.manaSpent gShiftAfterStrip.turnNumber p0 #[shiftUnits[1]!] (forObject := some dummySpellNonTr))

  -- Treasure leaves `.battlefield` via `.moved` (card Treasure) and `.ceasedToExist` (token Treasure) WITHOUT `abilityActivated`,
  -- then its delayed/triggered mana resolution calls `addMana`: `isTreasureSourceInLog` sees the battlefield-departure snapshot!
  let cardTreasureDef : CardDef := { name := "P48i4 GoldIngot", types := #[.artifact], subtypes := #["Treasure"] }
  let gMovedTr0 := addPermanent g3 cardTreasureDef p0 p0
  let ingotId := (gMovedTr0.permanentsOf p0)[0]!.id
  let (gMovedTr1, _) := gMovedTr0.move ingotId (.graveyard p0) none (cause := some testCause)
  let gMovedTrMana := gMovedTr1.addMana p0 (.colored .blue) 1 (source := some ingotId)

  let (gCeasedTr0, ceasedTok) := g3.createOneToken p0 Catalog.treasureToken (cause := some testCause)
  let gCeasedTr1 := gCeasedTr0.ceaseToExist ceasedTok.id (cause := some testCause)
  let gCeasedTrMana := gCeasedTr1.addMana p0 (.colored .black) 1 (source := some ceasedTok.id)

  -- 4b(ii). Modal `SpellResolution.runSpellModesAndEmpower` forwarding `lastKnownPower` and `lastKnownToughness`
  --         across `.continueSpellModes`, plus permanent-spell `chosenX` fallback on triggered abilities:
  let gLibSeeded := insertObject g3 forest p0 (.library p0)
  let modalToughTrigDef : CardDef := {
    creature "P48i4 ElderOak" ManaCost.empty #["Treefolk"] 1 5 with
    triggeredAbilities := #[
      TriggeredAbility.mkModal .thisDies #[
        Effect.scry 1,
        { resolution? := some (.addMana #[.colored .green] .equalSourceToughness), phrase := "Add {G} equal to toughness." }
      ] (headerPhrase := "Choose two.")
    ]
  }
  let gOak0 := addPermanent gLibSeeded modalToughTrigDef p0 p0
  let oakObj := (gOak0.permanentsOf p0).find? (·.name == modalToughTrigDef.name) |>.get!
  let oakAb := modalToughTrigDef.triggeredAbilities[0]!
  let (gOakGone, _) := gOak0.move oakObj.id (.graveyard p0) none (cause := some testCause)
  let gOakStacked0 :=
    gOakGone.putTriggeredAbilityOnStack p0 oakObj oakAb "triggers"
      (lastKnownPower := some 1) (lastKnownToughness := some 5) (eventCause := some testCause)
      (abilityEffectOverride := some oakAb.modeEffects[0]!)
  let oakTopEntry := gOakStacked0.stack.back!
  let gOakStacked :=
    gOakStacked0.changes #[
      .popStack,
      .pushStack { oakTopEntry with chosenMode := some 0, extraModes := #[1] } ]
  let gOakResPaused := gOakStacked.resolveTop -- mode 0 opens `.scry p0 1`, chaining `.continueSpellModes` with `lastKnownToughness == some 5`!
  let gOakFinished := mustApply gOakResPaused p0 (.scry #[(gOakResPaused.player p0).library.back!] #[])

  -- Permanent-spell `chosenX` on triggered abilities (`{X}` artifact with `TriggerPattern.thisEnters` `.addMana #[.colored .red] .chosenX`):
  let xPermManaDef : CardDef := {
    name := "P48i4 DynamoCore"
    manaCost := { symbols := #[.x] }
    types := #[.artifact]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .thisEnters { resolution? := some (.addMana #[.colored .red] .chosenX), phrase := "When this enters, add X {R}." }
    ]
  }
  let gXPerm0 := (insertObject g3 xPermManaDef p0 (.hand p0)).addMana p0 .colorless 3
  let gXPermCast :=
    mustApply (mustApply (mustApply gXPerm0 p0 (.cast (gXPerm0.player p0).hand.back!)) p0 (.chooseX 3)) p0 .pay
  let gXPermEntered := mustApply (mustApply (mustApply gXPermCast p0 .pass) p1 .pass) p2 .pass
  let gXPermTrigRes := mustApply (mustApply (mustApply gXPermEntered p0 .pass) p1 .pass) p2 .pass

  let item4bOk :=
    mustHold48i4 "4b_strictTreasureManaUnitAndDepartureLki"
      (shiftUnits.size == 2 &&
       GameEvent.treasureManaSpentOn gShiftSpentCheck.events dummySpellTr &&
       !GameEvent.treasureManaSpentOn gShiftSpentCheck.events dummySpellNonTr &&
       GameEvent.isTreasureSourceInLog gMovedTr1.events ingotId &&
       (gMovedTrMana.player p0).manaPool.units.all (·.fromTreasure) &&
       GameEvent.isTreasureSourceInLog gCeasedTr1.events ceasedTok.id &&
       (gCeasedTrMana.player p0).manaPool.units.all (·.fromTreasure)) &&
    mustHold48i4 "4b_modalTriggerLkiToughnessAndPermanentChosenX"
      ((match gOakResPaused.pending with | .scry q 1 _ => q == p0 | _ => false) &&
       (gOakFinished.player p0).manaPool.green == 5 &&
       (gXPermTrigRes.player p0).manaPool.red == 3)

  mustHold48i4 "4a.mountainExtraRedRankingComboAndChooseX" item4aOk &&
  mustHold48i4 "4b.treasureProvenanceModalToughnessAndPermChosenX" item4bOk &&
  mustHold48i4 "4.replay"
    (replayOk48i4 #[gMtnTapped, gShadowTapped, gComboDone, gXTapPaid,
      gShiftAfterStrip, gMovedTrMana, gCeasedTrMana, gOakFinished, gXPermTrigRes])

end Phase48Item4EventAlignment

end Mtg.Engine.EventTests
