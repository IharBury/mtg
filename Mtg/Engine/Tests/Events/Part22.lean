import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

/-! ### Phase 56 Item 1: Post-Phase-55 continuation/probe regressions (`SacrificeDiscard.sacrificeForActivation`,
`Event.lean` `isPurePriorityGrantLeaf` / `insertBeforeTrailingPriorityGrant` & mana-ability post-log priority drop,
`.seq` `rewindProposal` / `.leavePlayersWhoLost`, `Casting.afterWardResolved`, `drainProbeNonPriorityCont`),
CR 117.3c priority-recipient parity, top-level queue & `.seq` probe alignment, and
`chooseCastFromLooked` / `supplyOrder` / `putCardsOnBottom` / interpreter `outerCont?` ordering -/
section Phase56Item1EventAlignment

private def mustHold56i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase56Item1EventAlignment failed: {label}"

private def replayOk56i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let ridA : ReplacementId := { kind := .replaceDraw, player := some p0 }
  let ridB : ReplacementId := { kind := .replaceDraw, player := some p1 }

  -- 1a(i). `SacrificeDiscard.sacrificeForActivation`: resolution-cast spell with mandatory sacrifice
  --        and a settling continuation on `outerPendingReplacements` must NOT stall with `pending == .none`
  --        and undrained `outerPendingReplacements`!
  let sacResSpellDef : CardDef := {
    name := "P56i1 SacResSpell"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some {
      effect := Effect.gainLife 1
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.sacrificePermanents 1)]
    }
  }
  let gSacRes0 :=
    insertObject (addPermanent (emptyHand g4 p0) bear p0 p0) sacResSpellDef p0 .exile
  let sacFodderId := (gSacRes0.permanentsOf p0)[0]!.id
  let sacSpellExId := (gSacRes0.objects.filter (·.zone == .exile)).back!.id
  let gSacResMana :=
    (gSacRes0.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
      }
    ]).castAsPartOfResolution p0 sacSpellExId
  let gSacResCast := mustApply gSacResMana p0 .pay
  let gSacResDone := mustApply gSacResCast p0 (.sacrifice sacFodderId)
  let sacResOuterOk :=
    (match gSacResCast.pending with | .sacrificePermanent q _ => q == p0 | _ => false) &&
    gSacResDone.pending == .none &&
    gSacResDone.outerPendingReplacements.isEmpty &&
    gSacResDone.priority == p2 &&
    gSacResDone.stack.size == 1

  -- 1a(ii). `Event.lean` `isPurePriorityGrantLeaf` / `insertBeforeTrailingPriorityGrant` on mutating
  --         continuations, right-nested `.seq` tails, and `prevPending == .none` mana-ability + pure post-log tail:
  let dummyLog : PendingReplacement := .finishPostStep (.logExpiredPlayFromExile #[⟨99⟩] 0)
  let mutatingNotPure : Bool :=
    !PendingReplacement.finishResolutionChoice.isPurePriorityGrantLeaf &&
    !PendingReplacement.beginTurnAfterStartExpiry.isPurePriorityGrantLeaf &&
    !PendingReplacement.finishCleanupAfterClearEot.isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep .cleanupStepAfterDiscard).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep (.postSbaCleanup false)).isPurePriorityGrantLeaf &&
    !(PendingReplacement.beginStepCont .cleanup).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep (.beginStepBody .cleanup)).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep (.beginStepAfterPhaseBegan .cleanup)).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishConcede false none none none false #[] none).isPurePriorityGrantLeaf &&
    !(PendingReplacement.concedePlayersLoop #[p1] false false false none none none false #[]).isPurePriorityGrantLeaf &&
    (PendingReplacement.receivePriority p0).isPurePriorityGrantLeaf &&
    PendingReplacement.afterWardResolved.isPurePriorityGrantLeaf &&
    (PendingReplacement.beginStepCont .precombatMain).isPurePriorityGrantLeaf
  -- Right-nested `.seq` tail inserts BEFORE the FIRST pure priority grant:
  let rightNested : PendingReplacement :=
    .seq (.gainLife p0 1 (some testCause)) (.seq (.receivePriority p1) (.receivePriority p2))
  let rightInserted := rightNested.insertBeforeTrailingPriorityGrant dummyLog
  let rightInsertOk :=
    rightInserted ==
      .seq (.seq (.gainLife p0 1 (some testCause)) dummyLog) (.seq (.receivePriority p1) (.receivePriority p2))
  -- Mutating `.finishResolutionChoice` puts `dummyLog` AFTER it (not before):
  let frcInserted := PendingReplacement.finishResolutionChoice.insertBeforeTrailingPriorityGrant dummyLog
  let frcInsertOk := frcInserted == .seq .finishResolutionChoice dummyLog
  -- `prevPending == .none` mana-ability leaf followed by a pure post-log tail grants priority at runtime & in probes:
  let gManaLog0 := addPermanent g4 forest p1 p1
  let mForestId := (gManaLog0.permanentsOf p1)[0]!.id
  let manaPicksLeaf : PendingReplacement :=
    .finishActivateManaAbilityPicks p1 mForestId forest.name #[.colored .green] #[] #[] false false none none 0 false .none
  let manaPlusPostLog : PendingReplacement := .seq manaPicksLeaf (.logMessage "after-mana")
  let gManaLogRun := gManaLog0.resumePendingReplacement manaPlusPostLog
  let manaPostLogOk :=
    gManaLog0.continuationGrantsPriority false manaPlusPostLog &&
    gManaLog0.continuationSettlesControlFlow false manaPlusPostLog &&
    gManaLog0.priorityRecipientOfContinuation? false manaPlusPostLog == some p1 &&
    gManaLogRun.playersReceivePriority &&
    gManaLogRun.priority == p1 &&
    gManaLogRun.log.contains "after-mana"

  -- 1a(iii). `.seq` `rewindProposal` & `.leavePlayersWhoLost` runtime-vs-probe parity:
  let sorc1Def : CardDef := {
    name := "P56i1 Sorc1"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gSeqRev0 :=
    insertObject (addPermanent (emptyHand g4 p0) forest p0 p0) sorc1Def p0 (.hand p0)
  let seqForestId := (gSeqRev0.permanentsOf p0)[0]!.id
  let gSeqRevProp0 := mustApply gSeqRev0 p0 (.cast (gSeqRev0.player p0).hand.back!)
  let (gSeqRevProp1, _) := gSeqRevProp0.move seqForestId .exile none (cause := some testCause)
  let gSeqRevProp := gSeqRevProp1.change (.pending .none)
  -- (a) `.restorePending` with `rewindProposal := some false` does NOT drop trailing `.receivePriority p2`:
  let restoreWithRewind : PendingReplacement :=
    .seq (.restorePending (.activateManaAbilities p0) false (rewindProposal := some false)) (.receivePriority p2)
  let gRestoreWithRewindRun := gSeqRevProp.resumePendingReplacement restoreWithRewind
  -- (b) `.leavePlayersWhoLost` clearing a lost player's proposal does NOT drop trailing `.receivePriority p3`:
  let gLeaveProp0 := gSeqRevProp.record (GameEvent.playerLost gSeqRevProp.turnNumber p0 .lifeZeroOrLess)
  let leaveThenPrio : PendingReplacement :=
    .seq (.leavePlayersWhoLost none false #[] none) (.receivePriority p3)
  let gLeaveThenPrioRun := gLeaveProp0.resumePendingReplacement leaveThenPrio
  let seqRewindAndLeaveParityOk :=
    gSeqRevProp.continuationGrantsPriority false restoreWithRewind &&
    gSeqRevProp.priorityRecipientOfContinuation? false restoreWithRewind == some p2 &&
    gRestoreWithRewindRun.priority == p2 &&
    gLeaveProp0.continuationGrantsPriority false leaveThenPrio &&
    gLeaveProp0.priorityRecipientOfContinuation? false leaveThenPrio == some p3 &&
    gLeaveThenPrioRun.priority == p3

  -- 1a(iv). `Casting.afterWardResolved` does NOT chain duplicate `.afterWardResolved` behind
  --         `.receivePriority p2` (no duplicate `PriorityEvent.received` / priority theft to `p0`):
  let gWardPrio0 :=
    g4.changes #[
      .pushContinuationFrame { pendingReplacement := some (.receivePriority p2) },
      .pending (.payWard p1 ⟨999⟩ CostSpec.discardCard)
    ]
  let gWardPrio1 := gWardPrio0.afterWardResolved
  let gWardPrioDone := gWardPrio1.drainPendingContinuations
  let prioEvs :=
    (gWardPrioDone.events.extract gWardPrio0.events.size gWardPrioDone.events.size).filter fun e =>
      match e.change with | .engine (.priority _) => true | _ => false
  let afterWardNoDupOk :=
    gWardPrio1.pendingReplacement == some (.receivePriority p2) &&
    gWardPrioDone.priority == p2 &&
    prioEvs.size == 1 &&
    ((g4.changes #[
      .pushContinuationFrame { pendingReplacement := some (.finishDrawThenBeginDiscard p0 1) },
      .pending (.payWard p1 ⟨999⟩ CostSpec.discardCard)
    ]).afterWardResolved).pendingReplacement == some (.finishDrawThenBeginDiscard p0 1) &&
    ((g4.changes #[
      .pushContinuationFrame { pendingReplacement := some (.finishBeginRecruit p0) },
      .pending (.payWard p1 ⟨999⟩ CostSpec.discardCard)
    ]).afterWardResolved).pendingReplacement == some (.finishBeginRecruit p0)

  -- 1a(v). `drainProbeNonPriorityCont` resumes `.logMessage` and `.finishPostStep .markNonManaCostPaid`
  --        (no longer leaving them stuck in `pendingReplacement`):
  let gLogDrain0 :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.logMessage "probe-log") (.finishPostStep .markNonManaCostPaid))),
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]
  let gLogDrainProbe :=
    gLogDrain0.change (.pendingReplacement (some (.seq (.logMessage "probe-log") (.receivePriority p2))))
  let drainUnhandledLeavesOk :=
    !gLogDrain0.anyContinuationGrantsPriority &&
    gLogDrainProbe.anyContinuationGrantsPriority &&
    gLogDrainProbe.firstContinuationPriorityGrant? == some (some p2)

  -- 1b(i). CR 117.3c priority-recipient parity:
  --        - `Casting.completeTurnFaceUp` saves `pendingPriority := some p1` for non-active `caster := p1`
  --          when `pendingPriority.isNone` and a settling continuation / `.finishResolutionChoice` exists;
  --        - `finishPostCastOutcome` maps implicit `some none` to `caster` when `pendingPriority.isNone`;
  --        - `classifyFinishProposedSpellCosts` finds dynamic explicit grant in `outerPendingReplacements`
  --          and in non-`endsWithPriorityGrant` `localOuter?` writing `pendingPriority` / chaining grants!
  let morphDef : CardDef := {
    creature "P56i1 Morph" ManaCost.empty #["Human"] 3 3 with
    keywords := #[.morph CostSpec.empty]
  }
  let gTfu0 := addPermanent g4 morphDef p1 p1
  let tfuId := (gTfu0.permanentsOf p1)[0]!.id
  let gTfuFd :=
    (setFaceDown gTfu0 tfuId true).changes #[
      .pushContinuationFrame { pendingReplacement := some (.gainLife p0 1 (some testCause)) }
    ]
  let (gTfuDone, _) := gTfuFd.completeTurnFaceUp p1 tfuId
  let tfuProp : ProposedSpell := {
    caster := p1, cost := ManaCost.empty, spellId := tfuId, sourceId := some tfuId,
    original := gTfuFd.object! tfuId, originalSnapshot := gTfuFd.snapshot (gTfuFd.object! tfuId),
    kind := .turnFaceUp
  }
  let gFpscDyn0 :=
    (setFaceDown gTfu0 tfuId true).changes #[
      .saveProposalCheckpoint,
      .proposedSpell (some tfuProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.gainLife p0 1 (some testCause))
      }
    ]
  let gFpscDynRun :=
    match gFpscDyn0.finishProposedSpellCosts .finalize true false false with
    | .ok g => g
    | .error e => panic! s!"gFpscDynRun failed: {e}"
  -- Non-`endsWithPriorityGrant` `localOuter?` leaves (`.finishTurnFaceUp _ _ true` and `.completeActivation true _`):
  let gFpscLocalDyn0 :=
    (setFaceDown gTfu0 tfuId true).changes #[
      .saveProposalCheckpoint,
      .proposedSpell (some tfuProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.finishTurnFaceUp p1 tfuId true)
      }
    ]
  let gFpscLocalDynRun :=
    match gFpscLocalDyn0.finishProposedSpellCosts .finalize true false false with
    | .ok g => g
    | .error e => panic! s!"gFpscLocalDynRun failed: {e}"
  let gFpscActDyn0 :=
    (setFaceDown gTfu0 tfuId true).changes #[
      .saveProposalCheckpoint,
      .proposedSpell (some tfuProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p3]
        pendingReplacement := some (.completeActivation true false)
      }
    ]
  let gFpscActDynRun :=
    match gFpscActDyn0.finishProposedSpellCosts .finalize true false false with
    | .ok g => g
    | .error e => panic! s!"gFpscActDynRun failed: {e}"
  let gPostCastImp0 :=
    g4.changes #[
      .pushContinuationFrame { pendingReplacement := some .finishResolutionChoice }
    ]
  let gManaImp0 :=
    gManaLog0.changes #[
      .pushContinuationFrame { pendingReplacement := some .finishResolutionChoice }
    ]
  let cr1173cParityOk :=
    gTfuDone.priority == p1 &&
    gFpscDynRun.priority == p2 &&
    gFpscDyn0.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p2 &&
    !PendingReplacement.endsWithPriorityGrant (.finishTurnFaceUp p1 tfuId true) &&
    gFpscLocalDynRun.priority == p2 &&
    gFpscLocalDyn0.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p2 &&
    !PendingReplacement.endsWithPriorityGrant (.completeActivation true false) &&
    gFpscActDynRun.priority == p3 &&
    gFpscActDyn0.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p3 &&
    gPostCastImp0.priorityRecipientOfContinuation? false (.finishPostCast p1 true false false) == some p1 &&
    gManaImp0.priorityRecipientOfContinuation? false manaPicksLeaf == some p1

  -- 1b(ii). `firstContinuationPriorityGrant?` / `anyContinuationGrantsPriority` blocking-head stop
  --         and `.seq` no-op settling `a` guard + left-nested `suppressesPostCastFinish`:
  let gBlockHead :=
    g4.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.restorePending (.chooseTargets p0) false)
      }
    ]
  let seqNoopSettling : PendingReplacement := .seq (.beginStepCont .declareAttackers) (.receivePriority p2)
  let leftNestedPostCast : PendingReplacement :=
    .seq (.seq (.finishPostCast p1 false false false) (.logMessage "after")) (.receivePriority p3)
  let queueAndSeqProbesOk :=
    gBlockHead.firstContinuationPriorityGrant? == none &&
    !gBlockHead.anyContinuationGrantsPriority &&
    gBlockHead.anyContinuationSettlesControlFlow &&
    !g4.continuationGrantsPriority false seqNoopSettling &&
    g4.continuationSettlesControlFlow false seqNoopSettling &&
    g4.continuationSettlesControlFlow false (.finishDrawThenBeginDiscard p0 1) &&
    g4.continuationSettlesControlFlow false (.finishBeginRecruit p0) &&
    g4.continuationSettlesControlFlow false (.shuffleThen p0 .none) &&
    g4.priorityRecipientOfContinuation? false leftNestedPostCast == some p3

  -- 1b(iii). Interpreter `outerCont?` ordering (`reattachOuterCont` pushes `outer` onto
  --          `outerPendingReplacements` when `currentInterpWait?.isSome` so interpreter runs FIRST),
  --          in-game `putCardsOnBottom` non-mulligan cause, and `supplyOrder` `.orderInto` pause deferral:
  let gInterpOuter0 :=
    g4.changes #[
      .pushContinuationFrame {
        resolvingContext := some (none, p0)
        interpWait? := some { ctx := { controller := p0 }, queue := #[Instruction.gainLifeFixed 4], stack := #[] }
        pendingReplacement := some (.restorePending (.scry p0 1))
      },
      .pending (.mayResolve p0)
    ]
  let gInterpOuter1 := mustApply gInterpOuter0 p0 .decline
  let gInGameBot0 :=
    (insertObject (emptyHand g4 p0) bear p0 (.hand p0)).changes #[
      .pushContinuationFrame {
        resolvingContext := some (none, p0)
        interpWait? := some { ctx := { controller := p0 }, queue := #[Instruction.gainLifeFixed 2], stack := #[] }
        pendingReplacement := some (.restorePending (.scry p0 1))
      },
      .pending (.putOnBottom p0 1)
    ]
  let inGameBotId := (gInGameBot0.player p0).hand[0]!
  let gInGameBot1 := mustApply gInGameBot0 p0 (.putOnBottom #[inGameBotId])
  let botMoveCauseNotMulligan :=
    (gInGameBot1.events.extract gInGameBot0.events.size gInGameBot1.events.size).all fun ev =>
      match ev.change with
      | .rules (.zone (.moved _ _ (.hand _) (.library _) _ _ _ _)) =>
        ev.cause? != some (.gameRule .mulligan)
      | _ => true
  -- `supplyOrder` `.orderInto` pausing on `.chooseReplacement` defers `afterRandom` until after replacement:
  let ordReplA : ReplacementId := { kind := .exileOppDeath, player := some p1 }
  let ordReplB : ReplacementId := { kind := .exileOppDeath, player := some p2 }
  let gOrdPause0 := addPermanent g4 bear p0 p0
  let ordBearId := (gOrdPause0.permanentsOf p0)[0]!.id
  let gOrdPause1 :=
    ((gOrdPause0.createEffect (.replacement {
        id := ordReplA, controller := some p1, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some ordBearId) false }) (cause := some testCause)).createEffect
      (.replacement {
        id := ordReplB, controller := some p2, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some ordBearId) false }) (cause := some testCause)).changes #[
      .pushContinuationFrame { afterRandom := .gainLife p0 3 },
      .pending (.resolveRandom (.orderInto #[ordBearId] (.graveyard p0) (some testCause)))
    ]
  let gOrdPaused := mustApply gOrdPause1 p0 (.supplyOrder #[ordBearId])
  let gOrdDone := mustApply gOrdPaused p0 (.chooseReplacement ordReplA)
  let interpOuterAndBotOk :=
    (gInterpOuter1.player p0).life == (g4.player p0).life + 4 &&
    gInterpOuter1.pending == .scry p0 1 &&
    (gInGameBot1.player p0).life == (g4.player p0).life + 2 &&
    gInGameBot1.pending == .scry p0 1 &&
    botMoveCauseNotMulligan

  mustHold56i1 "1a_sacResOuter" sacResOuterOk &&
  mustHold56i1 "1a_eventPureLeafAndInsert" (mutatingNotPure && rightInsertOk && frcInsertOk && manaPostLogOk) &&
  mustHold56i1 "1a_seqRewindAndLeaveParity" seqRewindAndLeaveParityOk &&
  mustHold56i1 "1a_afterWardNoDup" afterWardNoDupOk &&
  mustHold56i1 "1a_drainUnhandledLeaves" drainUnhandledLeavesOk &&
  mustHold56i1 "1b_cr1173cParity" cr1173cParityOk &&
  mustHold56i1 "1b_queueAndSeqProbes" queueAndSeqProbesOk &&
  mustHold56i1 "1b_interpOuterAndBot" interpOuterAndBotOk &&
  mustHold56i1 "1b_ordPausedPending" (match gOrdPaused.pending with | .chooseReplacement q _ => q == p0 | _ => false) &&
  mustHold56i1 "1b_ordPausedNoLifeYet" ((gOrdPaused.player p0).life == (g4.player p0).life) &&
  mustHold56i1 "1b_ordDoneLife" ((gOrdDone.player p0).life == (g4.player p0).life + 3) &&
  mustHold56i1 "1.replay"
    (replayOk56i1 #[gSacResDone, gManaLogRun, gRestoreWithRewindRun, gLeaveThenPrioRun,
      gWardPrioDone, gTfuDone, gFpscDynRun, gInterpOuter1, gInGameBot1, gOrdPaused, gOrdDone])

end Phase56Item1EventAlignment

/-! ### Phase 56 Item 2: `Leaving.clearAbortedSavedInCont` `fromEventIdx?`, `Core.hasPlayFromExileLoggedInSlice`
ghost-`pending` & clamped `ambigLogs`, `Core.emitExpiredPlayFromExileLogs` outer-frame placement,
paused `.move`/`.destroyPermanent`/`.endControlExileLoop`/`.checkSBA` & `StateBasedActions` deferral,
`chooseLegend` & `sacrificePermanentsLoop` deferral, and `.control`/`.copy` CR 800.4c log order -/
section Phase56Item2EventAlignment

private def mustHold56i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase56Item2EventAlignment failed: {label}"

private def replayOk56i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let bearExpMsg := s!"{bear.name} can no longer be played from exile"
  let countBearExpLogs (g : Game) := (g.log.filter (· == bearExpMsg)).size
  let mayCastFromExileDef : CardDef := {
    bear with
    name := "P56i2 CastFromExileSrc"
    staticAbilities := #[.ruleModifying none (.play (.mayPlayFrom .you .exile .anyObject true true false false))]
  }

  -- 2a(i). `Leaving.clearAbortedSavedInCont` preserves `fromEventIdx?` across `.leavePlayersWhoLost`,
  --        `.finishConcede`, and `.concedePlayersLoop` when a paused leave is joined by an aborting departure:
  let gClrBase := insertObject g4 bear p1 .stack (some p1)
  let clrSpell := (gClrBase.objects.filter (·.zone == .stack)).back!
  let clrProp : ProposedSpell := {
    caster := p1, cost := ManaCost.empty, spellId := clrSpell.id,
    original := clrSpell, originalSnapshot := gClrBase.snapshot clrSpell
  }
  let gClr0 :=
    gClrBase.changes #[
      .proposedSpell (some clrProp),
      .pushContinuationFrame {
        pendingReplacement := some (.seq
          (.leavePlayersWhoLost (some (.chooseX p1)) false #[] none (some 7))
          (.finishConcede false none none (some (.chooseX p1)) false #[] none (some 5)))
        outerPendingReplacements := #[
          .concedePlayersLoop #[p3] false false false none none (some (.chooseX p1)) false #[] none (some 3)
        ]
      },
      .pending (.scry p2 1)
    ]
  -- `p1` conceding aborts `p1`'s proposal while leaving `p2`'s `.scry` pending, preserving `some 7`, `some 5`, `some 3`:
  let gClr1 := mustApply gClr0 p1 .concede
  let clearPreservesIdxOk :=
    (gClr1.player p1).leftTheGame &&
    gClr1.pending == .scry p2 1 &&
    (match gClr1.pendingReplacement with
     | some (.seq (.leavePlayersWhoLost none false _ _ (some 7))
                  (.finishConcede _ _ _ none _ _ _ (some 5))) => true
     | _ => false) &&
    (match (gClr1.outerPendingReplacements[0]? : Option PendingReplacement) with
     | some (.concedePlayersLoop _ _ _ _ _ _ none _ _ _ (some 3)) => true
     | _ => false)

  -- 2a(ii). `Core.hasPlayFromExileLoggedInSlice`:
  --         (a) Exiled card `idA` whose permission expired then left exile is pruned from `pending`,
  --             so sibling same-named `idB` does not inflate `elig.size ≥ 2` and emit a duplicate log;
  --         (b) Ambiguous group `#[idA, idB, idC]` with 2 logs where `idA` receives a new `.playFromExile`
  --             clamps `ambigLogs` to `1 < 2`, so `idB`/`idC` still get logged instead of falsely suppressed.
  let gGhost0 := insertObject (insertObject g4 bear p0 .exile) bear p0 .exile
  let ghostIds := (gGhost0.objects.filter (·.zone == .exile)).map (·.id)
  let gIdA := ghostIds[0]!
  let gIdB := ghostIds[1]!
  let gGhost1 :=
    (gGhost0.createEffect (.permission (some p0) (.playFromExile gIdA { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile gIdB { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let gEidA := gGhost1.activeEffects[gGhost1.activeEffects.size - 2]!.1
  let gEidB := gGhost1.activeEffects[gGhost1.activeEffects.size - 1]!.1
  -- Expire `idA` without logging, move `idA` out of exile to hand, then expire & log `idB`:
  let gGhost2 := (gGhost1.expireEffectById gEidA (cause := some testCause)).move gIdA (.hand p0) none (cause := some testCause) |>.1
  let ghostSlice := gGhost2.events.size
  let gGhost3 := (gGhost2.expireEffectById gEidB (cause := some testCause)).logMsg bearExpMsg
  let gGhost4 := gGhost2.emitExpiredPlayFromExileLogs gGhost3 ghostSlice
  -- Ambiguous shrink clamp:
  let gAmb0 := insertObject (insertObject (insertObject g4 bear p0 .exile) bear p0 .exile) bear p0 .exile
  let ambIds := (gAmb0.objects.filter (·.zone == .exile)).map (·.id)
  let a1 := ambIds[0]!; let a2 := ambIds[1]!; let a3 := ambIds[2]!
  let gAmb1 :=
    ((gAmb0.createEffect (.permission (some p0) (.playFromExile a1 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile a2 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile a3 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let ae1 := gAmb1.activeEffects[gAmb1.activeEffects.size - 3]!.1
  let ae2 := gAmb1.activeEffects[gAmb1.activeEffects.size - 2]!.1
  let ae3 := gAmb1.activeEffects[gAmb1.activeEffects.size - 1]!.1
  let ambStart := gAmb1.events.size
  let gAmb2 :=
    ((((gAmb1.expireEffectById ae1 (cause := some testCause)).expireEffectById ae2 (cause := some testCause)).expireEffectById
      ae3 (cause := some testCause)).logMsg bearExpMsg).logMsg bearExpMsg
  -- Reactivating `a1` shrinks `ambigGroup` from 3 to 2 and decrements `ambigLogs` from 2 to 1 (< 2),
  -- so calling `emitExpiredPlayFromExileLogs` for `a2`/`a3` still logs the missing 3rd card:
  let gAmb3 := gAmb2.createEffect (.permission (some p0) (.playFromExile a1 { player := p0 }) .untilEndOfTurn)
    (cause := some testCause)
  let gAmb4 := gAmb1.emitExpiredPlayFromExileLogs gAmb3 ambStart
  -- Unambiguous `elig.size == 1` log for `a1` while `{a2, a3}` temporarily regain playability via
  -- `mayCastExiledBySource` decrements `ambigLogs` from 2 to 1 (< 2) instead of retiring `{a2, a3}`:
  let gAmbSingleBase := addPermanent gAmb2 mayCastFromExileDef p0 p0
  let ambSrcId := (gAmbSingleBase.permanentsOf p0).back!.id
  let gAmbSingle1 :=
    (((gAmbSingleBase.changeObject a2 (.exiledBy (some ambSrcId))).changeObject a3 (.exiledBy (some ambSrcId))).logMsg
      bearExpMsg).move ambSrcId (.graveyard p0) none (cause := some testCause) |>.1
  let gAmbSingle2 := gAmb1.emitExpiredPlayFromExileLogs gAmbSingle1 ambStart
  let hasLoggedGhostAndClampOk :=
    countBearExpLogs gGhost4 == 1 &&
    countBearExpLogs gAmb4 == 3 &&
    countBearExpLogs gAmbSingle2 ≥ 4

  -- 2a(iii). `Core.emitExpiredPlayFromExileLogs` places `deferCont` onto the BOTTOMMOST outer frame
  --          containing pending non-priority work even while paused on `.chooseReplacement`:
  let gOutPlaceBase := insertObject (addPermanent g4 mayCastFromExileDef p0 p0) bear p0 .exile
  let outMayCastId := (gOutPlaceBase.permanentsOf p0).back!.id
  let outExId := (gOutPlaceBase.objects.filter (·.zone == .exile)).back!.id
  let gOutPlace0 := gOutPlaceBase.changeObject outExId (.exiledBy (some outMayCastId))
  let gOutPlace1 :=
    gOutPlace0.createEffect (.permission (some p0) (.playFromExile outExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let outEid := gOutPlace1.activeEffects.back!.1
  let outStart := gOutPlace1.events.size
  let bottomWork : PendingReplacement := .endControlExileLoop #[] testCause none #[] (some outStart) false
  let gOutPlacePaused :=
    (gOutPlace1.expireEffectById outEid (cause := some testCause)).changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[bottomWork, .receivePriority p1]
        pendingReplacement := some (.gainLife p0 1 (some testCause))
      },
      .pending (.chooseReplacement p0 #[])
    ]
  let gOutPlaceDef := gOutPlace1.emitExpiredPlayFromExileLogs gOutPlacePaused outStart
  let outerPlaceOk :=
    gOutPlaceDef.outerPendingReplacements.size == 2 &&
    (gOutPlaceDef.outerPendingReplacements[0]!).containsDeferredPlayFromExile outExId &&
    !(gOutPlaceDef.outerPendingReplacements[1]!).containsDeferredPlayFromExile outExId &&
    !gOutPlaceDef.pendingReplacement.any (·.containsDeferredPlayFromExile outExId)

  -- 2b(i)–(ii). Simultaneous `sacrificePermanentsLoop` & `chooseLegend` `.playFromExile` deferral
  --             when a `.playFromExile` source moves BEFORE a `mayCastExiledBySource` permanent in the same batch:
  let gSacLoopBase := insertObject (addPermanent (addPermanent g4 bear p0 p0) mayCastFromExileDef p0 p0) bear p0 .exile
  let sacSrcId := (gSacLoopBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let sacMayCastId := (gSacLoopBase.permanentsOf p0).find? (·.name == mayCastFromExileDef.name) |>.get!.id
  let sacExId := (gSacLoopBase.objects.filter (·.zone == .exile)).back!.id
  let gSacLoop0 := gSacLoopBase.changeObject sacExId (.exiledBy (some sacMayCastId))
  let gSacLoop1 :=
    gSacLoop0.createEffect
      (.permission (some p0) (.playFromExile sacExId { player := p0 }) (.whileSourceOnBattlefield sacSrcId))
      (cause := some testCause)
  let gSacLoopDone :=
    gSacLoop1.sacrificePermanentsLoop #[(p0, sacSrcId), (p0, sacMayCastId)] (cause := some testCause)
  let legCastExDef : CardDef := { mayCastFromExileDef with supertypes := #[.legendary] }
  let gLegDefBase :=
    insertObject (addPermanent (addPermanent (addPermanent g4 legCastExDef p0 p0) legCastExDef p0 p0) legCastExDef p0 p0)
      bear p0 .exile
  let legIds := (gLegDefBase.permanentsOf p0).map (·.id)
  let legExId := (gLegDefBase.objects.filter (·.zone == .exile)).back!.id
  let gLegDef0 := gLegDefBase.changeObject legExId (.exiledBy (some legIds[2]!))
  -- `legIds[1]!` moves first while `legIds[2]!` still grants `mayCastExiledBySource`, then `legIds[2]!` moves too;
  -- keeping `legIds[0]!` (not `exiledBy` source) makes `legExId` unplayable ONLY after the simultaneous batch completes!
  let gLegDef1 :=
    gLegDef0.createEffect
      (.permission (some p0) (.playFromExile legExId { player := p0 }) (.whileSourceOnBattlefield legIds[1]!))
      (cause := some testCause)
  let gLegDefSba := gLegDef1.checkSBA
  let gLegDefDone := mustApply gLegDefSba p0 (.keepLegend legIds[0]!)
  let sacAndLegendDeferOk :=
    countBearExpLogs gSacLoopDone == 1 &&
    countBearExpLogs gLegDefDone == 1

  -- 2b(iii). `.control` / `.copy` CR 800.4c co-departing reconciliation log order:
  --          `restoreControlUntilSourceLeaves` and `restoreCopiesWhere` skip spurious return/copy-end logs
  --          for co-departing CR 800.4c permanents, while logging non-co-departing copy ends BEFORE exile!
  let relicDef : CardDef := { name := "P56i2 Relic", types := #[.artifact] }
  let gCoDep0 := addPermanent (addPermanent (addPermanent g4 bear p0 p0) hero p0 p2) bear p1 p1
  let cdSrcId := (gCoDep0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let cdPermId := (gCoDep0.permanentsOf p2).find? (·.name == hero.name) |>.get!.id
  -- `cdPermId` entered owned by `p0` under `p2`'s control (`defaultController := p2`), is controlled by `p1`
  -- while `cdSrcId` is on the battlefield, and survives `p2`'s concession:
  let gCoDep1 :=
    mustApply
      (gCoDep0.createEffect (.layered (.objects #[cdPermId]) (.control p1) (.whileSourceOnBattlefield cdSrcId))
        (cause := some testCause))
      p2 .concede
  let logBeforeCtrl := gCoDep1.log.size
  let gCoDepCtrlDone := gCoDep1.restoreControlUntilSourceLeaves cdSrcId (reconcileControl := true)
  let ctrlNewLogs := gCoDepCtrlDone.log.extract logBeforeCtrl gCoDepCtrlDone.log.size
  let noSpuriousReturnLog :=
    !ctrlNewLogs.any (fun s => s.contains hero.name && s.contains "returns to") &&
    (gCoDepCtrlDone.findObject? (gCoDepCtrlDone.followMoved cdPermId)).any (·.zone == .exile)
  -- `restoreCopiesWhere`: `cdKeepId` (stays on battlefield) logs copy-end BEFORE `cdRelicId` is exiled under CR 800.4c,
  -- while co-departing `cdRelicId` emits NO spurious `"is no longer a copy"` log:
  let cloneCard : CardDef := { bear with name := "P56i2 ClonedFace" }
  let gCoCopyBase := addPermanent (addPermanent g4 relicDef p0 p2) bear p1 p1
  let cdRelicId := (gCoCopyBase.permanentsOf p2)[0]!.id
  let cdKeepId := (gCoCopyBase.permanentsOf p1)[0]!.id
  let gCoCopy0 :=
    mustApply
      ((gCoCopyBase.createEffect (.layered (.objects #[cdRelicId, cdKeepId]) (.copy cloneCard) .untilEndOfTurn)
        (cause := some testCause)).createEffect
        (.layered (.creaturesWithout #[Keyword.flying]) (.control p1) .indefinite)
        (cause := some testCause))
      p2 .concede
  let logBeforeCopy := gCoCopy0.log.size
  let gCoCopyDone :=
    gCoCopy0.restoreCopiesWhere (fun _ _ _ d => d == .untilEndOfTurn)
      (cause := some testCause) (reconcileControl := true)
  let copyNewLogs := gCoCopyDone.log.extract logBeforeCopy gCoCopyDone.log.size
  let copyEndIdx? := copyNewLogs.findIdx? (fun s => s.contains "is no longer a copy")
  let exileIdx? := copyNewLogs.findIdx? (fun s => s.contains "exiled")
  let restoreCopyOrderOk :=
    (match copyEndIdx?, exileIdx? with
     | some ci, some ei => ci < ei
     | _, _ => false) &&
    (copyNewLogs.filter (fun s => s.contains "is no longer a copy")).size == 1 &&
    (gCoCopyDone.findObject? (gCoCopyDone.followMoved cdRelicId)).any (·.zone == .exile)

  -- `expireEffectById` `.commandEmblem` skips spurious copy-end & control-return logs for CR 800.4c co-departing:
  let embDef : CardDef := { name := "P56i2 Emb", types := #[] }
  let gEmbCo0 := insertObject (addPermanent g4 hero p0 p2) embDef p1 .command (some p1)
  let embCoPermId := (gEmbCo0.permanentsOf p2)[0]!.id
  let embCoId := (gEmbCo0.objects.filter (·.zone == .command)).back!.id
  let gEmbCo1 :=
    mustApply
      (((gEmbCo0.createEffect (.gameRule (.commandEmblem embCoId) .untilEndOfTurn) (cause := some testCause)).createEffect
        (.layered (.objects #[embCoPermId]) (.control p1) (.whileInZone embCoId .command)) (cause := some testCause)).createEffect
        (.layered (.objects #[embCoPermId]) (.copy cloneCard) (.whileInZone embCoId .command)) (cause := some testCause))
      p2 .concede
  let embEid :=
    (gEmbCo1.activeEffects.find? fun (_, e) =>
      match e with | .gameRule (.commandEmblem id) _ => id == embCoId | _ => false).get!.1
  let logBeforeEmb := gEmbCo1.log.size
  let gEmbCoDone := gEmbCo1.expireEffectById embEid (cause := some testCause) (reconcileControl := true)
  let embNewLogs := gEmbCoDone.log.extract logBeforeEmb gEmbCoDone.log.size
  let embCoDepartOk :=
    !embNewLogs.any (fun s => s.contains "returns to" || s.contains "is no longer a copy") &&
    (gEmbCoDone.findObject? (gEmbCoDone.followMoved embCoPermId)).any (·.zone == .exile)

  -- Paused `.move` (`deferPlayFromExileLogs := true`) & `.checkSBA (some fromIdx)` deferral across `.chooseReplacement`:
  let sbaReplA : ReplacementId := { kind := .exileOppDeath, player := some p1 }
  let sbaReplB : ReplacementId := { kind := .exileOppDeath, player := some p2 }
  let gSbaPauseBase :=
    insertObject (addPermanent (addPermanent g4 bear p0 p0) mayCastFromExileDef p0 p0) bear p0 .exile
  let sbaSrcId := (gSbaPauseBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let sbaMayCastId := (gSbaPauseBase.permanentsOf p0).find? (·.name == mayCastFromExileDef.name) |>.get!.id
  let sbaExId := (gSbaPauseBase.objects.filter (·.zone == .exile)).back!.id
  let gSbaPause0 :=
    ((((gSbaPauseBase.changeObject sbaExId (.exiledBy (some sbaMayCastId))).createEffect
      (.permission (some p0) (.playFromExile sbaExId { player := p0 }) (.whileSourceOnBattlefield sbaSrcId))
      (cause := some testCause)).createEffect
      (.replacement {
        id := sbaReplA, controller := some p1, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some sbaSrcId) false }) (cause := some testCause)).createEffect
      (.replacement {
        id := sbaReplB, controller := some p2, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some sbaSrcId) false }) (cause := some testCause))
  let gSbaLethal :=
    let g1 := gSbaPause0.dealDamageToPermanent (gSbaPause0.object! sbaSrcId) 2 (cause := some testCause)
    g1.dealDamageToPermanent (g1.object! sbaMayCastId) 2 (cause := some testCause)
  let gSbaPaused := gSbaLethal.checkSBA
  let gSbaDone := mustApply gSbaPaused p0 (.chooseReplacement sbaReplA)
  let sbaPauseDeferOk :=
    (match gSbaPaused.pending with | .chooseReplacement q _ => q == p0 | _ => false) &&
    countBearExpLogs gSbaPaused == 0 &&
    countBearExpLogs gSbaDone == 1

  mustHold56i2 "2a_clearAbortedPreservesFromIdx" clearPreservesIdxOk &&
  mustHold56i2 "2a_hasLoggedGhostAndClamp" hasLoggedGhostAndClampOk &&
  mustHold56i2 "2a_emitOuterPlace" outerPlaceOk &&
  mustHold56i2 "2b_sacAndLegendDefer" sacAndLegendDeferOk &&
  mustHold56i2 "2b_sbaPauseDefer" sbaPauseDeferOk &&
  mustHold56i2 "2b_coDepartControlAndCopyOrder" (noSpuriousReturnLog && restoreCopyOrderOk && embCoDepartOk) &&
  mustHold56i2 "2.replay"
    (replayOk56i2 #[gClr1, gGhost4, gAmb4, gOutPlaceDef, gSacLoopDone, gLegDefDone,
      gCoDepCtrlDone, gCoCopyDone, gEmbCoDone, gSbaPaused, gSbaDone])

end Phase56Item2EventAlignment

/-! ### Phase 56 Item 3: `EventObject` designation LKI (`.prepared` / `.harnessed` / `.goaded` / `.ringBearer`),
protection completeness (source-less `.everything`, emblems, `replaceDamage` `srcEvent?`, resolving `.grantKeywords`),
Layer 5–6 evaluation (`Core.colors` face-down / CR 305.7 / `.modifyColors`, Layer-6 `hasKwExtra?`),
`Core.lkiCombatWindow` & `.turnHistory` / `lookBackState?`, and `.otherSpellsManaValueThisTurn` /
self-flash `nth?` / `faceManaValue` & `playPermissionFor?` / Layer-4–5 CDAs in timing & costs -/
section Phase56Item3EventAlignment

private def mustHold56i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase56Item3EventAlignment failed: {label}"

private def replayOk56i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := afterDraw

  -- 3a(i). `EventObject` designation LKI:
  --        - `entersPrepared` permanent (no `designation` event) snapshots `prepared := true` and survives
  --          `wasPreparedAtDeparture` / `viewHasDesignation` / `Damage.damageSourceFromSnapshot`;
  --        - `.harnessed`, `.goaded`, and `.ringBearer` (even AFTER `closeBatch` cleared `pl.ringBearerId`)
  --          are preserved on `EventObject` and read directly in `EvalExpr.viewHasDesignation`!
  let entersPrepDef : CardDef := {
    bear with
    name := "P56i3 EntersPrep"
    staticAbilities := #[.replacement none (.entersWithDesignation .prepared)]
  }
  let gDes0 := insertObject g0 entersPrepDef p0 (.hand p0)
  let (gDes1, epId) := gDes0.move (gDes0.player p0).hand.back! .battlefield (some p0) (cause := some testCause)
  let gDes2 :=
    ((gDes1.record (GameEvent.designation gDes1.turnNumber (gDes1.snapshot (gDes1.object! epId))
        .harnessed true (cause := testCause))).record
      (GameEvent.designation gDes1.turnNumber (gDes1.snapshot (gDes1.object! epId))
        (.goaded p1) true (cause := testCause))).record
      (GameEvent.designation gDes1.turnNumber (gDes1.snapshot (gDes1.object! epId))
        .ringBearer true (cause := testCause))
  let snapDes := gDes2.snapshot (gDes2.object! epId)
  let gDesLeft := gDes2.withBatch (some testCause) fun g =>
    (g.move epId (.graveyard p0) none (cause := some testCause)).1
  let lkiViewDes : ObjectView := .lki snapDes
  let desigLkiOk :=
    snapDes.prepared && snapDes.harnessed && snapDes.goaded && snapDes.ringBearer &&
    (gDesLeft.player p0).ringBearerId == none &&
    gDesLeft.wasPreparedAtDeparture epId &&
    EvalExpr.evalObjectPred gDesLeft { controller := p0 } lkiViewDes (.hasDesignation .prepared) &&
    EvalExpr.evalObjectPred gDesLeft { controller := p0 } lkiViewDes (.hasDesignation .harnessed) &&
    EvalExpr.evalObjectPred gDesLeft { controller := p0 } lkiViewDes (.hasDesignation .goaded) &&
    EvalExpr.evalObjectPred gDesLeft { controller := p0 } lkiViewDes (.hasDesignation .ringBearer) &&
    (Game.damageSourceObjectFromLki snapDes (prepared := snapDes.prepared)).status.prepared

  -- 3a(ii). Protection completeness:
  --         - `.protection .everything` blocks targeting with `sourceId == none`;
  --         - command-zone emblem granting `.player (.protectionFrom .you (.color (.literal .red)))` blocks
  --           both targeting AND damage;
  --         - `Damage.replaceDamage` permanent protection uses `srcEvent?` LKI fallback when `src? == none`;
  --         - resolving `.grantKeywords #[.protection (.color .chosenOnSource)]` resolves against granting source!
  let protAllBearDef : CardDef := {
    bear with name := "P56i3 ProtAllBear", keywords := #[.protection .everything]
  }
  let protRedBearDef : CardDef := {
    bear with name := "P56i3 ProtRedBear", keywords := #[.protection (.color (.literal .red))]
  }
  let redGobDef : CardDef := creature "P56i3 RedGob" { symbols := #[.colored .red] } #["Goblin"] 2 2
  let protRedEmblemDef : CardDef := {
    name := "P56i3 RedProtEmblem"
    types := #[]
    staticAbilities := #[.ruleModifying none (.player (.protectionFrom .you (.color (.literal .red))))]
  }
  let gProt0 :=
    addPermanent
      (addPermanent
        (addPermanent (insertObject g0 protRedEmblemDef p0 .command (some p0)) protAllBearDef p0 p0)
        protRedBearDef p0 p0)
      redGobDef p1 p1
  let protAllObj := (gProt0.permanentsOf p0).find? (·.name == protAllBearDef.name) |>.get!
  let protRedObj := (gProt0.permanentsOf p0).find? (·.name == protRedBearDef.name) |>.get!
  let redGobObj := (gProt0.permanentsOf p1)[0]!
  let redGobSnap := gProt0.snapshot redGobObj
  let gProt0PlayerAll := gProt0.createEffect (.protectionFromEverything p0) (cause := some testCause)
  -- Emblem prevents red damage to `p0`, and `srcEvent?` LKI prevents red damage to `protRedObj`:
  let gEmbDmg := gProt0.dealDamageToPlayer p0 3 (source := some redGobObj) (cause := some testCause)
  let (gRedGone, _) := gProt0.move redGobObj.id (.graveyard p1) none (cause := some testCause)
  let repLkiPerm :=
    gRedGone.replaceDamage 2 (src? := none) (srcEvent? := some redGobSnap)
      (recipientPerm? := some protRedObj) (cause := some testCause)
  let gLkiPermDmg :=
    gRedGone.dealDamageToPermanent protRedObj 2 (source := some redGobSnap)
      (cause := some testCause)
  -- Resolving `.grantKeywords #[.protection (.color .chosenOnSource)]` installs resolved `.literal .red`:
  let (gGrant0, grantSrc) := g0.allocObject bear p0 .battlefield (some p0) { chosenColor := some .red }
  let (gGrant1, grantTgt) := gGrant0.allocObject bear p0 .battlefield (some p0) { chosenColor := some .blue }
  let gGrant2 :=
    gGrant1.applyEffect p0
      { body := .installEffect (.applyContinuous .untilEndOfTurn (.inZones .battlefield (.sameAs (.target 0)))
          (.grantKeywords #[.protection (.color .chosenOnSource)])) }
      #[.permanent grantTgt.id] (sourceId := some grantSrc.id)
  let gGrant3 := addPermanent gGrant2 redGobDef p1 p1
  let protCompleteOk :=
    !gProt0.canBeTargetedBy p1 protAllObj none &&
    !gProt0PlayerAll.playerCanBeTargetedBy p1 p0 none &&
    !gProt0.playerCanBeTargetedBy p1 p0 (some redGobObj.id) &&
    (gEmbDmg.player p0).life == (gProt0.player p0).life &&
    repLkiPerm.amount == 0 &&
    (gLkiPermDmg.object! protRedObj.id).status.damage == (0 : Int) &&
    gGrant3.protectedFrom (gGrant3.object! grantTgt.id) (gGrant3.permanentsOf p1)[0]!

  -- 3a(iii). Layer 5–6 evaluation:
  --          - `Core.colors` applies Layer-5 color-changing effects to face-down permanents;
  --          - `Core.colors` skips color CDA when Layer-4 `strippedRulesTextByBasicLandSet` holds (CR 305.7);
  --          - `Core.colors` evaluates static `.modifyColors`;
  --          - Layer-6 `hasKwExtra?` checks ability-stripped Equipment (`false`) and Layer-6-granted Equip (`true`)!
  let colorStaticDef : CardDef := {
    name := "P56i3 PainterBlue"
    types := #[.artifact]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .hasType .creature }
        (.modifyColors { mode := .add, colors := { blue := true } })
    ]
  }
  let cdaGreenLandDef : CardDef := {
    name := "P56i3 GreenLandCda"
    types := #[.land]
    staticAbilities := #[.characteristicDefining (.setColors { green := true })]
  }
  let gL50 := addPermanent (addPermanent (addPermanent g0 bear p0 p0) colorStaticDef p0 p0) cdaGreenLandDef p0 p0
  let fdBearId := (gL50.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let cdaLandId := (gL50.permanentsOf p0).find? (·.name == cdaGreenLandDef.name) |>.get!.id
  let gL51 :=
    (setFaceDown gL50 fdBearId true).createEffect
      (.layered (.objects #[cdaLandId]) (.types .set #[] #[.mountain] #[]) .indefinite)
      (cause := some testCause)
  -- Layer-6 `hasKwExtra?` for Equip:
  let equipDef : CardDef := {
    name := "P56i3 Sword"
    types := #[.artifact]
    subtypes := #["Equipment"]
    keywords := #[.equip (.hasType .creature) (CostSpec.ofGeneric 2)]
  }
  let grantFlyToEquipDef : CardDef := {
    name := "P56i3 EquipFly"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .all #[.hasType .artifact, .hasKeyword (.param .equip)] }
        (.grantKeywords #[Keyword.flying])
    ]
  }
  let gL60 := addPermanent (addPermanent g0 equipDef p0 p0) grantFlyToEquipDef p0 p0
  let swordId := (gL60.permanentsOf p0).find? (·.name == equipDef.name) |>.get!.id
  let gL6Stripped :=
    gL60.createEffect (.layered (.objects #[swordId]) (.abilities {} .all) .indefinite)
      (cause := some testCause)
  let layer56Ok :=
    (gL51.colors (gL51.object! fdBearId)).contains .blue &&
    !(gL51.colors (gL51.object! cdaLandId)).contains .green &&
    gL60.hasFlying (gL60.object! swordId) &&
    !gL6Stripped.hasFlying (gL6Stripped.object! swordId)

  -- 3b(i). `Core.lkiCombatWindow` multi-turn `atkDepart` reset (Turn-1 `removedFromCombat` must NOT
  --        shadow Turn-3 `attackersDeclared`) & `Core.evalStaticCondL5` `.firstResolutionThisTurn`
  --        & `EvalExpr` `lookBackState?`:
  let gCbt0 := addPermanent g0 bear p0 p0
  let atkId := (gCbt0.permanentsOf p0)[0]!.id
  let atkSnap := gCbt0.snapshot (gCbt0.object! atkId)
  let atkSnapAtk := { atkSnap with attacking := true }
  let evsMultiTurn : Array GameEvent := #[
    GameEvent.attackersDeclared 1 p0 #[(atkSnap, .player p1)],
    GameEvent.removedFromCombat 1 atkSnapAtk (cause := testCause),
    GameEvent.attackersDeclared 3 p0 #[(atkSnap, .player p1)]
  ]
  let (wTurn, _, _, _) := Game.lkiCombatWindow evsMultiTurn atkId 3 none
  let gFirstRes1 :=
    gCbt0.record
      (GameEvent.resolved gCbt0.turnNumber p0 1 (gCbt0.snapshot (gCbt0.objects[0]!)) (sourceId := some atkId))
  let firstResCond : Condition := .turnHistory .firstResolutionThisTurn
  let gLbPre := g0
  let gLbPost := gLbPre.record (GameEvent.drew gLbPre.turnNumber p0 ⟨99⟩ 1 (cause := testCause))
  let drewCond : Condition := .turnHistory (.eventOccurredThisTurn .you (.drewCard 1))
  let combatAndHistoryOk :=
    wTurn == 3 &&
    gCbt0.evalTriggerCond p0 (some (gCbt0.object! atkId)) none firstResCond &&
    !gFirstRes1.evalTriggerCond p0 (some (gFirstRes1.object! atkId)) none firstResCond &&
    EvalExpr.evalCondition gLbPost { controller := p0 } drewCond &&
    !EvalExpr.evalCondition gLbPost { controller := p0, lookBackState? := some gLbPre } drewCond

  -- 3b(ii)–(iv). `.otherSpellsManaValueThisTurn` proposed-spell `ownFallback` guard, self-flash `nth?`,
  --              `faceManaValue` & `playPermissionFor?` Impending/Morph parity, and Layer-4/5 CDAs in timing/costs:
  let mv4SpellDef : CardDef := {
    name := "P56i3 Mv4", manaCost := ManaCost.ofGeneric 4, types := #[.sorcery],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gOwnFb0 :=
    (insertObject g0 mv4SpellDef p0 .stack (some p0)).record
      (GameEvent.spellCast g0.turnNumber p0 { name := "Anon3", manaValue := 3 } (.hand p0))
  let mv4Id := (gOwnFb0.objects.filter (·.zone == .stack)).back!.id
  let mv4Prop : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 4, spellId := mv4Id,
    original := gOwnFb0.object! mv4Id, originalSnapshot := gOwnFb0.snapshot (gOwnFb0.object! mv4Id)
  }
  let gOwnFbProp := gOwnFb0.change (.proposedSpell (some mv4Prop))
  let ownMvDuringProposal :=
    EvalExpr.evalValue gOwnFbProp { controller := p0, sourceId := some mv4Id }
      (.playerMetric .otherSpellsManaValueThisTurn .you)
  -- Self-flash `nth?` (only first spell each turn has flash):
  let selfFlashFirstDef : CardDef := {
    name := "P56i3 FirstFlash"
    manaCost := ManaCost.zero
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
    staticAbilities := #[.ruleModifying none (.play (.castAsThoughFlash .you .anyObject true (some 1)))]
  }
  let gOppTurn := (g0.record (GameEvent.turnBegan (g0.turnNumber + 1) p1)).receivePriority p0
  let gOppTurnCast1 :=
    gOppTurn.record (GameEvent.spellCast gOppTurn.turnNumber p0 { name := "Prior", manaValue := 1 } (.hand p0))
  -- Impending printed MV vs alternative cost & Morph MV 0 in `faceManaValue` / `playPermissionFor?`:
  let impCardDef : CardDef := {
    creature "P56i3 ImpCard" (ManaCost.ofGeneric 5) #["Avatar"] 5 5 with
    keywords := #[.impending 3 (CostSpec.ofGeneric 2)]
  }
  let morphCardDef : CardDef := {
    creature "P56i3 MorphCard" (ManaCost.ofGeneric 5) #["Human"] 4 4 with
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let gImpLowLife :=
    g0.loseLife p0 ((g0.player p0).life - 3).toNat (cause := some testCause)
  let gImpEx :=
    insertObject (insertObject gImpLowLife impCardDef p0 .exile) morphCardDef p0 .exile
  let impExObj := (gImpEx.objects.filter (·.name == impCardDef.name))[0]!
  let morphExObj := (gImpEx.objects.filter (·.name == morphCardDef.name))[0]!
  let gImpPerm :=
    (((gImpEx.createEffect
        (.permission (some p0) (.playFromExile impExObj.id { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
        (.permission (some p0) (.playFromExile impExObj.id { player := p0 }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
        (.permission (some p0) (.playFromExile morphExObj.id { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
        (.permission (some p0) (.playFromExile morphExObj.id { player := p0 }) .untilEndOfTurn)
        (cause := some testCause)
  let impFace := { impCardDef with manaCost := ManaCost.ofGeneric 2 }
  -- Layer-5 CDA green creature gets `pendingFreeRGCreature` cost reduction in `Costs.playManaCost`:
  let cdaGreenCreatDef : CardDef := {
    creature "P56i3 CdaGreenCreat" (ManaCost.ofGeneric 3) #["Beast"] 3 3 with
    staticAbilities := #[.characteristicDefining (.setColors { green := true })]
  }
  let gFreeRg :=
    (insertObject g0 cdaGreenCreatDef p0 (.hand p0)).createEffect
      (ContinuousEffectSpec.pendingFreeRGCreatureThisTurn p0) (cause := some testCause)
  let cdaGreenObj := gFreeRg.object! (gFreeRg.player p0).hand.back!
  mustHold56i3 "3a_desigLki" desigLkiOk &&
  mustHold56i3 "3a_protComplete" protCompleteOk &&
  mustHold56i3 "3a_layer56" layer56Ok &&
  mustHold56i3 "3b_combatAndHistory" combatAndHistoryOk &&
  mustHold56i3 "3b_ownMv" (ownMvDuringProposal == 3) &&
  mustHold56i3 "3b_selfFlash1" (gOppTurn.timingAllowsCast p0 selfFlashFirstDef) &&
  mustHold56i3 "3b_selfFlash2" (!gOppTurnCast1.timingAllowsCast p0 selfFlashFirstDef) &&
  mustHold56i3 "3b_impPerm" ((gImpPerm.playPermissionFor? p0 impExObj (face? := some impFace)).any (!·.payLifeEqualManaValue)) &&
  mustHold56i3 "3b_morphPerm" ((gImpPerm.playPermissionFor? p0 morphExObj (face? := some morphSpellFace)).any (·.payLifeEqualManaValue)) &&
  mustHold56i3 "3b_freeRgCda" (gFreeRg.playManaCost { cdaGreenObj with controller := some p0 } cdaGreenCreatDef == ManaCost.zero) &&
  mustHold56i3 "3.replay"
    (replayOk56i3 #[gDesLeft, gEmbDmg, gLkiPermDmg, gGrant3, gL51, gL6Stripped, gFreeRg])

end Phase56Item3EventAlignment

/-! ### Phase 56 Item 4a: Remaining non-card / bounced-token hand & graveyard guards
(Zemo's Boast black-token graveyard non-reversal, Balin bounced-token discard count,
`entersUntappedBehold` token filter, mid-game `putCardsOnBottom` / `Game.applyIdle` /
`castAsPartOfResolution` stack invariant) -/
section Phase56Item4EventAlignment

private def mustHold56i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase56Item4EventAlignment failed: {label}"

private def replayOk56i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let g0 := emptyHand afterDraw p0

  -- 4a(i). Zemo's Boast black-token graveyard non-reversal:
  --        A black token in the graveyard is ignored by Zemo's Boast candidate selection,
  --        so 2 real black cards (16 symbols) + a dead black token (10 symbols) still succeeds cleanly
  --        without false reversal, rejects `.decline`, rejects selecting the token, and rejects when only
  --        1 real card + 1 token is present!
  let zemoBoastDef : CardDef := {
    bear with
    name := "P56i4 Zemo"
    activatedAbilities := #[ActivatedAbility.zemoBoastAbility]
  }
  let heavyBlackDef : CardDef := {
    name := "P56i4 HeavyBlack"
    manaCost := { symbols := Array.replicate 8 (.colored .black) }
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let blackTokDef : CardDef := {
    creature "P56i4 BlackTok" { symbols := Array.replicate 10 (.colored .black) } #["Zombie"] 2 2 with
    isToken := true
  }
  let gZemo0 := addPermanent g0 zemoBoastDef p0 p0
  let gZemo1 := insertObject (insertObject gZemo0 heavyBlackDef p0 (.graveyard p0)) heavyBlackDef p0 (.graveyard p0)
  let realGyIds := (gZemo1.player p0).graveyard
  let (gZemo2, btok) := gZemo1.createOneToken p0 blackTokDef (cause := some testCause)
  let (gZemo3, btokGyId) := gZemo2.move btok.id (.graveyard p0) none (cause := some testCause)
  let zemo := (gZemo3.permanentsOf p0).find? (·.name == zemoBoastDef.name) |>.get!
  let gZemoAtk := gZemo3.record (GameEvent.attackersDeclared gZemo3.turnNumber p0 #[(gZemo3.snapshot zemo, .player ⟨1⟩)])
  let zemoIdx := (gZemoAtk.activatedAbilitiesOf zemo).size - 1
  let gZemoPrompt := mustApply gZemoAtk p0 (.activate zemo.id zemoIdx)
  let gZemoPaid := mustApply gZemoPrompt p0 (.choosePermanents realGyIds)
  -- Only 1 real black card (8) + 1 dead black token (10) is NOT payable (8 < 15):
  let gZemoShort0 := insertObject gZemo0 heavyBlackDef p0 (.graveyard p0)
  let (gZemoShort1, btokS) := gZemoShort0.createOneToken p0 blackTokDef (cause := some testCause)
  let (gZemoShort2, _) := gZemoShort1.move btokS.id (.graveyard p0) none (cause := some testCause)
  let zemoS := (gZemoShort2.permanentsOf p0).find? (·.name == zemoBoastDef.name) |>.get!
  let gZemoShortAtk :=
    gZemoShort2.record (GameEvent.attackersDeclared gZemoShort2.turnNumber p0 #[(gZemoShort2.snapshot zemoS, .player ⟨1⟩)])
  let zemoTokenFilteredOk :=
    (match gZemoPrompt.pending with
     | .resolutionChoice p (.zemoBoastExile _ sid) => p == p0 && sid == zemo.id
     | _ => false) &&
    !(gZemoPrompt.apply p0 .decline).isOk &&
    !(gZemoPrompt.apply p0 (.choosePermanents #[realGyIds[0]!, btokGyId])).isOk &&
    gZemoPaid.stack.size == 1 &&
    !(gZemoShortAtk.apply p0 (.activate zemoS.id zemoIdx)).isOk

  -- 4a(ii). Balin bounced-token discard count & `entersUntappedBehold` token filter:
  let gobTokDef : CardDef := {
    creature "P56i4 HandGobTok" ManaCost.empty #["Goblin"] 1 1 with
    isToken := true
  }
  let (gBalin0, gtok) := g0.createOneToken p0 gobTokDef (cause := some testCause)
  let (gBalin1, gtokHandId) := gBalin0.move gtok.id (.hand p0) none (cause := some testCause)
  let gBalin2 := insertObject gBalin1 bear p0 (.hand p0)
  let libBefore := (gBalin2.player p0).library.size
  let gyBefore := (gBalin2.player p0).graveyard.size
  let gBalinPrompt :=
    gBalin2.change (.pending (.resolutionChoice p0 (.mayDiscardHandBalin none)))
  let gBalinDone := mustApply gBalinPrompt p0 .accept
  -- Only 1 real card (`bear`) was discarded (not the bounced token), so only 1 card is drawn!
  let balinCountOk :=
    (gBalinDone.player p0).library.size == libBefore - 1 &&
    (gBalinDone.player p0).graveyard.size == gyBefore + 1
  -- `entersUntappedBehold` excludes bounced Goblin token in hand from replacement options:
  let beholdLandDef : CardDef := {
    name := "P56i4 BeholdLand"
    types := #[.land]
    staticAbilities := #[.replacement none (.entersTappedUnlessPay (CostSpec.ofItems #[.behold .goblin]))]
  }
  let gBeh0 := insertObject gBalin1 beholdLandDef p0 (.hand p0)
  let behLandId := (gBeh0.player p0).hand.back!
  let (gBeh1, _) := gBeh0.move behLandId .battlefield (some p0) (cause := some testCause)
  -- With ONLY a bounced Goblin token in hand, no `.entersUntappedBehold` prompt is offered; land enters tapped!
  let entersBeholdFilterOk :=
    gBeh1.pending == Pending.none &&
    (gBeh1.permanentsOf p0).any (fun o => o.name == beholdLandDef.name && o.status.tapped)

  -- 4a(iii). Mid-game `putCardsOnBottom` / `Mtg.Engine.applyIdle` / `castAsPartOfResolution` stack invariant:
  let gTokHandOnly := gBalin1
  let gBotTokPrompt := gTokHandOnly.change (.pending (.putOnBottom p0 1))
  let botTokRejected := !(gBotTokPrompt.apply p0 (.putOnBottom #[gtokHandId])).isOk
  let gBotReal := insertObject gTokHandOnly bear p0 (.hand p0)
  let realBearHandId := (gBotReal.player p0).hand.back!
  let botLibBefore := (gBotReal.player p0).library.size
  let gIdleBot : Game :=
    Mtg.Engine.applyIdle (gBotReal.change (.pending (.putOnBottom p0 1)))
  -- `castAsPartOfResolution` on a token (CR 111.8) must NOT corrupt `g.stack`!
  let (gCastTok0, ctok) := g0.createOneToken p0 gobTokDef (cause := some testCause)
  let (gCastTok1, ctokExId) := gCastTok0.move ctok.id .exile none (cause := some testCause)
  let gCastTok2 := gCastTok1.castAsPartOfResolution p0 ctokExId
  let tokGuardAndStackOk :=
    !Game.isCastableObject (gCastTok1.object! ctokExId) &&
    botTokRejected &&
    gIdleBot.pending == Pending.none &&
    (gIdleBot.player p0).library.size == botLibBefore + 1 &&
    !(gIdleBot.player p0).hand.contains realBearHandId &&
    ((gIdleBot.player p0).library[0]?.bind gIdleBot.findObject?).any (·.name == bear.name) &&
    gCastTok2.stack.isEmpty

  mustHold56i4 "4a_zemoTokenFiltered" zemoTokenFilteredOk &&
  mustHold56i4 "4a_balinCount" balinCountOk &&
  mustHold56i4 "4a_entersBeholdFilter" entersBeholdFilterOk &&
  mustHold56i4 "4a_tokGuardAndStack" tokGuardAndStackOk &&
  mustHold56i4 "4.replay"
    (replayOk56i4 #[gZemoPrompt, gZemoPaid, gBalinDone, gBeh1, gIdleBot, gCastTok2])

end Phase56Item4EventAlignment

end Mtg.Engine.EventTests
