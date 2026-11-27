import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

/-! ### Phase 61 Item 1: `probeRestorePendingCore.afterFlushed` `.seq` ordering / multi-entry
`outerPendingReplacements` / cycle `queued` parity, recursive `isManaAbilityContinuation` &
left-nested `.seq (.seq a b) c` `openedNewPrompt` probes, `hasNestedManaAbilityPostStep` /
`advanceProbeOnResumeCore` nested-checkpoint reversal across the 7 `resume*AfterLeave`/
`afterTriggerTargetsChosen` post-steps and 6 proposal-completion leaves while keeping
`.payCostPickItems`/`.finishActivationExtraCosts`/`.finishResolutionChoice`/`.receivePriority`/
`.afterWardResolved` on `(false, gCur)`, `PostStep.emitExpiredPlayFromExileFrom.isPurePostLog`,
`prepareReverseInRestorePending` deferred idle priority, CR 117.3b–c `resolutionCast` vs
non-resolution `Casting.lean:1417` & `poppedTail?` priority stashes, semantic
`ensureEndsWithFinishResolutionChoice`/`chainProposalOuterCont` checks, and CR 601.2h Teamwork
total-power revalidation -/
section Phase61Item1EventAlignment

private def mustHold61i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase61Item1EventAlignment failed: {label}"

private def replayOk61i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let leyADef : CardDef := { name := "P61i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P61i1 LeyB", types := #[.enchantment] }
  let gRep0 := addPermanent (addPermanent g3 leyADef p0 p0) leyBDef p0 p0
  let qLeyA := (gRep0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let qLeyB := (gRep0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let dRidA : ReplacementId := { kind := .addNoncombatDamage, object := some qLeyA }
  let dRidB : ReplacementId := { kind := .multiplyDamage, object := some qLeyB }
  let gRep :=
    (gRep0.createEffect
      (.replacement {
        id := dRidA, source := some qLeyA, controller := some p0, affectedPlayer := p0,
        kind := .addNoncombatDamage none 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := dRidB, source := some qLeyB, controller := some p0, affectedPlayer := p0,
        kind := .multiplyDamage none 2 }) (cause := some testCause)

  -- 1a. `probeRestorePendingCore.afterFlushed` `.seq` ordering, multi-entry
  --     `outerPendingReplacements`, and cycle `queued := false` parity!
  let gSeqOrder :=
    g3.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
      }
    ]
  let seqOrderPr : PendingReplacement :=
    .seq (.restorePending .none false) (.restorePending (.mayResolve p0) false)
  let gMultiOuter :=
    g3.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.restorePending (.mayResolve p0) false, .finishResolutionChoice]
        pendingReplacement := some (.restorePending .none false)
      }
    ]
  -- Cycle guard `inner == pr`: `.restorePending .none false` while `pendingReplacement` holds the same node:
  let gCycleSelf :=
    g3.changes #[
      .pushContinuationFrame {
        pendingReplacement := some (.restorePending .none false)
      }
    ]
  let afterFlushedFixOk :=
    !gSeqOrder.continuationGrantsPriority false seqOrderPr &&
    gSeqOrder.priorityRecipientOfContinuation? false seqOrderPr == none &&
    gSeqOrder.continuationSettlesControlFlow false seqOrderPr &&
    !gMultiOuter.anyContinuationGrantsPriority &&
    gMultiOuter.firstContinuationPriorityGrant? == none &&
    gMultiOuter.anyContinuationSettlesControlFlow &&
    !gCycleSelf.continuationGrantsPriority false (.restorePending .none false) &&
    !gCycleSelf.continuationSettlesControlFlow false (.restorePending .none false)

  -- 1b. Recursive `isManaAbilityContinuation` & `isSilentFinishPostCast` and left-nested
  --     `.seq (.seq a b) c` `openedNewPrompt` probes!
  let manaPostSac : PendingReplacement :=
    .finishActivateManaAbilityPostSac p0 ⟨99910⟩ "Rock" {} #[ManaType.colored .green] false (some 0) none 0 false .none
  let nestedManaSeq : PendingReplacement :=
    .seq
      (.seq (.finishPostStep (.logExiledIfInExile ⟨99911⟩ "exiled")) manaPostSac)
      (.receivePriority p2)
  let silentPostCastSeq : PendingReplacement :=
    .seq
      (.seq (.finishPostStep (.logExiledIfInExile ⟨99911⟩ "exiled")) (.finishPostCast p0 false false false))
      (.receivePriority p2)
  -- Left-nested `.seq (.seq a b) c` where `a` opens `.chooseReplacement`, `b` is a log, `c` grants `p2`:
  let leftNestedRepl : PendingReplacement :=
    .seq
      (.seq (.restorePending (.chooseReplacement p0 #[dRidA, dRidB]) false) (.logMessage "mid"))
      (.receivePriority p2)
  let seqProbesOk :=
    g3.continuationGrantsPriority false nestedManaSeq &&
    g3.priorityRecipientOfContinuation? false nestedManaSeq == some p2 &&
    g3.firstPriorityGrantRecipient? false nestedManaSeq == some (some p2) &&
    g3.continuationGrantsPriority false silentPostCastSeq &&
    g3.priorityRecipientOfContinuation? false silentPostCastSeq == some p2 &&
    gRep.continuationGrantsPriority false leftNestedRepl &&
    gRep.priorityRecipientOfContinuation? false leftNestedRepl == some p2 &&
    gRep.firstPriorityGrantRecipient? false leftNestedRepl == some (some p2) &&
    gRep.continuationSettlesControlFlow false leftNestedRepl

  -- 1c. `hasNestedManaAbilityPostStep` / `advanceProbeOnResumeCore` nested-checkpoint reversal
  --     across the 7 `resume*AfterLeave`/`afterTriggerTargetsChosen` post-steps and 6
  --     proposal-completion leaves, while keeping `.payCostPickItems`/`.finishActivationExtraCosts`/
  --     `.finishResolutionChoice`/`.receivePriority`/`.afterWardResolved` on `(false, gCur)`!
  let nonActSpell : CardDef := {
    name := "P61i1 NonActInstant"
    manaCost := ManaCost.ofColor .blue
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gNonAct0 :=
    ((insertObject (emptyHand g3 p0) nonActSpell p1 (.hand p1)).change (.priority p1)).change
      (.pendingPriority none)
  let naHandId := (gNonAct0.player p1).hand.back!
  let gOuterProp := mustApply gNonAct0 p1 (.cast naHandId)
  let outerSpellId := gOuterProp.proposedSpell.get!.spellId
  let gNestedCkpt :=
    (gOuterProp.change .saveProposalCheckpoint).change (.beginProposalAction .manaAbility)
  let gNestedGone :=
    ((gNestedCkpt.change (.pending .none)).move outerSpellId (.graveyard p1) none (cause := some testCause)).1
  let revLeaves13 : Array PendingReplacement := #[
    .finishPostStep (.resumeChooseModeAfterLeave p1),
    .finishPostStep (.resumeChooseTargetsAfterLeave p1),
    .finishPostStep .afterTriggerTargetsChosen,
    .finishPostStep (.resumeTriggerModesAfterLeave p1 ⟨99920⟩ 1 #[]),
    .finishPostStep (.resumeUpToTriggerModesAfterLeave p1 ⟨99920⟩ 1 #[]),
    .finishPostStep (.resumeHawkeyeModesAfterLeave p1 ⟨99920⟩ 1 #[]),
    .finishPostStep (.resumeProposalCostAfterLeave p1 (.activateManaAbilities p1)),
    .finishBecomeCast p1 outerSpellId true false false,
    .finishProposedSpellCosts .finalize true false false,
    .completeActivation false false,
    .finishBecomeActivated p1 "Src" none none (some outerSpellId) none none false false,
    .finishPostLoyaltyActivated p1 "Src" none none (some outerSpellId) none none false false,
    .finishTurnFaceUp p1 outerSpellId false
  ]
  -- Each of the 13 unguarded reversing leaves must reverse the outer proposal under a nested mana
  -- checkpoint and drop a trailing `.logMessage` (not run it)!
  let revLeaves13Ok :=
    revLeaves13.all fun leaf =>
      let gR := gNestedGone.resumePendingReplacement (.seq leaf (.logMessage "p61-must-drop-leaf-tail"))
      gR.proposedSpell.isNone && !gR.log.contains "p61-must-drop-leaf-tail"
  -- Conversely, non-reversing leaves (`.finishResolutionChoice`, `.receivePriority`, `.afterWardResolved`,
  -- `.payCostPickItems`, `.finishActivationExtraCosts`) must NOT drop trailing `.logMessage` via
  -- `hasNestedManaAbilityPostStep`:
  let gKeepTail1 :=
    (gNestedCkpt.change (.pending .none)).resumePendingReplacement
      (.seq (.receivePriority p2) (.logMessage "p61-keep-tail"))
  let gKeepTail2 :=
    (gNestedCkpt.change (.pending .none)).resumePendingReplacement
      (.seq .finishResolutionChoice (.logMessage "p61-keep-tail"))
  let gKeepTail3 :=
    (gNestedCkpt.change (.pending .none)).resumePendingReplacement
      (.seq .afterWardResolved (.logMessage "p61-keep-tail"))
  let gKeepTail4 :=
    (gNestedCkpt.change (.pending .none)).resumePendingReplacement
      (.seq (.payCostPickItems p1 none (some ⟨99921⟩) .discardACard #[]) (.logMessage "p61-keep-tail"))
  let gKeepTail5 :=
    (gNestedCkpt.change (.pending .none)).resumePendingReplacement
      (.seq (.finishActivationExtraCosts p1 ⟨99921⟩ none false false)
        (.logMessage "p61-keep-tail"))
  let nonRevKeptOk :=
    gKeepTail1.log.contains "p61-keep-tail" &&
    gKeepTail2.log.contains "p61-keep-tail" &&
    gKeepTail3.log.contains "p61-keep-tail" &&
    gKeepTail4.log.contains "p61-keep-tail" &&
    gKeepTail5.log.contains "p61-keep-tail"

  -- 1d. `PostStep.emitExpiredPlayFromExileFrom` is classified as `isPurePostLog`!
  let pfePostLog : PendingReplacement := .finishPostStep (.emitExpiredPlayFromExileFrom 0)
  let pfePurePostLogOk :=
    pfePostLog.isPurePostLog &&
    (PendingReplacement.seq (.receivePriority p2) pfePostLog).endsWithPriorityGrant &&
    (PendingReplacement.seq .finishResolutionChoice pfePostLog).endsWithFinishResolutionChoice

  -- 1e. `prepareReverseInRestorePending` deferred idle priority: when an unreversed action happened
  --     during proposal casting, reversing inside `.restorePending` with `followedByExplicitPriority?`
  --     or `followedByFinishChoice` must NOT emit a premature or duplicate `PriorityEvent.received`!
  let gUnrevProp0 := gOuterProp.gainLife p0 1 (cause := some testCause)
  let gUnrevGone :=
    ((gUnrevProp0.change (.pending .none)).move outerSpellId (.graveyard p1) none (cause := some testCause)).1
  let preEvCount := gNonAct0.events.size
  let gRevExpl :=
    gUnrevGone.resumePendingReplacement
      (.seq (.restorePending (.activateManaAbilities p1) false none #[p1] none) (.receivePriority p2))
  let explPrioEvs :=
    (gRevExpl.events.extract preEvCount gRevExpl.events.size).filter fun
      | .engine _ (.priority _) _ => true
      | _ => false
  let gRevFc :=
    gUnrevGone.resumePendingReplacement
      (.seq (.restorePending (.activateManaAbilities p1) false none #[p1] none) .finishResolutionChoice)
  let fcPrioEvs :=
    (gRevFc.events.extract preEvCount gRevFc.events.size).filter fun
      | .engine _ (.priority _) _ => true
      | _ => false
  let deferredIdlePrioOk :=
    gRevExpl.proposedSpell.isNone &&
    gRevExpl.priority == p2 &&
    explPrioEvs.size == 1 &&
    gRevFc.proposedSpell.isNone &&
    gRevFc.priority == p1 &&
    fcPrioEvs.size == 1

  -- 1f. CR 117.3b–c `resolutionCast := true` vs non-resolution `Casting.lean:1417` & `poppedTail?`!
  --     (i) Non-active player `p1` reversing a `resolutionCast := true` spell with `followedByFinishChoice`
  --         must NOT stash `p1` in `pendingPriority`; `.finishResolutionChoice` returns priority to `p0` (`activePlayer`)!
  let gResCast0 :=
    insertObject (emptyHand g3 p0) nonActSpell p1 .exile
  let resExId := (gResCast0.objects.filter (·.zone == .exile)).back!.id
  let gResCastProp := gResCast0.castAsPartOfResolution p1 resExId (withoutManaCost := false)
  let resSpellId := gResCastProp.proposedSpell.get!.spellId
  let gResCastGone :=
    ((gResCastProp.change (.pending .none)).move resSpellId (.graveyard p1) none (cause := some testCause)).1
  let gResCastRevDirect :=
    gResCastGone.reverseProposedSpell (resumeContinuation := true) (followedByFinishChoice := true)
  let gResCastRevRestore :=
    gResCastGone.resumePendingReplacement
      (.seq (.restorePending (.activateManaAbilities p1) false none #[p1] none) .finishResolutionChoice)
  --     (ii) Non-resolution cast (`!prop.resolutionCast`) reversing through `Casting.lean:1417`
  --          with an open non-settling continuation frame STILL stashes `p1` in `pendingPriority`!
  let gNonActWithLog :=
    gNonAct0.change (.pushContinuationFrame { pendingReplacement := some (.logMessage "open-non-settling") })
  let gNonResOpenProp := mustApply gNonActWithLog p1 (.cast naHandId)
  let nonResOpenCorePrio :=
    match (gNonResOpenProp.change (.pending .none)).reverseProposedSpellCore?
        (resumeContinuation := false) (followedByFinishChoice := true) with
    | .ok (gCore, _, _) => gCore.pendingPriority
    | .error _ => none
  let gNonResRevOpenCont :=
    (gNonResOpenProp.change (.pending .none)).reverseProposedSpell
      (resumeContinuation := false) (followedByFinishChoice := true)
  --     (iii) `.restorePending` `poppedTail? = some tailSeq`: stashes caster `p1` on `followedByFinishChoice`,
  --           and avoids duplicate `.receivePriority` when `tailSeq` already grants priority (`p2`)!
  let gPoppedFc :=
    (gUnrevGone.change (.pushContinuationFrame {
      outerPendingReplacements := #[.logMessage "popped-tail"]
    })).resumePendingReplacement
      (.seq (.restorePending (.activateManaAbilities p1) true none #[p1] none)
        .finishResolutionChoice)
  let prePoppedExplEv := gNonAct0.events.size
  let gPoppedExpl :=
    (gUnrevGone.change (.pushContinuationFrame {
      outerPendingReplacements := #[.receivePriority p2]
    })).resumePendingReplacement
      (.seq (.restorePending (.activateManaAbilities p1) true none #[p1] none)
        (.receivePriority p0))
  let poppedExplPrioEvs :=
    (gPoppedExpl.events.extract prePoppedExplEv gPoppedExpl.events.size).filter fun
      | .engine _ (.priority _) _ => true
      | _ => false
  let cr117StashOk :=
    gResCastProp.proposedSpell.any (·.resolutionCast) &&
    gResCastRevDirect.proposedSpell.isNone &&
    gResCastRevDirect.pendingPriority.isNone &&
    gResCastRevRestore.proposedSpell.isNone &&
    gResCastRevRestore.priority == p0 &&
    nonResOpenCorePrio == some p1 &&
    gNonResRevOpenCont.proposedSpell.isNone &&
    gNonResRevOpenCont.priority == p1 &&
    gPoppedFc.proposedSpell.isNone &&
    gPoppedFc.priority == p1 &&
    gPoppedExpl.proposedSpell.isNone &&
    gPoppedExpl.priority == p2 &&
    poppedExplPrioEvs.size == 1

  -- 1g. Semantic `chainProposalOuterCont` check: semantically settling `outer` (such as
  --     `.finishPostStep .advanceAfterStepEnded` or `.seq (.receivePriority p2) (.logMessage "x")`)
  --     does NOT append a duplicate `.finishResolutionChoice`!
  let outerAdv : PendingReplacement := .finishPostStep .advanceAfterStepEnded
  let outerSeqP2 : PendingReplacement := .seq (.receivePriority p2) (.logMessage "after-p2")
  let gChainedAdv := g3.chainProposalOuterCont p1 outerAdv
  let gChainedSeqP2 := g3.chainProposalOuterCont p1 outerSeqP2
  let semanticChainOk :=
    gChainedAdv.pendingReplacement == some outerAdv &&
    gChainedSeqP2.pendingReplacement == some outerSeqP2 &&
    gChainedSeqP2.pendingPriority.isNone

  -- 1h. CR 601.2h Teamwork total-power revalidation: shrink chosen Teamwork creature's power
  --     during CR 601.2g -> both `finishProposedSpell` AND `tapTeamworkCreaturesForProposed`
  --     reject/reverse when total power drops below `need`!
  let teamworkSpellDef : CardDef := {
    name := "P61i1 TeamworkBolt"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    keywords := #[.teamwork 4]
    spellAbility := some { effect := Effect.gainLife 3 }
  }
  let bigCreDef : CardDef := creature "P61i1 BigHelper" ManaCost.empty #["Giant"] 4 4
  let gTw0 :=
    (insertObject (addPermanent (emptyHand g3 p0) bigCreDef p0 p0) teamworkSpellDef p0 (.hand p0)).record
      (GameEvent.manaAdded g3.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }])
  let helperId := (gTw0.permanentsOf p0).find? (·.name == bigCreDef.name) |>.get!.id
  let twHandId := (gTw0.player p0).hand.back!
  let gTwCast := mustApply gTw0 p0 (.cast twHandId)
  let gTwAnnounced :=
    mustApply (mustApply gTwCast p0 (.announceTeamwork true)) p0 (.choosePermanents #[helperId])
  -- Now shrink `helperId` from 4/4 to 1/4 during CR 601.2g mana-ability window!
  let gTwShrunk :=
    gTwAnnounced.createEffect
      (.layered (.objects #[helperId]) (.ptModify (-3) 0) .untilEndOfTurn)
      (cause := some testCause)
  let gTwPayFinish :=
    match gTwShrunk.apply p0 .pay with
    | .ok g => g
    | .error _ => gTwShrunk
  let twDirectTapErr :=
    match gTwShrunk.tapTeamworkCreaturesForProposed gTwShrunk.proposedSpell.get! with
    | .error _ => true
    | .ok _ => false
  let teamworkRevalOk :=
    gTwAnnounced.proposedSpell.any (fun pr => pr.teamworkCreatures == #[helperId]) &&
    gTwPayFinish.proposedSpell.isNone &&
    gTwPayFinish.stack.isEmpty &&
    !(gTwPayFinish.object! helperId).status.tapped &&
    twDirectTapErr

  mustHold61i1 "1a_afterFlushedFix" afterFlushedFixOk &&
  mustHold61i1 "1b_seqProbes" seqProbesOk &&
  mustHold61i1 "1c_revLeaves13" revLeaves13Ok &&
  mustHold61i1 "1c_nonRevKept" nonRevKeptOk &&
  mustHold61i1 "1d_pfePurePostLog" pfePurePostLogOk &&
  mustHold61i1 "1e_deferredIdlePrio" deferredIdlePrioOk &&
  mustHold61i1 "1f_cr117Stash" cr117StashOk &&
  mustHold61i1 "1g_semanticChain" semanticChainOk &&
  mustHold61i1 "1h_teamworkReval" teamworkRevalOk &&
  mustHold61i1 "1.replay"
    (replayOk61i1 #[gRevExpl, gRevFc, gResCastRevDirect, gResCastRevRestore,
      gNonResRevOpenCont, gPoppedFc, gPoppedExpl, gChainedAdv, gChainedSeqP2,
      gTwPayFinish])

end Phase61Item1EventAlignment

/-! ### Phase 61 Item 2: `withBatchCoreReturn` `keepOpen` with `g1.pending == .none`,
`splitAfterCloseBatchFor?` paused `.finishLinkedExileMove`, `.afterCopyAndCastExileLoop`
copy-outside-batch, immediate flicker multi-target/single-target batch separation & log name,
multi-object counter-put single-batch pause, `.revealUntil` `exileWhileRevealing` pause
continuation, `execDamage` `trackExcess` lifelink pause + multi-pause synthetic frame cleanup +
deathtouch `lethalDamageThreshold`, `sheHulkAfterDamage` paused `optionalOnceActed`, 6 new
`isPlayFromExileDeferBoundaryLeaf` leaves, `DelayedTrigger.stepEnv` AnyObjId/remapping, and
`Damage.dealDamageToPermanent` under `.chooseLegend` `sbaPaused` + lazy
`emitExpiredPlayFromExileLogsLazy` loops -/
section Phase61Item2EventAlignment

private def mustHold61i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase61Item2EventAlignment failed: {label}"

private def replayOk61i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand afterDraw p0
  let leyADef : CardDef := { name := "P61i2 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P61i2 LeyB", types := #[.enchantment] }
  let gRep0 := addPermanent (addPermanent g0 leyADef p0 p0) leyBDef p0 p0
  let qLeyA := (gRep0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let qLeyB := (gRep0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let dRidA : ReplacementId := { kind := .addNoncombatDamage, object := some qLeyA }
  let dRidB : ReplacementId := { kind := .multiplyDamage, object := some qLeyB }
  let gRep :=
    (gRep0.createEffect
      (.replacement {
        id := dRidA, source := some qLeyA, controller := some p0, affectedPlayer := p0,
        kind := .addNoncombatDamage none 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := dRidB, source := some qLeyB, controller := some p0, affectedPlayer := p0,
        kind := .multiplyDamage none 2 }) (cause := some testCause)

  -- 2a. `withBatchCoreReturn` `keepOpen` with pre-existing `pendingReplacement` and `g1.pending == .none`
  --     MUST close the batch cleanly instead of leaking `currentBatch`!
  let gPrePr :=
    g0.change (.pushContinuationFrame { pendingReplacement := some (.logMessage "pre-existing") })
  let (gAfterBatch, _) := gPrePr.withBatchCoreReturn none fun gB => (gB.gainLife p0 1 (cause := some testCause), ())
  -- `splitAfterCloseBatchFor?` keeps paused `.finishLinkedExileMove` with non-default trailing fields
  -- grouped with `.closeBatch`!
  let targetBid : BatchId := ⟨42⟩
  let flFull : PendingReplacement :=
    .finishLinkedExileMove #[⟨7⟩] (some #[]) (some (⟨8⟩, .battlefield)) #[⟨8⟩] (some 3)
  let splitDirect := splitAfterCloseBatchFor? targetBid (.seq (.closeBatch targetBid 0) flFull)
  let splitWithTail :=
    splitAfterCloseBatchFor? targetBid
      (.seq (.closeBatch targetBid 0) (.seq flFull (.logMessage "after-close")))
  let batchAndSplitOk :=
    gAfterBatch.currentBatch.isNone &&
    splitDirect == some (.seq (.closeBatch targetBid 0) flFull, none) &&
    splitWithTail == some (.seq (.closeBatch targetBid 0) flFull, some (.logMessage "after-close"))

  -- 2b. `.afterCopyAndCastExileLoop` copy-outside-batch: pause during exile, resume -> exile batch
  --     closes BEFORE copy creation (separate `BatchId`s)!
  let copySpellDef : CardDef := {
    name := "P61i2 CopyBolt", manaCost := ManaCost.ofColor .red, types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gCopyEx0 := insertObject gRep copySpellDef p0 (.graveyard p0)
  let gCopyExPaused :=
    (gCopyEx0.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).applyUnified p0
      { body := .moveZone (.inZones { zones := #[.graveyard], owner := .ofPlayer .you } .anyObject)
          .exile .exile
          { grantPlayPerm? := some {
              duration := .untilEndOfTurn, copyAndCast := true, freeCast := true, maxCasts? := some 1 } } } #[]
  let gCopyExResumed := mustApply gCopyExPaused p0 (.chooseReplacement dRidA)
  let copyExileBatches :=
    gCopyExResumed.events.filterMap fun
      | .rules _ (.zone (.moved _ _ (.graveyard _) .exile ..)) _ b => b
      | _ => none
  let copyCreateBatches :=
    gCopyExResumed.events.filterMap fun
      | .rules _ (.zone (.created eo _)) _ b => if eo.zone == .exile then b else none
      | _ => none
  let copyOutsideBatchOk :=
    gCopyExPaused.currentBatch.isSome &&
    gCopyExResumed.currentBatch.isNone &&
    !copyExileBatches.isEmpty &&
    !copyCreateBatches.isEmpty &&
    copyExileBatches.back! != copyCreateBatches.back! &&
    (match gCopyExResumed.pending with | .resolutionChoice _ (.mayCastCopy _) => true | _ => false)

  -- 2c. Immediate flicker (single-target & multi-target `.owner`): separate exile and return
  --     `BatchId`s and non-duplicated permanent name in log; plus paused `dstP != o.owner` and
  --     `.returnThenExileAtEndStep` still return after replacement choice!
  let bear2Def : CardDef := creature "P61i2 FlickerCub" ManaCost.empty #["Bear"] 2 2
  let gFlk1 := addPermanent g0 bear2Def p0 p0
  let gFlk1Done :=
    gFlk1.applyUnified p0
      { body := .moveZone (.inZones .battlefield (.hasType .creature)) .exile .exile
          { delayedReturn? := some (.immediately false .owner) } } #[]
  let flk1ExileB :=
    gFlk1Done.events.filterMap fun
      | .rules _ (.zone (.moved _ _ .battlefield .exile ..)) _ b => b
      | _ => none
  let flk1RetB :=
    gFlk1Done.events.filterMap fun
      | .rules _ (.zone (.moved _ _ .exile .battlefield ..)) _ b => b
      | _ => none
  let flk1NoDupName := !gFlk1Done.log.any (fun s => (s.splitOn "P61i2 FlickerCub").length > 2)
  let gFlk2 := addPermanent gFlk1 bear2Def p0 p0
  let gFlk2Done :=
    gFlk2.applyUnified p0
      { body := .moveZone (.inZones .battlefield (.hasType .creature)) .exile .exile
          { delayedReturn? := some (.immediately false .owner) } } #[]
  let flk2ExileB :=
    gFlk2Done.events.filterMap fun
      | .rules _ (.zone (.moved _ _ .battlefield .exile ..)) _ b => b
      | _ => none
  let flk2RetB :=
    gFlk2Done.events.filterMap fun
      | .rules _ (.zone (.moved _ _ .exile .battlefield ..)) _ b => b
      | _ => none
  -- Paused non-owner return (`dstP := p0 != o.owner := p1`) and `.returnThenExileAtEndStep`:
  let gFlkSteal0 := addPermanent gRep bear2Def p1 p1
  let gFlkStealPaused :=
    (gFlkSteal0.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).applyUnified p0
      { body := .moveZone (.inZones .battlefield (.hasType .creature)) .exile .exile
          { delayedReturn? := some (.immediately false .controller) } } #[]
  let gFlkStealDone := mustApply gFlkStealPaused p0 (.chooseReplacement dRidA)
  let gFlkTempPaused :=
    (gFlkSteal0.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).applyUnified p0
      { body := .moveZone (.inZones .battlefield (.hasType .creature)) .exile .exile
          { delayedReturn? := some (.returnThenExileAtEndStep false .controller) } } #[]
  let gFlkTempDone := mustApply gFlkTempPaused p0 (.chooseReplacement dRidA)
  let flickerOk :=
    flk1ExileB.size == 1 && flk1RetB.size == 1 && flk1ExileB[0]! != flk1RetB[0]! &&
    flk1NoDupName &&
    flk2ExileB.size == 2 && flk2RetB.size == 2 &&
    flk2ExileB[0]! == flk2ExileB[1]! && flk2RetB[0]! == flk2RetB[1]! &&
    flk2ExileB[0]! != flk2RetB[0]! &&
    (gFlkStealDone.permanentsOf p0).any (·.name == bear2Def.name) &&
    (gFlkTempDone.permanentsOf p0).any (·.name == bear2Def.name) &&
    gFlkTempDone.delayedTriggers.any (fun dt => match dt.kind with | .endStepExile _ => true | _ => false)

  -- 2d. Multi-object counter-put (`.permanent (.modifyCounters (.put ..))`) shares ONE `BatchId`
  --     across replacement pause!
  let gCnt2 := addPermanent (addPermanent gRep bear p0 p0) bear2Def p0 p0
  let gCntPaused :=
    (gCnt2.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).applyUnified p0
      { body := .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1))
          (.inZones .battlefield (.hasType .creature))) } #[]
  let gCntDone := mustApply gCntPaused p0 (.chooseReplacement dRidA)
  let cntPutBatches :=
    gCntDone.events.filterMap fun
      | .rules _ (.permanent (.counters _ .plusOnePlusOne _ _)) _ b => b
      | _ => none
  let multiCounterBatchOk :=
    cntPutBatches.size == 2 && cntPutBatches[0]! == cntPutBatches[1]! &&
    gCntDone.currentBatch.isNone

  -- 2e. `.revealUntil` `exileWhileRevealing := true` pauses on replacement, resumes to find hit,
  --     binds `StepOutcome` on `.bindClose`, and executes the `.bind` body!
  let gRevLib0 :=
    insertObject (insertObject gRep bear2Def p0 (.library p0)) forest p0 (.library p0)
  let gRevPaused :=
    (gRevLib0.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).applyUnified p0
      { body := .bind ⟨0⟩
          (.player (.inspectLibrary {
            source := .revealUntil .you (.hasType .creature) (.const 1) true
            action := .none
            rest := .leaveInPlace
          }))
          (.ifCond (.stepSucceeded ⟨0⟩) (.life (.gain .you (.const 5))) .noop) } #[]
  let gRevDone := mustApply gRevPaused p0 (.chooseReplacement dRidA)
  let revealUntilPauseOk :=
    gRevPaused.pending == .chooseReplacement p0 #[dRidA, dRidB] &&
    gRevDone.pending == .none &&
    (gRevDone.player p0).life == (gRevLib0.player p0).life + 5 &&
    gRevDone.objects.any (fun o => o.zone == .exile && o.name == bear2Def.name)

  -- 2f. `execDamage`:
  --     (i) `trackExcess` lifelink pause preserves `excessDamage` in `.bind` (`StepOutcome`);
  --     (ii) top-level multi-pause `.bind` cleans up synthetic `stepEnv` frame (`continuations.isEmpty`);
  --     (iii) deathtouch `lethalDamageThreshold` (`1` for deathtouch source, `0` when `deathtouchDealtSinceLastSba`)!
  let llSrcDef : CardDef := {
    creature "P61i2 LifelinkBoltSrc" ManaCost.empty #["Wizard"] 2 2 with
    keywords := #[Keyword.lifelink]
  }
  let dtSrcDef : CardDef := {
    creature "P61i2 DeathtouchSrc" ManaCost.empty #["Snake"] 1 1 with
    keywords := #[Keyword.deathtouch]
  }
  let tough4Def : CardDef := creature "P61i2 ToughFour" ManaCost.empty #["Beast"] 4 4
  let llRidA : ReplacementId := { kind := .multiplyLifeGain, object := some qLeyA }
  let llRidB : ReplacementId := { kind := .addLifeGain, object := some qLeyB }
  let gExDmg0 :=
    ((addPermanent (addPermanent (addPermanent gRep0 llSrcDef p0 p0) dtSrcDef p0 p0) tough4Def p1 p1).createEffect
      (.replacement {
        id := llRidA, source := some qLeyA, controller := some p0, affectedPlayer := p0,
        kind := .modifyLifeGain p0 0 2 }) (cause := some testCause)).createEffect
      (.replacement {
        id := llRidB, source := some qLeyB, controller := some p0, affectedPlayer := p0,
        kind := .modifyLifeGain p0 1 1 }) (cause := some testCause)
  let llSrcId := (gExDmg0.permanentsOf p0).find? (·.name == llSrcDef.name) |>.get!.id
  let dtSrcId := (gExDmg0.permanentsOf p0).find? (·.name == dtSrcDef.name) |>.get!.id
  let tough4Id := (gExDmg0.permanentsOf p1).find? (·.name == tough4Def.name) |>.get!.id
  let gExDmgPaused :=
    gExDmg0.applyUnified p0
      { body := .bind ⟨0⟩
          (.damage (.deal .this
            (.objects (.inZones .battlefield (.named (.literal tough4Def.name))))
            (.const 6) { trackExcess := true }))
          (.life (.gain .you (.stepMetric .excessDamage ⟨0⟩))) }
      #[] (sourceId := some llSrcId)
  let gExDmgDone :=
    match gExDmgPaused.pending with
    | .chooseReplacement q cs =>
      -- Resolve lifelink replacement pause; second pause on the `.bind` life-gain also triggers!
      let g1 := mustApply gExDmgPaused q (.chooseReplacement cs[0]!)
      match g1.pending with
      | .chooseReplacement q2 cs2 => mustApply g1 q2 (.chooseReplacement cs2[0]!)
      | _ => g1
    | _ => gExDmgPaused
  let tough4Obj := gExDmg0.object! tough4Id
  let gDtMarked :=
    gExDmg0.dealDamageToPermanent tough4Obj 1 (some (gExDmg0.snapshot (gExDmg0.object! dtSrcId)))
      (cause := some testCause)
  let execDamageOk :=
    (match gExDmgPaused.pending with | .chooseReplacement _ _ => true | _ => false) &&
    gExDmgDone.pending == .none &&
    -- 6 damage to 4/4 => 2 excess damage => after lifelink (+13 life) + excess life gain (+5 or +6):
    (gExDmgDone.player p0).life > (gExDmg0.player p0).life + 13 &&
    gExDmgDone.continuations.isEmpty &&
    gExDmg0.lethalDamageThreshold tough4Obj (deathtouch := false) == 4 &&
    gExDmg0.lethalDamageThreshold tough4Obj (deathtouch := true) == 1 &&
    gDtMarked.lethalDamageThreshold (gDtMarked.object! tough4Id) (deathtouch := false) == 0

  -- 2g. `PostStep.sheHulkAfterDamage` records BOTH `sheHulkDealtDamage` and `optionalOnceActed`
  --     after replacement pause!
  let shSourceId : ObjectId := qLeyA
  let gShPrompt :=
    gRep.change (.pending (.resolutionChoice p0 (.sheHulkMayDamage 3 (.player p0) (some shSourceId))))
  let gShPaused := mustApply gShPrompt p0 .accept
  let gShDone := mustApply gShPaused p0 (.chooseReplacement dRidA)
  let shActedRecorded :=
    gShDone.events.any fun e =>
      e.turn == gShDone.turnNumber &&
        match e.change with
        | .rules (.player (.optionalOnceActed _ sid)) => sid == shSourceId
        | _ => false
  let sheHulkPauseOk :=
    (match gShPaused.pending with | .chooseReplacement _ _ => true | _ => false) &&
    gShDone.pending == .none &&
    GameEvent.sheHulkDealtDamageThisTurn gShDone.events gShDone.turnNumber &&
    shActedRecorded

  -- 2h. All 6 new `isPlayFromExileDeferBoundaryLeaf` leaves return `true`!
  let newPfeLeaves : Array PendingReplacement := #[
    .amass p0 .orc 1 none,
    .createKindTokens p0 TokenSpec.treasure 1 false false none false none,
    .finishPostStep (.enteredBattlefieldPutRestBottomRandom p0 ⟨99⟩ #[] none),
    .finishPostStep (.putRestOnBottomRandom p0 #[] none),
    .finishPostStep (.putOntoBattlefieldHasteAtFour p0 ⟨99⟩ 2 true),
    .finishPostStep (.wheelDrawThenOfferNext p0 3 #[])
  ]
  let pfeBoundariesOk := newPfeLeaves.all PendingReplacement.isPlayFromExileDeferBoundaryLeaf

  -- 2i. `DelayedTrigger.stepEnv` checked by `delayedTriggerAnyObjId` and remapped by
  --     `ensureDelayedTrigger` during `reverseProposedSpell`!
  let dtSpell : CardDef := {
    name := "P61i2 DtSpell", manaCost := ManaCost.ofColor .blue, types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gDt0 := addPermanent (insertObject g0 dtSpell p0 (.hand p0)) bear p0 p0
  let dtHandId := (gDt0.player p0).hand.back!
  let gDtProp := mustApply gDt0 p0 (.cast dtHandId)
  let dtSpellId := gDtProp.proposedSpell.get!.spellId
  -- Record an irreversible action (drawing a card) that installs a delayed trigger whose `stepEnv`
  -- references `dtSpellId` (the post-proposal stack `ObjectId`): reversal must keep the delayed
  -- trigger AND remap `dt.stepEnv` from `dtSpellId` back to `dtHandId`!
  let dtRefsProp : DelayedTrigger := {
    controller := p0
    kind := .copyNextInstantSorceryThisTurn
    cause := testCause
    instruction? := some .noop
    stepEnv := #[(⟨0⟩, { objects := #[dtSpellId] })]
  }
  let gDtWithIrrev :=
    ((((gDtProp.change (.beginProposalAction (.manaAbility none))).draw p0 1).record
      (.rules gDtProp.turnNumber (.delayedTrigger (.created dtRefsProp)) testCause)).change
      .endProposalAction)
  let gDtReversed := gDtWithIrrev.reverseProposedSpell (resumeContinuation := false)
  let delayedStepEnvOk :=
    dtSpellId != dtHandId &&
    gDtReversed.proposedSpell.isNone &&
    !gDtReversed.delayedTriggers.any (fun dt => dt.stepEnv.any (fun (_, o) => o.objects.contains dtSpellId)) &&
    gDtReversed.delayedTriggers.any (fun dt => dt.stepEnv.any (fun (_, o) => o.objects.contains dtHandId))

  -- 2j. `Damage.dealDamageToPermanent` under `.chooseLegend` (`g.sbaPaused`) defers damage &
  --     lifelink instead of bypassing `markDamageOn`!
  let legDef : CardDef := { bear with name := "P61i2 Legend", supertypes := #[.legendary] }
  let gLegSba0 := addPermanent (addPermanent (addPermanent g0 llSrcDef p0 p0) legDef p1 p1) legDef p1 p1
  let legIds := (gLegSba0.permanentsOf p1).filter (·.name == legDef.name) |>.map (·.id)
  let llId2 := (gLegSba0.permanentsOf p0).find? (·.name == llSrcDef.name) |>.get!.id
  let gLegPaused := gLegSba0.change (.pending (.chooseLegend p1 legDef.name legIds))
  let gLegDmg :=
    gLegPaused.dealDamageToPermanent (gLegPaused.object! legIds[0]!) 2
      (some (gLegPaused.snapshot (gLegPaused.object! llId2))) (cause := some testCause)
  let legendSbaDeferOk :=
    gLegPaused.sbaPaused &&
    (gLegDmg.object! legIds[0]!).status.damage == 0 &&
    (gLegDmg.player p0).life == (gLegSba0.player p0).life &&
    gLegDmg.pendingReplacement.isSome

  mustHold61i2 "2a_batchAndSplit" batchAndSplitOk &&
  mustHold61i2 "2b_copyOutsideBatch" copyOutsideBatchOk &&
  mustHold61i2 "2c_flicker" flickerOk &&
  mustHold61i2 "2d_multiCounterBatch" multiCounterBatchOk &&
  mustHold61i2 "2e_revealUntilPause" revealUntilPauseOk &&
  mustHold61i2 "2f_execDamage" execDamageOk &&
  mustHold61i2 "2g_sheHulkPause" sheHulkPauseOk &&
  mustHold61i2 "2h_pfeBoundaries" pfeBoundariesOk &&
  mustHold61i2 "2i_delayedStepEnv" delayedStepEnvOk &&
  mustHold61i2 "2j_legendSbaDefer" legendSbaDeferOk &&
  mustHold61i2 "2.replay"
    (replayOk61i2 #[gAfterBatch, gCopyExResumed, gFlk1Done, gFlk2Done, gFlkStealDone, gFlkTempDone,
      gCntDone, gRevDone, gExDmgDone, gShDone, gDtReversed, gLegDmg])

end Phase61Item2EventAlignment

/-! ### Phase 61 Item 3: CR 613.7a self-executed `.grantStatic` `maxTs` timestamps, Layer 7b/7c
static-granted `.grantStatic` P/T CDAs & timestamps, Myriad attacking non-defending opponent &
planeswalker choice, `.endOfCombatSacrifice`/`.endStepSacrifice` after control change,
`mkHistoricalGameAt`/`objectCounterCountAt` on `.cast .announced` Morph & Impending, face-down
`.exile` across `Movement.move` / `applyZoneEvent .moved` / `mkHistoricalGameAt`, and origin-zone
Layer-6 Flash / Aura Layer-3 `TextChange` / Layer-6 `lockInTargetCostReduction` -/
section Phase61Item3EventAlignment

private def mustHold61i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase61Item3EventAlignment failed: {label}"

private def replayOk61i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g0 := emptyHand afterDraw p0
  let g3 := g0.change (.addPlayer { id := p2, name := "Liliana" })

  -- 3a. CR 613.7a self-executed `.grantStatic` `maxTs` timestamps:
  --     Grantor `A` (earlier ts) grants all creatures `.continuous none .self (.grantKeywords #[.indestructible])`;
  --     intermediate effect `B` removes indestructible from all creatures;
  --     recipient `o` enters AFTER `B` -> `grantTs = max(o.timestamp, A.timestamp) > B.timestamp`,
  --     so `o` MUST have Indestructible in BOTH `evalLayer6Aux` and `evalStaticsFast`!
  let grantIndStatic : StaticAbility :=
    .continuous none { zones := .battlefield, pred := .hasType .creature }
      (.grantStatic #[.continuous none { zones := .battlefield, pred := .sameAs .this }
        (.grantKeywords #[Keyword.indestructible])])
  let grantorADef : CardDef := {
    name := "P61i3 GrantorA", types := #[.enchantment]
    staticAbilities := #[grantIndStatic]
  }
  -- Early creature enters BEFORE `B` (loses indestructible to `B`); late creature enters AFTER `B` (keeps it)!
  let gTs0 := addPermanent g0 grantorADef p0 p0
  let gTs1 := addPermanent gTs0 bear p0 p0
  let earlyBearId := (gTs1.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gTs2 :=
    gTs1.createEffect
      (.layered (.creaturesControlledBy p0) (.abilities {} .loseIndestructible) .indefinite)
      (cause := some testCause)
  let lateBearDef : CardDef := creature "P61i3 LateBear" ManaCost.empty #["Bear"] 2 2
  let gTs3 := addPermanent gTs2 lateBearDef p0 p0
  let lateBearId := (gTs3.permanentsOf p0).find? (·.name == lateBearDef.name) |>.get!.id
  -- Also test `evalStaticsFast` path (no activeEffects Layer-6 effect, nested `.grantStatic` self-execution):
  let nestedSelfGrantDef : CardDef := {
    name := "P61i3 NestedGrantor", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .hasType .creature }
        (.grantStatic #[.continuous none { zones := .battlefield, pred := .sameAs .this }
          (.grantStatic #[.continuous none { zones := .battlefield, pred := .sameAs .this }
            (.modifyPT (.const 2) (.const 2))])])
    ]
  }
  let gTsFast0 := addPermanent g0 nestedSelfGrantDef p0 p0
  let gTsFast1 := addPermanent gTsFast0 bear p0 p0
  let fastBearId := (gTsFast1.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let grantStaticTsOk :=
    !gTs3.hasKeyword (gTs3.object! earlyBearId) (· == Keyword.indestructible) &&
    gTs3.hasKeyword (gTs3.object! lateBearId) (· == Keyword.indestructible) &&
    gTsFast1.power (gTsFast1.object! fastBearId) == 4

  -- 3b. Layer 7b static-granted `.grantStatic` P/T CDA & Layer 7c static-granted P/T-dependent `.modifyPT`!
  let cdaGrantorDef : CardDef := {
    name := "P61i3 CdaGrantor", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .hasType .creature }
        (.grantStatic #[.characteristicDefining (.setPT (some (.const 6)) (some (.const 6)))])
    ]
  }
  let gCda := addPermanent (addPermanent g0 cdaGrantorDef p0 p0) bear p0 p0
  let cdaBear := (gCda.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let ptDepGrantorDef : CardDef := {
    name := "P61i3 PtDepGrantor", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .hasType .creature }
        (.grantStatic #[.continuous none { zones := .battlefield, pred := .hasType .creature }
          (.modifyPT (.objectStat .power .this) (.const 0))])
    ]
  }
  let gPtDep := addPermanent (addPermanent g0 ptDepGrantorDef p0 p0) bear p0 p0
  let ptDepBear := (gPtDep.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let layer7bcGrantStaticOk :=
    gCda.power cdaBear == 6 && gCda.toughness cdaBear == 6 &&
    gPtDep.power ptDepBear == 4

  -- 3c. Myriad CR 702.116a attacking non-defending opponent `p2` (not `p1`) in 3-player game,
  --     AND prompting/choosing `p2`'s planeswalker!
  let myriadDef : CardDef := {
    creature "P61i3 MyriadScout" ManaCost.empty #["Scout"] 2 2 with
    keywords := #[Keyword.myriad]
  }
  let pwDef : CardDef := {
    name := "P61i3 OppWalker", types := #[.planeswalker], loyalty := some 4
  }
  let gMyr0 := addPermanent g3 myriadDef p0 p0
  let myrId := (gMyr0.permanentsOf p0).find? (·.name == myriadDef.name) |>.get!.id
  let gMyrAtk := mustApply (gMyr0.beginStep .declareAttackers) p0 (.declareAttackers #[myrId] (some p1))
  let gMyrMay := mustApply (mustApply (mustApply gMyrAtk p0 .pass) p1 .pass) p2 .pass
  let gMyrRes := mustApply gMyrMay p0 .accept
  let myrToks := (gMyrRes.permanentsOf p0).filter (·.printed.isToken)
  let gMyrPw0Raw := addPermanent gMyr0 pwDef p2 p2
  let pwId := (gMyrPw0Raw.permanentsOf p2).find? (·.name == pwDef.name) |>.get!.id
  let gMyrPw0 := gMyrPw0Raw.recordPutCounters pwId .loyalty 4 (some p2) (cause := some testCause)
  let gMyrPwAtk := mustApply (gMyrPw0.beginStep .declareAttackers) p0 (.declareAttackers #[myrId] (some p1))
  let gMyrPwMay := mustApply (mustApply (mustApply gMyrPwAtk p0 .pass) p1 .pass) p2 .pass
  let gMyrPwPrompt := mustApply gMyrPwMay p0 .accept
  let gMyrPwChosen := mustApply gMyrPwPrompt p0 (.choosePermanents #[pwId])
  let myrPwToks := (gMyrPwChosen.permanentsOf p0).filter (·.printed.isToken)
  let myriadOk :=
    myrToks.size == 1 &&
    myrToks[0]!.status.attacking &&
    myrToks[0]!.status.attackingTarget == some (.player p2) &&
    (match gMyrPwPrompt.pending with | .resolutionChoice q (.chooseEnteringAttackTarget ..) => q == p0 | _ => false) &&
    myrPwToks.size == 1 &&
    myrPwToks[0]!.status.attacking &&
    myrPwToks[0]!.status.attackingTarget == some (.planeswalker pwId)

  -- 3d. `.endOfCombatSacrifice` (Decayed) & `.endStepSacrifice` do NOT sacrifice after control change
  --     (`CR 701.21a / 702.147a`)!
  let gSacCtrl0 := addPermanent (addPermanent g0 bear p0 p0) bear p0 p0
  let sacCre1 := (gSacCtrl0.permanentsOf p0)[0]!.id
  let sacCre2 := (gSacCtrl0.permanentsOf p0)[1]!.id
  let gSacCtrl1 :=
    gSacCtrl0.createEffect (.layered (.objects #[sacCre1, sacCre2]) (.control p1) .indefinite)
      (cause := some testCause)
  let gSacAfterEoc := gSacCtrl1.resolveDelayedTrigger p0 (.endOfCombatSacrifice sacCre1) testCause
  let gSacAfterEnd := gSacAfterEoc.resolveDelayedTrigger p0 (.endStepSacrifice sacCre2) testCause
  let sacCtrlOk :=
    (gSacAfterEnd.findObject? sacCre1).any (·.isOnBattlefield) &&
    (gSacAfterEnd.findObject? sacCre2).any (·.isOnBattlefield)

  -- 3e. `mkHistoricalGameAt` & `objectCounterCountAt` on real `.cast .announced` Morph & Impending!
  let morphDef : CardDef := {
    creature "P61i3 RealMorph" (ManaCost.ofGeneric 5) #["Beast"] 4 4 with
    keywords := #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])]
  }
  let impDef : CardDef := {
    creature "P61i3 RealImp" (ManaCost.ofGeneric 5) #["Avatar"] 5 5 with
    types := #[.enchantment, .creature]
    keywords := #[.impending 4 (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])]
  }
  let gM0 :=
    (insertObject g0 morphDef p0 (.hand p0)).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }])
  let gMProp := mustApply gM0 p0 (.cast (gM0.player p0).hand.back!)
  let gMAnn := mustApply gMProp p0 (.announceKicker true)
  let gMCast := mustApply gMAnn p0 .pay
  let mStackId := gMCast.stack.back!.objectId
  let mHist := gMCast.mkHistoricalGameAt gMCast.events.size
  let gI0 :=
    (insertObject g0 impDef p0 (.hand p0)).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }])
  let gIProp := mustApply gI0 p0 (.cast (gI0.player p0).hand.back!)
  let gIAnn := mustApply gIProp p0 (.announceKicker true)
  let gICast := mustApply gIAnn p0 .pay
  let iStackId := gICast.stack.back!.objectId
  let iHist := gICast.mkHistoricalGameAt gICast.events.size
  let castAnnouncedHistOk :=
    (mHist.findObject? mStackId).any (fun o => o.zone == .stack && o.status.faceDown) &&
    gICast.objectCounterCountAt iStackId .time gICast.events.size == 4 &&
    (iHist.findObject? iStackId).any (fun o => o.zone == .stack && o.status.counterCount .time == 4)

  -- 3f. Face-down `.exile` preserved across `Movement.move`, `applyZoneEvent .moved`, `replayEvents`,
  --     and `mkHistoricalGameAt` (while `isFaceDownMasked` stays `false` in `.exile`)!
  let gFdEx0 := insertObject g0 bear p0 (.hand p0)
  let fdHandId := (gFdEx0.player p0).hand.back!
  let (gFdEx1, fdExId) := gFdEx0.move fdHandId .exile none (faceDown? := some true) (cause := some testCause)
  let fdExObj := gFdEx1.object! fdExId
  let fdExHist := gFdEx1.mkHistoricalGameAt gFdEx1.events.size
  let faceDownExileOk :=
    fdExObj.zone == .exile &&
    fdExObj.status.faceDown &&
    !Game.isFaceDownMasked fdExObj &&
    (fdExHist.findObject? fdExId).any (fun o => o.zone == .exile && o.status.faceDown)

  -- 3g. Origin-zone Layer-6 Flash (`timingAllowsCast` + `coreSorceryTimingOk` via `playPermissionFor?`),
  --     Aura Layer-3 `TextChange` (`legalAuraTargets`/`castFaceHasLegalTarget`/`beginResolutionCastTargets`),
  --     and Layer-6 `lockInTargetCostReduction`!
  let handFlashGrantDef : CardDef := {
    name := "P61i3 HandFlash", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.hand, .exile], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[Keyword.flash])
    ]
  }
  let gFlash0 :=
    (insertObject (insertObject (addPermanent g0 handFlashGrantDef p0 p0) bear p0 (.hand p0)) bear p0 .exile).record
      (GameEvent.stepBegan g0.turnNumber .upkeep)
  let flashBearObj := gFlash0.object! (gFlash0.player p0).hand.back!
  let flashExObj := (gFlash0.objects.filter (·.zone == .exile)).back!
  -- Exile card with `withoutManaCost := true, ignoreTiming := false` AND `withoutManaCost := false, ignoreTiming := true`:
  -- during upkeep, `coreSorceryTimingOk` sees origin-zone `.exile` Flash so `playPermissionFor?` picks the free perm!
  let gFlashExPerms :=
    (gFlash0.createEffect
      (.permission (some p0) (.playFromExile flashExObj.id { player := p0, withoutManaCost := true, ignoreTiming := false })
        .untilEndOfTurn) (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile flashExObj.id { player := p0, withoutManaCost := false, ignoreTiming := true })
        .untilEndOfTurn) (cause := some testCause)
  -- Aura enchanting "Goblin" changed via Layer-3 `TextChange` to "Bear":
  let goblinAuraDef : CardDef := {
    name := "P61i3 GoblinAura"
    manaCost := ManaCost.zero
    types := #[.enchantment], subtypes := #["Aura"]
    staticAbilities := #[.enchantRestriction { domain := .object .battlefield (.hasSubtype (.literal .goblin)) }]
  }
  let gAura0 := addPermanent (insertObject g0 goblinAuraDef p0 (.hand p0)) bear p0 p0
  let auraHandId := (gAura0.player p0).hand.back!
  let auraBearId := (gAura0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let bearTc : TextChange := .replaceCreatureType .goblin .bear
  let gAuraTc :=
    gAura0.createEffect (.layered (.objects #[auraHandId]) (.text bearTc) .indefinite)
      (cause := some testCause)
  let gAuraCast := mustApply gAuraTc p0 (.cast auraHandId)
  -- Layer-6 granted target cost reduction (`lockInTargetCostReduction`):
  let redGrantDef : CardDef := {
    name := "P61i3 TargetDiscountLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .hasType .instant }
        (.grantStatic #[.costModifier (some (.exists (.filter (.target 0) (.hasType .creature))))
          .thisSpell (.reduceGeneric (.const 2))])
    ]
  }
  let bolt3Def : CardDef := {
    name := "P61i3 ThreeBolt", manaCost := ManaCost.ofGeneric 3, types := #[.instant]
    spellAbility := some {
      effect := {
        targets := { slots := #[{ domain := .anyTarget }] }
        body := .damage (.deal .this (.targetSlot 0) (.const 1) {})
      }
    }
  }
  let gDisc0 :=
    addPermanent (insertObject (addPermanent g0 redGrantDef p0 p0) bolt3Def p0 (.hand p0)) bear p1 p1
  let discBearId := (gDisc0.permanentsOf p1).find? (·.name == bear.name) |>.get!.id
  let gDiscCast := mustApply gDisc0 p0 (.cast (gDisc0.player p0).hand.back!)
  let gDiscTargeted := mustApply gDiscCast p0 (.target (.permanent discBearId))
  let layer36CastOk :=
    gFlash0.timingAllowsCast p0 bear (card? := some flashBearObj) &&
    (gFlashExPerms.playPermissionFor? p0 flashExObj).any (·.withoutManaCost) &&
    (gAuraTc.legalAuraTargets p0 goblinAuraDef (tcs := #[bearTc])) == #[.permanent auraBearId] &&
    gAuraTc.castFaceHasLegalTarget p0 goblinAuraDef #[bearTc] (some auraHandId) &&
    gAuraCast.pending == .chooseTargets p0 &&
    gDiscTargeted.proposedSpell.any (fun pr => pr.cost == ManaCost.ofGeneric 1)

  mustHold61i3 "3a_grantStaticTs" grantStaticTsOk &&
  mustHold61i3 "3b_layer7bcGrantStatic" layer7bcGrantStaticOk &&
  mustHold61i3 "3c_myriad" myriadOk &&
  mustHold61i3 "3d_sacCtrl" sacCtrlOk &&
  mustHold61i3 "3e_castAnnouncedHist" castAnnouncedHistOk &&
  mustHold61i3 "3f_faceDownExile" faceDownExileOk &&
  mustHold61i3 "3g_layer36Cast" layer36CastOk &&
  mustHold61i3 "3.replay"
    (replayOk61i3 #[gTs3, gTsFast1, gCda, gPtDep, gMyrRes, gMyrPwChosen,
      gSacAfterEnd, gMCast, gICast, gFdEx1, gFlashExPerms, gAuraCast, gDiscTargeted])

end Phase61Item3EventAlignment

/-! ### Phase 61 Item 4: `playManaCost` `flashbackUntilEot` on `.stack` without `freeSelf`/`freeRG`
stacking, Layer-6 Morph/Kicker/Gift/Teamwork across `announceKicker`/`announceTeamwork`/`announceX`/
`afterModesChosen`/`afterAdditionalCostAnnounced`/`afterOptionalAdditionalCost`,
`castExiledAsAbilityResolves`/`mayCastExiledElseDamage` Morph-land & `!forcedPerm`,
`castAsPartOfResolution`/`copyAndCast` land rejection, `copyAndCast`/`castFreeCopy`
`anyMana`/`payLife`/`castsLeft == 0`, `grantPlayPermToMoved` `maxTotalManaValue?`/`asFlashback` &
Widow guards, Tarmogoyf/`graveyardCardsOfSubtype`/`instantSorceryInGraveyard` `isDiscardableCard`,
and `ResolutionChoices` `defaultChoiceAction` vs `answerResolutionChoice` panic/stale/empty/
`max == 0` safety -/
section Phase61Item4EventAlignment

private def mustHold61i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase61Item4EventAlignment failed: {label}"

private def replayOk61i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand afterDraw p0

  -- 4a. `Costs.playManaCost` `flashbackUntilEot` on `.stack` does NOT stack `freeSelf`/`freeRG`
  --     (`CR 118.9a / 702.34a`)!
  let freeSelfSpell : CardDef := {
    name := "P61i4 FreeSelfFb", manaCost := ManaCost.ofGenericAndColor 2 .white, types := #[.instant]
    staticAbilities := #[.costModifier none .thisSpell .alternativeFree]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gFb0 := insertObject g0 freeSelfSpell p0 (.graveyard p0)
  let fbGyId := (gFb0.player p0).graveyard.back!
  let gFb1 := gFb0.createEffect (ContinuousEffectSpec.flashbackUntilEot fbGyId) (cause := some testCause)
  let gFbCast := mustApply gFb1 p0 (.cast fbGyId)
  let fbNoStackOk :=
    gFbCast.pending == .activateManaAbilities p0 &&
    gFbCast.proposedSpell.any (fun pr => pr.cost == ManaCost.ofGenericAndColor 2 .white)

  -- 4b. Layer-6 Morph/Kicker/Gift/Teamwork across `announceKicker`, `announceTeamwork`, `announceX`,
  --     `afterModesChosen`, `afterAdditionalCostAnnounced`, and `afterOptionalAdditionalCost`!
  --     (i) Layer-6 Morph on a `{X}` spell: accepting logs `"face down"` (not `"kicks"`),
  --         declining opens `.chooseX p0`!
  let xCreatureDef : CardDef := {
    creature "P61i4 XBear" { symbols := #[.x, .colored .green] } #["Bear"] 2 2 with
    types := #[.creature]
  }
  let morphHandLord : CardDef := {
    name := "P61i4 MorphHandLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.hand], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])])
    ]
  }
  let gMorphX0 :=
    (insertObject (addPermanent g0 morphHandLord p0 p0) xCreatureDef p0 (.hand p0)).record
      (GameEvent.manaAdded g0.turnNumber p0
        #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }, { mana := .colored .green }])
  let gMorphXCast := mustApply gMorphX0 p0 (.cast (gMorphX0.player p0).hand.back!)
  let gMorphXAccept := mustApply gMorphXCast p0 (.announceKicker true)
  let gMorphXDecline := mustApply gMorphXCast p0 (.announceKicker false)
  --     (ii) Layer-6 Teamwork on a `{X}` spell: `announceX` opens `.chooseTeamwork`, AND
  --          `announceTeamwork` accepts Layer-6 granted Teamwork cleanly!
  let twLordDef : CardDef := {
    name := "P61i4 TwStackLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .hasType .creature }
        (.grantKeywords #[.teamwork 2])
    ]
  }
  let gTwX0 :=
    addPermanent (insertObject (addPermanent g0 twLordDef p0 p0) xCreatureDef p0 (.hand p0)) bear p0 p0
  let twBearId := (gTwX0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gTwXCast := mustApply gTwX0 p0 (.cast (gTwX0.player p0).hand.back!)
  let gTwXChosen := mustApply gTwXCast p0 (.chooseX 1)
  let gTwXAnnounced :=
    mustApply (mustApply gTwXChosen p0 (.announceTeamwork true)) p0 (.choosePermanents #[twBearId])
  --     (iii) Layer-6 Kicker after modal choice (`afterModesChosen`) & mandatory additional cost
  --           (`afterAdditionalCostAnnounced`) & optional additional cost (`afterOptionalAdditionalCost`)!
  let kickStackLord : CardDef := {
    name := "P61i4 KickStackLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .hasType .sorcery }
        (.grantKeywords #[.kicker (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)])])
    ]
  }
  let modalSorcDef : CardDef := {
    name := "P61i4 ModalSorc", manaCost := ManaCost.zero, types := #[.sorcery]
    spellAbility := some {
      effect := { body := .chooseModes {
        modes := #[Effect.gainLife 1, Effect.gainLife 2]
      } }
    }
  }
  let addCostSorcDef : CardDef := {
    name := "P61i4 AddCostSorc", manaCost := ManaCost.zero, types := #[.sorcery]
    spellAbility := some {
      effect := Effect.gainLife 1
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.discardCardOrPayGeneric 2)]
    }
  }
  let optCostSorcDef : CardDef := {
    name := "P61i4 OptCostSorc", manaCost := ManaCost.zero, types := #[.sorcery]
    keywords := #[.kicker (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)])]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let twSorcLordDef : CardDef := {
    name := "P61i4 TwSorcLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .hasType .sorcery }
        (.grantKeywords #[.teamwork 2])
    ]
  }
  let gModK0 := insertObject (addPermanent g0 kickStackLord p0 p0) modalSorcDef p0 (.hand p0)
  let gModKCast := mustApply gModK0 p0 (.cast (gModK0.player p0).hand.back!)
  let gModKChosen := mustApply gModKCast p0 (.chooseMode 0)
  let gAddK0 := insertObject (insertObject (addPermanent g0 kickStackLord p0 p0) forest p0 (.hand p0)) addCostSorcDef p0 (.hand p0)
  let gAddKCast := mustApply gAddK0 p0 (.cast (gAddK0.player p0).hand.back!)
  let gAddKAfter := mustApply gAddKCast p0 (.chooseAdditionalCost true)
  let gOptK0 := addPermanent (insertObject (addPermanent g0 twSorcLordDef p0 p0) optCostSorcDef p0 (.hand p0)) bear p0 p0
  let gOptKCast := mustApply gOptK0 p0 (.cast (gOptK0.player p0).hand.back!)
  let gOptKAfter := mustApply gOptKCast p0 (.announceKicker false)
  let layer6PropContsOk :=
    mustHold61i4 "4b_morphCastPending" (gMorphXCast.pending == .chooseKicker p0) &&
    mustHold61i4 "4b_morphAcceptLog" (gMorphXAccept.log.any (fun s => (s.splitOn "face down").length > 1)) &&
    mustHold61i4 "4b_morphNoKicksLog" (!gMorphXAccept.log.any (fun s => (s.splitOn "kicks").length > 1)) &&
    mustHold61i4 "4b_morphDeclineChooseX" (gMorphXDecline.pending == .chooseX p0) &&
    mustHold61i4 "4b_twXChosen" (gTwXChosen.pending == .chooseTeamwork p0) &&
    mustHold61i4 "4b_twXAnnounced" (gTwXAnnounced.proposedSpell.any (fun pr => pr.teamworkCreatures == #[twBearId])) &&
    mustHold61i4 "4b_modKChosen" (gModKChosen.pending == .chooseKicker p0) &&
    mustHold61i4 "4b_addKAfter" (gAddKAfter.pending == .chooseKicker p0) &&
    mustHold61i4 "4b_optKAfter" (gOptKAfter.pending == .chooseTeamwork p0)

  -- 4c. `castExiledAsAbilityResolves` & `mayCastExiledElseDamage` Morph-land & `!forcedPerm`,
  --     and `castAsPartOfResolution` / `copyAndCast` reject non-Morph lands (`CR 305.9 / 707.12`)!
  let morphLandDef : CardDef := {
    name := "P61i4 MorphLand", manaCost := ManaCost.empty, types := #[.land]
    keywords := #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])]
  }
  let gExML0 :=
    (insertObject g0 morphLandDef p0 .exile).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }])
  let exMLId := (gExML0.objects.filter (·.zone == .exile)).back!.id
  let gExMLPrompt := gExML0.change (.pending (.mayCastExiledElseDamage p0 exMLId 2 none))
  let gExMLCast :=
    match gExMLPrompt.castExiledAsAbilityResolves p0 exMLId with
    | .ok g => g
    | .error e => panic! s!"gExMLCast failed: {e}"
  let gExMLForcedPrompt :=
    (gExML0.createEffect
      (.permission (some p0) (.playFromExile exMLId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)).change (.pending (.mayCastExiledElseDamage p0 exMLId 2 none))
  let exMLForcedErr :=
    match gExMLForcedPrompt.castExiledAsAbilityResolves p0 exMLId with
    | .error _ => true
    | .ok _ => false
  -- `mayCastExiledElseDamage` offers Morph-land when `!payLifeInsteadOfMana`, and does NOT enter
  -- the `mayCastExiledElseDamage` shortcut when `payLifeInsteadOfMana := true`!
  let gElseMLOffer :=
    gExML0.applyUnified p0
      { body := .bind ⟨3⟩
          (.stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
            { duration := .untilEndOfTurn, landsAllowed := false, freeCast := false }))
          (.ifCond (.not (.stepSucceeded ⟨3⟩))
            (.damage (.deal .this (.players (.matching .opponent .any)) (.const 2) {}))
            .noop) } #[]
  let gElseMLPayLife :=
    gExML0.applyUnified p0
      { body := .bind ⟨3⟩
          (.stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
            { duration := .untilEndOfTurn, landsAllowed := false, payLifeInsteadOfMana := true }))
          (.ifCond (.not (.stepSucceeded ⟨3⟩))
            (.damage (.deal .this (.players (.matching .opponent .any)) (.const 2) {}))
            .noop) } #[]
  -- `castAsPartOfResolution` and `copyAndCast` reject plain lands even with `landsAllowed := true`!
  let gExForest := insertObject g0 forest p0 .exile
  let exForestId := (gExForest.objects.filter (·.zone == .exile)).back!.id
  let gResLand := gExForest.castAsPartOfResolution p0 exForestId (withoutManaCost := true)
  let gCopyLand :=
    gExForest.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, copyAndCast := true, landsAllowed := true, freeCast := true }) } #[]
  let morphAndLandCastOk :=
    gExMLCast.pending == .chooseKicker p0 &&
    exMLForcedErr &&
    (match gElseMLOffer.pending with | .mayCastExiledElseDamage .. => true | _ => false) &&
    !(match gElseMLPayLife.pending with | .mayCastExiledElseDamage .. => true | _ => false) &&
    gResLand.pending == .none && gResLand.stack.isEmpty &&
    gCopyLand.pending == .none

  -- 4d. `copyAndCast` & `castFreeCopy`: `anyMana`, `payLifeEqualManaValue` -> `prop.payLife`,
  --     `maxCasts? == some 0`, and `castsLeft == 0` error!
  let copyLifeSpell : CardDef := {
    name := "P61i4 CopyLifeSpell", manaCost := ManaCost.ofGenericAndColor 2 .blue, types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gCopyLife0 := insertObject (insertObject g0 copyLifeSpell p0 .exile) copyLifeSpell p0 .exile
  let gCopyLifePrompt :=
    gCopyLife0.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, copyAndCast := true, anyManaColor := true,
            payLifeInsteadOfMana := true }) } #[]
  let copyLifeIds :=
    match gCopyLifePrompt.pending with
    | .resolutionChoice _ (.castCopiesFree ids _ _) => ids
    | _ => #[]
  let gCopyLifeCast := mustApply gCopyLifePrompt p0 (.cast copyLifeIds[0]!)
  let copyLifePerm :=
    gCopyLifePrompt.activeEffects.findSome? fun (_, s) =>
      match s with | .permission _ (.playFromExile cid pm) _ => if cid == copyLifeIds[0]! then some pm else none | _ => none
  -- `maxCasts? == some 0` skips copy creation/cast offers:
  let gCopyZeroMax :=
    gCopyLife0.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, copyAndCast := true, freeCast := true, maxCasts? := some 0 }) } #[]
  -- `castFreeCopy` rejects `castsLeft == 0`:
  let gZeroLeftPrompt :=
    gCopyLifePrompt.change (.pending (.resolutionChoice p0 (.castCopiesFree copyLifeIds 10 0)))
  let zeroLeftErr :=
    match gZeroLeftPrompt.apply p0 (.cast copyLifeIds[0]!) with
    | .error _ => true
    | .ok _ => false
  let copyAndFreeCopyOk :=
    copyLifePerm.any (fun pm => pm.anyMana && pm.payLifeEqualManaValue) &&
    gCopyLifeCast.proposedSpell.any (fun pr => pr.payLife == 3) &&
    gCopyZeroMax.pending == .none &&
    zeroLeftErr

  -- 4e. `grantPlayPermToMoved` `maxTotalManaValue?` & `asFlashback` (`isDiscardableCard`),
  --     and Widow shortcut guards (`payLifeInsteadOfMana := true`, `condition?.isSome`)!
  let mv5Spell : CardDef := {
    name := "P61i4 MvFive", manaCost := ManaCost.ofGeneric 5, types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gMvEx0 := insertObject g0 mv5Spell p0 (.hand p0)
  let gMvExDone :=
    gMvEx0.applyUnified p0
      { body := .moveZone (.inZones { zones := #[.hand], owner := .ofPlayer .you } .anyObject)
          .exile .exile
          { grantPlayPerm? := some {
              duration := .untilEndOfTurn, maxTotalManaValue? := some (.const 3) } } } #[]
  let gMv3Ex0 := insertObject g0 copyLifeSpell p0 (.hand p0)
  let gMv3ExDone :=
    gMv3Ex0.applyUnified p0
      { body := .moveZone (.inZones { zones := #[.hand], owner := .ofPlayer .you } .anyObject)
          .exile .exile
          { grantPlayPerm? := some {
              duration := .untilEndOfTurn, maxTotalManaValue? := some (.const 3) } } } #[]
  -- Copy moved to exile (`isCastableObject == true`, `isDiscardableCard == false`) must NOT receive
  -- `asFlashback` permission, whereas a real card moved to exile does:
  let copyObjId : ObjectId := ⟨g0.nextObjectId⟩
  let copyCardObj : GameObject := {
    id := copyObjId, printed := copyLifeSpell, owner := p0, controller := some p0
    zone := .stack, timestamp := g0.timestamp + 1, isCopy := true
  }
  let gCopyFb0 := g0.record (GameEvent.created g0.turnNumber p0 (g0.snapshot copyCardObj) (cause := testCause))
  let gCopyFbDone :=
    gCopyFb0.applyUnified p0
      { body := .moveZone (.inZones { zones := #[.stack], owner := .any } .anyObject) .exile .exile
          { grantPlayPerm? := some { duration := .untilEndOfTurn, asFlashback := true } } } #[]
  let gCardFbDone :=
    gMv3Ex0.applyUnified p0
      { body := .moveZone (.inZones { zones := #[.hand], owner := .ofPlayer .you } .anyObject)
          .exile .exile
          { grantPlayPerm? := some { duration := .untilEndOfTurn, asFlashback := true } } } #[]
  -- Widow shortcut must NOT drop `payLifeInsteadOfMana := true` or `condition?.isSome`!
  let gWidowBase := insertObject g0 copyLifeSpell p0 .exile
  let gWidowPayLife :=
    gWidowBase.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, anyManaColor := true, landsAllowed := false,
            freeCast := false, payLifeInsteadOfMana := true }) } #[]
  let gWidowCond :=
    gWidowBase.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, anyManaColor := true, landsAllowed := false,
            freeCast := false,
            condition? := some (.exists (.inZones .battlefield
              (.all #[.hasSubtype (.literal .goblin), .controlledBy .you]))) }) } #[]
  let grantAndWidowOk :=
    !(gMvExDone.activeEffects.any fun (_, s) => match s with | .permission _ (.playFromExile _ _) _ => true | _ => false) &&
    (gMv3ExDone.activeEffects.any fun (_, s) => match s with | .permission _ (.playFromExile _ _) _ => true | _ => false) &&
    gCopyFbDone.objects.any (·.zone == .exile) &&
    !(gCopyFbDone.activeEffects.any fun (_, s) => match s with | .permission _ (.flashback _) _ => true | _ => false) &&
    (gCardFbDone.activeEffects.any fun (_, s) => match s with | .permission _ (.flashback _) _ => true | _ => false) &&
    gWidowPayLife.activeEffects.any (fun (_, s) => match s with | .permission _ (.playFromExile _ pm) _ => pm.payLifeEqualManaValue && pm.anyMana | _ => false) &&
    gWidowCond.activeEffects.any (fun (_, s) => match s with | .permission _ (.playFromExile _ pm) _ => pm.requireSubtype == some .goblin && pm.anyMana | _ => false)

  -- 4f. Tarmogoyf (`graveyardCardTypeCount`), `graveyardCardsOfSubtype`, and
  --     `instantSorceryInGraveyard` ignore dead tokens (`isDiscardableCard`, CR 108.2b / 111.6)!
  let tokInstDef : CardDef := {
    name := "P61i4 InstTok", types := #[.instant, .creature], subtypes := #["Goblin"], isToken := true
  }
  let (gGyTok0, tokGyObj) := g0.createOneToken p0 tokInstDef (cause := some testCause)
  let (gGyTok, _) := gGyTok0.move tokGyObj.id (.graveyard p0) none (cause := some testCause)
  let gyNonCardOk :=
    gGyTok.graveyardCardTypeCount == 0 &&
    (gGyTok.graveyardCardsOfSubtype p0 .goblin).isEmpty &&
    gGyTok.instantSorceryInGraveyard p0 == 0

  -- 4g. `ResolutionChoices` `defaultChoiceAction` vs `answerResolutionChoice` panic/stale/empty/
  --     `max == 0` safety across all 19 variants!
  let staleId : ObjectId := ⟨99988⟩
  let gEmptyBoth := emptyHand g0 p1
  let safeChoices : Array ResolutionChoice := #[
    .extrapolatePick p0 #[staleId],
    .mayRevealToHand #[staleId] #[staleId] false,
    .sacrificeDamager #[staleId] #[] p0 #[],
    .chooseCards #[staleId] 1 (.amassArmy .orc 1 none),
    .chooseCards #[staleId] 0 (.amassArmy .orc 1 none),
    .chooseCards #[staleId] 0 (.toHand true),
    .discardFromRevealedHand p1 false,
    .discardThen .noop none none,
    .exileFromRevealedHand p1 none,
    .chooseKeyword staleId #[],
    .sacrificeCreatureEach p0 #[] #[],
    .discardTwo p0 #[] 0 #[],
    .chooseCreatureType #[],
    .sacrificeLeastPower #[staleId],
    .sacrificeNontokenEach #[] #[],
    .discardThenDraw,
    .hydeRemoveCounter #[staleId],
    .palisadeCreatureType #[],
    .blackGatePlayer staleId #[],
    .chooseEnteringAttackTarget #[] #[] none
  ]
  -- Test `.costPicks _ #[] true` with an active `proposedSpell`:
  let gCostPicksP := gFbCast.change (.pending (.resolutionChoice p0 (.costPicks staleId #[] true)))
  let costPicksDone? :=
    gCostPicksP.apply p0 (defaultChoiceAction gCostPicksP p0 (.costPicks staleId #[] true))
  -- Also test `.discardTwo` when player has exactly 1 card in hand (`< 2`):
  let gOneCard := insertObject gEmptyBoth forest p0 (.hand p0)
  let resChoicesSafeOk :=
    safeChoices.all (fun ch =>
      let gP := gEmptyBoth.change (.pending (.resolutionChoice p0 ch))
      let act := defaultChoiceAction gP p0 ch
      match gP.apply p0 act with
      | .ok gDone => gDone.pending == .none
      | .error _ => false) &&
    (match costPicksDone? with
     | .ok gDone => gDone.pending == .none && gDone.proposedSpell.isNone
     | .error _ => false) &&
    (let ch : ResolutionChoice := .discardTwo p0 #[] 0 #[]
     let gP := gOneCard.change (.pending (.resolutionChoice p0 ch))
     let act := defaultChoiceAction gP p0 ch
     match gP.apply p0 act with
     | .ok gDone => gDone.pending == .none
     | .error _ => false)

  mustHold61i4 "4a_fbNoStack" fbNoStackOk &&
  mustHold61i4 "4b_layer6PropConts" layer6PropContsOk &&
  mustHold61i4 "4c_morphAndLandCast" morphAndLandCastOk &&
  mustHold61i4 "4d_copyAndFreeCopy" copyAndFreeCopyOk &&
  mustHold61i4 "4e_grantAndWidow" grantAndWidowOk &&
  mustHold61i4 "4f_gyNonCard" gyNonCardOk &&
  mustHold61i4 "4g_resChoicesSafe" resChoicesSafeOk &&
  mustHold61i4 "4.replay"
    (replayOk61i4 #[gFbCast, gMorphXAccept, gMorphXDecline, gTwXAnnounced, gModKChosen,
      gAddKAfter, gOptKAfter, gExMLCast, gElseMLPayLife, gCopyLifeCast, gMvExDone,
      gMv3ExDone, gCopyFbDone, gCardFbDone, gWidowPayLife, gWidowCond, gGyTok])

end Phase61Item4EventAlignment

end Mtg.Engine.EventTests
