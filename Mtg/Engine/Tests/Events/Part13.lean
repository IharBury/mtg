import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase47Item1EventAlignment

private def mustHold47i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase47Item1EventAlignment failed: {label}"

private def replayOk47i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with name := "P47i1 LegBear", supertypes := #[.legendary] }

  -- 1a(i). `concedePlayersLoop` `anyContinuationGrantsPriority` / `firstContinuationPriorityGrant?`
  --        termination (`true` vs `false`, without infinite mutual recursion):
  let cplGrantsP1 : PendingReplacement :=
    .concedePlayersLoop #[p2] false false true (some p1) none none false #[] none
  let cplCombatDmg : PendingReplacement :=
    .concedePlayersLoop #[p2] false false false none (some true) none false #[] none
  let gCplGrant :=
    g4.changes #[.pushContinuationFrame {}, .pendingReplacement (some cplGrantsP1)]
  let gCplNoGrant :=
    g4.changes #[.pushContinuationFrame {}, .pendingReplacement (some cplCombatDmg)]

  -- 1a(ii). `continuationGrantsPriority` vs `firstPriorityGrantRecipient?` `some none` separation:
  --         All-passed non-empty stack (`resolveTop`) grants priority (`continuationGrantsPriority == true`),
  --         has `priorityRecipientOfContinuation? == none` AND `firstPriorityGrantRecipient? == none` (NOT `some none`),
  --         so `finishAndGrantPriority` does NOT overwrite `pendingPriority`:
  let zeroInstDef : CardDef := {
    name := "P47i1 Inst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellEffect := some (Effect.gainLife 1)
  }
  let gStackHand := insertObject g4 zeroInstDef p0 (.hand p0)
  let gStackReady := mustApply gStackHand p0 (.cast (gStackHand.player p0).hand.back!)
  let gAllPassedStack := gStackReady.change (.consecutivePasses 4)
  let fcAllPassed : PendingReplacement := .finishConcede true none none none false #[] none
  let gAllPassedQueued :=
    gAllPassedStack.changes #[
      .pendingPriority (some p2),
      .pushContinuationFrame {},
      .pendingReplacement (some fcAllPassed) ]
  let preAllPassedLen := gAllPassedQueued.events.size
  let gAllPassedAfterGrant := gAllPassedQueued.finishAndGrantPriority p0
  let noAllPassedOverwrite :=
    !(gAllPassedAfterGrant.events.extract preAllPassedLen gAllPassedAfterGrant.events.size).any fun ev =>
      ev.change == .engine (.pendingPriority (some p0))

  -- Conversely, `finishConcede` popping an implicit `.finishFraChoice` returns `some none` (`hasImplicitPriorityContinuation == true`):
  let fcPopImplicit : PendingReplacement := .finishConcede false none none none true #[] none
  let gFcImplicit0 :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement .finishFraChoice,
      .pendingReplacement (some fcPopImplicit) ]
  let gFcImplicitGranted := gFcImplicit0.finishAndGrantPriority p3

  -- `.beginStepCont .untap` with `hasQueuedPending == true`: `continuationGrantsPriority == true`, `firstPriorityGrantRecipient? == none`:
  let untapCarryOk :=
    g4.continuationGrantsPriority true (.beginStepCont .untap) &&
    g4.firstPriorityGrantRecipient? true (.beginStepCont .untap) == none

  -- 1a(iii). `openCont == true` post-cast recipient (`g.activePlayer == p0`, not `caster == p2`),
  --          non-granting `finishPostCast` prompt (`pendingMayCastFromExile`), and `finishAndGrantPriority`
  --          stashing non-active `pendingPriority` (`some p2`) before `promptTriggerTargetsIfNeeded`:
  let gAnchorBase := addPermanent g4 ({ name := "P47i1 Anchor", types := #[.artifact] }) p0 p0
  let tgtTrigAnchor := (gAnchorBase.permanentsOf p0).back!
  let tgtTrigAb : TriggeredAbility :=
    .triggered .youGainLife
      { targeting := .of .player, resolution := .gainLife (.fixed 1), phrase := "Target player gains 1 life." }
  let gWithUnannTrig :=
    gAnchorBase.putTriggeredAbilityOnStack p0 tgtTrigAnchor tgtTrigAb "triggers" (eventCause := some testCause)
  let gTrigTargetGranted := gWithUnannTrig.finishAndGrantPriority p2
  let gExCastPromptBase := insertObject g4 zeroInstDef p2 .exile
  let exCastPromptId := (gExCastPromptBase.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gFinishPostCastPrompt :=
    gExCastPromptBase.changes #[
      .pushContinuationFrame {},
      .pendingMayCastFromExile (some (p2, #[exCastPromptId], 1)) ]

  let item1aOk :=
    mustHold47i1 "1a_concedePlayersLoopTermination"
      (gCplGrant.anyContinuationGrantsPriority &&
       gCplGrant.firstContinuationPriorityGrant? == some (some p1) &&
       !gCplNoGrant.anyContinuationGrantsPriority &&
       gCplNoGrant.firstContinuationPriorityGrant? == none) &&
    mustHold47i1 "1a_someNoneSeparation"
      (gAllPassedStack.continuationGrantsPriority false fcAllPassed &&
       gAllPassedStack.priorityRecipientOfContinuation? false fcAllPassed == none &&
       gAllPassedStack.firstPriorityGrantRecipient? false fcAllPassed == none &&
       !gAllPassedQueued.hasImplicitPriorityContinuation &&
       noAllPassedOverwrite &&
       gFcImplicit0.hasImplicitPriorityContinuation &&
       gFcImplicitGranted.priority == p3 &&
       untapCarryOk) &&
    mustHold47i1 "1a_openContTriggerTargetPendingPriority"
      (g4.continuationGrantsPriority false (.finishPostCast p2 true false true) &&
       g4.priorityRecipientOfContinuation? false (.finishPostCast p2 true false true) == some p0 &&
       g4.priorityRecipientOfContinuation? false (.finishPostCast p2 true false false) == some p2 &&
       !gFinishPostCastPrompt.continuationGrantsPriority false (.finishPostCast p2 true false true) &&
       gFinishPostCastPrompt.priorityRecipientOfContinuation? false (.finishPostCast p2 true false true) == none &&
       gTrigTargetGranted.pending == .chooseTargets p0 &&
       gTrigTargetGranted.pendingPriority == some p2)

  -- 1b(i). Step / turn / cleanup pause & skipped-`.draw` probes:
  let csntNoBegin : PendingReplacement := .continueStartNextTurn p1 #[] false
  let gP0Gone := mustApply g4 p0 .concede
  -- `continueStartNextTurn` (`runBeginTurn == true`) continues probing past a `.chooseLegend` pause in `expireUntilNextTurnEffects p2`:
  let gCsntLeg0 := addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0
  let csntLeg2Id := (gCsntLeg0.permanentsOf p0)[1]!.id
  let gCsntLeg1 :=
    mustApply
      (gCsntLeg0.createEffect (.layered (.objects #[csntLeg2Id]) (.control p2) (.untilNextTurnOf p2))
        (cause := some testCause))
      p2 .concede
  let csntLegendPauseOk :=
    gCsntLeg1.continuationGrantsPriority false (.continueStartNextTurn p1 #[p2] true) &&
    gCsntLeg1.priorityRecipientOfContinuation? false (.continueStartNextTurn p1 #[p2] true) == some p1
  -- Turn 1 2-player upkeep (`started`) skips `.draw` -> `.precombatMain` grants priority to `p0`:
  let skippedDrawOk :=
    started.continuationGrantsPriority false (.beginStepCont .draw) &&
    started.priorityRecipientOfContinuation? false (.beginStepCont .draw) == some p0
  -- Cleanup (`cleanupStepAfterDiscardRecipient?`) drains `.endControlExileLoop` when `sbaPaused` instead of dropping `pendingReplacement`:
  let ltbBearDef : CardDef := {
    bear with
    name := "P47i1 LtbBear"
    triggeredAbilities := #[.triggered .leaving (Effect.gainLife 1)]
  }
  let gCleanupDrain0 := addPermanent g4 ltbBearDef p0 p0
  let ltbPerm := (gCleanupDrain0.permanentsOf p0)[0]!
  let gCleanupDrainPaused :=
    gCleanupDrain0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement
        (some (.endControlExileLoop #[(ltbPerm.id, ltbPerm.name, some p0)] (some testCause) none #[])),
      .pending (.chooseReplacement p0 #[]) ]
  let cleanupDrainOk :=
    gCleanupDrainPaused.continuationGrantsPriority false (.finishPostStep .cleanupStepAfterDiscard) &&
    gCleanupDrainPaused.priorityRecipientOfContinuation? false (.finishPostStep .cleanupStepAfterDiscard) == some p0

  -- 1b(ii). Associative `.seq` first-grant `.finishFraChoice` & reversal forwarding across cost/activation leaves,
  --         plus `.restorePending _ (popOuter := true) (rewindProposal := none)`:
  let sorc3Def : CardDef := {
    name := "P47i1 Sorc3"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 2)
  }
  let gUnpayable0 := (insertObject (emptyHand g4 p0) sorc3Def p0 (.hand p0)).change (.pendingPriority (some p2))
  let gUnpayableProp := (mustApply gUnpayable0 p0 (.cast (gUnpayable0.player p0).hand.back!)).change (.pending .none)
  let revCostStep : PendingReplacement :=
    .finishPostStep (.resumeProposalCostAfterLeave p0 (.discardForAdditionalCost p0))
  -- Both left-associated and right-associated `.seq` with `.finishFraChoice` ahead of `.receivePriority p3`
  -- reverse `gUnpayableProp` and grant `pendingPriority == p2`, whereas `.receivePriority p3` first grants `p3`:
  let gSeqFinishFraLeft :=
    gUnpayableProp.resumePendingReplacement (.seq (.seq revCostStep .finishFraChoice) (.receivePriority p3))
  let gSeqFinishFraRight :=
    gUnpayableProp.resumePendingReplacement (.seq revCostStep (.seq .finishFraChoice (.receivePriority p3)))
  let gSeqExplicitP3 :=
    gUnpayableProp.resumePendingReplacement (.seq revCostStep (.seq (.receivePriority p3) .finishFraChoice))
  -- Non-cost-prompt `.restorePending .none true none #[] none` whose outer `outerPendingReplacements.back?` reverses:
  -- `stepCanReverseProposal` detects reversal so `.seq` stops before `.receivePriority p3`!
  let gRestorePopRev :=
    (gUnpayableProp.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement revCostStep ]).resumePendingReplacement
      (.seq (.restorePending .none true none #[] none) (.seq .finishFraChoice (.receivePriority p3)))

  let item1bOk :=
    mustHold47i1 "1b_stepTurnCleanupProbes"
      (!g4.continuationGrantsPriority false csntNoBegin &&
       g4.priorityRecipientOfContinuation? false csntNoBegin == none &&
       g4.continuationGrantsPriority false .beginTurnAfterStartExpiry &&
       g4.priorityRecipientOfContinuation? false .beginTurnAfterStartExpiry == some p0 &&
       !gP0Gone.continuationGrantsPriority false .beginTurnAfterStartExpiry &&
       csntLegendPauseOk &&
       skippedDrawOk &&
       cleanupDrainOk) &&
    mustHold47i1 "1b_seqFinishFraAndRestoreReversal"
      (gSeqFinishFraLeft.proposedSpell.isNone &&
       gSeqFinishFraLeft.priority == p2 &&
       gSeqFinishFraRight.proposedSpell.isNone &&
       gSeqFinishFraRight.priority == p2 &&
       gSeqExplicitP3.proposedSpell.isNone &&
       gSeqExplicitP3.priority == p3 &&
       gRestorePopRev.proposedSpell.isNone &&
       gRestorePopRev.priority == p2)

  -- 1c(i). `StateBasedActions.mergeLeaveArgs` (`saved? == some` + `rest?`) & `chainOrMergeLeave` preferring `.leavePlayersWhoLost`:
  let gLegBase := addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0
  let legIds := ((gLegBase.permanentsOf p0).filter (·.name == legBearDef.name)).map (·.id)
  let gMergeBoth0 :=
    gLegBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement
        (some (.seq .checkSBA
                    (.seq (.leavePlayersWhoLost (some (.mayPayGeneric p0 2)) false #[p2] none)
                          (.gainLife p0 7 (some testCause))))),
      .pending (.chooseLegend p0 legBearDef.name legIds) ]
  let (gMergeBoth1, _, _) :=
    ((gMergeBoth0.record (GameEvent.playerLost gMergeBoth0.turnNumber p2 .lifeZeroOrLess)).record
      (GameEvent.playerLost gMergeBoth0.turnNumber p3 .lifeZeroOrLess)).checkSBACountedWithLeaves
      (savedIn := some (.mayPayGeneric p0 5)) (departedIn := #[p3])
  let gMergePrompt1 := mustApply gMergeBoth1 p0 (.keepLegend legIds[0]!)
  let gMergePrompt2 := mustApply gMergePrompt1 p0 .decline
  let gMergeDone := mustApply gMergePrompt2 p0 .decline

  -- 1c(ii). Deferred post-`curPending` `Leaving.playerLeavesGameCore` stash reopen (`reopenDeferredExileCasts`):
  let gStash0 := insertObject g4 sorc3Def p0 .exile
  let stashExId := (gStash0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gStashBlockedByP2 :=
    gStash0.changes #[
      .pushContinuationFrame {},
      .continuation (.pendingMayCastFromExile (some (p0, #[stashExId], 1))),
      .pending (.mayPayGeneric p2 2) ]
  let gStashReopened := mustApply gStashBlockedByP2 p2 .concede

  let item1cOk :=
    mustHold47i1 "1c_mergeLeaveArgsBothPromptsAndTail"
      (gMergePrompt1.pending == .mayPayGeneric p0 2 &&
       gMergePrompt2.pending == .mayPayGeneric p0 5 &&
       gMergeDone.pending == .none &&
       (gMergeDone.player p0).life == 27 &&
       (gMergeDone.player p2).leftTheGame &&
       (gMergeDone.player p3).leftTheGame) &&
    mustHold47i1 "1c_reopenDeferredExileStash"
      (gStashReopened.pending == .fraChoice p0 (.mayCastUpToFromExile #[stashExId] 1) &&
       gStashReopened.pendingMayCastFromExile.isNone)

  mustHold47i1 "1a.concedeTerminationAndPriorityGrants" item1aOk &&
  mustHold47i1 "1b.stepTurnProbesAndSeqForwarding" item1bOk &&
  mustHold47i1 "1c.mergeLeaveArgsAndDeferredStashReopen" item1cOk &&
  mustHold47i1 "1.replay"
    (replayOk47i1 #[gAllPassedAfterGrant, gFcImplicitGranted, gTrigTargetGranted,
      gSeqFinishFraLeft, gSeqFinishFraRight, gSeqExplicitP3, gRestorePopRev,
      gMergeDone, gStashReopened])

end Phase47Item1EventAlignment

section Phase47Item2EventAlignment

private def mustHold47i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase47Item2EventAlignment failed: {label}"

private def replayOk47i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let sorc3Def : CardDef := {
    name := "P47i2 Sorc3"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 2)
  }

  -- 2a(i). Strict live-exile vs historical `depIdx` `requireSubtype` filtering + `Turns` `hadPlayable` expiry logs:
  let gReqSub0 := insertObject g4 sorc3Def p0 .exile
  let reqExId := (gReqSub0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gReqNoElf :=
    gReqSub0.createEffect
      (.permission (some p0)
        (.playFromExile reqExId { player := p0, withoutManaCost := true, requireSubtype := some .elf })
        .untilEndOfTurn)
      (cause := some testCause)
  let reqObjNoElf := gReqNoElf.object! reqExId
  let preNoElfEotLog := gReqNoElf.log.size
  let gReqNoElfEot := gReqNoElf.clearEOT
  let noElfEotLogs := gReqNoElfEot.log.extract preNoElfEotLog gReqNoElfEot.log.size
  -- Add an Elf: now playable, `clearEOT` logs `"can no longer be played from exile"`, AND if cast onto `.stack`
  -- before the Elf leaves, historical `depIdx` preserves `withoutManaCost` on `.stack`!
  let gReqWithElf := addPermanent gReqNoElf llanowarElves p0 p0
  let elfId := (gReqWithElf.permanentsOf p0).find? (·.name == llanowarElves.name) |>.get!.id
  let preWithElfEotLog := gReqWithElf.log.size
  let gReqWithElfEot := gReqWithElf.clearEOT
  let withElfEotLogs := gReqWithElfEot.log.extract preWithElfEotLog gReqWithElfEot.log.size
  let gReqOnStack := mustApply gReqWithElf p0 (.cast reqExId)
  let reqStackId := gReqOnStack.stack.back!.objectId
  let (gReqElfGoneOnStack, _) := gReqOnStack.move elfId .exile none (cause := some testCause)

  -- 2a(ii). CR 707.12 card-copy Adventure in `.exile -> .stack`, departed-stack tracing, and return-to-`.exile` stop:
  let advCardDef : CardDef := {
    bear with
    name := "P47i2 CopyKnight"
    manaCost := ManaCost.ofGeneric 3
    adventure := some {
      name := "P47i2 CopyQuest"
      manaCost := ManaCost.ofGeneric 2
      types := #[.instant]
      spellEffect := some (Effect.gainLife 1)
    }
  }
  let gCopyAdvHand := insertObject g4 advCardDef p0 (.hand p0)
  let (gCopyAdv0, copyAdvExId) :=
    gCopyAdvHand.move (gCopyAdvHand.player p0).hand.back! .exile none (isCopy := some true) (cause := some testCause)
  let gCopyAdv1 :=
    gCopyAdv0.createEffect
      (.permission (some p0) (.playFromExile copyAdvExId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gCopyAdvStack := mustApply gCopyAdv1 p0 (.castAdventure copyAdvExId)
  let copyAdvStackId := gCopyAdvStack.stack.back!.objectId
  let copyAdvStackObj := gCopyAdvStack.object! copyAdvStackId
  -- Departed-stack tracing (`reqStackId` moved `.stack -> .graveyard p0`) & return-to-`.exile` stop (`reqStackId` moved `.stack -> .exile`):
  let (gDepartedStack, _) := gReqOnStack.move reqStackId (.graveyard p0) none (cause := some testCause)
  let (gReturnedExile, reExiledId) := gReqOnStack.move reqStackId .exile none (cause := some testCause)

  -- 2a(iii). `CastSpell` `prepPerm` guard skipped when `mayCastExiledBySource` holds:
  let nullSummonerDef : CardDef := {
    bear with
    name := "P47i2 NullSummoner"
    castExiledWithSevenInGraveyard := true
  }
  let prepHostDef : CardDef := {
    bear with
    name := "P47i2 UnprepHost"
    prepareFace := some { name := "P47i2 Prep", manaCost := ManaCost.zero, types := #[.instant], spellEffect := some (Effect.gainLife 1) }
  }
  let gNull0 :=
    Id.run do
      let mut g := addPermanent (addPermanent g4 nullSummonerDef p0 p0) prepHostDef p0 p0
      for _ in [0:7] do
        g := insertObject g bear p0 (.graveyard p0)
      return g
  let nullId := (gNull0.permanentsOf p0).find? (·.name == nullSummonerDef.name) |>.get!.id
  let unprepHostId := (gNull0.permanentsOf p0).find? (·.name == prepHostDef.name) |>.get!.id
  let zeroInstDef2 : CardDef := { name := "P47i2 ZeroBolt", manaCost := ManaCost.zero, types := #[.instant], spellEffect := some (Effect.gainLife 1) }
  let gNull1 := insertObject gNull0 zeroInstDef2 p0 (.hand p0)
  let handBoltId := (gNull1.player p0).hand.back!
  let (gNull2Raw, nullExId) := gNull1.move handBoltId .exile none (cause := some testCause)
  let gNull2 := gNull2Raw.changeObject nullExId (.exiledBy (some nullId))
  let gNullWithStalePrep :=
    gNull2.createEffect
      (.permission (some p0) (.playFromExile nullExId { player := p0, withoutManaCost := true, prepareSource := some unprepHostId }) .untilEndOfTurn)
      (cause := some testCause)
  let gNullCastOk := mustApply gNullWithStalePrep p0 (.cast nullExId)

  let item2aOk :=
    mustHold47i2 "2a_requireSubtypeStrictAndHistorical"
      ((gReqNoElf.playPermissionsFor p0 reqObjNoElf).isEmpty &&
       (gReqNoElf.activePlayPermissions reqObjNoElf).isEmpty &&
       (gReqNoElf.bestActivePlayPermission? reqObjNoElf).isNone &&
       !gReqNoElf.playsWithoutPayingManaCost reqObjNoElf &&
       gReqNoElf.playManaCost reqObjNoElf sorc3Def == ManaCost.ofGeneric 3 &&
       !noElfEotLogs.any (·.contains "can no longer be played from exile") &&
       withElfEotLogs.any (· == s!"{sorc3Def.name} can no longer be played from exile") &&
       (gReqElfGoneOnStack.playPermissionsFor p0 (gReqElfGoneOnStack.object! reqStackId)).any (·.withoutManaCost)) &&
    mustHold47i2 "2a_cardCopyAdvDepartedStackAndReExile"
      (copyAdvStackObj.isCopy &&
       copyAdvStackObj.isAdventureSpell &&
       (gCopyAdvStack.playPermissionEntriesOf copyAdvStackId).size == 1 &&
       (gCopyAdvStack.playPermissionFor? p0 copyAdvStackObj).any (·.withoutManaCost) &&
       (gDepartedStack.playPermissionEntriesOf reqStackId).size == 1 &&
       (gReturnedExile.playPermissionEntriesOf reExiledId).isEmpty) &&
    mustHold47i2 "2a_mayCastExiledBySourceSkipsStalePrep"
      (gNullCastOk.stack.size == 1)

  -- 2b. One-shot paid resolution casts (`paidResolutionOrigPerm?`, `FraChoices` `.mayCastCards`)
  --     vs unpayable `payLifeEqualManaValue`, plus `Impending` under clean `.playFromExile` & `Adventure` exile permissions:
  let gPaidRes0 := ((insertObject g4 sorc3Def p0 .exile).loseLife p0 18).addMana p0 .colorless 3
  let paidResExId := (gPaidRes0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gPaidResUnpayableLife :=
    gPaidRes0.createEffect
      (.permission (some p0) (.playFromExile paidResExId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gMayCastCardsPrompt :=
    gPaidResUnpayableLife.change (.pending (.fraChoice p0 (.mayCastCards #[paidResExId] false false)))
  let gMayCastCardsProposed := mustApply gMayCastCardsPrompt p0 (.cast paidResExId)
  let gMayCastCardsPaid := mustApply gMayCastCardsProposed p0 .pay
  -- Conversely, when `p0` has 20 life, `paidResolutionOrigPerm?` DOES select `payLifeEqualManaValue`:
  let gPaidResHealthy0 := insertObject g4 sorc3Def p0 .exile
  let paidResHealthyId := (gPaidResHealthy0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gPaidResHealthy :=
    gPaidResHealthy0.createEffect
      (.permission (some p0) (.playFromExile paidResHealthyId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)

  -- `Impending` under `.playFromExile` (with both `payLifeEqualManaValue` and clean permission):
  let impExDef : CardDef := {
    bear with
    name := "P47i2 ImpendingTitan"
    manaCost := ManaCost.ofGeneric 4
    impending := some (2, ManaCost.ofGeneric 1)
  }
  let gImpEx0 := (insertObject g4 impExDef p0 .exile).addMana p0 .colorless 1
  let impExId := (gImpEx0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gImpEx1 :=
    ((gImpEx0.createEffect
        (.permission (some p0) (.playFromExile impExId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile impExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause))
  let gImpProposed := mustApply gImpEx1 p0 (.cast impExId)
  let gImpChosen := mustApply gImpProposed p0 (.announceKicker true)
  let gImpPaid := mustApply gImpChosen p0 .pay

  -- `adventureExileForbidsRecast` with `mayCastExiledBySource` & `Agent` `!·.fromAdventure`:
  let gAdvNull0 := insertObject gNull0 advCardDef p0 (.hand p0)
  let advHandId := (gAdvNull0.player p0).hand.back!
  let (gAdvNull1Raw, advNullExId) := gAdvNull0.move advHandId .exile none (cause := some testCause)
  let gAdvNull1 := gAdvNull1Raw.changeObject advNullExId (.exiledBy (some nullId))
  let gAdvNullFromAdv :=
    gAdvNull1.createEffect
      (.permission (some p0) (.playFromExile advNullExId { player := p0, fromAdventure := true }) .untilEndOfTurn)
      (cause := some testCause)
  let advNullObj := gAdvNullFromAdv.object! advNullExId
  let gAdvAgent0 := (insertObject (emptyHand g4 p0) advCardDef p0 .exile).addMana p0 .colorless 2
  let advAgentExId := (gAdvAgent0.objects.filter (fun (o : GameObject) => o.zone == Zone.exile)).back!.id
  let gAdvAgentForbidden :=
    gAdvAgent0.createEffect
      (.permission (some p0) (.playFromExile advAgentExId { player := p0, fromAdventure := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gAdvAgentClean :=
    gAdvAgent0.createEffect
      (.permission (some p0) (.playFromExile advAgentExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let agentForbiddenPasses :=
    match Agent.choose gAdvAgentForbidden p0 with | some .pass => true | _ => false
  let agentCleanCastsAdv :=
    match Agent.choose gAdvAgentClean p0 with | some (.castAdventure id) => id == advAgentExId | _ => false

  let item2bOk :=
    mustHold47i2 "2b_paidResSkipsUnpayableLifeGrant"
      (gPaidResUnpayableLife.paidResolutionOrigPerm? p0 (gPaidResUnpayableLife.object! paidResExId) == none &&
       gMayCastCardsPaid.stack.size == 1 &&
       (gMayCastCardsPaid.player p0).manaPool.colorless == 0 &&
       (gMayCastCardsPaid.player p0).life == 2 &&
       (gPaidResHealthy.paidResolutionOrigPerm? p0 (gPaidResHealthy.object! paidResHealthyId)).any (·.payLifeEqualManaValue)) &&
    mustHold47i2 "2b_impendingCleanExileGrant"
      (gImpProposed.pending == .chooseKicker p0 &&
       gImpChosen.proposedSpell.any (fun prop => prop.payLife == 0 && prop.cost == ManaCost.ofGeneric 1) &&
       gImpPaid.stack.size == 1 &&
       (gImpPaid.player p0).life == 20) &&
    mustHold47i2 "2b_advExileRecastAndAgent"
      (!gAdvNullFromAdv.adventureExileForbidsRecast advNullObj (some p0) &&
       !gAdvNullFromAdv.adventureExileForbidsRecast advNullObj none &&
       agentForbiddenPasses &&
       agentCleanCastsAdv)

  -- 2c. Phased-out `coDepartingIds` (`isBattlefieldObject`), copy-before-emblem in `beginTurn`,
  --     emblem-scoped `.copy`, transitive `.fraEmblem`, and multi-object `.copy` restoration logs:
  let embDef : CardDef := { name := "P47i2 Emblem", types := #[] }
  -- Phased-out permanent owned by living `p2` with underlying `.control p3 .indefinite` (departed `p3`, CR 800.4c)
  -- and `.control p0 .untilEndOfTurn` does NOT depart on `clearEOT`, so its copy-restoration log IS emitted!
  let gPhCo0 := addPermanent g4 bear p2 p2
  let phCoId := (gPhCo0.permanentsOf p2)[0]!.id
  let gPhCo1 :=
    mustApply
      ((((gPhCo0.createEffect (.layered (.objects #[phCoId]) (.control p3) .indefinite) (cause := some testCause)).createEffect
          (.layered (.objects #[phCoId]) (.control p0) .untilEndOfTurn) (cause := some testCause)).createEffect
         (.layered (.objects #[phCoId]) (.copy hero) .untilEndOfTurn) (cause := some testCause)).phaseOut
        (gPhCo0.object! phCoId) (cause := some testCause))
      p3 .concede
  let prePhCoLog := gPhCo1.log.size
  let gPhCoAfter := gPhCo1.clearEOT
  let phCoLogs := gPhCoAfter.log.extract prePhCoLog gPhCoAfter.log.size

  -- Copy-before-emblem in `beginTurn`:
  let gCbE0 := insertObject (addPermanent g4 bear p0 p0) embDef p0 .command (some p0)
  let cbeBearId := (gCbE0.permanentsOf p0)[0]!.id
  let cbeEmbId := (gCbE0.objects.filter (fun (o : GameObject) => o.zone == Zone.command))[0]!.id
  let gCbE1 :=
    ((gCbE0.createEffect (.layered (.objects #[cbeBearId]) (.copy hero) (.untilNextTurnOf p1))
        (cause := some testCause)).createEffect
      (.gameRule (.fraEmblem cbeEmbId) (.untilNextTurnOf p1)) (cause := some testCause))
  let preCbELog := gCbE1.log.size
  let gCbEAfter := gCbE1.startNextTurnAndBegin
  let cbeLogs := gCbEAfter.log.extract preCbELog gCbEAfter.log.size

  -- Emblem-scoped `.copy` (`emb1` vs `emb2`), transitive `.fraEmblem`, and multi-object `.copy`:
  let gTwoEmb0 :=
    insertObject (insertObject (addPermanent (addPermanent g4 bear p0 p0) ({ bear with name := "P47i2 BearTwo" }) p0 p0)
      embDef p0 .command (some p0)) embDef p0 .command (some p0)
  let b1Id := (gTwoEmb0.permanentsOf p0)[0]!.id
  let b2Id := (gTwoEmb0.permanentsOf p0)[1]!.id
  let embs := gTwoEmb0.objects.filter (fun (o : GameObject) => o.zone == Zone.command)
  let emb1Id := embs[0]!.id
  let emb2Id := embs[1]!.id
  let gTwoEmb1 :=
    ((gTwoEmb0.createEffect (.layered (.objects #[b1Id]) (.copy hero) (.whileInZone emb1Id .command))
        (cause := some testCause)).createEffect
      (.layered (.objects #[b2Id]) (.copy hero) (.whileInZone emb2Id .command))
      (cause := some testCause))
  let preTwoEmbLog := gTwoEmb1.log.size
  let gOneEmbCeased := gTwoEmb1.ceaseToExist emb1Id (cause := some testCause)
  let oneEmbLogs := gOneEmbCeased.log.extract preTwoEmbLog gOneEmbCeased.log.size

  -- Transitive `srcPerm -> embMid (.whileSourceOnBattlefield srcPerm) -> bTrans (.whileInZone embMid .command)`:
  let anchorDef2 : CardDef := { name := "P47i2 TransAnchor", types := #[.artifact] }
  let gTrans0 := insertObject (addPermanent (addPermanent g4 anchorDef2 p0 p0) bear p0 p0) embDef p0 .command (some p0)
  let transSrcId := ((gTrans0.permanentsOf p0).find? (fun (o : GameObject) => o.name == anchorDef2.name)).get!.id
  let transBearId := ((gTrans0.permanentsOf p0).find? (fun (o : GameObject) => o.name == bear.name)).get!.id
  let transEmbId := (gTrans0.objects.filter (fun (o : GameObject) => o.zone == Zone.command))[0]!.id
  let gTrans1 :=
    ((gTrans0.createEffect (.gameRule (.fraEmblem transEmbId) (.whileSourceOnBattlefield transSrcId))
        (cause := some testCause)).createEffect
      (.layered (.objects #[transBearId]) (.copy hero) (.whileInZone transEmbId .command))
      (cause := some testCause))
  let preTransLog := gTrans1.log.size
  let (gTransSrcGone, _) := gTrans1.move transSrcId .exile none (cause := some testCause)
  let transLogs := gTransSrcGone.log.extract preTransLog gTransSrcGone.log.size

  -- Multi-object `.copy`:
  let gMultiCopy :=
    gTwoEmb0.createEffect (.layered (.objects #[b1Id, b2Id]) (.copy hero) .untilEndOfTurn)
      (cause := some testCause)
  let preMultiCopyLog := gMultiCopy.log.size
  let gMultiCopyEot := gMultiCopy.clearEOT
  let multiCopyLogs := gMultiCopyEot.log.extract preMultiCopyLog gMultiCopyEot.log.size

  let item2cOk :=
    mustHold47i2 "2c_phasedOutCoDepartingLogsRestore"
      ((gPhCoAfter.object! phCoId).status.phasedOut &&
       phCoLogs.any (· == s!"{bear.name} is no longer a copy of {hero.name}")) &&
    mustHold47i2 "2c_copyBeforeEmblemBeginTurn"
      ((cbeLogs.filter (· == s!"{bear.name} is no longer a copy of {hero.name}")).size == 1 &&
       (gCbEAfter.findObject? cbeEmbId).isNone) &&
    mustHold47i2 "2c_emblemScopedTransitiveAndMultiCopy"
      (oneEmbLogs.any (· == s!"{bear.name} is no longer a copy of {hero.name}") &&
       !oneEmbLogs.any (· == "P47i2 BearTwo is no longer a copy of Event Hero") &&
       gOneEmbCeased.name (gOneEmbCeased.object! b2Id) == hero.name &&
       (gTransSrcGone.findObject? transEmbId).isNone &&
       transLogs.any (· == s!"{bear.name} is no longer a copy of {hero.name}") &&
       multiCopyLogs.any (· == s!"{bear.name} is no longer a copy of {hero.name}") &&
       multiCopyLogs.any (· == "P47i2 BearTwo is no longer a copy of Event Hero"))

  mustHold47i2 "2a.strictExilePermsCopyAdvAndPrepGuard" item2aOk &&
  mustHold47i2 "2b.paidResCastsImpendingAndAdvExile" item2bOk &&
  mustHold47i2 "2c.coDepartingEmblemAndMultiCopyLogs" item2cOk &&
  mustHold47i2 "2.replay"
    (replayOk47i2 #[gReqNoElfEot, gReqWithElfEot, gReqElfGoneOnStack, gCopyAdvStack,
      gDepartedStack, gReturnedExile, gNullCastOk, gMayCastCardsPaid, gImpPaid,
      gAdvNullFromAdv, gPhCoAfter, gCbEAfter, gOneEmbCeased, gTransSrcGone, gMultiCopyEot])

end Phase47Item2EventAlignment

section Phase47Item3EventAlignment

private def mustHold47i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase47Item3EventAlignment failed: {label}"

private def replayOk47i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 3a(i). ETB `EventCause.costPayment (.life | .behold)` prospective scoping in `Core.isInitialMaterialize`
  --        vs live-source `payLifeCost`:
  let gWithElf := addPermanent g4 (creature "P47i3 Elf" ManaCost.empty #["Elf"] 1 1) p0 p0
  let elfId := (gWithElf.permanentsOf p0)[0]!.id
  let prospId : ObjectId := ⟨gWithElf.nextObjectId⟩
  let gAbortedEtbCosts :=
    (((gWithElf.change
        (.replacementOrder #[
          { kind := .entersUntappedPayLife 2, object := some prospId },
          { kind := .entersUntappedBehold elfId .elf, object := some prospId } ])).record
        (GameEvent.life gWithElf.turnNumber p0 2 (gained := false)
          (cause := .costPayment .life p0 (some prospId)))).record
      (GameEvent.life gWithElf.turnNumber p0 1 (gained := true)
        (cause := .costPayment .behold p0 (some prospId))))
  let preRealIdx := gAbortedEtbCosts.events.size
  let gAfterAbortedCosts := addPermanent gAbortedEtbCosts bear p0 p0
  let realPerm := (gAfterAbortedCosts.permanentsOf p0)[1]!

  let gLivePay0 := quiet (addPermanent g4 bear p0 p0)
  let livePayPerm := (gLivePay0.permanentsOf p0)[0]!
  let gLivePay1 :=
    match gLivePay0.payLifeCost p0 1 (forObject := some livePayPerm.id) with
    | .ok g => g.change (.materializeObject livePayPerm)
    | .error e => panic! e

  -- 3a(ii). Post-departure `.ringBearer false` & `.removedOnResolution` `eventObjectIsLiveSubject` guards,
  --         non-initial `.materializeObject` overwrite in `abilitySourceLiveAt`, and `.materializeObject`
  --         counter registration in `preLogEffectsAndCounterSources`:
  let gRbDep0 := addPermanent g4 bear p0 p0
  let rbOldObj := (gRbDep0.permanentsOf p0)[0]!
  let rbOldSnap := gRbDep0.snapshot rbOldObj
  let (gRbDep1, _) := gRbDep0.move rbOldObj.id (.graveyard p0) none (cause := some testCause)
  let gRbDep2 :=
    gRbDep1.record (GameEvent.designation gRbDep1.turnNumber rbOldSnap .ringBearer false (cause := testCause))

  let gSpellRem0 := insertObject g4 ({ name := "P47i3 Inst", manaCost := ManaCost.zero, types := #[.instant], spellEffect := some (Effect.gainLife 1) }) p0 (.hand p0)
  let gSpellOnStack := mustApply gSpellRem0 p0 (.cast (gSpellRem0.player p0).hand.back!)
  let stackSpellObj := gSpellOnStack.object! gSpellOnStack.stack.back!.objectId
  let stackSpellSnap := gSpellOnStack.snapshot stackSpellObj
  let gSpellResolved :=
    mustApply (mustApply (mustApply (mustApply gSpellOnStack p0 .pass) p1 .pass) p2 .pass) p3 .pass
  let gSpellAfterRem :=
    gSpellResolved.record
      (GameEvent.rules gSpellResolved.turnNumber (.stackObject (.removedOnResolution stackSpellSnap)) testCause)

  -- Non-initial `.materializeObject` overwrite in `abilitySourceLiveAt`:
  let gNonInitMat0 := addPermanent (addPermanent g4 ({ name := "P47i3 SrcArt", types := #[.artifact] }) p0 p0) bear p0 p0
  let srcArt := (gNonInitMat0.permanentsOf p0).find? (·.name == "P47i3 SrcArt") |>.get!
  let buffBearId := (gNonInitMat0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gNonInitMat1 :=
    ((gNonInitMat0.createEffect
        (.layered (.objects #[buffBearId]) (.ptModify 3 3) (.whileSourceOnBattlefield srcArt.id))
        (cause := some testCause)).record
      (GameEvent.abilityActivated gNonInitMat0.turnNumber ⟨gNonInitMat0.nextObjectId + 50⟩
        (gNonInitMat0.snapshot srcArt) p0 (.nonMana none false false false (some 0) false))).change
      (.materializeObject { srcArt with zone := .exile, controller := none })
  let histAfterNonInitMat := gNonInitMat1.mkHistoricalGameAt gNonInitMat1.events.size

  -- Target `.materializeObject` counter registration in `preLogEffectsAndCounterSources`:
  let gPreCnt0 := addPermanent (addPermanent g4 ({ name := "P47i3 CntSrc", types := #[.artifact] }) p0 p0) bear p0 p0
  let cntSrc0 := (gPreCnt0.permanentsOf p0).find? (·.name == "P47i3 CntSrc") |>.get!
  let cntBearId := (gPreCnt0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gPreCnt1 :=
    (gPreCnt0.recordPutCounters cntSrc0.id .charge 1 (some p0) (cause := some testCause)).createEffect
      (.layered (.objects #[cntBearId]) (.ptModify 2 2) (.whileSourceHasCounter cntSrc0.id .charge))
      (cause := some testCause)
  let cntSrcWithCharge := gPreCnt1.object! cntSrc0.id
  let gPreCntQuiet :=
    (((quiet gPreCnt1).record
        (GameEvent.life gPreCnt1.turnNumber p0 1 (gained := false)
          (cause := .costPayment .tap p0 (some cntSrc0.id)))).change
      (.materializeObject cntSrcWithCharge)).ceaseToExist cntSrc0.id (cause := some testCause)
  let histAtZeroPreCnt := gPreCntQuiet.mkHistoricalGameAt 0

  let item3aOk :=
    mustHold47i3 "3a_etbProspectiveCostScoping"
      (realPerm.id == prospId &&
       gAfterAbortedCosts.objectZoneAndPhasedOutAt? prospId preRealIdx == none &&
       gAfterAbortedCosts.objectZoneAndPhasedOutAt? prospId gAfterAbortedCosts.events.size == some (.battlefield, false) &&
       gLivePay1.objectZoneAndPhasedOutAt? livePayPerm.id 0 == some (.battlefield, false)) &&
    mustHold47i3 "3a_liveSubjectAndMaterialize"
      (gRbDep2.objectZoneAndPhasedOutAt? rbOldObj.id gRbDep2.events.size == none &&
       gSpellAfterRem.objectZoneAndPhasedOutAt? stackSpellObj.id gSpellAfterRem.events.size == none &&
       histAfterNonInitMat.power (histAfterNonInitMat.object! buffBearId) == 2 &&
       histAtZeroPreCnt.power (histAtZeroPreCnt.object! cntBearId) == 4)

  -- 3b. Phased-out arrival (`poIdx + 1`) & controllerless newly phased-in CR 800.4c exile,
  --     paused `phaseInControlledLoop` `startEventIdx`, and forward `phaseOutBatchStartIdx`:
  let gP2Gone := mustApply g4 p2 .concede
  let anchor3 := ({ name := "P47i3 Anchor", types := #[.artifact] } : CardDef)
  -- Phased-out arrival (`status := { phasedOut := true }` on initial allocation, controlled by `p0` via `anchor3`,
  -- then `anchor3` leaves while phased out, then it phases in -> `poIdx + 1` sees `p0`'s prior control and exiles it!):
  let gPoArr0 := addPermanent gP2Gone anchor3 p0 p0
  let poArrAnchorId := (gPoArr0.permanentsOf p0)[0]!.id
  let (gPoArr1, poArrObj) := gPoArr0.allocObject bear p2 .battlefield none { phasedOut := true }
  let gPoArr2 :=
    gPoArr1.createEffect
      (.layered (.objects #[poArrObj.id]) (.control p0) (.whileSourceOnBattlefield poArrAnchorId))
      (cause := some testCause)
  let (gPoArrAnchorGone, _) := gPoArr2.move poArrAnchorId .exile none (cause := some testCause)
  let gPoArrPhasedIn := gPoArrAnchorGone.phaseIn (gPoArrAnchorGone.object! poArrObj.id)
  let gPoArrReconciled :=
    Game.reconcileControlAfterTransition gPoArrAnchorGone gPoArrPhasedIn (cause := some testCause)

  -- Controllerless newly phased-in permanent (`defaultController == none`, `owner == p2` departed, no control effect ever):
  let (gNoCtrlPh0, noCtrlPhObj) := gP2Gone.allocObject bear p2 .battlefield none { phasedOut := true }
  let gNoCtrlPhIn := gNoCtrlPh0.phaseIn (gNoCtrlPh0.object! noCtrlPhObj.id)
  let gNoCtrlReconciled :=
    Game.reconcileControlAfterTransition gNoCtrlPh0 gNoCtrlPhIn (cause := some testCause)

  -- Paused `phaseInControlledLoop` (`startEventIdx` carried across `.phaseInControlledLoop #[] (some testCause) (some loopStartIdx)`):
  let gLoopResume0 := gNoCtrlPhIn
  let loopStartIdx := gNoCtrlPh0.events.size
  let gLoopResumed :=
    gLoopResume0.resumePendingReplacement (.phaseInControlledLoop #[] (some testCause) (some loopStartIdx))

  -- Forward `phaseOutBatchStartIdx` across an unbatched `.rules` event inside a paused batch:
  let gBatchGap0 := addPermanent (addPermanent g4 bear p0 p0) hero p0 p0
  let bg1 := (gBatchGap0.permanentsOf p0)[0]!
  let bg2 := (gBatchGap0.permanentsOf p0)[1]!
  let gapBid : BatchId := ⟨gBatchGap0.nextBatchId⟩
  let gBatchStep1 :=
    (gBatchGap0.change
      (.pauseBatch gapBid (some testCause) gBatchGap0.objects gBatchGap0.players
        gBatchGap0.activeEffects gBatchGap0.pending gBatchGap0.stack)).phaseOut bg1 (cause := some testCause)
  let gBatchStep2 :=
    (gBatchStep1.change .clearPausedBatch).record
      (GameEvent.life gBatchStep1.turnNumber p0 1 (gained := true) (cause := testCause))
  let gBatchGap1 :=
    ((gBatchStep2.change
      (.pauseBatch gapBid (some testCause) gBatchStep2.objects gBatchStep2.players
        gBatchStep2.activeEffects gBatchStep2.pending gBatchStep2.stack)).phaseOut
      (gBatchStep2.object! bg2.id) (cause := some testCause)).change .clearPausedBatch
  let bg1Idx? := gBatchGap1.events.findIdx? fun ev =>
    match ev.change with | .rules (.permanent (.phasedOut eo)) => eo.id == some bg1.id | _ => false
  let bg2Idx? := gBatchGap1.events.findIdx? fun ev =>
    match ev.change with | .rules (.permanent (.phasedOut eo)) => eo.id == some bg2.id | _ => false

  let item3bOk :=
    mustHold47i3 "3b_phasedOutArrivalControllerlessAndLoop"
      ((gPoArrReconciled.followMovedToZone? poArrObj.id (· == .exile)).isSome &&
       (gNoCtrlReconciled.followMovedToZone? noCtrlPhObj.id (· == .exile)).isSome &&
       (gLoopResumed.followMovedToZone? noCtrlPhObj.id (· == .exile)).isSome) &&
    mustHold47i3 "3b_phaseOutBatchStartIdxForward"
      (match bg1Idx?, bg2Idx? with
       | some i1, some i2 => i1 + 1 < i2 && gBatchGap1.phaseOutBatchStartIdx i2 == i1
       | _, _ => false)

  -- 3c. `inferPreLogTurnIsExtra` & `departedNextTurnWouldHaveBegunSince` (`clearEOT` `.powerUpsForbiddenThisTurn`
  --     expiry, `!addedMidLog` `.addPlayer`, and `dropLost` extra-turn stack reconstruction):
  let gRegT2 := g4.startNextTurnAndBegin
  let gRegT5 := ((gRegT2.startNextTurnAndBegin).startNextTurnAndBegin).startNextTurnAndBegin
  let gExtraT3 :=
    (gRegT2.record (GameEvent.extraTurnAdded gRegT2.turnNumber p3 (cause := testCause))).startNextTurnAndBegin
  -- Expire `.powerUpsForbiddenThisTurn` in `clearEOT` both mid-log (after `quiet`) and pre-log (before `quiet`)
  -- -> `inferPreLogTurnIsExtra` STILL returns `true` in both cases!
  let gExtraClearedAfterQuiet := (quiet gExtraT3).clearEOT
  let gExtraClearedPreLog := quiet (gExtraT3.clearEOT)
  -- Mid-log `.addPlayer` does NOT pollute pre-log `alive` (including wrapped `t == 5` around 4 seats):
  let p4 : PlayerId := ⟨4⟩
  let gMidLogAddPlayer := (quiet gRegT2).change (.addPlayer { id := p4, name := "Ajani" })
  let gMidLogAddPlayerT5 := (quiet gRegT5).change (.addPlayer { id := p4, name := "Ajani" })
  -- `dropLost` extra-turn stack reconstruction: `p2` gets an extra turn on `p1`'s regular turn, then `p2` concedes
  -- before the turn ends; when `startNextTurnAndBegin` advances to `p3`'s regular turn (`extra := false`),
  -- a permanent phased out under `p2` on `p1`'s turn DOES phase in on `p3`'s turn (`p1 -> [p2 departed] -> p3`)!
  let gDropExtra0 := addPermanent gRegT2 bear p0 p0
  let dropPhId := (gDropExtra0.permanentsOf p0)[0]!.id
  let gDropExtra1 :=
    (gDropExtra0.createEffect (.layered (.objects #[dropPhId]) (.control p2) .indefinite)
      (cause := some testCause)).phaseOut (gDropExtra0.object! dropPhId) (cause := some testCause)
  let gDropExtraQuiet :=
    mustApply
      ((quiet gDropExtra1).record (GameEvent.extraTurnAdded gDropExtra1.turnNumber p2 (cause := testCause)))
      p2 .concede
  let gDropExtraP3Turn := gDropExtraQuiet.startNextTurnAndBegin

  let item3cOk :=
    mustHold47i3 "3c_1_afterQuietClearEot"
      (gExtraClearedAfterQuiet.inferPreLogTurnIsExtra p3 gExtraClearedAfterQuiet.turnNumber) &&
    mustHold47i3 "3c_2_preLogClearEot"
      (gExtraClearedPreLog.inferPreLogTurnIsExtra p3 gExtraClearedPreLog.turnNumber) &&
    mustHold47i3 "3c_3_midLogAddPlayer"
      (!gMidLogAddPlayer.inferPreLogTurnIsExtra p1 gMidLogAddPlayer.turnNumber &&
       !gMidLogAddPlayerT5.inferPreLogTurnIsExtra p0 gMidLogAddPlayerT5.turnNumber) &&
    mustHold47i3 "3c_4_dropExtraActiveP3"
      (gDropExtraP3Turn.activePlayer == p3) &&
    mustHold47i3 "3c_5_dropExtraPhasedIn"
      (!(gDropExtraP3Turn.object! dropPhId).status.phasedOut &&
       (gDropExtraP3Turn.object! dropPhId).isOnBattlefield)

  mustHold47i3 "3a.etbProspectiveAndMaterializeLiveness" item3aOk &&
  mustHold47i3 "3b.phasedOutArrivalAndBatchStartIdx" item3bOk &&
  mustHold47i3 "3c.preLogExtraTurnAndDropLost" item3cOk &&
  mustHold47i3 "3.replay"
    (replayOk47i3 #[gAfterAbortedCosts, gRbDep2, gSpellAfterRem, gNonInitMat1,
      gPoArrReconciled, gNoCtrlReconciled, gLoopResumed, gBatchGap1, gExtraT3, gDropExtra1])

end Phase47Item3EventAlignment

section Phase47Item4EventAlignment

private def mustHold47i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase47Item4EventAlignment failed: {label}"

private def replayOk47i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustStepAgent47 (g : Game) (p : PlayerId) : Game :=
  match Agent.choose g p with
  | some act => mustApply g p act
  | none => panic! "Phase47Item4EventAlignment: Agent.choose returned none"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := emptyHand (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })) p0

  -- 4a(i). `Game.manaTypesFromTap` mixed-type `.fixed` tap simulation (`{T}: Add {U}{R}`):
  let urLandDef : CardDef := {
    name := "P47i4 SteamBoiler"
    types := #[.land]
    tapAddTogether := #[.colored .blue, .colored .red]
  }
  let urBoltDef : CardDef := {
    bear with
    name := "P47i4 SteamDrake"
    manaCost := { symbols := #[.colored .blue, .colored .red] }
  }
  let gUr0 := insertObject (addPermanent g3 urLandDef p0 p0) urBoltDef p0 (.hand p0)
  let urLandObj := (gUr0.permanentsOf p0)[0]!
  let urCost := urBoltDef.manaCost
  let gUrStep1 := mustStepAgent47 gUr0 p0 -- casts `urBoltDef`
  let gUrStep2 := mustStepAgent47 gUrStep1 p0 -- taps `urLandObj` once (adding `{U}{R}`)
  let gUrStep3 := mustStepAgent47 gUrStep2 p0 -- pays `{U}{R}`!

  -- 4a(ii). `canPayFromSources` & `preferredManaTap` pruning on 12 any-color sources:
  let anyRockDef : CardDef := { name := "P47i4 RainbowOrb", types := #[.artifact], tapAddAnyColor := true }
  let gManyAny0 :=
    Id.run do
      let mut g := g3
      for _ in [0:12] do
        g := addPermanent g anyRockDef p0 p0
      return g
  let manySources := (gManyAny0.manaSources p0).toList
  let uSpell4Def : CardDef := {
    name := "P47i4 Wave4"
    manaCost := ManaCost.ofGenericAndColor 3 .blue
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 1)
  }
  let gManyAnyCast :=
    let g := insertObject gManyAny0 uSpell4Def p0 (.hand p0)
    mustApply g p0 (.cast (g.player p0).hand.back!)
  let manyPref? := gManyAnyCast.preferredManaTap p0 gManyAnyCast.proposedSpell.get!

  -- 4a(iii). `Agent` `disjointFromAllPicks := false` on `.chooseX` + `.crew` + `sacrificeAnotherCreature`
  --          AND tap-pick color preservation (`{G}, Tap an untapped creature` with `hasteElf + bear` vs `hasteElf` alone):
  let xCrewSacVehDef : CardDef := {
    name := "P47i4 XSacSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    activatedAbilities := #[{
      cost := { mana := { symbols := #[.x] }, fra := .crew 2, sacrificeAnotherCreature := true }
      effect := Effect.gainLife 2
    }]
  }
  let gXCrewSac0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent g3 xCrewSacVehDef p0 p0) bear p0 p0) forest p0 p0)
      forest p0 p0
  let xcsVehId := (gXCrewSac0.permanentsOf p0).find? (·.name == xCrewSacVehDef.name) |>.get!.id
  let xcsActOk :=
    match Agent.choose gXCrewSac0 p0 with | some (.activate id 0) => id == xcsVehId | _ => false
  let gXCrewSacProp := mustApply gXCrewSac0 p0 (.activate xcsVehId 0)
  let xcsXOk :=
    match Agent.choose gXCrewSacProp p0 with | some (.chooseX 2) => true | _ => false
  let gXCrewSacDone :=
    mustStepAgent47 (mustStepAgent47 (mustStepAgent47 (mustStepAgent47 (mustStepAgent47 (mustStepAgent47 gXCrewSacProp p0) p0) p0) p0) p0) p0

  let tapCreatureGDef : CardDef := {
    name := "P47i4 RiteAltar"
    types := #[.enchantment]
    activatedAbilities := #[{
      cost := { mana := { symbols := #[.colored .green] }, tapAnUntappedCreatureYouControl := true }
      effect := Effect.gainLife 2
    }]
  }
  let hasteElfDef : CardDef := { llanowarElves with name := "P47i4 HasteElf", keywords := { haste := true } }
  let gTapGOnlyElf := addPermanent (addPermanent g3 tapCreatureGDef p0 p0) hasteElfDef p0 p0
  let gTapGWithBear := addPermanent gTapGOnlyElf bear p0 p0
  let altarId := (gTapGWithBear.permanentsOf p0).find? (·.name == tapCreatureGDef.name) |>.get!.id
  let tapGWithBearActOk :=
    match Agent.choose gTapGWithBear p0 with | some (.activate id 0) => id == altarId | _ => false
  let gTapGDone :=
    mustStepAgent47 (mustStepAgent47 (mustStepAgent47 (mustStepAgent47 gTapGWithBear p0) p0) p0) p0

  let item4aOk :=
    mustHold47i4 "4a_mixedFixedTap"
      (gUr0.manaTypesFromTap urLandObj (.colored .blue) == #[.colored .blue, .colored .red] &&
       (gUr0.availableManaExcept p0 none).canPay urCost &&
       gUr0.canPayFromSources ManaPool.empty urCost false false (gUr0.manaSources p0).toList &&
       gUrStep3.stack.size == 1) &&
    mustHold47i4 "4a_anyColorPruning"
      (manySources.length == 12 &&
       gManyAny0.canPayFromSources ManaPool.empty (ManaCost.ofGeneric 10) false false manySources &&
       !gManyAny0.canPayFromSources ManaPool.empty (ManaCost.ofGeneric 13) false false manySources &&
       manyPref?.any (fun (_, t) => t == .colored .blue)) &&
    mustHold47i4 "4a_agentSharedCrewSacAndTapColor"
      (xcsActOk &&
       xcsXOk &&
       gXCrewSacDone.stack.size == 1 &&
       (match Agent.choose gTapGOnlyElf p0 with | some (.activate _ _) => false | _ => true) &&
       tapGWithBearActOk &&
       gTapGDone.stack.size == 1)

  -- 4b(i). `ManaAbilities` mana-cost `spend := { abilitySourceSubtypes := g.subtypes o }`:
  let gobFilterDef : CardDef := {
    creature "P47i4 GobAlchemist" ManaCost.empty #["Goblin"] 1 1 with
    keywords := { haste := true }
    filterMana := some (ManaCost.ofGeneric 1, #[.colored .blue])
  }
  let rockFilterDef : CardDef := {
    name := "P47i4 PlainFilter"
    types := #[.artifact]
    filterMana := some (ManaCost.ofGeneric 1, #[.colored .blue])
  }
  let gGobFilt0 :=
    (addPermanent (addPermanent g3 gobFilterDef p0 p0) rockFilterDef p0 p0).addMana
      p0 (.colored .red) 1 (restriction := some (.forSubtypeSpellOrSource .goblin))
  let gobFiltObj := (gGobFilt0.permanentsOf p0).find? (·.name == gobFilterDef.name) |>.get!
  let rockFiltObj := (gGobFilt0.permanentsOf p0).find? (·.name == rockFilterDef.name) |>.get!
  let gGobFiltPaid : Game :=
    match gGobFilt0.activateManaAbility p0 gobFiltObj.id 0 #[.colored .blue, .colored .blue] with
    | .ok g => g
    | .error e => panic! e

  -- 4b(ii). `ManaPool` `.notSpellsFromHand` after narrow positive restrictions & `.colorless` before colored `.fra`:
  let poolNarrowVsHand : ManaPool :=
    ((ManaPool.empty.addUnit { mana := .colored .red, restriction := some (.fra (.subtypeSpell .goblin)) }).addUnit
      { mana := .colored .blue, restriction := some (.fra .notSpellsFromHand) })
  let poolAfterExileGob :=
    match poolNarrowVsHand.pay? (ManaCost.ofGeneric 1)
        (spend := { spell := true, fromHand := false, subtypes := #[.goblin] }) with
    | some p' => p'
    | none => panic! "expected poolNarrowVsHand payment"
  let poolColorlessFirst : ManaPool :=
    ((ManaPool.empty.addUnit { mana := .colored .red, restriction := some (.fra .notSpellsFromHand) }).addUnit
      { mana := .colorless, restriction := some (.fra .notSpellsFromHand) })
  let poolAfterGeneric :=
    match poolColorlessFirst.pay? (ManaCost.ofGeneric 1)
        (spend := { spell := true, fromHand := false }) with
    | some p' => p'
    | none => panic! "expected poolColorlessFirst payment"

  -- 4b(iii). `ManaUnit.fromTreasure` on restricted Treasure mana, live non-Treasure check in `addManaUnits`,
  --          and latest-entry `GameEvent.isTreasureSourceInLog`:
  let trRestrDef : CardDef := {
    name := "P47i4 RelicTreasure"
    types := #[.artifact]
    subtypes := #["Treasure"]
    activatedAbilities := #[{
      cost := { tap := true, sacrificeSource := true }
      effect := { resolution := .addAnyColorSpendOnlyArtifactSpell, phrase := "Add one mana of any color for artifact spell." }
    }]
  }
  let gTrRestr0 := addPermanent g3 trRestrDef p0 p0
  let trRestrId := (gTrRestr0.permanentsOf p0)[0]!.id
  let gTrRestrTapped : Game :=
    match gTrRestr0.activateManaAbility p0 trRestrId 0 #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  -- Token created as a Treasure, then Layer 4 changes type to Enchantment (stripping `.treasure` subtype) while still on battlefield:
  let (gTrStripped0, strippedTok) := g3.createOneToken p0 treasureToken (cause := some testCause)
  let trSnapBeforeStrip := gTrStripped0.snapshot strippedTok
  let gTrStripped1 :=
    gTrStripped0.createEffect
      (.layered (.objects #[strippedTok.id]) (.types .set #[.enchantment] #[] #[]) .untilEndOfTurn)
      (cause := some testCause)
  let gTrStrippedMana := gTrStripped1.addMana p0 (.colored .green) 1 (source := some strippedTok.id)
  let trSnapAfterStrip := gTrStripped1.snapshot (gTrStripped1.object! strippedTok.id)
  let gTrTwoActs :=
    (gTrStripped1.record
      (GameEvent.abilityActivated gTrStripped1.turnNumber ⟨gTrStripped1.nextObjectId + 10⟩ trSnapBeforeStrip p0 .mana)).record
      (GameEvent.abilityActivated gTrStripped1.turnNumber ⟨gTrStripped1.nextObjectId + 11⟩ trSnapAfterStrip p0 .mana)

  let item4bOk :=
    mustHold47i4 "4b_manaAbSourceSubtypeSpend"
      (gGobFilt0.manaAbilityIndexFor gobFiltObj (.colored .blue) (plainOnly := false) == some 0 &&
       gGobFilt0.manaAbilityIndexFor rockFiltObj (.colored .blue) (plainOnly := false) == none &&
       (gGobFilt0.activateManaAbility p0 rockFiltObj.id 0 #[.colored .blue, .colored .blue]).toOption.isNone &&
       (gGobFiltPaid.player p0).manaPool.blue == 2 &&
       (gGobFiltPaid.player p0).manaPool.fraRestricted.isEmpty) &&
    mustHold47i4 "4b_poolNotSpellsFromHandAndColorlessOrder"
      (poolAfterExileGob.fraRestricted == #[(.colored .blue, .notSpellsFromHand)] &&
       poolAfterGeneric.fraRestricted == #[(.colored .red, .notSpellsFromHand)]) &&
    mustHold47i4 "4b_restrictedTreasureAndLiveNonTreasure"
      ((gTrRestrTapped.player p0).manaPool.units.all (·.fromTreasure) &&
       !(gTrRestrTapped.player p0).manaPool.units.isEmpty &&
       (gTrStrippedMana.player p0).manaPool.units.all (!·.fromTreasure) &&
       !GameEvent.isTreasureSourceInLog gTrTwoActs.events strippedTok.id)

  -- 4c(i). `applyAddMana` `.chosenX` & `lastKnownToughness` forwarding:
  let xManaShrineDef : CardDef := {
    name := "P47i4 XGenerator"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { mana := { symbols := #[.x] } }
      effect := {
        targeting := .of .player
        resolution := .addMana #[.colored .red] .chosenX
        phrase := "Target player; add X {R}."
      }
    }]
  }
  let gXMana0 := (addPermanent g3 xManaShrineDef p0 p0).addMana p0 .colorless 3
  let xGenId := (gXMana0.permanentsOf p0)[0]!.id
  let gXManaAct :=
    mustApply (mustApply (mustApply (mustApply gXMana0 p0 (.activate xGenId 0)) p0 (.chooseX 3)) p0 (.target (.player p0))) p0 .pay
  let gXManaRes := mustApply (mustApply (mustApply gXManaAct p0 .pass) p1 .pass) p2 .pass

  let toughDiesDef : CardDef := {
    creature "P47i4 WallSap" ManaCost.empty #["Plant"] 1 4 with
    triggeredAbilities := #[
      .triggered .dies { resolution := .addMana #[.colored .green] .equalSourceToughness, phrase := "Add {G} equal to toughness." }
    ]
  }
  let gTough0 := addPermanent g3 toughDiesDef p0 p0
  let wallId := (gTough0.permanentsOf p0)[0]!.id
  let gToughDestroyed := (gTough0.destroyPermanent (gTough0.object! wallId) (cause := some testCause)).receivePriority p0
  let gToughRes := mustApply (mustApply (mustApply gToughDestroyed p0 .pass) p1 .pass) p2 .pass

  -- 4c(ii). Layer 3 `TextChange` `Resolution.addMana` `NumberSelector` / `tapAddRestricted` (`FraManaUse.subtypeEquipmentSagaSpell`)
  --         & `CardDef.tapAddColorlessPerSubtype` parity:
  let countElfRitualDef : CardDef := {
    name := "P47i4 ElfRite"
    manaCost := ManaCost.zero
    types := #[.sorcery]
    spellEffect := some { resolution := .addMana #[.colored .green] (.perSubtype .elf), phrase := "Add {G} for each Elf you control." }
  }
  let dwarfForgeDef : CardDef := {
    name := "P47i4 DwarfForge"
    types := #[.land]
    tapAddRestricted := some (#[.colored .red], "Dwarf, Equipment, and Saga spells")
  }
  let elfTowerDef : CardDef := {
    name := "P47i4 ElfTower"
    types := #[.land]
    tapAddColorlessPerSubtype := some .elf
  }
  let gL3Base0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g3 bear p0 p0) bear p0 p0)
          dwarfForgeDef p0 p0)
        elfTowerDef p0 p0)
      countElfRitualDef p0 (.hand p0)
  let forgeId := (gL3Base0.permanentsOf p0).find? (·.name == dwarfForgeDef.name) |>.get!.id
  let towerId := (gL3Base0.permanentsOf p0).find? (·.name == elfTowerDef.name) |>.get!.id
  let riteHandId := (gL3Base0.player p0).hand.back!
  let gL3Text :=
    ((gL3Base0.createEffect
        (.layered (.objects #[forgeId]) (.text (.replaceCreatureType .dwarf .bear)) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.layered (.objects #[towerId]) (.text (.replaceCreatureType .elf .bear)) .untilEndOfTurn)
      (cause := some testCause))
  let gForgeTapped : Game :=
    match gL3Text.activateManaAbility p0 forgeId 0 #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gTowerTapped : Game :=
    match gL3Text.activateManaAbility p0 towerId 0 #[.colorless, .colorless] with
    | .ok g => g
    | .error e => panic! e
  let gRiteCast := mustApply gL3Text p0 (.cast riteHandId)
  let riteStackId := gRiteCast.stack.back!.objectId
  let gRiteText :=
    gRiteCast.createEffect
      (.layered (.objects #[riteStackId]) (.text (.replaceCreatureType .elf .bear)) .indefinite)
      (cause := some testCause)
  let gRiteRes := mustApply (mustApply (mustApply gRiteText p0 .pass) p1 .pass) p2 .pass

  let item4cOk :=
    mustHold47i4 "4c_chosenXAndLkiToughness"
      ((gXManaRes.player p0).manaPool.red == 3 &&
       (gToughRes.player p0).manaPool.green == 4) &&
    mustHold47i4 "4c_layer3AddManaRestrictedAndColorlessPerSub"
      ((gForgeTapped.player p0).manaPool.fraRestricted == #[(.colored .red, .subtypeEquipmentSagaSpell .bear)] &&
       ((gForgeTapped.player p0).manaPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, subtypes := #[.bear] })) &&
       !((gForgeTapped.player p0).manaPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, subtypes := #[.dwarf] })) &&
       (gTowerTapped.player p0).manaPool.colorless == 2 &&
       (gRiteRes.player p0).manaPool.green == 2 &&
       elfTowerDef.manaAbilities == #[.colorless])

  mustHold47i4 "4a.mixedTapPruningAndAgentCosts" item4aOk &&
  mustHold47i4 "4b.manaAbSpendPoolOrderAndTreasure" item4bOk &&
  mustHold47i4 "4c.addManaChosenXToughnessAndLayer3" item4cOk &&
  mustHold47i4 "4.replay"
    (replayOk47i4 #[gUrStep3, gXCrewSacDone, gTapGDone, gGobFiltPaid, gTrRestrTapped, gTrStrippedMana,
      gTrTwoActs, gXManaRes, gToughRes, gForgeTapped, gTowerTapped, gRiteRes])

end Phase47Item4EventAlignment

end Mtg.Engine.EventTests
