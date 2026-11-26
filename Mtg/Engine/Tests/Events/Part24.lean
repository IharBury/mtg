import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

/-! ### Phase 58 Item 1: `advanceLiveQueueStep` `nextQ`/`alreadyOrderedCycle`, multi-frame empty
top frames, `currentInterpWait?` & non-`sbaPaused` runtime-vs-post-prompt top-level queue probing,
`drainProbeNonPriorityCont` / `.afterTriggerTargetsChosen` / `wrapOuter` -> `chainProposalOuterCont`
/ `stepCanReverseProposal` probe parity & `outerDepth` safety, `chainProposalOuterCont` &
`reverseProposedSpellCore?` implicit-priority preservation, `.crew`/`.costPicks`/`.zemoBoastExile`/
`.turnFaceUp` `openCont`, and `.restorePending`/`stackTriggers`/`afterTriggerTargetsChosen`/
`keepLegend`/`finishScry` continuation ordering -/
section Phase58Item1EventAlignment

private def mustHold58i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase58Item1EventAlignment failed: {label}"

private def replayOk58i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let leyADef : CardDef := { name := "P58i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P58i1 LeyB", types := #[.enchantment] }
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

  -- 1a(i). `advanceLiveQueueStep` recomputes `nextQ` after clearing `.chooseReplacement` (so
  --        a subsequent `.beginStepCont .untap` is NOT poisoned into falsely granting priority,
  --        and `.receivePriority p2` behind a replacement-opening step still reports `some (some p2)`),
  --        and clears `pendingReplacement` cleanly on `alreadyOrderedCycle` without spinning.
  let dmgStep : PendingReplacement := .dealDamageToPlayer p0 1 none false (some testCause) false
  let gNextQUntap :=
    gRep.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.beginStepCont .untap]
        pendingReplacement := some dmgStep
      }
    ]
  let gNextQPrio :=
    gRep.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some dmgStep
      }
    ]
  let gAlreadyOrdered :=
    (gRep.change (.replacementOrder #[dRidA, dRidB])).changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.seq dmgStep (.logMessage "after"))
      }
    ]
  let advLiveQueueOk :=
    !gNextQUntap.anyContinuationGrantsPriority &&
    !gNextQUntap.anyContinuationSettlesControlFlow &&
    gNextQPrio.firstContinuationPriorityGrant? == some (some p2) &&
    gAlreadyOrdered.firstContinuationPriorityGrant? == some (some p2)

  -- 1a(ii). Multi-frame empty top frames (`#[frame0, {}]`): all 4 top-level queue probes AND
  --         `drainPendingContinuations` pop empty top frames so Frame 0 continuations are never stranded.
  let gMultiFrame :=
    g3.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
      },
      .pushContinuationFrame {}
    ]
  let gMultiFrameDrained := gMultiFrame.drainPendingContinuations
  let multiFrameOk :=
    gMultiFrame.firstContinuationPriorityGrant? == some (some p2) &&
    gMultiFrame.anyContinuationGrantsPriority &&
    gMultiFrame.anyContinuationSettlesControlFlow &&
    !gMultiFrame.hasImplicitPendingPriorityContinuation &&
    gMultiFrameDrained.priority == p2

  -- 1a(iii). `currentInterpWait?` simulated ahead of `outerPendingReplacements` in top-level queue probes:
  --          an interpreter wait that opens a blocking prompt (scry 1) settles control flow ahead of
  --          a lower `outerPendingReplacements` `.receivePriority p2`.
  let gWithLib := insertObject (insertObject g3 bear p0 (.library p0)) bear p0 (.library p0)
  let scryWait : InterpState :=
    { ctx := { controller := p0 }
      queue := #[.player (.scry .you (.const 1))]
      stack := #[] }
  let gInterpAheadExplicit :=
    gWithLib.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        interpWait? := some scryWait
      }
    ]
  let gInterpAheadImplicit :=
    gWithLib.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.finishResolutionChoice]
        interpWait? := some scryWait
      }
    ]
  let interpWaitProbeOk :=
    gInterpAheadExplicit.firstContinuationPriorityGrant? == none &&
    !gInterpAheadExplicit.anyContinuationGrantsPriority &&
    gInterpAheadExplicit.anyContinuationSettlesControlFlow &&
    !gInterpAheadExplicit.hasImplicitPendingPriorityContinuation &&
    gInterpAheadImplicit.firstContinuationPriorityGrant? == none &&
    gInterpAheadImplicit.anyContinuationSettlesControlFlow &&
    gInterpAheadImplicit.hasImplicitPendingPriorityContinuation

  -- 1a(iv). Runtime-drain vs post-prompt top-level queue probing:
  --         while a non-`sbaPaused` prompt is open (`.scry p0 1`) with `.receivePriority p2`
  --         queued behind it, runtime probes stop immediately (matching `drainPendingContinuations`),
  --         while `finishAndGrantPriority p1` uses post-prompt probing and sees explicit `p2` so it
  --         does NOT clobber `pendingPriority` to `some p1`!
  let gOpenNonSba :=
    (gWithLib.change (.pending (.scry p0 1))).changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
      }
    ]
  let gOpenNonSbaFin := gOpenNonSba.finishAndGrantPriority p1
  let gOpenNonSbaImplicit :=
    (gWithLib.change (.pending (.scry p0 1))).changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.finishResolutionChoice]
      }
    ]
  let gOpenNonSbaImplicitFin := gOpenNonSbaImplicit.finishAndGrantPriority p1
  let runtimeVsPostPromptOk :=
    gOpenNonSba.firstContinuationPriorityGrant? == none &&
    !gOpenNonSba.anyContinuationGrantsPriority &&
    !gOpenNonSba.anyContinuationSettlesControlFlow &&
    !gOpenNonSba.hasImplicitPendingPriorityContinuation &&
    gOpenNonSbaFin.pendingPriority == none &&
    gOpenNonSbaImplicitFin.pendingPriority == some p1

  -- 1a(v). Unified drainable leaves (`.continueInterpreter`, `.shuffleThen`) settle
  --        `continuationSettlesControlFlow` and preserve implicit `pendingPriority`, and
  --        `.afterTriggerTargetsChosen` uses implicit `pendingPriority` even when opening a target prompt.
  let gContInterp := gWithLib.chainPendingReplacement (.continueInterpreter scryWait)
  let gShuffleTwo := gWithLib.chainPendingReplacement (.shuffleThen p0 .none)
  let gTrigWait :=
    let g1 := addPermanent g3 bear p1 p1
    let trigSrc := (g1.permanentsOf p1)[0]!
    let trigAb : TriggeredAbility :=
      TriggeredAbility.mkTrigger .thisEnters
        { targets := TargetSpec.creature, body := .life (.gain .you (.const 1)) }
    let g2 := g1.change (.enqueueWaitingTriggers #[{
      controller := p0, source := trigSrc, ability := trigAb, pattern := .thisEnters
    }])
    g2.chainPendingReplacement (.finishPostStep .afterTriggerTargetsChosen)
  let unifiedDrainAndTrigOk :=
    gContInterp.anyContinuationSettlesControlFlow &&
    gContInterp.hasImplicitPendingPriorityContinuation &&
    gShuffleTwo.anyContinuationSettlesControlFlow &&
    gShuffleTwo.hasImplicitPendingPriorityContinuation &&
    gTrigWait.anyContinuationSettlesControlFlow &&
    gTrigWait.hasImplicitPendingPriorityContinuation

  -- 1a(vi). `chainProposalOuterCont` & `reverseProposedSpellCore?` preserve non-active caster `p1`
  --         in `pendingPriority` when `outer` / `g.pendingReplacement` relies on implicit
  --         `pendingPriority` (such as `.finishResolutionChoice` or `.seq (.logMessage ..) .finishResolutionChoice`).
  let gChImp0 := g3.chainProposalOuterCont p1 .finishResolutionChoice
    (grantPriority := true) (hadOuterReplacement := false) (openCont := false)
  let gChImp1 := g3.chainProposalOuterCont p1 (.seq (.logMessage "after") .finishResolutionChoice)
    (grantPriority := true) (hadOuterReplacement := false) (openCont := false)
  let gChExp := g3.chainProposalOuterCont p1 (.receivePriority p2)
    (grantPriority := true) (hadOuterReplacement := false) (openCont := false)
  let gP1Prio := g3.change (.priority p1)
  let instCostDef : CardDef := {
    name := "P58i1 Inst"
    manaCost := { symbols := #[.colored .red] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gRev0 := insertObject gP1Prio instCostDef p1 (.hand p1)
  let instId := (gRev0.player p1).hand.back!
  let gRevProp := mustApply gRev0 p1 (.cast instId)
  let gRevPaused :=
    let g0' :=
      ((gRev0.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).chainPendingReplacement
        .finishResolutionChoice).change .saveProposalCheckpoint
    g0'.change (.proposedSpell gRevProp.proposedSpell)
  let revImplOk :=
    match gRevPaused.reverseProposedSpellCore? (resumeContinuation := true)
        (followedByExplicitPriority? := some p1) with
    | .ok (gR, _) => gR.pendingPriority == some p1
    | .error _ => false
  let implicitProposalOk :=
    gChImp0.pendingPriority == some p1 &&
    gChImp1.pendingPriority == some p1 &&
    gChExp.pendingPriority == none &&
    revImplOk

  -- 1a(vii). `stepCanReverseProposal` recognizes `.finishResolutionChoice` / `.receivePriority`
  --          inside `.seq first rest` so reversing a dead proposal drops `rest`, AND
  --          `.leavePlayersWhoLost` + `.restorePending` probe does not panic on `outerDepth`.
  let gDeadProp :=
    let g1 := (gRevProp.change (.pending .none)).record (GameEvent.playerLeftGame gRevProp.turnNumber p1)
    g1.resumePendingReplacement (.seq .finishResolutionChoice (.logMessage "SHOULD_NOT_RUN"))
  let gDeadProp2 :=
    let g1 := (gRevProp.change (.pending .none)).record (GameEvent.playerLeftGame gRevProp.turnNumber p1)
    g1.resumePendingReplacement (.seq (.receivePriority p0) (.logMessage "SHOULD_NOT_RUN"))
  let gOuterDepthProbe :=
    g3.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.seq (.leavePlayersWhoLost none false #[p1]) (.restorePending .none false none #[] none))
      }
    ]
  let stepCanReverseOk :=
    gDeadProp.proposedSpell.isNone &&
    !gDeadProp.log.any (· == "SHOULD_NOT_RUN") &&
    gDeadProp2.proposedSpell.isNone &&
    !gDeadProp2.log.any (· == "SHOULD_NOT_RUN") &&
    gOuterDepthProbe.firstContinuationPriorityGrant? == some (some p2)

  -- 1b. Interactive continuation ordering & `openCont`:
  --     - `afterTriggerTargetsChosen` & `stackTriggers` drain queued continuations before `receivePriority`;
  --     - `finishScry` splits only leading `.finishPostCast` prefix ahead of `currentInterpWait?`;
  --     - `keepLegend` routes non-`.finishSbaSweep` outer through `reattachOuterCont` behind `currentInterpWait?`;
  --     - `.restorePending` for `.resolveRandom (.chooseObject ids)` runs `currentInterpWait?`
  --       ahead of `outerCont?`/`popped?`;
  --     - `.turnFaceUp` preserves queued `outerPendingReplacements` (`openCont`) cleanly.
  let logIdx? (base g : Game) (msg : String) : Option Nat :=
    (g.events.extract base.events.size g.events.size).findIdx? fun e =>
      match e.change with
      | .engine (.logMsg s) => s == msg
      | _ => false
  let prioIdx? (base g : Game) (who : PlayerId) : Option Nat :=
    (g.events.extract base.events.size g.events.size).findIdx? fun e =>
      match e.change with
      | .engine (.priority r) => r == who
      | _ => false
  let gainIdx? (base g : Game) : Option Nat :=
    (g.events.extract base.events.size g.events.size).findIdx? fun e =>
      match e.change with
      | .rules (.life _) => true
      | _ => false

  let gAfterTrigQueued :=
    (g3.change (.pendingPriority (some p1))).chainPendingReplacement (.logMessage "QUEUED_BEFORE_PRIO")
  let gAfterTrigDone := gAfterTrigQueued.afterTriggerTargetsChosen
  let afterTrigOrderOk :=
    match logIdx? gAfterTrigQueued gAfterTrigDone "QUEUED_BEFORE_PRIO",
          prioIdx? gAfterTrigQueued gAfterTrigDone p1 with
    | some li, some pi => li < pi
    | _, _ => false

  let gStackTrig0 :=
    let g1 := addPermanent g3 bear p0 p0
    let bObj := (g1.permanentsOf p0)[0]!
    let tAb1 := TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 1)
    let tAb2 := TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 2)
    let g2 := g1.change (.enqueueWaitingTriggers #[
      { controller := p0, source := bObj, ability := tAb1, pattern := .thisEnters },
      { controller := p0, source := bObj, ability := tAb2, pattern := .thisEnters }
    ])
    let g3' := g2.change (.pending (.chooseTriggerToStack p0))
    let g4' := g3'.change (.pendingPriority (some p1))
    g4'.chainPendingReplacement (.logMessage "QUEUED_BEFORE_STACK_TRIG_PRIO")
  let gStackTrigDone :=
    match gStackTrig0.stackTriggers p0 #[0, 1] with
    | .ok g => g
    | .error _ => gStackTrig0
  let stackTrigOrderOk :=
    match logIdx? gStackTrig0 gStackTrigDone "QUEUED_BEFORE_STACK_TRIG_PRIO",
          prioIdx? gStackTrig0 gStackTrigDone p1 with
    | some li, some pi => li < pi
    | _, _ => false

  let interpLogWait : InterpState :=
    { ctx := { controller := p0 }
      queue := #[.life (.gain .you (.const 1))]
      stack := #[] }
  let gScrySplit0 :=
    (gWithLib.beginScry p0 1).changes #[
      .interpWait? (some interpLogWait),
      .pendingReplacement (some (.seq (.finishPostCast p0 false true true) (.logMessage "POST_OUTER")))
    ]
  let gScrySplit1 := mustApply gScrySplit0 p0 (.scry #[] #[(gWithLib.player p0).library.back!])
  let scrySplitOk :=
    match gainIdx? gScrySplit0 gScrySplit1, logIdx? gScrySplit0 gScrySplit1 "POST_OUTER" with
    | some gi, some li => gi < li
    | _, _ => false

  let legDef : CardDef := {
    creature "P58i1 Legend" ManaCost.empty #["Hero"] 2 2 with
    supertypes := #[.legendary]
  }
  let gLeg0 := addPermanent (addPermanent g3 legDef p0 p0) legDef p0 p0
  let legIds := (gLeg0.permanentsOf p0).map (·.id)
  let gLegPrompt :=
    (gLeg0.change (.pending (.chooseLegend p0 legDef.name legIds))).changes #[
      .pushContinuationFrame {
        interpWait? := some interpLogWait
        pendingReplacement := some (.logMessage "LEGEND_OUTER")
      }
    ]
  let gLegDone := mustApply gLegPrompt p0 (.keepLegend legIds[0]!)
  let keepLegendOrderOk :=
    match gainIdx? gLegPrompt gLegDone, logIdx? gLegPrompt gLegDone "LEGEND_OUTER" with
    | some gi, some li => gi < li
    | _, _ => false

  let gRestoreChoice0 :=
    g3.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "POPPED_OUTER"]
        interpWait? := some interpLogWait
        pendingReplacement := some (.logMessage "INLINE_OUTER")
      }
    ]
  let gRestoreChoice1 :=
    (gRestoreChoice0.resumePendingReplacement
      (.restorePending (.resolveRandom (.chooseObject #[⟨99999⟩])) true none #[] none)).drainPendingContinuations
  let restoreOrderOk :=
    match gainIdx? gRestoreChoice0 gRestoreChoice1,
          logIdx? gRestoreChoice0 gRestoreChoice1 "INLINE_OUTER",
          logIdx? gRestoreChoice0 gRestoreChoice1 "POPPED_OUTER" with
    | some gi, some ii, some pi => gi < ii && ii < pi
    | _, _, _ => false

  -- `.turnFaceUp` `openCont`: queued `.logMessage "TFU_OUTER"` in `outerPendingReplacements`
  -- runs cleanly after turning a face-down creature with Morph `{0}` face up!
  let morphZeroDef : CardDef := {
    creature "P58i1 FreeMorph" ManaCost.empty #["Shapeshifter"] 2 2 with
    keywords := #[.morph {}]
  }
  let gTfu0 := addPermanent g3 morphZeroDef p0 p0
  let morphId := (gTfu0.permanentsOf p0).find? (·.name == morphZeroDef.name) |>.get!.id
  let gTfuFd :=
    (gTfu0.record (GameEvent.turnedFaceDown gTfu0.turnNumber (gTfu0.snapshot (gTfu0.object! morphId))
      (cause := testCause))).changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "TFU_OUTER"]
      }
    ]
  let gTfuDone := mustApply gTfuFd p0 (.activate morphId 0)
  let turnFaceUpOpenContOk :=
    !(gTfuDone.object! morphId).status.faceDown &&
    gTfuDone.log.any (· == "TFU_OUTER")

  mustHold58i1 "1a_advLiveQueue" advLiveQueueOk &&
  mustHold58i1 "1a_multiFrame" multiFrameOk &&
  mustHold58i1 "1a_interpWaitProbe" interpWaitProbeOk &&
  mustHold58i1 "1a_runtimeVsPostPrompt" runtimeVsPostPromptOk &&
  mustHold58i1 "1a_unifiedDrainAndTrig" unifiedDrainAndTrigOk &&
  mustHold58i1 "1a_implicitProposal" implicitProposalOk &&
  mustHold58i1 "1a_stepCanReverse" stepCanReverseOk &&
  mustHold58i1 "1b_afterTrigOrder" afterTrigOrderOk &&
  mustHold58i1 "1b_stackTrigOrder" stackTrigOrderOk &&
  mustHold58i1 "1b_scrySplit" scrySplitOk &&
  mustHold58i1 "1b_keepLegendOrder" keepLegendOrderOk &&
  mustHold58i1 "1b_restoreOrder" restoreOrderOk &&
  mustHold58i1 "1b_turnFaceUpOpenCont" turnFaceUpOpenContOk &&
  mustHold58i1 "1.replay"
    (replayOk58i1 #[gMultiFrameDrained, gOpenNonSbaFin, gOpenNonSbaImplicitFin,
      gChImp0, gChImp1, gDeadProp, gDeadProp2, gAfterTrigDone, gStackTrigDone,
      gScrySplit1, gLegDone, gRestoreChoice1, gTfuDone])

end Phase58Item1EventAlignment

/-! ### Phase 58 Item 2: `.playFromExile` emitter predicates, `hasPlayFromExileLoggedInSlice`
`batchEnd`/`preIdx`/bipartite `resolveSaturated`/pre-log `mkHistoricalGameAt`,
`isPlayFromExileDeferBoundaryLeaf` + `containsProposalReversal` + `emitExpiredPlayFromExileLogs`
boundary stop, `expireLeavingObjectEffectsWithLogs` live-emblem deferral, `playerLeavesGameCore`
`exileQueue` order, `createEffects` single-end reconciliation, CR 704.5d/e/q SBA & `keepLegend`
`deferPfe`, `Turns.untapStepPermanents` stun-pause, and remaining simultaneous move/counter loops -/
section Phase58Item2EventAlignment

private def mustHold58i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase58Item2EventAlignment failed: {label}"

private def replayOk58i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let exCardDef : CardDef := { name := "P58i2 ExCard", types := #[.sorcery] }
  let srcADef : CardDef := { name := "P58i2 SrcA", types := #[.artifact] }
  let srcBDef : CardDef := { name := "P58i2 SrcB", types := #[.artifact] }

  -- 2a(i) & 2a(iii). `isPlayFromExileDeferBoundaryLeaf` includes the 10 new boundary leaves;
  --                  `emitExpiredPlayFromExileLogs` stops `targetUpdate?` at a boundary slot
  --                  instead of injecting past `.finishCleanupAfterClearEot` or a proposal-reversal leaf,
  --                  and respects `.moveSimultaneousToGraveyard` `deferPlayFromExileLogs` flag!
  let boundaryLeavesOk :=
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.continueStartNextTurn p0 #[] true #[]) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.finishPostStep .advanceAfterStepEnded) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf
      (.payCostPickItems p0 none none .sacrificeAnotherCreature #[] none) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf
      (.finishActivationExtraCosts p0 ⟨1⟩ none false false .stunAndSacrifice 0) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.finishPostStep (.resumeChooseModeAfterLeave p0)) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.finishPostStep (.resumeChooseTargetsAfterLeave p0)) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.finishPostStep (.resumeProposalCostAfterLeave p0 .none)) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.finishPostStep (.resumeTriggerModesAfterLeave p0 ⟨1⟩ 1 #[])) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.finishPostStep (.resumeUpToTriggerModesAfterLeave p0 ⟨1⟩ 1 #[])) &&
    PendingReplacement.isPlayFromExileDeferBoundaryLeaf (.finishPostStep (.resumeHawkeyeModesAfterLeave p0 ⟨1⟩ 1 #[]))

  -- Test `expireLeavingObjectEffectsWithLogs` live-emblem deferral + `emitExpiredPlayFromExileLogs` boundary stop:
  let gEmb0 := insertObject (addPermanent g3 srcADef p0 p0) exCardDef p0 .exile
  let srcAId := (gEmb0.permanentsOf p0).find? (·.name == srcADef.name) |>.get!.id
  let exCardId := (gEmb0.objects.find? (·.name == exCardDef.name)).get!.id
  let gEmb1 := gEmb0.createCommandObject p0 { name := "P58i2 Emblem", types := #[] }
  let embId := (gEmb1.objects.find? (·.name == "P58i2 Emblem")).get!.id
  let gEmb2 :=
    (gEmb1.createEffect (.gameRule (.commandEmblem embId) (.untilSourceLeaves srcAId))
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile exCardId { player := p0 }) (.whileInZone embId .command))
      (cause := some testCause)
  let preIdxEmb := gEmb2.events.size
  let gEmbDeferred :=
    gEmb2.expireLeavingObjectEffectsWithLogs (gEmb2.object! srcAId) (includeWhileSource := true)
  let pfeLogsDuringDefer :=
    (gEmbDeferred.log.extract gEmb2.log.size gEmbDeferred.log.size).filter
      (·.contains "can no longer be played from exile")
  let gEmbEmitted := emitExpiredPlayFromExileLogs gEmb2 gEmbDeferred preIdxEmb
  let pfeLogsAfterEmit :=
    (gEmbEmitted.log.extract gEmb2.log.size gEmbEmitted.log.size).filter
      (·.contains "can no longer be played from exile")
  let emblemDeferOk :=
    pfeLogsDuringDefer.isEmpty && pfeLogsAfterEmit.size == 1

  -- Boundary stop + `containsProposalReversal` + `.moveSimultaneousToGraveyard` `deferPlayFromExileLogs`:
  -- (a) With a second active `.playFromExile` on `exCardId`, `emitExpiredPlayFromExileLogs` enters the
  --     `deferredIds` injection path:
  --     - `outerPendingReplacements := #[.logMessage "LATER", .finishCleanupAfterClearEot]` stops at
  --       `.finishCleanupAfterClearEot` (slot 1), leaving slot 0 = `.logMessage "LATER"` untouched!
  --     - With an active `proposedSpell`, `outerPendingReplacements := #[.logMessage "LATER", .finishTurnFaceUp ..]`
  --       stops at `.finishTurnFaceUp` (`containsProposalReversal`), leaving slot 0 = `.logMessage "LATER"` untouched!
  -- (b) With `fromEventIdx? := some preIdxEmb`, `.moveSimultaneousToGraveyard` with
  --     `deferPlayFromExileLogs := false` suppresses duplicate emission in `hasPlayFromExileLoggedInSlice`,
  --     while `deferPlayFromExileLogs := true` does NOT suppress emission.
  let gEmb2Two :=
    gEmb2.createEffect (.permission (some p0) (.playFromExile exCardId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let preIdxEmbTwo := gEmb2Two.events.size
  let gEmbDeferredTwo :=
    gEmb2Two.expireLeavingObjectEffectsWithLogs (gEmb2Two.object! srcAId) (includeWhileSource := true)
  let gBound0 :=
    gEmbDeferredTwo.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "LATER", .finishCleanupAfterClearEot]
      }
    ]
  let gBound1 := emitExpiredPlayFromExileLogs gEmb2Two gBound0 preIdxEmbTwo
  let dummyProp : ProposedSpell := {
    spellId := srcAId, caster := p0, cost := ManaCost.empty, original := gEmb2.object! srcAId,
    originalSnapshot := gEmb2.snapshot (gEmb2.object! srcAId), kind := .turnFaceUp
  }
  let gBoundRev0 :=
    gEmbDeferredTwo.changes #[
      .proposedSpell (some dummyProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "LATER", .finishTurnFaceUp p0 srcAId false]
      }
    ]
  let gBoundRev1 := emitExpiredPlayFromExileLogs gEmb2Two gBoundRev0 preIdxEmbTwo
  let gPauseBase := gEmbDeferred.change (.pending (.chooseReplacement p0 #[]))
  let gMoveSimEmit1 :=
    (gPauseBase.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.moveSimultaneousToGraveyard #[] none (some testCause)
          (deferPlayFromExileLogs := false) (fromEventIdx? := some preIdxEmb)]
      }
    ]).runEndControlExileLoop #[(srcAId, "exile", some p0)] (some testCause)
      (fromEventIdx? := some preIdxEmb) (deferPlayFromExileLogs := true)
  let gMoveSimDefer1 :=
    (gPauseBase.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.moveSimultaneousToGraveyard #[] none (some testCause)
          (deferPlayFromExileLogs := true) (fromEventIdx? := some preIdxEmb)]
      }
    ]).runEndControlExileLoop #[(srcAId, "exile", some p0)] (some testCause)
      (fromEventIdx? := some preIdxEmb) (deferPlayFromExileLogs := true)
  let gInterpLoopEmit1 :=
    (gPauseBase.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.continueInterpreter {
          ctx := { controller := p0 }, queue := #[],
          stack := #[.afterMoveLoop #[] .exile .exile {} testCause (some preIdxEmb)]
        }]
      }
    ]).runEndControlExileLoop #[(srcAId, "exile", some p0)] (some testCause)
      (fromEventIdx? := some preIdxEmb) (deferPlayFromExileLogs := true)
  let isDeferredEndCtrl (g : Game) : Option Bool :=
    match g.pendingReplacement with
    | some (.endControlExileLoop _ _ _ _ _ d) => some d
    | _ => none
  -- PR #712 review regressions:
  -- (c) Non-reversing `.restorePending .none false` and `.restorePending .none true` over a
  --     non-reversing outer do NOT cut off later non-boundary slots while `proposedSpell.isSome`;
  --     whereas `.restorePending .none true` over a reversing outer or a proposal-pause payload
  --     (`.activateManaAbilities`) with `rewindProposal := none` DOES stop before later slots.
  let gRestNoRev0 :=
    gEmbDeferredTwo.changes #[
      .proposedSpell (some dummyProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "NON_BOUNDARY_OUTER"]
        pendingReplacement := some (.restorePending .none false none #[] none)
      }
    ]
  let gRestNoRev1 := emitExpiredPlayFromExileLogs gEmb2Two gRestNoRev0 preIdxEmbTwo
  let gRestPopNoRev0 :=
    gEmbDeferredTwo.changes #[
      .proposedSpell (some dummyProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "NON_BOUNDARY_OUTER"]
        pendingReplacement := some (.restorePending .none true none #[] none)
      }
    ]
  let gRestPopNoRev1 := emitExpiredPlayFromExileLogs gEmb2Two gRestPopNoRev0 preIdxEmbTwo
  let gRestPopRev0 :=
    gEmbDeferredTwo.changes #[
      .proposedSpell (some dummyProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "AFTER_REV", .finishTurnFaceUp p0 srcAId false]
        pendingReplacement := some (.restorePending .none true none #[] none)
      }
    ]
  let gRestPopRev1 := emitExpiredPlayFromExileLogs gEmb2Two gRestPopRev0 preIdxEmbTwo
  let gRestPauseRev0 :=
    gEmbDeferredTwo.changes #[
      .proposedSpell (some dummyProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "AFTER_PAUSE_REV"]
        pendingReplacement := some (.restorePending (.activateManaAbilities p0) false none #[] none)
      }
    ]
  let gRestPauseRev1 := emitExpiredPlayFromExileLogs gEmb2Two gRestPauseRev0 preIdxEmbTwo
  -- (d) Bare `.finishResolutionChoice` / `.receivePriority _` on the top frame keeps same-top-frame
  --     non-boundary outers in `searchSlots` while `proposedSpell.isSome`, without crossing to lower frames!
  let gBarePrioTop0 :=
    gEmbDeferredTwo.changes #[
      .proposedSpell (some dummyProp),
      .pushContinuationFrame {
        pendingReplacement := some (.logMessage "LOWER_FRAME")
      },
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "TOP_NON_BOUNDARY"]
        pendingReplacement := some .finishResolutionChoice
      }
    ]
  let gBarePrioTop1 := emitExpiredPlayFromExileLogs gEmb2Two gBarePrioTop0 preIdxEmbTwo
  let gBareRecvTop0 :=
    gEmbDeferredTwo.changes #[
      .proposedSpell (some dummyProp),
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "AFTER_REV", .finishTurnFaceUp p0 srcAId false, .logMessage "BEFORE_REV"]
        pendingReplacement := some (.receivePriority p0)
      }
    ]
  let gBareRecvTop1 := emitExpiredPlayFromExileLogs gEmb2Two gBareRecvTop0 preIdxEmbTwo
  let boundaryStopOk :=
    gBound1.outerPendingReplacements[0]? == some (.logMessage "LATER") &&
    (gBound1.outerPendingReplacements[1]?.any (·.containsDeferredPlayFromExile exCardId)) &&
    gBoundRev1.outerPendingReplacements[0]? == some (.logMessage "LATER") &&
    (gBoundRev1.outerPendingReplacements[1]?.any (·.containsDeferredPlayFromExile exCardId)) &&
    isDeferredEndCtrl gMoveSimEmit1 == some true &&
    isDeferredEndCtrl gMoveSimDefer1 == some false &&
    isDeferredEndCtrl gInterpLoopEmit1 == some true &&
    (gRestNoRev1.outerPendingReplacements[0]?.any (·.containsDeferredPlayFromExile exCardId)) &&
    (gRestPopNoRev1.outerPendingReplacements[0]?.any (·.containsDeferredPlayFromExile exCardId)) &&
    (gRestPopRev1.pendingReplacement.any (·.containsDeferredPlayFromExile exCardId)) &&
    gRestPopRev1.outerPendingReplacements[0]? == some (.logMessage "AFTER_REV") &&
    (gRestPauseRev1.pendingReplacement.any (·.containsDeferredPlayFromExile exCardId)) &&
    gRestPauseRev1.outerPendingReplacements[0]? == some (.logMessage "AFTER_PAUSE_REV") &&
    (gBarePrioTop1.outerPendingReplacements[0]?.any (·.containsDeferredPlayFromExile exCardId)) &&
    gBarePrioTop1.continuations[0]!.pendingReplacement == some (.logMessage "LOWER_FRAME") &&
    (gBareRecvTop1.outerPendingReplacements[2]?.any (·.containsDeferredPlayFromExile exCardId)) &&
    gBareRecvTop1.outerPendingReplacements[0]? == some (.logMessage "AFTER_REV")

  -- 2a(ii). `hasPlayFromExileLoggedInSlice` unbatched multi-event + interleaved `.engine`/`.life`
  --         and bipartite `resolveSaturated` (two overlapping `.playFromExile` expirations on two
  --         exiled cards with non-uniform eligibility sets):
  let gSlice0 :=
    insertObject (insertObject (addPermanent (addPermanent g3 srcADef p0 p0) srcBDef p0 p0)
      exCardDef p0 .exile)
      { exCardDef with name := "P58i2 ExCard2" } p0 .exile
  let sA := (gSlice0.permanentsOf p0).find? (·.name == srcADef.name) |>.get!.id
  let sB := (gSlice0.permanentsOf p0).find? (·.name == srcBDef.name) |>.get!.id
  let ex1 := (gSlice0.objects.find? (·.name == exCardDef.name)).get!.id
  let ex2 := (gSlice0.objects.find? (·.name == "P58i2 ExCard2")).get!.id
  let gSlice1 :=
    ((gSlice0.createEffect (.permission (some p0) (.playFromExile ex1 { player := p0 }) (.untilSourceLeaves sA))
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile ex2 { player := p0 }) (.untilSourceLeaves sA))
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile ex2 { player := p0 }) (.untilSourceLeaves sB))
        (cause := some testCause)
  let slicePre := gSlice1
  let sliceFrom := gSlice1.events.size
  -- Interleave a life-gain event and an engine log between unbatched expirations:
  let gSlice2 :=
    let g := gSlice1.gainLife p0 1 (cause := some testCause)
    let g := g.logMsg "interleaved"
    let g := g.expireMatching (fun e => e.duration == .untilSourceLeaves sA)
      (cause := some testCause) (deferPlayFromExileLogs := true)
    let g := g.logMsg "between"
    g.expireMatching (fun e => e.duration == .untilSourceLeaves sB)
      (cause := some testCause) (deferPlayFromExileLogs := true)
  let gSlice3 := emitExpiredPlayFromExileLogs slicePre gSlice2 sliceFrom
  let gSlice4 := emitExpiredPlayFromExileLogs slicePre gSlice3 sliceFrom
  let slicePfeLogs :=
    (gSlice3.log.extract gSlice2.log.size gSlice3.log.size).filter
      (·.contains "can no longer be played from exile")
  let sliceDedupLogs :=
    (gSlice4.log.extract gSlice3.log.size gSlice4.log.size).filter
      (·.contains "can no longer be played from exile")
  let sliceBipartiteOk :=
    slicePfeLogs.size == 2 && sliceDedupLogs.isEmpty

  -- 2a(iv). `createEffects` reconciles control once at the end of a multi-effect batch, and
  --         `playerLeavesGameCore` processes `exileQueue` cleanly in order!
  let gCtrl0 := addPermanent g3 bear p0 p0
  let ctrlBearId := (gCtrl0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gCtrl1 :=
    gCtrl0.createEffects #[
      .layered (.objects #[ctrlBearId]) (.control p1) .indefinite,
      .layered (.objects #[ctrlBearId]) (.control p0) .indefinite
    ] (cause := some testCause)
  let ctrlReturnLogs :=
    (gCtrl1.log.extract gCtrl0.log.size gCtrl1.log.size).filter (·.contains "control")
  let createEffectsBatchOk :=
    gCtrl1.controlledBy (gCtrl1.object! ctrlBearId) p0 && ctrlReturnLogs.isEmpty

  let gLeave0 := addPermanent (addPermanent g3 bear p0 p1) { bear with name := "P58i2 P1Ctrl" } p0 p1
  let (gLeave1, _, _, _) := gLeave0.playerLeavesGameCore p1
  let playerLeaveOk :=
    (gLeave1.player p1).leftTheGame &&
    (gLeave1.permanentsOf p1).isEmpty &&
    !(gLeave1.objects.any (fun o => o.owner == p0 && o.zone == .battlefield && gLeave1.controlledBy o p1))

  -- 2b(i). CR 704.5d/e/q SBA: token outside battlefield ceases to exist, +1/+1 & -1/-1 annihilate
  --        without ghost events on leaving creatures.
  let tokSbaDef : CardDef := {
    creature "P58i2 SbaTok" ManaCost.empty #["Goblin"] 1 1 with
    isToken := true
  }
  let gSba0 := addPermanent (addPermanent g3 bear p0 p0) { bear with name := "P58i2 Bear2" } p0 p0
  let (gSbaT0, tokSba) := gSba0.createOneToken p0 tokSbaDef (cause := some testCause)
  let (gSbaT1, tokGyId) := gSbaT0.move tokSba.id (.graveyard p0) none (cause := some testCause)
  let b1 := (gSbaT1.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let b2 := (gSbaT1.permanentsOf p0).find? (·.name == "P58i2 Bear2") |>.get!.id
  let gSba1 :=
    ((gSbaT1.recordPutCounters b1 .plusOnePlusOne 2 (cause := some testCause)).recordPutCounters
      b1 .minusOneMinusOne 2 (cause := some testCause)).recordPutCounters
      b2 .minusOneMinusOne 2 (cause := some testCause)
  let gSbaAfter := gSba1.checkSBA
  let sbaOk :=
    (gSbaAfter.findObject? b1).any (fun o => o.isOnBattlefield && o.status.plusOnePlusOne == 0 && o.status.minusOneMinusOne == 0) &&
    !(gSbaAfter.findObject? b2).any (·.isOnBattlefield) &&
    (gSbaAfter.findObject? tokGyId).isNone

  -- 2b(ii). `Turns.untapStepPermanents` defers `.playFromExile` and removes stun counter cleanly;
  --         `Interpreter.execCounterOp` removes multiple counter kinds per permanent via `recordRemoveCountersMulti`.
  let gUntap0 :=
    insertObject (addPermanent (addPermanent g3 bear p0 p0) { bear with name := "P58i2 Untap2" } p0 p0)
      exCardDef p0 .exile
  let u1 := (gUntap0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let u2 := (gUntap0.permanentsOf p0).find? (·.name == "P58i2 Untap2") |>.get!.id
  let gUntap1 :=
    ((gUntap0.record (GameEvent.tapped gUntap0.turnNumber (gUntap0.snapshot (gUntap0.object! u1)) true (cause := testCause))).record
      (GameEvent.tapped gUntap0.turnNumber (gUntap0.snapshot (gUntap0.object! u2)) true (cause := testCause))).recordPutCounters
      u1 .stun 1 (cause := some testCause)
  let gUntapDone := gUntap1.untapStepPermanents #[u1, u2]
  let untapStunOk :=
    (gUntapDone.object! u1).status.tapped &&
    (gUntapDone.object! u1).status.stun == 0 &&
    !(gUntapDone.object! u2).status.tapped

  let gCtrOp0 :=
    (gUntap0.recordPutCounters u1 .plusOnePlusOne 1 (cause := some testCause)).recordPutCounters
      u1 .shield 1 (cause := some testCause)
  let gCtrOp1 :=
    gCtrOp0.applyUnified p0
      { body := .permanent (.modifyCounters (.remove none .anyNumber) .this) } #[]
      (sourceId := some u1)
  let ctrOpOk :=
    (gCtrOp1.object! u1).status.plusOnePlusOne == 0 &&
    (gCtrOp1.object! u1).status.shield == 0

  -- 2b(iii). Simultaneous move loops (`discardHandIdsLoop`, `millCardsLoop`) complete cleanly
  --          with deferred `.playFromExile` logging.
  let gDiscLoop0 := insertObject (insertObject g3 bear p0 (.hand p0)) { bear with name := "P58i2 BearHand2" } p0 (.hand p0)
  let hand2 := (gDiscLoop0.player p0).hand
  let gDiscLoop1 := gDiscLoop0.discardHandIdsLoop p0 hand2 (logEach := true) (cause := some testCause)
  let gMillLoop0 := insertObject (insertObject g3 bear p0 (.library p0)) { bear with name := "P58i2 BearLib2" } p0 (.library p0)
  let lib2 := (gMillLoop0.player p0).library
  let gMillLoop1 := gMillLoop0.millCardsLoop p0 lib2 (cause := some testCause)
  let simLoopsOk :=
    (gDiscLoop1.player p0).hand.isEmpty &&
    (gMillLoop1.player p0).library.isEmpty

  mustHold58i2 "2a_boundaryLeaves" boundaryLeavesOk &&
  mustHold58i2 "2a_emblemDefer" emblemDeferOk &&
  mustHold58i2 "2a_boundaryStop" boundaryStopOk &&
  mustHold58i2 "2a_sliceBipartite" sliceBipartiteOk &&
  mustHold58i2 "2a_createEffectsBatch" createEffectsBatchOk &&
  mustHold58i2 "2a_playerLeave" playerLeaveOk &&
  mustHold58i2 "2b_sba" sbaOk &&
  mustHold58i2 "2b_untapStun" untapStunOk &&
  mustHold58i2 "2b_ctrOp" ctrOpOk &&
  mustHold58i2 "2b_simLoops" simLoopsOk &&
  mustHold58i2 "2.replay"
    (replayOk58i2 #[gEmbDeferred, gEmbEmitted, gBound1, gRestNoRev1, gRestPopNoRev1,
      gRestPopRev1, gRestPauseRev1, gBarePrioTop1, gBareRecvTop1, gSlice3, gCtrl1,
      gLeave1, gSbaAfter, gUntapDone, gCtrOp1, gDiscLoop1, gMillLoop1])

end Phase58Item2EventAlignment

/-! ### Phase 58 Item 3: Layer 6 `ownUncondDelta.rem`/`grantedDelta.rem` & fast paths (self-static,
attached-host non-attached-scope, transitive `.grantStatic`, `hasKwDepAttStatic`, stack-spell Layer-6),
Layer-6 Cascade & cumulative Extort, `mkHistoricalGameAt` & `wasPreparedAtDeparture?` designation LKI,
`Turns` self-`untilNextTurnOf` & `Damage.replaceDamage` duplicate `.protectionFrom .everything` &
`.subtype (.fromStep v)` & Hexproof from quality, `.nthResolutionThisTurn` cross-source /
`.scriedThisTurn` departed player / `.manaSpent` copy & bound, and face-down exile
`actualPrintedManaCost?` / `playManaCost` `cardForCaster` / `spellFaceView` `.stack` + Layer-6
keywords / card-type & cumulative Affinity -/
section Phase58Item3EventAlignment

private def mustHold58i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase58Item3EventAlignment failed: {label}"

private def replayOk58i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let srcA3Def : CardDef := { name := "P58i3 SrcA", types := #[.artifact] }
  let srcB3Def : CardDef := { name := "P58i3 SrcB", types := #[.artifact] }

  -- 3a(i) & 3a(ii). Layer 6:
  --   - `ownUncondDelta.rem` (self-static removing own printed keyword) honored!
  --   - `grantedDelta.rem` (active-effect `.loseIndestructible` / `.all` removal at timestamp) honored!
  --   - self-applied `.continuous` static (`src.id == o.id`) honored by fast paths!
  --   - non-attached-host static on an attached Aura honored by fast paths!
  --   - `hasKwDepAttStatic` (attached Aura with keyword-dependent condition) honored by fast paths!
  --   - transitive `.grantStatic` from a peer granting a Layer-6 static honored!
  --   - battlefield peer / command emblem Layer-6 static applying to a stack spell honored!
  let selfRemDef : CardDef := {
    creature "P58i3 SelfRem" ManaCost.empty #["Human"] 2 2 with
    keywords := #[Keyword.flying]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .sameAs .this }
        .loseAllAbilities
    ]
  }
  let selfGrantDef : CardDef := {
    creature "P58i3 SelfGrant" ManaCost.empty #["Human"] 2 2 with
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .sameAs .this }
        (.grantKeywords #[Keyword.vigilance])
    ]
  }
  let auraGlobalDef : CardDef := {
    name := "P58i3 GlobalAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[
      .continuous none
        { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] }
        (.grantKeywords #[Keyword.trample]),
      .continuous
        (some (.forAll .attachedHost (.hasKeyword .vigilance)))
        { zones := .battlefield, pred := .sameAs .attachedHost }
        (.grantKeywords #[Keyword.reach])
    ]
  }
  let peerGrantStaticDef : CardDef := {
    name := "P58i3 PeerGrantStatic"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none
        { zones := .battlefield, pred := .all #[.hasType .artifact, .controlledBy .you] }
        (.grantStatic #[
          .continuous none
            { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] }
            (.grantKeywords #[Keyword.haste])
        ])
    ]
  }
  let gL6_0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g3 selfRemDef p0 p0) selfGrantDef p0 p0)
          auraGlobalDef p0 p0)
        srcA3Def p0 p0)
      peerGrantStaticDef p0 p0
  let selfRemId := (gL6_0.permanentsOf p0).find? (·.name == selfRemDef.name) |>.get!.id
  let selfGrantId := (gL6_0.permanentsOf p0).find? (·.name == selfGrantDef.name) |>.get!.id
  let auraId := (gL6_0.permanentsOf p0).find? (·.name == auraGlobalDef.name) |>.get!.id
  -- Attach `auraGlobalDef` to `selfGrantId` via `GameEvent.attached`:
  let gL6_1 :=
    gL6_0.record (GameEvent.attached gL6_0.turnNumber (gL6_0.snapshot (gL6_0.object! auraId))
      selfGrantId (cause := testCause))
  -- Test `grantedDelta.rem`: grant indestructible via active effect, then remove via `.loseIndestructible`:
  let gL6_2 :=
    (gL6_1.createEffect
      (.layered (.objects #[selfGrantId]) (.abilities { keywords := #[Keyword.indestructible] } .none) .indefinite)
      (cause := some testCause)).createEffect
      (.layered (.objects #[selfGrantId]) (.abilities {} .loseIndestructible) .indefinite)
      (cause := some testCause)
  -- Also test stack-spell Layer-6 grant from a command-zone emblem:
  let stackSpellDef : CardDef := {
    name := "P58i3 StackSpell"
    manaCost := { symbols := #[.colored .red] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let stackEmblemDef : CardDef := {
    name := "P58i3 StackEmblem"
    types := #[]
    staticAbilities := #[
      .continuous none
        { zones := { zones := #[.stack], owner := .ofPlayer .you }, pred := .hasType .instant }
        (.grantKeywords #[Keyword.cascade])
    ]
  }
  let gL6_3 :=
    insertObject (gL6_2.createCommandObject p0 stackEmblemDef) stackSpellDef p0 .stack
  let stackSpellObj := (gL6_3.objects.find? (·.name == stackSpellDef.name)).get!
  let layer6Ok :=
    mustHold58i3 "3a_l6_selfRem" (!gL6_2.hasSimpleKeyword (gL6_2.object! selfRemId) .flying) &&
    mustHold58i3 "3a_l6_selfGrant" (gL6_2.hasSimpleKeyword (gL6_2.object! selfGrantId) .vigilance) &&
    mustHold58i3 "3a_l6_auraGlobal" (gL6_2.hasSimpleKeyword (gL6_2.object! selfGrantId) .trample) &&
    mustHold58i3 "3a_l6_auraKwDep" (gL6_2.hasSimpleKeyword (gL6_2.object! selfGrantId) .reach) &&
    mustHold58i3 "3a_l6_peerGrantStatic" (gL6_2.hasSimpleKeyword (gL6_2.object! selfGrantId) .haste) &&
    mustHold58i3 "3a_l6_grantedRem" (!gL6_2.hasSimpleKeyword (gL6_2.object! selfGrantId) .indestructible) &&
    mustHold58i3 "3a_l6_stackEmblem" (KeywordAbility.cascadeCount (gL6_3.currentKeywords stackSpellObj) == 1)

  -- 3a(iii). Layer-6 Cascade (via emblem above!) & cumulative Extort (two Extort instances -> 2 triggers):
  let extortDef : CardDef := {
    creature "P58i3 DoubleExtort" ManaCost.empty #["Cleric"] 2 2 with
    keywords := #[Keyword.extort, Keyword.extort]
  }
  let gExt0 := insertObject (addPermanent gL6_3 extortDef p0 p0)
    { name := "P58i3 CastMe", manaCost := ManaCost.empty, types := #[.instant],
      spellAbility := some { effect := Effect.gainLife 1 } } p0 (.hand p0)
  let castMeId := (gExt0.player p0).hand.back!
  let gExt1 := mustApply gExt0 p0 (.cast castMeId)
  let extortTrigCount :=
    gExt1.waitingTriggers.foldl (fun acc w =>
      if w.source.name == extortDef.name then acc + 1 else acc) 0
  let cascadeTrigCount :=
    gExt1.waitingTriggers.foldl (fun acc w =>
      if w.source.name == "P58i3 CastMe" then acc + 1 else acc) 0
  let cascadeExtortOk :=
    extortTrigCount == 2 && cascadeTrigCount == 1

  -- 3a(iv). Designation LKI: `wasPreparedAtDeparture?` returns `none` when no entry/designation
  --         event exists, preserving `eo.prepared` on pre-log snapshots in `damageSourceFromSnapshot`,
  --         AND `mkHistoricalGameAt` preserves `status.prepared` across `copiable.isSome` entries!
  let preLogPrepEo : EventObject := {
    id := some ⟨77777⟩
    name := "P58i3 PreLogPrep"
    owner := p0
    controller := some p0
    types := #[.creature]
    prepared := true
  }
  let snapRestored := g3.damageSourceFromSnapshot preLogPrepEo
  let gPrep0 := addPermanent g3 bear p0 p0
  let prepId := (gPrep0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gPrep1 :=
    gPrep0.record (GameEvent.designation gPrep0.turnNumber (gPrep0.snapshot (gPrep0.object! prepId))
      .prepared true (cause := testCause))
  let gPrepHist := gPrep1.mkHistoricalGameAt gPrep1.events.size
  let designationLkiOk :=
    g3.wasPreparedAtDeparture? ⟨77777⟩ == none &&
    snapRestored.status.prepared &&
    (gPrepHist.findObject? prepId).any (·.status.prepared)

  -- 3b(i). Player protection & Hexproof from quality:
  --   - Self-`untilNextTurnOf` `.protectionFrom` survives `expireUntilTurnCommandEffects`,
  --     and logs CR 800.4m expiry on departure in `expireUntilNextTurnEffects`;
  --   - `Damage.replaceDamage` does NOT produce duplicate prevention candidates for `.protectionFrom .everything`;
  --   - `Interpreter.applyRuleMod` resolves `.protectionFrom (.subtype (.fromStep v))`;
  --   - `KeywordAbility.hexproof (some q)` & `PlayerRule.hexproof who (some q)` enforced!
  let gProt0 :=
    g3.createEffect (.playerRule p0 (.protectionFrom .everything) (.untilNextTurnOf p0))
      (cause := some testCause)
  let gProtAfterCmd := gProt0.expireUntilTurnCommandEffects p0
  let gProtDmg := gProtAfterCmd.dealDamageToPlayer p0 3 (source := none) (cause := some testCause)
  let gProtLeave := gProtAfterCmd.expireUntilNextTurnEffects p0
  let gProtStep0 :=
    g3.changes #[
      .pushContinuationFrame {
        stepEnv := #[(⟨1⟩, { chosenSubtype? := some .goblin, succeeded := true })]
      }
    ]
  let gProtStep1 :=
    gProtStep0.applyUnified p0
      { body := .installEffect (.applyRule .untilEndOfTurn
          (.player (.protectionFrom .you (.subtype (.fromStep ⟨1⟩))))) } #[]
  let redGoblinDef : CardDef := {
    creature "P58i3 RedGoblin" { symbols := #[.colored .red] } #["Goblin"] 1 1 with
    colorIndicator := some (ColorSet.singleton .red)
  }
  let blueBearDef : CardDef := {
    creature "P58i3 BlueBear" { symbols := #[.colored .blue] } #["Bear"] 2 2 with
    colorIndicator := some (ColorSet.singleton .blue)
  }
  let hexRedDef : CardDef := {
    creature "P58i3 HexRed" ManaCost.empty #["Knight"] 2 2 with
    keywords := #[.hexproof (some (.color (.literal .red)))]
  }
  let playerHexRedEmblem : CardDef := {
    name := "P58i3 PlayerHexRedEmblem"
    types := #[]
    staticAbilities := #[
      .ruleModifying none (.player (.hexproof .you (some (.color (.literal .red)))))
    ]
  }
  let gHex0 :=
    addPermanent
      (addPermanent
        (addPermanent (gProtStep1.createCommandObject p0 playerHexRedEmblem) hexRedDef p0 p0)
        redGoblinDef p1 p1)
      blueBearDef p1 p1
  let hexRedObj := (gHex0.permanentsOf p0).find? (·.name == hexRedDef.name) |>.get!
  let redGobObj := (gHex0.permanentsOf p1).find? (·.name == redGoblinDef.name) |>.get!
  let blueBearObj := (gHex0.permanentsOf p1).find? (·.name == blueBearDef.name) |>.get!
  let protAndHexOk :=
    gProtAfterCmd.protectionFromEverything p0 &&
    gProtDmg.pending == .none &&
    (gProtDmg.player p0).life == (gProtAfterCmd.player p0).life &&
    (gProtLeave.log.extract gProtAfterCmd.log.size gProtLeave.log.size).any
      (·.contains "protection") &&
    gHex0.playerProtectedFrom p0 (some redGobObj) &&
    !gHex0.playerProtectedFrom p0 (some blueBearObj) &&
    !gHex0.canBeTargetedBy p1 hexRedObj (some redGobObj.id) &&
    gHex0.canBeTargetedBy p1 hexRedObj (some blueBearObj.id) &&
    !gHex0.playerCanBeTargetedBy p1 p0 (some redGobObj.id) &&
    gHex0.playerCanBeTargetedBy p1 p0 (some blueBearObj.id)

  -- 3b(ii). `.nthResolutionThisTurn` cross-source check, `.scriedThisTurn` departed player,
  --         and `.manaSpent` returning 0 for an uncast stack copy!
  let gScryDep :=
    (g3.record (GameEvent.looked g3.turnNumber p2 1)).record
      (GameEvent.playerLeftGame g3.turnNumber p2)
  let scryDepHolds :=
    EvalExpr.evalCondition gScryDep { controller := p0 }
      (.turnHistory (.scriedThisTurn { relation := .anyPlayer, pred := .any }))
  let gNth0 := addPermanent (addPermanent g3 bear p0 p0) { bear with name := "P58i3 OtherSrc" } p0 p0
  let src1 := (gNth0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let src2 := (gNth0.permanentsOf p0).find? (·.name == "P58i3 OtherSrc") |>.get!.id
  let trig0 : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 1)
  let trig1 : TriggeredAbility := TriggeredAbility.mkTrigger .thisAttacks (Effect.gainLife 1)
  let gNth1 :=
    (gNth0.record (GameEvent.rules gNth0.turnNumber
      (.stackObject (.resolved (gNth0.snapshot (gNth0.object! src1)) 1 (some src1) (some trig0))) testCause)).putTriggerBatch
      #[{ controller := p0, source := gNth0.object! src2, ability := trig1, pattern := .thisAttacks }]
  let abOnStackId := gNth1.stack.back!.objectId
  let gNth2 := gNth1.change (.resolvingAbility (some abOnStackId))
  let nthOtherSourceOk :=
    -- Resolving `src2`'s `trig1` must NOT filter `src1`'s `.nthResolutionThisTurn 1` by `trig1`!
    EvalExpr.evalCondition gNth2 { controller := p0, sourceId := some src1 }
      (.turnHistory (.nthResolutionThisTurn 1))
  let copySpellId : ObjectId := ⟨88881⟩
  let copySpellEo : EventObject := {
    id := some copySpellId, name := "P58i3 StackCopy", owner := p0, controller := some p0,
    types := #[.instant], zone := .stack, isCopy := true
  }
  let gCopySpent :=
    (g3.record (GameEvent.rules g3.turnNumber (.stackObject (.copied src1 copySpellEo p0)) testCause)).record
      (GameEvent.rules g3.turnNumber (.player (.manaSpent p0 #[{ mana := .colored .red }] (some copySpellId))) testCause)
  let manaSpentCopyZero :=
    EvalExpr.evalValue gCopySpent { controller := p0, sourceId := some copySpellId } (.manaSpent .this) == 0
  let historyFixesOk := scryDepHolds && nthOtherSourceOk && manaSpentCopyZero

  -- 3b(iii). Face-down exiled card (`actualPrintedManaCost?` / `actualCastManaValue` / `playManaCost`
  --          with `withoutManaCost` & `cardForCaster` Layer-5 color static), `spellFaceView` `.stack`
  --          + Layer-6 keywords, and card-type & cumulative Affinity in `Costs.evalSpellCostMods`:
  let fdCardDef : CardDef := {
    name := "P58i3 FdExileSpell"
    manaCost := { symbols := #[.generic 3, .colored .red] }
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gFd0 := insertObject g3 fdCardDef p0 .exile
  let fdId := (gFd0.objects.find? (·.name == fdCardDef.name)).get!.id
  let gFd1 :=
    (gFd0.record (GameEvent.turnedFaceDown gFd0.turnNumber (gFd0.snapshot (gFd0.object! fdId))
      (cause := testCause))).createEffect
      (.permission (some p0) (.playFromExile fdId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  let fdObj := gFd1.object! fdId
  let fdCostFree := gFd1.playManaCost { fdObj with controller := some p0 } (gFd1.unmaskedCopiableValues fdObj)
  -- Layer-5 color-changing static affecting a spell on the stack + blue-spell cost reducer:
  let painterBlueDef : CardDef := {
    name := "P58i3 PainterBlue"
    types := #[.artifact]
    staticAbilities := #[
      .continuous none
        { zones := { zones := #[.stack], owner := .ofPlayer .you }, pred := .anyObject }
        (.modifyColors { mode := .add, colors := ColorSet.singleton .blue }),
      .costModifier none
        (.spells .you (.hasColor (.literal .blue)))
        (.reduceGeneric (.const 2))
    ]
  }
  let gColorCost0 := insertObject (addPermanent g3 painterBlueDef p0 p0) fdCardDef p0 (.hand p0)
  let colorCostObj := (gColorCost0.objects.find? (·.name == fdCardDef.name)).get!
  let colorCostReduced := gColorCost0.playManaCost colorCostObj fdCardDef
  let affCardDef : CardDef := {
    name := "P58i3 DoubleAffArt"
    manaCost := { symbols := #[.generic 4, .colored .blue] }
    types := #[.sorcery]
    keywords := #[
      .affinity { zones := .battlefield, pred := .hasType .artifact },
      .affinity { zones := .battlefield, pred := .hasType .artifact }
    ]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gAff0 :=
    insertObject (addPermanent (addPermanent g3 srcA3Def p0 p0) srcB3Def p0 p0) affCardDef p0 (.hand p0)
  let affObj := (gAff0.objects.find? (·.name == affCardDef.name)).get!
  -- 2 artifacts on battlefield * 2 Affinity for artifacts instances = 4 generic reduction -> `{U}`!
  let affCost := gAff0.playManaCost { affObj with controller := some p0 } affCardDef
  let spellView := EvalExpr.spellFaceView gL6_3 stackSpellObj stackSpellDef p0 (stackSpellDef.manaCost.manaValue)
  let spellViewIsSpell :=
    EvalExpr.evalObjectPred gL6_3 { controller := p0 } spellView (.isKind .spell)
  let spellViewZoneAndKwOk :=
    match spellView with
    | .lki eo => eo.zone == .stack && KeywordAbility.cascadeCount eo.keywords == 1
    | _ => false
  let fdAndAffOk :=
    mustHold58i3 "3b_fd_printedMc" (gFd1.actualPrintedManaCost? fdObj fdCardDef == some fdCardDef.manaCost) &&
    mustHold58i3 "3b_fd_mv" (gFd1.actualCastManaValue fdObj fdCardDef == 4) &&
    mustHold58i3 "3b_fd_free" (fdCostFree == { symbols := #[.generic 0] }) &&
    mustHold58i3 "3b_colorCost" (colorCostReduced == { symbols := #[.generic 1, .colored .red] }) &&
    mustHold58i3 "3b_affCost" (affCost == { symbols := #[.colored .blue] }) &&
    mustHold58i3 "3b_spellViewSpell" spellViewIsSpell &&
    mustHold58i3 "3b_spellViewZoneKw" spellViewZoneAndKwOk

  mustHold58i3 "3a_layer6" layer6Ok &&
  mustHold58i3 "3a_cascadeExtort" cascadeExtortOk &&
  mustHold58i3 "3a_designationLki" designationLkiOk &&
  mustHold58i3 "3b_protAndHex" protAndHexOk &&
  mustHold58i3 "3b_historyFixes" historyFixesOk &&
  mustHold58i3 "3b_fdAndAff" fdAndAffOk &&
  mustHold58i3 "3.replay"
    (replayOk58i3 #[gL6_3, gExt1, gPrep1, gProtAfterCmd, gProtDmg, gProtLeave, gProtStep1,
      gHex0, gScryDep, gNth2, gCopySpent, gFd1, gColorCost0, gAff0])

end Phase58Item3EventAlignment

/-! ### Phase 58 Item 4: Hybrid/twobrid `ManaPool.payUnits?`/`coveredMana`, `{X}` `isPlainTap`,
`tapChoicesForSource` multi-ability permanent, unprojected mana-ability `CostItem`s, same-permanent
non-plain chaining & `zemoOk`, `mayPlayLand` cast-only exclusion, non-card guards (`copyAndCast`,
`.reveal`, `discardNonlandFrom`, `.mayCastExiledElseDamage`, `graveyardCardsNamed`), and
`defaultChoiceAction` (`.extrapolateReveal`, `.mayPutMilledPermanent`, `.mayTapSourceThen`) -/
section Phase58Item4EventAlignment

private def mustHold58i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase58Item4EventAlignment failed: {label}"

private def replayOk58i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand afterDraw p0

  -- 4a(i). Hybrid/twobrid `ManaPool.payUnits?` & `coveredMana` exact backtracking solver:
  let poolBG : ManaPool := { units := #[{ mana := .colored .black }, { mana := .colored .green }] }
  let costHybridB : ManaCost := { symbols := #[.hybrid .black .green, .colored .black] }
  let poolWU : ManaPool := { units := #[{ mana := .colored .white }, { mana := .colored .blue }] }
  let costHybridOverlap : ManaCost := { symbols := #[.hybrid .white .blue, .hybrid .white .black] }
  let poolWCC : ManaPool := { units := #[{ mana := .colored .white }, { mana := .colorless }, { mana := .colorless }] }
  let costTwobridW : ManaCost := { symbols := #[.twobrid .white, .colored .white] }
  let poolWC : ManaPool := { units := #[{ mana := .colored .white }, { mana := .colorless }] }
  let hybridSolverOk :=
    (poolBG.payUnits? costHybridB).isSome &&
    poolBG.coveredMana costHybridB == 2 &&
    (poolWU.payUnits? costHybridOverlap).isSome &&
    poolWU.coveredMana costHybridOverlap == 2 &&
    (poolWCC.payUnits? costTwobridW).isSome &&
    poolWCC.coveredMana costTwobridW == 3 &&
    (poolWC.payUnits? costTwobridW).isNone

  -- 4a(ii) & 4a(iv). `{X}, {T}: Add {G}` and unprojected `CostItem`s (`.putCounters`):
  let xManaDef : CardDef := {
    name := "P58i4 XMana"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana { symbols := #[.x] }, .tapSelf]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let unprojManaDef : CardDef := {
    name := "P58i4 UnprojMana"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .putCounters (.const 1) .charge .self]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let gMana0 := addPermanent (addPermanent g0 xManaDef p0 p0) unprojManaDef p0 p0
  let xManaObj := (gMana0.permanentsOf p0).find? (·.name == xManaDef.name) |>.get!
  let unprojObj := (gMana0.permanentsOf p0).find? (·.name == unprojManaDef.name) |>.get!
  let xDef := (gMana0.manaAbilityDefs xManaObj)[0]!
  let unprojDef := (gMana0.manaAbilityDefs unprojObj)[0]!
  let xAndUnprojOk :=
    !xDef.isPlainTap &&
    !gMana0.isPlainTapManaAbilityDef p0 xManaObj xDef &&
    !gMana0.manaAbilityDefUsable p0 xManaObj xDef &&
    (gMana0.manaAbilityIndexFor xManaObj (.colored .green) (plainOnly := false)).isNone &&
    !(gMana0.activateManaAbility p0 xManaObj.id 0 #[.colored .green]).isOk &&
    unprojDef.hasUnmodeledCostItem &&
    !unprojDef.isPlainTap &&
    !gMana0.manaAbilityDefUsable p0 unprojObj unprojDef &&
    (gMana0.manaAbilityIndexFor unprojObj (.colored .green) (plainOnly := false)).isNone &&
    !(gMana0.activateManaAbility p0 unprojObj.id 0 #[.colored .green]).isOk

  -- 4a(iii). `tapChoicesForSource` enumerates multiple plain `{T}` abilities on one permanent
  --          without collapsing restricted 2-mana behind unrestricted 1-mana:
  let multiTapDef : CardDef := {
    name := "P58i4 MultiTap"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.tapSelf]
        effect := Effect.addMana #[.colored .green] },
      { cost := CostSpec.ofItems #[.tapSelf]
        effect := { body := .player (.addMana .you {
          spec := ManaSpec.fixed #[.colored .green, .colored .green]
          restriction := some (.onlyForSpells (.hasType .creature))
        }) } }
    ]
  }
  let gMultiTap := addPermanent g0 multiTapDef p0 p0
  let mtObj := (gMultiTap.permanentsOf p0).find? (·.name == multiTapDef.name) |>.get!
  let creatureSpend : ManaSpend := { spell := true, types := #[.creature] }
  let choices :=
    gMultiTap.tapChoicesForSource mtObj #[.colored .green]
      { symbols := #[.colored .green, .colored .green] } (spend := creatureSpend)
  let canPayGGCreature :=
    gMultiTap.canPayFromSources {} { symbols := #[.colored .green, .colored .green] }
      [(mtObj, #[.colored .green])] creatureSpend
  let multiTapOk :=
    choices.size == 2 &&
    choices.any (fun ch => ch.baseAdded == #[.colored .green, .colored .green]) &&
    canPayGGCreature

  -- 4a(v). Same-permanent non-plain chaining (`Pay 1 life: Add {G}` -> `{G}: Add {R}`) &
  --        non-black `canPayExileManaSymbols`:
  let chainPermDef : CardDef := {
    name := "P58i4 ChainPerm"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.payLife (.const 1)]
        effect := Effect.addMana #[.colored .green] },
      { cost := CostSpec.ofItems #[.mana { symbols := #[.colored .green] }]
        effect := Effect.addMana #[.colored .red] }
    ]
  }
  let gChainPerm := addPermanent g0 chainPermDef p0 p0
  let redPipsDef : CardDef := {
    name := "P58i4 RedPips"
    manaCost := { symbols := #[.colored .red, .colored .red, .colored .red] }
    types := #[.sorcery]
  }
  let gExSym := insertObject gChainPerm redPipsDef p0 (.graveyard p0)
  let chainPermId := (gExSym.permanentsOf p0).find? (·.name == chainPermDef.name) |>.get!.id
  let samePermChainOk :=
    gChainPerm.hasUsableNonPlainManaAbility p0 &&
    gExSym.canPayExileManaSymbols p0 chainPermId (some .red) 3 .anyObject &&
    !gExSym.canPayExileManaSymbols p0 chainPermId (some .black) 3 .anyObject

  -- 4b(i). `mayPlayLand` excludes cast-only permissions (Elven Chorus creature-only library top,
  --        flashback, `withoutManaCost` exile permission):
  let elvenDef : CardDef := {
    name := "P58i4 ElvenPerm"
    types := #[.enchantment]
    staticAbilities := #[
      .ruleModifying none (.play (.mayPlayFrom .you .library (.hasType .creature) false false false false))
    ]
  }
  let dryadArborDef : CardDef := {
    name := "P58i4 DryadArbor"
    types := #[.land, .creature]
    subtypes := #["Forest", "Dryad"]
    power := some (.fixed 1)
    toughness := some (.fixed 1)
  }
  let gLand0 :=
    insertObject
      (insertObject
        (insertObject
          (insertObject (addPermanent g0 elvenDef p0 p0) dryadArborDef p0 (.library p0))
          forest p0 (.graveyard p0))
        forest p0 .exile)
      mountain p0 .exile
  let libLand := (gLand0.objects.find? (·.name == dryadArborDef.name)).get!
  let gyLand := (gLand0.objects.find? (fun o => o.zone == .graveyard p0 && o.name == forest.name)).get!
  let exCastOnlyLand := (gLand0.objects.find? (fun o => o.zone == .exile && o.name == forest.name)).get!
  let exPlayableLand := (gLand0.objects.find? (fun o => o.zone == .exile && o.name == mountain.name)).get!
  let gLand1 :=
    ((gLand0.createEffect (.permission (some p0) (.flashback gyLand.id) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile exCastOnlyLand.id { player := p0, withoutManaCost := true })
        .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile exPlayableLand.id { player := p0 }) .untilEndOfTurn)
        (cause := some testCause)
  let mayPlayLandOk :=
    !gLand1.mayPlayLand p0 libLand &&
    !(gLand1.apply p0 (.playLand libLand.id)).isOk &&
    !gLand1.mayPlayLand p0 gyLand &&
    !(gLand1.apply p0 (.playLand gyLand.id)).isOk &&
    !gLand1.mayPlayLand p0 exCastOnlyLand &&
    !(gLand1.apply p0 (.playLand exCastOnlyLand.id)).isOk &&
    gLand1.mayPlayLand p0 exPlayableLand &&
    (gLand1.apply p0 (.playLand exPlayableLand.id)).isOk

  -- 4b(ii). Remaining non-card guards: `discardNonlandFrom`, `graveyardCardsNamed`,
  --         `Interpreter` `.mayCastExiledElseDamage`, `.reveal` general arm, and `copyAndCast` of a token!
  let nonlandTokDef : CardDef := {
    creature "P58i4 NonlandTok" ManaCost.empty #["Goblin"] 1 1 with
    isToken := true
  }
  let (gNc0, tok1) := g0.createOneToken p1 nonlandTokDef (cause := some testCause)
  let (gNc1, tokHandId) := gNc0.move tok1.id (.hand p1) none (cause := some testCause)
  let gDiscNonland := gNc1.discardNonlandFrom p0 p1
  let gRevealTok :=
    gNc1.applyUnified p1
      { body := .player (.reveal .you (.inZones { zones := #[.hand], owner := .ofPlayer .you } .anyObject) (some (.exact (.const 1)))) } #[]
  let (gGyNc0, tok2) := g0.createOneToken p0 nonlandTokDef (cause := some testCause)
  let (gGyNc1, _) := gGyNc0.move tok2.id (.graveyard p0) none (cause := some testCause)
  let (gExNc0, tok3) := g0.createOneToken p0 nonlandTokDef (cause := some testCause)
  let (gExNc1, _) := gExNc0.move tok3.id .exile none (cause := some testCause)
  let gMayCastElseDmg :=
    gExNc1.applyUnified p0
      { body := .bind ⟨1⟩
          (.stack (.mayCastOrPlay (.inZones .exile (.named (.literal nonlandTokDef.name)))
            { duration := .untilEndOfTurn, landsAllowed := false }))
          (.ifCond (.not (.stepSucceeded ⟨1⟩))
            (.damage (.deal .this (.players (.matching .opponent .any)) (.const 2)))
            .noop) } #[]
  let gCopyCastTok :=
    gExNc0.applyUnified p0
      { body := .moveZone (.inZones .battlefield (.named (.literal nonlandTokDef.name)))
          .exile .exile
          { grantPlayPerm? := some { duration := .untilEndOfTurn, copyAndCast := true, freeCast := true } } } #[]
  let nonCardGuardsOk :=
    (gDiscNonland.player p1).hand.contains tokHandId &&
    gRevealTok.pending == .none &&
    (gGyNc1.graveyardCardsNamed p0 nonlandTokDef.name).isEmpty &&
    gMayCastElseDmg.pending == .none &&
    (gMayCastElseDmg.player p1).life == (gExNc1.player p1).life - 2 &&
    gCopyCastTok.pending == .none

  -- 4b(iii). `defaultChoiceAction` guards for `.extrapolateReveal` (`picks.size < 2`),
  --          `.mayPutMilledPermanent` (departed card), and `.mayTapSourceThen` (already tapped):
  let gDef0 := addPermanent g0 bear p0 p0
  let defBearId := (gDef0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gDefTapped :=
    gDef0.record (GameEvent.tapped gDef0.turnNumber (gDef0.snapshot (gDef0.object! defBearId)) true (cause := testCause))
  let gExtrapIdle :=
    Mtg.Engine.applyIdle
      (g0.change (.pending (.resolutionChoice p0 .extrapolateReveal)))
  let gMillPutIdle :=
    Mtg.Engine.applyIdle
      (g0.change (.pending (.resolutionChoice p0 (.mayPutMilledPermanent #[⟨99992⟩] 1))))
  let gTapThenIdle :=
    Mtg.Engine.applyIdle
      (gDefTapped.change (.pending (.resolutionChoice p0 (.mayTapSourceThen (Effect.gainLife 1).body defBearId))))
  let defaultChoiceOk :=
    gExtrapIdle.pending == .none &&
    gMillPutIdle.pending == .none &&
    gTapThenIdle.pending == .none &&
    (gTapThenIdle.player p0).life == (gDefTapped.player p0).life

  mustHold58i4 "4a_hybridSolver" hybridSolverOk &&
  mustHold58i4 "4a_xAndUnproj" xAndUnprojOk &&
  mustHold58i4 "4a_multiTap" multiTapOk &&
  mustHold58i4 "4a_samePermChain" samePermChainOk &&
  mustHold58i4 "4b_mayPlayLand" mayPlayLandOk &&
  mustHold58i4 "4b_nonCardGuards" nonCardGuardsOk &&
  mustHold58i4 "4b_defaultChoice" defaultChoiceOk &&
  mustHold58i4 "4.replay"
    (replayOk58i4 #[gMana0, gMultiTap, gChainPerm, gLand1, gDiscNonland, gRevealTok,
      gMayCastElseDmg, gCopyCastTok, gExtrapIdle, gMillPutIdle, gTapThenIdle])

end Phase58Item4EventAlignment

end Mtg.Engine.EventTests
