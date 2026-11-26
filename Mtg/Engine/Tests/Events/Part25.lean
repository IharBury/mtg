import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

/-! ### Phase 59 Item 1: `drainProbePausedStep` rollback & `advanceLiveQueueStep` / `.seq a b`
`alreadyOrderedCycle` tail preservation and termination, `isDrainableProbeLeaf` priority-granting
classifiers, `stepCanReverseProposal` `gCur` pop & mana-ability / `.resume*TriggerModesAfterLeave`
reversal parity, `finishActivateManaAbilityPostSac` post-prompt probing & `resumeAfterBecomeCast`
empty-frame cleanup, paused `.crew`/`.costPicks`/`.zemoBoastExile` `needsSacrificeOther` & idle
`followedByFinishChoice` reversal priority, `.restorePending` `sbaPaused` explicit-priority /
`flushUnlessPaysWait` probe parity & `finishScry` behind `.logExpiredPlayFromExile`, and combat
direct-`receivePriority` / `dealAssignedCombatDamage` / `announceCombatDamage` `outerCont?` &
`Actions.Game.apply` `currentInterpWait?` -/
section Phase59Item1EventAlignment

private def mustHold59i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase59Item1EventAlignment failed: {label}"

private def replayOk59i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let leyADef : CardDef := { name := "P59i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P59i1 LeyB", types := #[.enchantment] }
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

  -- 1a. `alreadyOrderedCycle` preserves trailing `.seq` tails in `advanceLiveQueueStep` AND
  --     terminates across all 5 `.seq a b` classifiers (`continuationGrantsPriority`,
  --     `continuationSettlesControlFlow`, `priorityRecipientOfContinuation?`,
  --     `firstContinuationPriorityGrant?`, `hasImplicitPendingPriorityContinuation`).
  let dmgStep : PendingReplacement := .dealDamageToPlayer p0 1 none false (some testCause) false
  let gCyclePrio :=
    (gRep.change (.replacementOrder #[dRidA, dRidB])).changes #[
      .pushContinuationFrame {
        pendingReplacement := some (.seq dmgStep (.receivePriority p2))
      }
    ]
  let gCycleImplicit :=
    (gRep.change (.replacementOrder #[dRidA, dRidB])).changes #[
      .pushContinuationFrame {
        pendingReplacement := some (.seq dmgStep .finishResolutionChoice)
      }
    ]
  let gCycleTailOuter :=
    (gRep.change (.replacementOrder #[dRidA, dRidB])).changes #[
      .pushContinuationFrame {
        pendingReplacement := some (.seq (.seq dmgStep (.receivePriority p1)) (.receivePriority p2))
      }
    ]
  let cycleTailOk :=
    gCyclePrio.anyContinuationGrantsPriority &&
    gCyclePrio.anyContinuationSettlesControlFlow &&
    gCyclePrio.firstContinuationPriorityGrant? == some (some p2) &&
    !gCyclePrio.hasImplicitPendingPriorityContinuation &&
    gCycleImplicit.anyContinuationGrantsPriority &&
    gCycleImplicit.firstContinuationPriorityGrant? == some none &&
    gCycleImplicit.hasImplicitPendingPriorityContinuation &&
    gCycleTailOuter.firstContinuationPriorityGrant? == some (some p1)

  -- 1b. `drainProbePausedStep` rollback on a non-drainable head does NOT leak `defaultReplacementId`
  --     into `replacementOrder`, and `isDrainableProbeLeaf` ahead of a priority grant in
  --     `outerPendingReplacements` does not abort `firstContinuationPriorityGrant?` /
  --     `anyContinuationGrantsPriority` when the drainable leaf pauses on `.chooseReplacement`.
  let gDrainPauseAheadOfOuter :=
    gRep.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some dmgStep
      }
    ]
  let gDrainableQueuesPrio :=
    (gRep.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).changes #[
      .pushContinuationFrame {
        pendingReplacement := some (.seq dmgStep (.receivePriority p2))
      }
    ]
  let gNonDrainablePaused :=
    (gRep.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).changes #[
      .pushContinuationFrame {
        pendingReplacement := some (.seq (.receivePriority p1) (.receivePriority p2))
      }
    ]
  let drainableProbeOk :=
    gDrainPauseAheadOfOuter.anyContinuationGrantsPriority &&
    gDrainPauseAheadOfOuter.firstContinuationPriorityGrant? == some (some p2) &&
    gDrainableQueuesPrio.anyContinuationGrantsPriority &&
    gDrainableQueuesPrio.firstContinuationPriorityGrant? == some (some p2) &&
    gNonDrainablePaused.firstContinuationPriorityGrant? == some (some p1) &&
    gNonDrainablePaused.replacementOrder.isEmpty

  -- 1c. `resumeAfterBecomeCast` respects `g.afterRandom == .none` and pops empty `{}` carrier frames.
  let gEmptyCarrier :=
    g3.changes #[.pushContinuationFrame {}, .pushContinuationFrame {}]
  let gAfterResumeEmpty := gEmptyCarrier.resumeAfterBecomeCast
  let gAfterRandCarrier :=
    g3.changes #[
      .pushContinuationFrame {
        afterRandom := .draw p0 1
        pendingReplacement := some (.logMessage "should-stay-while-afterRandom")
      }
    ]
  let gAfterResumeRand := gAfterRandCarrier.resumeAfterBecomeCast
  let resumeAfterBecomeCastOk :=
    gAfterResumeEmpty.continuations.isEmpty &&
    gAfterResumeRand.pendingReplacement == some (.logMessage "should-stay-while-afterRandom")

  -- 1d. `finishScry`'s `splitLeadingFinishPostCast` splits `.finishPostCast` even when
  --     `emitExpiredPlayFromExileLogs` prepended `.finishPostStep (.logExpiredPlayFromExile ..)` ahead of it,
  --     so `.finishPostCast` runs before `currentInterpWait?`.
  let gScry0 := insertObject (insertObject g3 bear p0 (.library p0)) bear p0 (.library p0)
  let topLibId := (gScry0.player p0).library.back!
  let interpWaitLife : InterpState :=
    { ctx := { controller := p0 }
      queue := #[Instruction.gainLifeFixed 5 .you]
      stack := #[] }
  let gScryPaused :=
    (gScry0.change (.pending (.scry p0 1 1))).changes #[
      .pushContinuationFrame {
        interpWait? := some interpWaitLife
        pendingReplacement :=
          some (.seq (.finishPostStep (.logExpiredPlayFromExile #[] 0))
            (.finishPostCast p0 false false true))
      }
    ]
  let gScryDone := mustApply gScryPaused p0 (.scry #[topLibId] #[])
  let finishScryLogPrefixOk :=
    gScryDone.pending == .none &&
    (gScryDone.player p0).life == (gScry0.player p0).life + 5 &&
    gScryDone.pendingReplacement.isNone &&
    gScryDone.currentInterpWait?.isNone

  -- 1e. `Actions.Game.apply` drains `currentInterpWait?` when idle and does not grant priority
  --     while `afterRandom != .none` or `currentInterpWait?.isSome`.
  let gActWait :=
    (g3.change (.pending (.resolutionChoice p0 .kingpinMayPay2Life))).changes #[
      .pushContinuationFrame {
        interpWait? := some interpWaitLife
      }
    ]
  let gActWaitDone := mustApply gActWait p0 .decline
  let actionsInterpWaitOk :=
    gActWaitDone.pending == .none &&
    gActWaitDone.currentInterpWait?.isNone &&
    (gActWaitDone.player p0).life == (g3.player p0).life + 5

  -- 1f. `probeRestorePendingCore` `flushUnlessPaysWait` parity when `curPopped?.isSome`:
  --     an `.unlessPays` wait with `⟨999⟩` bound behind a non-settling popped outer (`.logMessage`)
  --     that opens a scry prompt on flush settles control flow in both runtime and probe.
  --     Also `.restorePending` when `sbaPaused && followedByExplicitPriority? = some prio`
  --     does not duplicate `.receivePriority` when the continuation already grants priority!
  let unlessWait : InterpState :=
    { ctx := { controller := p0 }
      queue := #[]
      stack := #[.unlessPays p0 (Instruction.scry (.const 1) .you)] }
  let gFlushProbe :=
    gScry0.changes #[
      .pushContinuationFrame {
        stepEnv := #[(⟨999⟩, { succeeded := false })]
        interpWait? := some unlessWait
        outerPendingReplacements := #[.logMessage "after-restore"]
        pendingReplacement := some (.restorePending .none true)
      }
    ]
  let gFlushRuntime := gFlushProbe.drainPendingContinuations
  let gRestorePrioDedup :=
    (gRep.changes #[
      .pending (.chooseReplacement p0 #[dRidA, dRidB]),
      .pushContinuationFrame {
        pendingReplacement := some (.receivePriority p2)
      }
    ]).resumePendingReplacement
      (.seq (.restorePending (.chooseReplacement p0 #[dRidA, dRidB]) false) (.receivePriority p1))
  let restoreFlushParityOk :=
    gFlushProbe.anyContinuationSettlesControlFlow &&
    (match gFlushRuntime.pending with | .scry q 1 _ => q == p0 | _ => false) &&
    gRestorePrioDedup.firstContinuationPriorityGrant? == some (some p2)

  -- 1g. Combat `declareAttackers` drains queued continuations via `finishAndGrantPriorityFwd`,
  --     `dealAssignedCombatDamage` with a `.chooseReplacement` pause does not duplicate
  --     `.receivePriority` when `anyContinuationSettlesControlFlowFwd` holds.
  let gAtkStep :=
    (g3.record (GameEvent.stepBegan g3.turnNumber .declareAttackers p0)).changes #[
      .pending .declareAttackers,
      .pushContinuationFrame {
        pendingReplacement := some (.logMessage "combat-queued-log")
      }
    ]
  let gAtkDone := mustApply gAtkStep p0 (.declareAttackers #[])
  let gCbt0 := addPermanent (addPermanent gRep0 bear p0 p0) hero p1 p1
  let cbtBearId := (gCbt0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let cbtBlkId := (gCbt0.permanentsOf p1).find? (·.name == hero.name) |>.get!.id
  let cbtRidB : ReplacementId := { kind := .multiplyDamage, object := some qLeyB }
  let gCbt1 :=
    ((((gCbt0.recordPutCounters cbtBlkId .shield 1 (byPlayer := some p1) (cause := some testCause)).createEffect
      (.replacement {
        id := cbtRidB, source := some qLeyB, controller := some p0, affectedPlayer := p1,
        kind := .multiplyDamage none 2 }) (cause := some testCause)).record
      (GameEvent.stepBegan gCbt0.turnNumber .combatDamage p0)).record
      (GameEvent.becameAttacking gCbt0.turnNumber (gCbt0.snapshot (gCbt0.object! cbtBearId))
        (.player p1) (.turnBased .declareAttackers))).record
      (GameEvent.combatDamageAssigned gCbt0.turnNumber true
        #[{ source := cbtBearId, toCreatures := #[(cbtBlkId, 2)], toPlayer := 0 }])
  let gCbtAssigned := gCbt1.dealAssignedCombatDamage 0 (outerCont? := some (.receivePriority p2))
  let combatDrainOk :=
    gAtkDone.pending == .none &&
    gAtkDone.pendingReplacement.isNone &&
    gAtkDone.log.contains "combat-queued-log" &&
    (match gCbtAssigned.pending with | .chooseReplacement .. => true | _ => false) &&
    gCbtAssigned.firstContinuationPriorityGrant? == some (some p2)

  -- 1h. Idle `followedByFinishChoice && !g.sbaPaused` proposal reversal by a non-active caster
  --     stashes `pendingPriority` so `finishResolutionChoice` grants priority to the non-active caster.
  let nonActiveSpell : CardDef := {
    name := "P59i1 NonActiveInstant"
    manaCost := { symbols := #[.colored .blue] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gNonAct0 :=
    insertObject (g3.change (.priority p1)) nonActiveSpell p1 (.hand p1)
  let naHandId := (gNonAct0.player p1).hand.back!
  let gNonActProp := mustApply gNonAct0 p1 (.cast naHandId)
  let gNonActRev :=
    gNonActProp.reverseProposedSpell (resumeContinuation := true) (followedByFinishChoice := true)
  let nonActiveRevPrioOk :=
    gNonActRev.proposedSpell.isNone &&
    gNonActRev.pending == .none &&
    gNonActRev.priority == p1

  -- 1i. `stepCanReverseProposal` pops `gCur` on `.restorePending _ true` and includes
  --     `.resume*TriggerModesAfterLeave` + nested mana-ability post-steps (`prevPending != .none`)
  --     so a `.seq` tail is dropped on reversal, AND `finishActivateManaAbilityPostSac` uses
  --     post-prompt continuation probing when `!g.sbaPaused`.
  let gRevSeq0 := mustApply gNonAct0 p1 (.cast naHandId)
  let gRevSeqTrig :=
    gRevSeq0.resumePendingReplacement
      (.seq (.finishPostStep (.resumeTriggerModesAfterLeave p1 ⟨99991⟩ 1 #[]))
        (.logMessage "should-drop-on-reversal"))
  let gRevRestorePop :=
    (gRevSeq0.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.logMessage "outer-to-pop"]
        pendingReplacement := some (.seq (.restorePending .none true)
          (.seq (.finishPostStep (.resumeTriggerModesAfterLeave p1 ⟨99991⟩ 1 #[]))
            (.logMessage "should-not-leak-after-pop")))
      }
    ]).drainPendingContinuations
  let leyASnap := gRep.snapshot (gRep.object! qLeyA)
  let gPostSacPrompt :=
    (g3.changes #[
      .pending (.resolutionChoice p0 .kingpinMayPay2Life),
      .pushContinuationFrame {
        pendingReplacement := some (.receivePriority p2)
      }
    ]).finishActivateManaAbilityPostSac p0 qLeyA leyADef.name leyASnap #[] false (some 0) none 0 false .none
  let gPostSacImplicit :=
    (g3.changes #[
      .pending (.resolutionChoice p1 .kingpinMayPay2Life),
      .pushContinuationFrame {
        pendingReplacement := some .finishResolutionChoice
      }
    ]).finishActivateManaAbilityPostSac p1 qLeyA leyADef.name leyASnap #[] false (some 0) none 0 false .none
  let revAndPostSacOk :=
    (gRevSeqTrig.proposedSpell.isSome || !gRevSeqTrig.log.contains "should-drop-on-reversal") &&
    !gRevRestorePop.log.contains "should-not-leak-after-pop" &&
    gPostSacPrompt.pendingReplacement.isNone &&
    gPostSacPrompt.outerPendingReplacements == #[.receivePriority p2] &&
    gPostSacImplicit.pendingPriority == some p1

  mustHold59i1 "1a_cycleTail" cycleTailOk &&
  mustHold59i1 "1b_drainableProbe" drainableProbeOk &&
  mustHold59i1 "1c_resumeAfterBecomeCast" resumeAfterBecomeCastOk &&
  mustHold59i1 "1d_finishScryLogPrefix" finishScryLogPrefixOk &&
  mustHold59i1 "1e_actionsInterpWait" actionsInterpWaitOk &&
  mustHold59i1 "1f_restoreFlushParity" restoreFlushParityOk &&
  mustHold59i1 "1g_combatDrain" combatDrainOk &&
  mustHold59i1 "1h_nonActiveRevPrio" nonActiveRevPrioOk &&
  mustHold59i1 "1i_revAndPostSac" revAndPostSacOk &&
  mustHold59i1 "1.replay"
    (replayOk59i1 #[gCyclePrio, gCycleImplicit, gCycleTailOuter, gDrainPauseAheadOfOuter,
      gDrainableQueuesPrio, gNonDrainablePaused, gAfterResumeEmpty, gAfterResumeRand,
      gScryDone, gActWaitDone, gFlushRuntime, gRestorePrioDedup, gAtkDone, gCbtAssigned,
      gNonActRev, gRevSeqTrig, gRevRestorePop, gPostSacPrompt])

end Phase59Item1EventAlignment

/-! ### Phase 59 Item 2: `emitExpiredPlayFromExileLogs` / `hasQueuedPfeEmitterAfter` `interpWait?`
& `afterRandom`, `isPlayFromExileDeferBoundaryLeaf` & `.checkSBA`, `hasPlayFromExileLoggedInSlice`
singleton-match `ambigEvents` retention, `expireEffectById`/`expireMatching` deferral,
`execCounterOpStep` `.moveAll`/`.moveOne` pause preservation, `markDamageOn` unpreventable-shield
departure & simultaneous damage deferral, non-untap-step `untapPermanentsLoop` / `.setTapped` &
cost `recordRemoveCounters` pauses, and remaining multi-object move loops -/
section Phase59Item2EventAlignment

private def mustHold59i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase59Item2EventAlignment failed: {label}"

private def replayOk59i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand afterDraw p0

  -- 2a. `isPlayFromExileDeferBoundaryLeaf` includes `.checkSBA`, non-batch `.continueInterpreter`,
  --     `.shuffleThen`, `.finishBeginRecruit`, `.finishAbilityResolution`, etc.; AND
  --     `emitExpiredPlayFromExileLogs` halts before `outerPendingReplacements` when `interpWait?`
  --     or `afterRandom` is active on the top frame!
  let nonBatchWait : InterpState :=
    { ctx := { controller := p0 }, queue := #[Instruction.gainLifeFixed 1 .you], stack := #[] }
  let batchLoopWait : InterpState :=
    { ctx := { controller := p0 }, queue := #[], stack := #[.afterCounterOpLoop #[] (.put .plusOnePlusOne (.const 1)) testCause none] }
  let gEx0 := insertObject (insertObject g0 bear p0 .exile) bear p0 .exile
  let exBears := gEx0.objects.filter (fun o => o.zone == .exile && o.name == bear.name)
  let exIdA := exBears[0]!.id
  let exIdB := exBears[1]!.id
  let gExPerms :=
    (gEx0.createEffect (.permission (some p0) (.playFromExile exIdA { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile exIdB { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let gPfeInterpBase :=
    (gExPerms.createEffect (.permission (some p0) (.playFromExile exIdA { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).changes #[
      .pushContinuationFrame {
        interpWait? := some nonBatchWait
        outerPendingReplacements := #[.logMessage "outer-after-interp"]
      }
    ]
  let effIdAFirst := (gPfeInterpBase.activeEffects.find? (fun (_, s) =>
    match s with | .permission _ (.playFromExile oid _) _ => oid == exIdA | _ => false)).get!.1
  let pfeStartIdx := gPfeInterpBase.events.size
  let gPfeInterpMid := gPfeInterpBase.expireEffectById effIdAFirst (deferPlayFromExileLogs := true)
  let gPfeInterpExp := Game.emitExpiredPlayFromExileLogs gPfeInterpBase gPfeInterpMid pfeStartIdx
  let boundaryLeavesOk :=
    (PendingReplacement.checkSBA none).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.continueInterpreter nonBatchWait).isPlayFromExileDeferBoundaryLeaf &&
    !(PendingReplacement.continueInterpreter batchLoopWait).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.shuffleThen p0 .none).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.finishBeginRecruit p0).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.finishPostStep (.finishAbilityResolution {} p0 none none none false)).isPlayFromExileDeferBoundaryLeaf &&
    gPfeInterpExp.outerPendingReplacements == #[PendingReplacement.logMessage "outer-after-interp"] &&
    gPfeInterpExp.pendingReplacement.isSome

  -- 2b. `expireEffectById` emits `.playFromExile` expiry log when `deferPlayFromExileLogs == false`,
  --     and `expireMatching` defers across multiple expiring effects and logs once at end.
  let effIdA := (gExPerms.activeEffects.find? (fun (_, s) =>
    match s with | .permission _ (.playFromExile oid _) _ => oid == exIdA | _ => false)).get!.1
  let gExpOne := gExPerms.expireEffectById effIdA (deferPlayFromExileLogs := false)
  let gExpBoth := gExPerms.expireMatching (fun s =>
    match s with | .permission _ (.playFromExile _ _) _ => true | _ => false)
  let logCount (g : Game) : Nat :=
    (g.log.filter (· == s!"{bear.name} can no longer be played from exile")).size
  let expirePfeOk :=
    logCount gExpOne == 1 &&
    logCount gExpBoth == 2

  -- 2c. `hasPlayFromExileLoggedInSlice` singleton-match `ambigEvents` retention:
  --     two same-named exiled cards `A, B`: Log #1 ambiguous `(true, #[A, B])`, then `B` temporarily
  --     regains `mayCastExiledBySource` (Null Summoner phases in), Log #2 singleton `#[A]` resolves
  --     `B` as already logged from Log #1 so when Null Summoner phases back out, calling
  --     `emitExpiredPlayFromExileLogs` from `startIdx2c` does NOT emit a duplicate 3rd log!
  let g2cBase0 := addPermanent gExPerms Catalog.nullSummoner p0 p0
  let nsId := (g2cBase0.permanentsOf p0).find? (·.name == Catalog.nullSummoner.name) |>.get!.id
  let g2cBase :=
    (g2cBase0.changeObject exIdB (.exiledBy (some nsId))).record
      (GameEvent.phasedOut g2cBase0.turnNumber (g2cBase0.snapshot (g2cBase0.object! nsId)) (cause := testCause))
  let startIdx2c := g2cBase.events.size
  let g2c1 :=
    (g2cBase.expireMatching (fun s =>
      match s with | .permission _ (.playFromExile _ _) _ => true | _ => false)
      (deferPlayFromExileLogs := true)).logMsg s!"{bear.name} can no longer be played from exile"
  let g2c2 :=
    (g2c1.record (GameEvent.phasedIn g2c1.turnNumber (g2c1.snapshot (g2c1.object! nsId)) (cause := testCause))).logMsg
      s!"{bear.name} can no longer be played from exile"
  let g2c3 :=
    g2c2.record (GameEvent.phasedOut g2c2.turnNumber (g2c2.snapshot (g2c2.object! nsId)) (cause := testCause))
  let g2cEmit := Game.emitExpiredPlayFromExileLogs g2cBase g2c3 startIdx2c
  let ambigRetentionOk :=
    logCount g2cEmit == 2

  -- 2d. `Damage.markDamageOn` unpreventable damage on a creature with a `.shield` counter
  --     does not panic and respects `deferPlayFromExileLogs`.
  let gSh0 := addPermanent g0 bear p0 p0
  let shBearId := (gSh0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gSh1 := gSh0.recordPutCounters shBearId .shield 1 (byPlayer := some p0) (cause := some testCause)
  let gShDmg :=
    gSh1.markDamageOn (gSh1.object! shBearId) 2 s!"{bear.name} takes 2 damage"
      (unpreventable := true) (cause := some testCause) (deferPlayFromExileLogs := true)
  let markDamageShieldOk :=
    (gShDmg.object! shBearId).status.damage == 2 &&
    (gShDmg.object! shBearId).status.shield == 0

  -- 2e. `Interpreter.execCounterOpStep` `.moveAll` preserves ALL removed counters across
  --     an actual CR 616.1 replacement pause via `InterpCont.afterMoveCountersPut`!
  let gMovC0 := addPermanent (addPermanent g0 bear p0 p0) hero p0 p0
  let srcCId := (gMovC0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let dstCId := (gMovC0.permanentsOf p0).find? (·.name == hero.name) |>.get!.id
  let cRepA : ReplacementId := { kind := .addCountersPut, object := some srcCId }
  let cRepB : ReplacementId := { kind := .multiplyCountersPut, object := some dstCId }
  let gMovC1 :=
    (gMovC0.recordPutCounters srcCId .plusOnePlusOne 2 (byPlayer := some p0) (cause := some testCause)).recordPutCounters
      srcCId .flying 1 (byPlayer := some p0) (cause := some testCause)
  let gMovCRep :=
    (gMovC1.createEffect
      (.replacement {
        id := cRepA, source := some srcCId, controller := some p0, affectedPlayer := p0,
        kind := .modifyCountersPut (some dstCId) (some .plusOnePlusOne) 1 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := cRepB, source := some dstCId, controller := some p0, affectedPlayer := p0,
        kind := .modifyCountersPut (some dstCId) (some .plusOnePlusOne) 0 2 }) (cause := some testCause)
  let gMovCPaused :=
    gMovCRep.applyUnified p0
      { targets := TargetSpec.append TargetSpec.creature TargetSpec.creature
        body := .permanent (.modifyCounters (.moveAll (.target 0)) (.target 1)) }
      #[.permanent srcCId, .permanent dstCId]
  let gMovCDone :=
    match gMovCPaused.pending with
    | .chooseReplacement q choices =>
      let gStep1 := mustApply gMovCPaused q (.chooseReplacement choices[0]!)
      gStep1.drainPendingContinuations
    | _ => gMovCPaused
  let moveCountersOk :=
    (match gMovCPaused.pending with | .chooseReplacement .. => true | _ => false) &&
    gMovCDone.pending == .none &&
    (gMovCDone.object! srcCId).status.plusOnePlusOne == 0 &&
    (gMovCDone.object! srcCId).status.counterCount .flying == 0 &&
    (gMovCDone.object! dstCId).status.plusOnePlusOne > 2 &&
    (gMovCDone.object! dstCId).status.counterCount .flying == 1

  -- 2f. Non-untap-step simultaneous untaps (`Pumps.untapPermanentsLoop` & `Interpreter` `.setTapped false`)
  --     handle stun counters & defer `.playFromExile` logs across the batch.
  let gUnt0 := addPermanent (addPermanent g0 bear p0 p0) hero p0 p0
  let u1 := (gUnt0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let u2 := (gUnt0.permanentsOf p0).find? (·.name == hero.name) |>.get!.id
  let gUnt1 :=
    (((gUnt0.record (GameEvent.tapped gUnt0.turnNumber (gUnt0.snapshot (gUnt0.object! u1)) true (cause := testCause))).record
      (GameEvent.tapped gUnt0.turnNumber (gUnt0.snapshot (gUnt0.object! u2)) true (cause := testCause))).recordPutCounters
        u1 .stun 1 (byPlayer := some p0) (cause := some testCause))
  let gUntDone := gUnt1.untapPermanentsLoop #[u1, u2] (cause := some testCause) (logged := true)
  let gUntInterp :=
    gUnt1.applyUnified p0
      { body := .permanent (.setTapped (.inZones .battlefield (.hasType .creature)) false) } #[]
  let untapLoopOk :=
    (gUntDone.object! u1).status.tapped &&
    (gUntDone.object! u1).status.stun == 0 &&
    !(gUntDone.object! u2).status.tapped &&
    (gUntInterp.object! u1).status.tapped &&
    (gUntInterp.object! u1).status.stun == 0 &&
    !(gUntInterp.object! u2).status.tapped

  -- 2g. `Actions.returnOwnedCreaturesScheduleBirds` runs via pause-safe `returnOwnedCreaturesLoop`,
  --     `Choices.exileCardsLoop` & `ResolutionEffects.millOpponentsOnly` execute cleanly.
  let gEagles := gUnt0.returnOwnedCreaturesScheduleBirds p0 #[u1, u2]
  let gMillOpps :=
    (insertObject g0 bear p1 (.library p1)).millOpponentsOnly #[p1] 1 (some testCause)
  let gExLoop := gUnt0.exileCardsLoop #[u1, u2] (cause := some testCause)
  let multiLoopsOk :=
    gEagles.delayedTriggers.any (fun dt => match dt.kind with | .eaglesBirds 2 => true | _ => false) &&
    (gEagles.player p0).hand.size == 2 &&
    (gMillOpps.player p1).graveyard.size == 1 &&
    (gExLoop.objects.filter (fun o => o.zone == .exile)).size == 2

  mustHold59i2 "2a_boundaryLeaves" boundaryLeavesOk &&
  mustHold59i2 "2b_expirePfe" expirePfeOk &&
  mustHold59i2 "2c_ambigRetention" ambigRetentionOk &&
  mustHold59i2 "2d_markDamageShield" markDamageShieldOk &&
  mustHold59i2 "2e_moveCounters" moveCountersOk &&
  mustHold59i2 "2f_untapLoop" untapLoopOk &&
  mustHold59i2 "2g_multiLoops" multiLoopsOk &&
  mustHold59i2 "2.replay"
    (replayOk59i2 #[gPfeInterpExp, gExpOne, gExpBoth, g2cEmit, gShDmg, gMovCDone,
      gUntDone, gUntInterp, gEagles, gMillOpps, gExLoop])

end Phase59Item2EventAlignment

/-! ### Phase 59 Item 3: Layer 4–6 self-static `retainsBase` / `ownUncondDelta` /
`splitGrantedDeltas`, CR 305.7 static `hasActiveBasicLandSetEffect`, peer attached-host
`hasKwDepAttStatic`, non-battlefield Layer 6, expanded `Exalted`/`Decayed`/`Myriad`/`Undying`
& cumulative `.exalted` counters, Layer-6 Improvise, Layer-4 `.addAllCreatureTypes` & removals,
`HistGlobalState`/`mkHistoricalGameAt`/`mkHistoricalGameForObjAt` & `wasPreparedAtDeparture?`,
non-self `.lifeCantChange` expiry, temporary `PlayerRule.hexproof`, deduplicated protection
`ReplacementId`s, `.fromStep`/`.hexproof` source-bound & `playerProtectionRuleMatches` `you`,
face-down non-battlefield/non-stack unmasked `copiableValues`, Layer-6 spell cost mods &
single-pass Layer-3 `TextChange`, and cross-controller / nested `.nthResolutionThisTurn` -/
section Phase59Item3EventAlignment

private def mustHold59i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase59Item3EventAlignment failed: {label}"

private def replayOk59i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand afterDraw p0

  -- 3a. Self-static on a permanent entering AFTER Humility/Dress Down (`.abilities {} .all`)
  --     is suppressed (`retainsBase` respected in `evalStaticsFast` & `evalLayer6Aux`);
  --     earlier `.loseIndestructible` vs later printed self-static `.indestructible` respects timestamp;
  --     and `splitGrantedDeltas` does NOT keep a granted keyword-dependent static alive after `rem == .all`!
  let selfIndestDef : CardDef := {
    creature "P59i3 SelfIndest" ManaCost.zero #["Bear"] 2 2 with
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .sameAs .this } (.grantKeywords #[Keyword.indestructible])
    ]
  }
  let gDressDown0 :=
    g0.createEffect (.layered (.creaturesControlledBy p0) (.abilities {} .all) .untilEndOfTurn) (cause := some testCause)
  let gDressDown1 := addPermanent gDressDown0 selfIndestDef p0 p0
  let ddId := (gDressDown1.permanentsOf p0).find? (·.name == selfIndestDef.name) |>.get!.id
  let gTsSelf0 :=
    g0.createEffect (.layered (.creaturesControlledBy p0) (.abilities {} .loseIndestructible) .untilEndOfTurn)
      (cause := some testCause)
  let gTsSelf1 := addPermanent gTsSelf0 selfIndestDef p0 p0
  let tsSelfId := (gTsSelf1.permanentsOf p0).find? (·.name == selfIndestDef.name) |>.get!.id
  let gSplit0 := addPermanent g0 bear p0 p0
  let spId := (gSplit0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let grantedKwDepStatic : StaticAbility :=
    .continuous (some (.exists (.filter .this (.hasKeyword .flying))))
      { zones := .battlefield, pred := .sameAs .this } (.grantKeywords #[Keyword.vigilance])
  let gSplit1 :=
    ((gSplit0.createEffect
      (.layered (.objects #[spId]) (.abilities { staticAbilities := #[grantedKwDepStatic] } .none) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[spId]) (.abilities {} .all) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[spId]) (.abilities { keywords := #[Keyword.flying] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let selfStaticRetainsBaseOk :=
    !(gDressDown1.currentKeywords (gDressDown1.object! ddId)).contains Keyword.indestructible &&
    (gTsSelf1.currentKeywords (gTsSelf1.object! tsSelfId)).contains Keyword.indestructible &&
    (gSplit1.currentKeywords (gSplit1.object! spId)).contains Keyword.flying &&
    !(gSplit1.currentKeywords (gSplit1.object! spId)).contains Keyword.vigilance

  -- 3b. CR 305.7 static `.modifyTypes .set #[.island]` on an attached Aura sets
  --     `hasActiveBasicLandSetEffect` and strips the land's printed abilities;
  --     AND peer attached-host keyword-dependent static (`hasKwDepAttStatic`) works across `P != o`!
  let specialLandDef : CardDef := {
    name := "P59i3 SpecialLand"
    types := #[.land]
    keywords := #[Keyword.indestructible]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixed #[.colored .green])]
  }
  let spreadSeasDef : CardDef := {
    name := "P59i3 SpreadingSeas"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[
      .continuous none StaticAbility.scopeEnchantedPermanent
        (.modifyTypes { mode := .set, subtypes := #[.island] })
    ]
  }
  let gSeas0 := addPermanent (addPermanent g0 specialLandDef p0 p0) spreadSeasDef p0 p0
  let slId := (gSeas0.permanentsOf p0).find? (·.name == specialLandDef.name) |>.get!.id
  let auraId := (gSeas0.permanentsOf p0).find? (·.name == spreadSeasDef.name) |>.get!.id
  let gSeas1 :=
    gSeas0.record (GameEvent.attached gSeas0.turnNumber (gSeas0.snapshot (gSeas0.object! auraId)) slId (cause := testCause))
  let peerAuraDef : CardDef := {
    name := "P59i3 PeerKwAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[
      .continuous (some (.exists (.filter .attachedHost (.hasKeyword .flying))))
        { zones := .battlefield, pred := .all #[.controlledBy .you, .hasType .creature] }
        (.grantKeywords #[Keyword.trample])
    ]
  }
  let gPeer0 := addPermanent (addPermanent (addPermanent g0 bear p0 p0) hero p0 p0) peerAuraDef p0 p0
  let peerHostId := (gPeer0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let peerOtherId := (gPeer0.permanentsOf p0).find? (·.name == hero.name) |>.get!.id
  let peerAuraId := (gPeer0.permanentsOf p0).find? (·.name == peerAuraDef.name) |>.get!.id
  let gPeer1 :=
    (gPeer0.record (GameEvent.attached gPeer0.turnNumber (gPeer0.snapshot (gPeer0.object! peerAuraId)) peerHostId (cause := testCause))).createEffect
      (.layered (.objects #[peerHostId]) (.abilities { keywords := #[Keyword.flying] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let cr3057AndPeerOk :=
    gSeas1.hasActiveBasicLandSetEffect &&
    !(gSeas1.currentKeywords (gSeas1.object! slId)).contains Keyword.indestructible &&
    (gSeas1.subtypes (gSeas1.object! slId)).contains .island &&
    (gPeer1.currentKeywords (gPeer1.object! peerOtherId)).contains Keyword.trample

  -- 3c. Non-battlefield Layer 6 static grants a keyword to a card in hand, and
  --     expanded `Exalted`/`Decayed`/`Myriad`/`Undying` triggers + cumulative `.exalted` counters work!
  let handFlashLord : CardDef := {
    name := "P59i3 HandFlash"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.hand], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[Keyword.flash])
    ]
  }
  let gNonBf := insertObject (addPermanent g0 handFlashLord p0 p0) bear p0 (.hand p0)
  let handBear := gNonBf.object! (gNonBf.player p0).hand.back!
  let exaBearDef : CardDef := {
    creature "P59i3 ExaltedBear" ManaCost.zero #["Bear"] 2 2 with
    keywords := #[Keyword.exalted, Keyword.undying]
  }
  let gExa0 := addPermanent g0 exaBearDef p0 p0
  let exaId := (gExa0.permanentsOf p0).find? (·.name == exaBearDef.name) |>.get!.id
  let gExa2 := gExa0.recordPutCounters exaId .exalted 2 (byPlayer := some p0) (cause := some testCause)
  let nonBfAndKeywordExpandOk :=
    (gNonBf.currentKeywords handBear).contains Keyword.flash &&
    ((gExa2.currentKeywords (gExa2.object! exaId)).filter (· == Keyword.exalted)).size == 3 &&
    (gExa2.triggeredAbilities (gExa2.object! exaId)).size ≥ 4

  -- 3d. Layer-6 Improvise (`Pumps.spellHasImprovise`) & Layer-4 `.addAllCreatureTypes` +
  --     `removeSubtypes`/`removeSupertypes`/`removeColors`:
  let impGrantDef : CardDef := {
    name := "P59i3 ImpGrant"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .controlledBy .you }
        (.grantKeywords #[Keyword.improvise])
    ]
  }
  let plainInstant : CardDef := {
    name := "P59i3 PlainInst"
    manaCost := ManaCost.ofGeneric 2
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gImp0 := insertObject (addPermanent g0 impGrantDef p0 p0) plainInstant p0 .stack
  let impStackObj := (gImp0.objects.filter (fun o => o.zone == .stack)).back!
  let legRedBearDef : CardDef := {
    creature "P59i3 LegRedBear" { symbols := #[.colored .red] } #["Bear"] 2 2 with
    supertypes := #[.legendary]
  }
  let gAllTypes0 := addPermanent g0 legRedBearDef p0 p0
  let atBearId := (gAllTypes0.permanentsOf p0).find? (·.name == legRedBearDef.name) |>.get!.id
  let gAllTypes1 :=
    gAllTypes0.applyUnified p0
      { targets := TargetSpec.creature
        body := .seq #[
          .installEffect (.applyContinuous .untilEndOfTurn (.target 0) .addAllCreatureTypes),
          .installEffect (.applyContinuous .untilEndOfTurn (.target 0)
            (.modifyTypes { mode := .add, removeSubtypes := #[.goblin], removeSupertypes := #[.legendary] })),
          .installEffect (.applyContinuous .untilEndOfTurn (.target 0)
            (.modifyColors { mode := .add, removeColors := ColorSet.ofList [.red] }))
        ] }
      #[.permanent atBearId]
  let improviseAndAllTypesOk :=
    gImp0.spellHasImprovise (gImp0.baseCard impStackObj) p0 (spellObj? := some impStackObj) &&
    (gAllTypes1.subtypes (gAllTypes1.object! atBearId)).contains .wizard &&
    !(gAllTypes1.subtypes (gAllTypes1.object! atBearId)).contains .goblin &&
    !(gAllTypes1.supertypes (gAllTypes1.object! atBearId)).contains .legendary &&
    !(gAllTypes1.colors (gAllTypes1.object! atBearId)).contains .red &&
    !(gAllTypes1.currentKeywords (gAllTypes1.object! atBearId)).contains Keyword.changeling

  -- 3e. Non-self `.lifeCantChange` expiry on `q'`'s turn, temporary `PlayerRule.hexproof`,
  --     and `Damage.replaceDamage` deduplicated `ReplacementId`s:
  let gLifeRule0 :=
    g0.createEffect (.playerRule p1 .lifeCantChange (.untilNextTurnOf p0)) (cause := some testCause)
  let gLifeRuleExp := gLifeRule0.expireUntilTurnCommandEffects p0
  let gHex0 :=
    g0.applyUnified p0
      { body := .installEffect (.applyRule .untilEndOfTurn (.player (.hexproof .you none))) } #[]
  let redSrcDef : CardDef := creature "P59i3 RedSrc" { symbols := #[.colored .red] } #["Goblin"] 2 2
  let gProtDup0 := addPermanent g0 redSrcDef p1 p1
  let redSrcId := (gProtDup0.permanentsOf p1).find? (·.name == redSrcDef.name) |>.get!.id
  let gProtDup :=
    (gProtDup0.createEffect (.playerRule p0 (.protectionFrom (.color (.literal .red)) (some atBearId) (some p0)) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.playerRule p0 (.protectionFrom (.color (.literal .red)) (some atBearId) (some p0)) .untilEndOfTurn)
      (cause := some testCause)
  let protDmgRes :=
    gProtDup.replaceDamage 3 (src? := some (gProtDup.object! redSrcId)) (recipientPlayer? := some p0)
  let rulesAndProtOk :=
    gLifeRuleExp.activeEffects.all (fun (_, s) =>
      match s with | .playerRule _ .lifeCantChange _ => false | _ => true) &&
    gHex0.playerHasHexproof p0 &&
    !gHex0.playerHasHexproof p1 &&
    protDmgRes.amount == 0 &&
    protDmgRes.choice?.isNone

  -- 3f. Face-down exiled card is NOT masked as a 2/2 creature by `copiableValues` (CR 708.2 applies
  --     only on `.battlefield`/`.stack`), while battlefield face-down IS masked as 2/2;
  --     AND Layer-6 granted Affinity reduces spell cost + non-idempotent Layer-3 `TextChange` applies once!
  let gFdEx0 := insertObject g0 forest p0 .exile
  let fdExId := (gFdEx0.objects.find? (fun o => o.zone == .exile && o.name == forest.name)).get!.id
  let gFdEx := gFdEx0.record (GameEvent.turnedFaceDown gFdEx0.turnNumber (gFdEx0.snapshot (gFdEx0.object! fdExId)) (cause := testCause))
  let gFdBf0 := addPermanent g0 forest p0 p0
  let fdBfId := (gFdBf0.permanentsOf p0).find? (·.name == forest.name) |>.get!.id
  let gFdBf := gFdBf0.record (GameEvent.turnedFaceDown gFdBf0.turnNumber (gFdBf0.snapshot (gFdBf0.object! fdBfId)) (cause := testCause))
  let affGrantDef : CardDef := {
    name := "P59i3 AffGrant", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .hasType .instant }
        (.grantKeywords #[.affinity { zones := .battlefield, pred := .all #[.controlledBy .you, .hasType .artifact] }])
    ]
  }
  let artDef : CardDef := { name := "P59i3 Art1", types := #[.artifact] }
  let gAff0 := insertObject (addPermanent (addPermanent g0 affGrantDef p0 p0) artDef p0 p0) plainInstant p0 (.hand p0)
  let affHandObj := gAff0.object! (gAff0.player p0).hand.back!
  -- Chained non-idempotent Layer 3 TextChange:
  -- Order 1: Goblin -> Elf, then Elf -> Zombie => single-pass turns Goblin -> Zombie (Elf does NOT reduce cost: {2}).
  -- Order 2: Elf -> Zombie, then Goblin -> Elf => single-pass turns Goblin -> Elf (Elf reduces cost to {1};
  --          a buggy double-pass would turn Elf -> Zombie on pass 2 and leave cost at {2}!).
  let gobAffSpell : CardDef := {
    name := "P59i3 GobAff"
    manaCost := ManaCost.ofGeneric 2
    types := #[.instant]
    keywords := #[.affinity { zones := .battlefield, pred := .all #[.controlledBy .you, .hasSubtype (.literal .goblin)] }]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let elfPermDef : CardDef := creature "P59i3 ElfPerm" ManaCost.zero #["Elf"] 1 1
  let gTc0 := insertObject (addPermanent g0 elfPermDef p0 p0) gobAffSpell p0 (.hand p0)
  let tcHandId := (gTc0.player p0).hand.back!
  let gTc1 :=
    (gTc0.createEffect (.layered (.objects #[tcHandId]) (.text (.replaceCreatureType .goblin .elf)) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[tcHandId]) (.text (.replaceCreatureType .elf .zombie)) .untilEndOfTurn)
      (cause := some testCause)
  let gTcOrder :=
    (gTc0.createEffect (.layered (.objects #[tcHandId]) (.text (.replaceCreatureType .elf .zombie)) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[tcHandId]) (.text (.replaceCreatureType .goblin .elf)) .untilEndOfTurn)
      (cause := some testCause)
  let tcOrderObj := gTcOrder.object! tcHandId
  let faceDownAndLayer36Ok :=
    gFdEx.isLand (gFdEx.object! fdExId) &&
    gFdEx.name (gFdEx.object! fdExId) == forest.name &&
    !gFdBf.isLand (gFdBf.object! fdBfId) &&
    gFdBf.isCreature (gFdBf.object! fdBfId) &&
    gAff0.playManaCost { affHandObj with controller := some p0 } (gAff0.baseCard affHandObj) == ManaCost.ofGeneric 1 &&
    gTc1.playManaCost { gTc1.object! tcHandId with controller := some p0 } (gTc1.baseCard (gTc1.object! tcHandId)) == ManaCost.ofGeneric 2 &&
    gTcOrder.playManaCost { tcOrderObj with controller := some p0 } (gTcOrder.baseCard tcOrderObj) == ManaCost.ofGeneric 1

  -- 3g. `HistGlobalState` / `mkHistoricalGameAt` preserves `faceDown`, `tapped`, `isNight`, `isMonarch`:
  let gHist0 := addPermanent g0 bear p0 p0
  let hBearId := (gHist0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let histIdx := gHist0.events.size
  let gHist1 :=
    (((gHist0.record (GameEvent.tapped gHist0.turnNumber (gHist0.snapshot (gHist0.object! hBearId)) true (cause := testCause))).record
      (GameEvent.turnedFaceDown gHist0.turnNumber (gHist0.snapshot (gHist0.object! hBearId)) (cause := testCause))).record
      (GameEvent.rules gHist0.turnNumber (.turn (.dayNightChanged true)) testCause)).record
      (GameEvent.becameMonarch gHist0.turnNumber p0 (cause := some testCause))
  let gHistBack := gHist1.mkHistoricalGameAt histIdx
  let histReplayOk :=
    !(gHistBack.object! hBearId).status.tapped &&
    !(gHistBack.object! hBearId).status.faceDown &&
    gHistBack.isNight == gHist0.isNight &&
    !(gHistBack.player p0).isMonarch

  -- 3h. `GameEvent.resolutions` counts across control changes when `sourceId.isSome`, AND
  --     nested `.optional` `.nthResolutionThisTurn` records `GameEvent.resolved`:
  let snapBear := gHist0.snapshot (gHist0.object! hBearId)
  let resEv1 := GameEvent.resolved 1 p0 1 snapBear (sourceId := some ⟨42⟩)
  let resEv2 := GameEvent.resolved 1 p1 2 snapBear (sourceId := some ⟨42⟩)
  let gNestedNth :=
    gHist0.applyUnified p0
      { body := .optional .you none
          (.ifCond (.turnHistory (.nthResolutionThisTurn 1)) (Instruction.gainLifeFixed 3 .you) .noop)
          .noop }
      #[] (sourceId := some hBearId)
  let nthResOk :=
    GameEvent.resolutions #[resEv1, resEv2] 1 p1 (sourceId := some ⟨42⟩) == 2 &&
    gNestedNth.events.any (fun e => match e.change with | .rules (.stackObject (.resolved ..)) => true | _ => false)

  mustHold59i3 "3a_selfStaticRetainsBase" selfStaticRetainsBaseOk &&
  mustHold59i3 "3b_cr3057AndPeer" cr3057AndPeerOk &&
  mustHold59i3 "3c_nonBfAndKeywordExpand" nonBfAndKeywordExpandOk &&
  mustHold59i3 "3d_improviseAndAllTypes" improviseAndAllTypesOk &&
  mustHold59i3 "3e_rulesAndProt" rulesAndProtOk &&
  mustHold59i3 "3f_faceDownAndLayer36" faceDownAndLayer36Ok &&
  mustHold59i3 "3g_histReplay" histReplayOk &&
  mustHold59i3 "3h_nthRes" nthResOk &&
  mustHold59i3 "3.replay"
    (replayOk59i3 #[gDressDown1, gTsSelf1, gSplit1, gSeas1, gPeer1, gNonBf, gExa2, gImp0, gAllTypes1,
      gLifeRuleExp, gHex0, gProtDup, gFdEx, gFdBf, gAff0, gTc1, gTcOrder, gHist1, gNestedNth])

end Phase59Item3EventAlignment

/-! ### Phase 59 Item 4: `ManaCost.afterReduction` / `playManaCost` `{0}`–`{X}` / no-mana-cost alt,
`solveHybridsPay` tier priority, `ManaAbilities`/`LandsAndMana` `.custom (.tapObjects ..)` &
hand/graveyard reservations / `removeAnyNumberPlusOne` vs `prop.removePlusOneX` / `crewExcludesSelf`,
`PlayPermission.landsAllowed` cast-only exile exclusion, 3 `defaultChoiceAction` panic fixes,
`copyAndCast` / `asFlashback` `eligible` & graveyard `isDiscardableCard` guards -/
section Phase59Item4EventAlignment

private def mustHold59i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase59Item4EventAlignment failed: {label}"

private def replayOk59i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let g0 := emptyHand afterDraw p0

  -- 4a. `ManaCost.afterReduction` and `Costs.playManaCost` on `{0}`, `{X}` (X=0),
  --     and no-mana-cost cards (normal = unpayable `empty`, alt cost = payable `zero`):
  let xCost : ManaCost := { symbols := #[.x] }
  let zeroSpellDef : CardDef := {
    name := "P59i4 ZeroSpell"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let xSpellDef : CardDef := {
    name := "P59i4 XSpell"
    manaCost := xCost
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let noCostSpellDef : CardDef := {
    name := "P59i4 NoCostSpell"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gCost0 :=
    insertObject (insertObject (insertObject g0 zeroSpellDef p0 (.hand p0)) xSpellDef p0 (.hand p0))
      noCostSpellDef p0 (.hand p0)
  let hIds := (gCost0.player p0).hand
  let zeroObj := gCost0.object! hIds[0]!
  let xObj := gCost0.object! hIds[1]!
  let noCostObj := gCost0.object! hIds[2]!
  let freePerm : PlayPermission := { player := p0, withoutManaCost := true }
  let afterReductionAndPlayCostOk :=
    ManaCost.afterReduction ManaCost.zero ManaCost.empty == ManaCost.zero &&
    ManaCost.afterReduction xCost ManaCost.empty == ManaCost.zero &&
    ManaCost.afterReduction ManaCost.empty ManaCost.empty == ManaCost.empty &&
    gCost0.playManaCost { zeroObj with controller := some p0 } zeroSpellDef == ManaCost.zero &&
    (gCost0.playManaCost { xObj with controller := some p0 } xSpellDef).substituteX 0 == ManaCost.empty &&
    ManaCost.afterReduction xCost ((gCost0.playManaCost { xObj with controller := some p0 } xSpellDef).substituteX 0) == ManaCost.zero &&
    gCost0.playManaCost { noCostObj with controller := some p0 } noCostSpellDef == ManaCost.empty &&
    gCost0.playManaCost { noCostObj with controller := some p0 } noCostSpellDef (origPerm := some freePerm) == ManaCost.zero

  -- 4b. `solveHybridsPay` prefers the higher `spendOneUnit?`-tier color (spending restricted/rider/
  --     Treasure `{U}` over unrestricted `{W}` on `{W/U}`).
  let wuCost : ManaCost := { symbols := #[.hybrid .white .blue] }
  let poolWU : ManaPool := {
    units := #[
      { mana := .colored .white },
      { mana := .colored .blue, fromTreasure := true }
    ]
  }
  let hybridTierOk :=
    match poolWU.payUnits? wuCost {} with
    | some (rem, spent) =>
      spent.size == 1 && spent[0]!.fromTreasure && spent[0]!.mana == .colored .blue &&
      rem.units.size == 1 && rem.units[0]!.mana == .colored .white
    | none => false

  -- 4c. `PlayPermission.landsAllowed := false` (including `grantWidowCast`) prevents playing
  --     an exiled land (CR 305.9), while `landsAllowed := true` allows it.
  let gLand0 := insertObject (insertObject g0 forest p0 .exile) forest p0 .exile
  let exLands := gLand0.objects.filter (fun o => o.zone == .exile && o.name == forest.name)
  let castOnlyLand := exLands[0]!
  let playAllowedLand := exLands[1]!
  let gLand1 :=
    (gLand0.grantWidowCast p0 (some castOnlyLand.id) (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile playAllowedLand.id { player := p0, landsAllowed := true })
        .untilEndOfTurn) (cause := some testCause)
  let landsAllowedOk :=
    !gLand1.mayPlayLand p0 castOnlyLand &&
    !(gLand1.apply p0 (.playLand castOnlyLand.id)).isOk &&
    gLand1.mayPlayLand p0 playAllowedLand &&
    (gLand1.apply p0 (.playLand playAllowedLand.id)).isOk

  -- 4d. Three `defaultChoiceAction` vs `answerResolutionChoice` panic fixes:
  --     (i) `.chooseCards ids max .creaturesToBattlefield` clamps to `max` without panicking;
  --     (ii) `.triggerModes` on missing `objId` handles cleanly without throwing `"Choose a mode"`;
  --     (iii) `.mayCastCards` aligns Morph with Layer-6 `currentKeywords` and excludes lands!
  let gCh0 := insertObject (insertObject g0 bear p0 (.hand p0)) hero p0 (.hand p0)
  let chIds := (gCh0.player p0).hand
  let gChPaused := gCh0.change (.pending (.resolutionChoice p0 (.chooseCards chIds 1 .creaturesToBattlefield)))
  let gChooseCardsClamped :=
    mustApply gChPaused p0 (defaultChoiceAction gChPaused p0 (.chooseCards chIds 1 .creaturesToBattlefield))
  let gTmPaused := g0.change (.pending (.resolutionChoice p0 (.triggerModes ⟨99993⟩ 1 #[])))
  let gTrigModesMissing :=
    mustApply gTmPaused p0 (defaultChoiceAction gTmPaused p0 (.triggerModes ⟨99993⟩ 1 #[]))
  let morphGrantDef : CardDef := {
    name := "P59i4 MorphGrant", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.exile], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])])
    ]
  }
  let bigBearDef : CardDef := creature "P59i4 BigBear" (ManaCost.ofGeneric 7) #["Bear"] 5 5
  let gMayCast0 :=
    (insertObject (addPermanent g0 morphGrantDef p0 p0) bigBearDef p0 .exile).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }])
  let bigExId := (gMayCast0.objects.find? (fun o => o.zone == .exile && o.name == bigBearDef.name)).get!.id
  let gMayCastPaused :=
    gMayCast0.change (.pending (.resolutionChoice p0 (.mayCastCards #[bigExId] false false)))
  let gMayCastDone :=
    mustApply gMayCastPaused p0 (defaultChoiceAction gMayCastPaused p0 (.mayCastCards #[bigExId] false false))
  let defaultChoiceFixesOk :=
    gChooseCardsClamped.pending == .none &&
    (gChooseCardsClamped.permanentsOf p0).size == 1 &&
    gTrigModesMissing.pending == .none &&
    gMayCastDone.proposedSpell.isSome &&
    !gMayCastDone.stack.isEmpty

  -- 4e. `copyAndCast` / `asFlashback` obey `eligible` (`landsAllowed := false`) and graveyard
  --     `isDiscardableCard` excludes non-card tokens in `drawPerSevenCardGraveyard` /
  --     `returnFromGyTappedAttackingFinality`.
  let nonlandTokDef : CardDef := {
    creature "P59i4 GyTok" ManaCost.empty #["Goblin"] 1 1 with
    isToken := true
  }
  let gGyTok0 :=
    insertObject (insertObject (insertObject (insertObject (insertObject (insertObject
      (insertObject g0 bear p0 (.library p0))
      bear p0 (.graveyard p0)) bear p0 (.graveyard p0)) bear p0 (.graveyard p0))
      bear p0 (.graveyard p0)) bear p0 (.graveyard p0)) bear p0 (.graveyard p0)
  let (gGyTok1, tokObj) := gGyTok0.createOneToken p0 nonlandTokDef (cause := some testCause)
  let (gGyTok2, _) := gGyTok1.move tokObj.id (.graveyard p0) none (cause := some testCause)
  let gDrawSeven := gGyTok2.drawPerSevenCardGraveyard p0
  let gExLandCopy :=
    gLand0.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, copyAndCast := true, landsAllowed := false, freeCast := true }) }
      #[]
  let eligibleAndGyNonCardOk :=
    (gDrawSeven.player p0).hand.isEmpty &&
    gExLandCopy.pending == .none

  -- 4f. `Agent.payManaOrTapFirstSource` pays colored and `.combination` Ward costs,
  --     `activateManaAbility` allows `.custom (.tapObjects ..)` tapping a non-tap-reserved
  --     proposed source!
  let bounceLandDef : CardDef := {
    name := "P59i4 BounceWUB"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility
        (.combination (.explicit #[.colored .white, .colored .blue, .colored .black]) (.const 2))
    ]
  }
  let gWard0 := addPermanent g0 bounceLandDef p0 p0
  let bounceId := (gWard0.permanentsOf p0).find? (·.name == bounceLandDef.name) |>.get!.id
  let wardAct := Agent.payManaOrTapFirstSource gWard0 p0 { symbols := #[.colored .white, .colored .blue] }
  let tapPickManaDef : CardDef := {
    name := "P59i4 TapPickMana"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let sacSelfCreDef : CardDef := {
    creature "P59i4 SacSelfCre" ManaCost.zero #["Bear"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofColor .green), .sacrifice (.exact 1) .self]
      effect := Effect.gainLife 2
    }]
  }
  let gTapPick0 := addPermanent (addPermanent g0 tapPickManaDef p0 p0) sacSelfCreDef p0 p0
  let tapPickSrcId := (gTapPick0.permanentsOf p0).find? (·.name == tapPickManaDef.name) |>.get!.id
  let sacSelfId := (gTapPick0.permanentsOf p0).find? (·.name == sacSelfCreDef.name) |>.get!.id
  let gTapPickProp := mustApply gTapPick0 p0 (.activate sacSelfId 0)
  let tapPickOk := (gTapPickProp.apply p0 (.activateManaAbility tapPickSrcId 0 #[.colored .green] #[sacSelfId])).isOk
  let wardAndManaResOk :=
    (match wardAct with
     | some (.activateManaAbility sid 0 mana #[]) =>
       sid == bounceId && mana.contains (.colored .white) && mana.contains (.colored .blue)
     | _ => false) &&
    tapPickOk

  mustHold59i4 "4a_afterReductionAndPlayCost" afterReductionAndPlayCostOk &&
  mustHold59i4 "4b_hybridTier" hybridTierOk &&
  mustHold59i4 "4c_landsAllowed" landsAllowedOk &&
  mustHold59i4 "4d_defaultChoiceFixes" defaultChoiceFixesOk &&
  mustHold59i4 "4e_eligibleAndGyNonCard" eligibleAndGyNonCardOk &&
  mustHold59i4 "4f_wardAndManaRes" wardAndManaResOk &&
  mustHold59i4 "4.replay"
    (replayOk59i4 #[gCost0, gLand1, gChooseCardsClamped, gTrigModesMissing, gMayCastDone,
      gDrawSeven, gExLandCopy, gWard0, gTapPickProp])

end Phase59Item4EventAlignment

end Mtg.Engine.EventTests
