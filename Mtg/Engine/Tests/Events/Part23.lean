import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

/-! ### Phase 57 Item 1: Top-level continuation-queue `.chooseReplacement` non-stall & live outer
probing, `Event.lean` 12 pure-log leaves & narrowed `isPurePriorityGrantLeaf`, unwired
`.afterTriggerTargetsChosen` / `.resume*TriggerModesAfterLeave` / `drainProbeNonPriorityCont` /
`receivePriorityOutcomeFuel` / `classifyFinishProposedSpellCosts` / `.leavePlayersWhoLost`
`.delegate` probe parity, non-active CR 117.3c `outerCont?` priority preservation,
`SacrificeDiscard` `sourceId == none` & `Casting` completion / `afterWardResolved` tails, and
interactive `reattachOuterCont` `currentInterpWait?` ordering -/
section Phase57Item1EventAlignment

private def mustHold57i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase57Item1EventAlignment failed: {label}"

private def replayOk57i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let leyADef : CardDef := { name := "P57i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P57i1 LeyB", types := #[.enchantment] }

  -- 1a(i). Top-level queue helpers: `.chooseReplacement` `openedNewPrompt` does NOT falsely
  --        settle `anyContinuationSettlesControlFlow`, and continues past `.chooseReplacement`
  --        to find remaining live queued priority grants (including `.finishResolutionChoice`)!
  let gQ0 :=
    addPermanent (addPermanent g4 leyADef p0 p0) leyBDef p0 p0
  let qLeyA := (gQ0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let qLeyB := (gQ0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let dRidA : ReplacementId := { kind := .addNoncombatDamage, object := some qLeyA }
  let dRidB : ReplacementId := { kind := .multiplyDamage, object := some qLeyB }
  let gQRep :=
    (gQ0.createEffect
      (.replacement {
        id := dRidA, source := some qLeyA, controller := some p0, affectedPlayer := p0,
        kind := .addNoncombatDamage none 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := dRidB, source := some qLeyB, controller := some p0, affectedPlayer := p0,
        kind := .multiplyDamage none 2 }) (cause := some testCause)
  -- Non-priority damage leaf that opens a `.chooseReplacement` prompt with NO priority grant behind it:
  let dmgCont : PendingReplacement := .dealDamageToPlayer p0 1 none false (some testCause) false
  let gQNoGrant := gQRep.chainPendingReplacement dmgCont
  -- Same damage leaf with an explicit `.receivePriority p2` behind it on `outerPendingReplacements`:
  let gQWithExplicit :=
    gQRep.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some dmgCont
      }
    ]
  -- Same damage leaf with implicit `.finishResolutionChoice` behind it:
  let gQWithImplicit :=
    gQRep.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.finishResolutionChoice]
        pendingReplacement := some dmgCont
      }
    ]
  let topLevelQueueOk :=
    !gQNoGrant.anyContinuationSettlesControlFlow &&
    !gQNoGrant.anyContinuationGrantsPriority &&
    gQNoGrant.firstContinuationPriorityGrant? == none &&
    !gQNoGrant.hasImplicitPendingPriorityContinuation &&
    gQWithExplicit.anyContinuationSettlesControlFlow &&
    gQWithExplicit.anyContinuationGrantsPriority &&
    gQWithExplicit.firstContinuationPriorityGrant? == some (some p2) &&
    !gQWithExplicit.hasImplicitPendingPriorityContinuation &&
    gQWithImplicit.anyContinuationSettlesControlFlow &&
    gQWithImplicit.anyContinuationGrantsPriority &&
    gQWithImplicit.firstContinuationPriorityGrant? == some none &&
    gQWithImplicit.hasImplicitPendingPriorityContinuation

  -- 1a(ii). `Event.lean` 12 pure-log leaves in `isPurePostLog` & narrowed `isPurePriorityGrantLeaf`:
  let pureLog12 : Array PendingReplacement := #[
    .logPutCounterDelta ⟨1⟩ .plusOnePlusOne 0 .isPutOn,
    .finishPostStep (.logDiscardIfInGraveyard ⟨1⟩ p0 "disc"),
    .finishPostStep (.logExiledIfInExile ⟨1⟩ "ex"),
    .finishPostStep (.logReturnedToHand ⟨1⟩ p0 "Bear"),
    .finishPostStep (.logPutsIntoHand p0 ⟨1⟩ "Bear"),
    .finishPostStep (.logPutOnOwnerLibrary ⟨1⟩ p0 "Bear" true),
    .finishPostStep (.logIfCountersIncreased ⟨1⟩ {} "inc"),
    .finishPostStep (.finishMoveToOwnerGraveyardLog ⟨1⟩ .battlefield p0 "Bear" "dies" none),
    .finishPostStep (.logDiscardedCount p0 0),
    .finishPostStep (.logGiftTreasureGiven p1),
    .finishPostStep (.logCreatedTokensSummary p0 0),
    .finishPostStep (.logDelayedBirdSoldiersCreated p0 0)
  ]
  let all12PureLog := pureLog12.all PendingReplacement.isPurePostLog
  let narrowedPurePrioOk :=
    (PendingReplacement.receivePriority p0).isPurePriorityGrantLeaf &&
    (PendingReplacement.finishPostStep (.beginStepBody .upkeep)).isPurePriorityGrantLeaf &&
    (PendingReplacement.finishPostStep (.beginStepBody .beginningOfCombat)).isPurePriorityGrantLeaf &&
    (PendingReplacement.finishPostStep (.beginStepBody .endOfCombat)).isPurePriorityGrantLeaf &&
    (PendingReplacement.finishPostStep (.beginStepBody .postcombatMain)).isPurePriorityGrantLeaf &&
    (PendingReplacement.finishPostStep (.beginStepBody .end)).isPurePriorityGrantLeaf &&
    !PendingReplacement.afterWardResolved.isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep .startNextTurnAndBegin).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep .endTurnAfterCleanupStepEnded).isPurePriorityGrantLeaf &&
    !(PendingReplacement.beginStepCont .precombatMain).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep (.beginStepAfterPhaseBegan .upkeep)).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep (.beginStepBody .draw)).isPurePriorityGrantLeaf &&
    !(PendingReplacement.finishPostStep (.beginStepBody .precombatMain)).isPurePriorityGrantLeaf
  -- Mana ability (`prevPending == .none`) followed by one of the newly added pure-log leaves
  -- grants priority both in probes and at runtime:
  let gManaLog0 := addPermanent g4 forest p1 p1
  let mForestId := (gManaLog0.permanentsOf p1)[0]!.id
  let manaPlusPure12 : PendingReplacement :=
    .seq
      (.finishActivateManaAbilityPicks p1 mForestId forest.name #[.colored .green] #[] #[] false false none none 0 false .none)
      (.finishPostStep (.logCreatedTokensSummary p1 0))
  let gManaPlusRun := gManaLog0.resumePendingReplacement manaPlusPure12
  let pureLogManaPrioOk :=
    all12PureLog && narrowedPurePrioOk &&
    gManaLog0.continuationGrantsPriority false manaPlusPure12 &&
    gManaLog0.continuationSettlesControlFlow false manaPlusPure12 &&
    gManaLog0.priorityRecipientOfContinuation? false manaPlusPure12 == some p1 &&
    gManaPlusRun.playersReceivePriority &&
    gManaPlusRun.priority == p1

  -- 1a(iii). Unwired & divergent probes:
  -- (a) `.afterTriggerTargetsChosen` & `.resumeTriggerModesAfterLeave` wired across state-aware probes:
  let gTrigDone0 := g4.change (.pendingPriority (some p2))
  let afterTrigCont : PendingReplacement := .finishPostStep .afterTriggerTargetsChosen
  let gAfterTrigRun := gTrigDone0.resumePendingReplacement afterTrigCont
  let afterTrigWiredOk :=
    gTrigDone0.continuationGrantsPriority false afterTrigCont &&
    gTrigDone0.continuationSettlesControlFlow false afterTrigCont &&
    gTrigDone0.priorityRecipientOfContinuation? false afterTrigCont == none &&
    (gTrigDone0.chainPendingReplacement afterTrigCont).hasImplicitPendingPriorityContinuation &&
    (gTrigDone0.chainPendingReplacement afterTrigCont).firstContinuationPriorityGrant? == some none &&
    gAfterTrigRun.priority == p2
  let resumeTrigCont : PendingReplacement :=
    .finishPostStep (.resumeTriggerModesAfterLeave p1 ⟨9999⟩ 1 #[])
  let gResumeTrigRun := gTrigDone0.resumePendingReplacement resumeTrigCont
  let resumeTrigWiredOk :=
    gTrigDone0.continuationGrantsPriority false resumeTrigCont &&
    gTrigDone0.continuationSettlesControlFlow false resumeTrigCont &&
    gTrigDone0.priorityRecipientOfContinuation? false resumeTrigCont == none &&
    (gTrigDone0.chainPendingReplacement resumeTrigCont).hasImplicitPendingPriorityContinuation &&
    (gTrigDone0.chainPendingReplacement resumeTrigCont).firstContinuationPriorityGrant? == some none &&
    gResumeTrigRun.priority == p2
  -- (b) `drainProbeNonPriorityCont` effectful leaves (e.g. `.markDamageOn`, `.grantAdventureExilePermission`):
  let gDrain0 := addPermanent g4 bear p0 p0
  let dBearId := (gDrain0.permanentsOf p0)[0]!.id
  let markAndPrio : PendingReplacement :=
    .seq (.markDamageOn dBearId 2 "bolt" false none false false (some testCause)) (.receivePriority p2)
  let drainProbeOk :=
    gDrain0.continuationGrantsPriority false markAndPrio &&
    gDrain0.priorityRecipientOfContinuation? false markAndPrio == some p2
  -- (c) `.leavePlayersWhoLost` `.delegate` `stepCanReverseProposal` runtime-vs-probe parity:
  --     When `.leavePlayersWhoLost` delegates to a proposal-reversing `.restorePending` inside
  --     `.seq first rest`, runtime `.seq` drops `rest` (matching the probe)!
  let sorc1Def : CardDef := {
    name := "P57i1 Sorc1"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gRev0 := insertObject (addPermanent (emptyHand g4 p0) forest p0 p0) sorc1Def p0 (.hand p0)
  let gRevProp0 := mustApply gRev0 p0 (.cast (gRev0.player p0).hand.back!)
  let revSpellId := gRevProp0.proposedSpell.get!.spellId
  let (gRevProp1, _) := gRevProp0.move revSpellId .exile none (cause := some testCause)
  let gRevProp := gRevProp1.change (.pending .none)
  let leaveDelegateSeq : PendingReplacement :=
    .seq
      (.leavePlayersWhoLost (some (.activateManaAbilities p0)) false #[] none none)
      (.logMessage "should-not-run-after-leave-reverse")
  let gRevRun := gRevProp.resumePendingReplacement leaveDelegateSeq
  let leaveDelegateRevOk :=
    gRevProp.proposedSpell.isSome &&
    gRevRun.proposedSpell.isNone &&
    !gRevRun.log.contains "should-not-run-after-leave-reverse"

  -- 1b(i). CR 117.3c non-active `outerCont?` priority preservation:
  --        Non-active player `p1` (activePlayer is `p0`) completes a `.spell` cast while a
  --        non-priority `outerCont?` (`!outer.endsWithPriorityGrant`) is present; priority MUST
  --        return to `p1` (CR 117.3c), NOT `g.activePlayer` (`p0`)!
  let sacInstDef : CardDef := {
    name := "P57i1 SacInst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some {
      effect := Effect.gainLife 1
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.sacrificePermanents 1)]
    }
  }
  let gNonAct0 :=
    (insertObject (addPermanent (emptyHand g4 p1) bear p1 p1) sacInstDef p1 (.hand p1)).receivePriority p1
  let naFodderId := (gNonAct0.permanentsOf p1)[0]!.id
  let naInstId := (gNonAct0.player p1).hand.back!
  let gNonActCast0 := mustApply (mustApply gNonAct0 p1 (.cast naInstId)) p1 .pay
  let gNonActWithOuter :=
    gNonActCast0.chainPendingReplacement (.logMessage "non-active-outer-log")
  let gNonActDone := mustApply gNonActWithOuter p1 (.sacrifice naFodderId)
  let nonActOuterPrioOk :=
    gNonActDone.activePlayer == p0 &&
    gNonActDone.pending == .none &&
    gNonActDone.priority == p1 &&
    gNonActDone.log.contains "non-active-outer-log"

  -- 1b(ii). `SacrificeDiscard` `sourceId == none` with `outerCont? == none && currentInterpWait?.isSome`
  --         resumes `finishResolutionChoice` (never stalls!), and `Casting.afterWardResolved`
  --         checks non-`sbaPaused` `pending` before popping outers:
  let gSacInterp0 := addPermanent (emptyHand g4 p0) bear p0 p0
  let siFodderId := (gSacInterp0.permanentsOf p0)[0]!.id
  let dummyInterp : InterpState := {
    ctx := { controller := p0 }
    queue := #[.life (.gain .you (.const 3))]
    stack := #[]
  }
  let gSacInterpPrompt :=
    gSacInterp0.changes #[
      .pushContinuationFrame { interpWait? := some dummyInterp },
      .pending (.sacrificePermanent p0 ⟨9999⟩)
    ]
  let lifeBeforeSi := (gSacInterpPrompt.player p0).life
  let gSacInterpDone := mustApply gSacInterpPrompt p0 (.sacrifice siFodderId)
  let sacInterpResumeOk :=
    gSacInterpDone.pending == .none &&
    gSacInterpDone.currentInterpWait?.isNone &&
    (gSacInterpDone.player p0).life == lifeBeforeSi + 3
  -- `afterWardResolved` with a non-`sbaPaused` open prompt does NOT prematurely pop `outerPendingReplacements`:
  let gWardOpen :=
    g4.changes #[
      .pushContinuationFrame { outerPendingReplacements := #[.logMessage "keep-outer"] },
      .pending (.scry p0 1)
    ]
  let gWardAfter := gWardOpen.afterWardResolved
  let wardPendingOrderOk :=
    gWardAfter.pending == .scry p0 1 &&
    gWardAfter.outerPendingReplacements == #[.logMessage "keep-outer"] &&
    !gWardAfter.log.contains "keep-outer"

  -- 1b(iii). Interactive handlers use `reattachOuterCont` so `outer` executes AFTER `currentInterpWait?`
  --          (while Ancestry-scry `.finishPostCast` keeps precedence in `finishScry`):
  let gScryOrd0 := g4
  let interpAfterScry : InterpState := {
    ctx := { controller := p0 }
    queue := #[.life (.gain .you (.const 2))]
    stack := #[]
  }
  let gScryOrdPrompt :=
    gScryOrd0.changes #[
      .pushContinuationFrame {
        interpWait? := some interpAfterScry
        pendingReplacement := some (.logMessage "outer-after-interp")
      },
      .pending (.scry p0 1)
    ]
  let lifeBeforeScry := (gScryOrdPrompt.player p0).life
  let topScryId := (gScryOrdPrompt.player p0).library.back!
  let gScryOrdDone := mustApply gScryOrdPrompt p0 (.scry #[topScryId] #[])
  -- Find order in `gScryOrdDone.events`: life gain from `interpAfterScry` occurs BEFORE `"outer-after-interp"`!
  let lifeIdx? := gScryOrdDone.events.findIdx? fun
    | .rules _ (.life (.gained q 2)) _ _ => q == p0
    | _ => false
  let outerLogIdx? := gScryOrdDone.events.findIdx? fun
    | .engine _ (.logMsg "outer-after-interp") _ => true
    | _ => false
  let reattachOrderOk :=
    gScryOrdDone.pending == .none &&
    (gScryOrdDone.player p0).life == lifeBeforeScry + 2 &&
    (match lifeIdx?, outerLogIdx? with
     | some li, some oi => li < oi
     | _, _ => false)

  mustHold57i1 "1a_topLevelQueue" topLevelQueueOk &&
  mustHold57i1 "1a_pureLogAndPrio" pureLogManaPrioOk &&
  mustHold57i1 "1a_afterTrigWired" afterTrigWiredOk &&
  mustHold57i1 "1a_resumeTrigWired" resumeTrigWiredOk &&
  mustHold57i1 "1a_drainProbe" drainProbeOk &&
  mustHold57i1 "1a_leaveDelegateRev" leaveDelegateRevOk &&
  mustHold57i1 "1b_nonActOuterPrio" nonActOuterPrioOk &&
  mustHold57i1 "1b_sacInterpResume" sacInterpResumeOk &&
  mustHold57i1 "1b_wardPendingOrder" wardPendingOrderOk &&
  mustHold57i1 "1b_reattachOrder" reattachOrderOk &&
  mustHold57i1 "1.replay"
    (replayOk57i1 #[gManaPlusRun, gAfterTrigRun, gResumeTrigRun, gRevRun, gNonActDone, gSacInterpDone, gWardAfter, gScryOrdDone])

end Phase57Item1EventAlignment

/-! ### Phase 57 Item 2: Paused `.endControlExileLoop` `deferPlayFromExileLogs` regression,
recursive `StateBasedActions` deferral & CR 704.5q counter annihilation, 5 remaining simultaneous
multi-permanent move loops (`destroyPermanentsLoop`, `exilePermanentsLoop`, `flickerPermanents`,
`returnCreaturesNotOfType`, `Interpreter.execMoveLoopStep`), `hasPlayFromExileLoggedInSlice` /
`emitExpiredPlayFromExileLogs` multi-frame & pre-priority placement, and `.control`/`.copy`
CR 800.4c reconciliation -/
section Phase57Item2EventAlignment

private def mustHold57i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase57Item2EventAlignment failed: {label}"

private def replayOk57i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let bearExpMsg := s!"{bear.name} can no longer be played from exile"
  let countBearExpLogs (g : Game) := (g.log.filter (· == bearExpMsg)).size
  let mayCastFromExileDef : CardDef := {
    bear with
    name := "P57i2 CastFromExileSrc"
    staticAbilities := #[.ruleModifying none (.play (.mayPlayFrom .you .exile .anyObject true true false false))]
  }

  -- 2a(i). Paused `.endControlExileLoop` clears `deferPlayFromExileLogs := false` when pausing
  --        on `.chooseReplacement` under a synchronous caller (`ceaseToExist` with
  --        `deferPlayFromExileLogs := true`), and only keeps `true` when an already-queued
  --        continuation owns `loopFromIdx..` without an intervening priority/reversal boundary:
  let gEndCtrl0 :=
    insertObject (addPermanent g3 mayCastFromExileDef p1 p1) bear p0 .exile
  let ecSrcId := (gEndCtrl0.permanentsOf p1)[0]!.id
  let ecExId := (gEndCtrl0.objects.filter (·.zone == .exile)).back!.id
  let gEndCtrl1 :=
    ((gEndCtrl0.changeObject ecExId (.exiledBy (some ecSrcId))).createEffect
      (.permission (some p0) (.playFromExile ecExId { player := p0 }) (.whileSourceOnBattlefield ecSrcId))
      (cause := some testCause))
  let ecStart := gEndCtrl1.events.size
  let gEndCtrlRes :=
    gEndCtrl1.runEndControlExileLoop #[(ecSrcId, "exiled (CR 800.4c)", some p0)] testCause
      (fromEventIdx? := some ecStart) (deferPlayFromExileLogs := true)
  -- Synchronous completion with `deferPlayFromExileLogs := true` defers to caller (`0` logs yet),
  -- then caller's `emitExpiredPlayFromExileLogs` emits `1`:
  let gEndCtrlEmitted := gEndCtrl1.emitExpiredPlayFromExileLogs gEndCtrlRes ecStart
  -- Real `.chooseReplacement` pause reached via `ceaseToExist` (`deferPlayFromExileLogs := true`,
  -- matching `reconcilePostReplayDepartures` / `recordRemoveCountersMulti` / `move`):
  let ecEmbCard : CardDef := { name := "P57i2 PauseEmblem" }
  let gEcPause0 :=
    insertObject (insertObject (addPermanent g3 mayCastFromExileDef p0 p2) ecEmbCard p1 .command (some p1))
      bear p0 .exile
  let ecPausePermId := (gEcPause0.permanentsOf p2)[0]!.id
  let ecPauseEmbId := (gEcPause0.objects.filter (·.zone == .command)).back!.id
  let ecPauseExId := (gEcPause0.objects.filter (·.zone == .exile)).back!.id
  let ecRepA : ReplacementId := { kind := .addNoncombatDamage, object := some ecPausePermId }
  let ecRepB : ReplacementId := { kind := .multiplyDamage, object := some ecPausePermId }
  let gEcPause1 :=
    ((((((gEcPause0.changeObject ecPauseExId (.exiledBy (some ecPausePermId))).createEffect
      (.layered (.objects #[ecPausePermId]) (.control p1) (.whileInZone ecPauseEmbId .command))
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile ecPauseExId { player := p0 }) (.whileSourceOnBattlefield ecPausePermId))
      (cause := some testCause)).createEffect
      (.replacement { id := ecRepA, affectedPlayer := p0, kind := .addNoncombatDamage none 1 })
      (cause := some testCause)).createEffect
      (.replacement { id := ecRepB, affectedPlayer := p0, kind := .multiplyDamage none 2 })
      (cause := some testCause)).playerLeavesGame p2)
  -- Open a real `.chooseReplacement` prompt before calling `ceaseToExist (deferPlayFromExileLogs := true)`:
  let gEcWithChoice := gEcPause1.dealDamageToPlayer p0 1 (cause := some testCause)
  let ecPauseStart := gEcWithChoice.events.size
  let gEcCeased :=
    gEcWithChoice.ceaseToExist ecPauseEmbId (cause := some testCause)
      (reconcileControl := true) (deferPlayFromExileLogs := true)
  -- Synchronous caller emits on return (before the paused exile has occurred -> 0 logs):
  let gEcSyncEmit := gEcWithChoice.emitExpiredPlayFromExileLogs gEcCeased ecPauseStart
  let rec hasNonDeferredEndCtrl : PendingReplacement → Bool
    | .endControlExileLoop _ _ _ _ _ false => true
    | .seq a b => hasNonDeferredEndCtrl a || hasNonDeferredEndCtrl b
    | _ => false
  let rec hasDeferredEndCtrl : PendingReplacement → Bool
    | .endControlExileLoop _ _ _ _ _ true => true
    | .seq a b => hasDeferredEndCtrl a || hasDeferredEndCtrl b
    | _ => false
  -- Answering the open `.chooseReplacement` resumes damage and then `.endControlExileLoop`,
  -- exiling `ecPausePermId` and emitting the `.playFromExile` expiry log ONCE!
  let gEcResumed := mustApply gEcSyncEmit p0 (.chooseReplacement ecRepA)
  -- Conversely, when an already-queued `.checkSBA (some ecPauseStart)` owns `ecPauseStart..`
  -- ahead of any priority/reversal boundary, paused `runEndControlExileLoop` keeps `defer := true`:
  let gEcOwned :=
    (gEcWithChoice.changes #[
      .pushContinuationFrame { outerPendingReplacements := #[.checkSBA (some ecPauseStart)] }
    ]).runEndControlExileLoop #[(ecPausePermId, "exiled (CR 800.4c)", some p1)] testCause
      (fromEventIdx? := some ecPauseStart) (deferPlayFromExileLogs := true)
  let endCtrlDeferOk :=
    countBearExpLogs gEndCtrlRes == 0 &&
    countBearExpLogs gEndCtrlEmitted == 1 &&
    (match gEcCeased.pending with | .chooseReplacement .. => true | _ => false) &&
    gEcCeased.pendingReplacement.any hasNonDeferredEndCtrl &&
    countBearExpLogs gEcSyncEmit == 0 &&
    countBearExpLogs gEcResumed == 1 &&
    (gEcResumed.findObject? (gEcResumed.followMoved ecPausePermId)).any (·.zone == .exile) &&
    gEcOwned.pendingReplacement.any hasDeferredEndCtrl

  -- 2a(ii). CR 704.5q counter annihilation removes `+1/+1` and `-1/-1` counters cleanly via
  --         `finishSbaSweep` `.counterAnnihilation` stage:
  let gAnnih0 := addPermanent g3 bear p0 p0
  let annihId := (gAnnih0.permanentsOf p0)[0]!.id
  let gAnnih1 :=
    (gAnnih0.recordPutCounters annihId .plusOnePlusOne 2 (some p0) (cause := some testCause)).recordPutCounters
      annihId .minusOneMinusOne 1 (some p0) (cause := some testCause)
  let gAnnih2 := gAnnih1.checkSBA
  let annihObj := gAnnih2.object! annihId
  let sbaCounterAnnihOk :=
    annihObj.status.counters.count .plusOnePlusOne == 1 &&
    annihObj.status.counters.count .minusOneMinusOne == 0

  -- 2a(iii). All 5 remaining simultaneous multi-permanent move loops defer `.playFromExile` logs
  --          across the full batch and emit ONCE when both source and `mayCastExiledBySource` leave:
  let mkBatchSetup : Game × ObjectId × ObjectId × ObjectId :=
    let gA := insertObject (addPermanent (addPermanent g3 bear p0 p0) mayCastFromExileDef p0 p0) bear p0 .exile
    let srcId := (gA.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
    let mcId := (gA.permanentsOf p0).find? (·.name == mayCastFromExileDef.name) |>.get!.id
    let exId := (gA.objects.filter (·.zone == .exile)).back!.id
    let gB :=
      (gA.changeObject exId (.exiledBy (some mcId))).createEffect
        (.permission (some p0) (.playFromExile exId { player := p0 }) (.whileSourceOnBattlefield srcId))
        (cause := some testCause)
    (gB, srcId, mcId, exId)
  let (gSim0, simSrc, simMc, _) := mkBatchSetup
  let gSimDestroy := gSim0.destroyPermanentsLoop #[simSrc, simMc] (cause := some testCause)
  let gSimExile := gSim0.exilePermanentsLoop #[simSrc, simMc] (cause := some testCause)
  let gSimFlicker := gSim0.flickerPermanents #[simSrc, simMc] (cause := some testCause)
  let gSimReturn := gSim0.returnCreaturesNotOfType .goblin
  let gSimInterp :=
    gSim0.applyUnified p0
      { body := .moveZone (.inZones .battlefield (.hasType .creature)) .exile .exile {} } #[]
  let fiveLoopsDeferOk :=
    countBearExpLogs gSimDestroy == 1 &&
    countBearExpLogs gSimExile == 1 &&
    countBearExpLogs gSimFlicker == 1 &&
    countBearExpLogs gSimReturn == 1 &&
    countBearExpLogs gSimInterp == 1

  -- 2b(i). `Core.hasPlayFromExileLoggedInSlice`:
  --        (a) Already-unplayable card's extra `.expired` event does NOT poison `pending`/`elig`;
  --        (b) Pre-`startIdx` ambiguous log does NOT mark an in-slice card as `loggedInSlice`;
  --        (c) Multi-frame `g.continuations` (`size ≥ 2`) inspects lower frames in `emitExpiredPlayFromExileLogs`
  --            and places `deferCont` AHEAD of `.finishResolutionChoice` / proposal-reversing `.restorePending`!
  let gPoison0 := insertObject (insertObject g3 bear p0 .exile) bear p0 .exile
  let pIds := (gPoison0.objects.filter (·.zone == .exile)).map (·.id)
  let pIdA := pIds[0]!; let pIdB := pIds[1]!
  let gPoison1 :=
    gPoison0.createEffect (.permission (some p0) (.playFromExile pIdB { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let pEidB := gPoison1.activeEffects.back!.1
  -- Record a synthetic `.expired` for already-unplayable `pIdA`, then expire & log `pIdB`:
  let poisonStart := gPoison1.events.size
  let gPoison2 :=
    ((gPoison1.record (GameEvent.effectExpired gPoison1.turnNumber ⟨9001⟩
        (some (.permission (some p0) (.playFromExile pIdA { player := p0 }) .untilEndOfTurn))
        (cause := testCause))).expireEffectById pEidB (cause := some testCause)).logMsg bearExpMsg
  let gPoison3 := gPoison1.emitExpiredPlayFromExileLogs gPoison2 poisonStart
  -- Pre-`startIdx` ambiguous log vs in-slice sibling:
  let gPreAmb0 := insertObject (insertObject (insertObject g3 bear p0 .exile) bear p0 .exile) bear p0 .exile
  let paIds := (gPreAmb0.objects.filter (·.zone == .exile)).map (·.id)
  let pa1 := paIds[0]!; let pa2 := paIds[1]!; let pa3 := paIds[2]!
  let gPreAmb1 :=
    ((gPreAmb0.createEffect (.permission (some p0) (.playFromExile pa1 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile pa2 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile pa3 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let pae1 := gPreAmb1.activeEffects[gPreAmb1.activeEffects.size - 3]!.1
  let pae2 := gPreAmb1.activeEffects[gPreAmb1.activeEffects.size - 2]!.1
  let pae3 := gPreAmb1.activeEffects[gPreAmb1.activeEffects.size - 1]!.1
  -- Before `sliceStart`: `pa1` and `pa2` expire and ONE ambiguous log is emitted (`inS = false`):
  let gPreAmb2 :=
    ((gPreAmb1.expireEffectById pae1 (cause := some testCause)).expireEffectById
      pae2 (cause := some testCause)).logMsg bearExpMsg
  let sliceStart := gPreAmb2.events.size
  -- Inside `[sliceStart, hi)`: `pa3` expires (no log yet!), must emit 1 log (not suppressed by pre-slice log!):
  let gPreAmb3 := gPreAmb2.expireEffectById pae3 (cause := some testCause)
  let gPreAmb4 := gPreAmb2.emitExpiredPlayFromExileLogs gPreAmb3 sliceStart
  -- Multi-frame `emitExpiredPlayFromExileLogs` & pre-boundary placement before `.finishResolutionChoice`:
  let gFrcDef0 := insertObject (addPermanent g3 mayCastFromExileDef p0 p0) bear p0 .exile
  let fdMcId := (gFrcDef0.permanentsOf p0).back!.id
  let fdExId := (gFrcDef0.objects.filter (·.zone == .exile)).back!.id
  let gFrcDef1 :=
    (gFrcDef0.changeObject fdExId (.exiledBy (some fdMcId))).createEffect
      (.permission (some p0) (.playFromExile fdExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let fdEid := gFrcDef1.activeEffects.back!.1
  let fdStart := gFrcDef1.events.size
  let gFrcPaused :=
    (gFrcDef1.expireEffectById fdEid (cause := some testCause)).changes #[
      .pushContinuationFrame { outerPendingReplacements := #[.finishResolutionChoice] },
      .pushContinuationFrame {},
      .pending (.chooseReplacement p0 #[])
    ]
  let gFrcPlaced := gFrcDef1.emitExpiredPlayFromExileLogs gFrcPaused fdStart
  let placedBeforeFrc :=
    match (gFrcPlaced.continuations[0]?.bind (fun f => f.outerPendingReplacements[0]?) : Option PendingReplacement) with
    | some (.seq (.finishPostStep (.logExpiredPlayFromExile ids _)) .finishResolutionChoice) =>
      ids.contains fdExId
    | _ => false
  let sliceAndMultiFrameOk :=
    countBearExpLogs gPoison3 == 1 &&
    countBearExpLogs gPreAmb4 == 2 &&
    placedBeforeFrc

  -- 2b(iii). `Core.restoreControlUntilSourceLeaves` keeps `"returns to"` log when a permanent
  --          loses a `srcId`-tied `.control` effect and stays under living owner's control;
  --          `Core.expireEffectById` `.commandEmblem` emits expired `.playFromExile` logs when `!defer`:
  let gCtrlRev0 := addPermanent (addPermanent g3 bear p1 p1) hero p0 p0
  let ctrlTarget := (gCtrlRev0.permanentsOf p1)[0]!
  let ctrlSrc := (gCtrlRev0.permanentsOf p0)[0]!
  let gCtrlRev1 :=
    (gCtrlRev0.playerLeavesGame p2).createEffect
      (.layered (.objects #[ctrlTarget.id]) (.control p2) (.untilSourceLeaves ctrlSrc.id))
      (cause := some testCause)
  let gCtrlRev2 := gCtrlRev1.restoreControlUntilSourceLeaves ctrlSrc.id
  let ctrlRevLogOk :=
    gCtrlRev2.controllerOf (gCtrlRev2.object! ctrlTarget.id) == some p1 &&
    gCtrlRev2.log.any (fun m => m.contains "returns to")
  let embCard : CardDef := { name := "P57i2 Emblem" }
  let gEmb0 := insertObject (insertObject g3 embCard p0 .command (some p0)) bear p0 .exile
  let embObj := (gEmb0.objects.filter (·.zone == .command)).back!
  let embExId := (gEmb0.objects.filter (·.zone == .exile)).back!.id
  let gEmb1 :=
    (gEmb0.createEffect (.gameRule (.commandEmblem embObj.id) (.untilNextTurnOf p0))
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile embExId { player := p0 }) (.whileInZone embObj.id .command))
      (cause := some testCause)
  let embRuleEid := gEmb1.activeEffects[gEmb1.activeEffects.size - 2]!.1
  let gEmb2 := gEmb1.expireEffectById embRuleEid (cause := some testCause) (deferPlayFromExileLogs := false)
  let embExileLogOk := countBearExpLogs gEmb2 == 1

  mustHold57i2 "2a_endCtrlDefer" endCtrlDeferOk &&
  mustHold57i2 "2a_sbaCounterAnnih" sbaCounterAnnihOk &&
  mustHold57i2 "2a_fiveLoopsDefer" fiveLoopsDeferOk &&
  mustHold57i2 "2b_sliceAndMultiFrame" sliceAndMultiFrameOk &&
  mustHold57i2 "2b_ctrlRevLog" ctrlRevLogOk &&
  mustHold57i2 "2b_embExileLog" embExileLogOk &&
  mustHold57i2 "2.replay"
    (replayOk57i2 #[gEndCtrlEmitted, gEcResumed, gAnnih2, gSimDestroy, gSimExile,
      gSimFlicker, gSimReturn, gSimInterp, gPoison3, gPreAmb4, gCtrlRev2, gEmb2])

end Phase57Item2EventAlignment

/-! ### Phase 57 Item 3: `Event.evalEventObjPred` `.hasDesignation` & designation LKI,
source-less `dealDamageFrom` protection / `replaceDamage` `effSrc?` / general player protection
`(q, dur)`, Layer-5 non-battlefield `.colors` & Layer-6 CR 305.7 / peer-emblem fast paths,
`.turnHistory` & `EvalExpr` `lookBackState?`, and `faceDown` / Layer-5 colors / Layer-6 Flash /
opponent-exile `Costs.applyCastCostReductions` & Layer-3 affinity -/
section Phase57Item3EventAlignment

private def mustHold57i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase57Item3EventAlignment failed: {label}"

private def replayOk57i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := afterDraw

  -- 3a(i). `Event.evalEventObjPred` `.hasDesignation` (all 4 designations), `isRingBearer` LKI,
  --        and `entersAsCopyCreatureUntilEot` (CR 707.2) not inheriting uncopied `entersPrepared`:
  let eoNone : EventObject := { id := some ⟨50⟩, types := #[.creature] }
  let eoPrep := { eoNone with prepared := true }
  let eoHarn := { eoNone with harnessed := true }
  let eoGoad := { eoNone with goaded := true }
  let eoRing := { eoNone with ringBearer := true }
  let predCheck (eo : EventObject) (tag : PermanentDesignationTag) : Bool :=
    (GameEvent.moved 1 eo .battlefield (.graveyard p0) (cause := testCause)).matchesTriggerPattern
      p0 none (.zoneChange (.hasDesignation tag) (.ofZone .battlefield) (.ofZone .graveyard))
  let desigPredOk :=
    !predCheck eoNone .prepared && predCheck eoPrep .prepared && !predCheck eoPrep .harnessed &&
    !predCheck eoNone .harnessed && predCheck eoHarn .harnessed &&
    !predCheck eoNone .goaded && predCheck eoGoad .goaded &&
    !predCheck eoNone .ringBearer && predCheck eoRing .ringBearer
  let lkiRingObj : GameObject := {
    id := ⟨51⟩, printed := bear, owner := p0, zone := .battlefield,
    controller := some p0, isLkiSnapshot := true,
    lkiLayer6 := some { ringBearer := true }
  }
  let lkiNotRingObj := { lkiRingObj with lkiLayer6 := some { ringBearer := false } }
  let isRingBearerLkiOk :=
    g0.isRingBearer p0 lkiRingObj && !g0.isRingBearer p0 lkiNotRingObj
  -- `entersAsCopyCreatureUntilEot` (CR 707.2) does NOT set `prepared := true` from uncopied printed `entersPrepared`:
  let prepCloneDef : CardDef := {
    creature "P57i3 PrepClone" ManaCost.empty #["Shapeshifter"] 0 0 with
    staticAbilities := #[StaticAbility.entersPrepared, StaticAbility.asEntersMayCopyCreatureHasteUntilEot]
  }
  let gCopyPrep0 := insertObject (addPermanent g0 bear p0 p0) prepCloneDef p0 (.hand p0)
  let bearBfId := (gCopyPrep0.permanentsOf p0)[0]!.id
  let cloneCardId := (gCopyPrep0.player p0).hand.back!
  let (gCopyPrep1, _) :=
    gCopyPrep0.move cloneCardId .battlefield (some p0) (cause := some testCause)
  let copyChoiceId :=
    match gCopyPrep1.pending with
    | .chooseReplacement _ cs =>
      (cs.find? (fun c => match c.kind with | .entersAsCopyCreatureUntilEot tid => tid == bearBfId | _ => false)).get!
    | _ => { kind := .entersAsCopyCreatureUntilEot bearBfId }
  let gCopyPrep2 := mustApply gCopyPrep1 p0 (.chooseReplacement copyChoiceId)
  let enteredCloneObj := (gCopyPrep2.permanentsOf p0).find? (·.id != bearBfId) |>.get!
  let (gCopyPrepDepart, _) := gCopyPrep2.move enteredCloneObj.id (.graveyard p0) none (cause := some testCause)
  let copyPrepOk :=
    gCopyPrep2.name enteredCloneObj == bear.name &&
    !enteredCloneObj.status.prepared &&
    !gCopyPrepDepart.wasPreparedAtDeparture enteredCloneObj.id

  -- 3a(ii). Source-less `dealDamageFrom` protection, `replaceDamage` `effSrc?`, and general
  --         `(q, dur)` player protection via `Interpreter.applyRule`:
  let protColorlessDef : CardDef := {
    creature "P57i3 ProtColorless" ManaCost.empty #["Knight"] 3 5 with
    keywords := #[.protection .colorless]
  }
  let protAllDef : CardDef := {
    creature "P57i3 ProtAll" ManaCost.empty #["Avatar"] 3 3 with
    keywords := #[.protection .everything]
  }
  let gProt0 := addPermanent (addPermanent g0 protColorlessDef p0 p0) protAllDef p0 p0
  let pColObj := (gProt0.permanentsOf p0).find? (·.name == protColorlessDef.name) |>.get!
  let pAllObj := (gProt0.permanentsOf p0).find? (·.name == protAllDef.name) |>.get!
  -- Source-less (`source := none`, `sourceSnap := none`) damage IS dealt to `.protection .colorless`
  -- and IS prevented by `.protection .everything` — including when interrupted by `.chooseReplacement`
  -- (both opening a replacement choice itself AND entering while `.chooseReplacement` is already open)!
  let gProt1 := gProt0.dealDamageFrom "Nameless" pColObj 2 (source := none) (sourceSnap := none) (cause := some testCause)
  let gProt2 := gProt1.dealDamageFrom "Nameless" pAllObj 2 (source := none) (sourceSnap := none) (cause := some testCause)
  let protRepA : ReplacementId := { kind := .addNoncombatDamage, object := some pColObj.id }
  let protRepB : ReplacementId := { kind := .multiplyDamage, object := some pColObj.id }
  let gProtRep0 :=
    (gProt0.createEffect
      (.replacement { id := protRepA, affectedPlayer := p0, kind := .addNoncombatDamage none 1 })
      (cause := some testCause)).createEffect
      (.replacement { id := protRepB, affectedPlayer := p0, kind := .multiplyDamage none 2 })
      (cause := some testCause)
  -- (a) Source-less `dealDamageFrom` itself opens `.chooseReplacement` on `pColObj`:
  let gProtPauseCol :=
    gProtRep0.dealDamageFrom "Nameless" pColObj 1 (source := none) (sourceSnap := none) (cause := some testCause)
  let pauseColSrcNone :=
    match gProtPauseCol.pendingReplacement with
    | some (.dealDamageFrom _ none tid _ _ _ _) => tid == pColObj.id
    | _ => false
  let gProtPauseColDone := mustApply gProtPauseCol p0 (.chooseReplacement protRepA)
  -- Same replacement-paused call on `pAllObj` (`.protection .everything`) is prevented (`0` damage):
  let gProtPauseAll :=
    gProtRep0.dealDamageFrom "Nameless" pAllObj 1 (source := none) (sourceSnap := none) (cause := some testCause)
  let gProtPauseAllDone : Game :=
    match gProtPauseAll.pending with
    | .chooseReplacement .. => mustApply gProtPauseAll p0 (.chooseReplacement protRepA)
    | _ => gProtPauseAll
  -- (b) Source-less `dealDamageFrom` entered while an unrelated `.chooseReplacement` is ALREADY open:
  let openRepA : ReplacementId := { kind := .addNoncombatDamage, object := some pAllObj.id }
  let openRepB : ReplacementId := { kind := .multiplyDamage, object := some pAllObj.id }
  let gProtOpen0 :=
    (gProt0.createEffect
      (.replacement { id := openRepA, affectedPlayer := p1, kind := .addNoncombatDamage none 1 })
      (cause := some testCause)).createEffect
      (.replacement { id := openRepB, affectedPlayer := p1, kind := .multiplyDamage none 2 })
      (cause := some testCause)
  let gProtOpen1 := gProtOpen0.dealDamageToPlayer p1 1 (cause := some testCause)
  let gProtOpen2 :=
    gProtOpen1.dealDamageFrom "Nameless" pColObj 2 (source := none) (sourceSnap := none) (cause := some testCause)
  let rec hasSrcLessDealFrom (tid : ObjectId) : PendingReplacement → Bool
    | .dealDamageFrom _ none id _ _ _ _ => id == tid
    | .seq a b => hasSrcLessDealFrom tid a || hasSrcLessDealFrom tid b
    | _ => false
  let gProtOpenDone := mustApply gProtOpen2 p1 (.chooseReplacement openRepA)
  -- Active `.replacement` `multiplyDamage` with `some redSrcObj.id` matches `effSrc?` from `srcEvent?`
  -- even when `source := none` (e.g. departed LKI source):
  let redSrcDef : CardDef := {
    creature "P57i3 RedSrc" { symbols := #[.colored .red] } #["Goblin"] 1 1 with
  }
  let gRepSrc0 := addPermanent (addPermanent g0 bear p1 p1) redSrcDef p0 p0
  let tgtBear := (gRepSrc0.permanentsOf p1)[0]!
  let redSrcObj := (gRepSrc0.permanentsOf p0)[0]!
  let redSnap := gRepSrc0.snapshot redSrcObj
  let (gRepSrc1, _) := gRepSrc0.move redSrcObj.id (.graveyard p0) none (cause := some testCause)
  let gRepSrc2 :=
    gRepSrc1.createEffect
      (.replacement {
        id := { kind := .multiplyDamage, object := some redSrcObj.id }
        affectedPlayer := p1
        kind := .multiplyDamage (some redSrcObj.id) 2
      })
      (cause := some testCause)
  let gRepSrc3 :=
    gRepSrc2.dealDamageFrom redSrcDef.name (gRepSrc2.object! tgtBear.id) 1
      (source := none) (sourceSnap := some redSnap) (cause := some testCause)
  -- General player protection `(q, dur)` via `Interpreter`: protection from red until EOT!
  let gPlProt0 := addPermanent g0 redSrcDef p1 p1
  let p1RedSrc := (gPlProt0.permanentsOf p1)[0]!
  let gPlProt1 :=
    gPlProt0.applyUnified p0
      { body := .installEffect (.applyRule .untilEndOfTurn (.player (.protectionFrom .you (.color (.literal .red))))) } #[]
  let lifeBeforeProt := (gPlProt1.player p0).life
  let gPlProt2 := gPlProt1.dealDamageToPlayer p0 3 (source := some p1RedSrc) (cause := some testCause)
  let gPlProtEot := gPlProt2.clearTurnActivations
  let gPlProtAfterEot := gPlProtEot.dealDamageToPlayer p0 3 (source := some p1RedSrc) (cause := some testCause)
  let protCompleteOk :=
    (gProt2.object! pColObj.id).status.damage == 2 &&
    (gProt2.object! pAllObj.id).status.damage == 0 &&
    pauseColSrcNone &&
    (gProtPauseColDone.object! pColObj.id).status.damage == 4 &&
    (gProtPauseAllDone.object! pAllObj.id).status.damage == 0 &&
    gProtOpen2.pendingReplacement.any (hasSrcLessDealFrom pColObj.id) &&
    (gProtOpenDone.object! pColObj.id).status.damage == 2 &&
    (gRepSrc3.object! tgtBear.id).status.damage == 2 &&
    gPlProt1.playerProtectedFrom p0 (some p1RedSrc) &&
    (gPlProt2.player p0).life == lifeBeforeProt &&
    !gPlProtEot.playerProtectedFrom p0 (some p1RedSrc) &&
    (gPlProtAfterEot.player p0).life == lifeBeforeProt - 3

  -- 3a(iii). Layer-5 non-battlefield `.colors` & Layer-6 peer/emblem fast paths & CR 305.7 `triggeredAbilities`:
  let gHandCol0 := insertObject g0 bear p0 (.hand p0)
  let handBearId := (gHandCol0.player p0).hand.back!
  let gHandCol1 :=
    gHandCol0.createEffect
      (.layered (.objects #[handBearId]) (.colors .set { blue := true }) .untilEndOfTurn)
      (cause := some testCause)
  -- Peer permanent with `.loseAllAbilities` disables `staticAbilities`, `retainsPrintedAbilities`,
  -- `triggeredAbilities`, and `activatedAbilitiesOf` fast paths on other creatures:
  let dressDownDef : CardDef := {
    name := "P57i3 DressDown"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .hasType .creature } .loseAllAbilities
    ]
  }
  let trigBearDef : CardDef := {
    bear with
    name := "P57i3 TrigBear"
    staticAbilities := #[.creaturesYouControlHave #[Keyword.trample]]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 1)]
    activatedAbilities := #[{ cost := CostSpec.ofItems #[.tapSelf], effect := Effect.gainLife 1 }]
  }
  let gL6Peer0 := addPermanent (addPermanent g0 trigBearDef p0 p0) dressDownDef p0 p0
  let tbObj := (gL6Peer0.permanentsOf p0).find? (·.name == trigBearDef.name) |>.get!
  -- CR 305.7 basic-land-set strips `triggeredAbilities` on a nonbasic land:
  let trigLandDef : CardDef := {
    name := "P57i3 TrigLand"
    types := #[.land]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 1)]
  }
  let gBloodMoon0 := addPermanent g0 trigLandDef p0 p0
  let tlObj := (gBloodMoon0.permanentsOf p0)[0]!
  let gBloodMoon1 :=
    gBloodMoon0.createEffect
      (.layered (.objects #[tlObj.id]) (.types .set #[.land] #[.mountain] #[]) .indefinite)
      (cause := some testCause)
  let layer56Ok :=
    (gHandCol1.colors (gHandCol1.object! handBearId)).contains .blue &&
    (gL6Peer0.staticAbilities tbObj).isEmpty &&
    !gL6Peer0.retainsPrintedAbilities tbObj &&
    (gL6Peer0.triggeredAbilities tbObj).isEmpty &&
    (gL6Peer0.activatedAbilitiesOf tbObj).isEmpty &&
    (gBloodMoon1.triggeredAbilities (gBloodMoon1.object! tlObj.id)).isEmpty

  -- 3b(i). `.turnHistory` (`turnNumber > 1`, `noSourceSentinelId`) & `EvalExpr` `lookBackState?`:
  let gTurn1Ev :=
    g0.record (GameEvent.drew 0 p0 ⟨88⟩ 1 (cause := testCause))
  let lastTurnDrewCond : Condition := .turnHistory (.eventOccurredLastTurn .you (.drewCard 1))
  let gLb0 := addPermanent g0 bear p0 p0
  let lbBear := (gLb0.permanentsOf p0)[0]!
  let gLb1 := gLb0.recordPutCounters lbBear.id .plusOnePlusOne 1 (some p0) (cause := some testCause)
  let recCtrCond : Condition :=
    .exists (.inZones .battlefield (.all #[.named (.literal bear.name), .receivedCounterThisTurn none none]))
  let historyAndLbOk :=
    gTurn1Ev.turnNumber == 1 &&
    !gTurn1Ev.evalTriggerCond p0 none none lastTurnDrewCond &&
    EvalExpr.evalCondition gLb1 { controller := p0 } recCtrCond &&
    !EvalExpr.evalCondition gLb1 { controller := p0, lookBackState? := some gLb0 } recCtrCond

  -- 3b(ii). Layer-6 Flash in `Casting.timingAllowsCast`, opponent-exile `Costs.playManaCost`
  --         `caster` threading, and Layer-3 text changes on `affinityForSubtype`:
  let sorcFlashDef : CardDef := {
    name := "P57i3 SorcFlash"
    manaCost := ManaCost.zero
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gFlash0 := (insertObject g0 sorcFlashDef p0 (.hand p0)).record (GameEvent.turnBegan (g0.turnNumber + 1) p1)
  let gFlash1 := gFlash0.receivePriority p0
  let flashCard := gFlash1.object! (gFlash1.player p0).hand.back!
  let gFlashGranted :=
    gFlash1.createEffect
      (.layered (.objects #[flashCard.id]) (.abilities { keywords := #[Keyword.flash] } .none) .untilEndOfTurn)
      (cause := some testCause)
  -- Opponent-exile cost reduction (`card.controller == none`, owned by `p1`, cast by `p0` via
  -- `PlayPermission { player := p0 }` while `p0` controls 2 Goblins):
  let affSpellDef : CardDef := {
    name := "P57i3 AffSpell"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
    keywords := #[.affinity { zones := .battlefield, pred := .hasSubtype (.literal .goblin) }]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gobDef : CardDef := creature "P57i3 Gob" ManaCost.empty #["Goblin"] 1 1
  let gOppEx0 :=
    insertObject (addPermanent (addPermanent g0 gobDef p0 p0) gobDef p0 p0) affSpellDef p1 .exile
  let oppExCard := (gOppEx0.objects.filter (·.zone == .exile)).back!
  -- `p0` controls 2 Goblins, `p1` controls 0: `playManaCost` with `origPerm := some { player := p0 }`
  -- threads `caster := p0` into `applyCastCostReductions`, reducing `{3}` -> `{1}`!
  let oppExCost := gOppEx0.playManaCost oppExCard affSpellDef (origPerm := some { player := p0 })
  -- Layer-3 text change swapping `Goblin` -> `Elf` changes `affinityForSubtype`:
  let gAffL3 :=
    gOppEx0.createEffect
      (.layered (.objects #[oppExCard.id]) (.text (.replaceCreatureType .goblin .elf)) .untilEndOfTurn)
      (cause := some testCause)
  let oppExCostAfterL3 :=
    gAffL3.playManaCost (gAffL3.object! oppExCard.id) affSpellDef (origPerm := some { player := p0 })
  let fdMorphFace : CardDef := { bear with name := "", manaCost := { symbols := #[.colored .green] } }
  let (fdTypes, fdSupers, fdCols) := gFlash1.faceCdaCharacteristics flashCard fdMorphFace
  let timingAndCostsOk :=
    !gFlash1.timingAllowsCast p0 sorcFlashDef (card? := some flashCard) &&
    gFlashGranted.timingAllowsCast p0 sorcFlashDef (card? := some (gFlashGranted.object! flashCard.id)) &&
    fdTypes == #[.creature] && fdSupers.isEmpty && fdCols == {} &&
    oppExCard.controller.isNone &&
    oppExCost == ManaCost.ofGeneric 1 &&
    oppExCostAfterL3 == ManaCost.ofGeneric 3

  mustHold57i3 "3a_desigPred" desigPredOk &&
  mustHold57i3 "3a_isRingBearerLki" isRingBearerLkiOk &&
  mustHold57i3 "3a_copyPrep" copyPrepOk &&
  mustHold57i3 "3a_protComplete" protCompleteOk &&
  mustHold57i3 "3a_layer56" layer56Ok &&
  mustHold57i3 "3b_historyAndLb" historyAndLbOk &&
  mustHold57i3 "3b_timingAndCosts" timingAndCostsOk &&
  mustHold57i3 "3.replay"
    (replayOk57i3 #[gCopyPrep2, gProt2, gProtPauseColDone, gProtPauseAllDone, gProtOpenDone,
      gRepSrc3, gPlProt2, gPlProtAfterEot, gHandCol1, gBloodMoon1, gLb1, gFlashGranted, gAffL3])

end Phase57Item3EventAlignment

/-! ### Phase 57 Item 4a: Critical `canPayFromSources` `.colorAmong #[]` (Mox Amber) &
`prop?`-reserved collapse + `hasUsableZeroOutputTapManaAbility`, `.discardTwo` bounced-token
softlock & discard skip-logs, and `defaultChoiceAction` / `.mayCastUpToFromExile` /
`mayCastFromLookedError` / `castFreeCopy` / `VisionQuest` / `.creaturesToBattlefield` /
`Interpreter` non-card guards -/
section Phase57Item4EventAlignment

private def mustHold57i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase57Item4EventAlignment failed: {label}"

private def replayOk57i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand afterDraw p0

  -- 4a(i). [Critical] `canPayFromSources` with `.colorAmong #[]` (Mox Amber with no legendary
  --        creature/planeswalker) does NOT collapse to `false` when Forest can pay `{G}`,
  --        AND `hasUsableZeroOutputTapManaAbility` is `true` for untapped Mox Amber!
  let moxAmberDef : CardDef := {
    name := "P57i4 MoxAmber"
    supertypes := #[.legendary]
    types := #[.artifact]
    activatedAbilities := #[
      ActivatedAbility.manaAbility
        (.colorAmong (.colorsAmong .legendaryCreaturesAndPlaneswalkersYouControl) false)
    ]
  }
  let gSpellDef : CardDef := {
    name := "P57i4 GreenInstant"
    manaCost := { symbols := #[.colored .green] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gMox0 := insertObject (addPermanent (addPermanent g0 moxAmberDef p0 p0) forest p0 p0) gSpellDef p0 (.hand p0)
  let moxObj := (gMox0.permanentsOf p0).find? (·.name == moxAmberDef.name) |>.get!
  let moxSpellId := (gMox0.player p0).hand.back!
  let gMoxCast := mustApply gMox0 p0 (.cast moxSpellId)
  let moxSources := gMox0.manaSources p0
  -- Also test `canPayFromSources` directly when an empty-choice source OR a `prop?`-reserved
  -- source (`teamworkCreatures`) is included alongside a usable Forest:
  let gTwoForest := addPermanent gMox0 forest p0 p0
  let twoForests := (gTwoForest.permanentsOf p0).filter (·.name == forest.name)
  let fReserved := twoForests[0]!
  let fFree := twoForests[1]!
  let reservedProp : ProposedSpell :=
    { gMoxCast.proposedSpell.get! with teamworkCreatures := #[fReserved.id] }
  let moxDirectPayOk :=
    gMox0.canPayFromSources {} { symbols := #[.colored .green] }
      ((moxObj, anyColorMana) :: moxSources.toList) &&
    gTwoForest.canPayFromSources {} { symbols := #[.colored .green] }
      [(fReserved, #[.colored .green]), (fFree, #[.colored .green])]
      (prop? := some reservedProp)
  let moxAndZeroOutOk :=
    (gMox0.manaAbilitiesOf moxObj).isEmpty &&
    gMox0.hasUsableZeroOutputTapManaAbility p0 &&
    moxDirectPayOk &&
    (match gMoxCast.pending with | .activateManaAbilities q => q == p0 | _ => false)

  -- 4a(ii). `.discardTwo` bounced-token softlock & discard skip-logs:
  let gobTokDef : CardDef := {
    creature "P57i4 HandTok" ManaCost.empty #["Goblin"] 1 1 with
    isToken := true
  }
  let (gTokHand0, t1) := g0.createOneToken p0 gobTokDef (cause := some testCause)
  let (gTokHand1, t1Id) := gTokHand0.move t1.id (.hand p0) none (cause := some testCause)
  let (gTokHand2, t2) := gTokHand1.createOneToken p0 gobTokDef (cause := some testCause)
  let (gTokHand3, _) := gTokHand2.move t2.id (.hand p0) none (cause := some testCause)
  let gTokHand4 := insertObject gTokHand3 bear p0 (.hand p0)
  -- `p0` has 3 objects in hand (2 bounced tokens + 1 real Bear): `discardableHandIds.size == 1 ≤ 2`,
  -- so `.discardTwo` redirect when `p1` concedes does NOT softlock on `p0`!
  let gDiscTwoPrompt :=
    gTokHand4.change (.pending (.resolutionChoice p1 (.discardTwo p1 #[p0] 0)))
  let gDiscTwoAfter := mustApply gDiscTwoPrompt p1 .concede
  let discardTwoTokenOk :=
    (gTokHand4.player p0).hand.size == 3 &&
    (gTokHand4.discardableHandIds p0).size == 1 &&
    gDiscTwoAfter.pending == .none

  -- 4a(iii). `defaultChoiceAction` (`.mayCastCascade`, `.mayCastCards`, `.mayCastFromGraveyard`)
  --          skips uncastable tokens without panicking in `Mtg.Engine.applyIdle`, and
  --          `castFreeCopy` / `.mayCastUpToFromExile` / `mayCastFromLookedError` reject tokens/copies:
  let (gExTok0, exTok) := g0.createOneToken p0 gobTokDef (cause := some testCause)
  let (gExTok1, exTokId) := gExTok0.move exTok.id .exile none (cause := some testCause)
  let gCascTokIdle :=
    Mtg.Engine.applyIdle
      (gExTok1.change (.pending (.resolutionChoice p0 (.mayCastCascade exTokId #[]))))
  let gMayCardsTokIdle :=
    Mtg.Engine.applyIdle
      (gExTok1.change (.pending (.resolutionChoice p0 (.mayCastCards #[exTokId] false false))))
  let (gGyTok0, gyTok) := g0.createOneToken p0 gobTokDef (cause := some testCause)
  let (gGyTok1, gyTokId) := gGyTok0.move gyTok.id (.graveyard p0) none (cause := some testCause)
  let gGyCastTokIdle :=
    Mtg.Engine.applyIdle
      (gGyTok1.change (.pending (.resolutionChoice p0 (.mayCastFromGraveyard #[gyTokId]))))
  let gMayUpToPrompt :=
    gExTok1.change (.pending (.resolutionChoice p0 (.mayCastUpToFromExile #[exTokId] 1)))
  let mayUpToRejectsTok := !(gMayUpToPrompt.apply p0 (.cast exTokId)).isOk
  let lookedRejectsTok := (gExTok1.mayCastFromLookedError p0 #[exTokId] 5 exTokId).isSome
  let gCastCopyPrompt :=
    gTokHand1.change (.pending (.resolutionChoice p0 (.castCopiesFree #[t1Id] 5 1)))
  let castFreeCopyRejectsNonExile := !(gCastCopyPrompt.apply p0 (.cast t1Id)).isOk
  let castGuardsOk :=
    gCascTokIdle.pending == .none && gCascTokIdle.stack.isEmpty &&
    gMayCardsTokIdle.pending == .none && gMayCardsTokIdle.stack.isEmpty &&
    gGyCastTokIdle.pending == .none && gGyCastTokIdle.stack.isEmpty &&
    mayUpToRejectsTok && lookedRejectsTok && castFreeCopyRejectsNonExile

  -- 4a(iv). Remaining non-card leaks: `beginVisionQuest`/`finishVisionQuest`, `Interpreter`
  --         `.reveal` / hand choice moves ignore bounced tokens, and `permSpec.copyAndCast` does
  --         NOT turn an exiled token into a castable copy:
  let artTokDef : CardDef := {
    creature "P57i4 ArtTok" ManaCost.empty #["Construct"] 1 1 with
    types := #[.artifact, .creature]
    isToken := true
  }
  let (gArtTok0, artTok) := g0.createOneToken p0 artTokDef (cause := some testCause)
  let (gArtTokGy, artTokGyId) := gArtTok0.move artTok.id (.graveyard p0) none (cause := some testCause)
  let gVqDone := gArtTokGy.beginVisionQuest p0 1
  let gVqFinDone := gArtTokGy.finishVisionQuest p0 (some artTokGyId) 1 false
  let gRevTokDone :=
    gTokHand1.applyUnified p0
      { body := .player (.reveal .you (.inZones (.handOf .you) .anyObject)) } #[]
  let gCopyCastTok :=
    gExTok1.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .ofPlayer .you } .anyObject)
          { copyAndCast := true }) } #[]
  let newRevLogs := gRevTokDone.log.extract gTokHand1.log.size gRevTokDone.log.size
  let remainingNonCardOk :=
    !(match gVqDone.pending with | .resolutionChoice _ (.visionQuestZones ..) => true | _ => false) &&
    gVqDone.log.any (·.contains "finds no artifact creature card") &&
    gVqFinDone.log.any (·.contains "That card can't be found") &&
    (gVqFinDone.permanentsOf p0).isEmpty &&
    !newRevLogs.any (·.contains gobTokDef.name) &&
    gCopyCastTok.pending == .none &&
    gCopyCastTok.stack.isEmpty

  mustHold57i4 "4a_moxAndZeroOut" moxAndZeroOutOk &&
  mustHold57i4 "4a_discardTwoToken" discardTwoTokenOk &&
  mustHold57i4 "4a_castGuards" castGuardsOk &&
  mustHold57i4 "4a_remainingNonCard" remainingNonCardOk &&
  mustHold57i4 "4.replay"
    (replayOk57i4 #[gMoxCast, gDiscTwoAfter, gCascTokIdle, gMayCardsTokIdle, gGyCastTokIdle,
      gVqDone, gVqFinDone, gRevTokDone, gCopyCastTok])

end Phase57Item4EventAlignment

end Mtg.Engine.EventTests
