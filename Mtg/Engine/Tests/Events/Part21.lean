import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

/-! ### Phase 55 Item 1: `.seq` priority & deferral-tail probe parity, `finishAndGrantPriority`
post-drain `pendingPriority`, `afterWardResolved` / `classifyAfterWardResolvedFuel`,
runtime continuation-ordering fixes (`becomeCast`, `completeTurnFaceUp`, `wrapOuter`,
`PriorityActions.finishProposedSpell`, `Decisions.putCardsOnBottom`), `drainProbePausedStep`
`.chooseLegend` preservation, `.receivePriority` / `receivePriorityOutcome`, mana-ability &
`probeRestorePendingCore` & `stepCanReverseProposal` leaves, and concede `.chooseReplacement` draining -/
section Phase55Item1EventAlignment

private def mustHold55i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase55Item1EventAlignment failed: {label}"

private def replayOk55i1 (gs : Array Game) : Bool :=
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
    name := "P55i1 ZeroInst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let legBearDef : CardDef := { bear with name := "P55i1 LegBear", supertypes := #[.legendary] }
  let ridA : ReplacementId := { kind := .replaceDraw, player := some p0 }
  let ridB : ReplacementId := { kind := .replaceDraw, player := some p1 }

  -- 1a(i). Pure post-log tails transparent to `endsWithPriorityGrant` / `endsWithFinishResolutionChoice` /
  --        `endsWithNonProposalPriorityGrant`, plus `.seq` pre-`b` check and newly opened `.chooseReplacement` probing:
  let logTail1 : PendingReplacement := .logMessage "tail"
  let logTail2 : PendingReplacement := .finishPostStep (.logExpiredPlayFromExile #[] 0)
  let seqRecvLog : PendingReplacement := .seq (.receivePriority p2) logTail1
  let seqFrcLog : PendingReplacement := .seq .finishResolutionChoice logTail2
  let seqEventHelpersOk :=
    seqRecvLog.endsWithPriorityGrant false &&
    seqRecvLog.endsWithNonProposalPriorityGrant &&
    seqFrcLog.endsWithFinishResolutionChoice &&
    seqFrcLog.endsWithPriorityGrant false &&
    g4.continuationGrantsPriority false seqRecvLog &&
    g4.priorityRecipientOfContinuation? false seqRecvLog == some p2 &&
    g4.firstPriorityGrantRecipient? false seqRecvLog == some (some p2)

  -- Newly opened `.chooseReplacement` inside `.seq a b` probes `resA.game.chainPendingReplacement b`:
  let headWolfDef : CardDef := {
    bear with name := "P55i1 HeadWolf", staticAbilities := #[.exileOppDeathCreateWolf]
  }
  let gRepSeq0 := addPermanent (addPermanent g4 bear p0 p0) headWolfDef p1 p1
  let repBearId := (gRepSeq0.permanentsOf p0)[0]!.id
  let gRepSeq1 := gRepSeq0.recordPutCounters repBearId .finality 1 (some p0) (cause := some testCause)
  let moveDieCont : PendingReplacement :=
    .move repBearId (.graveyard p0) none (some .destroy) none false false false none false false false #[] (some .bottom) 0 true none none none none true none #[] (some testCause)
  let seqOpenRep := PendingReplacement.seq moveDieCont (.receivePriority p2)
  let seqOpenRepOk :=
    gRepSeq1.continuationGrantsPriority false seqOpenRep &&
    gRepSeq1.continuationSettlesControlFlow false seqOpenRep &&
    gRepSeq1.priorityRecipientOfContinuation? false seqOpenRep == some p2 &&
    gRepSeq1.firstPriorityGrantRecipient? false seqOpenRep == some (some p2)

  -- 1a(ii). `.seq` `(followedByFinishChoice, followedByExplicitPriority?)` reversal threading:
  let sorc1Def : CardDef := {
    name := "P55i1 Sorc1"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gRevBase0 :=
    (insertObject (addPermanent (emptyHand g4 p0) forest p0 p0) sorc1Def p0 (.hand p0)).change
      (.pendingPriority (some p2))
  let tmpForestId := (gRevBase0.permanentsOf p0)[0]!.id
  let gRevCast := mustApply gRevBase0 p0 (.cast (gRevBase0.player p0).hand.back!)
  let (gRevNoLand, _) := gRevCast.move tmpForestId .exile none (cause := some testCause)
  let gRevProp := gRevNoLand.change (.pending .none)
  let revCostLeaf : PendingReplacement :=
    .finishPostStep (.resumeProposalCostAfterLeave p0 (.discardForAdditionalCost p0))
  let seqRevExplicitP3 : PendingReplacement := .seq revCostLeaf (.receivePriority p3)
  let seqRevFinishChoice : PendingReplacement := .seq revCostLeaf .finishResolutionChoice
  let gSeqRevP3Run := gRevProp.resumePendingReplacement seqRevExplicitP3
  let gSeqRevFcRun := gRevProp.resumePendingReplacement seqRevFinishChoice
  let seqReversalThreadingOk :=
    gRevProp.continuationGrantsPriority false seqRevExplicitP3 &&
    gRevProp.priorityRecipientOfContinuation? false seqRevExplicitP3 == some p3 &&
    gRevProp.firstPriorityGrantRecipient? false seqRevExplicitP3 == some (some p3) &&
    gSeqRevP3Run.priority == p3 &&
    gRevProp.continuationGrantsPriority false seqRevFinishChoice &&
    gRevProp.firstPriorityGrantRecipient? false seqRevFinishChoice == some none &&
    gSeqRevFcRun.priority == p2

  -- 1a(iii). `finishAndGrantPriority` post-drain `pendingPriority` preservation:
  -- Draining `.finishPostCast p1 true false false` opens `.chooseLegend p0` while `Entering.receivePriority p1`
  -- sets `pendingPriority := some p1`; `finishAndGrantPriority p2` must NOT overwrite `pendingPriority` with `p2`!
  let gPostDrainPrio0 :=
    (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishPostCast p1 true false false))
    ]
  let gPostDrainPrio1 := gPostDrainPrio0.finishAndGrantPriority p2
  let postDrainPrioOk :=
    (match gPostDrainPrio1.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
    gPostDrainPrio1.pendingPriority == some p1

  -- 1a(iv). `Decisions.putCardsOnBottom` preserves `pendingPriority` / drains `outerPendingReplacements`
  --         when `mulliganToBottom` is empty on the `currentInterpWait?.isNone` arm:
  let gBot0 :=
    (insertObject (emptyHand g4 p0) bear p0 (.hand p0)).changes #[
      .pending (.putOnBottom p0 1),
      .pendingPriority (some p2),
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p3)
    ]
  let botCardId := (gBot0.player p0).hand[0]!
  let gBot1 := mustApply gBot0 p0 (.putOnBottom #[botCardId])
  let putBottomOk :=
    gBot1.pending == .none &&
    gBot1.priority == p3

  -- 1b(i). `drainProbePausedStep` preserves fresh `.chooseLegend` prompts (does not auto-resolve them):
  let gLegSba0 :=
    (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0).record
      (GameEvent.playerLost g4.turnNumber p2 .lifeZeroOrLess)
  let leaveWithFreshLeg : PendingReplacement := .leavePlayersWhoLost none false #[] none
  let freshLegendPreservedOk :=
    !gLegSba0.continuationGrantsPriority false leaveWithFreshLeg &&
    gLegSba0.continuationSettlesControlFlow false leaveWithFreshLeg

  -- 1b(ii). `.receivePriority p1` routed through `classifyFinishAndGrantPriority` when outer holds `.receivePriority p2`,
  --         and `receivePriorityOutcome` maps implicit `some none` to `some p1` when `!hadEntryPending`:
  let gRecvOuter0 :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p2)
    ]
  let gRecvOuterRun := gRecvOuter0.resumePendingReplacement (.receivePriority p1)
  let gRecvNoEntryEx0 := insertObject g4 zeroInstDef p0 .exile
  let exCardId := (gRecvNoEntryEx0.objects.filter (·.zone == .exile)).back!.id
  let gRecvImplicitNoEntry :=
    gRecvNoEntryEx0.changes #[
      .pushContinuationFrame {},
      .pendingMayCastFromExile (some (p0, #[exCardId], 1))
    ]
  let receivePriorityParityOk :=
    gRecvOuter0.priorityRecipientOfContinuation? false (.receivePriority p1) == some p2 &&
    gRecvOuterRun.priority == p2 &&
    !gRecvImplicitNoEntry.continuationGrantsPriority false (.receivePriority p1) &&
    gRecvImplicitNoEntry.continuationSettlesControlFlow false (.receivePriority p1)

  -- 1b(iii). Mana-ability `.dealDamageToPlayer` / `.runModalManaEffect` / `.endProposalAction` probes:
  let gModalMana0 := addPermanent g4 bear p0 p0
  let modalSrcId := (gModalMana0.permanentsOf p0)[0]!.id
  let modalPromptEff : Effect := {
    body := .optional .you none (Effect.gainLife 1).body .noop
  }
  let modalManaCont : PendingReplacement := .runModalManaEffect p0 modalSrcId modalPromptEff
  let painDmgCont : PendingReplacement := .dealDamageToPlayer p1 2 none false (some testCause)
  let manaProbesOk :=
    gModalMana0.continuationSettlesControlFlow false modalManaCont &&
    !gModalMana0.continuationGrantsPriority false modalManaCont &&
    !g4.continuationSettlesControlFlow false painDmgCont &&
    !g4.continuationSettlesControlFlow false (.endProposalAction false)

  -- 1b(iv). `probeRestorePendingCore` `.tricksterLibrary` runs `conniveTricksterTarget` (opens discard prompt -> settles):
  let gTrick0 := mustApply (addPermanent (insertObject g4 bear p0 (.library p0)) bear p0 p0) p2 .concede
  let trickBearId := (gTrick0.permanentsOf p0)[0]!.id
  let trickRestore : PendingReplacement :=
    .restorePending (.resolutionChoice p2 (.tricksterLibrary p0 trickBearId (some trickBearId))) false
  let gTrickRun := gTrick0.resumePendingReplacement trickRestore
  let trickProbeOk :=
    gTrick0.continuationSettlesControlFlow false trickRestore &&
    !gTrick0.continuationGrantsPriority false trickRestore &&
    gTrickRun.pending != .none

  -- 1b(v). Concede classifiers drain `.chooseReplacement` (finding priority grant) while stopping on `.chooseLegend`:
  let gConcedeLeg0 := addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0
  let fcRunSba : PendingReplacement := .finishConcede false (some p1) none none false #[] none
  let concedeLegendStopsOk :=
    !gConcedeLeg0.continuationGrantsPriority false fcRunSba &&
    gConcedeLeg0.continuationSettlesControlFlow false fcRunSba

  -- 1b(vi). `finishPostCastOutcome` returns `.noGrant` on non-settling `.chooseReplacement` when `!grantPriority`:
  let gRepNonSettle :=
    g4.changes #[
      .pushContinuationFrame {},
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]
  let postCastNonSettleOk :=
    !gRepNonSettle.continuationSettlesControlFlow false (.finishPostCast p0 false true false)

  mustHold55i1 "1a_seqEventHelpers" seqEventHelpersOk &&
  mustHold55i1 "1a_seqOpenRep" seqOpenRepOk &&
  mustHold55i1 "1a_seqReversalThreading" seqReversalThreadingOk &&
  mustHold55i1 "1a_postDrainPrio" postDrainPrioOk &&
  mustHold55i1 "1a_putBottom" putBottomOk &&
  mustHold55i1 "1b_freshLegendPreserved" freshLegendPreservedOk &&
  mustHold55i1 "1b_receivePriorityParity" receivePriorityParityOk &&
  mustHold55i1 "1b_manaProbes" manaProbesOk &&
  mustHold55i1 "1b_trickProbe" trickProbeOk &&
  mustHold55i1 "1b_concedeLegendStops" concedeLegendStopsOk &&
  mustHold55i1 "1b_postCastNonSettle" postCastNonSettleOk &&
  mustHold55i1 "1.replay"
    (replayOk55i1 #[gSeqRevP3Run, gSeqRevFcRun, gPostDrainPrio1, gBot1, gRecvOuterRun, gTrickRun])

end Phase55Item1EventAlignment

/-! ### Phase 55 Item 2: `hasPlayFromExileLoggedInSlice` multi-group & `startIdx`-scoped
`loggedInSlice`, `finishConcedePriority` SBA-loser `.playFromExile` logs,
`emitExpiredPlayFromExileLogs` pre-priority-grant ordering, `runEndControlExileLoop` `priorCont?`
ordering, multi-move / SBA / turn `deferPlayFromExileLogs` threading, and `.control`-expiry
reconciliation in `restoreControlUntilSourceLeaves` / `expireWhileSourceEffects` / `expireEffectById` -/
section Phase55Item2EventAlignment

private def mustHold55i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase55Item2EventAlignment failed: {label}"

private def replayOk55i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 2a(i). `hasPlayFromExileLoggedInSlice` via `emitExpiredPlayFromExileLogs`:
  --        (a) Ambiguous 2-object group retires once logged twice, so a 3rd same-named card expiring
  --            emits its log cleanly without being shadowed;
  --        (b) `loggedInSlice` is scoped to `i ≥ startIdx`, so a reactivated permission expiring a second
  --            time at `i ≥ startIdx` is NOT falsely suppressed by an earlier log before `startIdx`.
  let gEx3 := insertObject (insertObject (insertObject g4 bear p0 .exile) bear p0 .exile) bear p0 .exile
  let exIds := (gEx3.objects.filter (·.zone == .exile)).map (·.id)
  let idA := exIds[0]!
  let idB := exIds[1]!
  let idC := exIds[2]!
  let bearExpMsg := s!"{bear.name} can no longer be played from exile"
  let countBearExpLogs (g : Game) := (g.log.filter (· == bearExpMsg)).size
  let gExGrp1 :=
    (gEx3.createEffect (.permission (some p0) (.playFromExile idA { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile idB { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let eidA := gExGrp1.activeEffects[gExGrp1.activeEffects.size - 2]!.1
  let eidB := gExGrp1.activeEffects[gExGrp1.activeEffects.size - 1]!.1
  let gExGrp2 :=
    ((gExGrp1.expireEffectById eidA (cause := some testCause) (deferPlayFromExileLogs := true)).expireEffectById eidB
        (cause := some testCause) (deferPlayFromExileLogs := true))
      |>.logMsg bearExpMsg
      |>.logMsg bearExpMsg
  -- Re-calling `emitExpiredPlayFromExileLogs` over the already-logged `[0..)` slice adds 0 duplicates:
  let gExGrp2Check := gExGrp1.emitExpiredPlayFromExileLogs gExGrp2 0
  let sliceStart := gExGrp2.events.size
  let gExGrp3 :=
    gExGrp2.createEffect (.permission (some p0) (.playFromExile idC { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let eidC := gExGrp3.activeEffects.back!.1
  let gExGrp4Raw := gExGrp3.expireEffectById eidC (cause := some testCause) (deferPlayFromExileLogs := true)
  let gExGrp4 := gExGrp3.emitExpiredPlayFromExileLogs gExGrp4Raw sliceStart
  -- Second expiry of `idA` after `sliceStart2` must NOT be suppressed by pre-`sliceStart2` log:
  let sliceStart2 := gExGrp4.events.size
  let gExReact1 :=
    gExGrp4.createEffect (.permission (some p0) (.playFromExile idA { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let eidA2 := gExReact1.activeEffects.back!.1
  let gExReact2Raw := gExReact1.expireEffectById eidA2 (cause := some testCause) (deferPlayFromExileLogs := true)
  let gExReact2 := gExReact1.emitExpiredPlayFromExileLogs gExReact2Raw sliceStart2
  let hasLoggedDedupOk :=
    countBearExpLogs gExGrp2 == 2 &&
    countBearExpLogs gExGrp2Check == 2 &&
    countBearExpLogs gExGrp4 == 3 &&
    countBearExpLogs gExReact2 == 4

  -- 2a(ii). `emitExpiredPlayFromExileLogs` inserts deferred `.logExpiredPlayFromExile` BEFORE
  --         trailing `.receivePriority`, preserving `endsWithPriorityGrant` and pre-priority log order:
  let gEmit0 := insertObject g4 bear p0 .exile
  let emitExId := (gEmit0.objects.filter (·.zone == .exile)).back!.id
  let gEmitPerm :=
    (gEmit0.createEffect (.permission (some p0) (.playFromExile emitExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile emitExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let emitEid := gEmitPerm.activeEffects.back!.1
  let emitStart := gEmitPerm.events.size
  let gEmitPaused :=
    (gEmitPerm.expireEffectById emitEid (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.receivePriority p1)),
      .pending (.chooseReplacement p0 #[])
    ]
  let gEmitDeferred := gEmitPerm.emitExpiredPlayFromExileLogs gEmitPaused emitStart
  let emitPrePrioOk :=
    match gEmitDeferred.pendingReplacement with
    | some (.seq (.finishPostStep (.logExpiredPlayFromExile ids _)) (.receivePriority q)) =>
      ids.contains emitExId && q == p1 &&
        (PendingReplacement.seq (.finishPostStep (.logExpiredPlayFromExile ids emitStart)) (.receivePriority q)).endsWithPriorityGrant false
    | _ => false

  -- 2a(iii). `Decisions.finishConcedePriority` emits `.playFromExile` expiry log for SBA-losing player:
  let gConSba0 := insertObject (addPermanent g4 bear p2 p2) bear p0 .exile
  let conSbaSrcId := (gConSba0.permanentsOf p2)[0]!.id
  let conSbaExId := (gConSba0.objects.filter (·.zone == .exile)).back!.id
  let gConSba1 :=
    (gConSba0.createEffect
      (.permission (some p0) (.playFromExile conSbaExId { player := p0 }) (.whileSourceOnBattlefield conSbaSrcId))
      (cause := some testCause)).loseLife p2 20
  let gConSbaDone := mustApply gConSba1 p1 .concede
  let conSbaLogOk :=
    (gConSbaDone.player p1).leftTheGame &&
    (gConSbaDone.player p2).leftTheGame &&
    gConSbaDone.log.contains bearExpMsg

  -- 2b(i). `Core.restoreControlUntilSourceLeaves` emits `"returns to <player>'s control"` BEFORE CR 800.4c
  --        exile reconciliation without duplicating return logs:
  let gCtrlOrd0 := addPermanent (addPermanent (addPermanent g4 bear p0 p0) bear p1 p1) bear p2 p2
  let srcP0Id := (gCtrlOrd0.permanentsOf p0)[0]!.id
  let tgtP1Id := (gCtrlOrd0.permanentsOf p1)[0]!.id
  let tgtP2Id := (gCtrlOrd0.permanentsOf p2)[0]!.id
  let gCtrlOrd1 :=
    ((gCtrlOrd0.createEffect
      (.layered (.objects #[tgtP1Id]) (.control p2) (.whileSourceOnBattlefield srcP0Id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[tgtP2Id]) (.control p0) (.whileSourceOnBattlefield tgtP1Id))
      (cause := some testCause))
  let logBefore := gCtrlOrd1.log.size
  let (gCtrlOrd2, _) := gCtrlOrd1.move srcP0Id (.graveyard p0) none (cause := some testCause)
  let newLogs := gCtrlOrd2.log.extract logBefore gCtrlOrd2.log.size
  let returnLogCount :=
    (newLogs.filter (fun s => s.endsWith s!"returns to {(gCtrlOrd2.player p1).name}'s control")).size
  let restoreControlOrderOk :=
    gCtrlOrd2.controlledBy (gCtrlOrd2.object! tgtP1Id) p1 &&
    returnLogCount == 1

  -- 2b(ii). `Core.expireEffectById` on a `.control` effect with `reconcileControl := true` reconciles CR 701.54a
  --         `.ringBearer` loss (not only combat removal):
  let gRing0 := addPermanent g4 bear p0 p0
  let ringBearId := (gRing0.permanentsOf p0)[0]!.id
  let gRing1a := gRing0.createEffect (.control ringBearId p1) (cause := some testCause)
  let ctrlEid := gRing1a.activeEffects.back!.1
  let gRing1 :=
    gRing1a.record
      (GameEvent.designation gRing1a.turnNumber (gRing1a.snapshot (gRing1a.object! ringBearId))
        .ringBearer true (cause := testCause))
  let gRing2 := gRing1.expireEffectById ctrlEid (cause := some testCause) (reconcileControl := true)
  let expireControlRingOk :=
    (gRing1.player p1).ringBearerId == some ringBearId &&
    gRing2.controlledBy (gRing2.object! ringBearId) p0 &&
    (gRing2.player p1).ringBearerId == none

  mustHold55i2 "2a_hasPlayFromExileLoggedDedup" hasLoggedDedupOk &&
  mustHold55i2 "2a_emitPrePrioPlacement" emitPrePrioOk &&
  mustHold55i2 "2a_finishConcedeSbaLoserLog" conSbaLogOk &&
  mustHold55i2 "2b_restoreControlReturnLogOrder" restoreControlOrderOk &&
  mustHold55i2 "2b_expireEffectByIdControlReconcile" expireControlRingOk &&
  mustHold55i2 "2.replay"
    (replayOk55i2 #[gExGrp4, gExReact2, gEmitDeferred, gConSbaDone, gCtrlOrd2, gRing2])

end Phase55Item2EventAlignment

/-! ### Phase 55 Item 3: `evalTriggerCond` & `viewHasDesignation` LKI, protection blocking &
player damage & concrete Layer-6 resolution, Layer-7 `liveObjectHasExtraKeyword` parity,
`lkiCombatWindow` & `.permanentLeftBattlefield` `ceasedToExist`, Layer-5 color CDAs &
`spellFaceView` CDAs, `.otherSpellsManaValueThisTurn` `ownFallback` parity, `actualPrintedManaCost?`
MDFC/prepare & `coreSorceryTimingOk`, and copied-spell target LKI -/
section Phase55Item3EventAlignment

private def mustHold55i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase55Item3EventAlignment failed: {label}"

private def replayOk55i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := afterDraw

  -- 3a(i). `Core.evalTriggerCond` checks `o.isLkiSnapshot` first & preserves `wasPreparedAtDeparture`,
  --        and `EvalExpr.viewHasDesignation` handles `.lki _ / .prepared`:
  let gPrep0 := addPermanent g0 bear p0 p0
  let prepId := (gPrep0.permanentsOf p0)[0]!.id
  let gPrepLive :=
    gPrep0.record
      (GameEvent.designation gPrep0.turnNumber (gPrep0.snapshot (gPrep0.object! prepId))
        .prepared true (cause := testCause))
  let lkiNotPrep : GameObject :=
    { gPrepLive.object! prepId with
      status := { (gPrepLive.object! prepId).status with prepared := false }
      isLkiSnapshot := true }
  let (gPrepLeft, _) := gPrepLive.move prepId (.graveyard p0) none (cause := some testCause)
  let isPrepCond : Condition := .forAll .this (.hasDesignation .prepared)
  let lkiView : ObjectView := .lki (gPrepLive.snapshot (gPrepLive.object! prepId))
  let evalTrigAndDesigOk :=
    -- Explicit `isLkiSnapshot` is NOT overridden by live prepared permanent:
    !gPrepLive.evalTriggerCond p0 (some lkiNotPrep) none isPrepCond &&
    -- Departed prepared permanent's live-miss LKI fallback preserves `.prepared`:
    gPrepLeft.evalTriggerCond p0 (some { gPrepLive.object! prepId with status := {} }) none isPrepCond &&
    -- `viewHasDesignation` checks `wasPreparedAtDeparture` for `.lki`:
    EvalExpr.evalObjectPred gPrepLeft { controller := p0 } lkiView (.hasDesignation .prepared)

  -- 3a(ii). `Core.canBlock` CR 702.16f protection & `Damage.replaceDamage` CR 702.16e player protection:
  let redGoblinDef : CardDef := {
    creature "P55i3 RedGoblin" { symbols := #[.colored .red] } #["Goblin"] 2 2 with
    types := #[.creature]
  }
  let protRedBearDef : CardDef := {
    bear with
    name := "P55i3 ProtRedBear"
    keywords := #[.protection (.color (.literal .red))]
  }
  let protPlayerRedDef : CardDef := {
    name := "P55i3 RedWard"
    types := #[.enchantment]
    staticAbilities := #[.ruleModifying none (.player (.protectionFrom .you (.color (.literal .red))))]
  }
  let gProt0 := addPermanent (addPermanent g0 protRedBearDef p0 p0) redGoblinDef p1 p1
  let atkProt := (gProt0.permanentsOf p0)[0]!
  let blkRed := (gProt0.permanentsOf p1)[0]!
  let gPlayerProt0 := addPermanent (addPermanent g0 protPlayerRedDef p0 p0) redGoblinDef p1 p1
  let redSrc := (gPlayerProt0.permanentsOf p1)[0]!
  let gPlayerProtDmg := gPlayerProt0.dealDamageToPlayer p0 3 (source := some redSrc) (cause := some testCause)
  let protBlockAndPlayerDmgOk :=
    !gProt0.canBlock blkRed atkProt &&
    (gPlayerProtDmg.player p0).life == (gPlayerProt0.player p0).life

  -- 3a(iii). Concrete Layer-6 `.protection .chosenCardType` & `.protection (.color .chosenOnSource)`:
  --          `em1` (instant) stripped by Layer-6 ability removal, then `em2` (sorcery) grants
  --          `.protection .chosenCardType` -> permanent has protection from sorcery ONLY (not leaked instant)!
  let grantProtChosenTypeDef : CardDef := {
    name := "P55i3 ProtTypeGrant"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] }
        (.grantKeywords #[.protection .chosenCardType])
    ]
  }
  let grantProtChosenColorDef : CardDef := {
    name := "P55i3 ProtColorGrant"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] }
        (.grantKeywords #[.protection (.color .chosenOnSource)])
    ]
  }
  let instCardDef : CardDef := { name := "P55i3 Inst", types := #[.instant] }
  let sorcCardDef : CardDef := { name := "P55i3 Sorc", types := #[.sorcery] }
  let (gL6Prot0a, em1) := g0.allocObject grantProtChosenTypeDef p0 .battlefield (some p0) { chosenCardType := some .instant }
  let (gL6Prot0b, _) := gL6Prot0a.allocObject grantProtChosenTypeDef p0 .battlefield (some p0) { chosenCardType := some .sorcery }
  let gL6Prot1 := addPermanent gL6Prot0b bear p0 p0
  let targetBearId := (gL6Prot1.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  -- Strip `em1`'s abilities via Layer-6 continuous effect:
  let gL6Prot2 :=
    gL6Prot1.createEffect
      (.layered (.objects #[em1.id]) (.abilities {} .all) .indefinite)
      (cause := some testCause)
  let gL6ProtInst := insertObject gL6Prot2 instCardDef p1 .stack
  let gL6ProtSorc := insertObject gL6Prot2 sorcCardDef p1 .stack
  let instObj := (gL6ProtInst.objects.filter (·.zone == .stack)).back!
  let sorcObj := (gL6ProtSorc.objects.filter (·.zone == .stack)).back!
  -- Granting source's `chosenColor` (not target's `chosenColor`):
  let (gL6Col0a, _) := g0.allocObject grantProtChosenColorDef p0 .battlefield (some p0) { chosenColor := some .red }
  let (gL6Col0b, colBear) := gL6Col0a.allocObject bear p0 .battlefield (some p0) { chosenColor := some .blue }
  let gL6Col1 := addPermanent gL6Col0b redGoblinDef p1 p1
  let concreteL6ProtOk :=
    !gL6ProtInst.protectedFrom (gL6ProtInst.object! targetBearId) instObj &&
    gL6ProtSorc.protectedFrom (gL6ProtSorc.object! targetBearId) sorcObj &&
    gL6Col1.protectedFrom (gL6Col1.object! colBear.id) (gL6Col1.permanentsOf p1)[0]! &&
    grantProtChosenTypeDef.hasProtectionFromChosenCardType

  -- 3a(iv). Layer-7 `liveObjectHasExtraKeyword` parity for `.hasKeyword (.param .equip)`:
  let grantEquipAndBuffDef : CardDef := {
    name := "P55i3 EquipL6L7"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .all #[.hasType .artifact, .controlledBy .you] }
        (.grantKeywords #[.equip (.hasType .creature) (CostSpec.ofGeneric 2)]),
      .continuous none { zones := .battlefield, pred := .all #[.hasType .creature, .hasKeyword (.param .equip)] }
        (.modifyPT (.const 2) (.const 2))
    ]
  }
  let artCrDef : CardDef := {
    bear with name := "P55i3 ArtBear", types := #[.artifact, .creature]
  }
  let gL7Kw0 := addPermanent (addPermanent g0 artCrDef p0 p0) grantEquipAndBuffDef p0 p0
  let artBear := (gL7Kw0.permanentsOf p0)[0]!
  let layer7KwOk := gL7Kw0.power artBear == 4 && gL7Kw0.toughness artBear == 4

  -- 3a(v). `.turnHistory (.permanentLeftBattlefield pred)` matches `ZoneEvent.ceasedToExist`:
  let gCease0 := addPermanent g0 bear p1 p1
  let ceaseBearId := (gCease0.permanentsOf p1)[0]!.id
  let gCease1 := gCease0.ceaseToExist ceaseBearId (cause := some (.gameRule .playerLeftGame))
  let leftBfCond : Condition :=
    .turnHistory (.eventOccurredThisTurn { relation := .anyPlayer, pred := .any }
      (.permanentLeftBattlefield (.hasType .creature)))
  let ceasedToExistLeftBfOk :=
    EvalExpr.evalCondition gCease1 { controller := p0 } leftBfCond

  -- 3b(i). Layer-5 `.characteristicDefining (.setColors cs)` across all zones & `EvalExpr.spellFaceView` CDAs:
  let blueCdaDef : CardDef := {
    name := "P55i3 BlueCda"
    manaCost := ManaCost.zero
    types := #[.creature]
    power := some (.fixed 2)
    toughness := some (.fixed 2)
    staticAbilities := #[.characteristicDefining (.setColors { blue := true })]
  }
  let gCdaHand := insertObject g0 blueCdaDef p0 (.hand p0)
  let cdaHandObj := gCdaHand.object! (gCdaHand.player p0).hand.back!
  let cdaColorOk :=
    (gCdaHand.colors cdaHandObj).contains .blue &&
    (EvalExpr.viewColors gCdaHand (EvalExpr.spellFaceView gCdaHand cdaHandObj blueCdaDef p0 0)).contains .blue

  -- 3b(ii). `.otherSpellsManaValueThisTurn` opponent `ownFallback` (`st.controllerOf spell == some p`):
  let mv5Def : CardDef := {
    name := "P55i3 Mv5", manaCost := ManaCost.ofGeneric 5, types := #[.instant],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gOppMv0 :=
    (insertObject g0 mv5Def p0 .stack).record
      (GameEvent.spellCast g0.turnNumber p1 { name := "Opp3", manaValue := 3 } (.hand p1))
  let stackMv5Id := (gOppMv0.objects.filter (·.zone == .stack)).back!.id
  let envMv5 : EvalEnv := { controller := p0, sourceId := some stackMv5Id }
  let oppOtherMv :=
    EvalExpr.evalValue gOppMv0 envMv5
      (.playerMetric .otherSpellsManaValueThisTurn (.matching .opponent .any))
  let oppOwnFallbackOk := oppOtherMv == 3

  -- 3b(iii). `Costs.actualPrintedManaCost?` matches MDFC `otherFace`:
  let backFaceDef : CardDef := {
    name := "P55i3 MdfcBack"
    manaCost := ManaCost.ofGenericAndColor 2 .green
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let mdfcDef : CardDef := {
    name := "P55i3 MdfcFront"
    manaCost := ManaCost.ofGeneric 5
    types := #[.creature]
    power := some (.fixed 4)
    toughness := some (.fixed 4)
    otherFace := some backFaceDef
  }
  let gMdfc0 := insertObject g0 mdfcDef p0 .exile
  let mdfcObj := (gMdfc0.objects.filter (·.zone == .exile)).back!
  let mdfcPrintedOk :=
    gMdfc0.actualPrintedManaCost? mdfcObj backFaceDef == some backFaceDef.manaCost

  -- 3b(iv). Copied stack spell `.targets` / `.targetsOf` LKI via `StackObjectEvent.copied` ancestry:
  let tgtBoltDef : CardDef := {
    name := "P55i3 TgtBolt"
    manaCost := { symbols := #[.colored .red] }
    types := #[.instant]
    spellAbility := some {
      effect := {
        targets := TargetSpec.creature
        body := .damage (.deal .this (.targetSlot 0) (.const 2))
      }
    }
  }
  let gCopy0 := addPermanent (insertObject (emptyHand g0 p0) tgtBoltDef p0 (.hand p0)) bear p1 p1
  let tgtBearId := (gCopy0.permanentsOf p1)[0]!.id
  let gCopy1 := gCopy0.addMana p0 (.colored .red) 1
  let gCopyProposed := mustApply gCopy1 p0 (.cast (gCopy1.player p0).hand.back!)
  let gCopyTargeted := mustApply gCopyProposed p0 (.target (.permanent tgtBearId))
  let gCopyCast := mustApply gCopyTargeted p0 .pay
  let origStackId := gCopyCast.stack.back!.objectId
  let (gCopy2, copyId?) := gCopyCast.copyStackSpellWithId (gCopyCast.object! origStackId) p0 (cause := some testCause)
  let copyId := copyId?.get!
  -- Move the copy off the stack so `.targets` / `.targetsOf` must use LKI:
  let gCopyGone := gCopy2.ceaseToExist copyId (cause := some (.gameRule .instantOrSorceryFinishedResolving))
  let copyTargetsLkiOk :=
    ((EvalExpr.evalObjects gCopyGone { controller := p0, sourceId := some copyId } (.targetsOf .this)).map (·.id?)) ==
      #[some tgtBearId]

  mustHold55i3 "3a_evalTriggerCondAndViewHasDesignation" evalTrigAndDesigOk &&
  mustHold55i3 "3a_protBlockAndPlayerDmg" protBlockAndPlayerDmgOk &&
  mustHold55i3 "3a_concreteL6Prot" concreteL6ProtOk &&
  mustHold55i3 "3a_layer7KwParity" layer7KwOk &&
  mustHold55i3 "3a_ceasedToExistLeftBf" ceasedToExistLeftBfOk &&
  mustHold55i3 "3b_cdaColorAndSpellFaceView" cdaColorOk &&
  mustHold55i3 "3b_oppOwnFallback" oppOwnFallbackOk &&
  mustHold55i3 "3b_mdfcActualPrintedManaCost" mdfcPrintedOk &&
  mustHold55i3 "3b_copyTargetsLki" copyTargetsLkiOk &&
  mustHold55i3 "3.replay"
    (replayOk55i3 #[gPrepLeft, gPlayerProtDmg, gL6Prot2, gCease1, gCopyGone])

end Phase55Item3EventAlignment

/-! ### Phase 55 Item 4a: Remaining non-card / bounced-token hand & graveyard guards
(discard deadlocks, CR 111.8 bypasses, infinite hand/graveyard mana, hand Behold, put-from-hand) -/
section Phase55Item4EventAlignment

private def mustHold55i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase55Item4EventAlignment failed: {label}"

private def replayOk55i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand (emptyHand afterDraw p0) p1

  -- Create a bounced token in `p0`'s hand (awaiting CR 704.5d SBA) and a dead token in `p0`'s graveyard:
  let tokDef : CardDef := {
    creature "P55i4 BouncedGoblin" ManaCost.empty #["Goblin"] 1 1 with
    isToken := true
    activatedAbilities := #[
      -- Hand-discard mana ability (`Discard this card: Add {R}`):
      { ActivatedAbility.manaAbility (.fixedOne (.colored .red))
          (CostSpec.ofItems #[.discard (.exact 1) .self]) with activeZones := #[.hand] },
      -- Graveyard-exile mana ability (`Exile this card from your graveyard: Add {R}`):
      { ActivatedAbility.manaAbility (.fixedOne (.colored .red))
          (CostSpec.ofItems #[.exile (.exact 1) { zones := #[.graveyard], owner := .ofPlayer .you } .self]) with
        activeZones := #[.graveyard] }
    ]
  }
  let (gWithHandTok0, tokHandObj) := g0.createOneToken p0 tokDef (cause := some testCause)
  let (gWithHandTok, tokInHandId) := gWithHandTok0.move tokHandObj.id (.hand p0) none (cause := some testCause)
  let (gWithGyTok0, tokGyObj) := g0.createOneToken p0 tokDef (cause := some testCause)
  let (gWithGyTok, tokInGyId) := gWithGyTok0.move tokGyObj.id (.graveyard p0) none (cause := some testCause)

  -- 4a(i). Discard deadlock & CR 111.8 bypass guards:
  -- With ONLY a bounced token in hand, `beginDiscardCards`, `finishBeginRecruit`, `beginMayDiscardDraw`,
  -- `discardEntireHand`, and `discardFromHand` must NOT open a deadlocked prompt or discard the token!
  let gBeginDisc := gWithHandTok.beginDiscardCards #[p0] 1
  let gRecruit := gWithHandTok.finishBeginRecruit p0
  let gMayDiscDraw := gWithHandTok.beginMayDiscardDraw p0 1
  let gDiscAll := gWithHandTok.discardEntireHand p0 (cause := some testCause)
  let gDiscFromHand := gWithHandTok.discardFromHand p0 tokInHandId (cause := some testCause)
  let discardTokenGuardsOk :=
    gWithHandTok.discardableHandIds p0 == #[] &&
    gBeginDisc.pending == .none &&
    gRecruit.pending == .none &&
    gMayDiscDraw.pending == .none &&
    (gDiscAll.player p0).hand == #[tokInHandId] &&
    gDiscAll.pending == .none &&
    (gDiscFromHand.player p0).hand == #[tokInHandId] &&
    gDiscFromHand.pending == .none

  -- 4a(ii). Infinite free mana & illegal hand/graveyard self-removal activation guards:
  let handManaBlocked :=
    !(gWithHandTok.activateManaAbility p0 tokInHandId 0 #[.colored .red]).isOk
  let gyManaBlocked :=
    !(gWithGyTok.activateManaAbility p0 tokInGyId 1 #[.colored .red]).isOk
  let manaAbilityTokenGuardsOk := handManaBlocked && gyManaBlocked

  -- 4a(iii). Non-card hand Behold (CR 701.4) guard:
  -- With ONLY a Goblin token in hand (none on battlefield) and 0 mana, beholding a Goblin or paying {2} must NOT succeed!
  let beholdGobSpellDef : CardDef := {
    name := "P55i4 BeholdGoblin"
    manaCost := ManaCost.zero
    types := #[.sorcery]
    spellAbility := some {
      effect := Effect.gainLife 2
      additionalCosts := #[
        AdditionalCostSpec.mandatory (CostSpec.ofItems #[
          .or #[CostSpec.ofItems #[.behold .goblin], CostSpec.ofGeneric 2]
        ])
      ]
    }
  }
  let realGobCardDef : CardDef := creature "P55i4 RealGoblin" ManaCost.empty #["Goblin"] 1 1
  let gBeholdTok0 := insertObject gWithHandTok beholdGobSpellDef p0 (.hand p0)
  let beholdSpellId := (gBeholdTok0.player p0).hand.back!
  let gBeholdReal := insertObject gBeholdTok0 realGobCardDef p0 (.hand p0)
  let beholdTokenGuardOk :=
    !gBeholdTok0.canPayAnnouncedAdditional p0 (gBeholdTok0.object! beholdSpellId) (gBeholdTok0.player p0).manaPool &&
    !gBeholdTok0.canPayAnnouncedAdditionalFromSources p0 (gBeholdTok0.object! beholdSpellId) &&
    gBeholdReal.canPayAnnouncedAdditional p0 (gBeholdReal.object! beholdSpellId) (gBeholdReal.player p0).manaPool &&
    gBeholdReal.canPayAnnouncedAdditionalFromSources p0 (gBeholdReal.object! beholdSpellId)

  mustHold55i4 "4a_discardTokenGuards" discardTokenGuardsOk &&
  mustHold55i4 "4a_manaAbilityTokenGuards" manaAbilityTokenGuardsOk &&
  mustHold55i4 "4a_beholdTokenGuard" beholdTokenGuardOk &&
  mustHold55i4 "4.replay"
    (replayOk55i4 #[gBeginDisc, gRecruit, gMayDiscDraw, gDiscAll, gDiscFromHand])

end Phase55Item4EventAlignment

end Mtg.Engine.EventTests
