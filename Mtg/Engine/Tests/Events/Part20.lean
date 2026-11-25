import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

section Phase54Item1EventAlignment

private def mustHold54i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase54Item1EventAlignment failed: {label}"

private def replayOk54i1 (gs : Array Game) : Bool :=
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
    name := "P54i1 ZeroInst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let legBearDef : CardDef := { bear with name := "P54i1 LegBear", supertypes := #[.legendary] }
  let ridA : ReplacementId := { kind := .replaceDraw, player := some p0 }
  let ridB : ReplacementId := { kind := .replaceDraw, player := some p1 }

  -- 1a(i). `.finishPostCast` with `grantPriority == false && hadOuter == false`:
  --        (a) Idle resolution-cast `.finishPostCast p1 false false false` delegates to `finishResolutionChoice`,
  --            so `continuationGrantsPriority == true`, `firstPriorityGrantRecipient? == some none`,
  --            `hasImplicitPendingPriorityContinuation == true`, and `finishAndGrantPriority p2` sets `pendingPriority == some p2`
  --            and grants priority to `p2` once (not double-granting);
  --        (b) When `pendingMayCastFromExile` opens a prompt on `.chooseReplacement`, `continuationGrantsPriority == false`,
  --            `continuationSettlesControlFlow == true`, `hasImplicitPendingPriorityContinuation == true`, and
  --            `receivePriority p2` / `finishAndGrantPriority p2` preserve `pendingPriority == some p2`.
  let gPcIdle0 :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishPostCast p1 false false false))
    ]
  let gPcIdleRun := gPcIdle0.finishAndGrantPriority p2
  let gPcIdleRecv :=
    (gPcIdle0.change (.pending (.chooseReplacement p0 #[ridA, ridB]))).receivePriority p2
  let gEx0 := insertObject g4 zeroInstDef p0 .exile
  let exCardId := (gEx0.objects.filter (·.zone == .exile)).back!.id
  let gPcPromptRep :=
    gEx0.changes #[
      .pushContinuationFrame {},
      .pendingMayCastFromExile (some (p0, #[exCardId], 1)),
      .pendingReplacement (some (.finishPostCast p0 false false false)),
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]
  let gPcPromptRecv := gPcPromptRep.receivePriority p2
  let gPcPromptFinish := gPcPromptRep.finishAndGrantPriority p2

  -- 1a(ii). `finishAndGrantPriority` post-drain prompt `pendingPriority` preservation &
  --         `continuationUsesImplicitPendingPriority` prompt leaves:
  let gDiscPrompt0 :=
    (insertObject g4 zeroInstDef p0 (.hand p0)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishDrawThenBeginDiscard p0 1))
    ]
  let gDiscPromptRun := gDiscPrompt0.finishAndGrantPriority p2
  let gRecruitPrompt0 :=
    (insertObject g4 zeroInstDef p0 (.hand p0)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishBeginRecruit p0))
    ]
  let gRecruitPromptRun := gRecruitPrompt0.finishAndGrantPriority p2
  let gInfl0 := addPermanent (insertObject g4 bear p0 (.library p0)) bear p0 p0
  let inflSrcId := (gInfl0.permanentsOf p0)[0]!.id
  let gInflPrompt :=
    gInfl0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishPostStep (.logInfluenceThenScryTwo inflSrcId 0))),
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]
  let gInflPromptRun :=
    (gInflPrompt.change (.pending .none)).finishAndGrantPriority p2
  let gShuf0 := insertObject g4 bear p0 (.library p0)
  let gShufPrompt :=
    gShuf0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.shuffleThen p0 (.draw p0 1))),
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]
  let gRestorePromptRep :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.restorePending (.chooseTargets p0) false)),
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]
  let gFcPromptImplicit :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishConcede false none none (some (.chooseTargets p0)) false #[] none)),
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]

  -- 1a(iii). Resolution-cast reversal classification (`classifyProposedSpellReversal` &
  --          `classifyFinishResolutionChoiceFuel`) and stale `explicitGrant?` re-validation:
  let gResRev0 :=
    (insertObject (emptyHand g4 p0) zeroInstDef p0 (.hand p0)).changes #[
      .priority p2,
      .pushContinuationFrame {},
      .saveProposalCheckpoint
    ]
  let resSpellId := (gResRev0.player p0).hand[0]!
  let resOrig := gResRev0.object! resSpellId
  let (gResRev1, resStackId) := gResRev0.move resSpellId .stack (some p0) (verb := some .cast) (actor := some p0)
  let resProp : ProposedSpell := {
    caster := p0
    spellId := resStackId
    original := resOrig
    originalSnapshot := gResRev0.snapshot resOrig
    cost := ManaCost.empty
    resolutionCast := true
    needsDiscardCard := true
  }
  let gResRev2 := gResRev1.change (.proposedSpell (some resProp))
  -- Orphaned proposal (spell exiled) inside `.finishResolutionChoice` must also classify implicitly (`some none`):
  let (gResOrphan, _) := gResRev2.move resStackId .exile none (cause := some testCause)
  -- Stale `explicitGrant?`: outer has `.receivePriority p1`, while `pendingReplacement` kills `p1` (loses game);
  -- `classifyFinishResolutionChoice` must re-validate `p1` -> living next player `p2`!
  let gStaleExp0 :=
    (g4.loseLife p1 20 (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p1),
      .pendingReplacement (some .checkSBA)
    ]

  -- 1a(iv). `completeTurnFaceUp` / `finishPostLoyaltyActivated` outer-replacement ordering & `noSourceSentinelId`:
  let gLoyOuter0 :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 3 (some testCause))),
      .pending (.chooseReplacement p0 #[ridA, ridB])
    ]
  let gLoyOuter1 :=
    gLoyOuter0.finishPostLoyaltyActivated p0 "P54i1 PW" none none none none none
      (hadOuterReplacement := true)
  -- Verify `finishPostLoyaltyActivated` with `abilityId := none` & `sourceId := none` does NOT leak `g.nextObjectId`:
  let gLoyNoSrc0 := addPermanent g4 bear p0 p0
  let preNextObjId := gLoyNoSrc0.nextObjectId
  let gLoyNoSrc1 :=
    gLoyNoSrc0.finishPostLoyaltyActivated p0 "P54i1 PW" none none none none none
  let noNextObjLeak :=
    !(gLoyNoSrc1.events.extract gLoyNoSrc0.events.size gLoyNoSrc1.events.size).any fun ev =>
      match ev.change with
      | .rules (.cast (.abilityActivated abId _ _ _)) => abId == ⟨preNextObjId⟩
      | _ => false

  -- 1b(i). `.finishProposedSpellCosts` pre-`.finalize` Sneak projection (`linkedExile` legendary -> `.chooseLegend`)
  --        and `hadOuter == true` `.seq` reversal aborting trailing `.gainLife`:
  let gSnkLeg0 :=
    let g := addPermanent (addPermanent (insertObject (emptyHand g4 p0) zeroInstDef p0 (.hand p0)) bear p0 p0) legBearDef p0 p0
    let atkId := (g.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
    let g := insertObject g legBearDef p0 .exile
    let exLegId := (g.objects.filter (·.zone == .exile)).back!.id
    let g := g.changeObject atkId (.linkedExile #[exLegId])
    let g := mustApply (g.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
    let g := mustApply g.advanceStep p1 (.declareBlockers #[])
    let spId := (g.player p0).hand.back!
    let orig := g.object! spId
    let g := g.change .saveProposalCheckpoint
    let (g, stId) := g.move spId .stack (some p0) (verb := some .cast) (actor := some p0)
    g.change (.proposedSpell (some {
      caster := p0, spellId := stId, original := orig, originalSnapshot := g.snapshot orig,
      cost := ManaCost.empty, sneakAttacker := some atkId
    }))
  let gSnkLegRun :=
    match gSnkLeg0.finishProposedSpellCosts .sneak true false false with
    | .ok g => g
    | .error e => panic! s!"gSnkLegRun failed: {e}"
  -- `hadOuter == true` reversal in `.seq (.finishProposedSpellCosts .finalize true true false) (.gainLife p0 5)`:
  let gHadOuterRev0 :=
    let g := (insertObject (emptyHand g4 p0) zeroInstDef p0 (.hand p0)).change .saveProposalCheckpoint
    let spId := (g.player p0).hand[0]!
    let orig := g.object! spId
    let (g, stId) := g.move spId .stack (some p0) (verb := some .cast) (actor := some p0)
    g.change (.proposedSpell (some {
      caster := p0, spellId := stId, original := orig, originalSnapshot := g.snapshot orig,
      cost := ManaCost.empty, needsDiscardCard := true
    }))
  let seqHadOuterRev : PendingReplacement :=
    .seq (.finishProposedSpellCosts .finalize true true false) (.gainLife p0 5 (some testCause))

  -- 1b(ii). `probeRestorePendingCore` `curPopped?` on `.chooseReplacement` & opened `pending` in `.seq (.restorePending p false) b`:
  let gRestRepSettles :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p2)
    ]
  let prRestRep : PendingReplacement := .restorePending (.chooseReplacement p0 #[ridA, ridB]) true
  let prSeqLivePrompt : PendingReplacement :=
    .seq (.restorePending (.chooseTargets p0) false) (.receivePriority p3)

  -- 1b(iii). `drainProbeNonPriorityCont` `.gainLife`, `.finishPostStep (.logExpiredPlayFromExile ..)`,
  --          and `.leavePlayersWhoLost`, plus `.seq` tail preservation:
  let gDrainLethal0 := g4.loseLife p0 20 (cause := some testCause)
  let prDrainLeave : PendingReplacement :=
    .seq (.leavePlayersWhoLost none false #[p0] none) (.receivePriority p0)
  let prDrainLogPfe : PendingReplacement :=
    .seq (.finishPostStep (.logExpiredPlayFromExile #[] 0)) (.receivePriority p2)
  let prDrainGain : PendingReplacement :=
    .seq (.gainLife p0 3 (some testCause)) (.receivePriority p2)

  -- 1b(iv). `.concedePlayersLoop` `mid == true` and `.finishConcede` `savedPendingPrio == none`:
  let cplMidTrue : PendingReplacement :=
    .concedePlayersLoop #[p1] false true false (some p2) none none false #[] none
  let fcImplicitNone : PendingReplacement :=
    .finishConcede false none none none false #[] none

  -- 1b(v). `.finishBecomeCast`, activation leaves, `.afterWardResolved`, and mana-ability leaves:
  let gBcOpenRep :=
    gResRev2.change (.pending (.chooseReplacement p0 #[ridA, ridB]))
  let prBcOpen : PendingReplacement := .finishBecomeCast p0 resStackId true false false
  let gWardWithProp := gResRev2
  let gWardWithOuter :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p2)
    ]
  let gManaStep0 := addPermanent g4 forest p0 p0
  let mForestId := (gManaStep0.permanentsOf p0)[0]!.id
  let mForestSnap := gManaStep0.snapshot (gManaStep0.object! mForestId)
  let prManaIdle : PendingReplacement :=
    .finishActivateManaAbilityPostSac p0 mForestId "Forest" mForestSnap #[.colored .green] false none none 0 false .none
  let prManaInPrompt : PendingReplacement :=
    .finishActivateManaAbilityPostSac p0 mForestId "Forest" mForestSnap #[.colored .green] false none none 0 false (.activateManaAbilities p0)
  let prManaSeq : PendingReplacement := .seq prManaIdle (.receivePriority p2)

  let item1aOk :=
    mustHold54i1 "1a_finishPostCastNoGrantDelegates"
      (gPcIdle0.anyContinuationGrantsPriority &&
       gPcIdle0.hasImplicitPriorityContinuation &&
       gPcIdle0.hasImplicitPendingPriorityContinuation &&
       gPcIdleRun.priority == p2 &&
       gPcIdleRecv.pendingPriority == some p2 &&
       !gPcPromptRep.anyContinuationGrantsPriority &&
       gPcPromptRep.anyContinuationSettlesControlFlow &&
       gPcPromptRep.hasImplicitPendingPriorityContinuation &&
       gPcPromptRecv.pendingPriority == some p2 &&
       gPcPromptFinish.pendingPriority == some p2) &&
    mustHold54i1 "1a_finishAndGrantPostDrainPromptAndImplicitLeaves"
      (gDiscPromptRun.pending == .chooseDiscardCard p0 #[] &&
       gDiscPromptRun.pendingPriority == some p2 &&
       gRecruitPromptRun.pending == .recruitDiscard p0 &&
       gRecruitPromptRun.pendingPriority == some p2 &&
       gInflPrompt.hasImplicitPendingPriorityContinuation &&
       gInflPromptRun.pending == .scry p0 2 &&
       gInflPromptRun.pendingPriority == some p2 &&
       gShufPrompt.hasImplicitPendingPriorityContinuation &&
       gRestorePromptRep.hasImplicitPendingPriorityContinuation &&
       gFcPromptImplicit.hasImplicitPendingPriorityContinuation) &&
    mustHold54i1 "1a_resCastReversalAndStaleExplicitGrant"
      (gResRev2.continuationGrantsPriority false (.finishProposedSpellCosts .finalize true false false) &&
       gResRev2.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == none &&
       gResRev2.firstPriorityGrantRecipient? false (.finishProposedSpellCosts .finalize true false false) == some none &&
       gResOrphan.continuationGrantsPriority false .finishResolutionChoice &&
       gResOrphan.priorityRecipientOfContinuation? false .finishResolutionChoice == none &&
       gResOrphan.firstPriorityGrantRecipient? false .finishResolutionChoice == some none &&
       gStaleExp0.priorityRecipientOfContinuation? false .finishResolutionChoice == some p2) &&
    mustHold54i1 "1a_loyaltyOuterOrderingAndSentinel"
      (gLoyOuter1.pendingReplacement == gLoyOuter0.pendingReplacement &&
       noNextObjLeak)

  let item1bOk :=
    mustHold54i1 "1b_finishProposedSpellCostsSneakAndHadOuterRev"
      ((match gSnkLegRun.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
       !gSnkLeg0.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       gSnkLeg0.continuationSettlesControlFlow false (.finishProposedSpellCosts .sneak true false false) &&
       gHadOuterRev0.continuationGrantsPriority false seqHadOuterRev &&
       gHadOuterRev0.priorityRecipientOfContinuation? false seqHadOuterRev == some p0) &&
    mustHold54i1 "1b_probeRestorePendingCorePoppedAndOpenedPending"
      (gRestRepSettles.continuationSettlesControlFlow false prRestRep &&
       !g4.continuationGrantsPriority false prSeqLivePrompt &&
       g4.priorityRecipientOfContinuation? false prSeqLivePrompt == none &&
       g4.firstPriorityGrantRecipient? false prSeqLivePrompt == none &&
       g4.continuationSettlesControlFlow false prSeqLivePrompt) &&
    mustHold54i1 "1b_drainProbeNonPriorityLeaves"
      (gDrainLethal0.priorityRecipientOfContinuation? false prDrainLeave == some p1 &&
       g4.priorityRecipientOfContinuation? false prDrainLogPfe == some p2 &&
       g4.priorityRecipientOfContinuation? false prDrainGain == some p2) &&
    mustHold54i1 "1b_concedePlayersLoopMidAndFinishConcedeImplicit"
      (g4.continuationGrantsPriority false cplMidTrue &&
       g4.priorityRecipientOfContinuation? false cplMidTrue == some p2 &&
       g4.continuationGrantsPriority false fcImplicitNone &&
       g4.priorityRecipientOfContinuation? false fcImplicitNone == none &&
       g4.firstPriorityGrantRecipient? false fcImplicitNone == some none) &&
    mustHold54i1 "1b_becomeCastWardAndManaAbilityProbes"
      (!gBcOpenRep.continuationGrantsPriority false prBcOpen &&
       gBcOpenRep.continuationSettlesControlFlow false prBcOpen &&
       !gWardWithProp.continuationGrantsPriority false .afterWardResolved &&
       gWardWithOuter.priorityRecipientOfContinuation? false .afterWardResolved == some p2 &&
       prManaIdle.endsWithPriorityGrant &&
       !prManaInPrompt.endsWithPriorityGrant &&
       gManaStep0.continuationGrantsPriority false prManaIdle &&
       gManaStep0.priorityRecipientOfContinuation? false prManaIdle == some p0 &&
       !gManaStep0.continuationGrantsPriority false prManaInPrompt &&
       gManaStep0.priorityRecipientOfContinuation? false prManaSeq == some p2)

  mustHold54i1 "1a" item1aOk &&
  mustHold54i1 "1b" item1bOk &&
  mustHold54i1 "1.replay"
    (replayOk54i1 #[
      gPcIdleRun, gPcIdleRecv, gPcPromptRecv, gPcPromptFinish,
      gDiscPromptRun, gRecruitPromptRun, gInflPromptRun, gLoyOuter1, gLoyNoSrc1, gSnkLegRun ])

end Phase54Item1EventAlignment

section Phase54Item2EventAlignment

private def mustHold54i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase54Item2EventAlignment failed: {label}"

private def replayOk54i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let copy1Def : CardDef := { bear with name := "P54i2 CopyOne" }
  let copy2Def : CardDef := { bear with name := "P54i2 CopyTwo" }
  let embDef : CardDef := { name := "P54i2 Emb", types := #[.enchantment] }
  let relicDef : CardDef := { name := "P54i2 Relic", types := #[.artifact] }
  let exCardDef : CardDef := {
    name := "P54i2 TwinSpell", manaCost := ManaCost.ofGeneric 1,
    types := #[.instant], spellAbility := some { effect := Effect.gainLife 1 }
  }
  let nullCastExDef : CardDef := {
    relicDef with
    name := "P54i2 NullCastRelic"
    staticAbilities := #[.castExiledWithSevenInGraveyard]
  }

  -- 2a(i). Same-name distinct-`ObjectId` `.playFromExile` expiry logs (synchronous & deferred):
  let gTwin0 := insertObject (insertObject g4 exCardDef p0 .exile) exCardDef p0 .exile
  let twinIds := (gTwin0.objects.filter (fun o => o.zone == .exile && o.name == exCardDef.name)).map (·.id)
  let twinId1 := twinIds[0]!
  let twinId2 := twinIds[1]!
  let gTwin1 :=
    (gTwin0.createEffect (.permission (some p0) (.playFromExile twinId1 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile twinId2 { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let twinStartIdx := gTwin1.events.size
  let twinPreLogs := gTwin1.log.size
  let gTwinExp := gTwin1.expireEffectsByDuration (fun _ d => d == .untilEndOfTurn) (some testCause)
  let twinLogs1 :=
    (gTwinExp.log.extract twinPreLogs gTwinExp.log.size).filter (·.endsWith "can no longer be played from exile")
  -- Calling `logExpiredPlayFromExileIds #[twinId1, twinId2] twinStartIdx` again must NOT emit duplicates:
  let gTwinExp2 := gTwinExp.logExpiredPlayFromExileIds #[twinId1, twinId2] twinStartIdx
  let twinLogs2 :=
    (gTwinExp2.log.extract twinPreLogs gTwinExp2.log.size).filter (·.endsWith "can no longer be played from exile")

  -- 2a(ii). `runEndControlExileLoop` outer `.playFromExile` pass:
  --         `p0` has 7 cards in graveyard and controls two permanents (`pfeRelic`, `nullRelic`) both exiled in one
  --         `runEndControlExileLoop` (`pfeRelic` first, `nullRelic` second); `exCard` is exiled by `nullRelic` AND
  --         has `.playFromExile` while `pfeRelic` is on battlefield -> single outer pass logs expiry once both leave!
  let gLoopBase :=
    Id.run do
      let mut g := insertObject (addPermanent (addPermanent g4 relicDef p0 p0) nullCastExDef p0 p0) exCardDef p0 .exile
      for _ in [0:7] do
        g := insertObject g bear p0 (.graveyard p0)
      return g
  let loopRelicId := (gLoopBase.permanentsOf p0).find? (·.name == relicDef.name) |>.get!.id
  let loopNullId := (gLoopBase.permanentsOf p0).find? (·.name == nullCastExDef.name) |>.get!.id
  let loopExId := (gLoopBase.objects.filter (fun o => o.zone == .exile && o.name == exCardDef.name)).back!.id
  let gLoop1 :=
    (gLoopBase.changeObject loopExId (.exiledBy (some loopNullId))).createEffect
      (.permission (some p0) (.playFromExile loopExId { player := p0 }) (.whileSourceOnBattlefield loopRelicId))
      (cause := some testCause)
  let loopPreLogs := gLoop1.log.size
  let gLoopAfter :=
    gLoop1.runEndControlExileLoop
      #[(loopRelicId, relicDef.name, some p0), (loopNullId, nullCastExDef.name, some p0)] (some testCause)
  let loopPfeLogs :=
    (gLoopAfter.log.extract loopPreLogs gLoopAfter.log.size).filter (·.endsWith "can no longer be played from exile")

  -- 2a(iii). Simultaneous multi-player `leavePlayersWhoLostCore` `.playFromExile` deferral:
  --          `p1` owns `pfeRelic`, `p2` owns `nullRelic`; BOTH lose simultaneously (`leavePlayersWhoLostCore`);
  --          single outer `.playFromExile` pass logs expiry of `exCard` even though `p1` left first while `p2`'s `nullRelic` was still live!
  let gMultiBase :=
    Id.run do
      let mut g := insertObject (addPermanent (addPermanent g4 relicDef p1 p1) nullCastExDef p2 p2) exCardDef p0 .exile
      for _ in [0:7] do
        g := insertObject g bear p0 (.graveyard p0)
      return g
  let mpRelicId := (gMultiBase.permanentsOf p1)[0]!.id
  let mpNullId := (gMultiBase.permanentsOf p2)[0]!.id
  let mpExId := (gMultiBase.objects.filter (fun o => o.zone == .exile && o.name == exCardDef.name)).back!.id
  let gMulti1 :=
    (((gMultiBase.changeObject mpExId (.exiledBy (some mpNullId))).createEffect
        (.permission (some p0) (.playFromExile mpExId { player := p0 }) (.whileSourceOnBattlefield mpRelicId))
        (cause := some testCause)).loseLife p1 20 (cause := some testCause)).loseLife p2 20 (cause := some testCause)
  let mpPreLogs := gMulti1.log.size
  let gMultiAfter := gMulti1.checkSBA
  let mpPfeLogs :=
    (gMultiAfter.log.extract mpPreLogs gMultiAfter.log.size).filter (·.endsWith "can no longer be played from exile")

  -- 2b(i). Simultaneous direct + emblem `.copy` collapse (`Turns.expireEffectsByDuration`) AND
  --        `.whileInZone` + `.whileSourceOnBattlefield` `.copy` & `.control` collapse (`Movement.move`):
  let gDirEmb0 := insertObject (addPermanent g4 bear p0 p0) embDef p1 .command (some p1)
  let deTgtId := (gDirEmb0.permanentsOf p0)[0]!.id
  let deEmbId := (gDirEmb0.objects.filter (·.zone == .command)).back!.id
  let gDirEmb1 :=
    (((gDirEmb0.createEffect (.gameRule (.commandEmblem deEmbId) .untilEndOfTurn) (cause := some testCause)).createEffect
        (.layered (.objects #[deTgtId]) (.copy copy1Def) (.whileInZone deEmbId .command)) (cause := some testCause)).createEffect
        (.layered (.objects #[deTgtId]) (.copy copy2Def) .untilEndOfTurn) (cause := some testCause))
  let dePreLogs := gDirEmb1.log.size
  let gDirEmbAfter := gDirEmb1.expireEffectsByDuration (fun _ d => d == .untilEndOfTurn) (some testCause)
  let deCopyLogs :=
    (gDirEmbAfter.log.extract dePreLogs gDirEmbAfter.log.size).filter (fun s => mentions s "is no longer a copy of")

  let gWws0 := addPermanent (addPermanent (addPermanent g4 relicDef p0 p0) bear p1 p1) bear p2 p2
  let wwsAncId := (gWws0.permanentsOf p0)[0]!.id
  let wwsCtrlId := (gWws0.permanentsOf p1)[0]!.id
  let wwsCopyId := (gWws0.permanentsOf p2)[0]!.id
  let gWws1 :=
    ((((gWws0.createEffect (.layered (.objects #[wwsCtrlId]) (.control p0) (.whileInZone wwsAncId .battlefield)) (cause := some testCause)).createEffect
        (.layered (.objects #[wwsCtrlId]) (.control p0) (.whileSourceOnBattlefield wwsAncId)) (cause := some testCause)).createEffect
        (.layered (.objects #[wwsCopyId]) (.copy copy1Def) (.whileInZone wwsAncId .battlefield)) (cause := some testCause)).createEffect
        (.layered (.objects #[wwsCopyId]) (.copy copy2Def) (.whileSourceOnBattlefield wwsAncId)) (cause := some testCause))
  let wwsPreLogs := gWws1.log.size
  let (gWwsAfter, _) := gWws1.move wwsAncId .exile none (cause := some testCause)
  let wwsCopyLogs :=
    (gWwsAfter.log.extract wwsPreLogs gWwsAfter.log.size).filter (fun s => mentions s "is no longer a copy of")
  let wwsCtrlLogs :=
    (gWwsAfter.log.extract wwsPreLogs gWwsAfter.log.size).filter (fun s => mentions s "returns to")

  -- 2b(ii). `Core.restoreCopiesWhere` inactive-copy guard:
  --         `.whileSourceHasCounter srcId .charge` copy effect whose source has 0 charge counters is ALREADY inactive;
  --         expiring it must emit ZERO `"is no longer a copy of"` logs!
  let gInact0 := addPermanent (addPermanent g4 relicDef p0 p0) bear p1 p1
  let inactSrcId := (gInact0.permanentsOf p0)[0]!.id
  let inactTgtId := (gInact0.permanentsOf p1)[0]!.id
  let gInact1 :=
    gInact0.createEffect
      (.layered (.objects #[inactTgtId]) (.copy copy1Def) (.whileSourceHasCounter inactSrcId .charge))
      (cause := some testCause)
  let inactPreLogs := gInact1.log.size
  let gInactAfter := gInact1.restoreCopiesWhere (fun _ _ _ _ => true) (some testCause)
  let inactCopyLogs :=
    (gInactAfter.log.extract inactPreLogs gInactAfter.log.size).filter (fun s => mentions s "is no longer a copy of")

  -- 2b(iii). Multi-target `.control` return logs (`restoreControlUntilSourceLeaves`, `expireWhileSourceEffects`)
  --          AND direct `reconcileControl := true` `.control`-only CR 800.4c exile:
  let gMultiCtrl0 := addPermanent (addPermanent (addPermanent g4 relicDef p0 p0) bear p1 p1) hero p2 p2
  let mcSrcId := (gMultiCtrl0.permanentsOf p0)[0]!.id
  let mcB1 := (gMultiCtrl0.permanentsOf p1)[0]!.id
  let mcB2 := (gMultiCtrl0.permanentsOf p2)[0]!.id
  let gMultiCtrl1 :=
    gMultiCtrl0.createEffect
      (.layered (.objects #[mcB1, mcB2]) (.control p0) (.whileSourceOnBattlefield mcSrcId))
      (cause := some testCause)
  let mcPreLogs := gMultiCtrl1.log.size
  let gMultiCtrlAfter := gMultiCtrl1.restoreControlUntilSourceLeaves mcSrcId (some testCause)
  let mcCtrlLogs :=
    (gMultiCtrlAfter.log.extract mcPreLogs gMultiCtrlAfter.log.size).filter (fun s => mentions s "returns to")

  -- Direct `reconcileControl := true` CR 800.4c exile: `p2` owns a bear that entered under `p1`'s control
  -- (`defaultController := some p1`), stolen by `p0` via `.whileSourceOnBattlefield`;
  -- `p1` concedes (`p2` is still alive so the bear stays on battlefield under `p0`'s control);
  -- then `expireWhileSourceEffects c8SrcId (reconcileControl := true)` expires `p0`'s control effect,
  -- leaving `controllerOf == none`, so CR 800.4c exiles the bear!
  let g800c0 := addPermanent (addPermanent g4 relicDef p0 p0) bear p2 p1
  let c8SrcId := (g800c0.permanentsOf p0)[0]!.id
  let c8BearId := (g800c0.permanentsOf p1)[0]!.id
  let g800c1 :=
    g800c0.createEffect
      (.layered (.objects #[c8BearId]) (.control p0) (.whileSourceOnBattlefield c8SrcId))
      (cause := some testCause)
  let g800c2 := mustApply g800c1 p1 .concede
  let g800c3 := g800c2.expireWhileSourceEffects c8SrcId (some testCause) (reconcileControl := true)

  let item2aOk :=
    mustHold54i2 "2a_sameNameDistinctIdPlayFromExile"
      (twinLogs1.size == 2 && twinLogs2.size == 2) &&
    mustHold54i2 "2a_runEndControlExileLoopOuterPlayFromExile"
      (loopPfeLogs.size == 1 && (gLoopAfter.followMovedToZone? loopRelicId (· == .exile)).isSome &&
       (gLoopAfter.followMovedToZone? loopNullId (· == .exile)).isSome) &&
    mustHold54i2 "2a_multiPlayerLeaveGamePlayFromExileDeferral"
      (mpPfeLogs.size == 1 && (gMultiAfter.player p1).leftTheGame && (gMultiAfter.player p2).leftTheGame)

  let item2bOk :=
    mustHold54i2 "2b_directPlusEmblemCopyCollapse"
      (deCopyLogs.size == 1 && deCopyLogs.any (fun s => mentions s copy2Def.name) &&
       !deCopyLogs.any (fun s => mentions s copy1Def.name)) &&
    mustHold54i2 "2b_whileInZonePlusWhileSourceCollapse"
      (wwsCopyLogs.size == 1 && wwsCopyLogs.any (fun s => mentions s copy2Def.name) &&
       !wwsCopyLogs.any (fun s => mentions s copy1Def.name) &&
       wwsCtrlLogs.size == 1) &&
    mustHold54i2 "2b_restoreCopiesWhereInactiveGuard"
      (inactCopyLogs.isEmpty) &&
    mustHold54i2 "2b_multiTargetControlAndDirect8004cReconcile"
      (mcCtrlLogs.size == 2 &&
       (g800c2.findObject? c8BearId).any (·.zone == .battlefield) &&
       (g800c3.followMovedToZone? c8BearId (· == .exile)).isSome)

  mustHold54i2 "2a" item2aOk &&
  mustHold54i2 "2b" item2bOk &&
  mustHold54i2 "2.replay"
    (replayOk54i2 #[gTwinExp2, gLoopAfter, gMultiAfter, gDirEmbAfter, gWwsAfter, gInactAfter, gMultiCtrlAfter, g800c3])

end Phase54Item2EventAlignment

section Phase54Item3EventAlignment

private def mustHold54i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase54Item3EventAlignment failed: {label}"

private def replayOk54i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 3a(i). `Core.hasActiveCopy` (and sibling `copy*`) `isLkiSnapshot` guard:
  let gCopy0 := addPermanent g3 bear p0 p0
  let cpBearId := (gCopy0.permanentsOf p0)[0]!.id
  let preCopySnap := gCopy0.snapshot (gCopy0.object! cpBearId)
  let preCopyLki := Game.lkiEventObjectAsGameObject preCopySnap
  let gCopyLive :=
    gCopy0.createEffect (.layered (.objects #[cpBearId]) (.copy hero) .untilEndOfTurn) (cause := some testCause)
  let liveObj := gCopyLive.object! cpBearId
  let lkiResnap := gCopyLive.snapshot preCopyLki

  -- 3a(ii). `hasProtChosenStatic` / `Core.protectedFrom` Layer-6 scope & ability-removal parity:
  let protGrantDef : CardDef := {
    name := "P54i3 ProtGrant"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none
        { zones := { zones := #[.battlefield], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[.protection .chosenCardType])
    ]
  }
  let artNonCreatDef : CardDef := { name := "P54i3 Cog", types := #[.artifact] }
  let protWatchDef : CardDef := {
    name := "P54i3 ProtWatch", types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.zoneChange (.hasKeyword .protection)
          (.inZones { zones := #[.battlefield], owner := .any })
          (.inZones { zones := #[.graveyard], owner := .any }))
        (Effect.gainLife 1)
    ]
  }
  -- Unchosen `protGrantDef` (`chosenCardType == none`):
  let gProtUnchosen :=
    addPermanent (addPermanent (addPermanent (addPermanent g3 protGrantDef p0 p0) bear p0 p0) artNonCreatDef p0 p0)
      shock p1 p1
  let protBear0 := (gProtUnchosen.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let protCog0 := (gProtUnchosen.permanentsOf p0).find? (·.name == artNonCreatDef.name) |>.get!
  let shockSrc0 := (gProtUnchosen.permanentsOf p1)[0]!
  let protUnchosenBear := gProtUnchosen.protectedFrom protBear0 shockSrc0
  let protUnchosenBearKw :=
    EvalExpr.evalObjectPred gProtUnchosen { controller := p0 } (.live protBear0) (.hasKeyword .protection)
  let protCogKw :=
    EvalExpr.evalObjectPred gProtUnchosen { controller := p0 } (.live protCog0) (.hasKeyword .protection)
  -- Chosen `chosenCardType := some .instant`: now `protBear` HAS protection, `protCog` (noncreature!) STILL does NOT!
  let (gProtChosen0, _) := g3.allocObject protGrantDef p0 .battlefield (some p0) { chosenCardType := some .instant }
  let gProtChosen :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent gProtChosen0 protWatchDef p0 p0)
          bear p0 p0)
        artNonCreatDef p0 p0)
      shock p1 p1
  let protBearId := (gProtChosen.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let protCogId := (gProtChosen.permanentsOf p0).find? (·.name == artNonCreatDef.name) |>.get!.id
  let shockSrc := (gProtChosen.permanentsOf p1)[0]!
  let protBearHas := gProtChosen.protectedFrom (gProtChosen.object! protBearId) shockSrc
  let protBearKw :=
    EvalExpr.evalObjectPred gProtChosen { controller := p0 } (.live (gProtChosen.object! protBearId)) (.hasKeyword .protection)
  let protCogHas := gProtChosen.protectedFrom (gProtChosen.object! protCogId) shockSrc
  let protCogChosenKw :=
    EvalExpr.evalObjectPred gProtChosen { controller := p0 } (.live (gProtChosen.object! protCogId)) (.hasKeyword .protection)
  -- Strip abilities from `protBear` at Layer 6 (Humility): `protectedFrom` & `.hasKeyword .protection` BOTH become FALSE!
  let gProtStripped :=
    gProtChosen.createEffect (.layered (.objects #[protBearId]) (.abilities {} .all) .indefinite)
      (cause := some testCause)
  let protBearStripped := gProtStripped.protectedFrom (gProtStripped.object! protBearId) shockSrc
  let protBearStrippedKw :=
    EvalExpr.evalObjectPred gProtStripped { controller := p0 } (.live (gProtStripped.object! protBearId)) (.hasKeyword .protection)
  -- `zoneEndpointMatches` `liveObjectHasExtraKeyword` on Layer-6 granted `.protection .chosenCardType`:
  -- destroying `protBear` inside a batch triggers `protWatchDef` (`zoneChange (.hasKeyword .protection)`)!
  let gProtDied :=
    gProtChosen.withBatch (some testCause) fun g =>
      (g.move protBearId (.graveyard p0) none (verb := some .destroy) (cause := some testCause)).1
  let epMatchesProt := !gProtDied.waitingTriggers.isEmpty

  -- 3a(iii). `lkiCombatWindow` / `lkiAttackingAlone` `ceasedToExist` & `.moved`-to-battlefield anchors:
  --          `p0` attacks with TWO creatures (`hasteBear`, `hero`); `hasteBear` is owned by `p1` (stolen by `p0`)
  --          so when `p1` concedes, `hasteBear` `ceasedToExist` (`hero` is still attacking) -> `lkiAttackingAlone` on `hasteBear` is FALSE!
  let hasteBearDef : CardDef := { bear with name := "P54i3 HasteBear", keywords := #[Keyword.haste] }
  let gCbt0 := addPermanent (addPermanent g3 hasteBearDef p1 p1) hero p0 p0
  let cbtBearId := (gCbt0.permanentsOf p1)[0]!.id
  let cbtHeroId := (gCbt0.permanentsOf p0)[0]!.id
  let gCbt1 :=
    gCbt0.createEffect (.layered (.objects #[cbtBearId]) (.control p0) .indefinite) (cause := some testCause)
  let gCbtAtk :=
    mustApply (gCbt1.beginStep .declareAttackers) p0 (.declareAttackers #[cbtBearId, cbtHeroId] (some p2) #[] #[])
  let gCbtLeave := mustApply gCbtAtk p1 .concede
  let bearCeasedLki := GameEvent.lastKnownBefore? gCbtLeave.events cbtBearId
  let ceasedNotAlone :=
    bearCeasedLki.any fun eo =>
      !gCbtLeave.lkiAttackingAlone gCbtLeave.events eo.attacking eo.id eo.controller none

  -- 3a(iv). Departed-host `.attachedTo` LKI vs live unattached Equipment & `attFilter.zones.owner`:
  let eqDef : CardDef := { name := "P54i3 Sword", types := #[.artifact], subtypes := #["Equipment"] }
  let gEq0 := addPermanent (addPermanent g3 bear p0 p0) eqDef p1 p1
  let eqHostId := (gEq0.permanentsOf p0)[0]!.id
  let eqBladeId := (gEq0.permanentsOf p1)[0]!.id
  -- Give the Sword `indestructible` ONLY while host is on battlefield, then destroy host:
  let gEq1 :=
    (gEq0.attachSourceTo (gEq0.object! eqBladeId) (gEq0.object! eqHostId) (cause := some testCause)).createEffect
      (.layered (.objects #[eqBladeId]) (.abilities { keywords := #[Keyword.indestructible] } .none) (.whileSourceOnBattlefield eqHostId))
      (cause := some testCause)
  let (gEqDied, _) := gEq1.move eqHostId (.graveyard p0) none (verb := some .destroy) (cause := some testCause)
  let deadHostSnap := GameEvent.lastKnownBefore? gEqDied.events eqHostId |>.get!
  let deadHostLki := Game.lkiEventObjectAsGameObject deadHostSnap
  -- Sword is now live & unattached (and lost indestructible when host died!), yet pre-unattach LKI HAD indestructible!
  -- Also Sword is controlled by `p1` (NOT `p0`), so `attFilter.zones.owner := .ofPlayer .you` (for `p0`) must NOT match!
  let evalEqPreUnattachInd :=
    EvalExpr.evalCondition gEqDied { controller := p0, sourceId := some eqHostId, sourceSnapshot := some deadHostSnap }
      (.exists (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .hasKeyword .indestructible, .attachedTo .this])))
  let evalEqOwnerMismatch :=
    EvalExpr.evalCondition gEqDied { controller := p0, sourceId := some eqHostId, sourceSnapshot := some deadHostSnap }
      (.exists (.filter .this (.hasAttachment { zones := { zones := #[.battlefield], owner := .ofPlayer .you }, pred := .hasSubtype (.literal .equipment) })))
  let coreEqOwnerMismatch :=
    gEqDied.evalTriggerCond p0 (some deadHostLki) none
      (.exists (.filter .this (.hasAttachment { zones := { zones := #[.battlefield], owner := .ofPlayer .you }, pred := .hasSubtype (.literal .equipment) })))

  -- 3b(i). Off-battlefield Layer-4 CDAs (`.allCreatureTypes` & `.setTypes`) in `evalLayer4Full`, `types`, `supertypes`, `hasSubtype`:
  let cdaAllTypesDef : CardDef := {
    creature "P54i3 ChangelingCda" ManaCost.zero #["Shapeshifter"] 2 2 with
    staticAbilities := #[.characteristicDefining .allCreatureTypes]
  }
  let cdaSetTypesDef : CardDef := {
    creature "P54i3 SetTypeCda" ManaCost.zero #[] 1 1 with
    staticAbilities := #[.characteristicDefining (.setTypes { mode := .add, types := #[.artifact], supertypes := #[.legendary], subtypes := #[.elf] })]
  }
  let gCda0 := insertObject (insertObject g3 cdaAllTypesDef p0 (.hand p0)) cdaSetTypesDef p0 (.graveyard p0)
  let cdaAllObj := gCda0.object! (gCda0.player p0).hand.back!
  let cdaSetObj := gCda0.object! (gCda0.player p0).graveyard.back!
  let offBfCdaOk :=
    gCda0.hasSubtype cdaAllObj .dragon &&
    gCda0.hasSubtype cdaAllObj .elf &&
    (gCda0.types cdaSetObj).contains .artifact &&
    (gCda0.supertypes cdaSetObj).contains .legendary &&
    gCda0.hasSubtype cdaSetObj .elf

  -- 3b(ii). `.otherSpellsManaValueThisTurn` self-exclusion when stack ObjectId != battlefield ObjectId:
  let mv3BearDef : CardDef := creature "P54i3 ThreeDrop" (ManaCost.ofGeneric 3) #["Bear"] 3 3
  let mv2InstDef : CardDef := {
    name := "P54i3 TwoInst", manaCost := ManaCost.ofGeneric 2, types := #[.instant],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gOther0 :=
    (insertObject (insertObject (emptyHand g3 p0) mv3BearDef p0 (.hand p0)) mv2InstDef p0 (.hand p0)).addMana p0 .colorless 5
  let id3 := (gOther0.player p0).hand[0]!
  let id2 := (gOther0.player p0).hand[1]!
  let gOther1 := mustApply (mustApply gOther0 p0 (.cast id3)) p0 .pay
  let gOther2 := mustApply (mustApply (mustApply gOther1 p0 .pass) p1 .pass) p2 .pass
  let gOther3 := mustApply (mustApply gOther2 p0 (.cast id2)) p0 .pay
  let gOther4 := mustApply (mustApply (mustApply gOther3 p0 .pass) p1 .pass) p2 .pass
  let bf3 := (gOther4.permanentsOf p0).find? (·.name == mv3BearDef.name) |>.get!
  -- `bf3` is on battlefield (different `ObjectId` from its stack cast!); `otherSpellsManaValueThisTurn` must be 2 (NOT 5!):
  let evalOtherMv :=
    EvalExpr.evalValue gOther4 { controller := p0, sourceId := some bf3.id } (.playerMetric .otherSpellsManaValueThisTurn .you)
  let coreOtherMvOk :=
    gOther4.evalTriggerCond p0 (some bf3) none
      (.cmp .eq (.playerMetric .otherSpellsManaValueThisTurn .you) (.const 2))

  -- 3b(iii). `Casting.timingAllowsCast` Impending printed MV & `Core.coreSorceryTimingOk` opponent `.anyPlayer` flash:
  let flashMv6Def : CardDef := {
    name := "P54i3 Flash6", types := #[.enchantment]
    staticAbilities := #[
      .ruleModifying none
        (.play (.castAsThoughFlash { relation := .anyPlayer, pred := .any } (.stat .manaValue .ge (.const 5)) false none))
    ]
  }
  let impMv6Def : CardDef := {
    creature "P54i3 ImpOverlord" (ManaCost.ofGeneric 6) #["Avatar"] 5 5 with
    types := #[.enchantment, .creature]
    keywords := #[.impending 4 (CostSpec.ofGeneric 2)]
  }
  -- Opponent `p1` controls `flashMv6Def` (`.anyPlayer` flash for spells with MV >= 5); it is `p1`'s turn with priority on `p0`:
  -- `impMv6Def` is exiled with TWO permissions: one plain (`ignoreTiming := false`, `withoutManaCost := true`, higher score)
  -- and one with `ignoreTiming := true` (`withoutManaCost := false`, lower score); `coreSorceryTimingOk` MUST succeed so
  -- `playPermissionFor?` picks the higher-scoring `withoutManaCost := true` permission!
  let gFlashImp0 :=
    ((insertObject (addPermanent g3 flashMv6Def p1 p1) impMv6Def p0 .exile).record
      (GameEvent.turnBegan 2 p1)).change (.priority p0)
  let impExId := (gFlashImp0.objects.filter (·.zone == .exile)).back!.id
  let gFlashImp :=
    (gFlashImp0.createEffect
      (.permission (some p0) (.playFromExile impExId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile impExId { player := p0, ignoreTiming := true }) .untilEndOfTurn)
      (cause := some testCause)
  let impCardObj := gFlashImp.object! impExId
  let impAltFace : CardDef := { impMv6Def with manaCost := ManaCost.ofGeneric 2 }
  -- Printed MV is 6 (>= 5), so BOTH `timingAllowsCast` (even passed `impAltFace`!) AND `coreSorceryTimingOk` allow flash!
  let timingImpOk :=
    gFlashImp.timingAllowsCast p0 impAltFace (card? := some impCardObj) &&
    (gFlashImp.playPermissionFor? p0 impCardObj).any (·.withoutManaCost)

  -- 3b(iv). `.targetsOf` / `.targets` LKI & `evalStaticValL5` `.chosenX` `isLkiSnapshot`:
  let gTgt0 := insertObject (addPermanent (emptyHand g3 p0) bear p1 p1) shock p0 (.hand p0)
  let tgtBearId := (gTgt0.permanentsOf p1)[0]!.id
  let gTgtProp := mustApply (gTgt0.addMana p0 (.colored .red) 1) p0 (.cast (gTgt0.player p0).hand[0]!)
  let gTgtPaid := mustApply (mustApply gTgtProp p0 (.targets #[.permanent tgtBearId])) p0 .pay
  let tgtSpellId := gTgtPaid.stack.back!.objectId
  -- Move the spell off the stack and the bear to graveyard; LKI `CastEvent.targeted` & `damageSourceById?` still recognize the target!
  let (gTgt2, _) := gTgtPaid.move tgtSpellId (.graveyard p0) none (cause := some testCause)
  let (gTgt3, _) := gTgt2.move tgtBearId (.graveyard p1) none (cause := some testCause)
  let tgtSpellLki := Game.lkiEventObjectAsGameObject (GameEvent.lastKnownBefore? gTgt3.events tgtSpellId |>.get!)
  let coreTargetsLkiOk :=
    gTgt3.evalTriggerCond p0 (some tgtSpellLki) none (.exists (.targetsOf .this))
  -- `evalStaticValL5` `.chosenX` `isLkiSnapshot` guard (synthetic LKI with `chosenX := none` reusing an ID with historical `chosenXOf? == some 4`):
  let xCardDef : CardDef := {
    name := "P54i3 XSpell", manaCost := ⟨#[.x]⟩, types := #[.sorcery],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gX0 := (insertObject (emptyHand g3 p0) xCardDef p0 (.hand p0)).addMana p0 .colorless 4
  let gX1 := mustApply (mustApply (mustApply gX0 p0 (.cast (gX0.player p0).hand[0]!)) p0 (.chooseX 4)) p0 .pay
  let xStackId := gX1.stack.back!.objectId
  let (gX2, _) := gX1.move xStackId (.graveyard p0) none (cause := some testCause)
  let xLkiNone := Game.lkiEventObjectAsGameObject {
    id := some xStackId, name := xCardDef.name, owner := p0, controller := some p0,
    zone := .stack, types := #[.sorcery], chosenX := none
  }
  let xLkiGuardOk :=
    gX2.evalTriggerCond p0 (some xLkiNone) none (.cmp .eq .chosenX (.const 0))

  let item3aOk :=
    mustHold54i3 "3a_hasActiveCopyLkiGuard"
      (gCopyLive.hasActiveCopy liveObj &&
       !gCopyLive.hasActiveCopy preCopyLki &&
       !lkiResnap.isCopy &&
       !gCopyLive.evalTriggerCond p0 none (some preCopyLki) (.exists (.filter .triggerSubject .isCopy))) &&
    mustHold54i3 "3a_protChosenStaticLayer6Parity"
      (!protUnchosenBear && !protUnchosenBearKw && !protCogKw &&
       protBearHas && protBearKw && !protCogHas && !protCogChosenKw &&
       !protBearStripped && !protBearStrippedKw) &&
    mustHold54i3 "3a_lkiCombatWindowCeasedToExist" ceasedNotAlone &&
    mustHold54i3 "3a_departedHostAttachedToLkiAndOwner"
      (evalEqPreUnattachInd && !evalEqOwnerMismatch && !coreEqOwnerMismatch)

  let item3bOk :=
    mustHold54i3 "3b_offBattlefieldLayer4Cdas" offBfCdaOk &&
    mustHold54i3 "3b_otherSpellsManaValueSelfExclusion" (evalOtherMv == 2 && coreOtherMvOk) &&
    mustHold54i3 "3b_timingAllowsCastImpendingAndCoreSorceryAnyPlayer" timingImpOk &&
    mustHold54i3 "3b_targetsLkiChosenXLkiAndZoneEndpoint"
      (coreTargetsLkiOk && xLkiGuardOk && epMatchesProt)

  mustHold54i3 "3a" item3aOk &&
  mustHold54i3 "3b" item3bOk &&
  mustHold54i3 "3.replay"
    (replayOk54i3 #[gCopyLive, gProtStripped, gProtDied, gCbtLeave, gEqDied, gOther4, gTgt3, gX2])

end Phase54Item3EventAlignment

section Phase54Item4EventAlignment

private def mustHold54i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase54Item4EventAlignment failed: {label}"

private def replayOk54i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := emptyHand afterDraw p0

  -- 4a(i). Bounced-token `sneakAttacker` non-card discard bug (CR 108.2b / 111.8):
  --        A bounced creature token in `.hand p0` is NOT a card and cannot be discarded:
  --        - `discardableHandIds` excludes it;
  --        - `discardPendingCard` rejects it with `.error`;
  --        - `hasUsableNonPlainManaAbility` excludes it;
  --        - Casting a Sneak + discard-or-pay-{2} spell with only a token attacker and no mana reverses (no free cast!).
  let tokBearDef : CardDef := { bear with name := "P54i4 TokBear", isToken := true, keywords := #[Keyword.haste] }
  let discSpellDef : CardDef := {
    name := "P54i4 DiscSpell"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some {
      effect := Effect.gainLife 3
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.discardCardOrPayGeneric 2)]
    }
    keywords := #[.sneak CostSpec.empty]
  }
  let discManaArtDef : CardDef := {
    name := "P54i4 DiscManaArt", types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.discard (.exact 1) .hand]
      effect := Effect.addMana #[.colored .red]
    }]
  }
  let gTokInHand0 := insertObject (addPermanent gBase discManaArtDef p0 p0) tokBearDef p0 (.hand p0)
  let tokInHandId := (gTokInHand0.player p0).hand[0]!
  let gTokDiscPrompt := gTokInHand0.change (.pending (.discardForAdditionalCost p0))
  let tokDiscRejected :=
    match gTokDiscPrompt.apply p0 (.discard tokInHandId) with
    | .error _ => true
    | .ok _ => false
  let tokNonPlainManaOk := !gTokInHand0.hasUsableNonPlainManaAbility p0
  let tokDiscardIdsEmpty := (gTokInHand0.discardableHandIds p0).isEmpty
  -- Sneak + discard-or-pay-{2} spell with ONLY a token attacker -> choosing discard reverses under CR 733.1 (no free cast!):
  let gSnkTok0 :=
    let g := addPermanent (insertObject gBase discSpellDef p0 (.hand p0)) tokBearDef p0 p0
    let atkId := (g.permanentsOf p0)[0]!.id
    let g := mustApply (g.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
    mustApply g.advanceStep p1 (.declareBlockers #[])
  let snkTokAtkId := (gSnkTok0.permanentsOf p0)[0]!.id
  let snkTokCardId := (gSnkTok0.player p0).hand[0]!
  let gSnkTokPrompt := mustApply gSnkTok0 p0 (.castWithSneak snkTokCardId snkTokAtkId)
  let snkTokDiscardChoiceRejected :=
    match gSnkTokPrompt.apply p0 (.chooseAdditionalCost false) with
    | .error _ => true
    | .ok _ => false
  -- Even if `needsDiscardCard` is already set on a Sneak proposal, `.finishProposedSpellCosts .sneak`
  -- bounces the token and reverses under CR 733.1 (no `.discardForAdditionalCost` prompt, no free cast!):
  let gSnkTokRev :=
    let prop := gSnkTokPrompt.proposedSpell.get!
    let gForced := gSnkTokPrompt.changes #[.pending .none, .proposedSpell (some { prop with needsDiscardCard := true })]
    match gForced.finishProposedSpellCosts .sneak true false false with
    | .ok g => g
    | .error e => panic! s!"gSnkTokRev failed: {e}"
  let snkTokNoFreeCast :=
    snkTokDiscardChoiceRejected &&
    gSnkTokRev.stack.isEmpty && gSnkTokRev.proposedSpell.isNone && gSnkTokRev.pending == .none &&
      (gSnkTokRev.player p0).life == 20 && Game.replayEvents gSnkTokRev.events == gSnkTokRev

  -- 4a(ii). `Casting.validateFrontFaceCast` Sneak `linkedExile` sacrifice parity:
  --         (a) `p0` attacks with sole creature `atkId` which has a `linkedExile` bear;
  --             casting a Sneak + mandatory-sacrifice-creature spell SUCCEEDS upfront because returning `atkId`
  --             returns the linked exiled bear to battlefield as a legal sacrifice!
  --         (b) `p0` attacks with `atkId` which anchors a `.whileSourceOnBattlefield` control effect on `p1`'s hero
  --             (sole other creature `p0` controls); casting Sneak + mandatory-sacrifice is REJECTED upfront
  --             because bouncing `atkId` returns `p1`'s hero to `p1`!
  let sneakSacSpellDef : CardDef := {
    name := "P54i4 SneakSac"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some {
      effect := Effect.gainLife 2
      additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeArtifactOrCreature]
    }
    keywords := #[.sneak CostSpec.empty]
  }
  let gSnkLink0 :=
    let g := insertObject (addPermanent (insertObject gBase sneakSacSpellDef p0 (.hand p0)) bear p0 p0) bear p0 .exile
    let atkId := (g.permanentsOf p0)[0]!.id
    let exBearId := (g.objects.filter (·.zone == .exile)).back!.id
    let g := g.changeObject atkId (.linkedExile #[exBearId])
    let g := mustApply (g.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
    mustApply g.advanceStep p1 (.declareBlockers #[])
  let snkLinkAtkId := (gSnkLink0.permanentsOf p0)[0]!.id
  let snkLinkSpellId := (gSnkLink0.player p0).hand[0]!
  let gSnkLinkApplied :=
    match gSnkLink0.apply p0 (.castWithSneak snkLinkSpellId snkLinkAtkId) with
    | .ok g1 =>
      some (if g1.pending == .activateManaAbilities p0 then mustApply g1 p0 .pay else g1)
    | .error _ => none

  let gSnkCtrl0 :=
    let g := addPermanent (addPermanent (insertObject gBase sneakSacSpellDef p0 (.hand p0)) bear p0 p0) hero p1 p1
    let atkId := (g.permanentsOf p0)[0]!.id
    let oppHeroId := (g.permanentsOf p1)[0]!.id
    let g := g.createEffect (.layered (.objects #[oppHeroId]) (.control p0) (.whileSourceOnBattlefield atkId)) (cause := some testCause)
    let g := mustApply (g.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
    mustApply g.advanceStep p1 (.declareBlockers #[])
  let snkCtrlAtkId := (gSnkCtrl0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let snkCtrlSpellId := (gSnkCtrl0.player p0).hand[0]!
  let snkCtrlRejected :=
    match gSnkCtrl0.apply p0 (.castWithSneak snkCtrlSpellId snkCtrlAtkId) with
    | .error _ => true
    | .ok _ => false

  let item4Ok :=
    mustHold54i4 "4a_tokDiscardIdsEmpty" tokDiscardIdsEmpty &&
    mustHold54i4 "4a_tokDiscRejected" tokDiscRejected &&
    mustHold54i4 "4a_tokNonPlainManaOk" tokNonPlainManaOk &&
    mustHold54i4 "4a_snkTokNoFreeCast" snkTokNoFreeCast &&
    mustHold54i4 "4a_validateFrontFaceCastSneakLinkedExileAndControlParity"
      (gSnkLinkApplied.any (fun g => g.pending == .sacrificePermanent p0 (g.proposedSpell.get!.spellId)) &&
       snkCtrlRejected)

  mustHold54i4 "4.all" item4Ok &&
  mustHold54i4 "4.replay"
    (replayOk54i4 (#[gTokInHand0, gSnkTok0, gSnkTokPrompt, gSnkTokRev, gSnkLink0, gSnkCtrl0] ++
      (match gSnkLinkApplied with | some g => #[g] | none => #[])))

end Phase54Item4EventAlignment

end Mtg.Engine.EventTests
