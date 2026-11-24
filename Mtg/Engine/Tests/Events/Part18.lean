import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

section Phase52Item1EventAlignment

private def mustHold52i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase52Item1EventAlignment failed: {label}"

private def replayOk52i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with name := "P52i1 LegBear", supertypes := #[.legendary] }
  let zeroInstDef : CardDef := {
    name := "P52i1 ZeroInst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let tgtDiesDef : CardDef := {
    creature "P52i1 TgtGerm" ManaCost.empty #["Germ"] 0 0 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .thisDies
        { targets := .player, body := Instruction.gainLifeFixed 1 (.target 0) }
    ]
  }
  let twoDiesDef : CardDef := {
    creature "P52i1 TwoDiesGerm" ManaCost.empty #["Germ"] 0 0 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .thisDies (Effect.gainLife 1),
      TriggeredAbility.mkTrigger .thisDies (Effect.gainLife 2)
    ]
  }

  -- 1a(i). `Entering.receivePriority` `.chooseReplacement` settlement guards (`!anyContinuationSettlesControlFlowFwd`):
  --        (a) Already paused on `.chooseReplacement` with settling non-priority continuation `.beginStepCont .declareAttackers`:
  --            `receivePriority p2` does NOT append duplicate `.receivePriority p2`!
  let gRepSettling :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.beginStepCont .declareAttackers)),
      .pending (.chooseReplacement p0 #[]) ]
  let gRepAfterRecvSettling := gRepSettling.receivePriority p2
  --        (b) Already paused on `.chooseReplacement` with implicit priority grant `.finishResolutionChoice`:
  --            `receivePriority p2` preserves `savePendingP g p2` (`pendingPriority == some p2`) without chaining `.receivePriority p2`!
  let gRepImplicit :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some .finishResolutionChoice),
      .pending (.chooseReplacement p0 #[]) ]
  let gRepAfterRecvImplicit := gRepImplicit.receivePriority p2
  --        (c) Already paused on `.chooseReplacement` with NON-settling continuation `.finishPostStep (.logExiledIfInExile ...)`:
  --            `receivePriority p2` DOES chain `.receivePriority p2`!
  let nonSettlingCont : PendingReplacement := .finishPostStep (.logExiledIfInExile ⟨9999⟩ "msg")
  let gRepNonSettling :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some nonSettlingCont),
      .pending (.chooseReplacement p0 #[]) ]
  let gRepAfterRecvNonSettling := gRepNonSettling.receivePriority p2

  -- 1a(ii). `Decisions` `receivePriorityOutcome` across post-`resolveTop` (`classifyFinishConcedePriority`),
  --         cleanup (`finishCleanupAfterClearEotRecipient?`, `.postSbaCleanup`), `continueStartNextTurnRecipient?`,
  --         and turn-starting `startNextTurnCore` probes:
  let fcAllPassed : PendingReplacement := .finishConcede true none none none false #[] none
  let zeroLegBearDef : CardDef := { legBearDef with manaCost := ManaCost.zero }
  -- Post-`resolveTop` resolving a second duplicate legend -> `checkSBA` opens `.chooseLegend` -> NOT a priority grant, settles!
  let gStackLeg0 := addPermanent (insertObject g4 zeroLegBearDef p0 (.hand p0)) legBearDef p0 p0
  let gStackLeg1 := mustApply gStackLeg0 p0 (.cast (gStackLeg0.player p0).hand.back!)
  let gStackLegAllPassed := gStackLeg1.change (.consecutivePasses 4)

  -- `finishCleanupAfterClearEotRecipient?` opening `.chooseLegend` pauses on `.chooseLegend` (NOT priority grant; settles = true):
  let gCleanupLeg0 := addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0
  -- `.postSbaCleanup true` when a waiting trigger requires targets (`.chooseTargets`) or ordering (`.chooseTriggerToStack`):
  let gCleanupTgt0 := addPermanent g4 tgtDiesDef p1 p1
  let (gCleanupTgt1, _, _) := gCleanupTgt0.checkSBACountedWithLeaves
  let gCleanupOrder0 := addPermanent g4 twoDiesDef p1 p1
  let (gCleanupOrder1, _, _) := gCleanupOrder0.checkSBACountedWithLeaves

  -- Turn-starting probes (`continueStartNextTurnRecipient?`, `.startNextTurnAndBegin`, `.endTurnAfterCleanupStepEnded`,
  -- `.postSbaCleanup false`): next player `p1` has a live `legBearDef` AND a phased-out `legBearDef` that phases in
  -- during `p1`'s untap step, so `p1`'s upkeep `checkSBA` opens `.chooseLegend` (grant = false, settles = true)!
  let gNextLeg0 := addPermanent (addPermanent g4 legBearDef p1 p1) legBearDef p1 p1
  let nextLeg2Id := (gNextLeg0.permanentsOf p1)[1]!.id
  let gNextLegPhased := gNextLeg0.phaseOut (gNextLeg0.object! nextLeg2Id) (cause := some testCause)

  -- 1b. Resolution-cast `.finishProposedSpellCosts` (`grantPriority == false`), pre-`.finalize` stage failures,
  --     unpaid `sneakAttacker` exclusion, and `.finishResolutionChoice` prompt-vs-priority split:
  let gEx0 := insertObject g4 zeroInstDef p2 .exile
  let exCardId := (gEx0.objects.filter (·.zone == .exile)).back!.id
  let gFrcOpensExile :=
    gEx0.changes #[.pushContinuationFrame {}, .pendingMayCastFromExile (some (p2, #[exCardId], 1))]
  let gFrcOpensTargets :=
    (gCleanupTgt1.putTriggerBatch gCleanupTgt1.currentTriggerBatch).change (.pending .none)
  let gFrcGrants := g4

  -- Resolution-cast proposed spell on stack (`prop.resolutionCast == true`, `grantPriority == false`):
  let gRes0 := insertObject (emptyHand g4 p0) zeroInstDef p0 (.hand p0)
  let resOrigId := (gRes0.player p0).hand.back!
  let resOrig := gRes0.object! resOrigId
  let gResCkpt := gRes0.change .saveProposalCheckpoint
  let (gResOnStack, resSpellId) := gResCkpt.move resOrigId .stack (some p0) (verb := some .cast) (actor := some p0)
  let resProp : ProposedSpell := {
    caster := p0
    spellId := resSpellId
    original := resOrig
    originalSnapshot := gRes0.snapshot resOrig
    cost := ManaCost.empty
    resolutionCast := true
  }
  let gResPropClean := gResOnStack.change (.proposedSpell (some resProp))
  let gResPropExBase := insertObject gResPropClean zeroInstDef p2 .exile
  let resExId := (gResPropExBase.objects.filter (·.zone == .exile)).back!.id
  let gResPropWithExile :=
    gResPropExBase.changes #[
      .pushContinuationFrame {},
      .pendingMayCastFromExile (some (p2, #[resExId], 1)) ]
  let prResFinalize : PendingReplacement := .finishProposedSpellCosts .finalize false false false

  -- Pre-`.finalize` stage failures (`.teamwork` tapped, `.behold` missing Dragon, `.sneak` blocked/not-declare-blockers):
  let gTw0 := addPermanent gResPropClean bear p0 p0
  let twBearId := (gTw0.permanentsOf p0)[0]!.id
  let gTwTapped :=
    (setTapped gTw0 twBearId true).change
      (.proposedSpell (some { resProp with resolutionCast := false, teamworkPaid := true, teamworkCreatures := #[twBearId] }))
  let gTwTappedNoCkpt := gTwTapped.change .clearProposalCheckpoint
  let gBeholdMissing :=
    gResPropClean.change
      (.proposedSpell (some { resProp with resolutionCast := false, needsBehold := some .dragon }))
  let gBeholdMissingNoCkpt := gBeholdMissing.change .clearProposalCheckpoint
  let gSneakBlocked :=
    gTw0.change
      (.proposedSpell (some { resProp with resolutionCast := false, sneakAttacker := some twBearId }))
  -- Unpaid `sneakAttacker` excluded from `sacrificeCreatureOrArtifactChoices` on `.finishProposedSpellCosts .sneak true false false`:
  let gSneakSoleSac0 :=
    let g := addPermanent (insertObject g4 zeroInstDef p0 (.hand p0)) bear p0 p0
    let atkId := (g.permanentsOf p0)[0]!.id
    let g := g.beginStep .declareAttackers
    let g := mustApply g p0 (.declareAttackers #[atkId] none #[] #[])
    let g := g.advanceStep
    let g := mustApply g p1 (.declareBlockers #[])
    let spId := (g.player p0).hand.back!
    let orig := g.object! spId
    let g := g.change .saveProposalCheckpoint
    let (g, stId) := g.move spId .stack (some p0) (verb := some .cast) (actor := some p0)
    g.change (.proposedSpell (some {
      caster := p0
      spellId := stId
      original := orig
      originalSnapshot := g.snapshot orig
      cost := ManaCost.empty
      sneakAttacker := some atkId
      needsSacrificeOther := true
    }))
  let gSneakSoleSacNoCkpt := gSneakSoleSac0.change .clearProposalCheckpoint
  let gSneakWithExtraSac := addPermanent gSneakSoleSac0 hero p0 p0

  -- PR #700 review regressions:
  -- (1) `postSbaCleanupRecipient?` runs `receivePriority` with `recheckSba := true` (checking SBAs even on `.postSbaCleanup true`
  --     and before stacking waiting triggers per CR 704.3):
  let gCleanupLegWithTrig :=
    let wt : WaitingTrigger := {
      controller := p1
      source := (gCleanupLeg0.permanentsOf p0)[0]!
      ability := TriggeredAbility.mkTrigger .thisDies (Effect.gainLife 1)
      pattern := .thisDies
    }
    gCleanupLeg0.change (.waitingTriggers #[wt])
  -- (2) `beginTurnAfterStartExpiryRecipient?` stops with `none` when `drainProbePausedStep` leaves `.chooseReplacement`
  --     (`alreadyOrderedCycle`) or `pendingReplacement.isSome` (instead of letting `beginStepContRecipient?` clear `.pending`):
  let repCycleId : ReplacementId := { kind := .replaceDraw, player := some p0 }
  let gTurnCycle :=
    g4.changes #[
      .replacementOrder #[repCycleId],
      .pending (.chooseReplacement p0 #[repCycleId]) ]
  let gTurnPendingRep :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.receivePriority p0)) ]
  -- (3) `hasAvailableDiscardForProposed` rejects token and opponent-owned unpaid Sneak attackers on an empty hand
  --     while accepting a non-token card owned by `p0` that actually returns to `p0`'s hand:
  let tokBearDef : CardDef := { bear with name := "P52i1 TokBear", isToken := true, keywords := #[Keyword.haste] }
  let mkSneakDiscardProbe (atkDef : CardDef) (atkOwner : PlayerId) : Game :=
    let g := addPermanent (insertObject (emptyHand g4 p0) zeroInstDef p0 (.hand p0)) atkDef atkOwner p0
    let atkId := (g.permanentsOf p0)[0]!.id
    let g := g.beginStep .declareAttackers
    let g := mustApply g p0 (.declareAttackers #[atkId] none #[] #[])
    let g := g.advanceStep
    let g := mustApply g p1 (.declareBlockers #[])
    let spId := (g.player p0).hand.back!
    let orig := g.object! spId
    let g := g.change .saveProposalCheckpoint
    let (g, stId) := g.move spId .stack (some p0) (verb := some .cast) (actor := some p0)
    g.change (.proposedSpell (some {
      caster := p0
      spellId := stId
      original := orig
      originalSnapshot := g.snapshot orig
      cost := ManaCost.empty
      sneakAttacker := some atkId
      needsDiscardCard := true
    }))
  let gSneakTokDisc0 := mkSneakDiscardProbe tokBearDef p0
  let gSneakTokDiscNoCkpt := gSneakTokDisc0.change .clearProposalCheckpoint
  let gSneakOppDisc0 := mkSneakDiscardProbe bear p1
  let gSneakOppDiscNoCkpt := gSneakOppDisc0.change .clearProposalCheckpoint
  let gSneakCardDisc0 := mkSneakDiscardProbe bear p0

  let item1aOk :=
    mustHold52i1 "1a_receivePriorityChooseReplacementGuards"
      (gRepAfterRecvSettling.pendingReplacement == gRepSettling.pendingReplacement &&
       gRepAfterRecvImplicit.pendingReplacement == gRepImplicit.pendingReplacement &&
       gRepAfterRecvImplicit.pendingPriority == some p2 &&
       gRepAfterRecvNonSettling.pendingReplacement == some (.seq nonSettlingCont (.receivePriority p2))) &&
    mustHold52i1 "1a_postResolveTopLegend"
      (!gStackLegAllPassed.continuationGrantsPriority false fcAllPassed &&
       gStackLegAllPassed.continuationSettlesControlFlow false fcAllPassed &&
       gStackLegAllPassed.priorityRecipientOfContinuation? false fcAllPassed == none) &&
    mustHold52i1 "1a_cleanupClearEotLegend"
      (!gCleanupLeg0.continuationGrantsPriority false .finishCleanupAfterClearEot &&
       gCleanupLeg0.priorityRecipientOfContinuation? false .finishCleanupAfterClearEot == none &&
       gCleanupLeg0.continuationSettlesControlFlow false .finishCleanupAfterClearEot) &&
    mustHold52i1 "1a_postSbaCleanupChecksSba"
      (!gCleanupLeg0.continuationGrantsPriority false (.finishPostStep (.postSbaCleanup true)) &&
       gCleanupLeg0.priorityRecipientOfContinuation? false (.finishPostStep (.postSbaCleanup true)) == none &&
       !gCleanupLegWithTrig.continuationGrantsPriority false (.finishPostStep (.postSbaCleanup true)) &&
       gCleanupLegWithTrig.priorityRecipientOfContinuation? false (.finishPostStep (.postSbaCleanup true)) == none) &&
    mustHold52i1 "1a_postSbaCleanupTriggers"
      (!gCleanupTgt1.continuationGrantsPriority false (.finishPostStep (.postSbaCleanup true)) &&
       gCleanupTgt1.continuationSettlesControlFlow false (.finishPostStep (.postSbaCleanup true)) &&
       !gCleanupOrder1.continuationGrantsPriority false (.finishPostStep (.postSbaCleanup true)) &&
       gCleanupOrder1.continuationSettlesControlFlow false (.finishPostStep (.postSbaCleanup true))) &&
    mustHold52i1 "1a_startNextTurnHealthy"
      (g4.continuationGrantsPriority false (.finishPostStep .startNextTurnAndBegin) &&
       g4.priorityRecipientOfContinuation? false (.finishPostStep .startNextTurnAndBegin) == some p1 &&
       g4.priorityRecipientOfContinuation? false (.finishPostStep .endTurnAfterCleanupStepEnded) == some p1 &&
       g4.priorityRecipientOfContinuation? false (.finishPostStep (.postSbaCleanup false)) == some p1) &&
    mustHold52i1 "1a_startNextTurnUpkeepLegend"
      (!gNextLegPhased.continuationGrantsPriority false (.finishPostStep .startNextTurnAndBegin) &&
       gNextLegPhased.priorityRecipientOfContinuation? false (.finishPostStep .startNextTurnAndBegin) == none &&
       gNextLegPhased.continuationSettlesControlFlow false (.finishPostStep .startNextTurnAndBegin) &&
       !gNextLegPhased.continuationGrantsPriority false (.continueStartNextTurn p1 #[] true) &&
       gNextLegPhased.continuationSettlesControlFlow false (.continueStartNextTurn p1 #[] true)) &&
    mustHold52i1 "1a_beginTurnAfterStartExpiryStopsOnPrompt"
      (!gTurnCycle.continuationGrantsPriority false .beginTurnAfterStartExpiry &&
       gTurnCycle.priorityRecipientOfContinuation? false .beginTurnAfterStartExpiry == none &&
       !gTurnPendingRep.continuationGrantsPriority false .beginTurnAfterStartExpiry &&
       gTurnPendingRep.priorityRecipientOfContinuation? false .beginTurnAfterStartExpiry == none)

  let item1bOk :=
    mustHold52i1 "1b_finishResolutionChoiceSplit"
      (!gFrcOpensExile.continuationGrantsPriority false .finishResolutionChoice &&
       gFrcOpensExile.continuationSettlesControlFlow false .finishResolutionChoice &&
       !gFrcOpensTargets.continuationGrantsPriority false .finishResolutionChoice &&
       gFrcOpensTargets.continuationSettlesControlFlow false .finishResolutionChoice &&
       gFrcGrants.continuationGrantsPriority false .finishResolutionChoice &&
       gFrcGrants.continuationSettlesControlFlow false .finishResolutionChoice) &&
    mustHold52i1 "1b_resolutionCastFinishProposedSpellCosts"
      (gResPropClean.continuationGrantsPriority false prResFinalize &&
       gResPropClean.continuationSettlesControlFlow false prResFinalize &&
       gResPropClean.priorityRecipientOfContinuation? false prResFinalize == none &&
       gResPropClean.firstPriorityGrantRecipient? false prResFinalize == some none &&
       !gResPropWithExile.continuationGrantsPriority false prResFinalize &&
       gResPropWithExile.continuationSettlesControlFlow false prResFinalize) &&
    mustHold52i1 "1b_preFinalizeStageAndUnpaidSneakAttacker"
      (gTwTapped.continuationGrantsPriority false (.finishProposedSpellCosts .teamwork true false false) &&
       gTwTapped.continuationSettlesControlFlow false (.finishProposedSpellCosts .teamwork true false false) &&
       gTwTapped.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .teamwork true false false) == none &&
       !gTwTappedNoCkpt.continuationGrantsPriority false (.finishProposedSpellCosts .teamwork true false false) &&
       !gTwTappedNoCkpt.continuationSettlesControlFlow false (.finishProposedSpellCosts .teamwork true false false) &&
       gBeholdMissing.continuationGrantsPriority false (.finishProposedSpellCosts .behold true false false) &&
       gBeholdMissing.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .behold true false false) == none &&
       !gBeholdMissingNoCkpt.continuationGrantsPriority false (.finishProposedSpellCosts .behold true false false) &&
       gSneakBlocked.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       gSneakBlocked.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .sneak true false false) == none &&
       gSneakSoleSac0.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       !gSneakSoleSacNoCkpt.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       !gSneakSoleSacNoCkpt.continuationSettlesControlFlow false (.finishProposedSpellCosts .sneak true false false) &&
       !gSneakWithExtraSac.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       gSneakWithExtraSac.continuationSettlesControlFlow false (.finishProposedSpellCosts .sneak true false false)) &&
    mustHold52i1 "1b_sneakDiscardTokenVsCard"
      (gSneakTokDisc0.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       gSneakTokDisc0.continuationSettlesControlFlow false (.finishProposedSpellCosts .sneak true false false) &&
       gSneakTokDisc0.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .sneak true false false) == none &&
       !gSneakTokDiscNoCkpt.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       !gSneakTokDiscNoCkpt.continuationSettlesControlFlow false (.finishProposedSpellCosts .sneak true false false) &&
       gSneakOppDisc0.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       !gSneakOppDiscNoCkpt.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       !gSneakCardDisc0.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false) &&
       gSneakCardDisc0.continuationSettlesControlFlow false (.finishProposedSpellCosts .sneak true false false))

  mustHold52i1 "1a.priorityAndTurnCleanupProbes" item1aOk &&
  mustHold52i1 "1b.resolutionCastAndStageProbes" item1bOk &&
  mustHold52i1 "1.replay"
    (replayOk52i1 #[
      gRepAfterRecvSettling, gRepAfterRecvImplicit, gRepAfterRecvNonSettling,
      gStackLegAllPassed, gCleanupLeg0, gCleanupTgt1, gCleanupOrder1, gNextLegPhased,
      gFrcOpensExile, gResPropClean, gResPropWithExile, gTwTapped, gSneakSoleSac0, gSneakWithExtraSac,
      gSneakTokDisc0, gSneakOppDisc0, gSneakCardDisc0 ])

end Phase52Item1EventAlignment

section Phase52Item2EventAlignment

private def mustHold52i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase52Item2EventAlignment failed: {label}"

private def replayOk52i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let copy1Def : CardDef := { bear with name := "P52i2 CopyOne" }
  let copy2Def : CardDef := { bear with name := "P52i2 CopyTwo" }
  let embDef : CardDef := { name := "P52i2 BaseEmb", types := #[.enchantment] }
  let relicDef : CardDef := { name := "P52i2 Relic", types := #[.artifact] }
  let exSpellDef : CardDef := {
    name := "P52i2 ExSpell"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let nullSummonerDef : CardDef := {
    creature "P52i2 NullSummoner" ManaCost.empty #["Wizard"] 2 3 with
    staticAbilities := #[.castExiledWithSevenInGraveyard]
  }

  -- 2a(i). `Turns.beginTurn` passes `preTurnExp` (not post-copy `g0`) to `expireUntilTurnCommandEffects`:
  --        A `.command` emblem copying `copy1Def` (`.untilNextTurnOf p0`) ceasing at `beginTurn` keeps
  --        `copy1Def.name` in `GameEvent.ceasedToExist`!
  let gEmbCopy0 := insertObject g4 embDef p1 .command (some p1)
  let embCopyId := (gEmbCopy0.objects.filter (·.zone == .command)).back!.id
  let gEmbCopy1 :=
    (gEmbCopy0.createEffect (.gameRule (.commandEmblem embCopyId) (.untilNextTurnOf p0))
      (cause := some testCause)).createEffect
      (.layered (.objects #[embCopyId]) (.copy copy1Def) (.untilNextTurnOf p0))
      (cause := some testCause)
  let preEmbCopyEvs := gEmbCopy1.events.size
  let gEmbCopyAfter := gEmbCopy1.beginTurn
  let embCeasedWithCopyName :=
    (gEmbCopyAfter.events.extract preEmbCopyEvs gEmbCopyAfter.events.size).any fun ev =>
      match ev.change with
      | .rules (.zone (.ceasedToExist eo)) =>
        eo.id == some embCopyId && eo.name == copy1Def.name
      | _ => false

  -- 2a(ii). `Leaving.recordRemoveCountersMulti` computes `coDepartingIds` on pre-removal `pre`:
  --         Phased-out permanent controlled via `.whileSourceHasCounter src .charge` (owned by departed `p3`)
  --         plus `.copy copy1Def` (`.whileSourceHasCounter src .charge`): removing the last `.charge` counter
  --         exiles it under CR 800.4c WITHOUT logging `"is no longer a copy of"`!
  let gCtr0 := addPermanent (addPermanent g4 relicDef p2 p2) bear p0 p3
  let ctrSrcId := (gCtr0.permanentsOf p2)[0]!.id
  let ctrDepId := (gCtr0.permanentsOf p3)[0]!.id
  let gCtr1 :=
    let g := gCtr0.recordPutCounters ctrSrcId .charge 1 (some p2) (cause := some testCause)
    let g := g.createEffect (.layered (.objects #[ctrDepId]) (.control p1) (.whileSourceHasCounter ctrSrcId .charge))
      (cause := some testCause)
    let g := g.createEffect (.layered (.objects #[ctrDepId]) (.copy copy1Def) (.whileSourceHasCounter ctrSrcId .charge))
      (cause := some testCause)
    let g := mustApply g p3 .concede
    g.phaseOut (g.object! ctrDepId) (cause := some testCause)
  let preCtrLog := gCtr1.log.size
  let gCtrAfter := gCtr1.recordRemoveCountersMulti ctrSrcId #[(.charge, 1)] (byPlayer := some p2) (cause := some testCause)
  let ctrLogs := gCtrAfter.log.extract preCtrLog gCtrAfter.log.size

  -- 2a(iii). Multi-step `Core.restoreCopiesWhere` (`expireWhileSourceEffects` combining direct + emblem copies,
  --          and `preRef` live-copy-chain filtering across sequential calls sharing `preRef`):
  let gComb0 := insertObject (addPermanent (addPermanent g4 bear p0 p0) relicDef p2 p2) embDef p2 .command (some p2)
  let combTgtId := (gComb0.permanentsOf p0)[0]!.id
  let combSrcId := (gComb0.permanentsOf p2)[0]!.id
  let combEmbId := (gComb0.objects.filter (·.zone == .command)).back!.id
  let gComb1 :=
    (((gComb0.createEffect (.gameRule (.commandEmblem combEmbId) (.whileSourceOnBattlefield combSrcId))
        (cause := some testCause)).createEffect
      (.layered (.objects #[combTgtId]) (.copy copy1Def) (.whileInZone combEmbId .command))
      (cause := some testCause)).createEffect
      (.layered (.objects #[combTgtId]) (.copy copy2Def) (.whileSourceOnBattlefield combSrcId))
      (cause := some testCause))
  let preCombLog := gComb1.log.size
  let (gCombAfter, _) := gComb1.move combSrcId .exile none (cause := some testCause)
  let combLogs := gCombAfter.log.extract preCombLog gCombAfter.log.size
  let gTwoStep0 :=
    (gComb0.createEffect (.layered (.objects #[combTgtId]) (.copy copy1Def) (.untilNextTurnOf p1))
      (cause := some testCause)).createEffect
      (.layered (.objects #[combTgtId]) (.copy copy2Def) .untilEndOfTurn)
      (cause := some testCause)
  let preTwoStepLog := gTwoStep0.log.size
  let gTwoStep1 := gTwoStep0.restoreCopiesWhere (fun _ _ _ d => d == .untilEndOfTurn) (preState? := some gTwoStep0)
  let gTwoStep2 := gTwoStep1.restoreCopiesWhere (fun _ _ _ d => d == .untilNextTurnOf p1) (preState? := some gTwoStep0)
  let twoStepLogs := gTwoStep2.log.extract preTwoStepLog gTwoStep2.log.size

  -- 2a(iv). `.copy`-aware `Leaving.coDepartingIds`:
  --         Non-creature `relicDef` (`defaultController := p3`, owned by `p0`) copies `bear` (`.untilEndOfTurn`)
  --         so `.creaturesWithout (some .flying)` gives `p1` control (persisting across `p3`'s concession).
  --         At `clearEOT`, expiring `.copy bear` drops `p1`'s control -> CR 800.4c exile WITHOUT
  --         `"is no longer a copy of"`, and phased-out `coDepartingIds` with `endingCopyEids` also includes it:
  let gCopyCtrl0 := addPermanent g4 relicDef p0 p3
  let copyCtrlId := (gCopyCtrl0.permanentsOf p3)[0]!.id
  let gCopyCtrlWithCopy :=
    gCopyCtrl0.createEffect (.layered (.objects #[copyCtrlId]) (.copy bear) .untilEndOfTurn)
      (cause := some testCause)
  let copyCtrlEid := gCopyCtrlWithCopy.activeEffects.back!.1
  let gCopyCtrl1 :=
    let g := gCopyCtrlWithCopy.createEffect
      (.layered (.creaturesWithout #[Keyword.flying]) (.control p1) .indefinite)
      (cause := some testCause)
    mustApply g p3 .concede
  let preCopyCtrlLog := gCopyCtrl1.log.size
  let gCopyCtrlAfter := gCopyCtrl1.clearEOT
  let copyCtrlLogs := gCopyCtrlAfter.log.extract preCopyCtrlLog gCopyCtrlAfter.log.size
  let gCopyCtrlPhased := gCopyCtrl1.phaseOut (gCopyCtrl1.object! copyCtrlId) (cause := some testCause)
  let phasedCopyCoDep :=
    gCopyCtrlPhased.coDepartingIds #[] (endingCopyEids := #[copyCtrlEid]) (includePhasedOut := true)

  -- 2b(i). 2HG departed-team `Phasing.phaseInControlled` indirect phase-in:
  let eq2hgDef : CardDef := { name := "P52i2 2HGBlade", types := #[.artifact], subtypes := #["Equipment"] }
  let cfg2hg : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed := 522
    startingPlayer := some 0
  }
  let g2hg0 : Game :=
    match Start.start cfg2hg with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let g2hg1 := addPermanent (addPermanent g2hg0 bear ⟨0⟩ ⟨0⟩) eq2hgDef ⟨2⟩ ⟨3⟩
  let host2hgId := (g2hg1.permanentsOf ⟨0⟩)[0]!.id
  let att2hgId := (g2hg1.permanentsOf ⟨3⟩)[0]!.id
  let g2hg2 :=
    let g := g2hg1.attachSourceTo (g2hg1.object! att2hgId) (g2hg1.object! host2hgId) (cause := some testCause)
    let g := g.phaseOut (g.object! host2hgId) (cause := some testCause)
    g.record (GameEvent.playerLeftGame g.turnNumber ⟨3⟩)
  let g2hgTeamB := (g2hg2.startNextTurnAndBegin).startNextTurnAndBegin
  let (g2hgHostGone, _) := g2hgTeamB.move host2hgId .exile none (cause := some testCause)
  let g2hgOppUntap := g2hgHostGone.startNextTurnAndBegin
  let g2hgTeamBNext := (g2hgOppUntap.startNextTurnAndBegin).startNextTurnAndBegin

  -- 2b(ii). Non-`Turns` `.playFromExile` logs & deferred `.logExpiredPlayFromExile` behind paused `endControlExileLoop`:
  let gExMove0 := insertObject (addPermanent g4 relicDef p0 p0) exSpellDef p0 .exile
  let exMoveSrcId := (gExMove0.permanentsOf p0)[0]!.id
  let exMoveCardId := (gExMove0.objects.filter (·.zone == .exile)).back!.id
  let gExMove1 :=
    gExMove0.createEffect
      (.permission (some p0) (.playFromExile exMoveCardId { player := p0 }) (.whileSourceOnBattlefield exMoveSrcId))
      (cause := some testCause)
  let preExMoveLog := gExMove1.log.size
  let (gExMoveAfter, _) := gExMove1.move exMoveSrcId .exile none (cause := some testCause)
  let exMoveLogs := gExMoveAfter.log.extract preExMoveLog gExMoveAfter.log.size

  let gExCtr0 :=
    let g := gExMove0.recordPutCounters exMoveSrcId .charge 1 (some p0) (cause := some testCause)
    g.createEffect
      (.permission (some p0) (.playFromExile exMoveCardId { player := p0 }) (.whileSourceHasCounter exMoveSrcId .charge))
      (cause := some testCause)
  let preExCtrLog := gExCtr0.log.size
  let gExCtrAfter := gExCtr0.recordRemoveCountersMulti exMoveSrcId #[(.charge, 1)] (byPlayer := some p0) (cause := some testCause)
  let exCtrLogs := gExCtrAfter.log.extract preExCtrLog gExCtrAfter.log.size

  let gPauseEx0 : Game := Id.run do
    let mut g := addPermanent g4 nullSummonerDef p0 p3
    for _ in [0:7] do
      g := insertObject g bear p0 (.graveyard p0)
    let summId := (g.permanentsOf p3)[0]!.id
    g := insertObject g exSpellDef p0 .exile
    let exId := (g.objects.filter (·.zone == .exile)).back!.id
    g := g.changeObject exId (.exiledBy (some summId))
    g := g.createEffect (.layered (.objects #[summId]) (.control p0) .untilEndOfTurn) (cause := some testCause)
    g := g.createEffect (.permission (some p2) (.playFromExile exId { player := p2 }) .untilEndOfTurn) (cause := some testCause)
    g := mustApply g p3 .concede
    let pre := g
    let fromIdx := pre.events.size
    g := g.expireMatching (fun | .permission _ (.playFromExile ..) _ => true | _ => false) (cause := some testCause)
    g := g.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.endControlExileLoop #[(summId, s!"{nullSummonerDef.name} is exiled (CR 800.4c)", some p0)] (some testCause) none #[])),
      .pending (.chooseReplacement p0 #[]) ]
    return emitExpiredPlayFromExileLogs pre g fromIdx
  let prePauseLog := gPauseEx0.log.size
  let gPauseExResumed :=
    match gPauseEx0.pendingReplacement with
    | some pr => (gPauseEx0.changes #[.pending .none, .pendingReplacement none]).resumePendingReplacement pr
    | none => gPauseEx0
  let pauseExLogs := gPauseExResumed.log.extract prePauseLog gPauseExResumed.log.size

  -- 2b(iii). `.whileInZone` `.copy` / `.control` expiry logs in `Movement.move` (exile -> graveyard) and non-`.command` `ceaseToExist`:
  let gWiz0 := insertObject (addPermanent g4 bear p0 p0) exSpellDef p1 .exile
  let wizTgtId := (gWiz0.permanentsOf p0)[0]!.id
  let wizSrcId := (gWiz0.objects.filter (·.zone == .exile)).back!.id
  let gWiz1 :=
    (gWiz0.createEffect (.layered (.objects #[wizTgtId]) (.copy copy1Def) (.whileInZone wizSrcId .exile))
      (cause := some testCause)).createEffect
      (.layered (.objects #[wizTgtId]) (.control p1) (.whileInZone wizSrcId .exile))
      (cause := some testCause)
  let preWizMoveLog := gWiz1.log.size
  let (gWizAfterMove, _) := gWiz1.move wizSrcId (.graveyard p1) none (cause := some testCause)
  let wizMoveLogs := gWizAfterMove.log.extract preWizMoveLog gWizAfterMove.log.size
  let preWizCeaseLog := gWiz1.log.size
  let gWizAfterCease := gWiz1.ceaseToExist wizSrcId (cause := some testCause)
  let wizCeaseLogs := gWizAfterCease.log.extract preWizCeaseLog gWizAfterCease.log.size

  let item2aOk :=
    mustHold52i2 "2a_beginTurnPreTurnExpCopyEmblem" embCeasedWithCopyName &&
    mustHold52i2 "2a_preRemovalCounterCoDepartingPhased"
      ((gCtrAfter.followMovedToZone? ctrDepId (· == .exile)).isSome &&
       !ctrLogs.any (·.contains "is no longer a copy of")) &&
    mustHold52i2 "2a_multiStepRestoreCopiesWhere"
      ((combLogs.filter (· == s!"{bear.name} is no longer a copy of {copy2Def.name}")).size == 1 &&
       !combLogs.any (·.contains copy1Def.name) &&
       twoStepLogs.any (· == s!"{copy1Def.name} is no longer a copy of {copy2Def.name}") &&
       twoStepLogs.any (· == s!"{bear.name} is no longer a copy of {copy1Def.name}")) &&
    mustHold52i2 "2a_copyAwareCoDepartingIds"
      ((gCopyCtrlAfter.followMovedToZone? copyCtrlId (· == .exile)).isSome &&
       !copyCtrlLogs.any (·.contains "is no longer a copy of") &&
       phasedCopyCoDep.contains copyCtrlId)

  let item2bOk :=
    mustHold52i2 "2b_2hgDepartedTeamIndirectPhaseIn"
      ((g2hgTeamB.object! att2hgId).status.phasedOut &&
       g2hgOppUntap.activePlayer == ⟨0⟩ &&
       (g2hgOppUntap.object! att2hgId).status.phasedOut &&
       g2hgTeamBNext.activePlayer == ⟨2⟩ &&
       (g2hgTeamBNext.events.extract g2hgOppUntap.events.size g2hgTeamBNext.events.size).any (fun ev =>
         match ev.change with
         | .rules (.permanent (.phasedIn eo _)) => eo.id == some att2hgId
         | _ => false)) &&
    mustHold52i2 "2b_playFromExileDeferredAndNonTurnsLogs"
      (exMoveLogs.any (· == s!"{exSpellDef.name} can no longer be played from exile") &&
       exCtrLogs.any (· == s!"{exSpellDef.name} can no longer be played from exile") &&
       !gPauseEx0.log.any (· == s!"{exSpellDef.name} can no longer be played from exile") &&
       pauseExLogs.any (· == s!"{exSpellDef.name} can no longer be played from exile")) &&
    mustHold52i2 "2b_whileInZoneCopyAndControlLogs"
      (wizMoveLogs.any (· == s!"{bear.name} is no longer a copy of {copy1Def.name}") &&
       wizMoveLogs.any (· == s!"{bear.name} returns to {(gWiz1.player p0).name}'s control") &&
       wizCeaseLogs.any (· == s!"{bear.name} is no longer a copy of {copy1Def.name}") &&
       wizCeaseLogs.any (· == s!"{bear.name} returns to {(gWiz1.player p0).name}'s control"))

  mustHold52i2 "2a.simultaneousExpiryAndCoDeparting" item2aOk &&
  mustHold52i2 "2b.2hgPhasingAndExpiryLogs" item2bOk &&
  mustHold52i2 "2.replay"
    (replayOk52i2 #[
      gEmbCopyAfter, gCtrAfter, gCombAfter, gTwoStep2, gCopyCtrlAfter,
      g2hgOppUntap, g2hgTeamBNext, gExMoveAfter, gExCtrAfter, gPauseExResumed,
      gWizAfterMove, gWizAfterCease ])

end Phase52Item2EventAlignment

section Phase52Item3EventAlignment

private def mustHold52i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase52Item3EventAlignment failed: {label}"

private def replayOk52i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g2 := emptyHand afterDraw p0

  -- 3a(i). `isLkiSnapshot` stack `{X}` mana value (`damageSourceObjectFromLki` / `lkiEventObjectAsGameObject`)
  --        + `Core.staticManaValue` / `Core.objectManaValue` parity + `noSourceSentinelId` cleanup:
  let xFireballDef : CardDef := {
    name := "P52i3 XFire"
    manaCost := ⟨#[.x, .colored .red]⟩
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gX0 := (insertObject g2 xFireballDef p0 (.hand p0)).addMana p0 (.colored .red) 1 |>.addMana p0 .colorless 3
  let gX1 := mustApply (mustApply (mustApply gX0 p0 (.cast (gX0.player p0).hand.back!)) p0 (.chooseX 3)) p0 .pay
  let xSpellId := gX1.stack.back!.objectId
  let xSnap := gX1.snapshot (gX1.object! xSpellId)
  let xLkiDmg := Game.damageSourceObjectFromLki xSnap
  let xLkiObj := Game.lkiEventObjectAsGameObject xSnap
  let xNoIdLki := Game.lkiEventObjectAsGameObject { xSnap with id := none }
  let xSynthSnap : EventObject := {
    id := none, name := "P52i3 SynthX", owner := p0, controller := some p0,
    zone := .stack, manaValue := 4, chosenX := some 3, types := #[.sorcery]
  }
  let xSynthLki := Game.damageSourceObjectFromLki xSynthSnap

  -- 3a(ii). `eo.faceDown` masking on live phased-out, battlefield LKI, and stack LKI:
  let morphRichDef : CardDef := {
    creature "P52i3 RichMorph" (ManaCost.ofGeneric 5) #["Beast"] 5 5 with
    keywords := #[.morph (CostSpec.ofGeneric 2)]
    activatedAbilities := #[{ cost := CostSpec.ofGeneric 1, effect := Effect.gainLife 1 }]
    loyalty := some 4
  }
  let gFd0 := (insertObject g2 morphRichDef p0 (.hand p0)).addMana p0 .colorless 3
  let gFd1 := mustApply (mustApply (mustApply gFd0 p0 (.cast (gFd0.player p0).hand.back!)) p0 (.announceKicker true)) p0 .pay
  let gFdDown := gFd1.resolveTop
  let fdId := (gFdDown.permanentsOf p0)[0]!.id
  let gFdPhased := gFdDown.phaseOut (gFdDown.object! fdId) (cause := some testCause)
  let fdSnap := gFdDown.snapshot (gFdDown.object! fdId)
  let fdLki := Game.lkiEventObjectAsGameObject fdSnap
  let fdStackSnap : EventObject := { fdSnap with zone := .stack, chosenX := some 4 }
  let fdStackLki := Game.damageSourceObjectFromLki fdStackSnap
  let fdCov := gFdDown.copiableValues fdLki

  -- 3a(iii). Layer-6 ability-loss / granted-ability / non-duplicated `triggeredAbilities` fidelity on `isLkiSnapshot`:
  let impEqWardDef : CardDef := {
    creature "P52i3 ImpEquip" (ManaCost.ofGeneric 4) #["Construct"] 3 3 with
    types := #[.artifact, .creature]
    subtypes := #["Equipment"]
    keywords := #[.impending 3 (CostSpec.ofGeneric 2), Keyword.prowess, .ward (CostSpec.ofGeneric 2)]
    activatedAbilities := #[
      Catalog.equipAbility (ManaCost.ofGeneric 1),
      { cost := CostSpec.ofGeneric 2, effect := Effect.gainLife 1 }
    ]
  }
  let gL60 := addPermanent g2 impEqWardDef p0 p0
  let l6Id := (gL60.permanentsOf p0)[0]!.id
  let l6IntactSnap := gL60.snapshot (gL60.object! l6Id)
  let l6IntactLki := Game.lkiEventObjectAsGameObject l6IntactSnap
  let gL6Stripped :=
    gL60.createEffect (.layered (.objects #[l6Id]) (.abilities {} .all) .untilEndOfTurn)
      (cause := some testCause)
  let l6StrippedSnap := gL6Stripped.snapshot (gL6Stripped.object! l6Id)
  let l6StrippedLki := Game.lkiEventObjectAsGameObject l6StrippedSnap
  let grantedTrig := TriggeredAbility.mkTrigger .thisDies (Effect.gainLife 3)
  let gFdGranted :=
    gFdDown.createEffect
      (.layered (.objects #[fdId])
        (.abilities {
          keywords := #[Keyword.prowess, .ward (CostSpec.ofGeneric 1)]
          triggeredAbilities := #[grantedTrig]
        } .none)
        .untilEndOfTurn)
      (cause := some testCause)
  let fdGrantedSnap := gFdGranted.snapshot (gFdGranted.object! fdId)
  let fdGrantedLki := Game.lkiEventObjectAsGameObject fdGrantedSnap

  -- 3b(i). `.phasedIn` & `!before.phasedOut` LKI boundaries in `Event.lastKnownBefore?` & `isTreasureSourceInLog`:
  let trDef : CardDef := { name := "P52i3 GoldBox", types := #[.artifact], subtypes := #["Treasure"] }
  let gPhBound0 := addPermanent g2 trDef p0 p0
  let trId := (gPhBound0.permanentsOf p0)[0]!.id
  let gPhBoundOut := gPhBound0.phaseOut (gPhBound0.object! trId) (cause := some testCause)
  let (gPhOutThenExiled, _) := gPhBoundOut.move trId .exile none (cause := some testCause)
  let gPhBoundIn := gPhBoundOut.phaseInControlled p0
  let gPhInNotTr :=
    gPhBoundIn.createEffect (.layered (.objects #[trId]) (.types .set #[.artifact] #[] #[]) .untilEndOfTurn)
      (cause := some testCause)

  -- 3b(ii). `findLiveSourceObject?` trigger-queue snapshots (`putTriggeredAbilityOnStack` & `putWaitingTrigger`):
  let anthemDef : CardDef := {
    name := "P52i3 Banner", types := #[.artifact],
    staticAbilities := #[.creaturesYouControlGet 3 3]
  }
  let trigBearDef : CardDef := {
    bear with
    name := "P52i3 TrigBear"
    triggeredAbilities := #[TriggeredAbility.mkTrigger .thisAttacks (Effect.gainLife 1)]
  }
  let gTq0 := addPermanent (addPermanent g2 anthemDef p0 p0) trigBearDef p0 p0
  let tqBearId := (gTq0.permanentsOf p0).find? (·.name == trigBearDef.name) |>.get!.id
  let gTqPhased := gTq0.phaseOut (gTq0.object! tqBearId) (cause := some testCause)
  let preTqEvs := gTqPhased.events.size
  let gTqStacked :=
    gTqPhased.putTriggeredAbilityOnStack p0 (gTqPhased.object! tqBearId) trigBearDef.triggeredAbilities[0]!
      "attacked" (eventCause := some testCause)
  let tqPutSnapOk :=
    (gTqStacked.events.extract preTqEvs gTqStacked.events.size).any fun ev =>
      match ev.change with
      | .rules (.triggerQueue (.putOnStack _ srcSnap _ _)) =>
        srcSnap.id == some tqBearId && srcSnap.power == some 5 && !srcSnap.phasedOut
      | _ => false
  let wtTq : WaitingTrigger := {
    controller := p0
    source := gTqPhased.object! tqBearId
    ability := trigBearDef.triggeredAbilities[0]!
    pattern := .thisAttacks
  }
  let gTqWait := gTqPhased.putWaitingTrigger wtTq .thisAttacks
  let tqWaitSnapOk :=
    (gTqWait.events.extract preTqEvs gTqWait.events.size).any fun ev =>
      match ev.change with
      | .rules (.triggerQueue (.triggered srcSnap _ _ _)) =>
        srcSnap.id == some tqBearId && srcSnap.power == some 5 && !srcSnap.phasedOut
      | _ => false

  -- 3b(iii). `EvalExpr.resolveObjectView?`, `Core` (`evalTriggerCond`) & `EvalExpr` `.hasAttachment` / `.attachedTo` /
  --          `.inZones .battlefield` co-phased Equipment LKI:
  let bladeDef : CardDef := { name := "P52i3 Blade", types := #[.artifact], subtypes := #["Equipment"] }
  let gAtt0 := addPermanent (addPermanent g2 bear p0 p0) bladeDef p0 p0
  let attHostId := (gAtt0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let attBladeId := (gAtt0.permanentsOf p0).find? (·.name == bladeDef.name) |>.get!.id
  let gAtt1 := gAtt0.attachSourceTo (gAtt0.object! attBladeId) (gAtt0.object! attHostId) (cause := some testCause)
  let gAttPhased := gAtt1.phaseOut (gAtt1.object! attHostId) (cause := some testCause)
  let attEnv : EvalEnv := { controller := p0, sourceId := some attHostId }
  let bladeEnv : EvalEnv := { controller := p0, sourceId := some attBladeId }
  let eqFilter : ObjectFilter := { zones := .battlefield, pred := .hasSubtype (.literal .equipment) }
  let eqCountExpr : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .attachedTo .this]))
  let phEqCount := EvalExpr.evalValue gAttPhased attEnv eqCountExpr
  let phHostView? := EvalExpr.resolveObjectView? gAttPhased attEnv attHostId
  let phHasAttEval :=
    match phHostView? with
    | some v => EvalExpr.evalObjectPred gAttPhased attEnv v (.hasAttachment eqFilter)
    | none => false
  let phCoreHasAtt :=
    gAttPhased.evalTriggerCond p0 (some (gAttPhased.object! attHostId)) none
      (.exists (.filter .this (.hasAttachment eqFilter)))
  let phCoreAttachedHost :=
    gAttPhased.evalTriggerCond p0 (some (gAttPhased.object! attBladeId)) none
      (.exists (.filter .attachedHost (.hasType .creature)))
  let phEvalAttachedTo :=
    match EvalExpr.resolveObjectView? gAttPhased bladeEnv attBladeId with
    | some v => EvalExpr.evalObjectPred gAttPhased attEnv v (.attachedTo .this)
    | none => false

  -- 3b(iv). Pre-`removeFromCombat` `Phasing.phaseOut` combat LKI (Enrage / attacking creature phasing out):
  let gCbt0 := addPermanent g2 bear p0 p0
  let cbtBearId := (gCbt0.permanentsOf p0)[0]!.id
  let gCbtAtk := mustApply (gCbt0.beginStep .declareAttackers) p0 (.declareAttackers #[cbtBearId] none #[] #[])
  let gCbtPhased := gCbtAtk.phaseOut (gCbtAtk.object! cbtBearId) (cause := some testCause)
  let cbtPhasedSnap? := GameEvent.lastKnownBefore? gCbtPhased.events cbtBearId
  let cbtEnv : EvalEnv := { controller := p0, sourceId := some cbtBearId }
  let cbtEvalAttacking :=
    EvalExpr.evalCondition gCbtPhased cbtEnv (.exists (.filter .this (.combatRole .attacking)))
  let cbtCoreAttacking :=
    gCbtPhased.evalTriggerCond p0 (some (gCbtPhased.object! cbtBearId)) none
      (.exists (.filter .this (.combatRole .attacking)))
  let cbtDefendingPlayer :=
    EvalExpr.evalPlayerPred gCbtPhased cbtEnv p1 .isDefendingPlayer

  let item3aOk :=
    mustHold52i3 "3a_stackXManaValueAndSentinel"
      (xSnap.manaValue == 4 &&
       xLkiDmg.printed.manaCost == xFireballDef.manaCost &&
       xLkiObj.printed.manaCost == xFireballDef.manaCost &&
       gX1.objectManaValue xLkiDmg == 4 &&
       gX1.objectManaValue xLkiObj == 4 &&
       gX1.objectManaValue xSynthLki == 4 &&
       xNoIdLki.id == noSourceSentinelId &&
       xSynthLki.id == noSourceSentinelId) &&
    mustHold52i3 "3a_faceDownMaskingAndZeroManaValue"
      (gFdPhased.objectManaValue (gFdPhased.object! fdId) == 0 &&
       gFdDown.objectManaValue fdLki == 0 &&
       gFdDown.objectManaValue fdStackLki == 0 &&
       fdCov.name == "" &&
       fdCov.types == #[.creature] &&
       fdCov.manaCost == ManaCost.empty &&
       fdCov.activatedAbilities.isEmpty &&
       fdCov.loyalty.isNone) &&
    mustHold52i3 "3a_layer6LkiFidelityAndNoImpendingDuplication"
      (gL60.retainsPrintedAbilities l6IntactLki &&
       (gL60.triggeredAbilities l6IntactLki).size == 1 &&
       !(gL60.prowessTriggers l6IntactLki).isEmpty &&
       !(gL60.wardCostsOn l6IntactLki).isEmpty &&
       (gL60.activatedAbilitiesOf l6IntactLki).size == 2 &&
       EvalExpr.viewHasKeyword gL60 (.lki l6IntactSnap) (.param .equip) &&
       EvalExpr.viewHasKeyword gL60 (.lki l6IntactSnap) .ward &&
       !gL6Stripped.retainsPrintedAbilities l6StrippedLki &&
       (gL6Stripped.triggeredAbilities l6StrippedLki).isEmpty &&
       (gL6Stripped.prowessTriggers l6StrippedLki).isEmpty &&
       (gL6Stripped.wardCostsOn l6StrippedLki).isEmpty &&
       (gL6Stripped.activatedAbilitiesOf l6StrippedLki).isEmpty &&
       !EvalExpr.viewHasKeyword gL6Stripped (.lki l6StrippedSnap) (.param .equip) &&
       !EvalExpr.viewHasKeyword gL6Stripped (.lki l6StrippedSnap) .ward &&
       !gFdGranted.retainsPrintedAbilities fdGrantedLki &&
       (gFdGranted.triggeredAbilities fdGrantedLki).size == 1 &&
       !(gFdGranted.prowessTriggers fdGrantedLki).isEmpty &&
       !(gFdGranted.wardCostsOn fdGrantedLki).isEmpty &&
       EvalExpr.viewHasKeyword gFdGranted (.lki fdGrantedSnap) .ward)

  let item3bOk :=
    mustHold52i3 "3b_phasedInAndNonPhasedOutLkiBoundaries"
      ((GameEvent.lastKnownBefore? gPhBoundIn.events trId).isNone &&
       (GameEvent.lastKnownBefore? gPhOutThenExiled.events trId).any (fun eo => !eo.phasedOut && eo.subtypes.contains .treasure) &&
       GameEvent.isTreasureSourceInLog gPhOutThenExiled.events trId &&
       !GameEvent.isTreasureSourceInLog gPhInNotTr.events trId) &&
    mustHold52i3 "3b_triggerQueueFindLiveSourceLki"
      (tqPutSnapOk && tqWaitSnapOk) &&
    mustHold52i3 "3b_phasedOutAttachmentAndEvalExprLki"
      ((match phHostView? with | some (.lki _) => true | _ => false) &&
       phEqCount == 1 &&
       phHasAttEval &&
       phCoreHasAtt &&
       phEvalAttachedTo &&
       phCoreAttachedHost &&
       gAttPhased.attachedEquipmentAtResolution (some attHostId) (some 2) == 1) &&
    mustHold52i3 "3b_phaseOutPreRemoveFromCombatLki"
      (cbtPhasedSnap?.any (fun eo => eo.attacking && eo.attackingTarget == some (.player p1)) &&
       cbtEvalAttacking &&
       cbtCoreAttacking &&
       cbtDefendingPlayer)

  mustHold52i3 "3a.isLkiSnapshotFidelity" item3aOk &&
  mustHold52i3 "3b.phasedOutLkiAndCombat" item3bOk &&
  mustHold52i3 "3.replay"
    (replayOk52i3 #[
      gX1, gFdPhased, gL6Stripped, gFdGranted,
      gPhOutThenExiled, gPhBoundIn, gPhInNotTr,
      gTqStacked, gTqWait, gAttPhased, gCbtPhased ])

end Phase52Item3EventAlignment

section Phase52Item4EventAlignment

private def mustHold52i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase52Item4EventAlignment failed: {label}"

private def replayOk52i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def isOptChooseX52 (a? : Option Action) (n : Nat) : Bool :=
  match a? with
  | some (.chooseX k) => k == n
  | _ => false

private def isOptAnnounceKickerTrue52 (a? : Option Action) : Bool :=
  match a? with
  | some (.announceKicker true) => true
  | _ => false

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := emptyHand afterDraw p0

  -- 4a(i). `ManaAbilities.addRestrictedMana` / `addTapManaToPool` / `TapManaChoice.applyToPool` provenance:
  let trLandDef : CardDef := {
    name := "P52i4 TreasureLand"
    types := #[.artifact, .land]
    subtypes := #["Treasure"]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .red))]
  }
  let gTrTap0 := addPermanent gBase trLandDef p0 p0
  let trLandObj := (gTrTap0.permanentsOf p0)[0]!
  let poolFromAddTap := gTrTap0.addTapManaToPool ManaPool.empty trLandObj (.colored .red)
  let tapChoicesTr := gTrTap0.tapChoicesForSource trLandObj #[.colored .red] (ManaCost.ofColor .red)
  let poolFromChoice := (tapChoicesTr[0]!).applyToPool ManaPool.empty

  -- 4a(iv). `Casting.tapPreservesPostManaCosts` unpaid `prop.tapSource` when `allPicks.isEmpty && crewN?.isNone`,
  --         and `Casting.hasCostPreservingPaymentSubset` non-creature `prop.sourceId` + `teamworkCreatures`:
  let tapEnchDef : CardDef := {
    name := "P52i4 ManaEnch"
    types := #[.enchantment]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne .colorless),
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf], effect := Effect.gainLife 2 }
    ]
  }
  let gEnch0 := addPermanent (addPermanent gBase tapEnchDef p0 p0) forest p0 p0
  let enchObj := (gEnch0.permanentsOf p0).find? (·.name == tapEnchDef.name) |>.get!
  let forestObj := (gEnch0.permanentsOf p0).find? (·.name == forest.name) |>.get!
  let propEnch : ProposedSpell := {
    caster := p0
    cost := ManaCost.ofGeneric 1
    spellId := ⟨987654⟩
    original := enchObj
    originalSnapshot := gEnch0.snapshot enchObj
    kind := .activatedAbility
    sourceId := some enchObj.id
    activation := some tapEnchDef.activatedAbilities[1]!
    tapSource := true
  }
  let enchSourcesAll := #[(enchObj, #[ManaType.colorless]), (forestObj, #[ManaType.colored .green])]
  let enchSourcesOnly := #[(enchObj, #[ManaType.colorless])]

  let tapEnchPickAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[
      .mana (ManaCost.ofGeneric 1),
      .tapObjects (.count (.const 1)) (.all #[.hasType .enchantment, .tapped false, .controlledBy .you])
    ]
    effect := Effect.gainLife 1
  }
  let tapEnchPickDef : CardDef := {
    name := "P52i4 PickEnch"
    types := #[.enchantment]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne .colorless),
      tapEnchPickAb
    ]
  }
  let gEnchPick1 := addPermanent gBase tapEnchPickDef p0 p0
  let enchPickA := (gEnchPick1.permanentsOf p0)[0]!
  let propEnchPick1 : ProposedSpell := {
    caster := p0
    cost := ManaCost.ofGeneric 1
    spellId := ⟨987655⟩
    original := enchPickA
    originalSnapshot := gEnchPick1.snapshot enchPickA
    kind := .activatedAbility
    sourceId := some enchPickA.id
    activation := some tapEnchPickAb
  }
  let gEnchPick2 := addPermanent gEnchPick1 tapEnchPickDef p0 p0
  let enchPickB := (gEnchPick2.permanentsOf p0)[1]!

  let dorkDef : CardDef := {
    creature "P52i4 Dork" ManaCost.empty #["Elf"] 1 1 with
    keywords := #[Keyword.haste]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .green))]
  }
  let gDork0 := addPermanent (addPermanent gBase dorkDef p0 p0) dorkDef p0 p0
  let dorkA := (gDork0.permanentsOf p0)[0]!
  let dorkB := (gDork0.permanentsOf p0)[1]!
  let gDork1 := insertObject gDork0 { name := "P52i4 TwSpell", manaCost := ManaCost.ofColor .green, types := #[.sorcery], spellAbility := some { effect := Effect.gainLife 1 } } p0 (.hand p0)
  let gDorkProp := mustApply gDork1 p0 (.cast (gDork1.player p0).hand.back!)
  let propTwDork := { gDorkProp.proposedSpell.get! with teamworkPaid := true, teamworkCreatures := #[dorkA.id] }
  let dorkSources := #[(dorkA, #[ManaType.colored .green]), (dorkB, #[ManaType.colored .green])]

  -- 4b(i). `Decisions.castAsPartOfResolution` clean-permission `canMorph` gate:
  --        Exiled Morph sorcery-speed card with ONLY a non-clean `withoutManaCost` permission while `firstCreatureHasFlash`
  --        is on the battlefield and `p0` does NOT have sorcery timing (during `p1`'s priority / non-empty stack, or
  --        front face is a sorcery with Morph creature face):
  let morphSorcDef : CardDef := {
    name := "P52i4 ResMorphSorc"
    manaCost := ManaCost.ofGeneric 5
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let radagastDef : CardDef := {
    creature "P52i4 FlashGrant" ManaCost.empty #["Wizard"] 2 2 with
    staticAbilities := #[StaticAbility.firstCreatureHasFlash]
  }
  -- Put a dummy spell on stack so sorcery front face fails timing, while creature `morphSpellFace` passes via `firstCreatureHasFlash`!
  let dummyStackInst : CardDef := {
    name := "P52i4 StackDummy"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gResMorph0 :=
    let g := addPermanent (insertObject (insertObject gBase morphSorcDef p0 .exile) dummyStackInst p0 (.hand p0)) radagastDef p0 p0
    let exId := (g.objects.filter (·.zone == .exile)).back!.id
    let g := g.createEffect
      (.permission (some p0) (.playFromExile exId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
    let g := mustApply g p0 (.cast (g.player p0).hand.back!)
    g.addMana p0 .colorless 3
  let resMorphExId := (gResMorph0.objects.filter (·.zone == .exile)).back!.id
  let gResMorphCast :=
    gResMorph0.castAsPartOfResolution p0 resMorphExId (ignoreTiming := false) (withoutManaCost := false)

  -- 4b(ii). `Agent.choose` `.chooseX` for resolution casts with unannounced additional cost (`Pay {2} or sac creature/artifact`):
  let xChoiceSpellDef : CardDef := {
    name := "P52i4 XChoice"
    manaCost := ⟨#[.x, .colored .red]⟩
    types := #[.sorcery]
    spellAbility := some {
      effect := Effect.gainLife 1
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 2)]
    }
  }
  let gResX0 :=
    (insertObject gBase xChoiceSpellDef p0 .exile).addMana p0 (.colored .red) 1 |>.addMana p0 .colorless 4
  let resXExId := (gResX0.objects.filter (·.zone == .exile)).back!.id
  let gResXPrompt :=
    gResX0.castAsPartOfResolution p0 resXExId (ignoreTiming := true) (withoutManaCost := false)
  let agResXChoice := Agent.choose gResXPrompt p0

  -- 4b(iii). `Agent.choose` `.chooseKicker` `preSpell` affordability (`notFrom? := some .hand` reduction must NOT fire for a hand cast!):
  let notFromHandRedDef : CardDef := {
    name := "P52i4 ExileDiscount"
    types := #[.enchantment]
    staticAbilities := #[
      .costModifier none (.spells .you .anyObject none (some .hand) #[.battlefield]) (.reduceGeneric (.const 3))
    ]
  }
  let morphChoiceHandDef : CardDef := {
    creature "P52i4 MorphChoice" (ManaCost.ofGeneric 3) #["Beast"] 4 4 with
    keywords := #[.morph (CostSpec.ofGeneric 2)]
    spellAbility := some {
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 2)]
    }
  }
  let gPreSpell0 :=
    (addPermanent (insertObject gBase morphChoiceHandDef p0 (.hand p0)) notFromHandRedDef p0 p0).addMana p0 .colorless 3
  let gPreSpellKicker := mustApply gPreSpell0 p0 (.cast (gPreSpell0.player p0).hand.back!)
  let agPreSpellChoice := Agent.choose gPreSpellKicker p0

  -- 4b(iv). Sneak `sneakAttacker` mandatory-sacrifice exclusion across `Casting`, `PriorityActions`, and `Agent`:
  let sneakMandSacDef : CardDef := {
    bear with
    name := "P52i4 SneakMandSac"
    manaCost := ManaCost.ofGeneric 4
    spellAbility := some { additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature] }
    keywords := #[.sneak CostSpec.empty]
  }
  let sneakChoiceSacDef : CardDef := {
    bear with
    name := "P52i4 SneakChoiceSac"
    manaCost := ManaCost.ofGeneric 4
    spellAbility := some {
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 2)]
    }
    keywords := #[.sneak CostSpec.empty]
  }
  let gSnkBase :=
    let g := addPermanent (insertObject (insertObject gBase sneakMandSacDef p0 (.hand p0)) sneakChoiceSacDef p0 (.hand p0)) bear p0 p0
    let atkId := (g.permanentsOf p0)[0]!.id
    let g := g.beginStep .declareAttackers
    let g := mustApply g p0 (.declareAttackers #[atkId] none #[] #[])
    let g := g.advanceStep
    mustApply g p1 (.declareBlockers #[])
  let snkAtkId := (gSnkBase.permanentsOf p0)[0]!.id
  let snkMandId := ((gSnkBase.player p0).hand.filter (fun id => (gSnkBase.object! id).name == sneakMandSacDef.name))[0]!
  let snkChoiceId := ((gSnkBase.player p0).hand.filter (fun id => (gSnkBase.object! id).name == sneakChoiceSacDef.name))[0]!
  let snkMandRejected := !(gSnkBase.apply p0 (.castWithSneak snkMandId snkAtkId)).isOk
  let gSnkChoicePrompt := mustApply gSnkBase p0 (.castWithSneak snkChoiceId snkAtkId)
  let snkChoiceProp := gSnkChoicePrompt.proposedSpell.get!
  let snkAnnounceSacRejected := !(gSnkChoicePrompt.apply p0 (.chooseAdditionalCost false)).isOk

  let item4aOk :=
    mustHold52i4 "4a_addTapManaAndChoiceProvenance"
      (poolFromAddTap.units.size == 1 &&
       poolFromAddTap.units[0]!.source == some trLandObj.id &&
       poolFromAddTap.units[0]!.fromTreasure &&
       poolFromChoice.units.size == 1 &&
       poolFromChoice.units[0]!.source == some trLandObj.id &&
       poolFromChoice.units[0]!.fromTreasure) &&
    mustHold52i4 "4a_enchTapPreservesEmpty" (gEnch0.tapPreservesPostManaCosts p0 propEnch #[]) &&
    mustHold52i4 "4a_enchTapPreservesSelfFalse" (!gEnch0.tapPreservesPostManaCosts p0 propEnch #[enchObj.id]) &&
    mustHold52i4 "4a_enchSubsetAllTrue" (gEnch0.hasCostPreservingPaymentSubset ManaPool.empty (ManaCost.ofGeneric 1) enchSourcesAll {} (some (p0, propEnch))) &&
    mustHold52i4 "4a_enchSubsetOnlyFalse" (!gEnch0.hasCostPreservingPaymentSubset ManaPool.empty (ManaCost.ofGeneric 1) enchSourcesOnly {} (some (p0, propEnch))) &&
    mustHold52i4 "4a_enchTapObjectsOnlyFalse" (!gEnchPick1.hasCostPreservingPaymentSubset ManaPool.empty (ManaCost.ofGeneric 1) #[(enchPickA, #[ManaType.colorless])] {} (some (p0, propEnchPick1))) &&
    mustHold52i4 "4a_enchTapObjectsTwoTrue" (gEnchPick2.hasCostPreservingPaymentSubset ManaPool.empty (ManaCost.ofGeneric 1) #[(enchPickA, #[ManaType.colorless]), (enchPickB, #[ManaType.colorless])] {} (some (p0, propEnchPick1))) &&
    mustHold52i4 "4a_dorkTwSubsetTrue" (gDorkProp.hasCostPreservingPaymentSubset ManaPool.empty (ManaCost.ofColor .green) dorkSources {} (some (p0, propTwDork))) &&
    mustHold52i4 "4a_dorkTwOnlyFalse" (!gDorkProp.hasCostPreservingPaymentSubset ManaPool.empty (ManaCost.ofColor .green) #[(dorkA, #[ManaType.colored .green])] {} (some (p0, propTwDork)))

  let item4bOk :=
    mustHold52i4 "4b_castAsPartOfResolutionCleanPermMorph"
      (gResMorphCast.stack.size == 2 &&
       gResMorphCast.proposedSpell.isSome) &&
    mustHold52i4 "4b_agentChooseXResolutionCastAdditionalCost"
      (gResXPrompt.pending == .chooseX p0 &&
       isOptChooseX52 agResXChoice 2) &&
    mustHold52i4 "4b_agentChooseKickerPreSpellNotFromHand"
      (gPreSpellKicker.pending == .chooseKicker p0 &&
       isOptAnnounceKickerTrue52 agPreSpellChoice) &&
    mustHold52i4 "4b_sneakAttackerSacrificeExclusion"
      (snkMandRejected &&
       gSnkChoicePrompt.additionalCostChoosesGeneric p0 snkChoiceProp &&
       snkAnnounceSacRejected &&
       (gSnkBase.mandatorySacrificeError? p0 snkMandId sneakMandSacDef (excludeExtra? := some snkAtkId)).isSome)

  mustHold52i4 "4a.provenanceAndCostPreservingSubsets" item4aOk &&
  mustHold52i4 "4b.resolutionMorphAgentAndSneakExclusion" item4bOk &&
  mustHold52i4 "4.replay"
    (replayOk52i4 #[
      gTrTap0, gEnch0, gDorkProp, gResMorphCast, gResXPrompt, gPreSpellKicker, gSnkChoicePrompt ])

end Phase52Item4EventAlignment

end Mtg.Engine.EventTests
