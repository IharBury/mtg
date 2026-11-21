import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase46Item1EventAlignment

private def mustHold46i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase46Item1EventAlignment failed: {label}"

private def replayOk46i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with name := "P46i1 LegBear", supertypes := #[.legendary] }

  -- 1a(i)-(ii). `StateBasedActions.chainOrMergeLeave` splits `.seq` at the first `.leavePlayersWhoLost`
  --             or `.checkSBA` leaf and folds any right-hand sibling `tail` between `O_0` and `O_caller`
  --             (`O_0 >> tail >> O_caller`) before restoring `saved?`:
  let gLegBase := addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0
  let legIds := ((gLegBase.permanentsOf p0).filter (·.name == legBearDef.name)).map (·.id)
  let gOrdLeave0 :=
    gLegBase.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 100 (some testCause)),
      .pushOuterPendingReplacement (.gainLife p0 1 (some testCause)),
      .pendingReplacement
        (some (.seq (.leavePlayersWhoLost none true #[p2] none)
                    (.gainLife p0 10 (some testCause)))),
      .pending (.chooseLegend p0 legBearDef.name legIds) ]
  let preOrdLeaveIdx := gOrdLeave0.events.size
  let (gOrdLeaveMerged, _, _) :=
    (gOrdLeave0.record (GameEvent.playerLost gOrdLeave0.turnNumber p2 .lifeZeroOrLess)).checkSBACountedWithLeaves
      (savedIn := some (.mayPayGeneric p0 3)) (popOuterIn := true) (departedIn := #[p3])
  let gOrdLeaveAtPrompt := mustApply gOrdLeaveMerged p0 (.keepLegend legIds[0]!)
  let gOrdLeaveDone := mustApply gOrdLeaveAtPrompt p0 .decline
  let ordLeaveSlice := gOrdLeaveDone.events.extract preOrdLeaveIdx gOrdLeaveDone.events.size
  let gainPos? (amt : Nat) : Option Nat :=
    ordLeaveSlice.findIdx? fun ev =>
      match ev.change with
      | .rules (.life (.gained q n)) => q == p0 && n == amt
      | _ => false
  let leaveOrderOk :=
    match gainPos? 100, gainPos? 10, gainPos? 1 with
    | some i0, some iTail, some iCaller => i0 < iTail && iTail < iCaller
    | _, _, _ => false

  let gOrdSba0 :=
    gLegBase.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 1 (some testCause)),
      .pendingReplacement (some (.seq .checkSBA (.gainLife p0 10 (some testCause)))),
      .pending (.chooseLegend p0 legBearDef.name legIds) ]
  let preOrdSbaIdx := gOrdSba0.events.size
  let (gOrdSbaMerged, _, _) :=
    (gOrdSba0.record (GameEvent.playerLost gOrdSba0.turnNumber p2 .lifeZeroOrLess)).checkSBACountedWithLeaves
      (savedIn := some (.mayPayGeneric p0 4)) (popOuterIn := true) (departedIn := #[p2])
  let gOrdSbaAtPrompt := mustApply gOrdSbaMerged p0 (.keepLegend legIds[0]!)
  let gOrdSbaDone := mustApply gOrdSbaAtPrompt p0 .decline
  let ordSbaSlice := gOrdSbaDone.events.extract preOrdSbaIdx gOrdSbaDone.events.size
  let sbaGainPos? (amt : Nat) : Option Nat :=
    ordSbaSlice.findIdx? fun ev =>
      match ev.change with
      | .rules (.life (.gained q n)) => q == p0 && n == amt
      | _ => false
  let sbaOrderOk :=
    match sbaGainPos? 10, sbaGainPos? 1 with
    | some iTail, some iCaller => iTail < iCaller
    | _, _ => false

  -- 1a(iii). Non-abort `pendingFreeCopies` preservation when third party `p2` leaves while `p0` is
  --          proposing one of `pendingFreeCopies` (`castsLeft == 0` / remaining `budget < mv`):
  let sacOrPayCopyDef : CardDef := {
    name := "P46i1 CopyBolt"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 2)]
    spellEffect := some { resolution := .gainLife 2, phrase := "Gain 2 life." }
  }
  let bigCopyDef : CardDef := {
    name := "P46i1 BigCopy"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
    spellEffect := some { resolution := .gainLife 3, phrase := "Gain 3 life." }
  }
  let gFreeCp0 := insertObject (insertObject g4 sacOrPayCopyDef p0 .exile) bigCopyDef p0 .exile
  let cp1Obj := (gFreeCp0.objects.filter (fun o => o.zone == .exile && o.name == sacOrPayCopyDef.name))[0]!
  let cp2Obj := (gFreeCp0.objects.filter (fun o => o.zone == .exile && o.name == bigCopyDef.name))[0]!
  let gFreeCpPrompt :=
    gFreeCp0.changes #[
      .pushContinuationFrame {},
      .pending (.fraChoice p0 (.castCopiesFree #[cp1Obj.id, cp2Obj.id] 2 1)) ]
  -- `p0` proposes `cp1Obj`: `pendingFreeCopies` now holds `(p0, #[cp2Obj.id], 0, 0)` while `p0` is at `.chooseAdditionalCost p0`:
  let gFreeCpProposed := mustApply gFreeCpPrompt p0 (.cast cp1Obj.id)
  let gFreeCpAfterP2 := mustApply gFreeCpProposed p2 .concede
  -- Choose to pay `{2}` with empty mana pool, then click `.pay` -> CR 733.1 reverses back to `.castCopiesFree` with `cp2Obj` intact!
  let gFreeCpReversed := mustApply (mustApply gFreeCpAfterP2 p0 (.chooseAdditionalCost true)) p0 .pay
  -- Conversely, if `p0` has `{2}` mana and completes casting `cp1Obj`, `finishPostCast` ceases uncastable `cp2Obj`:
  let gFreeCpPayable := gFreeCpAfterP2.addMana p0 .colorless 2
  let gFreeCpCastDone := mustApply (mustApply gFreeCpPayable p0 (.chooseAdditionalCost true)) p0 .pay

  let item1aOk :=
    mustHold46i1 "1a_leaveSeqOrder"
      (gOrdLeaveAtPrompt.pending == .mayPayGeneric p0 3 &&
       (gOrdLeaveAtPrompt.player p0).life == 20 &&
       leaveOrderOk &&
       (gOrdLeaveDone.player p0).life == 131 &&
       gOrdLeaveDone.pending == .none) &&
    mustHold46i1 "1a_sbaSeqOrder"
      (gOrdSbaAtPrompt.pending == .mayPayGeneric p0 4 &&
       (gOrdSbaAtPrompt.player p0).life == 20 &&
       sbaOrderOk &&
       (gOrdSbaDone.player p0).life == 31 &&
       gOrdSbaDone.pending == .none) &&
    mustHold46i1 "1a_pendingFreeCopiesPreserved"
      (gFreeCpProposed.pendingFreeCopies == some (p0, #[cp2Obj.id], 0, 0) &&
       gFreeCpAfterP2.pendingFreeCopies == some (p0, #[cp2Obj.id], 0, 0) &&
       (gFreeCpAfterP2.findObject? cp2Obj.id).any (·.zone == .exile) &&
       gFreeCpReversed.pending == .fraChoice p0 (.castCopiesFree #[cp1Obj.id, cp2Obj.id] 2 1) &&
       (gFreeCpReversed.findObject? cp1Obj.id).any (·.zone == .exile) &&
       (gFreeCpReversed.findObject? cp2Obj.id).any (·.zone == .exile) &&
       gFreeCpCastDone.stack.size == 1 &&
       gFreeCpCastDone.pendingFreeCopies.isNone &&
       (gFreeCpCastDone.findObject? cp2Obj.id).isNone)

  -- 1b. `continuationGrantsPriority`, `priorityRecipientOfContinuation?`, `endsWithPriorityGrant`,
  --     `endsWithNonProposalPriorityGrant`, and `nextQueuedPending`:
  let gP1Gone := mustApply g4 p1 .concede
  let fcOrdinary : PendingReplacement := .finishConcede true (some p1) none none false #[] none
  let fcCombatDmg : PendingReplacement := .finishConcede false (some p2) (some true) none false #[] none
  let gWithQueuedCont :=
    g4.changes #[.pushContinuationFrame {}, .pushOuterPendingReplacement (.gainLife p0 1 (some testCause))]
  let gAllPassed := g4.change (.consecutivePasses 4)
  let cplOrdinary : PendingReplacement :=
    .concedePlayersLoop #[p1] false false true (some p1) none none false #[] none
  -- End-to-end `finishAndGrantPriority p0` must NOT hijack `.finishConcede`'s explicit `p2` grant:
  let gFcQueued :=
    (gP1Gone.changes #[.pushContinuationFrame {}, .pendingReplacement (some fcOrdinary)]).finishAndGrantPriority p0

  -- `.finishPostCast`: `hadOpenContinuation == false` (`some caster`), `hadOpenContinuation == true` (`some activePlayer`),
  -- and `none` when `pendingFreeCopies` opens `.castCopiesFree`:
  let gPcWithCastable :=
    gFreeCp0.changes #[
      .pushContinuationFrame {},
      .continuation (.pendingFreeCopies (some (p1, #[cp1Obj.id], 2, 1))) ]
  let gPcExhausted :=
    gFreeCp0.changes #[
      .pushContinuationFrame {},
      .continuation (.pendingFreeCopies (some (p1, #[cp1Obj.id], 0, 0))) ]

  -- Step / turn / cleanup continuations:
  let csntNoBegin : PendingReplacement := .continueStartNextTurn p1 #[] false
  let csntLiveP1 : PendingReplacement := .continueStartNextTurn p1 #[] true
  let csntDeadP1 : PendingReplacement := .continueStartNextTurn p1 #[] true
  let cleanupDiscLeaf : PendingReplacement := .finishPostStep .cleanupStepAfterDiscard
  let postSbaTrueLeaf : PendingReplacement := .finishPostStep (.postSbaCleanup true)
  let postSbaFalseLeaf : PendingReplacement := .finishPostStep (.postSbaCleanup false)
  let gCleanupQueued :=
    (g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some postSbaFalseLeaf) ]).finishAndGrantPriority p3

  -- Combat step leaves (`.untap`, `.declareAttackers`, `.declareBlockers`, `.combatDamage`):
  let gAtkReady := addPermanent g4 bear p0 p0
  let atkId := (gAtkReady.permanentsOf p0)[0]!.id
  let gWithAttacker :=
    gAtkReady.record (GameEvent.attacked gAtkReady.turnNumber p0 (gAtkReady.snapshot (gAtkReady.object! atkId)) p1)
  let gMultiBlocked0 := addPermanent (addPermanent gWithAttacker bear p1 p1) hero p1 p1
  let p1BlkIds := (gMultiBlocked0.permanentsOf p1).map (·.id)
  let gMultiBlocked :=
    (gMultiBlocked0.record
      (GameEvent.blockersDeclared gMultiBlocked0.turnNumber p1
        #[(gMultiBlocked0.snapshot (gMultiBlocked0.object! p1BlkIds[0]!), atkId),
          (gMultiBlocked0.snapshot (gMultiBlocked0.object! p1BlkIds[1]!), atkId)]
        (cause := some (.turnBased .declareBlockers)))).record
      (GameEvent.becameBlocked gMultiBlocked0.turnNumber
        (gMultiBlocked0.snapshot (gMultiBlocked0.object! atkId)) p1BlkIds
        (cause := some (.turnBased .declareBlockers)))

  let tricksterRestore : PendingReplacement :=
    .seq (.restorePending (.fraChoice p1 (.tricksterLibrary p0 ⟨99999⟩ (some ⟨99998⟩) none)) true)
      (.gainLife p0 0 none)
  let gFcQueuedViaRestore :=
    gP1Gone.changes #[
      .pendingPriority (some p2),
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.finishConcede false none none none false #[] none),
      .pendingReplacement (some tricksterRestore) ]
  let gFcAfterQueued := gFcQueuedViaRestore.finishAndGrantPriority p0
  let gPcQueuedViaRestore :=
    gP1Gone.changes #[
      .pendingPriority (some p2),
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.finishPostCast p3 true false false),
      .pendingReplacement (some tricksterRestore) ]
  let prePcAfterLen := gPcQueuedViaRestore.events.size
  let gPcAfterQueued := gPcQueuedViaRestore.finishAndGrantPriority p0
  let noPcOverwriteToP0 :=
    !(gPcAfterQueued.events.extract prePcAfterLen gPcAfterQueued.events.size).any fun ev =>
      ev.change == .engine (.pendingPriority (some p0))

  let item1bOk :=
    mustHold46i1 "1b_finishConcede"
      (gP1Gone.priorityRecipientOfContinuation? false fcOrdinary == some p2 &&
       gP1Gone.priorityRecipientOfContinuation? true fcOrdinary == some p2 &&
       gFcQueued.priority == p2 &&
       !gFcQueuedViaRestore.hasImplicitPriorityContinuation &&
       gFcAfterQueued.priority == p2 &&
       g4.priorityRecipientOfContinuation? false fcCombatDmg == none &&
       gWithQueuedCont.priorityRecipientOfContinuation? false (.finishConcede false (some p2) none none false #[] none) == none &&
       gAllPassed.priorityRecipientOfContinuation? false (.finishConcede true none none none false #[] none) == some p0 &&
       (((gAllPassed.record (GameEvent.stepBegan gAllPassed.turnNumber .beginningOfCombat p0)).priorityRecipientOfContinuation? false (.finishConcede true none none none false #[] none)) == none) &&
       g4.priorityRecipientOfContinuation? false cplOrdinary == some p2 &&
       g4.priorityRecipientOfContinuation? true cplOrdinary == some p2) &&
    mustHold46i1 "1b_finishPostCast"
      (g4.priorityRecipientOfContinuation? false (.finishPostCast p1 true false false) == some p1 &&
       g4.priorityRecipientOfContinuation? true (.finishPostCast p1 true false false) == some p1 &&
       g4.priorityRecipientOfContinuation? false (.finishPostCast p1 true false true) == some p0 &&
       g4.priorityRecipientOfContinuation? true (.finishPostCast p1 true false true) == some p0 &&
       !gPcQueuedViaRestore.hasImplicitPriorityContinuation &&
       gPcAfterQueued.priority == p3 &&
       noPcOverwriteToP0 &&
       gPcWithCastable.priorityRecipientOfContinuation? false (.finishPostCast p1 true false false) == none &&
       gPcExhausted.priorityRecipientOfContinuation? false (.finishPostCast p1 true false false) == some p1) &&
    mustHold46i1 "1b_cleanupAndTurn"
      (cleanupDiscLeaf.endsWithPriorityGrant &&
       cleanupDiscLeaf.endsWithNonProposalPriorityGrant &&
       !cleanupDiscLeaf.nextQueuedPending true &&
       postSbaFalseLeaf.endsWithPriorityGrant &&
       postSbaFalseLeaf.endsWithNonProposalPriorityGrant &&
       !postSbaFalseLeaf.nextQueuedPending true &&
       !csntNoBegin.endsWithPriorityGrant &&
       !g4.continuationGrantsPriority false csntNoBegin &&
       g4.priorityRecipientOfContinuation? false csntNoBegin == none &&
       g4.continuationGrantsPriority false csntLiveP1 &&
       g4.priorityRecipientOfContinuation? false csntLiveP1 == some p1 &&
       gP1Gone.continuationGrantsPriority false csntDeadP1 &&
       gP1Gone.priorityRecipientOfContinuation? false csntDeadP1 == some p2 &&
       g4.continuationGrantsPriority false cleanupDiscLeaf &&
       g4.priorityRecipientOfContinuation? false postSbaTrueLeaf == some p0 &&
       g4.priorityRecipientOfContinuation? false postSbaFalseLeaf == some p1 &&
       gCleanupQueued.activePlayer == p1 &&
       gCleanupQueued.priority == p1) &&
    mustHold46i1 "1b_combatSteps"
      (!PendingReplacement.endsWithPriorityGrant (.beginStepCont .untap) true &&
       !g4.continuationGrantsPriority false (.beginStepCont .untap) &&
       g4.priorityRecipientOfContinuation? true (.beginStepCont .untap) == none &&
       !g4.continuationGrantsPriority false (.finishPostStep (.beginStepBody .declareAttackers)) &&
       g4.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .declareAttackers)) == none &&
       g4.continuationGrantsPriority false (.finishPostStep (.beginStepBody .declareBlockers)) &&
       g4.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .declareBlockers)) == some p0 &&
       !gWithAttacker.continuationGrantsPriority false (.finishPostStep (.beginStepBody .declareBlockers)) &&
       gWithAttacker.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .declareBlockers)) == none &&
       gWithAttacker.continuationGrantsPriority false (.finishPostStep (.beginStepBody .combatDamage)) &&
       gWithAttacker.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .combatDamage)) == some p0 &&
       !gMultiBlocked.continuationGrantsPriority false (.finishPostStep (.beginStepBody .combatDamage)) &&
       gMultiBlocked.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .combatDamage)) == none)

  -- 1c. `.seq` proposal-reversal coverage across `.resumeChooseTargetsAfterLeave` / `.resumeChooseModeAfterLeave`
  --     (`followedByExplicitPriority?` forwarding & `| some none => none` clearing):
  let oppTgtSpellDef : CardDef := {
    name := "P46i1 HexBolt"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .oppCreature
      resolution := .gainLife 1
      phrase := "Target creature an opponent controls; gain 1 life."
    }
  }
  let gTgtRev0 := insertObject (addPermanent g4 hero p1 p1) oppTgtSpellDef p0 (.hand p0)
  let tgtHandId := (gTgtRev0.player p0).hand.back!
  let gTgtProposed := mustApply gTgtRev0 p0 (.cast tgtHandId)
  let p1HeroId := (gTgtProposed.permanentsOf p1)[0]!.id
  let (gTgtHeroGone, _) := (gTgtProposed.change (.pending .none)).move p1HeroId .exile none (cause := some testCause)
  -- `.resumeChooseTargetsAfterLeave p0` reverses `p0`'s targetless proposal, stops `.seq` before `gainLife 9`,
  -- and forwards `followedByExplicitPriority? := some p3`!
  let gTgtSeqRev :=
    gTgtHeroGone.resumePendingReplacement
      (.seq (.finishPostStep (.resumeChooseTargetsAfterLeave p0))
        (.seq (.gainLife p0 9 (some testCause)) (.receivePriority p3)))
  -- Nested `.seq`: inner `.finishFraChoice` (`firstPriorityGrantRecipient? == some none`) clears outer
  -- `followedByExplicitPriority? == some p3` so active-player priority (`p0`) is granted instead of `p3`:
  let gImplicitClearsOuter :=
    gTgtHeroGone.resumePendingReplacement
      (.seq
        (.seq (.finishPostStep (.resumeChooseTargetsAfterLeave p0)) .finishFraChoice)
        (.receivePriority p3))

  let item1cOk :=
    gTgtSeqRev.proposedSpell.isNone &&
    (gTgtSeqRev.player p0).life == 20 &&
    gTgtSeqRev.priority == p3 &&
    gImplicitClearsOuter.proposedSpell.isNone &&
    gImplicitClearsOuter.priority == p0

  mustHold46i1 "1a.chainOrMergeLeaveSeqAndFreeCopies" item1aOk &&
  mustHold46i1 "1b.priorityRecipientAndStepGrants" item1bOk &&
  mustHold46i1 "1c.seqReversalAndImplicitClear" item1cOk &&
  mustHold46i1 "1.replay"
    (replayOk46i1 #[gOrdLeaveDone, gOrdSbaDone, gFreeCpAfterP2, gFreeCpReversed, gFreeCpCastDone,
      gFcQueued, gFcAfterQueued, gPcAfterQueued, gCleanupQueued, gMultiBlocked, gTgtSeqRev, gImplicitClearsOuter])

end Phase46Item1EventAlignment

section Phase46Item2EventAlignment

private def mustHold46i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase46Item2EventAlignment failed: {label}"

private def replayOk46i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let embDef46 : CardDef := { name := "P46i2 Emblem", types := #[] }

  -- 2a. `.command` emblem `restoreCopiesWhere` copy-restoration logs (both `expireEffectById` and `ceaseToExist`)
  --     AND simultaneous timed / counter CR 800.4c `coDepartingIds` `skipLogIds`:
  let gEmbCopy0 := insertObject (addPermanent g4 bear p0 p0) embDef46 p0 .command (some p0)
  let liveBearId := (gEmbCopy0.permanentsOf p0)[0]!.id
  let embCmd := (gEmbCopy0.objects.filter (·.zone == .command))[0]!
  let gEmbCopy1 :=
    (gEmbCopy0.createEffect
      (.gameRule (.fraEmblem embCmd.id) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[liveBearId]) (.copy hero) (.whileInZone embCmd.id .command))
      (cause := some testCause)
  let embRuleEid := gEmbCopy1.activeEffects[0]!.1
  let preExpLog := gEmbCopy1.log.size
  let gEmbExpiredById := gEmbCopy1.expireEffectById embRuleEid (cause := some testCause)
  let expByIdLogs := gEmbExpiredById.log.extract preExpLog gEmbExpiredById.log.size
  let gEmbCeasedDirect := gEmbCopy1.ceaseToExist embCmd.id (cause := some testCause)
  let ceasedDirectLogs := gEmbCeasedDirect.log.extract preExpLog gEmbCeasedDirect.log.size

  -- Simultaneous CR 800.4c `coDepartingIds` `skipLogIds` across `clearEOT`, `beginTurn`, `expireUntilNextTurnEffects`,
  -- and `recordRemoveCountersMulti`:
  let gP3Gone := mustApply g4 p3 .concede
  let gCoLive0 := addPermanent g4 bear p0 p3
  let coBearId := (gCoLive0.permanentsOf p3)[0]!.id
  let gEotCo :=
    mustApply
      (((gCoLive0.createEffect (.layered (.objects #[coBearId]) (.control p0) .untilEndOfTurn)
          (cause := some testCause)).createEffect
        (.layered (.objects #[coBearId]) (.copy hero) .untilEndOfTurn)
        (cause := some testCause)))
      p3 .concede
  let preEotCoLog := gEotCo.log.size
  let gEotCoAfter := gEotCo.clearEOT
  let eotCoLogs := gEotCoAfter.log.extract preEotCoLog gEotCoAfter.log.size

  let gBeginTurnCo :=
    mustApply
      (((gCoLive0.createEffect (.layered (.objects #[coBearId]) (.control p0) (.untilNextTurnOf p1))
          (cause := some testCause)).createEffect
        (.layered (.objects #[coBearId]) (.copy hero) (.untilNextTurnOf p1))
        (cause := some testCause)))
      p3 .concede
  let preBeginTurnCoLog := gBeginTurnCo.log.size
  let gBeginTurnCoAfter := gBeginTurnCo.startNextTurnAndBegin
  let beginTurnCoLogs := gBeginTurnCoAfter.log.extract preBeginTurnCoLog gBeginTurnCoAfter.log.size

  let gNextTurnCo :=
    mustApply
      (((gCoLive0.createEffect (.layered (.objects #[coBearId]) (.control p0) (.untilNextTurnOf p3))
          (cause := some testCause)).createEffect
        (.layered (.objects #[coBearId]) (.copy hero) (.untilNextTurnOf p3))
        (cause := some testCause)))
      p3 .concede
  let preDepTurnCoLog := gNextTurnCo.log.size
  let gDepTurnCoAfter := gNextTurnCo.expireUntilNextTurnEffects p3
  let depTurnCoLogs := gDepTurnCoAfter.log.extract preDepTurnCoLog gDepTurnCoAfter.log.size

  let anchorArtDef : CardDef := { name := "P46i2 ChargeAnchor", types := #[.artifact] }
  let gCntCo0 :=
    let g := addPermanent gCoLive0 anchorArtDef p0 p0
    let aid := (g.permanentsOf p0).find? (·.name == anchorArtDef.name) |>.get!.id
    g.recordPutCounters aid .charge 1 (some p0) (cause := some testCause)
  let cntAnchorId := (gCntCo0.permanentsOf p0).find? (·.name == anchorArtDef.name) |>.get!.id
  let gCntCo1 :=
    mustApply
      (((gCntCo0.createEffect (.layered (.objects #[coBearId]) (.control p0) (.whileSourceHasCounter cntAnchorId .charge))
          (cause := some testCause)).createEffect
        (.layered (.objects #[coBearId]) (.copy hero) (.whileSourceHasCounter cntAnchorId .charge))
        (cause := some testCause)))
      p3 .concede
  let preCntCoLog := gCntCo1.log.size
  let gCntCoAfter := gCntCo1.recordRemoveCountersMulti cntAnchorId #[(.charge, 1)] (byPlayer := some p0) (cause := some testCause)
  let cntCoLogs := gCntCoAfter.log.extract preCntCoLog gCntCoAfter.log.size

  let item2aOk :=
    mustHold46i2 "2a_cmdEmblemCopyRestore"
      (gEmbCopy1.name (gEmbCopy1.object! liveBearId) == hero.name &&
       gEmbExpiredById.name (gEmbExpiredById.object! liveBearId) == bear.name &&
       expByIdLogs.any (· == s!"{bear.name} is no longer a copy of {hero.name}") &&
       gEmbCeasedDirect.name (gEmbCeasedDirect.object! liveBearId) == bear.name &&
       ceasedDirectLogs.any (· == s!"{bear.name} is no longer a copy of {hero.name}")) &&
    mustHold46i2 "2a_coDepartingSkipLogs"
      ((gEotCoAfter.followMovedToZone? coBearId (· == .exile)).isSome &&
       !eotCoLogs.any (·.contains "is no longer a copy") &&
       (gBeginTurnCoAfter.followMovedToZone? coBearId (· == .exile)).isSome &&
       !beginTurnCoLogs.any (·.contains "is no longer a copy") &&
       (gDepTurnCoAfter.followMovedToZone? coBearId (· == .exile)).isSome &&
       !depTurnCoLogs.any (·.contains "is no longer a copy") &&
       (gCntCoAfter.followMovedToZone? coBearId (· == .exile)).isSome &&
       !cntCoLogs.any (·.contains "is no longer a copy"))

  -- 2b. `Core.playPermissionEntriesOf`: `.exile -> .stack` (`!(o.isCopy && o.isAdventureSpell)`),
  --     reverse `depIdx?`, `durationActiveAt` (phased-out source), departed-grantee filtering,
  --     and `Turns` `hadPlayable` expiry logs:
  let advQuestFace : AdventureFace := {
    name := "P46i2 Quest"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { resolution := .gainLife 1, phrase := "Gain 1 life." }
  }
  let advCreatureDef : CardDef := { bear with name := "P46i2 Adventurer", adventure := some advQuestFace }
  let gExStack0 := insertObject gP3Gone advCreatureDef p0 .exile
  let exCardId := (gExStack0.objects.filter (·.zone == .exile))[0]!.id
  let gExStackPerm :=
    gExStack0.createEffect
      (.permission (some p0) (.playFromExile exCardId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  -- Cast the Adventure half from `.exile` onto `.stack`, then copy the Adventure spell on `.stack`:
  let gAdvFromExStack := mustApply gExStackPerm p0 (.castAdventure exCardId)
  let stackAdvId := gAdvFromExStack.stack.back!.objectId
  let (gAdvWithCopy, advCopyId?) := gAdvFromExStack.copyStackSpellWithId (gAdvFromExStack.object! stackAdvId) p0
  let advCopyId := advCopyId?.getD ⟨1⟩

  -- Phased-out `whileSourceOnBattlefield` source at `depIdx` -> `durationActiveAt` is `false`!
  let gPhSrcPerm0 := insertObject (addPermanent gP3Gone anchorArtDef p0 p0) bear p0 .exile
  let phPermSrc := (gPhSrcPerm0.permanentsOf p0)[0]!
  let phExId := (gPhSrcPerm0.objects.filter (·.zone == .exile))[0]!.id
  let gPhSrcPerm1 :=
    (gPhSrcPerm0.createEffect
      (.permission (some p0) (.playFromExile phExId { player := p0, withoutManaCost := true })
        (.whileSourceOnBattlefield phPermSrc.id))
      (cause := some testCause)).phaseOut phPermSrc (cause := some testCause)
  let (gPhSrcMovedOut, _) := gPhSrcPerm1.move phExId (.hand p0) none (cause := some testCause)

  -- Departed grantee `p3` (`!gP3Gone.stillInGame p3`) excluded from `playPermissionEntriesOf` and `hadPlayable`:
  let gDeadGrantee0 := insertObject gP3Gone bear p1 .exile
  let deadGrExId := (gDeadGrantee0.objects.filter (·.zone == .exile))[0]!.id
  let gDeadGranteeBoth :=
    ((gDeadGrantee0.createEffect
        (.permission (some p0) (.playFromExile deadGrExId { player := p0 }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p3) (.playFromExile deadGrExId { player := p3 }) (.untilNextTurnOf p1))
      (cause := some testCause))
  let preDeadGrEotLog := gDeadGranteeBoth.log.size
  let gDeadGrAfterEot := gDeadGranteeBoth.clearEOT
  let deadGrEotLogs := gDeadGrAfterEot.log.extract preDeadGrEotLog gDeadGrAfterEot.log.size
  let preDeadGrTurnLog := gDeadGrAfterEot.log.size
  let gDeadGrAfterTurn := gDeadGrAfterEot.expireFraUntilTurnEffects p1
  let deadGrTurnLogs := gDeadGrAfterTurn.log.extract preDeadGrTurnLog gDeadGrAfterTurn.log.size

  let item2bOk :=
    mustHold46i2 "2b_exileToStackAndAdvCopy"
      (stackAdvId != exCardId &&
       (gAdvFromExStack.playPermissionEntriesOf stackAdvId).size == 1 &&
       (gAdvFromExStack.playPermissionFor? p0 (gAdvFromExStack.object! stackAdvId)).any (·.withoutManaCost) &&
       advCopyId?.isSome &&
       (gAdvWithCopy.object! advCopyId).isCopy &&
       (gAdvWithCopy.object! advCopyId).isAdventureSpell &&
       (gAdvWithCopy.playPermissionEntriesOf advCopyId).isEmpty) &&
    mustHold46i2 "2b_nonexistentAndPhasedSrc"
      ((gAdvFromExStack.playPermissionEntriesOf ⟨999999⟩).isEmpty &&
       (gPhSrcMovedOut.playPermissionEntriesOf phExId).isEmpty) &&
    mustHold46i2 "2b_departedGranteeAndHadPlayable"
      ((gDeadGranteeBoth.playPermissionEntriesOf deadGrExId).size == 1 &&
       deadGrEotLogs.any (· == s!"{bear.name} can no longer be played from exile") &&
       !deadGrTurnLogs.any (· == s!"{bear.name} can no longer be played from exile"))

  -- 2c. Multi-permission ranking (`playPermissionsFor` / `playPermissionFor?`), `prepareSource`
  --     controller transfer & stack cast, and `Costs.playManaCost` (`playsWithoutPayingManaCost`):
  let costedAdvDef : CardDef := {
    name := "P46i2 CostedKnight"
    manaCost := ManaCost.ofGeneric 3
    types := #[.creature]
    subtypes := #["Knight"]
    power := some 3
    toughness := some 3
    adventure := some {
      name := "P46i2 PaidQuest"
      manaCost := ManaCost.ofGeneric 2
      types := #[.sorcery]
      spellEffect := some { resolution := .gainLife 2, phrase := "Gain 2 life." }
    }
  }
  let gMultiGrant0 := insertObject gP3Gone costedAdvDef p0 .exile
  let mgExId := (gMultiGrant0.objects.filter (·.zone == .exile))[0]!.id
  -- Earlier `withoutManaCost + ignoreTiming` + later paid sorcery-speed + earlier `fromAdventure` + clean second grant:
  let gMultiGrant1 :=
    (((gMultiGrant0.createEffect
        (.permission (some p0)
          (.playFromExile mgExId { player := p0, fromAdventure := true })
          .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p0)
        (.playFromExile mgExId { player := p0, withoutManaCost := true, ignoreTiming := true })
        .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0)
        (.playFromExile mgExId { player := p0 })
        .untilEndOfTurn)
      (cause := some testCause))
  let mgObj := gMultiGrant1.object! mgExId

  -- `prepareSource` stolen by `p1` (`becomePrepared` on `p0`, then `.control p1`, then `p1` casts the prepared copy):
  let prepCreatureDef : CardDef := {
    bear with
    name := "P46i2 PrepSquire"
    prepareFace := some {
      name := "P46i2 Rally"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellEffect := some { resolution := .gainLife 2, phrase := "Gain 2 life." }
    }
  }
  let gPrep0 := addPermanent gP3Gone prepCreatureDef p0 p0
  let prepSrcObj := (gPrep0.permanentsOf p0)[0]!
  let gPrep1 := gPrep0.becomePrepared prepSrcObj (cause := some testCause)
  let prepCopyId := (gPrep1.objects.filter (·.zone == .exile))[0]!.id
  let gPrepStolen :=
    gPrep1.createEffect (.layered (.objects #[prepSrcObj.id]) (.control p1) .untilEndOfTurn)
      (cause := some testCause)
  let gPrepStolenP1Prio := mustApply gPrepStolen p0 .pass
  let gPrepCastByP1 := mustApply gPrepStolenP1Prio p1 (.cast prepCopyId)
  let prepStackObj := gPrepCastByP1.object! gPrepCastByP1.stack.back!.objectId

  -- Unattributed `playsWithoutPayingManaCost` when owner `p0` has paid grant and non-owner `p1` has `withoutManaCost`,
  -- AND rejecting an unprepared `prepareSource` `withoutManaCost` grant (no `g.playPermission` fallback):
  let paidOgreDef : CardDef := creature "P46i2 Ogre" (ManaCost.ofGeneric 3) #["Ogre"] 2 2
  let gUnattr0 := insertObject gP3Gone paidOgreDef p0 .exile
  let unattrExId := (gUnattr0.objects.filter (·.zone == .exile))[0]!.id
  let gUnattr1 :=
    ((gUnattr0.createEffect
        (.permission (some p0) (.playFromExile unattrExId { player := p0 }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p1) (.playFromExile unattrExId { player := p1, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause))
  let gUnprepPerm0 := insertObject gPrep0 paidOgreDef p0 .exile
  let unprepExId := (gUnprepPerm0.objects.filter (·.zone == .exile))[0]!.id
  let gUnprepPerm1 :=
    gUnprepPerm0.createEffect
      (.permission (some p0)
        (.playFromExile unprepExId { player := p0, withoutManaCost := true, prepareSource := some prepSrcObj.id })
        .untilEndOfTurn)
      (cause := some testCause)

  let item2cOk :=
    mustHold46i2 "2c_multiGrantRankAndAdv"
      ((gMultiGrant1.playPermissionsFor p0 mgObj).size == 3 &&
       (gMultiGrant1.playPermissionFor? p0 mgObj).any (fun pm => pm.withoutManaCost && pm.ignoreTiming) &&
       gMultiGrant1.playsWithoutPayingManaCost mgObj &&
       gMultiGrant1.canCastAdventure p0 mgObj) &&
    mustHold46i2 "2c_prepareSourceTransfer"
      ((gPrepStolen.playPermissionsFor p0 (gPrepStolen.object! prepCopyId)).isEmpty &&
       (gPrepStolen.playPermissionsFor p1 (gPrepStolen.object! prepCopyId)).size == 1 &&
       (gPrepStolen.activePlayPermissions (gPrepStolen.object! prepCopyId)).map (·.player) == #[p1] &&
       !(gPrepCastByP1.object! prepSrcObj.id).status.prepared &&
       (gPrepCastByP1.playPermissionFor? p1 prepStackObj).any (·.player == p1)) &&
    mustHold46i2 "2c_unattributedBestPerm"
      ((gUnattr1.bestActivePlayPermission? (gUnattr1.object! unattrExId)).any (fun pm =>
         pm.player == p1 && pm.withoutManaCost) &&
       gUnattr1.playsWithoutPayingManaCost (gUnattr1.object! unattrExId) &&
       (gUnprepPerm1.playPermission (gUnprepPerm1.object! unprepExId)).isSome &&
       (gUnprepPerm1.bestActivePlayPermission? (gUnprepPerm1.object! unprepExId)).isNone &&
       gUnprepPerm1.playManaCost (gUnprepPerm1.object! unprepExId) paidOgreDef == ManaCost.ofGeneric 3 &&
       !gUnprepPerm1.playsWithoutPayingManaCost (gUnprepPerm1.object! unprepExId))

  mustHold46i2 "2a.commandEmblemRestoreAndCoDepartingSkip" item2aOk &&
  mustHold46i2 "2b.playPermissionEntriesOfScoping" item2bOk &&
  mustHold46i2 "2c.multiPermissionPrepareAndCosts" item2cOk &&
  mustHold46i2 "2.replay"
    (replayOk46i2 #[gEmbExpiredById, gEmbCeasedDirect, gEotCoAfter, gBeginTurnCoAfter, gDepTurnCoAfter, gCntCoAfter,
      gAdvWithCopy, gPhSrcMovedOut, gDeadGrAfterTurn, gMultiGrant1, gPrepCastByP1, gUnattr1, gUnprepPerm1])

end Phase46Item2EventAlignment

section Phase46Item3EventAlignment

private def mustHold46i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase46Item3EventAlignment failed: {label}"

private def replayOk46i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 3a. Aborted ETB-lookahead `ObjectId` (`⟨g4.nextObjectId⟩`) does NOT poison the subsequent real
  --     allocation of `⟨g4.nextObjectId⟩` in `Core.isInitialMaterialize`, whereas an already-live
  --     non-prospective reference (`grantor`) still marks the permanent as pre-existing:
  let nextProspId : ObjectId := ⟨g4.nextObjectId⟩
  let prospRid : ReplacementId := { kind := .asEntersChooseColor .red, object := some nextProspId }
  let gAbortedEtb :=
    (g4.changes #[
      .replacementOrder #[prospRid],
      .pending (.chooseReplacement p0 #[prospRid]),
      .pending .none,
      .replacementOrder #[] ]).record
      (GameEvent.life g4.turnNumber p0 1 (gained := true)
        (cause := .replaced { kind := .entersTappedSelf, object := some nextProspId } testCause))
  let preRealMatIdx := gAbortedEtb.events.size
  let gRealAlloc := addPermanent gAbortedEtb bear p0 p0
  let realAllocObj := (gRealAlloc.permanentsOf p0)[0]!

  let gLiveGrantor0 := quiet (addPermanent g4 bear p0 p0)
  let grantorPerm := (gLiveGrantor0.permanentsOf p0)[0]!
  let grantorRid : ReplacementId := {
    kind := .asEntersChooseColor .red
    object := some ⟨99998⟩
    grantor := some grantorPerm.id
  }
  let gLiveGrantor1 :=
    (gLiveGrantor0.changes #[
      .replacementOrder #[grantorRid],
      .replacementOrder #[] ]).change (.materializeObject grantorPerm)

  let item3aOk :=
    realAllocObj.id == nextProspId &&
    gRealAlloc.objectZoneAndPhasedOutAt? nextProspId preRealMatIdx == none &&
    gRealAlloc.objectZoneAndPhasedOutAt? nextProspId gRealAlloc.events.size == some (.battlefield, false) &&
    gLiveGrantor1.objectZoneAndPhasedOutAt? grantorPerm.id 0 == some (.battlefield, false)

  -- 3b. `objectCounterCountAt` post-bound `.ceasedToExist` & pre-log LKI filtering,
  --     `eventObjectIsLiveSubject` `StackObjectEvent.resolved`, and `stepHistoricalSlice` / `findEventObj` `.created` `eo.controller == none`:
  let gPreTokBase := insertObject g4 bear p0 .exile
  let tokExId := (gPreTokBase.objects.filter (·.zone == .exile))[0]!.id
  let (gPreTok000, preTok) := gPreTokBase.createOneToken p0 bear (extraCounters := #[(.charge, 2)]) (cause := some testCause)
  let gPreTokWithPerm :=
    (quiet gPreTok000).createEffect
      (.permission (some p0) (.playFromExile tokExId { player := p0 }) (.whileSourceHasCounter preTok.id .charge))
      (cause := some testCause)
  let (gPreTokMoved, _) := gPreTokWithPerm.move tokExId (.hand p0) none (cause := some testCause)
  let preTokBound := gPreTokMoved.events.size
  let gPreTokCeased := gPreTokMoved.ceaseToExist preTok.id (cause := some testCause)

  -- Pre-log departed token's non-live LKI snapshot in `[0 : bound]` must NOT seed `count?` (`|| count?.isNone` dropped):
  let deadTokSnap := gPreTok000.snapshot (gPreTok000.object! preTok.id)
  let gPreDeadQuiet :=
    (quiet gPreTokCeased).record
      (GameEvent.rules gPreTokCeased.turnNumber
        (.triggerQueue (.triggered deadTokSnap p0 default ⟨1⟩))
        testCause)

  -- `StackObjectEvent.resolved` does NOT resurrect `stackBearId` as a live `.stack` object:
  let gCastBear0 := insertObject g4 bear p0 (.hand p0)
  let gCastBearOnStack := mustApply gCastBear0 p0 (.cast (gCastBear0.player p0).hand.back!)
  let stackBearId := gCastBearOnStack.stack.back!.objectId
  let gCastBearResolved :=
    mustApply (mustApply (mustApply (mustApply gCastBearOnStack p0 .pass) p1 .pass) p2 .pass) p3 .pass
  let resolvedEvIdx? :=
    gCastBearResolved.events.findIdx? fun ev =>
      match ev.change with
      | .rules (.stackObject (.resolved eo ..)) => eo.id == some stackBearId
      | _ => false

  -- `stepHistoricalSlice` & `queueTriggersForBatch` (`findEventObj`) `ZoneEvent.created` with `eo.controller == none` on `.battlefield`:
  let tokWatcherDef : CardDef := {
    name := "P46i3 TokWatcher"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.ofPattern .tokenYouControlEnters "Draw a card." (.draw 1)]
  }
  let gCreatedStepBase := addPermanent g4 tokWatcherDef p1 p1
  let noCtrlTokId : ObjectId := ⟨gCreatedStepBase.nextObjectId + 15⟩
  let noCtrlTokEo : EventObject := {
    id := some noCtrlTokId
    name := "P46i3 NoCtrlWisp"
    owner := p1
    controller := none
    defaultController := some p1
    zone := .battlefield
    token := true
    types := #[.creature]
    power := some 1
    toughness := some 1
    printed := none
  }
  let gCreatedStep0 :=
    (gCreatedStepBase.record (GameEvent.created gCreatedStepBase.turnNumber p1 noCtrlTokEo (cause := testCause))).record
      (GameEvent.life gCreatedStepBase.turnNumber p0 1 (gained := true) (cause := testCause))
  let postStepCreateIdx := gCreatedStep0.events.size
  let gCreatedStepCeased := gCreatedStep0.ceaseToExist noCtrlTokId (cause := some testCause)
  let histAfterStepCreate := gCreatedStepCeased.mkHistoricalGameAt postStepCreateIdx
  let gBatchedTransientTok :=
    gCreatedStepBase.withBatch (some testCause) fun g =>
      (g.record (GameEvent.created g.turnNumber p1 noCtrlTokEo (cause := testCause))).ceaseToExist
        noCtrlTokId (cause := some testCause)

  let item3bOk :=
    mustHold46i3 "3b_postBoundCeasedAndPreLogLki"
      (gPreTokCeased.objectCounterCountAt preTok.id .charge preTokBound == 2 &&
       (gPreTokCeased.playPermissionEntriesOf tokExId).size == 1 &&
       gPreDeadQuiet.objectCounterCountAt preTok.id .charge gPreDeadQuiet.events.size == 0) &&
    mustHold46i3 "3b_resolvedNotLiveSubject"
      (match resolvedEvIdx? with
       | some rIdx =>
         gCastBearResolved.objectZoneAndPhasedOutAt? stackBearId (rIdx + 1) == none &&
         ((gCastBearResolved.mkHistoricalGameAt (rIdx + 1)).findObject? stackBearId).isNone
       | none => false) &&
    mustHold46i3 "3b_stepHistoricalCreatedController"
      ((histAfterStepCreate.findObject? noCtrlTokId).any (fun o =>
         histAfterStepCreate.controllerOf o == some p1 && o.printed.isToken) &&
       (gBatchedTransientTok.waitingTriggers.filter (·.pattern == .tokenYouControlEnters)).size == 1)

  -- 3c. Simultaneous `Phasing.phaseInControlledLoop`, newly phased-in `hadPriorCtrl` CR 800.4c exile
  --     + `Movement.preBatchBoardFor` `phasedOut == false`, `.ringBearer` & `reconcilePostReplayDepartures`
  --     phased-out guards, and `departedNextTurnWouldHaveBegunSince` pre-log regular-turn reconstruction:
  let gP2Gone := mustApply g4 p2 .concede
  let anchorArt3 : CardDef := { name := "P46i3 Anchor", types := #[.artifact] }
  -- Put `phDepB` (owned by departed `p2`) BEFORE `phAnchorA` so `phaseInControlledLoop` visits `phDepB` first!
  let gSimPh0 := addPermanent (addPermanent gP2Gone bear p2 p2) anchorArt3 p0 p0
  let phDepB := (gSimPh0.objects.filter (fun o => o.zone == .battlefield && o.name == bear.name))[0]!
  let phAnchorA := (gSimPh0.permanentsOf p0).find? (·.name == anchorArt3.name) |>.get!
  let gSimPh1 :=
    gSimPh0.createEffect
      (.layered (.objects #[phDepB.id]) (.control p0) (.whileSourceOnBattlefield phAnchorA.id))
      (cause := some testCause)
  let gSimPhBothOut :=
    gSimPh1.phaseOutPermanents #[gSimPh1.object! phDepB.id, gSimPh1.object! phAnchorA.id] (cause := some testCause)
  let gSimPhBothIn := gSimPhBothOut.phaseInControlled p0

  -- Orphaned `phDepB`: `phAnchorA` leaves while `phDepB` is phased out; when `phDepB` later phases in,
  -- `hadPriorCtrl` exiles `phDepB` via CR 800.4c with `before.phasedOut == false` (not stale `true`)!
  let gOrphanOut := gSimPh1.phaseOut (gSimPh1.object! phDepB.id) (cause := some testCause)
  let (gOrphanAnchorGone, _) := gOrphanOut.move phAnchorA.id .exile none (cause := some testCause)
  let preOrphanInIdx := gOrphanAnchorGone.events.size
  let gOrphanPhasedIn := gOrphanAnchorGone.phaseInControlled p0
  let orphanExileBeforePhasedOut? : Option Bool :=
    (gOrphanPhasedIn.events.extract preOrphanInIdx gOrphanPhasedIn.events.size).findSome? fun ev =>
      match ev.change with
      | .rules (.zone (.moved before _ .battlefield .exile ..)) =>
        if before.id == some phDepB.id then some before.phasedOut else none
      | _ => none

  -- `.ringBearer` preserved on phased-out permanent & `reconcilePostReplayDepartures` leaves phased-out permanent intact:
  let gRb0 := addPermanent gP2Gone bear p0 p0
  let rbId := (gRb0.permanentsOf p0)[0]!.id
  let gRbPhased :=
    (gRb0.record (GameEvent.ringTempted gRb0.turnNumber p0 (some rbId) 1 (cause := some testCause))).phaseOut
      (gRb0.object! rbId) (cause := some testCause)
  let gPostReplayGuard := gOrphanAnchorGone.reconcilePostReplayDepartures

  -- Pre-log regular-turn reconstruction in `departedNextTurnWouldHaveBegunSince`:
  -- (i) Pre-log extra turn (`hasPreLogPowerUpsForbidden == true`) followed by `.turnBegan p3 false`
  --     reconstructs `preLogRegSeat == p1` (instead of `startingPlayer == p0`), phasing in `preLogPhId`;
  -- (ii) Pre-log regular turn of `p1` followed by `.turnBegan p0 true` (extra) then `.turnBegan p3 false`
  --      keeps `preLogPhId2` phased out during `p0`'s extra turn and phases it in on `p3`'s regular turn:
  let gTurnRegP1 := g4.startNextTurnAndBegin
  let gInP3Extra0 :=
    (gTurnRegP1.record (GameEvent.extraTurnAdded gTurnRegP1.turnNumber p3 (cause := testCause))).startNextTurnAndBegin
  let gInP3Extra1 := addPermanent gInP3Extra0 bear p0 p0
  let preLogPhId := (gInP3Extra1.permanentsOf p0)[0]!.id
  let gInP3ExtraPhased :=
    (gInP3Extra1.createEffect (.layered (.objects #[preLogPhId]) (.control p2) .indefinite)
      (cause := some testCause)).phaseOut (gInP3Extra1.object! preLogPhId) (cause := some testCause)
  let gPreLogExtraP2Gone := mustApply (quiet gInP3ExtraPhased) p2 .concede
  let gP3RegAfterPreLogExtra :=
    (gPreLogExtraP2Gone.record (GameEvent.turnBegan (gPreLogExtraP2Gone.turnNumber + 1) p3 (extra := false))).phaseInControlled p3

  let gRegP1WithPh0 := addPermanent gTurnRegP1 bear p0 p0
  let preLogPhId2 := (gRegP1WithPh0.permanentsOf p0)[0]!.id
  let gRegP1Phased :=
    (gRegP1WithPh0.createEffect (.layered (.objects #[preLogPhId2]) (.control p2) .indefinite)
      (cause := some testCause)).phaseOut (gRegP1WithPh0.object! preLogPhId2) (cause := some testCause)
  let gPreLogRegP2Gone := mustApply (quiet gRegP1Phased) p2 .concede
  let gDuringP0Extra :=
    (gPreLogRegP2Gone.record (GameEvent.turnBegan (gPreLogRegP2Gone.turnNumber + 1) p0 (extra := true))).phaseInControlled p0
  let gP3RegAfterP0Extra :=
    (gDuringP0Extra.record (GameEvent.turnBegan (gDuringP0Extra.turnNumber + 1) p3 (extra := false))).phaseInControlled p3

  let item3cOk :=
    mustHold46i3 "3c_simPhaseIn"
      ((gSimPhBothIn.object! phAnchorA.id).isOnBattlefield &&
       (gSimPhBothIn.object! phDepB.id).isOnBattlefield &&
       gSimPhBothIn.controllerOf (gSimPhBothIn.object! phDepB.id) == some p0) &&
    mustHold46i3 "3c_orphanPhaseInExileAndPreBatchBoard"
      ((gOrphanPhasedIn.followMovedToZone? phDepB.id (· == .exile)).isSome &&
       orphanExileBeforePhasedOut? == some false) &&
    mustHold46i3 "3c_ringBearerAndReplayGuard"
      ((gRbPhased.player p0).ringBearerId == some rbId &&
       (gPostReplayGuard.object! phDepB.id).zone == .battlefield &&
       (gPostReplayGuard.object! phDepB.id).status.phasedOut) &&
    mustHold46i3 "3c_preLogRegularTurnReconstruction"
      (gInP3ExtraPhased.activePlayer == p3 &&
       gInP3ExtraPhased.lastRegularTurnSeat == p1 &&
       !(gP3RegAfterPreLogExtra.object! preLogPhId).status.phasedOut &&
       (gP3RegAfterPreLogExtra.object! preLogPhId).isOnBattlefield &&
       (gDuringP0Extra.object! preLogPhId2).status.phasedOut &&
       !(gP3RegAfterP0Extra.object! preLogPhId2).status.phasedOut &&
       (gP3RegAfterP0Extra.object! preLogPhId2).isOnBattlefield)

  mustHold46i3 "3a.abortedEtbLookaheadScoping" item3aOk &&
  mustHold46i3 "3b.counterCountLiveSubjectAndCreatedSlice" item3bOk &&
  mustHold46i3 "3c.phaseInBatchHadPriorCtrlAndPreLogTurn" item3cOk &&
  mustHold46i3 "3.replay"
    (replayOk46i3 #[gRealAlloc, gCastBearResolved, gCreatedStepCeased, gBatchedTransientTok,
      gSimPhBothIn, gOrphanPhasedIn, gRbPhased, gInP3ExtraPhased, gRegP1Phased])

end Phase46Item3EventAlignment

section Phase46Item4EventAlignment

private def mustHold46i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase46Item4EventAlignment failed: {label}"

private def replayOk46i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustStepAgent46 (g : Game) (p : PlayerId) : Game :=
  match Agent.choose g p with
  | some act => mustApply g p act
  | none => panic! "Phase46Item4EventAlignment: Agent.choose returned none"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 4a. Multi-tap CR 601.2h `Casting.preferredManaTap` subset preservation & `Agent.choose` `.chooseX` reservation:
  -- (i) `{1}{G}, Crew 2` with sources `[c22 ({C}, 2/2), c11a ({C}, 1/1), c11b ({G}, 1/1)]`:
  --     Single-tap `#[c22]` leaves `c11a + c11b` (power 2 >= 2), yet NO completion containing `c22` preserves
  --     `Crew 2` because `{G}` also requires `c11b`! `preferredManaTap` MUST pick from `{c11a, c11b}`!
  let dork22C : CardDef := { creature "P46i4 Pilot22C" ManaCost.empty #["Pilot"] 2 2 with activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])] }
  let dork11C : CardDef := { creature "P46i4 Dork11C" ManaCost.empty #["Scout"] 1 1 with activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])] }
  let dork11G : CardDef := { creature "P46i4 Dork11G" ManaCost.empty #["Elf"] 1 1 with activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])] }
  let crew1GVehDef : CardDef := {
    name := "P46i4 EmeraldSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGenericAndColor 1 .green), .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 2 }
    ]
  }
  let gMultiCrew0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g3 crew1GVehDef p0 p0) dork22C p0 p0)
        dork11C p0 p0)
      dork11G p0 p0
  let mcVehId := (gMultiCrew0.permanentsOf p0).find? (·.name == crew1GVehDef.name) |>.get!.id
  let mc22Id := (gMultiCrew0.permanentsOf p0).find? (·.name == dork22C.name) |>.get!.id
  let mc11CId := (gMultiCrew0.permanentsOf p0).find? (·.name == dork11C.name) |>.get!.id
  let mc11GId := (gMultiCrew0.permanentsOf p0).find? (·.name == dork11G.name) |>.get!.id
  let gMultiCrewProp := mustApply gMultiCrew0 p0 (.activate mcVehId 0)
  let singleTapWouldLookSafe :=
    gMultiCrewProp.tapPreservesPostManaCosts p0 gMultiCrewProp.proposedSpell.get! #[mc22Id]
  let prefTap1? := gMultiCrewProp.preferredManaTap p0 gMultiCrewProp.proposedSpell.get!
  let gMultiCrewTap1 := mustStepAgent46 gMultiCrewProp p0
  let gMultiCrewTap2 := mustStepAgent46 gMultiCrewTap1 p0
  let gMultiCrewPaid := mustApply gMultiCrewTap2 p0 .pay
  let gMultiCrewDone := mustApply gMultiCrewPaid p0 (.choosePermanents #[mc22Id])

  -- `.tapTwoUntappedArtifacts` with `[artMana1, artMana2, spareArt, forest]` for `{2}`:
  -- Tapping both `artMana1` and `artMana2` would leave only 1 untapped artifact (`spareArt`), violating `.tapTwoUntappedArtifacts`;
  -- `betterManaTap` (`avoidArtifacts`) prefers `forest` first, then 1 mana artifact, leaving 2 untapped artifacts!
  let manaRockDef : CardDef := { name := "P46i4 ManaRock", types := #[.artifact], activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])] }
  let spareArtDef : CardDef := { name := "P46i4 SpareCog", types := #[.artifact] }
  let tapTwoArt2ManaDef : CardDef := {
    name := "P46i4 ArtFoundry"
    types := #[.enchantment]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapObjects (.exact 2) (.all #[.hasType .artifact, .tapped false, .controlledBy .you])], effect := Effect.gainLife 3 }
    ]
  }
  let gTwoArt0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g3 tapTwoArt2ManaDef p0 p0) manaRockDef p0 p0)
          manaRockDef p0 p0)
        spareArtDef p0 p0)
      forest p0 p0
  let foundryId := (gTwoArt0.permanentsOf p0).find? (·.name == tapTwoArt2ManaDef.name) |>.get!.id
  let forestTwoArtId := (gTwoArt0.permanentsOf p0).find? (·.name == forest.name) |>.get!.id
  let rocks := (gTwoArt0.permanentsOf p0).filter (·.name == manaRockDef.name)
  let spareCogId := (gTwoArt0.permanentsOf p0).find? (·.name == spareArtDef.name) |>.get!.id
  let gTwoArtProp := mustApply gTwoArt0 p0 (.activate foundryId 0)
  let twoArtPrefPicksLandFirst :=
    match gTwoArtProp.preferredManaTap p0 gTwoArtProp.proposedSpell.get! with
    | some (o, _) => o.id == forestTwoArtId
    | none => false
  let gTwoArtTap1 := mustStepAgent46 gTwoArtProp p0
  let gTwoArtTap2 := mustStepAgent46 gTwoArtTap1 p0
  let gTwoArtPaid := mustApply gTwoArtTap2 p0 .pay
  let gTwoArtDone := mustApply gTwoArtPaid p0 (.choosePermanents #[rocks[1]!.id, spareCogId])

  -- (ii) `Agent.choose` `.chooseX` reserves `crewExcl` (`dork22C` kept for `Crew 2`, so `X == 2` from 2 forests, not `3`):
  let xCrewVehDef : CardDef := {
    name := "P46i4 XSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana { symbols := #[.x] }, .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 1 }
    ]
  }
  let gXCrew0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent g3 xCrewVehDef p0 p0) dork22C p0 p0) forest p0 p0)
      forest p0 p0
  let xVehId := (gXCrew0.permanentsOf p0).find? (·.name == xCrewVehDef.name) |>.get!.id
  let xPilotId := (gXCrew0.permanentsOf p0).find? (·.name == dork22C.name) |>.get!.id
  let gXCrewProp := mustApply gXCrew0 p0 (.activate xVehId 0)
  let agentChoosesX2 :=
    match Agent.choose gXCrewProp p0 with
    | some (.chooseX 2) => true
    | _ => false
  let gXCrewStep1 := mustApply gXCrewProp p0 (.chooseX 2)
  let gXCrewStep2 := mustStepAgent46 gXCrewStep1 p0
  let gXCrewStep3 := mustStepAgent46 gXCrewStep2 p0
  let gXCrewDone := mustApply (mustApply gXCrewStep3 p0 .pay) p0 (.choosePermanents #[xPilotId])

  let item4aOk :=
    mustHold46i4 "4a_multiCrewSubset"
      (singleTapWouldLookSafe &&
       prefTap1?.any (fun (o, _) => o.id == mc11CId || o.id == mc11GId) &&
       !(gMultiCrewPaid.object! mc22Id).status.tapped &&
       gMultiCrewDone.stack.size == 1) &&
    mustHold46i4 "4a_twoArtifactsSubset"
      (twoArtPrefPicksLandFirst &&
       gTwoArtDone.stack.size == 1) &&
    mustHold46i4 "4a_agentChooseXReservesCrew"
      (agentChoosesX2 &&
       gXCrewDone.stack.size == 1 &&
       (gXCrewDone.object! gXCrewDone.stack.back!.objectId).chosenX == some 2)

  -- 4b. Spell-scoped `Casting.sacrificeCreatureOrArtifactChoices` & Treasure mana provenance:
  let dualSacPermanentDef : CardDef := {
    name := "P46i4 AltarFiend"
    manaCost := ManaCost.empty
    types := #[.creature]
    subtypes := #["Demon"]
    power := some 3
    toughness := some 3
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))], effect := Effect.gainLife 2 }
    ]
  }
  let gDualSacBf0 := addPermanent (addPermanent g3 dualSacPermanentDef p0 p0) spareArtDef p0 p0
  let fiendBfId := (gDualSacBf0.permanentsOf p0).find? (·.name == dualSacPermanentDef.name) |>.get!.id
  let cogBfId := (gDualSacBf0.permanentsOf p0).find? (·.name == spareArtDef.name) |>.get!.id
  let bfChoicesIncludeArtifact :=
    (gDualSacBf0.sacrificeCreatureOrArtifactChoices p0 fiendBfId).any (·.id == cogBfId)
  let gDualSacAbDone := mustApply (mustApply (mustApply gDualSacBf0 p0 (.activate fiendBfId 0)) p0 .pay) p0 (.sacrifice cogBfId)
  -- When cast as a `.spell`, `additionalCostSacrificeCreature` still rejects non-creature artifacts:
  let gDualSpell0 := insertObject (addPermanent (addPermanent g3 spareArtDef p0 p0) bear p0 p0) dualSacPermanentDef p0 (.hand p0)
  let spellCogId := (gDualSpell0.permanentsOf p0).find? (·.name == spareArtDef.name) |>.get!.id
  let gDualSpellProp := mustApply gDualSpell0 p0 (.cast (gDualSpell0.player p0).hand.back!)
  let spellStackId := gDualSpellProp.proposedSpell.get!.spellId
  let gDualSpellAtSac := mustApply gDualSpellProp p0 .pay
  let spellChoicesExcludeArtifact :=
    !(gDualSpellProp.sacrificeCreatureOrArtifactChoices p0 spellStackId).any (fun o => o.name == spareArtDef.name) &&
    (gDualSpellAtSac.apply p0 (.sacrifice spellCogId)).toOption.isNone

  -- Treasure provenance across (1) battlefield `addMana`, (2) stack-resolved `abilityActivated`, and (3) `TriggerQueueEvent`:
  let stackTreasureDef : CardDef := {
    name := "P46i4 ModalTreasure"
    types := #[.artifact]
    subtypes := #["Treasure"]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self]
      effect := {
        targeting := .of .player
        resolution := .addMana #[.colored .red] (.fixed 2)
        phrase := "Target player; add {R}{R}."
      }
    }]
  }
  let gTr0 := addPermanent g3 stackTreasureDef p0 p0
  let trId := (gTr0.permanentsOf p0)[0]!.id
  let gTrBfDirect := gTr0.addMana p0 (.colored .green) 1 (source := some trId)
  -- Activate targeted ability on `stackTreasureDef` (sacrificing `trId` to `.graveyard` while `abilityId != trId` goes on `.stack`):
  let gTrStackAb := mustApply (mustApply gTr0 p0 (.activate trId 0)) p0 (.target (.player p0))
  let gTrStackRes := mustApply (mustApply (mustApply gTrStackAb p0 .pass) p1 .pass) p2 .pass
  -- Triggered ability from `stackTreasureDef` put on `.stack`, then `trId` leaves before resolution:
  let trTrigAb := TriggeredAbility.ofPattern (.gainLife .you) "Add {U}{U}." (.addMana #[.colored .blue] (.fixed 2))
  let gTrTrigOnStack := gTr0.putTriggeredAbilityOnStack p0 (gTr0.object! trId) trTrigAb "triggers" (eventCause := some testCause)
  let (gTrTrigGone, _) := gTrTrigOnStack.move trId (.graveyard p0) none (cause := some testCause)
  let gTrTrigRes := mustApply (mustApply (mustApply gTrTrigGone p0 .pass) p1 .pass) p2 .pass

  let item4bOk :=
    mustHold46i4 "4b_spellScopedSacChoices"
      (bfChoicesIncludeArtifact &&
       gDualSacAbDone.stack.size == 1 &&
       spellChoicesExcludeArtifact) &&
    mustHold46i4 "4b_treasureProvenance"
      ((gTrBfDirect.player p0).manaPool.units.all (fun u => u.fromTreasure && u.restriction.isNone) &&
       (gTrStackRes.player p0).manaPool.units.size == 2 &&
       (gTrStackRes.player p0).manaPool.units.all (fun u =>
         u.mana == .colored .red && u.fromTreasure && u.restriction.isNone) &&
       (gTrTrigRes.player p0).manaPool.units.size == 2 &&
       (gTrTrigRes.player p0).manaPool.units.all (fun u =>
         u.mana == .colored .blue && u.fromTreasure && u.restriction.isNone))

  -- 4c. `Resolution.addMana` `NumberSelector` (`amount != .fixed 1`), arbitrary-subtype
  --     `.addAnyColorSpendOnlySubtype` (`abilitySourceSubtypes`), and Layer 3 `TextChange` mana parity:
  let chargeDynamoDef : CardDef := {
    name := "P46i4 ChargeDynamo"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := { resolution := .addMana #[.colored .red] .perChargeCounter, phrase := "Add {R} for each charge counter." }
    }]
  }
  let ritual3Def : CardDef := {
    name := "P46i4 Ritual3"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { resolution := .addMana #[.colored .red] (.fixed 3), phrase := "Add {R}{R}{R}." }
  }
  let gDyn0 :=
    let g := addPermanent g3 chargeDynamoDef p0 p0
    let did := (g.permanentsOf p0)[0]!.id
    g.recordPutCounters did .charge 3 (some p0) (cause := some testCause)
  let dynId := (gDyn0.permanentsOf p0)[0]!.id
  let gDynTapped : Game :=
    match gDyn0.activateManaAbility p0 dynId 0 #[.colored .red, .colored .red, .colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gRit0 := insertObject g3 ritual3Def p0 (.hand p0)
  let gRitRes :=
    mustApply (mustApply (mustApply (mustApply gRit0 p0 (.cast (gRit0.player p0).hand.back!)) p0 .pass) p1 .pass) p2 .pass

  -- Arbitrary-subtype `.addAnyColorSpendOnlySubtype .goblin` (`ManaSpendRestriction.subtypeSpellOrSource .goblin`):
  let gobShrineDef : CardDef := {
    name := "P46i4 GoblinShrine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := {
        resolution := .addAnyColorSpendOnlySubtype .goblin
        phrase := "Add one mana of any color. Spend this mana only to cast a Goblin spell or to activate an ability of a Goblin source."
      }
    }]
  }
  let gobPermanentDef : CardDef := {
    name := "P46i4 GoblinTinkerer"
    manaCost := ManaCost.ofColor .red
    types := #[.creature]
    subtypes := #["Goblin"]
    power := some 1
    toughness := some 1
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)], effect := Effect.gainLife 2 }
    ]
  }
  let nonGobArtDef : CardDef := {
    name := "P46i4 PlainRelic"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)], effect := Effect.gainLife 1 }
    ]
  }
  let gGob0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent g3 gobShrineDef p0 p0) gobPermanentDef p0 p0) nonGobArtDef p0 p0)
      gobPermanentDef p0 (.hand p0)
  let shrineId := (gGob0.permanentsOf p0).find? (·.name == gobShrineDef.name) |>.get!.id
  let gobPermId := (gGob0.permanentsOf p0).find? (·.name == gobPermanentDef.name) |>.get!.id
  let plainRelicId := (gGob0.permanentsOf p0).find? (·.name == nonGobArtDef.name) |>.get!.id
  let gobHandId := (gGob0.player p0).hand.back!
  let gGobMana : Game :=
    match gGob0.activateManaAbility p0 shrineId 0 #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  -- Spend `.subtypeSpellOrSource .goblin` mana to activate `gobPermanentDef`'s `{1}` ability!
  let gGobAbPaid := mustApply (mustApply gGobMana p0 (.activate gobPermId 0)) p0 .pay
  -- Spend `.subtypeSpellOrSource .goblin` mana to cast `gobPermanentDef` spell!
  let gGobSpellPaid := mustApply (mustApply gGobMana p0 (.cast gobHandId)) p0 .pay
  -- Non-Goblin ability cannot pay `{1}` with `.subtypeSpellOrSource .goblin` mana (CR 733.1 reverses):
  let gNonGobAbProp := mustApply gGobMana p0 (.activate plainRelicId 0)
  let gNonGobAbRev := mustApply gNonGobAbProp p0 .pay
  let nonGobAbRejected :=
    gNonGobAbRev.stack.isEmpty &&
    gNonGobAbRev.proposedSpell.isNone &&
    (gNonGobAbRev.player p0).manaPool.restrictedEntries == #[(.colored .red, .subtypeSpellOrSource .goblin)]

  -- Layer 3 `TextChange` (`.replaceCreatureType`) mana parity:
  -- (1) `tapAddManaForEach` (`.elf` -> `.bear` with two Bears on battlefield -> `{G}{G}`),
  -- (2) `tapAddAnyColorEqualToPower` (`.elf` -> `.goblin`),
  -- (3) `.addAnyColorSpendOnlySubtype .elf` (`.elf` -> `.wizard`),
  -- (4) `.addFourManaDragonSpells 4 .dragon` (`.dragon` -> `.goblin`):
  let archdruidDef : CardDef := {
    creature "P46i4 Archdruid" ManaCost.empty #["Druid"] 2 2 with
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.sequence #[(.colored .green, .count (.inZones .battlefield (.all #[.hasSubtype (.literal .elf), .controlledBy .you])))])]
  }
  let powerChanDef : CardDef := {
    creature "P46i4 PowerChan" ManaCost.empty #["Druid"] 2 2 with
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.oneOf .anyColor (.objectStat .power .this))
      (restriction := some .elf)]
  }
  let dragonHoardSpellDef : CardDef := {
    name := "P46i4 DragonRitual"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      resolution := .addFourManaDragonSpells 4 .dragon
      phrase := "Add four mana in any combination of colors for Dragon spells."
    }
  }
  let gL3Base :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent
            (addPermanent (addPermanent g3 archdruidDef p0 p0) powerChanDef p0 p0)
            gobShrineDef p0 p0)
          bear p0 p0)
        bear p0 p0)
      dragonHoardSpellDef p0 (.hand p0)
  let archId := (gL3Base.permanentsOf p0).find? (·.name == archdruidDef.name) |>.get!.id
  let pchanId := (gL3Base.permanentsOf p0).find? (·.name == powerChanDef.name) |>.get!.id
  let l3ShrineId := (gL3Base.permanentsOf p0).find? (·.name == gobShrineDef.name) |>.get!.id
  let hoardHandId := (gL3Base.player p0).hand.back!
  let gL3Changed :=
    (((gL3Base.createEffect
        (.layered (.objects #[archId]) (.text (.replaceCreatureType .elf .bear)) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.layered (.objects #[pchanId]) (.text (.replaceCreatureType .elf .goblin)) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[l3ShrineId]) (.text (.replaceCreatureType .goblin .wizard)) .untilEndOfTurn)
      (cause := some testCause))
  let gArchTapped : Game :=
    match gL3Changed.activateManaAbility p0 archId 0 #[.colored .green, .colored .green] with
    | .ok g => g
    | .error e => panic! e
  let gPchanTapped : Game :=
    match gL3Changed.activateManaAbility p0 pchanId 0 #[.colored .red, .colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gL3ShrineTapped : Game :=
    match gL3Changed.activateManaAbility p0 l3ShrineId 0 #[.colored .blue] with
    | .ok g => g
    | .error e => panic! e
  let gHoardCast := mustApply gL3Changed p0 (.cast hoardHandId)
  let hoardStackId := gHoardCast.stack.back!.objectId
  let gHoardText :=
    gHoardCast.createEffect
      (.layered (.objects #[hoardStackId]) (.text (.replaceCreatureType .dragon .goblin)) .indefinite)
      (cause := some testCause)
  let gHoardResPrompt := mustApply (mustApply (mustApply gHoardText p0 .pass) p1 .pass) p2 .pass

  let item4cOk :=
    mustHold46i4 "4c_addManaNumberSelector"
      ((gDynTapped.player p0).manaPool.red == 3 &&
       (gRitRes.player p0).manaPool.red == 3) &&
    mustHold46i4 "4c_arbitrarySubtypeSpendOnly"
      ((gGobMana.player p0).manaPool.restrictedEntries == #[(.colored .red, .subtypeSpellOrSource .goblin)] &&
       gGobAbPaid.stack.size == 1 &&
       gGobSpellPaid.stack.size == 1 &&
       nonGobAbRejected) &&
    mustHold46i4 "4c_layer3TextChangeMana"
      ((gArchTapped.player p0).manaPool.green == 2 &&
       (gPchanTapped.player p0).manaPool.restrictedEntries ==
         #[(.colored .red, .subtypeSpellOrSource .goblin), (.colored .red, .subtypeSpellOrSource .goblin)] &&
       (gL3ShrineTapped.player p0).manaPool.restrictedEntries == #[(.colored .blue, .subtypeSpellOrSource .wizard)] &&
       gHoardResPrompt.pending == .fraChoice p0 (.addManaColors 4 (.subtypeSpell .goblin)))

  mustHold46i4 "4a.multiTapSubsetAndChooseX" item4aOk &&
  mustHold46i4 "4b.spellScopedSacAndTreasureProvenance" item4bOk &&
  mustHold46i4 "4c.addManaSelectorSubtypeAndLayer3" item4cOk &&
  mustHold46i4 "4.replay"
    (replayOk46i4 #[gMultiCrewDone, gTwoArtDone, gXCrewDone, gDualSacAbDone,
      gTrBfDirect, gTrStackRes, gTrTrigRes, gDynTapped, gRitRes,
      gGobAbPaid, gGobSpellPaid, gArchTapped, gPchanTapped, gL3ShrineTapped, gHoardResPrompt])

end Phase46Item4EventAlignment

end Mtg.Engine.EventTests
