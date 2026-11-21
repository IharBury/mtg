import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

section Phase50Item1EventAlignment

private def mustHold50i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase50Item1EventAlignment failed: {label}"

private def replayOk50i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let zeroToughDef : CardDef := creature "P50i1 Germ" ManaCost.empty #["Germ"] 0 0
  let legBearDef : CardDef := {
    creature "P50i1 LegendBear" ManaCost.empty #["Bear"] 2 2 with
    supertypes := #[.legendary]
  }
  let oddEvenDef : CardDef := {
    name := "P50i1 OddStatue"
    types := #[.artifact]
    staticAbilities := #[.asEntersChooseOddEven]
  }

  -- 1a(i). CR 800.4j `priorityInstead` normalization across `Decisions` probes when `p0`
  --        (`g.activePlayer`) has left the game (`g.priorityInstead p0 == p1`):
  let gP0Gone := (mustApply g4 p0 .concede).change (.pending .none)
  let gP0GoneSba := addPermanent gP0Gone zeroToughDef p1 p1
  let cleanupRecip :=
    gP0GoneSba.priorityRecipientOfContinuation? false .finishCleanupAfterClearEot
  let stepUpkeepRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.beginStepCont .upkeep)
  let bodyUpkeepRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .upkeep))
  let bodyAtkRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .declareAttackers))
  let postCastDepCasterRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.finishPostCast p0 true false false)
  let postCastOpenContRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.finishPostCast p2 true false true)
  let gPostCastRuntime := gP0Gone.finishPostCast p0 (grantPriority := true)
  let becomeCastGoneSpellRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.finishBecomeCast p2 ⟨999999⟩ true false true)
  let recvDepartedRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.receivePriority p0)
  let recvLivingRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.receivePriority p2)
  let actShrineDef : CardDef := {
    name := "P50i1 Shrine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)]
      effect := Effect.gainLife 1
    }]
  }
  let gP0GoneWithShrine := (addPermanent gP0Gone actShrineDef p2 p2).change (.priority p2)
  let shrineId := (gP0GoneWithShrine.permanentsOf p2).find? (·.name == actShrineDef.name) |>.get!.id
  let gP0GoneWithProp := (mustApply gP0GoneWithShrine p2 (.activate shrineId 0)).change (.pending .none)
  let compActRecip :=
    gP0GoneWithProp.priorityRecipientOfContinuation? false (.completeActivation false true)
  let becomeActRecip :=
    gP0Gone.priorityRecipientOfContinuation? false
      (.finishBecomeActivated p2 "Src" none none none none none false true)
  let loyActRecip :=
    gP0Gone.priorityRecipientOfContinuation? false
      (.finishPostLoyaltyActivated p2 "Src" none none none none none false true)
  let postSbaCleanupRecip :=
    gP0Gone.priorityRecipientOfContinuation? false (.finishPostStep (.postSbaCleanup true))

  -- 1a(ii). `.beginTurnAfterStartExpiry` departed-active-player probe parity & untap pause draining:
  let expTurnGrants := gP0Gone.continuationGrantsPriority false .beginTurnAfterStartExpiry
  let expTurnRecip := gP0Gone.priorityRecipientOfContinuation? false .beginTurnAfterStartExpiry
  let gExpTurnResumed := gP0Gone.resumePendingReplacement .beginTurnAfterStartExpiry

  -- Deferred `protectionFromEverything` turn-start expiry + `.untap` replacement pause draining:
  let gProtExp :=
    gP0Gone.createEffect (.protectionFromEverything p0) (cause := some testCause)
  let protExpGrants := gProtExp.continuationGrantsPriority false .beginTurnAfterStartExpiry
  let protExpRecip := gProtExp.priorityRecipientOfContinuation? false .beginTurnAfterStartExpiry
  let gProtExpResumed := gProtExp.resumePendingReplacement .beginTurnAfterStartExpiry

  -- Pre-paused `.chooseReplacement` queuing `.phaseInControlled p0` drains cleanly in `.beginTurnAfterStartExpiry`:
  let gUntapPaused :=
    gP0Gone.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.phaseInControlled p0)),
      .pending (.chooseReplacement p1 #[]) ]
  let untapPausedGrants := gUntapPaused.continuationGrantsPriority false .beginTurnAfterStartExpiry
  let untapPausedRecip := gUntapPaused.priorityRecipientOfContinuation? false .beginTurnAfterStartExpiry
  let g2pOver := mustApply afterDraw p0 .concede

  -- 1a(iii). `Decisions.keepLegend` continuation-first priority routing:
  let gKeepBase := addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0
  let keepLegIds := ((gKeepBase.permanentsOf p0).filter (·.name == legBearDef.name)).map (·.id)
  let gKeepQueuedP2 :=
    gKeepBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.receivePriority p2)),
      .pending (.chooseLegend p0 legBearDef.name keepLegIds) ]
  let gKeepResumed := mustApply gKeepQueuedP2 p0 (.keepLegend keepLegIds[0]!)

  let item1aOk :=
    mustHold50i1 "1a_priorityInsteadProbes"
      (gP0Gone.priorityInstead p0 == p1 &&
       cleanupRecip == some p1 &&
       stepUpkeepRecip == some p1 &&
       bodyUpkeepRecip == some p1 &&
       bodyAtkRecip == some p1 &&
       postCastDepCasterRecip == some p1 &&
       postCastOpenContRecip == some p1 &&
       gPostCastRuntime.priority == p1 &&
       becomeCastGoneSpellRecip == some p1 &&
       recvDepartedRecip == some p1 &&
       recvLivingRecip == some p2 &&
       compActRecip == some p1 &&
       becomeActRecip == some p1 &&
       loyActRecip == some p1 &&
       postSbaCleanupRecip == some p1) &&
    mustHold50i1 "1a_beginTurnAfterStartExpiryParity"
      (expTurnGrants &&
       expTurnRecip == some p1 &&
       gExpTurnResumed.step == .upkeep &&
       gExpTurnResumed.priority == p1 &&
       protExpGrants &&
       protExpRecip == some p1 &&
       gProtExpResumed.step == .upkeep &&
       gProtExpResumed.priority == p1 &&
       untapPausedGrants &&
       untapPausedRecip == some p1 &&
       !g2pOver.continuationGrantsPriority false .beginTurnAfterStartExpiry &&
       (g2pOver.priorityRecipientOfContinuation? false .beginTurnAfterStartExpiry).isNone) &&
    mustHold50i1 "1a_keepLegendContinuationFirst"
      (gKeepResumed.pending == .none &&
       gKeepResumed.priority == p2)

  -- 1b. `StateBasedActions.checkSBACounted` & `checkSBACountedWithLeavesCore` post-close
  --     repause restoration across BOTH `curBid? == none` (`g.currentBatch.isNone && g.sbaPaused`)
  --     and `curBid? == some newBid` (`newBid != bid`, `chainAfterOnRepause := false`), for both
  --     `flushedFromPending = true` and `flushedFromPending = false`, plus `savedIn` & `outerAfterIn?`:
  let liveP1Prompt : Pending := .mayPayGeneric p1 2
  let mkNoBatchRepauseBase (inPending : Bool) : Game × Array ObjectId := Id.run do
    let gA := insertObject (mustApply g4 p3 .concede) oddEvenDef p0 (.hand p0)
    let batchStartIdx := gA.events.size
    let (gPaused0, _) :=
      gA.putOntoBattlefield (gA.player p0).hand.back! p0 (cause := some testCause)
    let (bid, _) := gPaused0.currentBatch.get!
    -- Set an invalidated legend prompt (`clearedInvalidLegend == true` in `normalizePendingLegendChoice`)
    -- so `shouldFlush` fires even when `savedIn` holds a live prompt for `p1`:
    let gLeg :=
      addPermanent (addPermanent (gPaused0.changes #[
        .pending (.chooseLegend p3 legBearDef.name #[⟨99998⟩, ⟨99999⟩]),
        .pendingReplacement none ]) legBearDef p0 p0) legBearDef p0 p0
    let legIds := ((gLeg.permanentsOf p0).filter (·.name == legBearDef.name)).map (·.id)
    -- `splitAfterCloseBatchFor? bid` recurses into the RHS when the LHS has no `bid`, so
    -- `closePrefix` clears `currentBatch` (`curBid? == none`) and pauses on `.chooseLegend p0`!
    let prePauseNoBatch : PendingReplacement :=
      .seq (.closeBatch ⟨99999⟩ gLeg.events.size)
        (.restorePending (.chooseLegend p0 legBearDef.name legIds) false)
    let closeAndTail : PendingReplacement :=
      .seq prePauseNoBatch
        (.seq (.closeBatch bid batchStartIdx)
          (.seq .checkSBA (.gainLife p0 5 (some testCause))))
    let gOut :=
      if inPending then
        gLeg.changes #[
          .pushContinuationFrame {},
          .pendingReplacement (some closeAndTail) ]
      else
        gLeg.changes #[
          .pushContinuationFrame {},
          .pushOuterPendingReplacement closeAndTail ]
    return (gOut, legIds)

  -- (i) `checkSBACounted` with `curBid? == none` and `flushedFromPending = true` + live `savedIn`:
  let (gSbaPend0, sbaPendLegs) := mkNoBatchRepauseBase true
  let (gSbaPend1, sbaPendChanged) :=
    gSbaPend0.checkSBACounted (savedIn := some liveP1Prompt) (departedIn := #[p3])
  let gSbaPendAfterKeep := mustApply gSbaPend1 p0 (.keepLegend sbaPendLegs[0]!)
  let gSbaPendDone := mustApply gSbaPendAfterKeep p1 .decline

  -- (ii) `checkSBACounted` with `curBid? == none` and `flushedFromPending = false` (`popOuterIn = true`) + live `savedIn`:
  let (gSbaOuter0, sbaOuterLegs) := mkNoBatchRepauseBase false
  let (gSbaOuter1, sbaOuterChanged) :=
    gSbaOuter0.checkSBACounted (savedIn := some liveP1Prompt)
      (popOuterIn := true) (departedIn := #[p3])
  let gSbaOuterAfterKeep := mustApply gSbaOuter1 p0 (.keepLegend sbaOuterLegs[0]!)
  let gSbaOuterDone := mustApply gSbaOuterAfterKeep p1 .decline

  -- (iii) `checkSBACountedWithLeavesCore` with `curBid? == none`, `flushedFromPending = true`,
  --       `outerAfterIn?`, and pending loser `p2` (`r.lost && !r.leftTheGame`):
  let (gCorePend0, corePendLegs) := mkNoBatchRepauseBase true
  let gCorePendLoser :=
    gCorePend0.record (GameEvent.playerLost gCorePend0.turnNumber p2 .lifeZeroOrLess)
  let (gCorePend1, corePendChanged, _, _, _, _) :=
    gCorePendLoser.checkSBACountedWithLeavesCore
      (departedIn := #[p3])
      (outerAfterIn? := some (.gainLife p0 7 (some testCause)))
  let gCorePendDone := mustApply gCorePend1 p0 (.keepLegend corePendLegs[0]!)

  -- (iv) `curBid? == some newBid` (`newBid != bid`) via `queuedLinkedExile` returning `oddEvenDef`
  --      on `.closeBatch bid`: verifies `chainAfterOnRepause := false` prevents double-chaining
  --      `flushedPendingAfter?` (`life == 32`, not `37`) while folding `outerAfterIn?` + loser `p2`:
  let (gNewBid0, newBidLegs, origBid) : Game × Array ObjectId × BatchId := Id.run do
    let gA0 := insertObject (mustApply g4 p3 .concede) oddEvenDef p0 .exile
    let exOddId := gA0.objects.back!.id
    let gA := insertObject gA0 oddEvenDef p0 (.hand p0)
    let batchStartIdx := gA.events.size
    let (gPaused0, _) :=
      gA.putOntoBattlefield (gA.player p0).hand.back! p0 (cause := some testCause)
    let (bid, _) := gPaused0.currentBatch.get!
    let gLeg :=
      addPermanent (addPermanent (gPaused0.changes #[
        .pending (.chooseLegend p3 legBearDef.name #[⟨99998⟩, ⟨99999⟩]),
        .pendingReplacement none,
        .queueLinkedExile #[exOddId],
        .pushContinuationFrame {} ]) legBearDef p0 p0) legBearDef p0 p0
    let legIds := ((gLeg.permanentsOf p0).filter (·.name == legBearDef.name)).map (·.id)
    let closeAndTail : PendingReplacement :=
      .seq (.closeBatch bid batchStartIdx)
        (.seq .checkSBA (.gainLife p0 5 (some testCause)))
    let gWithLoser :=
      (gLeg.change (.pendingReplacement (some closeAndTail))).record
        (GameEvent.playerLost gLeg.turnNumber p2 .lifeZeroOrLess)
    return (gWithLoser, legIds, bid)
  let (gNewBid1, newBidChanged, _, newBidPop, _, _) :=
    gNewBid0.checkSBACountedWithLeavesCore
      (departedIn := #[p3])
      (outerAfterIn? := some (.gainLife p0 7 (some testCause)))
  let gNewBidAfterMode := mustApply gNewBid1 p0 (.chooseMode 0)
  let gNewBidDone := mustApply gNewBidAfterMode p0 (.keepLegend newBidLegs[0]!)

  let item1bOk :=
    mustHold50i1 "1b_checkSBACountedFlushedFromPendingNoBatch"
      (sbaPendChanged &&
       gSbaPend1.currentBatch.isNone &&
       (match gSbaPend1.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
       gSbaPendAfterKeep.pending == liveP1Prompt &&
       (gSbaPendAfterKeep.player p0).life == 20 &&
       gSbaPendDone.pending == .none &&
       (gSbaPendDone.player p0).life == 25) &&
    mustHold50i1 "1b_checkSBACountedFlushedFromOuterNoBatch"
      (sbaOuterChanged &&
       gSbaOuter1.currentBatch.isNone &&
       (match gSbaOuter1.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
       gSbaOuterAfterKeep.pending == liveP1Prompt &&
       (gSbaOuterAfterKeep.player p0).life == 20 &&
       gSbaOuterDone.pending == .none &&
       (gSbaOuterDone.player p0).life == 25) &&
    mustHold50i1 "1b_checkSBACountedWithLeavesCoreNoBatchOuterAfterAndLoser"
      (corePendChanged &&
       gCorePend1.currentBatch.isNone &&
       (match gCorePend1.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
       (gCorePendDone.player p2).leftTheGame &&
       gCorePendDone.pending == .none &&
       (gCorePendDone.player p0).life == 32) &&
    mustHold50i1 "1b_checkSBACountedWithLeavesCoreNewBatchNoDoubleChain"
      (newBidChanged &&
       newBidPop &&
       gNewBid1.currentBatch.any (fun (b, _) => b != origBid) &&
       (match gNewBid1.pending with | .chooseReplacement q _ => q == p0 | _ => false) &&
       (gNewBidAfterMode.player p2).leftTheGame &&
       (match gNewBidAfterMode.pending with | .chooseLegend q _ _ => q == p0 | _ => false) &&
       gNewBidDone.pending == .none &&
       (gNewBidDone.player p0).life == 32)

  mustHold50i1 "1a.probesAndKeepLegend" item1aOk &&
  mustHold50i1 "1b.sbaPostCloseRepauseRewrite" item1bOk &&
  mustHold50i1 "1.replay"
    (replayOk50i1 #[
      gP0Gone, gPostCastRuntime, gExpTurnResumed, gProtExpResumed, gKeepResumed,
      gSbaPend1, gSbaPendAfterKeep, gSbaPendDone,
      gSbaOuter1, gSbaOuterAfterKeep, gSbaOuterDone,
      gCorePend1, gCorePendDone,
      gNewBid1, gNewBidAfterMode, gNewBidDone ])

end Phase50Item1EventAlignment

section Phase50Item2EventAlignment

private def mustHold50i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase50Item2EventAlignment failed: {label}"

private def replayOk50i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def isCastAction (a : Option Action) (id : ObjectId) : Bool :=
  match a with
  | some (.cast cid) => cid == id
  | _ => false

private def isCastDirect (a : Action) (id : ObjectId) : Bool :=
  match a with
  | .cast cid => cid == id
  | _ => false

private def isDeclineAction (a : Option Action) : Bool :=
  match a with
  | some .decline => true
  | _ => false

private def isDeclineDirect (a : Action) : Bool :=
  match a with
  | .decline => true
  | _ => false

private def isAcceptDirect (a : Action) : Bool :=
  match a with
  | .accept => true
  | _ => false

private def isAnnounceKicker (a : Option Action) (want : Bool) : Bool :=
  match a with
  | some (.announceKicker v) => v == want
  | _ => false

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 2a. `Turns.expireFraUntilTurnEffects` pre-copy-restore `preState?` snapshot across
  --     `expireUntilNextTurnEffects` (`!teamHasLiving`) and `beginTurn` (`isSharedTurnFirstSeat`):
  let nullSummonerCloneDef : CardDef := {
    creature "P50i2 NullSummoner" ManaCost.empty #["Wizard"] 2 3 with
    staticAbilities := #[.castExiledWithSevenInGraveyard]
  }
  let exiledSpellDef : CardDef := {
    name := "P50i2 ExiledBolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some (Effect.gainLife 2)
  }
  -- Build a state where `p1` controls `bear` copied into `nullSummonerCloneDef` until `p0`'s next
  -- turn, `p1` has 7 cards in graveyard, `exId` was exiled with `exiledBy := some copierId`, and
  -- `exId` also has an expiring `.playFromExile exId { player := p2 } (.untilNextTurnOf p0)` where
  -- `p2` has left the game (`(pre.activePlayPermissions exObj).isEmpty == true`, while
  -- `pre.mayCastExiledBySource p1 exObj == true` BEFORE `restoreCopiesUntilNextTurn p0` and `false` AFTER):
  let mkPreCopyExpiryGame : Game × ObjectId := Id.run do
    let mut g := mustApply (addPermanent g3 bear p1 p1) p2 .concede
    for _ in [0:7] do
      g := insertObject g bear p1 (.graveyard p1)
    let copierId := (g.permanentsOf p1)[0]!.id
    g := insertObject g exiledSpellDef p1 (.hand p1)
    let handCardId := (g.player p1).hand.back!
    let (gMoved0, exId) :=
      g.move handCardId .exile none (cause := some testCause)
    let gMoved := gMoved0.changeObject exId (.exiledBy (some copierId))
    g :=
      (gMoved.createEffect
        (.layered (.objects #[copierId]) (.copy nullSummonerCloneDef) (.untilNextTurnOf p0))
        (cause := some testCause)).createEffect
        (.permission (some p2) (.playFromExile exId { player := p2 }) (.untilNextTurnOf p0))
        (cause := some testCause)
    return (g, exId)

  -- (i) `expireUntilNextTurnEffects p0` when `!teamHasLiving` (`p0` has left in a 4-player game):
  let p3 : PlayerId := ⟨3⟩
  let (gDepPre0, exDepId) := mkPreCopyExpiryGame
  let gDepPre1 :=
    mustApply (gDepPre0.change (.addPlayer { id := p3, name := "Jace" })) p0 .concede
  let preDepLogSize := gDepPre1.log.size
  let gDepExpired := gDepPre1.expireUntilNextTurnEffects p0
  let depLogs := gDepExpired.log.extract preDepLogSize gDepExpired.log.size

  -- (ii) `beginTurn` (`isSharedTurnFirstSeat` `preExpire` when `p0` begins their turn):
  let (gBeginPre0, exBeginId) := mkPreCopyExpiryGame
  let preBeginLogSize := gBeginPre0.log.size
  let gBeginExpired := gBeginPre0.beginTurn
  let beginLogs := gBeginExpired.log.extract preBeginLogSize gBeginExpired.log.size

  let item2aOk :=
    mustHold50i2 "2a_expireUntilNextTurnEffectsPreState"
      ((gDepExpired.findObject? exDepId).isSome &&
       depLogs.any (· == s!"{exiledSpellDef.name} can no longer be played from exile")) &&
    mustHold50i2 "2a_beginTurnSharedFirstSeatPreState"
      ((gBeginExpired.findObject? exBeginId).isSome &&
       beginLogs.any (· == s!"{exiledSpellDef.name} can no longer be played from exile"))

  -- 2b. Impending (`CR 702.176a`) castability & affordability across `Casting.canCastAndPayImpending`,
  --     `Agent` (`chooseCast`, `shouldActivate`, `.mayCastExiledElseDamage`, `.chooseKicker`), and
  --     paid `FraChoices.defaultFraAction` `.mayCastCards` (both Morph and Impending):
  let impendingOverlordDef : CardDef := {
    creature "P50i2 MistOverlord" (ManaCost.ofGeneric 6) #["Avatar"] 5 5 with
    types := #[.enchantment, .creature]
    keywords := #[.impending 4 (CostSpec.ofGeneric 2)]
  }
  let impendingCyclerDef : CardDef := {
    impendingOverlordDef with
    name := "P50i2 CyclingOverlord"
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .discard (.exact 1) .self]
      activeZones := #[.hand]
      effect := Effect.draw 1
    }]
  }
  let morphBehemothDef : CardDef := {
    creature "P50i2 MorphBehemoth" (ManaCost.ofGeneric 7) #["Beast"] 6 6 with
    keywords := #[.morph (CostSpec.ofGeneric 3)]
  }

  let gImpBase := emptyHand g3 p0
  let gImpHand1 := (insertObject gImpBase impendingOverlordDef p0 (.hand p0)).addMana p0 .colorless 1
  let impHand1Obj := gImpHand1.object! (gImpHand1.player p0).hand.back!
  let gImpHand2 := (insertObject gImpBase impendingOverlordDef p0 (.hand p0)).addMana p0 .colorless 2
  let impHand2Id := (gImpHand2.player p0).hand.back!
  let impHand2Obj := gImpHand2.object! impHand2Id
  let gImpGy2 := (insertObject gImpBase impendingOverlordDef p0 (.graveyard p0)).addMana p0 .colorless 2
  let impGyObj := gImpGy2.object! (gImpGy2.player p0).graveyard.back!

  -- `Agent.choose` casts `impHand2Id` from `morphOnlyPlayable`, then chooses `.announceKicker true`
  -- at `.chooseKicker` when front `{6}` is unaffordable (and `.announceKicker false` when `{6}` IS affordable):
  let agChooseCast2 := Agent.choose gImpHand2 p0
  let gImpProposed2 := mustApply gImpHand2 p0 (.cast impHand2Id)
  let agChooseKicker2 := Agent.choose gImpProposed2 p0
  let gImpCastPaid := mustApply (mustApply gImpProposed2 p0 (.announceKicker true)) p0 .pay
  let gImpEntered := mustApply (mustApply (mustApply gImpCastPaid p0 .pass) p1 .pass) p2 .pass

  let gImpHand6 := gImpHand2.addMana p0 .colorless 4
  let gImpProposed6 := mustApply gImpHand6 p0 (.cast impHand2Id)
  let agChooseKicker6 := Agent.choose gImpProposed6 p0

  -- `Agent` `shouldActivate` does not cycle `impendingCyclerDef` when Impending `{2}` is payable:
  let gCyc2 := (insertObject gImpBase impendingCyclerDef p0 (.hand p0)).addMana p0 .colorless 2
  let cycId := (gCyc2.player p0).hand.back!
  let agChooseCyc2 := Agent.choose gCyc2 p0

  -- `Agent` `.mayCastExiledElseDamage`: casts exiled `impendingOverlordDef` with 2 mana, declines with 1 mana:
  let gExImp0 := insertObject gImpBase impendingOverlordDef p0 .exile
  let exImpId := (gExImp0.objects.filter (fun o => o.zone == .exile)).back!.id
  let gExElse1 :=
    (gExImp0.addMana p0 .colorless 1).change (.pending (.mayCastExiledElseDamage p0 exImpId 3 none))
  let gExElse2 :=
    (gExImp0.addMana p0 .colorless 2).change (.pending (.mayCastExiledElseDamage p0 exImpId 3 none))
  let agExElse1 := Agent.choose gExElse1 p0
  let agExElse2 := Agent.choose gExElse2 p0

  -- `FraChoices.defaultFraAction` `.mayCastCards` (`withoutPaying := false`) handles both Impending & Morph:
  let gFraImp1 := gExImp0.addMana p0 .colorless 1
  let gFraImp2 := gExImp0.addMana p0 .colorless 2
  let fraImp1Act := gFraImp1.defaultFraAction p0 (.mayCastCards #[exImpId] false false)
  let fraImp2Act := gFraImp2.defaultFraAction p0 (.mayCastCards #[exImpId] false false)

  let gExMorph0 := insertObject gImpBase morphBehemothDef p0 .exile
  let exMorphId := (gExMorph0.objects.filter (fun o => o.zone == .exile)).back!.id
  let gFraMorph2 := gExMorph0.addMana p0 .colorless 2
  let gFraMorph3 := gExMorph0.addMana p0 .colorless 3
  let fraMorph2Act := gFraMorph2.defaultFraAction p0 (.mayCastCards #[exMorphId] false false)
  let fraMorph3Act := gFraMorph3.defaultFraAction p0 (.mayCastCards #[exMorphId] false false)

  let item2bOk :=
    mustHold50i2 "2b_canCastAndPayImpending"
      (!gImpHand1.canCastAndPayImpending p0 impHand1Obj &&
       gImpHand2.canCastAndPayImpending p0 impHand2Obj &&
       !gImpGy2.canCastAndPayImpending p0 impGyObj) &&
    mustHold50i2 "2b_agentCastKickerAndNoCycle"
      (isCastAction agChooseCast2 impHand2Id &&
       isAnnounceKicker agChooseKicker2 true &&
       isAnnounceKicker agChooseKicker6 false &&
       (gImpEntered.permanentsOf p0).any (fun o =>
         o.name == impendingOverlordDef.name && o.status.time == 4 && !gImpEntered.isCreature o) &&
       isCastAction agChooseCyc2 cycId) &&
    mustHold50i2 "2b_agentMayCastExiledElseDamageAndFraMayCastCards"
      (isDeclineAction agExElse1 &&
       isCastAction agExElse2 exImpId &&
       isDeclineDirect fraImp1Act &&
       isCastDirect fraImp2Act exImpId &&
       isDeclineDirect fraMorph2Act &&
       isCastDirect fraMorph3Act exMorphId)

  mustHold50i2 "2a.expireFraUntilTurnEffectsPreState" item2aOk &&
  mustHold50i2 "2b.impendingParity" item2bOk &&
  mustHold50i2 "2.replay"
    (replayOk50i2 #[
      gDepExpired, gBeginExpired, gImpHand2, gImpProposed2, gImpCastPaid, gImpEntered,
      gImpProposed6, gCyc2, gExElse1, gExElse2, gFraImp2, gFraMorph3 ])

end Phase50Item2EventAlignment

section Phase50Item3EventAlignment

private def mustHold50i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase50Item3EventAlignment failed: {label}"

private def replayOk50i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let equipDef : CardDef := {
    name := "P50i3 PhaseBlade"
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  let oddEvenDef : CardDef := {
    name := "P50i3 OddStatue"
    types := #[.artifact]
    staticAbilities := #[.asEntersChooseOddEven]
  }

  -- 3a(i). `Phasing.phaseInControlled` defers `targetIds` evaluation when `sbaPausedOnPhasing g`
  --        holds on entry: `p0`'s Equipment `eq` phased out indirectly with `p1`'s `host`
  --        (`phasedWith == some hostObj.id`), while an open replacement prompt precedes
  --        `phaseInControlled p0` and `p1` leaves the game (removing `host`) before `phaseInControlled p0` runs:
  let gInd0 := addPermanent (addPermanent g3 bear p1 p1) equipDef p0 p0
  let hostObj := (gInd0.permanentsOf p1)[0]!
  let eqObj0 := (gInd0.permanentsOf p0).find? (·.name == equipDef.name) |>.get!
  let gIndAttached := gInd0.attachSourceTo eqObj0 hostObj (cause := some testCause)
  -- Phase out `hostObj`: `eqObj0` phases out indirectly with `hostObj`!
  let gIndPhased := gIndAttached.phaseOut (gIndAttached.object! hostObj.id) (cause := some testCause)
  let eqIndObj := gIndPhased.object! eqObj0.id
  let initiallyIndirect :=
    eqIndObj.status.phasedOut && eqIndObj.status.phasedWith == some hostObj.id &&
      (gIndPhased.phaseInControlled p0 |>.object! eqObj0.id).status.phasedOut
  -- Pause on `oddEvenDef` entering for `p0`, then call `phaseInControlled p0` while paused:
  let gIndPause0 := insertObject gIndPhased oddEvenDef p0 (.hand p0)
  let (gIndPaused, _) :=
    gIndPause0.putOntoBattlefield (gIndPause0.player p0).hand.back! p0 (cause := some testCause)
  let gIndDeferred := gIndPaused.phaseInControlled p0
  -- Before resolving `p0`'s replacement choice, `p1` concedes (`hostObj` leaves the game, making
  -- `canPhaseInDirectly eq == true`), then `p0` resolves `.chooseMode 0`: `eq` phases in!
  let gIndP1Gone := mustApply gIndDeferred p1 .concede
  let gIndResumed := mustApply gIndP1Gone p0 (.chooseMode 0)

  -- 3a(ii). `PendingReplacement.phaseInControlledLoop` explicit `allowDirectSingle`:
  --         - `Game.splitAfterCloseBatchFor?` preserves both `false` and `true`;
  --         - `.phaseInControlledLoop #[eq.id] cause none false false` (`startEventIdx == none`,
  --           `allowDirectSingle == false`) does NOT bypass `canPhaseInDirectly` (CR 702.26h),
  --           whereas direct `g.phaseIn eq` (`allowDirectSingle := true`) DOES phase `eq` in!
  let testBid : BatchId := ⟨42⟩
  let prSplitFalse : PendingReplacement :=
    .seq (.closeBatch testBid 0)
      (.seq (.phaseInControlledLoop #[] (some testCause) none true false) (.receivePriority p0))
  let prSplitTrue : PendingReplacement :=
    .seq (.closeBatch testBid 0)
      (.seq (.phaseInControlledLoop #[] (some testCause) none true true) (.receivePriority p0))
  let splitPreservesFalse :=
    Game.splitAfterCloseBatchFor? testBid prSplitFalse ==
      some (PendingReplacement.seq (.closeBatch testBid 0) (.phaseInControlledLoop #[] (some testCause) none true false),
            some (PendingReplacement.receivePriority p0))
  let splitPreservesTrue :=
    Game.splitAfterCloseBatchFor? testBid prSplitTrue ==
      some (PendingReplacement.seq (.closeBatch testBid 0) (.phaseInControlledLoop #[] (some testCause) none true true),
            some (PendingReplacement.receivePriority p0))

  let gLoopBlocked :=
    gIndPhased.resumePendingReplacement
      (.phaseInControlledLoop #[eqObj0.id] (some (.turnBased .phaseInOut)) none false false)
  let gDirectAllowed :=
    gIndPhased.phaseIn (gIndPhased.object! eqObj0.id) (cause := some testCause)

  let item3aOk :=
    mustHold50i3 "3a_deferredPhaseInControlledPostPause"
      (initiallyIndirect &&
       !(gIndResumed.object! eqObj0.id).status.phasedOut) &&
    mustHold50i3 "3a_allowDirectSingleGuardAndSplit"
      (splitPreservesFalse &&
       splitPreservesTrue &&
       (gLoopBlocked.object! eqObj0.id).status.phasedOut &&
       !(gDirectAllowed.object! eqObj0.id).status.phasedOut)

  -- 3b(i). CR 702.26b `!phasedOut` counter/tap trigger suppression across `Event.countersPutInEvent`,
  --        `Event.matchesTrigger`, and `Core.matchTriggers`:
  let plusOneWatcherDef : CardDef := {
    creature "P50i3 PlusOneWatcher" ManaCost.empty #["Hero"] 1 4 with
    triggeredAbilities := #[SharedTrigger.resource .plusOneOnHeroesCreateWall |>.toTriggeredAbility]
  }
  let goblinWatcherDef : CardDef := {
    name := "P50i3 GoblinWatcher"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.ofPattern .youPutCountersOnGoblinOrcArmy "" (.draw 1)
      (grouping := .oncePerBatch)]
  }
  let tapWatcherDef : CardDef := {
    name := "P50i3 TapWatcher"
    types := #[.enchantment]
    triggeredAbilities := #[SharedTrigger.watch .firstTapUntap |>.toTriggeredAbility]
  }
  let goblinHeroDef : CardDef :=
    creature "P50i3 GoblinHero" ManaCost.empty #["Goblin", "Hero"] 2 2
  let gPo0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g3 plusOneWatcherDef p0 p0) goblinWatcherDef p0 p0)
        tapWatcherDef p0 p0)
      goblinHeroDef p0 p0
  let ghObj0 := (gPo0.permanentsOf p0).find? (·.name == goblinHeroDef.name) |>.get!
  let gPo1 := gPo0.phaseOut ghObj0 (cause := some testCause)
  let phasedSnap := gPo1.snapshot (gPo1.object! ghObj0.id)
  let phasedCtrEv :=
    GameEvent.counters gPo1.turnNumber (some p0) phasedSnap .plusOnePlusOne 1 (cause := testCause)
  let phasedTapEv :=
    GameEvent.tapped gPo1.turnNumber phasedSnap (cause := testCause)
  let gPoBatch :=
    gPo1.withBatch (some testCause) fun g =>
      (g.record phasedCtrEv).record phasedTapEv

  let phasedSuppressedOk :=
    phasedSnap.phasedOut &&
    phasedCtrEv.countersPutInEvent.isEmpty &&
    !phasedCtrEv.matchesTriggerPattern p0 none .youPutPlusOneOnCreature &&
    !phasedCtrEv.matchesTriggerPattern p0 none .youPutCountersOnGoblinOrcArmy &&
    !phasedTapEv.matchesTriggerPattern p0 (some ghObj0.id) .thisBecomesTapped &&
    !phasedTapEv.matchesTriggerPattern p0 (some ghObj0.id) .creaturesYouControlBecomeTapped &&
    gPoBatch.waitingTriggers.isEmpty

  -- 3b(ii). Intra-batch LKI fallback in `Core.matchTriggers` for `.youPutPlusOne` and
  --         `.youPutCountersOnGoblinOrcArmy`:
  --         (a) Mid-batch leave-battlefield (`eo.id.bind post.findObject? == none`):
  let gMidLeave0 :=
    addPermanent (addPermanent (addPermanent g3 plusOneWatcherDef p0 p0) goblinWatcherDef p0 p0)
      goblinHeroDef p0 p0
  let midLeaveTargetId := (gMidLeave0.permanentsOf p0).find? (·.name == goblinHeroDef.name) |>.get!.id
  let gMidLeaveBatch :=
    gMidLeave0.withBatch (some testCause) fun g =>
      let g :=
        g.putCountersDeferredLog midLeaveTargetId .plusOnePlusOne 1 (some p0) (.playerPutsOn p0)
          (cause := some testCause)
      (g.move midLeaveTargetId .exile none (cause := some testCause)).1

  --         (b) Mid-batch leave-battlefield AND mid-batch phase-out of a noncreature artifact
  --             animated into a Goblin Hero Creature (`eo.toCardDef` would return `plainRelicDef`
  --             if `eo.printed` were not cleared on LKI `causeForQueue`, and `post.findObject?`
  --             returns `!isOnBattlefield` when phased out):
  let plainRelicDef : CardDef := {
    name := "P50i3 AnimRelic"
    types := #[.artifact]
  }
  let gMidPhase0 :=
    addPermanent (addPermanent (addPermanent g3 plusOneWatcherDef p0 p0) goblinWatcherDef p0 p0)
      plainRelicDef p0 p0
  let relicId := (gMidPhase0.permanentsOf p0).find? (·.name == plainRelicDef.name) |>.get!.id
  let gMidPhaseAnim :=
    (gMidPhase0.createEffect
      (.layered (.objects #[relicId]) (.types .add #[.creature] #[.goblin, .hero] #[]) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[relicId]) (.ptSet 2 2) .untilEndOfTurn)
      (cause := some testCause)
  let gMidAnimLeaveBatch :=
    gMidPhaseAnim.withBatch (some testCause) fun g =>
      let g :=
        g.putCountersDeferredLog relicId .plusOnePlusOne 1 (some p0) (.playerPutsOn p0)
          (cause := some testCause)
      (g.move relicId .exile none (cause := some testCause)).1
  let gMidPhaseBatch :=
    gMidPhaseAnim.withBatch (some testCause) fun g =>
      let g :=
        g.putCountersDeferredLog relicId .plusOnePlusOne 1 (some p0) (.playerPutsOn p0)
          (cause := some testCause)
      g.phaseOut (g.object! relicId) (cause := some testCause)

  let item3bOk :=
    mustHold50i3 "3b_phasedOutCounterAndTapSuppressed"
      phasedSuppressedOk &&
    mustHold50i3 "3b_intraBatchLeaveBattlefieldLki"
      ((gMidLeaveBatch.findObject? midLeaveTargetId).isNone &&
       (gMidLeaveBatch.waitingTriggers.filter (·.pattern == .youPutPlusOneOnOtherHeroYouControl)).size == 1 &&
       (gMidLeaveBatch.waitingTriggers.filter (·.pattern == .youPutCountersOnGoblinOrcArmy)).size == 1 &&
       (gMidAnimLeaveBatch.findObject? relicId).isNone &&
       (gMidAnimLeaveBatch.waitingTriggers.filter (·.pattern == .youPutPlusOneOnOtherHeroYouControl)).size == 1 &&
       (gMidAnimLeaveBatch.waitingTriggers.filter (·.pattern == .youPutCountersOnGoblinOrcArmy)).size == 1) &&
    mustHold50i3 "3b_intraBatchAnimatedPhaseOutLki"
      ((gMidPhaseBatch.object! relicId).status.phasedOut &&
       !gMidPhaseBatch.isCreature (gMidPhaseBatch.object! relicId) &&
       (gMidPhaseBatch.waitingTriggers.filter (·.pattern == .youPutPlusOneOnOtherHeroYouControl)).size == 1 &&
       (gMidPhaseBatch.waitingTriggers.filter (·.pattern == .youPutCountersOnGoblinOrcArmy)).size == 1)

  mustHold50i3 "3a.phasingPostPauseAndAllowDirectSingle" item3aOk &&
  mustHold50i3 "3b.phasedOutGuardsAndIntraBatchCounterLki" item3bOk &&
  mustHold50i3 "3.replay"
    (replayOk50i3 #[
      gIndPhased, gIndDeferred, gIndP1Gone, gIndResumed, gLoopBlocked, gDirectAllowed,
      gPoBatch, gMidLeaveBatch, gMidAnimLeaveBatch, gMidPhaseBatch ])

end Phase50Item3EventAlignment

section Phase50Item4EventAlignment

private def mustHold50i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase50Item4EventAlignment failed: {label}"

private def replayOk50i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def isCastDirect4 (a : Action) (id : ObjectId) : Bool :=
  match a with
  | .cast cid => cid == id
  | _ => false

private def isDeclineDirect4 (a : Action) : Bool :=
  match a with
  | .decline => true
  | _ => false

private def isAcceptDirect4 (a : Action) : Bool :=
  match a with
  | .accept => true
  | _ => false

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 4a(i). `LandsAndMana.hasUsableNonPlainManaAbility` preserves post-mana sacrifice, discard,
  --        `CostPick`, and `.crew` costs (both direct `d.picks` and `effCost` plain-source taps):
  let sacSpellDef : CardDef := {
    name := "P50i4 ShrapnelBlast"
    manaCost := { symbols := #[.colored .green] }
    types := #[.instant]
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeArtifactOrCreature]
    spellEffect := some (Effect.gainLife 3)
  }
  let gBase := emptyHand g3 p0
  let (gTr1a, _) :=
    (insertObject (addPermanent gBase forest p0 p0) sacSpellDef p0 (.hand p0)).createOneToken
      p0 Game.treasureToken (cause := some testCause)
  let gTrProp1 := mustApply gTr1a p0 (.cast (gTr1a.player p0).hand.back!)
  let trLoneBlocked :=
    !gTrProp1.hasUsableNonPlainManaAbility p0 (prop? := gTrProp1.proposedSpell)
  let (gTr2a, _) :=
    (insertObject (addPermanent (addPermanent gBase forest p0 p0) bear p0 p0) sacSpellDef p0 (.hand p0)).createOneToken
      p0 Game.treasureToken (cause := some testCause)
  let gTrProp2 := mustApply gTr2a p0 (.cast (gTr2a.player p0).hand.back!)
  let trExtraAllowed :=
    gTrProp2.hasUsableNonPlainManaAbility p0 (prop? := gTrProp2.proposedSpell)

  -- Springleaf Drum (`d.picks = #[.tapUntappedCreature]`) + Vehicle Crew 1 `{1}`:
  let drumDef : CardDef := {
    name := "P50i4 Drum"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := { resolution := .addMana #[.colored .blue] (.fixed 1), phrase := "Add {U}." }
    }]
  }
  let crewSkiffDef : CardDef := {
    name := "P50i4 Skiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapObjects (.totalPowerAtLeast (.const 1)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.gainLife 2
    }]
  }
  let gDrumCrew1 :=
    addPermanent (addPermanent (addPermanent (addPermanent gBase forest p0 p0) drumDef p0 p0) crewSkiffDef p0 p0) bear p0 p0
  let skiff1Id := (gDrumCrew1.permanentsOf p0).find? (·.name == crewSkiffDef.name) |>.get!.id
  let gDrumCrewProp1 := mustApply gDrumCrew1 p0 (.activate skiff1Id 0)
  let drumLoneCrewBlocked :=
    !gDrumCrewProp1.hasUsableNonPlainManaAbility p0 (prop? := gDrumCrewProp1.proposedSpell)
  let gDrumCrew2 := addPermanent gDrumCrew1 bear p0 p0
  let gDrumCrewProp2 := mustApply gDrumCrew2 p0 (.activate skiff1Id 0)
  let drumTwoCrewAllowed :=
    gDrumCrewProp2.hasUsableNonPlainManaAbility p0 (prop? := gDrumCrewProp2.proposedSpell)

  -- Filter artifact (`{1}, {T}: Add {U}{U}`) + Vehicle Crew 1 `{1}` when the ONLY plain mana source
  -- is a 1/1 haste mana Elf:
  let filterSignetDef : CardDef := {
    name := "P50i4 Signet"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf]
      effect := { resolution := .addMana #[.colored .blue] (.fixed 2), phrase := "Add {U}{U}." }
    }]
  }
  let hasteElfDef : CardDef := {
    llanowarElves with
    name := "P50i4 HasteElf"
    power := some 1
    toughness := some 1
    keywords := #[Keyword.haste]
  }
  let gEffCrew1 :=
    addPermanent (addPermanent (addPermanent gBase filterSignetDef p0 p0) crewSkiffDef p0 p0) hasteElfDef p0 p0
  let effSkiffId := (gEffCrew1.permanentsOf p0).find? (·.name == crewSkiffDef.name) |>.get!.id
  let gEffCrewProp1 := mustApply gEffCrew1 p0 (.activate effSkiffId 0)
  let effLoneElfCrewBlocked :=
    !gEffCrewProp1.hasUsableNonPlainManaAbility p0 (prop? := gEffCrewProp1.proposedSpell)
  let gEffCrew2 := addPermanent gEffCrew1 forest p0 p0
  let gEffCrewProp2 := mustApply gEffCrew2 p0 (.activate effSkiffId 0)
  let effWithForestAllowed :=
    gEffCrewProp2.hasUsableNonPlainManaAbility p0 (prop? := gEffCrewProp2.proposedSpell)

  -- 4a(ii). `FraChoices.defaultFraAction` (`.mayCastCascade`, `.mayCastCards`, `.mayCastFromGraveyard`)
  --         uses `currentKeywords`, `canPaySpellCostFromSources`, and `canPayAnnouncedAdditionalFromSources`:
  let urComboLandDef : CardDef := {
    name := "P50i4 SteamConduit"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.combination (.explicit #[.colored .blue, .colored .red]) (.const 2))]
  }
  let urSpellDef : CardDef := {
    name := "P50i4 SteamBolt"
    manaCost := { symbols := #[.colored .blue, .colored .red] }
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 2)
  }
  let greenCreature2Def : CardDef :=
    creature "P50i4 SaprolingHost" { symbols := #[.generic 1, .colored .green] } #["Plant"] 2 2

  let gComboEx := insertObject (addPermanent gBase urComboLandDef p0 p0) urSpellDef p0 .exile
  let comboExId := (gComboEx.objects.filter (fun o => o.zone == .exile)).back!.id
  let gComboGy0 := insertObject (addPermanent gBase urComboLandDef p0 p0) urSpellDef p0 (.graveyard p0)
  let comboGyId := (gComboGy0.player p0).graveyard.back!
  let gComboGy :=
    gComboGy0.createEffect (.permission (some p0) (.flashback comboGyId) .untilEndOfTurn)
      (cause := some testCause)

  -- Layer-6 granted `flash` on an exiled `{1}{G}` creature with a timing-bound `withoutManaCost`
  -- `.playFromExile` grant for `p1` during `p0`'s turn (`priority == p1`, `0` mana): without `flash`,
  -- `timingAllowsCast` is `false` so `paidResolutionOrigPerm?` ignores the free grant (`.decline`);
  -- with Layer-6 `flash` (`keywords := g.currentKeywords o`), `paidResolutionOrigPerm?` selects it (`.cast`)!
  let gFlash0a := (insertObject gBase greenCreature2Def p1 .exile).change (.priority p1)
  let flashExId := (gFlash0a.objects.filter (fun o => o.zone == .exile)).back!.id
  let gFlash0 :=
    gFlash0a.createEffect
      (.permission (some p1) (.playFromExile flashExId { player := p1, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gFlashGranted :=
    gFlash0.createEffect
      (.layered (.objects #[flashExId]) (.abilities { keywords := #[Keyword.flash] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let flashNoKwAct := gFlash0.defaultFraAction p1 (.mayCastCards #[flashExId] false false)
  let flashGrantedAct := gFlashGranted.defaultFraAction p1 (.mayCastCards #[flashExId] false false)

  -- `canPayAnnouncedAdditionalFromSources` on `.mayCastCascade`: a spell with
  -- `additionalCostDiscardOrPayGeneric := some 2` when `p0` has an empty hand and `1`
  -- `ManaOutput.combination` (`tapAddTwoAmong`) land (`availableMana` scores it as `0`, so
  -- old `canPayAnnouncedAdditional` returned `false`, whereas `canPayAnnouncedAdditionalFromSources`
  -- sees `{2}` and accepts):
  let discardOrPay2CascDef : CardDef := {
    name := "P50i4 SteamCascade"
    manaCost := { symbols := #[.generic 2] }
    types := #[.sorcery]
    additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.discardCardOrPayGeneric 2)]
    spellEffect := some (Effect.gainLife 2)
  }
  let gCascPay0 := insertObject gBase discardOrPay2CascDef p0 .exile
  let cascPayId := (gCascPay0.objects.filter (fun o => o.zone == .exile)).back!.id
  let gCascPayCombo := addPermanent gCascPay0 urComboLandDef p0 p0

  let sacCascadeDef : CardDef := {
    sacSpellDef with
    name := "P50i4 SacCascade"
  }
  let gCascNoSac := insertObject gBase sacCascadeDef p0 .exile
  let cascNoSacId := (gCascNoSac.objects.filter (fun o => o.zone == .exile)).back!.id
  let gCascWithSac := addPermanent gCascNoSac bear p0 p0

  let item4aOk :=
    mustHold50i4 "4a_nonPlainPreservesPostManaCosts"
      (trLoneBlocked &&
       trExtraAllowed &&
       drumLoneCrewBlocked &&
       drumTwoCrewAllowed &&
       effLoneElfCrewBlocked &&
       effWithForestAllowed) &&
    mustHold50i4 "4a_1_availMana" (!(gComboEx.availableMana p0).canPay urSpellDef.manaCost) &&
    mustHold50i4 "4a_2_comboEx" (isCastDirect4 (gComboEx.defaultFraAction p0 (.mayCastCards #[comboExId] false false)) comboExId) &&
    mustHold50i4 "4a_3_comboGy" (isCastDirect4 (gComboGy.defaultFraAction p0 (.mayCastFromGraveyard #[comboGyId])) comboGyId) &&
    mustHold50i4 "4a_4_flashLayer6"
      (isDeclineDirect4 flashNoKwAct &&
       isCastDirect4 flashGrantedAct flashExId) &&
    mustHold50i4 "4a_5_cascComboPayExtra"
      (isDeclineDirect4 (gCascPay0.defaultFraAction p0 (.mayCastCascade cascPayId #[])) &&
       isAcceptDirect4 (gCascPayCombo.defaultFraAction p0 (.mayCastCascade cascPayId #[]))) &&
    mustHold50i4 "4a_6_cascNoSac" (isDeclineDirect4 (gCascNoSac.defaultFraAction p0 (.mayCastCascade cascNoSacId #[]))) &&
    mustHold50i4 "4a_7_cascWithSac" (isAcceptDirect4 (gCascWithSac.defaultFraAction p0 (.mayCastCascade cascNoSacId #[])))

  -- 4b(i). `unlessPaysResCtx` preservation across `beginUnlessPays` -> `Decisions.decline`
  --        `.payOrLetCounter` AND `Decisions.flushUnlessPays` (when payer `p2` concedes):
  let gUnlessB0 :=
    addPermanent (addPermanent (addPermanent g3 bear p1 p1) bear p1 p1) bear p2 p2
  let p1Bears := gUnlessB0.permanentsOf p1
  let bearAId := p1Bears[0]!.id
  let bearBId := p1Bears[1]!.id
  let p2ExtraBearId := (gUnlessB0.permanentsOf p2)[0]!.id
  -- `p2` temporarily controls `bearA` (owned by `p1`); if `p2` concedes (CR 800.4a), control of
  -- `bearA` reverts to `p1` so `Target.permanent bearAId` stays legal when `flushUnlessPays` runs!
  let gUnlessBase :=
    gUnlessB0.createEffect (.layered (.objects #[bearAId]) (.control p2) .untilEndOfTurn)
      (cause := some testCause)
  let ctxRich : SpellResolutionCtx := {
    castFromGraveyard := true
    kicked := true
    giftPromised := true
    chosenX := some 4
    lastKnownPower := some 5
    lastKnownToughness := some 7
  }
  let innerAllCtx : SpellResolution :=
    .sequence [
      .«if» .castFromGraveyard (.loseLife .equalSourcePower .eachOpponent),
      .loseLife .equalSourceToughness .eachOpponent,
      .«if» .giftPromised (.loseLife .chosenX .eachOpponent),
      .phaseOutKicker
    ]
  let unlessEff : Effect := {
    targeting := .of .creature
    resolution := .ofSpell (.unlessPays innerAllCtx 2)
    phrase := "Target creature's controller pays {2} or loses life and creatures phase out."
  }
  let gUnless0 :=
    gUnlessBase.applyEffect p0 unlessEff #[.permanent bearAId]
      (castFromGraveyard := ctxRich.castFromGraveyard)
      (kicked := ctxRich.kicked)
      (giftPromised := ctxRich.giftPromised)
      (chosenX := ctxRich.chosenX)
      (lastKnownPower := ctxRich.lastKnownPower)
      (lastKnownToughness := ctxRich.lastKnownToughness)
  -- Decline `.payOrLetCounter` as `p2`: `p1` & `p2` each lose `5 + 7 + 4 = 16` life (`20 -> 4`),
  -- and `phaseOutKicker` (`kicked == true`) phases out BOTH creatures `p2` controls (`bearA` & `p2ExtraBearId`)!
  let gUnlessDeclined := mustApply gUnless0 p2 .decline
  -- Payer `p2` concedes at `.payOrLetCounter`: `Leaving` sets `unlessPaysDue := true`, `bearA`
  -- reverts to `p1`, and `flushUnlessPays` causes `p1` to lose `16` life (`20 -> 4`) and phases out
  -- BOTH `bearA` and `bearB` (`kicked == true`, whereas `kicked == false` would phase out only `bearA`)!
  let gUnlessFlushed := mustApply gUnless0 p2 .concede

  -- 4b(ii). Explicit `chosenX = some 0` precedence over permanent `sourceId` `chosenXOf? == some 5`
  --         across `applyFraResolution?` / `FrcResolve.spellX`, `applyUnifiedAbility`,
  --         `.continueUnifiedAbility` (also verifying `chosenX` and `lastKnownToughness` are NOT swapped!),
  --         `.continueSpellModes`, `acceptMay`, `chooseSpellOr`, and `TriggerArgs` (`triggerInt` & `applyAddMana`):
  let xHydraPermDef : CardDef :=
    creature "P50i4 XSourceHydra" { symbols := #[.x] } #["Hydra"] 3 3
  let gXSrc0 := (insertObject gBase xHydraPermDef p0 (.hand p0)).addMana p0 .colorless 5
  let gXSrcCast :=
    mustApply (mustApply (mustApply gXSrc0 p0 (.cast (gXSrc0.player p0).hand.back!)) p0 (.chooseX 5)) p0 .pay
  let gXSrcBf := mustApply (mustApply (mustApply gXSrcCast p0 .pass) p1 .pass) p2 .pass
  let xSrcId := (gXSrcBf.permanentsOf p0).find? (·.name == xHydraPermDef.name) |>.get!.id
  let srcHasX5 := gXSrcBf.chosenXOf? xSrcId == some 5

  -- 1. `FrcResolve.spellX` / `applyFraResolution?` (`.frc .warriorsX`):
  let warriorsEff : Effect := { resolution := .frc .warriorsX, phrase := "Create X 1/1 Warrior creature tokens." }
  let gWarriorsZero := gXSrcBf.applyEffect p0 warriorsEff #[] (chosenX := some 0) (sourceId := some xSrcId)
  let gWarriorsFallback := gXSrcBf.applyEffect p0 warriorsEff #[] (chosenX := none) (sourceId := some xSrcId)
  let countWarriors (g : Game) : Nat :=
    ((g.permanentsOf p0).filter (fun o => g.hasSubtype o .warrior || o.name.contains "Warrior")).size

  -- 2. `applyUnifiedAbility`:
  let loseXEff : Effect := {
    resolution := .ofSpell (.loseLife .chosenX .eachOpponent)
    phrase := "Each opponent loses X life."
  }
  let gAbZero :=
    gXSrcBf.applyAbilityEffect p0 loseXEff #[] (sourceId := some xSrcId) (chosenX := some 0)
  let gAbFallback :=
    gXSrcBf.applyAbilityEffect p0 loseXEff #[] (sourceId := some xSrcId) (chosenX := none)

  -- 3. `.continueUnifiedAbility` (`chosenX := some 0`, `lastKnownToughness := some 7`):
  --    On-battlefield `xSrcId` (`3/3`) deals `0 + 3 = 3` (`20 -> 17`, proving `chosenX = some 0` beats
  --    `xSrcId`'s `chosenXOf? = some 5` and is not swapped with `lastKnownToughness = some 7`), and
  --    off-battlefield (`sourceId := none`) deals `0 + 7 = 7` (`20 -> 13`, proving `lastKnownToughness`
  --    is preserved in its own slot):
  let loseTghStep : Resolution := .ofSpell (.loseLife .equalSourceToughness .eachOpponent)
  let loseXStep : Resolution := .ofSpell (.loseLife .chosenX .eachOpponent)
  let gContAbZero :=
    gXSrcBf.resumePendingReplacement
      (.continueUnifiedAbility p0 loseXEff #[loseXStep, loseTghStep] #[]
        (some xSrcId) (some 4) (some 0) (some 7))
  let gContAbLkiZero :=
    gXSrcBf.resumePendingReplacement
      (.continueUnifiedAbility p0 loseXEff #[loseXStep, loseTghStep] #[]
        none (some 4) (some 0) (some 7))

  -- 4. `.continueSpellModes` (`chosenX := some 0`, `sourceId := some xSrcId`):
  let gContModesZero :=
    gXSrcBf.resumePendingReplacement
      (.continueSpellModes p0 #[loseXEff] #[] false false false (some 0) (some xSrcId))

  -- 5. `acceptMay` & `chooseSpellOr` (`chosenX := some 0`, `sourceId := some xSrcId`):
  let mayXEff : Effect := {
    resolution := .ofSpell (.may (.loseLife .chosenX .eachOpponent) (.sequence []) .ifYouDont)
    phrase := "You may have each opponent lose X life."
  }
  let gMayZero :=
    mustApply (gXSrcBf.applyEffect p0 mayXEff #[] (chosenX := some 0) (sourceId := some xSrcId)) p0 .accept
  let orXEff : Effect := {
    resolution := .ofSpell (.or [.loseLife .chosenX .eachOpponent, .gainLife (.fixed 1)])
    phrase := "Choose one."
  }
  let gOrPromptZero :=
    gXSrcBf.applyEffect p0 orXEff #[] (chosenX := some 0) (sourceId := some xSrcId)
  let gOrZero :=
    match gOrPromptZero.chooseSpellOr p0 0 with
    | .ok g' => g'
    | .error msg => panic! s!"chooseSpellOr failed: {msg}"

  -- 6. `TriggerArgs.triggerInt` & `applyAddMana`:
  let trigIntZero :=
    gXSrcBf.triggerInt { controller := p0, sourceId := some xSrcId, chosenX := some 0 } .chosenX
  let trigIntFallback :=
    gXSrcBf.triggerInt { controller := p0, sourceId := some xSrcId, chosenX := none } .chosenX
  let gAddManaZero :=
    gXSrcBf.applyAddMana p0 (some xSrcId) #[.colorless] .chosenX (chosenX := some 0)
  let gAddManaFallback :=
    gXSrcBf.applyAddMana p0 (some xSrcId) #[.colorless] .chosenX (chosenX := none)

  let item4bOk :=
    mustHold50i4 "4b_unlessPaysResCtxDeclineAndFlush"
      (gUnless0.unlessPaysResCtx == ctxRich &&
       (gUnlessDeclined.player p1).life == 4 &&
       (gUnlessDeclined.player p2).life == 4 &&
       (gUnlessDeclined.object! bearAId).status.phasedOut &&
       (gUnlessDeclined.object! p2ExtraBearId).status.phasedOut &&
       !(gUnlessDeclined.object! bearBId).status.phasedOut &&
       (gUnlessFlushed.player p2).leftTheGame &&
       (gUnlessFlushed.player p1).life == 4 &&
       (gUnlessFlushed.object! bearAId).status.phasedOut &&
       (gUnlessFlushed.object! bearBId).status.phasedOut) &&
    mustHold50i4 "4b_chosenXZeroPrecedenceOverSourceId"
      (srcHasX5 &&
       countWarriors gWarriorsZero == 0 &&
       countWarriors gWarriorsFallback == 5 &&
       (gAbZero.player p1).life == 20 &&
       (gAbFallback.player p1).life == 15 &&
       (gContAbZero.player p1).life == 17 &&
       (gContAbLkiZero.player p1).life == 13 &&
       (gContModesZero.player p1).life == 20 &&
       (gMayZero.player p1).life == 20 &&
       (gOrZero.player p1).life == 20 &&
       trigIntZero == some 0 &&
       trigIntFallback == some 5 &&
       (gAddManaZero.player p0).manaPool.total == 0 &&
       (gAddManaFallback.player p0).manaPool.total == 5)

  mustHold50i4 "4a.nonPlainCostPreservationAndFraDefaultActions" item4aOk &&
  mustHold50i4 "4b.unlessPaysResCtxAndChosenXZero" item4bOk &&
  mustHold50i4 "4.replay"
    (replayOk50i4 #[
      gTrProp1, gTrProp2, gDrumCrewProp1, gDrumCrewProp2, gEffCrewProp1, gEffCrewProp2,
      gComboEx, gComboGy, gFlashGranted, gCascPayCombo, gCascWithSac,
      gUnless0, gUnlessDeclined, gUnlessFlushed,
      gXSrcBf, gWarriorsZero, gWarriorsFallback, gAbZero, gAbFallback,
      gContAbZero, gContAbLkiZero, gContModesZero, gMayZero, gOrZero, gAddManaZero, gAddManaFallback ])

end Phase50Item4EventAlignment

end Mtg.Engine.EventTests
