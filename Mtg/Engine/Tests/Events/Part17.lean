import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

section Phase51Item1EventAlignment

private def mustHold51i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase51Item1EventAlignment failed: {label}"

private def replayOk51i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let zeroToughDef : CardDef := creature "P51i1 Germ" ManaCost.empty #["Germ"] 0 0
  let legBearDef : CardDef := { bear with name := "P51i1 LegBear", supertypes := #[.legendary] }
  let oddEvenDef : CardDef := {
    name := "P51i1 OddStatue"
    types := #[.artifact]
    staticAbilities := #[.asEntersChooseOddEven]
  }
  let zeroInstDef : CardDef := {
    name := "P51i1 ZeroInst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }

  -- 1a(i). `Entering.receivePriority` post-`checkSBA` and post-`putTriggerBatch` CR 800.4j `priorityInstead` re-resolution:
  --        (a) `p0` is at `0` life on entry (`stillInGame p0 == true`), loses & leaves in `checkSBA`,
  --            and `receivePriority p0` grants priority to `p1` (and stamps `pendingPriority := some p1` when
  --            `p2`'s unannounced trigger opens `.chooseTargets p2`, NOT departed `p0`):
  let gZeroLife := g4.loseLife p0 20 (cause := some testCause)
  let gRecvAfterSba := gZeroLife.receivePriority p0
  let tgtDiesZeroDef : CardDef := {
    zeroToughDef with
    name := "P51i1 TgtDiesGerm"
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .thisDies
        { targets := .player, body := Instruction.gainLifeFixed 1 (.target 0) }
    ]
  }
  let gZeroLifeWithTgtTrig := addPermanent gZeroLife tgtDiesZeroDef p2 p2
  let gRecvTgtAfterSba := gZeroLifeWithTgtTrig.receivePriority p0

  --        (b) Post-`putTriggerBatch` `savePendingP`: when `p0` loses in `checkSBA` and `p1`'s `0/0` Germ
  --            simultaneously dies with TWO `.dies` triggers so `putTriggerBatch` pauses on
  --            `.chooseTriggerToStack p1`, `pendingPriority` is `some p1` (not `some p0`):
  let twoDiesZeroDef : CardDef := {
    zeroToughDef with
    name := "P51i1 TwoDiesGerm"
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .thisDies (Effect.gainLife 1),
      TriggeredAbility.mkTrigger .thisDies (Effect.gainLife 2)
    ]
  }
  let gZeroLifeOrder := addPermanent gZeroLife twoDiesZeroDef p1 p1
  let gRecvOrderAfterSba := gZeroLifeOrder.receivePriority p0

  -- 1a(ii). `Decisions.classifyFinishConcedePriority`:
  --         (a) Deferred exile/copy arm (`pendingMayCastFromExile` / `pendingFreeCopies` when `proposedSpell.isNone`):
  let gEx0 := insertObject g4 zeroInstDef p2 .exile
  let exCardId := (gEx0.objects.filter (·.zone == .exile)).back!.id
  let fcIdleFalse : PendingReplacement := .finishConcede false none none none false #[] none
  let gPendingExOpen :=
    gEx0.changes #[.pushContinuationFrame {}, .pendingMayCastFromExile (some (p2, #[exCardId], 1))]
  let gPendingExEmpty :=
    gEx0.changes #[.pushContinuationFrame {}, .pendingMayCastFromExile (some (p2, #[exCardId], 0))]

  --         (b) `advanceStepRecipient?`: `.cleanup` (`nextTurnSeatOf` vs `cleanupGivesPriority` + EOT-exposed SBA),
  --             plus `.cleanup` concession paused on `.chooseLegend` keeping priority with `p1` after `keepLegend`:
  let fcAllPassed : PendingReplacement := .finishConcede true none none none false #[] none
  let gCleanupIdle :=
    ((g4.record (GameEvent.stepBegan g4.turnNumber .cleanup p0)).change
      (.cleanupGivesPriority true)).change (.consecutivePasses 4)
  let gCleanupGerm0 := addPermanent gCleanupIdle zeroToughDef p1 p1
  let cleanupGermId := (gCleanupGerm0.permanentsOf p1)[0]!.id
  let gCleanupGivesPrio :=
    gCleanupGerm0.createEffect
      (.layered (.objects #[cleanupGermId]) (.ptModify 1 1) .untilEndOfTurn)
      (cause := some testCause)
  let gCleanupLeg0 :=
    addPermanent
      (addPermanent
        ((g4.record (GameEvent.stepBegan g4.turnNumber .cleanup p0)).change (.cleanupGivesPriority true))
        legBearDef p1 p1)
      legBearDef p1 p1
  let cleanupLegIds := ((gCleanupLeg0.permanentsOf p1).filter (·.name == legBearDef.name)).map (·.id)
  let gCleanupConcedePaused := mustApply (gCleanupLeg0.change (.consecutivePasses 4)) p2 .concede
  let gCleanupAfterKeep := mustApply gCleanupConcedePaused p1 (.keepLegend cleanupLegIds[0]!)

  --         (c) CR 508.8 empty `.declareAttackers` (`hadAttackersThisCombat == false` -> `.endOfCombat` `some p0`)
  --             vs non-empty `.declareAttackers` (-> `.declareBlockers` prompt, `none` / settles):
  let gDeclAtkEmpty :=
    ((g4.record (GameEvent.phaseBegan g4.turnNumber .combat)).record
      (GameEvent.stepBegan g4.turnNumber .declareAttackers p0)).change (.consecutivePasses 4)
  let gAtkPerm0 := addPermanent gDeclAtkEmpty bear p0 p0
  let atkBearId := (gAtkPerm0.permanentsOf p0)[0]!.id
  let gDeclAtkNonEmpty :=
    gAtkPerm0.record (GameEvent.attackersDeclared gAtkPerm0.turnNumber p0
      #[(gAtkPerm0.snapshot (gAtkPerm0.object! atkBearId), .player p1)])

  --         (d) CR 510.4 `.combatDamage` with `pendingRegularCombatDamage == true`: unblocked regular-strike
  --             attacker grants `some p0`, whereas multi-blocked regular-strike attacker opens assignment (`none` / settles):
  let gRegDmgUnblocked :=
    (((gDeclAtkNonEmpty.record (GameEvent.stepBegan gDeclAtkNonEmpty.turnNumber .combatDamage p0)).record
      (GameEvent.extraStepAdded gDeclAtkNonEmpty.turnNumber .combatDamage .afterCurrent
        testCause)).change (.consecutivePasses 4))
  let gRegDmgMulti0 := addPermanent (addPermanent gRegDmgUnblocked bear p1 p1) hero p1 p1
  let p1BlkIds := (gRegDmgMulti0.permanentsOf p1).map (·.id)
  let gRegDmgMulti :=
    (gRegDmgMulti0.record (GameEvent.blockersDeclared gRegDmgMulti0.turnNumber p1 #[
      (gRegDmgMulti0.snapshot (gRegDmgMulti0.object! p1BlkIds[0]!), atkBearId),
      (gRegDmgMulti0.snapshot (gRegDmgMulti0.object! p1BlkIds[1]!), atkBearId) ])).record
      (GameEvent.becameBlocked gRegDmgMulti0.turnNumber
        (gRegDmgMulti0.snapshot (gRegDmgMulti0.object! atkBearId)) #[p1BlkIds[0]!, p1BlkIds[1]!])

  --         (e) Post-`resolveTop` `!g.stack.isEmpty`: active player `p0` loses during `resolveTop` while a lower
  --             stack entry remains — BOTH `PriorityActions.pass` and `classifyFinishConcedePriority` grant `p1`!
  --             And when top spell opens a non-replacement prompt (`scry 1` for `p2`), `fcAllPassed` is `.settlesPromptOrOver` (`!grants`, `settles`):
  let selfLoseInstDef : CardDef := {
    name := "P51i1 SelfFatal"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := { body := Instruction.loseLifeFixed 20 } }
  }
  let scryInstDef : CardDef := {
    name := "P51i1 ScryInst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := { body := Instruction.scryFixed 1 } }
  }
  let gTwoStack0 :=
    insertObject (insertObject g4 zeroInstDef p2 (.hand p2)) selfLoseInstDef p0 (.hand p0)
  let gTwoStack1 := mustApply gTwoStack0 p0 (.cast (gTwoStack0.player p0).hand.back!)
  -- Put `zeroInstDef` at the bottom and `selfLoseInstDef` on top:
  let gBottom0 := (insertObject g4 zeroInstDef p2 (.hand p2)).change (.priority p2)
  let gBottom1 := mustApply gBottom0 p2 (.cast (gBottom0.player p2).hand.back!)
  let gTopLose0 := (insertObject gBottom1 selfLoseInstDef p0 (.hand p0)).change (.priority p0)
  let gTopLose1 := mustApply gTopLose0 p0 (.cast (gTopLose0.player p0).hand.back!)
  let gTopLoseAllPassed := gTopLose1.change (.consecutivePasses 4)
  let gTopLoseViaPass :=
    mustApply (mustApply (mustApply (mustApply gTopLose1 p0 .pass) p1 .pass) p2 .pass) p3 .pass

  let gTopScry0 := (insertObject (insertObject gBottom1 bear p2 (.library p2)) scryInstDef p2 (.hand p2)).change (.priority p2)
  let gTopScry1 := mustApply gTopScry0 p2 (.cast (gTopScry0.player p2).hand.back!)
  let gTopScryAllPassed := gTopScry1.change (.consecutivePasses 4)

  --         (f) `firstPriorityGrantLeaf?` parity on `.grants none` (`Decisions.lean:1375, 2000`):
  --             `p2` has left, `gPausedOdd` is paused on `.chooseReplacement p0`, and its queued `.restorePending`
  --             delegates `connive = some 1` (`hasQueuedPending := true`) into `.beginStepCont .untap`, so
  --             `anyContinuationGrantsPriority == true` while `firstContinuationPriorityGrant? == none` ->
  --             `classifyFinishConcedePriority` returns `.grants none`, and `firstPriorityGrantRecipient?` on
  --             `.seq fcIdleFalse (.receivePriority p3)` returns `some none` (rather than skipping to `some (some p3)`):
  let headWolfDef : CardDef := {
    bear with name := "P51i1 HeadWolf", staticAbilities := #[.exileOppDeathCreateWolf]
  }
  let gTrick0 :=
    mustApply (addPermanent (addPermanent g4 bear p0 p0) headWolfDef p1 p1) p2 .concede
  let trickBearId := (gTrick0.permanentsOf p0)[0]!.id
  let gTrickFin :=
    gTrick0.recordPutCounters trickBearId .finality 1 (some p0) (cause := some testCause)
  let gPausedRepl :=
    gTrickFin.moveToOwnerGraveyard (gTrickFin.object! trickBearId) "dies" (cause := some testCause)
  let trickPending : Pending := .resolutionChoice p2 (.tricksterLibrary p0 trickBearId (some trickBearId))
  let fcOverOdd : PendingReplacement :=
    .finishConcede false none none (some gPausedRepl.pending) false #[] none
  let gFcGrantsNoneProbe :=
    gPausedRepl.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.beginStepCont .untap),
      .pendingReplacement (some (.restorePending trickPending true)) ]

  let item1aOk :=
    mustHold51i1 "1a_receivePriorityPostSbaAndPutTriggerBatch"
      ((gRecvAfterSba.player p0).leftTheGame &&
       gRecvAfterSba.priority == p1 &&
       (gRecvTgtAfterSba.player p0).leftTheGame &&
       gRecvTgtAfterSba.pending == .chooseTargets p2 &&
       gRecvTgtAfterSba.pendingPriority == some p1 &&
       (gRecvOrderAfterSba.player p0).leftTheGame &&
       gRecvOrderAfterSba.pending == .chooseTriggerToStack p1 &&
       gRecvOrderAfterSba.pendingPriority == some p1) &&
    mustHold51i1 "1a_classifyFinishConcedeDeferredExile"
      (!gPendingExOpen.continuationGrantsPriority false fcIdleFalse &&
       gPendingExOpen.continuationSettlesControlFlow false fcIdleFalse &&
       gPendingExEmpty.continuationGrantsPriority false fcIdleFalse &&
       gPendingExEmpty.firstPriorityGrantRecipient? false fcIdleFalse == some none) &&
    mustHold51i1 "1a_advanceStepCleanupAndCombat"
      (gCleanupIdle.continuationGrantsPriority false fcAllPassed &&
       gCleanupIdle.priorityRecipientOfContinuation? false fcAllPassed == some p1 &&
       gCleanupGivesPrio.priorityRecipientOfContinuation? false fcAllPassed == some p0 &&
       gCleanupAfterKeep.activePlayer == p1 &&
       gCleanupAfterKeep.priority == p1 &&
       gDeclAtkEmpty.priorityRecipientOfContinuation? false fcAllPassed == some p0 &&
       gDeclAtkNonEmpty.priorityRecipientOfContinuation? false fcAllPassed == none &&
       gDeclAtkNonEmpty.continuationSettlesControlFlow false fcAllPassed &&
       gRegDmgUnblocked.priorityRecipientOfContinuation? false fcAllPassed == some p0 &&
       gRegDmgMulti.priorityRecipientOfContinuation? false fcAllPassed == none &&
       gRegDmgMulti.continuationSettlesControlFlow false fcAllPassed) &&
    mustHold51i1 "1a_postResolveTopAllPassedRecip"
      (gTopLoseAllPassed.priorityRecipientOfContinuation? false fcAllPassed == some p1) &&
    mustHold51i1 "1a_postResolveTopViaPass"
      ((gTopLoseViaPass.player p0).leftTheGame &&
       gTopLoseViaPass.stack.size == 1 &&
       gTopLoseViaPass.priority == p1) &&
    mustHold51i1 "1a_postResolveTopScrySettles"
      (!gTopScryAllPassed.continuationGrantsPriority false fcAllPassed &&
       gTopScryAllPassed.continuationSettlesControlFlow false fcAllPassed) &&
    mustHold51i1 "1a_leafParity_c1" gFcGrantsNoneProbe.anyContinuationGrantsPriority &&
    mustHold51i1 "1a_leafParity_c2" (gFcGrantsNoneProbe.firstContinuationPriorityGrant? == none) &&
    mustHold51i1 "1a_leafParity_c3" (gFcGrantsNoneProbe.continuationGrantsPriority false fcOverOdd) &&
    mustHold51i1 "1a_leafParity_c4" (gFcGrantsNoneProbe.priorityRecipientOfContinuation? false fcOverOdd == none) &&
    mustHold51i1 "1a_leafParity_c5"
      (gFcGrantsNoneProbe.firstPriorityGrantRecipient? false (.seq fcOverOdd (.receivePriority p3)) == some none)

  -- 1b. Non-priority prompt-opening continuation guards (`!g.anyContinuationSettlesControlFlow`)
  --     across `Decisions` (`finishAndGrantPriority`, `finishResolutionChoice`, `chooseReplacement`),
  --     `ManaAbilities`, and `Actions`:
  let gPauseClean0 := insertObject g4 oddEvenDef p0 (.hand p0)
  let (gPausedOddClean, _) :=
    gPauseClean0.putOntoBattlefield (gPauseClean0.player p0).hand.back! p0 (cause := some testCause)
  -- Queue `.beginStepCont .declareAttackers` behind the `.chooseReplacement` batch close:
  let gSettlingPaused :=
    (gPausedOddClean.record (GameEvent.phaseBegan gPausedOddClean.turnNumber .combat)).chainPendingReplacement
      (.beginStepCont .declareAttackers)
  let settlesWithoutGrant :=
    !gSettlingPaused.anyContinuationGrantsPriority &&
    gSettlingPaused.anyContinuationSettlesControlFlow
  let gAfterFagp := gSettlingPaused.finishAndGrantPriority p2
  let gAfterFfc := gSettlingPaused.finishResolutionChoice
  let gAfterChooseMode := mustApply gAfterFagp p0 (.chooseMode 0)
  -- Also verify `Actions.activateAbility` / `ManaAbilities` guard: activating a plain mana ability
  -- that itself pauses or runs while a prompt-settling outer continuation is queued does not append `.receivePriority`:
  let gManaPause0 := addPermanent gSettlingPaused forest p0 p0
  let forestId := (gManaPause0.permanentsOf p0).find? (·.name == forest.name) |>.get!.id
  let gManaReady :=
    gManaPause0.changes #[
      .pending (.activateManaAbilities p0) ]
  let gAfterManaAct :=
    match gManaReady.activateManaAbility p0 forestId 0 #[.colored .green] with
    | .ok g' => g'
    | .error e => panic! e

  let gEmptySettleBase :=
    g4.changes #[.pushContinuationFrame {}, .pendingReplacement (some (.receivePriority p0))]
  let gEmptySettleAllGone :=
    #[p0, p1, p2, p3].foldl
      (fun acc p => acc.record (GameEvent.playerLeftGame acc.turnNumber p))
      gEmptySettleBase
  let emptySettlesOk :=
    !gEmptySettleAllGone.over &&
    gEmptySettleAllGone.livingPlayers.isEmpty &&
    gEmptySettleBase.continuationSettlesControlFlow false (.restorePending .none false) &&
    !gEmptySettleAllGone.continuationSettlesControlFlow false (.restorePending .none false) &&
    !gEmptySettleAllGone.continuationSettlesControlFlow false
      (.restorePending (.discardForAdditionalCost p0) false)

  let item1bOk :=
    mustHold51i1 "1b_anyContinuationSettlesControlFlowGuards"
      (settlesWithoutGrant &&
       emptySettlesOk &&
       gAfterFagp.pendingReplacement == gSettlingPaused.pendingReplacement &&
       gAfterFfc.pendingReplacement == gSettlingPaused.pendingReplacement &&
       gAfterChooseMode.pending == .declareAttackers &&
       gAfterChooseMode.pendingReplacement.isNone &&
       gAfterChooseMode.outerPendingReplacements.isEmpty &&
       !gAfterManaAct.anyContinuationGrantsPriority &&
       gAfterManaAct.anyContinuationSettlesControlFlow)

  mustHold51i1 "1a.priorityAndConcedeProbes" item1aOk &&
  mustHold51i1 "1b.settlesControlFlowGuards" item1bOk &&
  mustHold51i1 "1.replay"
    (replayOk51i1 #[
      gRecvAfterSba, gRecvTgtAfterSba, gRecvOrderAfterSba,
      gCleanupAfterKeep, gTwoStack1, gTopLoseViaPass, gFcGrantsNoneProbe,
      gAfterFagp, gAfterFfc, gAfterChooseMode, gAfterManaAct, gEmptySettleAllGone ])

end Phase51Item1EventAlignment

section Phase51Item2EventAlignment

private def mustHold51i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase51Item2EventAlignment failed: {label}"

private def replayOk51i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })

  -- 2a(i). `Turns.expirePlayFromExileEffect` / `emitExpiredPlayFromExileLogs` post-simultaneous-expiry
  --        `mayCastExiledBySource` across simultaneous `.control` & `.playFromExile` EOT expiry:
  let nullSummonerDef : CardDef := {
    creature "P51i2 NullSummoner" ManaCost.empty #["Wizard"] 2 3 with
    staticAbilities := #[.castExiledWithSevenInGraveyard]
  }
  let exBoltDef : CardDef := {
    name := "P51i2 ExBolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let mkSimulCtrlExileGame (p1AlsoSeven : Bool) (loseAbilInstead : Bool := false)
      (untilNextTurnP1 : Bool := false) : Game × ObjectId := Id.run do
    let mut g := addPermanent g4 nullSummonerDef p1 p1
    for _ in [0:7] do
      g := insertObject g bear p0 (.graveyard p0)
    if p1AlsoSeven then
      for _ in [0:7] do
        g := insertObject g bear p1 (.graveyard p1)
    let summId := (g.permanentsOf p1)[0]!.id
    g := insertObject g exBoltDef p0 (.hand p0)
    let (gM, exId) := g.move (g.player p0).hand.back! .exile none (cause := some testCause)
    g := gM.changeObject exId (.exiledBy (some summId))
    let dur : EffectDuration := if untilNextTurnP1 then .untilNextTurnOf p1 else .untilEndOfTurn
    g :=
      if loseAbilInstead then
        g.createEffect (.layered (.objects #[summId]) (.abilities {} .all) dur)
          (cause := some testCause)
      else
        g.createEffect (.layered (.objects #[summId]) (.control p0) dur)
          (cause := some testCause)
    g :=
      g.createEffect
        (.permission (some p2) (.playFromExile exId { player := p2 }) dur)
        (cause := some testCause)
    return (g, exId)

  let (gSimulLost0, exSimulLostId) := mkSimulCtrlExileGame false
  let preSimulLostLog := gSimulLost0.log.size
  let gSimulLostAfter := gSimulLost0.clearEOT
  let simulLostLogs := gSimulLostAfter.log.extract preSimulLostLog gSimulLostAfter.log.size

  let (gSimulNextLost0, exSimulNextLostId) := mkSimulCtrlExileGame false (untilNextTurnP1 := true)
  let preSimulNextLostLog := gSimulNextLost0.log.size
  let gSimulNextLostAfter := gSimulNextLost0.startNextTurnAndBegin
  let simulNextLostLogs := gSimulNextLostAfter.log.extract preSimulNextLostLog gSimulNextLostAfter.log.size

  let (gSimulRegainAbil0, _) := mkSimulCtrlExileGame true (loseAbilInstead := true)
  let preSimulRegainLog := gSimulRegainAbil0.log.size
  let gSimulRegainAfter := gSimulRegainAbil0.clearEOT
  let simulRegainLogs := gSimulRegainAfter.log.extract preSimulRegainLog gSimulRegainAfter.log.size

  -- 2a(ii). Single top-copy restore logging in `Turns.expireEffectsByDuration` & `Core.restoreCopiesWhere`:
  let copy1Def : CardDef := { bear with name := "P51i2 OlderCopy" }
  let copy2Def : CardDef := { bear with name := "P51i2 TopCopy" }
  let gStackCopy0 := addPermanent g4 bear p0 p0
  let copyTargetId := (gStackCopy0.permanentsOf p0)[0]!.id
  let gBothEot :=
    (gStackCopy0.createEffect (.layered (.objects #[copyTargetId]) (.copy copy1Def) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[copyTargetId]) (.copy copy2Def) .untilEndOfTurn)
      (cause := some testCause)
  let preBothEotLog := gBothEot.log.size
  let gBothEotCleared := gBothEot.clearEOT
  let bothEotLogs := gBothEotCleared.log.extract preBothEotLog gBothEotCleared.log.size

  let gBothStepEnd :=
    (gStackCopy0.createEffect (.layered (.objects #[copyTargetId]) (.copy copy1Def) (.untilEndOfStepOrPhase (.step .upkeep)))
      (cause := some testCause)).createEffect
      (.layered (.objects #[copyTargetId]) (.copy copy2Def) (.untilEndOfStepOrPhase (.step .upkeep)))
      (cause := some testCause)
  let preBothStepLog := gBothStepEnd.log.size
  let gBothStepCleared := gBothStepEnd.expireAtStepEnd .upkeep
  let bothStepLogs := gBothStepCleared.log.extract preBothStepLog gBothStepCleared.log.size

  let gBaseIndefTopEot :=
    (gStackCopy0.createEffect (.layered (.objects #[copyTargetId]) (.copy copy1Def) .indefinite)
      (cause := some testCause)).createEffect
      (.layered (.objects #[copyTargetId]) (.copy copy2Def) .untilEndOfTurn)
      (cause := some testCause)
  let preTopOnlyLog := gBaseIndefTopEot.log.size
  let gTopOnlyCleared := gBaseIndefTopEot.clearEOT
  let topOnlyLogs := gTopOnlyCleared.log.extract preTopOnlyLog gTopOnlyCleared.log.size

  let gOlderEotSurvivingTop :=
    (gStackCopy0.createEffect (.layered (.objects #[copyTargetId]) (.copy copy1Def) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[copyTargetId]) (.copy copy2Def) .indefinite)
      (cause := some testCause)
  let preSurvivingTopLog := gOlderEotSurvivingTop.log.size
  let gSurvivingTopCleared := gOlderEotSurvivingTop.clearEOT
  let survivingTopLogs := gSurvivingTopCleared.log.extract preSurvivingTopLog gSurvivingTopCleared.log.size

  let gRestoreWhere0 :=
    (gStackCopy0.createEffect (.layered (.objects #[copyTargetId]) (.copy copy1Def) (.untilNextTurnOf p1))
      (cause := some testCause)).createEffect
      (.layered (.objects #[copyTargetId]) (.copy copy2Def) (.untilNextTurnOf p1))
      (cause := some testCause)
  let preRwLog := gRestoreWhere0.log.size
  let gRestoreWhereDone := gRestoreWhere0.restoreCopiesUntilNextTurn p1
  let rwLogs := gRestoreWhereDone.log.extract preRwLog gRestoreWhereDone.log.size

  -- 2a(iii). CR 800.4c `coDepartingIds` `cmdInitSeeds` (departing player's battlefield commander
  --          returning to `.command`) & `coDepartingIdsFwd` log/unattach suppression in `Movement.move`
  --          and `Attachments.ceaseToExist`:
  let cmdDef : CardDef := { bear with name := "P51i2 Warlord", supertypes := #[.legendary] }
  let equipDef : CardDef := { name := "P51i2 Greaves", types := #[.artifact], subtypes := #["Equipment"] }
  let cmdCfg : StartConfig := {
    seats := #[
      { name := "P0", deck := testRedDeck },
      { name := "P1", deck := testGreenDeck },
      { name := "P2", deck := testRedDeck, commanders := #[cmdDef] },
      { name := "P3", deck := testGreenDeck }
    ]
    format := .constructed
    seed := 51
    startingPlayer := some 0
  }
  let gCmd0 : Game :=
    match Start.start cmdCfg with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let cmdInitObj := (gCmd0.objects.filter (fun o => o.name == cmdDef.name))[0]!
  let (gCmdBf0, cmdBfId) := gCmd0.move cmdInitObj.id .battlefield (some p2) (cause := some testCause)
  -- `p0` owns `hostBear` whose `defaultController` is `p3` (who concedes first), and `cmdBfId` steals `hostBear` for `p2`;
  -- `p2` also has a token `tokEq` attached to `hostBear` controlled by `p2`:
  let gCmdBf1 := addPermanent gCmdBf0 bear p0 p3
  let depHostId := (gCmdBf1.permanentsOf p3)[0]!.id
  let gCmdBf2 :=
    mustApply
      (gCmdBf1.createEffect
        (.layered (.objects #[depHostId]) (.control p2) (.whileSourceOnBattlefield cmdBfId))
        (cause := some testCause))
      p3 .concede
  let (gCmdBf3, tokEq) := gCmdBf2.createOneToken p2 equipDef (cause := some testCause)
  let gCmdBf4 := gCmdBf3.attachSourceTo (gCmdBf3.object! tokEq.id) (gCmdBf3.object! depHostId) (cause := some testCause)
  let coDepsForP2 := gCmdBf4.coDepartingIds #[] (departingPlayer? := some p2)
  let preP2LeaveLog := gCmdBf4.log.size
  let gCmdAfterP2Leave := mustApply gCmdBf4 p2 .concede
  let p2LeaveLogs := gCmdAfterP2Leave.log.extract preP2LeaveLog gCmdAfterP2Leave.log.size

  -- 2b. 2HG `isSharedTurnFirstSeat` + `includeTeammates := true` `Phasing.phaseInControlled` parity
  --     in `Turns.beginStepBody` `.untap` and `Decisions.beginTurnAfterStartExpiry`:
  let cfg2hg : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed := 512
    startingPlayer := some 0
  }
  let g2hg0 : Game :=
    match Start.start cfg2hg with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let g2hg1 := addPermanent (addPermanent g2hg0 bear ⟨2⟩ ⟨2⟩) hero ⟨3⟩ ⟨3⟩
  let b0PermId := (g2hg1.permanentsOf ⟨2⟩)[0]!.id
  let b1PermId := (g2hg1.permanentsOf ⟨3⟩)[0]!.id
  let g2hgPhased :=
    (g2hg1.phaseOut (g2hg1.object! b0PermId) (cause := some testCause)).phaseOut
      (g2hg1.object! b1PermId) (cause := some testCause)
  -- Advance across Team A (`⟨0⟩ -> ⟨1⟩ -> ⟨2⟩`): when Team B's shared turn begins on `⟨2⟩`,
  -- BOTH `b0PermId` (`⟨2⟩`) and `b1PermId` (`⟨3⟩`) phase in together!
  let gTeamBBegan := (g2hgPhased.startNextTurnAndBegin).startNextTurnAndBegin
  -- Now phase out `b0PermId` during `⟨2⟩`'s half of Team B's shared turn, and advance to `⟨3⟩`:
  -- `⟨3⟩` is NOT `isSharedTurnFirstSeat`, so `b0PermId` must STAY phased out on `⟨3⟩`'s half!
  let gTeamBHalfPhased := gTeamBBegan.phaseOut (gTeamBBegan.object! b0PermId) (cause := some testCause)
  let gTeamBSecondSeat := gTeamBHalfPhased.startNextTurnAndBegin

  -- `beginTurn` simultaneous direct + command-emblem `.copy` collapse (Phase 54):
  -- `copyTargetId` has older `.copy copy1Def` tied to `.command` emblem `embBT` (`.untilNextTurnOf p0`)
  -- and newer `.copy copy2Def` (`.untilNextTurnOf p0`). Both expire simultaneously in `beginTurn`,
  -- collapsing into a single `"{bear.name} is no longer a copy of {copy2Def.name}"` log without
  -- mentioning the intermediate `copy1Def.name`:
  let embBTDef : CardDef := { name := "P51i2 TurnEmb", types := #[.enchantment] }
  let gBtCopy0 := insertObject gStackCopy0 embBTDef p1 .command (some p1)
  let embBTId := (gBtCopy0.objects.filter (·.zone == .command)).back!.id
  let gBtCopy1 :=
    (((gBtCopy0.createEffect (.gameRule (.commandEmblem embBTId) (.untilNextTurnOf p0))
        (cause := some testCause)).createEffect
      (.layered (.objects #[copyTargetId]) (.copy copy1Def) (.whileInZone embBTId .command))
      (cause := some testCause)).createEffect
      (.layered (.objects #[copyTargetId]) (.copy copy2Def) (.untilNextTurnOf p0))
      (cause := some testCause))
  let preBtCopyLog := gBtCopy1.log.size
  let gBtCopyDone := gBtCopy1.beginTurn
  let btCopyLogs := gBtCopyDone.log.extract preBtCopyLog gBtCopyDone.log.size

  -- Co-departing permanents via `coDepartingIdsExport` (`coDepartingIdsFwd`) in `Movement.move`
  -- and `Attachments.ceaseToExist` (phased-in CR 800.4c exile vs phased-out CR 702.26b preservation),
  -- plus phased-out battlefield-seed CR 800.4c exile in `playerLeavesGameCore` (`includePhasedOut := true`):
  let anchorMoveDef : CardDef := { name := "P51i2 MoveAnchor", types := #[.artifact] }
  let gPhSkip0 :=
    insertObject (addPermanent (addPermanent g4 bear p0 p3) anchorMoveDef p2 p2) embBTDef p2 .command (some p2)
  let phDepId := (gPhSkip0.permanentsOf p3)[0]!.id
  let moveAnchorId := (gPhSkip0.permanentsOf p2)[0]!.id
  let ceaseEmbId := (gPhSkip0.objects.filter (·.zone == .command)).back!.id
  let gLiveMoveSetup :=
    mustApply
      ((gPhSkip0.createEffect
          (.layered (.objects #[phDepId]) (.control p2) (.whileSourceOnBattlefield moveAnchorId))
          (cause := some testCause)).createEffect
        (.layered (.objects #[phDepId]) (.copy copy1Def) (.whileSourceOnBattlefield moveAnchorId))
        (cause := some testCause))
      p3 .concede
  let preLiveMoveLog := gLiveMoveSetup.log.size
  let (gLiveAfterMove, _) := gLiveMoveSetup.move moveAnchorId .exile none (cause := some testCause)
  let liveMoveLogs := gLiveAfterMove.log.extract preLiveMoveLog gLiveAfterMove.log.size

  let gLiveCeaseSetup :=
    mustApply
      (((gPhSkip0.createEffect (.gameRule (.commandEmblem ceaseEmbId) .indefinite)
          (cause := some testCause)).createEffect
          (.layered (.objects #[phDepId]) (.control p2) (.whileInZone ceaseEmbId .command))
          (cause := some testCause)).createEffect
        (.layered (.objects #[phDepId]) (.copy copy1Def) (.whileInZone ceaseEmbId .command))
        (cause := some testCause))
      p3 .concede
  let preLiveCeaseLog := gLiveCeaseSetup.log.size
  let gLiveAfterCease := gLiveCeaseSetup.ceaseToExist ceaseEmbId (cause := some testCause)
  let liveCeaseLogs := gLiveAfterCease.log.extract preLiveCeaseLog gLiveAfterCease.log.size

  let gPhMoveSetup := gLiveMoveSetup.phaseOut (gLiveMoveSetup.object! phDepId) (cause := some testCause)
  let prePhMoveLog := gPhMoveSetup.log.size
  let (gPhAfterMove, _) := gPhMoveSetup.move moveAnchorId .exile none (cause := some testCause)
  let phMoveLogs := gPhAfterMove.log.extract prePhMoveLog gPhAfterMove.log.size

  -- Battlefield seed in `cmdInitSeeds` with `includePhasedOut := true` (`playerLeavesGameCore` ->
  -- `endControlEffectsSimultaneously`): `p2` owns `moveAnchorId`, which grants living `p1` control +
  -- `copy1Def` on phased-out `phDepId` (`fallback = departed p3 != p2`):
  let gPhLeaveSetup :=
    let gC :=
      mustApply
        ((gPhSkip0.createEffect
            (.layered (.objects #[phDepId]) (.control p1) (.whileSourceOnBattlefield moveAnchorId))
            (cause := some testCause)).createEffect
          (.layered (.objects #[phDepId]) (.copy copy1Def) (.whileSourceOnBattlefield moveAnchorId))
          (cause := some testCause))
        p3 .concede
    gC.phaseOut (gC.object! phDepId) (cause := some testCause)
  let prePhLeaveLog := gPhLeaveSetup.log.size
  let gPhAfterP2Leave := mustApply gPhLeaveSetup p2 .concede
  let phLeaveLogs := gPhAfterP2Leave.log.extract prePhLeaveLog gPhAfterP2Leave.log.size

  let item2aOk :=
    mustHold51i2 "2a_simultaneousCtrlAndPlayFromExileLogs"
      ((gSimulLostAfter.findObject? exSimulLostId).isSome &&
       (simulLostLogs.filter (· == s!"{exBoltDef.name} can no longer be played from exile")).size == 1 &&
       (gSimulNextLostAfter.findObject? exSimulNextLostId).isSome &&
       (simulNextLostLogs.filter (· == s!"{exBoltDef.name} can no longer be played from exile")).size == 1 &&
       !simulRegainLogs.any (· == s!"{exBoltDef.name} can no longer be played from exile")) &&
    mustHold51i2 "2a_stackedCopyRestoreSingleLog"
      ((bothEotLogs.filter (· == s!"{bear.name} is no longer a copy of {copy2Def.name}")).size == 1 &&
       !bothEotLogs.any (·.contains copy1Def.name) &&
       (bothStepLogs.filter (· == s!"{bear.name} is no longer a copy of {copy2Def.name}")).size == 1 &&
       !bothStepLogs.any (·.contains copy1Def.name) &&
       (topOnlyLogs.filter (· == s!"{copy1Def.name} is no longer a copy of {copy2Def.name}")).size == 1 &&
       !survivingTopLogs.any (·.contains "is no longer a copy of") &&
       (rwLogs.filter (· == s!"{bear.name} is no longer a copy of {copy2Def.name}")).size == 1 &&
       !rwLogs.any (·.contains copy1Def.name) &&
       (btCopyLogs.filter (· == s!"{bear.name} is no longer a copy of {copy2Def.name}")).size == 1 &&
       !btCopyLogs.any (·.contains copy1Def.name)) &&
    mustHold51i2 "2a_commanderCoDepartingIdsAndLogSuppression"
      (coDepsForP2.contains cmdBfId &&
       coDepsForP2.contains depHostId &&
       coDepsForP2.contains tokEq.id &&
       (gLiveMoveSetup.coDepartingIdsExport #[moveAnchorId]).contains phDepId &&
       (gLiveCeaseSetup.coDepartingIdsExport #[ceaseEmbId]).contains phDepId &&
       (gLiveAfterMove.followMovedToZone? phDepId (· == .exile)).isSome &&
       (gLiveAfterCease.followMovedToZone? phDepId (· == .exile)).isSome &&
       !liveMoveLogs.any (·.contains "is no longer a copy of") &&
       !liveCeaseLogs.any (·.contains "is no longer a copy of") &&
       !liveCeaseLogs.any (·.contains "returns to") &&
       gPhMoveSetup.coDepartingIdsExport #[moveAnchorId] == gPhMoveSetup.coDepartingIds #[moveAnchorId] &&
       !(gPhMoveSetup.coDepartingIdsExport #[moveAnchorId]).contains phDepId &&
       (gPhAfterMove.object! phDepId).status.phasedOut &&
       phMoveLogs.any (· == s!"{bear.name} is no longer a copy of {copy1Def.name}") &&
       (gPhLeaveSetup.coDepartingIds #[moveAnchorId] (departingPlayer? := some p2) (includePhasedOut := true)).contains phDepId &&
       (gPhAfterP2Leave.followMovedToZone? phDepId (· == .exile)).isSome &&
       !phLeaveLogs.any (·.contains "is no longer a copy of") &&
       (gCmdAfterP2Leave.followMovedToZone? depHostId (· == .exile)).isSome &&
       (gCmdAfterP2Leave.findObject? tokEq.id).isNone &&
       !p2LeaveLogs.any (·.contains "becomes unattached") &&
       !p2LeaveLogs.any (·.contains "Control of"))

  let item2bOk :=
    mustHold51i2 "2b_2hgSharedTurnPhaseInControlledParity"
      (gTeamBBegan.activePlayer == ⟨2⟩ &&
       !(gTeamBBegan.object! b0PermId).status.phasedOut &&
       !(gTeamBBegan.object! b1PermId).status.phasedOut &&
       gTeamBSecondSeat.activePlayer == ⟨3⟩ &&
       (gTeamBSecondSeat.object! b0PermId).status.phasedOut)

  mustHold51i2 "2a.expiryCopyAndCoDeparting" item2aOk &&
  mustHold51i2 "2b.twoHeadedGiantPhasing" item2bOk &&
  mustHold51i2 "2.replay"
    (replayOk51i2 #[
      gSimulLostAfter, gSimulNextLostAfter, gSimulRegainAfter,
      gBothEotCleared, gBothStepCleared, gTopOnlyCleared, gSurvivingTopCleared, gRestoreWhereDone,
      gBtCopyDone, gLiveAfterMove, gLiveAfterCease, gPhAfterMove, gPhAfterP2Leave,
      gCmdBf4, gCmdAfterP2Leave, gTeamBBegan, gTeamBSecondSeat ])

end Phase51Item2EventAlignment

section Phase51Item3EventAlignment

private def mustHold51i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase51Item3EventAlignment failed: {label}"

private def replayOk51i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 3a(i). `GameObject.isLkiSnapshot` isolation in `damageSourceObjectFromLki` & `makeEventObjFromSnapshot`:
  --        No counter double-counting (`+1/+1` counters) and no post-departure anthem/ability-strip leakage!
  let anthemDef : CardDef := {
    name := "P51i3 WarBanner"
    types := #[.artifact]
    staticAbilities := #[.creaturesYouControlGet 1 1]
  }
  let gLki0 := addPermanent (addPermanent g3 anthemDef p0 p0) bear p0 p0
  let lkiBearId := (gLki0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gLki1 :=
    (((gLki0.addCounters (gLki0.object! lkiBearId) .plusOnePlusOne 2 (byPlayer := some p0)
        (cause := some testCause)).createEffect
      (.layered (.objects #[lkiBearId]) (.abilities { keywords := #[Keyword.lifelink] } .none) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[lkiBearId]) (.types .add #[] #[.goblin] #[]) .untilEndOfTurn)
      (cause := some testCause))
  let liveBearObj := gLki1.object! lkiBearId
  let livePtBefore := (gLki1.power liveBearObj, gLki1.toughness liveBearObj) -- 2 + 2 (+1/+1) + 1 (anthem) = (5, 5)
  let bearSnap := gLki1.snapshot liveBearObj
  let (gLkiExiled0, _) := gLki1.move lkiBearId .exile none (cause := some testCause)
  -- Add a second post-departure anthem (`+1/+1`) and expire EOT effects (`clearEOT`):
  let gLkiPost := (addPermanent gLkiExiled0 anthemDef p0 p0).clearEOT
  let lkiReconstructed := Game.damageSourceObjectFromLki bearSnap

  -- 3a(ii). `.phasedOut` in `Event.lastKnownBefore?`, `Damage`, `ResolutionEffects.abilitySourceFor`,
  --         and intra-batch `Core.matchTriggers` (`.sagaChapter`, `.nthPlanCounter`, `.damage`):
  let gPhLki := gLki1.phaseOut (gLki1.object! lkiBearId) (cause := some testCause)
  let phLastKnown? := GameEvent.lastKnownBefore? gPhLki.events lkiBearId
  let phLastPower? := gPhLki.lastKnownPowerOf? lkiBearId
  let phDmgSrc? := gPhLki.damageSourceById? lkiBearId
  let phAbSrc := gPhLki.abilitySourceFor p0 (some lkiBearId)
  -- Dealing 3 damage from phased-out `lkiBearId` uses its pre-phase-out LKI (`lifelink == true`), gaining 3 life!
  let gPhDealt := gPhLki.dealDamageToPlayer p1 3 (source := phDmgSrc?) (cause := some testCause)

  -- Intra-batch `.sagaChapter` & `.nthPlanCounter` when the permanent phases out later in the SAME batch:
  let sagaPermDef : CardDef :=
    fromOracle [
      "P51i3 LoreSaga",
      "{1}{G}",
      "Enchantment — Saga",
      "I — You gain 1 life.",
      "II — You gain 2 life."
    ]
  let planPermDef : CardDef := {
    name := "P51i3 MasterPlan"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger (.putCountersOnSelf .plan) (Effect.gainLife 2) (word := .when) (grouping := .counterThreshold .plan #[1])]
  }
  let gSagaPlan0 :=
    addPermanent (addPermanent g3 sagaPermDef p0 p0) planPermDef p0 p0
  let sagaId := (gSagaPlan0.permanentsOf p0).find? (·.name == sagaPermDef.name) |>.get!.id
  let planId := (gSagaPlan0.permanentsOf p0).find? (·.name == planPermDef.name) |>.get!.id
  -- `addPermanent` puts `sagaPermDef` directly onto `.battlefield` with 0 lore counters;
  -- put 1 `.lore` counter on `sagaId` and 1 `.plan` counter on `planId`, then phase BOTH out in the same batch!
  let gSagaPlanBatch :=
    gSagaPlan0.withBatch (some testCause) fun g =>
      let g := g.putCountersDeferredLog sagaId .lore 1 (some p0) (.playerPutsOn p0) (cause := some testCause)
      let g := g.putCountersDeferredLog planId .plan 1 (some p0) (.playerPutsOn p0) (cause := some testCause)
      let g := g.phaseOut (g.object! sagaId) (cause := some testCause)
      g.phaseOut (g.object! planId) (cause := some testCause)

  let item3aOk :=
    mustHold51i3 "3a_isLkiSnapshotNoDoubleCountOrPostDepartureLeak"
      (livePtBefore == (5, 5) &&
       lkiReconstructed.isLkiSnapshot &&
       (gLkiPost.power lkiReconstructed, gLkiPost.toughness lkiReconstructed) == (5, 5) &&
       KeywordAbility.hasLifelink (gLkiPost.currentKeywords lkiReconstructed) &&
       gLkiPost.hasSubtype lkiReconstructed .goblin &&
       gLkiPost.controllerOf lkiReconstructed == some p0) &&
    mustHold51i3 "3a_phasedOutLastKnownBeforeAndDamageLki"
      (phLastKnown?.any (fun s => s.power == some 5 && KeywordAbility.hasLifelink s.keywords) &&
       phLastPower? == some 5 &&
       phDmgSrc?.any (fun o =>
         o.isLkiSnapshot &&
         (gPhLki.power o, gPhLki.toughness o) == (5, 5) &&
         KeywordAbility.hasLifelink (gPhLki.currentKeywords o)) &&
       phAbSrc.isLkiSnapshot &&
       KeywordAbility.hasLifelink (gPhLki.currentKeywords phAbSrc) &&
       (gPhDealt.player p1).life == 17 &&
       (gPhDealt.player p0).life == 23) &&
    mustHold51i3 "3a_intraBatchSagaAndPlanPhasedOutLki"
      ((gSagaPlanBatch.object! sagaId).status.phasedOut &&
       (gSagaPlanBatch.object! planId).status.phasedOut &&
       gSagaPlanBatch.waitingTriggers.any (fun wt => wt.source.id == sagaId) &&
       gSagaPlanBatch.waitingTriggers.any (fun wt => wt.source.id == planId))

  -- 3b(i). `.equippedBecomesTapped` CR 702.26b suppression & intra-batch `preFallbackEqs` vs `detachedBeforeTap`:
  let tapBowDef : CardDef :=
    fromOracle [
      "P51i3 TapBow",
      "{R}",
      "Artifact — Equipment",
      "Whenever equipped creature becomes tapped, it deals 1 damage to each opponent.",
      "Equip {1}"
    ]
  let gEq0 := addPermanent (addPermanent g3 bear p0 p0) tapBowDef p0 p0
  let eqHostId := (gEq0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let eqBowId := (gEq0.permanentsOf p0).find? (·.name == tapBowDef.name) |>.get!.id
  let gEqAttached := gEq0.attachSourceTo (gEq0.object! eqBowId) (gEq0.object! eqHostId) (cause := some testCause)
  -- Directly phase out ONLY `eqBowId` (`eqHostId` stays phased in), then tap `eqHostId`: NO trigger!
  let gEqPhased := gEqAttached.phaseOut (gEqAttached.object! eqBowId) (cause := some testCause)
  let gHostTappedWhileEqPhased := setTapped gEqPhased eqHostId true
  -- Conversely, when `eqBowId` is phased in at tap time and exiled AFTER the tap in the SAME batch, it DOES trigger!
  let gHostTappedThenEqExiled :=
    gEqAttached.withBatch (some testCause) fun g =>
      let g := setTapped g eqHostId true
      (g.move eqBowId .exile none (cause := some testCause)).1
  -- And if `eqBowId` is exiled BEFORE `eqHostId` is tapped in the SAME batch (`detachedBeforeTap`), it does NOT trigger!
  let gEqExiledThenHostTapped :=
    gEqAttached.withBatch (some testCause) fun g =>
      let g := (g.move eqBowId .exile none (cause := some testCause)).1
      setTapped g eqHostId true

  -- 3b(ii). CR 702.26b `!phasedOut` + `fromZone != .battlefield` across `Event` predicates,
  --         `Core.eventSuppressedByKarn`, and `Movement` `.wouldDie` replacement suppression:
  let karnDef : CardDef := {
    name := "P51i3 KarnGuard"
    types := #[.planeswalker]
    loyalty := some 5
    staticAbilities := #[.enteringArtifactsCreaturesDontTrigger]
  }
  let gKarn := addPermanent g3 karnDef p0 p0
  let dummyId : ObjectId := ⟨777777⟩
  let phasedGobArtSnap : EventObject := {
    id := some dummyId
    name := "P51i3 PhasedGobCog"
    owner := p0
    controller := some p0
    zone := .battlefield
    phasedOut := true
    attacking := true
    types := #[.artifact, .creature]
    subtypes := #[.goblin]
    power := some 2
    toughness := some 2
  }
  let liveGobArtSnap : EventObject := { phasedGobArtSnap with phasedOut := false }
  let phasedDeathEv := GameEvent.moved 1 phasedGobArtSnap .battlefield (.graveyard p0) (cause := testCause)
  let phasedEtbEv := GameEvent.moved 1 phasedGobArtSnap .stack .battlefield (cause := testCause)
  let sameZoneMoveEv := GameEvent.moved 1 liveGobArtSnap .battlefield .battlefield (cause := testCause)
  let realEtbEv := GameEvent.moved 1 liveGobArtSnap .stack .battlefield (cause := testCause)
  let phasedCreatedEv := GameEvent.created 1 p0 { phasedGobArtSnap with token := true } (cause := testCause)
  let phasedCtrEv := GameEvent.counters 1 (some p0) phasedGobArtSnap .plusOnePlusOne 1 (cause := testCause)
  let phasedTapEv := GameEvent.tapped 1 phasedGobArtSnap (cause := testCause)
  let gWithPhasedDeath := (quiet g3).record phasedDeathEv

  -- Moving a phased-out creature with `.exileIfDiesUntilEot` to graveyard does NOT apply `.wouldDie` exile replacement:
  let gDie0 := addPermanent g3 bear p0 p0
  let dieBearId := (gDie0.permanentsOf p0)[0]!.id
  let gDiePhased :=
    (gDie0.createEffect (.exileIfDiesUntilEot dieBearId) (cause := some testCause)).phaseOut
      (gDie0.object! dieBearId) (cause := some testCause)
  let (gDieMoved, dieNewId) := gDiePhased.move dieBearId (.graveyard p0) none (cause := some testCause)

  let item3bOk :=
    mustHold51i3 "3b_equippedBecomesTappedPhasedAndIntraBatch"
      (gHostTappedWhileEqPhased.waitingTriggers.isEmpty &&
       gHostTappedThenEqExiled.waitingTriggers.size == 1 &&
       gEqExiledThenHostTapped.waitingTriggers.isEmpty) &&
    mustHold51i3 "3b_eventPredicatesAndKarnAndWouldDie"
      (!phasedDeathEv.isCreatureToGraveyard &&
       GameEvent.creatureDeaths #[phasedDeathEv] 1 == 0 &&
       gWithPhasedDeath.loggedCreatureDeaths == 0 &&
       !phasedDeathEv.isPermanentToGraveyard &&
       (GameEvent.creaturesToGraveyard #[phasedDeathEv] 1).isEmpty &&
       (GameEvent.lastDiedAttacker #[phasedDeathEv]).isNone &&
       !phasedEtbEv.enteredBattlefield &&
       !sameZoneMoveEv.enteredBattlefield &&
       !GameEvent.artifactEntered #[phasedEtbEv, phasedCreatedEv, sameZoneMoveEv] 1 p0 &&
       !GameEvent.subtypeEntered #[phasedEtbEv, phasedCreatedEv, sameZoneMoveEv] 1 p0 .goblin &&
       !GameEvent.objectEntered #[phasedEtbEv, sameZoneMoveEv] 1 dummyId &&
       !phasedCreatedEv.watches .wouldCreateToken &&
       !phasedCtrEv.watches .wouldPutCounter &&
       (GameEvent.lastBecameTapped #[phasedTapEv]).isNone &&
       !gKarn.eventSuppressedByKarn phasedEtbEv &&
       !gKarn.eventSuppressedByKarn phasedCreatedEv &&
       !gKarn.eventSuppressedByKarn sameZoneMoveEv &&
       gKarn.eventSuppressedByKarn realEtbEv &&
       (gDieMoved.object! dieNewId).zone == Zone.graveyard p0)

  mustHold51i3 "3a.isLkiSnapshotAndPhasedLki" item3aOk &&
  mustHold51i3 "3b.phasedSuppressionPredicatesAndKarn" item3bOk &&
  mustHold51i3 "3.replay"
    (replayOk51i3 #[
      gLki1, gLkiPost, gPhLki, gPhDealt, gSagaPlanBatch,
      gHostTappedWhileEqPhased, gHostTappedThenEqExiled, gEqExiledThenHostTapped,
      gKarn, gDieMoved ])

end Phase51Item3EventAlignment

section Phase51Item4EventAlignment

private def mustHold51i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase51Item4EventAlignment failed: {label}"

private def replayOk51i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def isCastDirect51 (a : Action) (id : ObjectId) : Bool :=
  match a with
  | .cast cid => cid == id
  | _ => false

private def isDeclineDirect51 (a : Action) : Bool :=
  match a with
  | .decline => true
  | _ => false

private def isOptCast51 (a? : Option Action) (id : ObjectId) : Bool :=
  match a? with
  | some (.cast cid) => cid == id
  | _ => false

private def isOptDecline51 (a? : Option Action) : Bool :=
  match a? with
  | some .decline => true
  | _ => false

private def isOptAnnounceKickerTrue51 (a? : Option Action) : Bool :=
  match a? with
  | some (.announceKicker true) => true
  | _ => false

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let gBase := emptyHand (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })) p0

  -- 4a(i). Layer-6 `flash` in `Decisions.castAsPartOfResolution` (`ignoreTiming := false`):
  let gResFlash0 := (insertObject gBase bear p1 .exile).change (.priority p1)
  let resExBearId := (gResFlash0.objects.filter (·.zone == .exile)).back!.id
  let resNoFlash : Game :=
    gResFlash0.castAsPartOfResolution p1 resExBearId (withoutManaCost := true) (ignoreTiming := false)
  let gResFlashGranted :=
    gResFlash0.createEffect
      (.layered (.objects #[resExBearId]) (.abilities { keywords := #[Keyword.flash] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let resWithFlash : Game :=
    gResFlashGranted.castAsPartOfResolution p1 resExBearId (withoutManaCost := true) (ignoreTiming := false)

  -- 4a(ii). `ResolutionChoices.defaultChoiceAction` `.mayCastFromGraveyard`:
  --         (a) Zone precondition (`o.zone == .graveyard o.owner`) and type precondition (`isArtifact || isInstantOrSorcery`);
  --         (b) Impending fallback (`impending := some (4, {2})`, front `{6}`) on an artifact creature in graveyard!
  let zeroArtDef : CardDef := { name := "P51i4 ZeroRelic", manaCost := ManaCost.zero, types := #[.artifact] }
  let artOverlordDef : CardDef := {
    creature "P51i4 GearOverlord" (ManaCost.ofGeneric 6) #["Construct"] 5 5 with
    types := #[.artifact, .creature]
    keywords := #[.impending 4 (CostSpec.ofGeneric 2)]
  }
  let gGy0 := insertObject gBase zeroArtDef p0 (.graveyard p0)
  let gyArtId := (gGy0.player p0).graveyard.back!
  let (gGyMovedToExile, movedExId) := gGy0.move gyArtId .exile none (cause := some testCause)
  -- Non-artifact, non-instant/sorcery card in graveyard (`bear`, cost `{0}` variant):
  let zeroBearDef : CardDef := creature "P51i4 ZeroBear" ManaCost.zero #["Bear"] 2 2
  let gGyNonArt := insertObject gBase zeroBearDef p0 (.graveyard p0)
  let gyNonArtId := (gGyNonArt.player p0).graveyard.back!

  let gGyImp0 := insertObject gBase artOverlordDef p0 (.graveyard p0)
  let gyImpId := (gGyImp0.player p0).graveyard.back!
  let gGyImp1 := gGyImp0.addMana p0 .colorless 1
  let gGyImp2 := gGyImp0.addMana p0 .colorless 2

  -- 4a(iii). `Agent.choose`:
  --          (a) `.chooseKicker` Morph/Impending fallback when `prop.alternativeCost == true`
  --              (e.g. unpayable `payLifeEqualManaValue := true` alongside a clean `.playFromExile` permission):
  let morph5Def : CardDef := {
    creature "P51i4 ExMorph" (ManaCost.ofGeneric 5) #["Beast"] 4 4 with
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let gAltMorph0 := ((insertObject gBase morph5Def p0 .exile).loseLife p0 14 (cause := some testCause)).addMana p0 .colorless 3
  let altMorphExId := (gAltMorph0.objects.filter (·.zone == .exile)).back!.id
  -- `p0` starts at `6` life so `payLifeEqualManaValue := true` (`payLife == 5`) wins `playPermissionFor?` (`alternativeCost == true`),
  -- then loses `4` life (`2` life < `5`) before answering `.chooseKicker` while a clean `.playFromExile` permission allows `{3}` Morph:
  let gAltMorphPerms :=
    (gAltMorph0.createEffect
      (.permission (some p0) (.playFromExile altMorphExId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile altMorphExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let gAltMorphProposed :=
    (mustApply gAltMorphPerms p0 (.cast altMorphExId)).loseLife p0 4 (cause := some testCause)
  let agAltMorphChoice := Agent.choose gAltMorphProposed p0

  --          (b) `.mayCastFromLooked` checks spell taxes (`opponentsNoncreatureSpellsCostMore`) and mandatory additional costs:
  let taxPermDef : CardDef := {
    name := "P51i4 TaxStatue"
    types := #[.artifact]
    staticAbilities := #[.opponentsNoncreatureSpellsCostMore]
  }
  let lookedSorcDef : CardDef := {
    name := "P51i4 LookedSorc"
    manaCost := ManaCost.ofGeneric 2
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let sacLookedSorcDef : CardDef := {
    lookedSorcDef with
    name := "P51i4 LookedSacSorc"
    spellAbility := some { additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature] }
  }
  let gLooked0 := addPermanent (insertObject gBase lookedSorcDef p0 (.library p0)) taxPermDef p1 p1
  let lookedCardId := (gLooked0.player p0).library.back!
  let gLookedUnpaid := gLooked0.change (.pending (.mayCastFromLooked p0 #[lookedCardId] 3))
  let gLookedPaid := (gLooked0.addMana p0 .colorless 1).change (.pending (.mayCastFromLooked p0 #[lookedCardId] 3))

  let gLookedSac0 := insertObject gBase sacLookedSorcDef p0 (.library p0)
  let lookedSacId := (gLookedSac0.player p0).library.back!
  let gLookedNoCreature := gLookedSac0.change (.pending (.mayCastFromLooked p0 #[lookedSacId] 3))
  let gLookedWithCreature := (addPermanent gLookedSac0 bear p0 p0).change (.pending (.mayCastFromLooked p0 #[lookedSacId] 3))

  -- 4b. `Casting.tapPreservesPostManaCosts`: `teamworkCreatures`, `needsBehold`,
  --     `sneakAttacker`-excluded `sacrificeCreatureOrArtifactChoices`, tap-less `costPicksPayable`, and `zemoBoast`:
  let gTw0 := addPermanent (insertObject gBase lookedSorcDef p0 (.hand p0)) bear p0 p0
  let twBearId := (gTw0.permanentsOf p0)[0]!.id
  let gTwProp0 := mustApply gTw0 p0 (.cast (gTw0.player p0).hand.back!)
  let propTw := { gTwProp0.proposedSpell.get! with teamworkPaid := true, teamworkCreatures := #[twBearId] }
  let gTwTapped := setTapped gTwProp0 twBearId true

  let propBehold := { gTwProp0.proposedSpell.get! with needsBehold := some .dragon }
  let dragonDef : CardDef := creature "P51i4 Whelp" ManaCost.empty #["Dragon"] 2 2
  let gWithDragon := addPermanent gTwProp0 dragonDef p0 p0

  let sacCreatureSpellDef : CardDef := {
    name := "P51i4 SneakSac"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2, additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature] }
  }
  let gSnk0 := addPermanent (insertObject gBase sacCreatureSpellDef p0 (.hand p0)) bear p0 p0
  let snkAtkId := (gSnk0.permanentsOf p0)[0]!.id
  let gSnkProp0 := mustApply gSnk0 p0 (.cast (gSnk0.player p0).hand.back!)
  let propSneakSac := {
    gSnkProp0.proposedSpell.get! with
    needsSacrificeOther := true
    sneakAttacker := some snkAtkId
  }
  let gSnkExtra := addPermanent gSnkProp0 hero p0 p0

  let taplessSacRelicDef : CardDef := {
    name := "P51i4 SacAltar"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))]
      effect := Effect.gainLife 1
    }]
  }
  let gAltar0 := addPermanent gBase taplessSacRelicDef p0 p0
  let altarId := (gAltar0.permanentsOf p0)[0]!.id
  let propAltar : ProposedSpell := {
    caster := p0
    cost := ManaCost.ofGeneric 1
    spellId := ⟨999991⟩
    original := gAltar0.object! altarId
    originalSnapshot := gAltar0.snapshot (gAltar0.object! altarId)
    kind := .activatedAbility
    sourceId := some altarId
    activation := some taplessSacRelicDef.activatedAbilities[0]!
    needsSacrificeOther := true
  }
  let gAltarWithBear := addPermanent gAltar0 bear p0 p0

  let item4aOk :=
    mustHold51i4 "4a_castAsPartOfResolutionLayer6Flash"
      (resNoFlash.stack.isEmpty &&
       resWithFlash.stack.size == 1) &&
    mustHold51i4 "4a_mayCastFromGraveyardZoneTypeAndImpending"
      (isCastDirect51 (gGy0.defaultChoiceAction p0 (.mayCastFromGraveyard #[gyArtId])) gyArtId &&
       isDeclineDirect51 (gGyMovedToExile.defaultChoiceAction p0 (.mayCastFromGraveyard #[movedExId])) &&
       isDeclineDirect51 (gGyNonArt.defaultChoiceAction p0 (.mayCastFromGraveyard #[gyNonArtId])) &&
       isDeclineDirect51 (gGyImp1.defaultChoiceAction p0 (.mayCastFromGraveyard #[gyImpId])) &&
       isCastDirect51 (gGyImp2.defaultChoiceAction p0 (.mayCastFromGraveyard #[gyImpId])) gyImpId) &&
    mustHold51i4 "4a_agentChooseKickerAltCostAndMayCastFromLooked"
      (gAltMorphProposed.proposedSpell.any (·.alternativeCost) &&
       isOptAnnounceKickerTrue51 agAltMorphChoice &&
       isOptDecline51 (Agent.choose gLookedUnpaid p0) &&
       isOptCast51 (Agent.choose gLookedPaid p0) lookedCardId &&
       isOptDecline51 (Agent.choose gLookedNoCreature p0) &&
       isOptCast51 (Agent.choose gLookedWithCreature p0) lookedSacId)

  let item4bOk :=
    mustHold51i4 "4b_tapPreservesPostManaCostsAllPreconditions"
      (gTwProp0.tapPreservesPostManaCosts p0 propTw #[] &&
       !gTwProp0.tapPreservesPostManaCosts p0 propTw #[twBearId] &&
       !gTwTapped.tapPreservesPostManaCosts p0 propTw #[] &&
       !gTwProp0.tapPreservesPostManaCosts p0 propBehold #[] &&
       gWithDragon.tapPreservesPostManaCosts p0 propBehold #[] &&
       !gSnkProp0.tapPreservesPostManaCosts p0 propSneakSac #[] &&
       gSnkExtra.tapPreservesPostManaCosts p0 propSneakSac #[] &&
       !gAltar0.tapPreservesPostManaCosts p0 propAltar #[] &&
       gAltarWithBear.tapPreservesPostManaCosts p0 propAltar #[])

  mustHold51i4 "4a.flashFraGraveyardAndAgent" item4aOk &&
  mustHold51i4 "4b.tapPreservesPostManaCosts" item4bOk &&
  mustHold51i4 "4.replay"
    (replayOk51i4 #[
      resNoFlash, resWithFlash, gResFlashGranted, gGyMovedToExile, gGyNonArt, gGyImp2,
      gAltMorphProposed, gLookedUnpaid, gLookedPaid, gLookedNoCreature, gLookedWithCreature,
      gTwProp0, gTwTapped, gWithDragon, gSnkProp0, gSnkExtra, gAltar0, gAltarWithBear ])

end Phase51Item4EventAlignment

end Mtg.Engine.EventTests
