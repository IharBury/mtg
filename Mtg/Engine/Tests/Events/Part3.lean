import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/- Phase 16 isolation & replay tests:
   1. Pause-safe `amass` (fresh Army token & `+1/+1` counter `chooseReplacement`
      before `attachSourceTo`), library-reveal (`resolveRandomCreatureReveal`
      pausing before `putRestOnBottomRandom`), and mill-then-choose
      (`millThenPutFromGy` / `millThenChooseForHand` across replacement).
   2. `mayThen` `.maySacArtifactOrDiscard` (both sync and paused inside an active
      resolution frame before frame pop), `chooseTriggerOr` preserving outer
      `PendingReplacement`, and `turnFaceUp` (`SacrificeDiscard.sacrificeForActivation`
      deferring `turnedFaceUp` across `.chooseReplacement`).
   3. Sync-vs-paused replacement parity: Aura/permanent spell entry redirected to
      `.exile` (no `"enters the battlefield"` log or `afterPermanentEnters`, while
      normal paused Aura entry logs `"attached to {host}"`), and `Pumps` counter
      `putter` attribution + `n' == 0` early-exit + `.time` `syncImpendingNotACreature`.
   4. CR 603.2 / 603.4 `putQueuedTrigger` (already-triggered `wt.checked == true`
      not rechecked against post-event state), CR 603.4 / 608.2a resolution removal
      (`removedOnResolution` without `StackObjectEvent.resolved`), non-intervening
      trigger conditions unrechecked on resolution, and CR 702.176a Impending
      end-step trigger + intervening-`"if"` re-check.
   5. CR 608.2b / 115.1c / 702.16b target legality: targeted activated & non-FRA
      triggered ability all-targets-illegal removal, multi-slot spell per-slot
      validation & `skippedOptionalSlots : Array Nat` (`#[0]`), and CR 702.16b
      protection against ability sources.
   6. CR 704.3 / 704.8 SBA pre-704.5q counter-annihilation LKI & single-batch
      `Pending.chooseLegend` keeping Pass 1 open through `finishSbaSweep` (tokens
      704.5d, Sagas 714.4, Auras 704.5m, Equipment 704.5n).
   7. CR 111.8 token-flicker prohibition & simultaneous two-batch multi-target
      flicker.
   8. CR 603.10 `.creatureCardsPutIntoYourGy` (`after.creature && !after.token`)
      & CR 701.17c `ZoneVerb.mill` in public zones (`followMilledPublic?`).
   9. CR 800.4a/h leave-game continuation handling (`.chooseTargets` trigger
      checkpoint safety, `.chooseSacrificeCreature` last-player `finishChosenSacrifices`,
      multi-player `FraChoice` queue advance, and `.chooseReplacement` transfer).
   10. CR 702.131a/b/d `citysBlessing` / `enduringStory` batch evaluation in
       `Core.closeBatch` + instant/sorcery `ascend` in `resolveTop`, and
       `Option BatchId` (`none` vs `some ⟨0⟩`) envelope fidelity. -/
section Phase16EventAlignment

private def headHuntDef : CardDef :=
  { bear with name := "Phase16 Head Hunt", staticAbilities := #[.exileOppDeathCreateWolf] }
private def samsonDef16 : CardDef :=
  { bear with name := "Phase16 Doc Samson", staticAbilities := #[.extraCounterOnPermanents] }
private def equipDef16 : CardDef := {
  name := "Phase16 Sword"
  manaCost := ManaCost.empty
  types := #[.artifact]
  subtypes := #["Equipment"]
}
private def mustHold16 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 16 guard failed: {label}"

-- 1. Pause-safe `amass`, library-reveal, and mill-then-choose.
#guard
  -- 1a1. `amass` fresh Army token creation pausing on two non-commuting `entersWithExtraCounters`
  --      (`+1` vs `+2` `.plusOnePlusOne`) BEFORE `finishAmassOn` and BEFORE `attachSourceTo`!
  let gAF0 : Game := addPermanent (addPermanent afterDraw equipDef16 me me) bear me me
  let eqFId := (gAF0.battlefield.filter (·.name == "Phase16 Sword"))[0]!.id
  let bFId := (gAF0.battlefield.filter (·.name == bear.name))[0]!.id
  let idEnt1 : ReplacementId := { kind := .entersWithExtraCounters, object := some eqFId, counterKind := some .plusOnePlusOne }
  let idEnt2 : ReplacementId := { kind := .entersWithExtraCounters, object := some bFId, counterKind := some .plusOnePlusOne }
  let gAF0 : Game := (gAF0.createEffect
    (.replacement { id := idEnt1, source := some eqFId, controller := some me, affectedPlayer := me,
                    kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
    (.replacement { id := idEnt2, source := some bFId, controller := some me, affectedPlayer := me,
                    kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)
  let gAFPaused : Game := gAF0.amass me .orc 2 (attach := some eqFId) (cause := some testCause)
  let freshArmyPausedOk : Bool :=
    (match gAFPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gAFPaused.object! eqFId).attachedTo.isNone &&
    !(gAFPaused.permanentsOf me).any (fun o => gAFPaused.hasSubtype o .army)
  let gAFDone : Game := mustApply gAFPaused me (.chooseReplacement idEnt1)
  let freshArmiesDone := (gAFDone.permanentsOf me).filter (fun o => gAFDone.hasSubtype o .army)
  let freshArmyDoneOk : Bool :=
    gAFDone.pending == .none &&
    freshArmiesDone.size == 1 &&
    -- Entered with 1 + 2 = 3 `+1/+1` counters, then `finishAmassOn` added 2 -> 5 total, THEN `eqFId` attached!
    freshArmiesDone[0]!.status.plusOnePlusOne == 5 &&
    (gAFDone.object! eqFId).attachedTo == some freshArmiesDone[0]!.id

  -- 1a2. `finishAmassOn` pausing on two counter-put replacements (`+1` vs `×2`) BEFORE `attachSourceTo`!
  let gA0 : Game := addPermanent (addPermanent afterDraw equipDef16 me me) samsonDef16 me me
  let eqId := (gA0.battlefield.filter (·.name == "Phase16 Sword"))[0]!.id
  let docId := (gA0.battlefield.filter (·.name == "Phase16 Doc Samson"))[0]!.id
  let idDocPlus : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
  let idCntDbl : ReplacementId := { kind := .multiplyCountersPut, object := some eqId }
  let gA0 : Game := gA0.createEffect
    (.replacement { id := idCntDbl, source := some eqId, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut none (some .plusOnePlusOne) 0 2 }) (cause := some testCause)
  let gAP2 : Game := gA0.amass me .orc 2 (attach := some eqId) (cause := some testCause)
  let armiesAtP2 := (gAP2.permanentsOf me).filter (fun o => gAP2.hasSubtype o .army)
  let amassPaused2 : Bool :=
    armiesAtP2.size == 1 &&
    (match gAP2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gAP2.object! eqId).attachedTo.isNone
  let gADone : Game := mustApply gAP2 me (.chooseReplacement idDocPlus)
  let armiesDone := (gADone.permanentsOf me).filter (fun o => gADone.hasSubtype o .army)
  let amassFinishedOk : Bool :=
    gADone.pending == .none &&
    armiesDone.size == 1 &&
    armiesDone[0]!.status.plusOnePlusOne == 6 &&
    (gADone.object! eqId).attachedTo == some armiesDone[0]!.id

  -- 1b. `resolveRandomCreatureReveal` pausing on `chooseReplacement` before `putRestOnBottomRandom`.
  let oddCreatureDef : CardDef := { bear with name := "Phase16 Odd Bear", staticAbilities := #[.asEntersChooseOddEven] }
  let gR0 : Game := insertObject afterDraw oddCreatureDef me (.library me)
  let lib := (gR0.player me).library
  let chosenId := lib.back!
  let restId := lib[lib.size - 2]!
  let gRP : Game := gR0.resolveRandomCreatureReveal me #[chosenId, restId] chosenId (cause := some testCause)
  let revPausedOk : Bool :=
    (match gRP.pending with | .chooseReplacement p _ => p == me | _ => false) &&
    (gRP.player me).library.back? == some chosenId &&
    (gRP.player me).library[0]? != some restId
  let gRD : Game := mustApply gRP me (.chooseMode 1)
  let movedRest? := (gRD.followMovedToZone? restId (· == .library me)).map (·.id)
  let revDoneOk : Bool :=
    gRD.pending == .none &&
    gRD.battlefield.any (fun o => o.name == "Phase16 Odd Bear" && o.status.chosenOdd == some true) &&
    movedRest?.isSome &&
    movedRest? != some restId &&
    (gRD.player me).library[0]? == movedRest?

  -- 1c. `millThenPutFromGy` pausing on `chooseReplacement` when two graveyard exile redirects compete,
  --     AND still finding the milled creature card in `.exile` via CR 701.17c `followMilledPublic?`!
  let gM0 : Game := insertObject afterDraw hero me (.library me)
  let topHero := (gM0.player me).library.back!
  let idEx1 : ReplacementId := { kind := .finalityCounterExile, object := some topHero }
  let idEx2 : ReplacementId := { kind := .exileOppDeath, object := some topHero }
  let gM0 : Game := (gM0.createEffect
    (.replacement { id := idEx1, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some topHero) false })
    (cause := some testCause)).createEffect
    (.replacement { id := idEx2, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some topHero) false })
    (cause := some testCause)
  let gMP : Game := gM0.millThenPutFromGy me 1 (fun o => gM0.isCreature o) (maxPut := some 1) (types := #[.creature])
  let millPausedOk : Bool :=
    (match gMP.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    !(gMP.player me).hand.any (fun id => (gMP.object! id).name == hero.name)
  let gMD : Game := mustApply gMP me (.chooseReplacement idEx1)
  let millDoneOk : Bool :=
    gMD.pending == .none &&
    (gMD.player me).hand.any (fun id => (gMD.object! id).name == hero.name)

  mustHold16 "1a1.freshArmyPausedOk" freshArmyPausedOk &&
  mustHold16 "1a1.freshArmyDoneOk" freshArmyDoneOk &&
  mustHold16 "1a2.amassPaused2" amassPaused2 &&
  mustHold16 "1a2.amassFinishedOk" amassFinishedOk &&
  mustHold16 "1b.revPausedOk" revPausedOk &&
  mustHold16 "1b.revDoneOk" revDoneOk &&
  mustHold16 "1c.millPausedOk" millPausedOk &&
  mustHold16 "1c.millDoneOk" millDoneOk &&
  mustHold16 "1.replay" ([gAFPaused, gAFDone, gAP2, gADone, gRP, gRD, gMP, gMD].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. `mayThen` `.maySacArtifactOrDiscard`, `chooseTriggerOr`, and `turnFaceUp` continuation ordering.
#guard
  let (gMaySync, gMayPause, gMayPauseDone, gTrigOrPause, gTrigOrDone, gMorphSacPause, gMorphSacDone, step2ContOk) :=
    let relicDef : CardDef := { name := "Phase16 Relic", manaCost := ManaCost.empty, types := #[.artifact] }
    -- Sequence `[maySacArtifactOrDiscardDraw, gainLife 3]` so we prove `mayThenResume` (draw 1)
    -- runs BEFORE the outer sequence step (gain 3 life) and BEFORE frame pop in BOTH sync and paused cases!
    let seqRes : TriggeredAbility.TriggerResolution :=
      .sequence [
        .may (.pay CostSpec.sacrificeArtifactOrDiscardCard)
          (.draw (.fixed 1)) .ifYouDo,
        .gainLife (.fixed 3) ]
    let gS0 := addPermanent (addPermanent afterDraw bear me me) relicDef me me
    let srcId := (gS0.battlefield.filter (·.name == bear.name))[0]!.id
    let relId := (gS0.battlefield.filter (·.name == "Phase16 Relic"))[0]!.id
    let handBefore := (gS0.player me).hand.size
    -- 2a. Synchronous sacrifice inside `resolveTop` of `seqRes`:
    let gStSync := gS0.putTriggeredAbilityOnStack me (gS0.object! srcId) (.onEnterDraw 1) "enters"
      (eventCause := some testCause) (reflexiveResolution := some seqRes)
    let gPromptSync := gStSync.resolveTop
    let gSyncDone := mustApply gPromptSync me (.sacrifice relId)
    let syncMayOk :=
      (match gPromptSync.pending with | .maySacArtifactOrDiscard p 1 => p == me | _ => false) &&
      (gPromptSync.player me).life == 20 &&
      gSyncDone.pending == .none &&
      gSyncDone.stack.isEmpty &&
      gSyncDone.continuations.isEmpty &&
      (gSyncDone.player me).hand.size == handBefore + 1 &&
      (gSyncDone.player me).life == 23
    -- 2b. Paused sacrifice (`.finality` + `.untilEotExileIfDies` -> `Pending.chooseReplacement`) inside `resolveTop` of `seqRes`:
    let idExRel : ReplacementId := { kind := .untilEotExileIfDies, object := some relId }
    let gP0 := (gS0.createEffect
      (.replacement { id := idExRel, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some relId) false })
      (cause := some testCause)).recordPutCounters relId .finality 1 (some me) (cause := some testCause)
    let gStP := gP0.putTriggeredAbilityOnStack me (gP0.object! srcId) (.onEnterDraw 1) "enters"
      (eventCause := some testCause) (reflexiveResolution := some seqRes)
    let gPromptP := gStP.resolveTop
    let gSacPaused := mustApply gPromptP me (.sacrifice relId)
    let gSacDone := mustApply gSacPaused me (.chooseReplacement idExRel)
    let pausedMayOk :=
      (match gSacPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      (gSacPaused.player me).hand.size == handBefore &&
      (gSacPaused.player me).life == 20 &&
      !gSacPaused.stack.isEmpty &&
      gSacDone.pending == .none &&
      gSacDone.stack.isEmpty &&
      gSacDone.continuations.isEmpty &&
      (gSacDone.player me).hand.size == handBefore + 1 &&
      (gSacDone.player me).life == 23

    -- 2c. `chooseTriggerOr` preserving outer `PendingReplacement` (sequence step `.gainLife (.fixed 4)`):
    let orRes : TriggeredAbility.TriggerResolution :=
      .sequence [
        .or [.gainLife (.fixed 2), .draw (.fixed 1)],
        .gainLife (.fixed 4) ]
    let gOrSt := gS0.putTriggeredAbilityOnStack me (gS0.object! srcId) (.onEnterDraw 1) "enters"
      (eventCause := some testCause) (reflexiveResolution := some orRes)
    let gOrPrompt := gOrSt.resolveTop
    let gOrResolved := mustApply gOrPrompt me (.chooseMode 0)
    let trigOrOk :=
      (match gOrPrompt.pending with | .chooseTriggerOr p => p == me | _ => false) &&
      (gOrPrompt.player me).life == 20 &&
      gOrResolved.pending == .none &&
      gOrResolved.stack.isEmpty &&
      gOrResolved.continuations.isEmpty &&
      (gOrResolved.player me).life == 26

    -- 2d. `SacrificeDiscard.sacrificeForActivation` `.turnFaceUp` deferring `GameEvent.turnedFaceUp`
    --     across `Pending.chooseReplacement` when sacrificing a creature to turn face up:
    let morphFaceDef : CardDef :=
      { creature "Phase16 MorphSpy" ManaCost.empty #["Human"] 3 3 with keywords := #[.morph CostSpec.empty] }
    let gMf0 := addPermanent (addPermanent afterDraw morphFaceDef me me) bear me me
    let mId := (gMf0.battlefield.filter (·.name == "Phase16 MorphSpy"))[0]!.id
    let fodderId := (gMf0.battlefield.filter (·.name == bear.name))[0]!.id
    let idExFod : ReplacementId := { kind := .untilEotExileIfDies, object := some fodderId }
    let gMf0 := ((setFaceDown gMf0 mId true).createEffect
      (.replacement { id := idExFod, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some fodderId) false })
      (cause := some testCause)).recordPutCounters fodderId .finality 1 (some me) (cause := some testCause)
    let mObj := gMf0.object! mId
    let propMorph : ProposedSpell := {
      caster := me
      cost := ManaCost.empty
      spellId := mId
      sourceId := some mId
      original := mObj
      originalSnapshot := gMf0.snapshot mObj
      kind := .turnFaceUp
      needsSacrificeOther := true
    }
    let gMfPrompt := gMf0.changes #[.saveProposalCheckpoint, .proposedSpell (some propMorph), .pending (.sacrificePermanent me mId)]
    let gMfPaused := mustApply gMfPrompt me (.sacrifice fodderId)
    let gMfDone := mustApply gMfPaused me (.chooseReplacement idExFod)
    let morphSacOk :=
      (match gMfPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
      -- Still face-down while sacrifice replacement choice is pending (CR 708.8)!
      (gMfPaused.object! mId).status.faceDown &&
      !gMfPaused.events.any (fun e =>
        match e.change with | .rules (.permanent (.turnedFaceUp eo)) => eo.id == some mId | _ => false) &&
      gMfDone.pending == .none &&
      !(gMfDone.object! mId).status.faceDown &&
      gMfDone.proposalCheckpoint.isNone &&
      gMfDone.proposedSpell.isNone &&
      gMfDone.events.any (fun e =>
        match e.change with | .rules (.permanent (.turnedFaceUp eo)) => eo.id == some mId | _ => false)
    let _ := headHuntDef
    (gSyncDone, gSacPaused, gSacDone, gOrPrompt, gOrResolved, gMfPaused, gMfDone,
     syncMayOk && pausedMayOk && trigOrOk && morphSacOk)
  let step2AllOk :=
    step2ContOk &&
    [gMaySync, gMayPause, gMayPauseDone, gTrigOrPause, gTrigOrDone, gMorphSacPause, gMorphSacDone].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)
  mustHold16 "step2AllOk" step2AllOk

-- 3. Sync-vs-paused replacement parity (Aura/permanent `.exileInsteadOfStackLeave` & `Pumps` counter putters).
#guard
  let etbAuraDef : CardDef :=
    aura "Phase16 Exile Aura" ManaCost.empty "Enchant creature\nWhen Phase16 Exile Aura enters, you gain 5 life."
      (triggeredAbilities := #[TriggeredAbility.ofPattern .thisEnters "When Phase16 Exile Aura enters, you gain 5 life." (Instruction.gainLifeFixed 5)])
  let etbPermDef : CardDef := {
    bear with
    name := "Phase16 Exile Bear"
    triggeredAbilities := #[TriggeredAbility.ofPattern .thisEnters "When Phase16 Exile Bear enters, you gain 5 life." (Instruction.gainLifeFixed 5)]
  }
  let gE0 : Game := addPermanent afterDraw bear me me
  let hostId := (gE0.battlefield.filter (·.name == bear.name))[0]!.id
  -- 3a. Aura spell redirected to `.exile` on stack leave: no `"enters the battlefield"` log, no ETB life gain!
  let gEA0 : Game := insertObject gE0 etbAuraDef me (.hand me)
  let auraH := (gEA0.player me).hand.back!
  let gEA1 : Game := mustApply (mustApply gEA0 me (.cast auraH)) me (.target (.permanent hostId))
  let auraSpellId := gEA1.stack.back!.objectId
  let gEA1 : Game := gEA1.createEffect
    (.replacement { id := { kind := .flashbackExile, object := some auraSpellId },
                    affectedPlayer := me, kind := .exileInsteadOfStackLeave (some auraSpellId) })
    (cause := some testCause)
  let logBeforeEA := gEA1.log.size
  let gEA2 : Game := gEA1.resolveTop
  let auraExileOk : Bool :=
    gEA2.objects.any (fun o => o.name == "Phase16 Exile Aura" && o.zone == .exile) &&
    !(gEA2.log.extract logBeforeEA gEA2.log.size).any (fun s => (s.splitOn "enters the battlefield").length > 1) &&
    gEA2.waitingTriggers.isEmpty &&
    (gEA2.player me).life == 20
  -- 3b. Creature spell redirected to `.exile` on stack leave: no `"enters the battlefield"` log, no ETB life gain!
  let gEP0 : Game := insertObject gE0 etbPermDef me (.hand me)
  let permH := (gEP0.player me).hand.back!
  let gEP1 : Game := mustApply gEP0 me (.cast permH)
  let permSpellId := gEP1.stack.back!.objectId
  let gEP1 : Game := gEP1.createEffect
    (.replacement { id := { kind := .flashbackExile, object := some permSpellId },
                    affectedPlayer := me, kind := .exileInsteadOfStackLeave (some permSpellId) })
    (cause := some testCause)
  let logBeforeEP := gEP1.log.size
  let gEP2 : Game := gEP1.resolveTop
  let permExileOk : Bool :=
    gEP2.objects.any (fun o => o.name == "Phase16 Exile Bear" && o.zone == .exile) &&
    !(gEP2.log.extract logBeforeEP gEP2.log.size).any (fun s => (s.splitOn "enters the battlefield").length > 1) &&
    gEP2.waitingTriggers.isEmpty &&
    (gEP2.player me).life == 20
  -- 3c. Normal paused Aura spell entry DOES log `"attached to Event Bear"` once the as-enters choice resolves!
  let oddAuraDef : CardDef := {
    aura "Phase16 Odd Aura" ManaCost.empty "Enchant creature" with
    staticAbilities := #[.asEntersChooseOddEven]
  }
  let gOA0 : Game := insertObject gE0 oddAuraDef me (.hand me)
  let oddAuraH := (gOA0.player me).hand.back!
  let gOA1 : Game := mustApply (mustApply gOA0 me (.cast oddAuraH)) me (.target (.permanent hostId))
  let logBeforeOA := gOA1.log.size
  let gOAPaused : Game := gOA1.resolveTop
  let gOADone : Game := mustApply gOAPaused me (.chooseMode 1)
  let oddAuraAttachLogOk : Bool :=
    (gOADone.log.extract logBeforeOA gOADone.log.size).any (fun s =>
      (s.splitOn "Phase16 Odd Aura enters the battlefield attached to Event Bear").length > 1)
  -- 3d. `Pumps` counter `putter` attribution (`opp` resolving context -> `putter == some opp`),
  --     `n' == 0` early-exit (`mult := 0`), and `addCounters .time` `syncImpendingNotACreature`:
  let impBearDef16 : CardDef := { bear with name := "Phase16 Impending Bear", keywords := #[.impending 1 CostSpec.empty] }
  let gPP0 : Game := insertObject gE0 impBearDef16 me (.hand me)
  let impH := (gPP0.player me).hand.back!
  let gPP1 : Game := mustApply (mustApply gPP0 me (.cast impH)) me (.announceKicker true)
  let gPP1Res : Game := gPP1.resolveTop
  let gPP2 : Game := gPP1Res.removeAllCountersFrom
    (gPP1Res.battlefield.filter (·.name == "Phase16 Impending Bear"))[0]!.id
    (byPlayer := some me) (cause := some testCause)
  let impPermId := (gPP2.battlefield.filter (·.name == "Phase16 Impending Bear"))[0]!.id
  let wasCreatureAtZero : Bool := gPP2.isCreature (gPP2.object! impPermId)
  let gPP3 : Game := gPP2.withResolvingContext none opp fun g =>
    g.addIndestructibleCounter (g.object! hostId) 1 (cause := some (.oneShotEffect none none (some opp)))
  let gPP4 : Game := gPP3.addCounters (gPP3.object! impPermId) .time 1 (cause := some testCause)
  let gPP5 : Game := gPP4.createEffect
    (.replacement { id := { kind := .multiplyCountersPut, object := some hostId },
                    affectedPlayer := me, kind := .modifyCountersPut (some hostId) (some .lifelink) 0 0 })
    (cause := some testCause)
  let evBeforeZero := gPP5.events.size
  let logBeforeZero := gPP5.log.size
  let gPP6 : Game := gPP5.addLifelinkCounter (gPP5.object! hostId) 1 (cause := some testCause)
  let pumpsSubOk : Bool :=
    mustHold16 "3d.wasCrea" wasCreatureAtZero &&
    mustHold16 "3d.notCrea" (!gPP4.isCreature (gPP4.object! impPermId)) &&
    mustHold16 "3d.putter" (gPP3.events.any (fun e =>
      match e.change with
      | .rules (.permanent (.counters (.object eo) .indestructible (.put 1) (some p))) =>
        p == opp && eo.id == some hostId
      | _ => false)) &&
    mustHold16 "3d.zeroCnt" ((gPP6.object! hostId).status.counters.count .lifelink == 0) &&
    mustHold16 "3d.zeroEv" (!(gPP6.events.extract evBeforeZero gPP6.events.size).any (fun e =>
      match e.change with | .rules (.permanent (.counters ..)) => true | _ => false)) &&
    mustHold16 "3d.zeroLog" (gPP6.log.size == logBeforeZero)
  mustHold16 "3a.auraExileOk" auraExileOk &&
  mustHold16 "3b.permExileOk" permExileOk &&
  mustHold16 "3c.oddAuraAttachLogOk" oddAuraAttachLogOk &&
  pumpsSubOk &&
  mustHold16 "3.replayEA" (Game.replayEvents gEA2.events == gEA2 && allRulesEventsClassified gEA2) &&
  mustHold16 "3.replayEP" (Game.replayEvents gEP2.events == gEP2 && allRulesEventsClassified gEP2) &&
  mustHold16 "3.replayOA" (Game.replayEvents gOADone.events == gOADone && allRulesEventsClassified gOADone) &&
  mustHold16 "3.replayPP" (Game.replayEvents gPP6.events == gPP6 && allRulesEventsClassified gPP6)

-- 4. CR 603.2 / 603.4 `putQueuedTrigger`, CR 603.4 / 608.2a `removedOnResolution` without `resolved`,
--    non-intervening trigger condition unrechecked on resolution, & CR 702.176a Impending trigger.
#guard
  let whipTrig := TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain
  let gQ0 : Game := addPermanent afterDraw bear me me
  let bId := (gQ0.battlefield.filter (·.name == bear.name))[0]!.id
  let wtChecked : WaitingTrigger := {
    controller := me
    source := gQ0.object! bId
    ability := whipTrig
    pattern := .thisAttacks
    checked := true
  }
  let gQ1 : Game := (gQ0.enqueueWaitingTriggers #[wtChecked]).receivePriority me
  let queuedWentOnStack : Bool := gQ1.stack.size == 1
  let abStackId := gQ1.stack.back!.objectId
  let preResIdx := gQ1.events.size
  let gQ2 : Game := gQ1.resolveTop
  let resSlice := gQ2.events.extract preResIdx gQ2.events.size
  let intervRemovedNoResolved : Bool :=
    gQ2.stack.isEmpty &&
    (gQ2.player opp).life == 20 &&
    resSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some abStackId
      | _ => false) &&
    !resSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved ..)) => true
      | _ => false)

  let harnTrig := TriggeredAbility.onStep Effect.stepHarnessedFlicker
  let (gN1, harnStObj) : Game × GameObject := gQ0.putStackAbility (gQ0.object! bId) me (triggeredAbility := some harnTrig)
  let preNIdx := gN1.events.size
  let gN2 : Game := gN1.resolveTop
  let nonIntervResolved : Bool :=
    gN2.stack.isEmpty &&
    (gN2.events.extract preNIdx gN2.events.size).any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved eo ..)) => eo.id == some harnStObj.id
      | _ => false)

  let impDef4 : CardDef := { bear with name := "Phase16 Impending Elemental", keywords := #[.impending 2 CostSpec.empty] }
  let gI0 : Game := insertObject afterDraw impDef4 me (.hand me)
  let impCard := (gI0.player me).hand.back!
  let gI1 : Game := (mustApply (mustApply gI0 me (.cast impCard)) me (.announceKicker true)).resolveTop
  let impPerm := (gI1.battlefield.filter (·.name == "Phase16 Impending Elemental"))[0]!.id
  let gI2 : Game := gI1.beginStep .end
  let impTrigStackId := gI2.stack.back!.objectId
  let impOnStackOk : Bool :=
    gI2.stack.size == 1 &&
    (gI2.object! impPerm).status.time == 2 &&
    !gI2.isCreature (gI2.object! impPerm)
  let gI3 : Game := gI2.removeAllCountersFrom impPerm (byPlayer := some me) (cause := some testCause)
  let preImpRes := gI3.events.size
  let gI4 : Game := gI3.resolveTop
  let impSlice := gI4.events.extract preImpRes gI4.events.size
  let impFizzledOk : Bool :=
    gI4.stack.isEmpty &&
    gI4.isCreature (gI4.object! impPerm) &&
    impSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some impTrigStackId
      | _ => false) &&
    !impSlice.any (fun e =>
      match e.change with
      | .rules (.stackObject (.resolved ..)) => true
      | _ => false)
  mustHold16 "4a.queuedWentOnStack" queuedWentOnStack &&
  mustHold16 "4a.intervRemovedNoResolved" intervRemovedNoResolved &&
  mustHold16 "4b.nonIntervResolved" nonIntervResolved &&
  mustHold16 "4c.impOnStackOk" impOnStackOk &&
  mustHold16 "4c.impFizzledOk" impFizzledOk &&
  mustHold16 "4.replay" ([gQ1, gQ2, gN2, gI2, gI4].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 608.2b / 115.1c / 702.16b multi-slot & ability target legality.
#guard
  let pingActDef : CardDef := {
    bear with
    name := "Phase16 Prodigal Bear"
    activatedAbilities := #[{
      cost := CostSpec.empty
      effect := Effect.dealDamageToTargetCreature 1
    }]
  }
  let gT0 : Game := addPermanent (addPermanent afterDraw pingActDef me me) hero opp opp
  let pingerId := (gT0.battlefield.filter (·.name == "Phase16 Prodigal Bear"))[0]!.id
  let tgtHero := (gT0.battlefield.filter (·.name == hero.name))[0]!.id
  let gAct1 : Game := mustApply (mustApply gT0 me (.activate pingerId 0)) me (.target (.permanent tgtHero))
  let actStId := gAct1.stack.back!.objectId
  let (gAct2, _) : Game × ObjectId := gAct1.move tgtHero .exile none (cause := some testCause)
  let preActRes := gAct2.events.size
  let gAct3 : Game := gAct2.resolveTop
  let actFizzledOk : Bool :=
    gAct3.stack.isEmpty &&
    (gAct3.events.extract preActRes gAct3.events.size).any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some actStId
      | _ => false) &&
    !(gAct3.events.extract preActRes gAct3.events.size).any (fun e =>
      match e.change with | .rules (.stackObject (.resolved ..)) => true | _ => false)

  let gTr0 : Game := addPermanent afterDraw hero opp opp
  let trTgt := (gTr0.battlefield.filter (·.name == hero.name))[0]!.id
  let blinkAb := TriggeredAbility.onThisAttack Effect.thisAttackBlinkNontoken
  let (gTr1, trObj) : Game × GameObject := gTr0.putStackAbility (gTr0.object! trTgt) me (triggeredAbility := some blinkAb)
  let gTr1 : Game := (gTr1.setStackEntryTargets trObj.id #[Target.permanent trTgt] #[]).markTargetsAnnounced trObj.id true
  let (gTr2, _) : Game × ObjectId := gTr1.move trTgt (.graveyard opp) none (cause := some testCause)
  let preTrRes := gTr2.events.size
  let gTr3 : Game := gTr2.resolveTop
  let trigFizzledOk : Bool :=
    gTr3.stack.isEmpty &&
    (gTr3.events.extract preTrRes gTr3.events.size).any (fun e =>
      match e.change with
      | .rules (.stackObject (.removedOnResolution eo)) => eo.id == some trObj.id
      | _ => false) &&
    !(gTr3.events.extract preTrRes gTr3.events.size).any (fun e =>
      match e.change with | .rules (.stackObject (.resolved ..)) => true | _ => false)

  let mealSpellDef : CardDef := {
    name := "Phase16 Meal"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some (Effect.plusOneUpToOneAndPlayerGainsLife 2)
  }
  let gSlt0 : Game := insertObject (addPermanent afterDraw bear me me) mealSpellDef me (.hand me)
  let sltBear := (gSlt0.battlefield.filter (·.name == bear.name))[0]!.id
  let mealH := (gSlt0.player me).hand.back!
  let gSlt1 : Game := mustApply gSlt0 me (.cast mealH)
  let gSlt2 : Game := mustApply gSlt1 me .decline
  let gSlt3 : Game := mustApply gSlt2 me (.target (.player opp))
  let mealSpellId := gSlt3.stack.back!.objectId
  let skippedRecordedOk : Bool :=
    gSlt3.stack.back!.skippedOptionalSlots == #[0] &&
    gSlt3.events.any (fun e =>
      match e.change with
      | .rules (.cast (.targeted sid #[Target.player p] #[] #[0])) => sid == mealSpellId && p == opp
      | _ => false)
  let gSlt4 : Game := gSlt3.resolveTop
  let swappedSlotsIllegal : Bool :=
    gSlt4.targetsAllIllegalForSpec me .upToOneCreatureThenPlayer
      #[Target.player opp, Target.permanent sltBear] (skippedOptionalSlots := #[])
  let skipSlotOk : Bool :=
    skippedRecordedOk &&
    (gSlt4.player opp).life == 22 &&
    (gSlt4.object! sltBear).status.plusOnePlusOne == 0 &&
    swappedSlotsIllegal

  let redPingerDef : CardDef := {
    pingActDef with
    name := "Phase16 Red Pinger"
    manaCost := ⟨#[.colored .red]⟩
  }
  let protRedDef : CardDef := {
    hero with
    name := "Phase16 Red-Proof Hero"
    keywords := #[.protection (.color (.literal .red))]
  }
  let gPr0 : Game := addPermanent (addPermanent afterDraw redPingerDef me me) protRedDef opp opp
  let rPingId := (gPr0.battlefield.filter (·.name == "Phase16 Red Pinger"))[0]!.id
  let protId := (gPr0.battlefield.filter (·.name == "Phase16 Red-Proof Hero"))[0]!.id
  let legalsFromRed := gPr0.legalTargetsForSpec me .creature (some rPingId)
  let protSourceOk : Bool :=
    !legalsFromRed.contains (Target.permanent protId) &&
    legalsFromRed.contains (Target.permanent rPingId)

  mustHold16 "5a.actFizzledOk" actFizzledOk &&
  mustHold16 "5b.trigFizzledOk" trigFizzledOk &&
  mustHold16 "5c.skipSlotOk" skipSlotOk &&
  mustHold16 "5d.protSourceOk" protSourceOk &&
  mustHold16 "5.replay" ([gAct3, gTr3, gSlt4, gPr0].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 704.3 / 704.8 pre-704.5q SBA LKI & single-batch `chooseLegend` resuming `finishSbaSweep`.
#guard
  let tinyDef : CardDef := creature "Phase16 Tiny" ManaCost.empty #["Spirit"] 1 1
  let gL0 : Game := addPermanent afterDraw tinyDef me me
  let tinyId := (gL0.battlefield.filter (·.name == "Phase16 Tiny"))[0]!.id
  let gL0 : Game := (gL0.recordPutCounters tinyId .plusOnePlusOne 1 (some me) (cause := some testCause)).recordPutCounters
    tinyId .minusOneMinusOne 2 (some me) (cause := some testCause)
  let preLIdx := gL0.events.size
  let gL1 : Game := gL0.checkSBA
  let lkiCountersOk : Bool :=
    (gL1.events.extract preLIdx gL1.events.size).any (fun e =>
      match e.change with
      | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) =>
        before.id == some tinyId &&
        before.counters.contains (.plusOnePlusOne, 1) &&
        before.counters.contains (.minusOneMinusOne, 2)
      | _ => false)

  let zeroDef : CardDef := creature "Phase16 Zero" ManaCost.empty #["Germ"] 0 0
  let legDef : CardDef := { bear with name := "Phase16 Twin Legend", supertypes := #[.legendary] }
  let saga1Def : CardDef :=
    saga "Phase16 One-Chapter Saga" ManaCost.empty "" "I" #[chapter "I" "You gain 1 life." (Effect.gainLife 1)]
  let bareAuraDef : CardDef := aura "Phase16 Stray Aura" ManaCost.empty "Enchant creature"
  let noncreaArtDef : CardDef := { name := "Phase16 Pedestal", manaCost := ManaCost.empty, types := #[.artifact] }
  let (gB0, tokBf) : Game × GameObject := afterDraw.createToken me
    { creature "Phase16 Dead Token" ManaCost.empty #["Construct"] 1 1 with isToken := true }
    (cause := some testCause)
  let (gB0, tokGyId) : Game × ObjectId := gB0.move tokBf.id (.graveyard me) none (cause := some testCause)
  let gB0 : Game := addPermanent (addPermanent (addPermanent (addPermanent (addPermanent gB0
    zeroDef me me) legDef me me) legDef me me) bareAuraDef me me) noncreaArtDef me me
  let gB0 : Game := insertObject gB0 saga1Def me .battlefield (some me) { counters := #[(.lore, 1)] }
  let gB0 : Game := addPermanent gB0 equipDef16 me me
  let zeroId := (gB0.battlefield.filter (·.name == "Phase16 Zero"))[0]!.id
  let legs := (gB0.battlefield.filter (·.name == "Phase16 Twin Legend")).map (·.id)
  let legKeep := legs[0]!
  let legDrop := legs[1]!
  let sagaId := (gB0.battlefield.filter (·.name == "Phase16 One-Chapter Saga"))[0]!.id
  let auraId := (gB0.battlefield.filter (·.name == "Phase16 Stray Aura"))[0]!.id
  let pedId := (gB0.battlefield.filter (·.name == "Phase16 Pedestal"))[0]!.id
  let eqId6 := (gB0.battlefield.filter (·.name == "Phase16 Sword"))[0]!.id
  let gB0 : Game := gB0.record
    (GameEvent.attached gB0.turnNumber (gB0.snapshot (gB0.object! eqId6)) pedId (cause := testCause))
  let preSbaIdx := gB0.events.size
  let gBPaused : Game := gB0.checkSBA
  let pausedBatchOk : Bool :=
    (match gBPaused.pending with | .chooseLegend p "Phase16 Twin Legend" ids => p == me && ids.size == 2 | _ => false) &&
    gBPaused.currentBatch.isSome &&
    (gBPaused.findObject? sagaId).any (·.isOnBattlefield) &&
    (gBPaused.findObject? auraId).any (·.isOnBattlefield) &&
    (gBPaused.findObject? tokGyId).isSome &&
    (gBPaused.object! eqId6).attachedTo == some pedId
  let gBResumed : Game := mustApply gBPaused me (.keepLegend legKeep)
  let sbaSlice : Array GameEvent := gBResumed.events.extract preSbaIdx gBResumed.events.size
  let batchOfPred (pred : RulesEvent → Bool) : Option BatchId :=
    (sbaSlice.find? (fun e => match e.change with | .rules r => pred r | _ => false)).bind (·.batch)
  let bZero := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some zeroId | _ => false)
  let bLeg := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some legDrop | _ => false)
  let bTok := batchOfPred (fun | .zone (.ceasedToExist eo) => eo.id == some tokGyId | _ => false)
  let bSaga := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some sagaId | _ => false)
  let bAura := batchOfPred (fun | .zone (.moved b _ .battlefield _ _ _ _ _) => b.id == some auraId | _ => false)
  let bEq := batchOfPred (fun | .permanent (.unattached eo h) => eo.id == some eqId6 && h == pedId | _ => false)
  let sameSingleBatchOk : Bool :=
    gBResumed.pending == Pending.none &&
    gBResumed.currentBatch.isNone &&
    (gBResumed.findObject? legKeep).any (·.isOnBattlefield) &&
    bZero.isSome &&
    bZero == bLeg && bZero == bTok && bZero == bSaga && bZero == bAura && bZero == bEq

  mustHold16 "6a.lkiCountersOk" lkiCountersOk &&
  mustHold16 "6b.pausedBatchOk" pausedBatchOk &&
  mustHold16 "6b.sameSingleBatchOk" sameSingleBatchOk &&
  mustHold16 "6.replay" ([gL1, gBPaused, gBResumed].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 111.8 token-flicker prohibition & simultaneous two-batch multi-target flicker.
#guard
  let (gF0, tokObj) : Game × GameObject := (addPermanent (addPermanent afterDraw bear me me) hero me me).createToken me
    { creature "Phase16 Ephemeral Token" ManaCost.empty #["Spirit"] 1 1 with isToken := true }
    (cause := some testCause)
  let bId := (gF0.battlefield.filter (·.name == bear.name))[0]!.id
  let hId := (gF0.battlefield.filter (·.name == hero.name))[0]!.id
  let tId := tokObj.id
  let preFIdx := gF0.events.size
  let gF1 : Game := gF0.flickerPermanents #[bId, hId, tId] (cause := some testCause)
  let fSlice : Array GameEvent := gF1.events.extract preFIdx gF1.events.size
  let exileBatches := fSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield .exile _ _ _ _)) => e.batch
    | _ => none
  let returnBatches := fSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .exile .battlefield _ _ _ _)) => e.batch
    | _ => none
  let exTokId := (gF1.objects.filter (fun o => o.name == "Phase16 Ephemeral Token" && o.zone == Zone.exile))[0]!.id
  let (gF1Stay, stayId) : Game × ObjectId := gF1.move exTokId .battlefield (some me) (cause := some testCause)
  let gF2 : Game := gF1Stay.checkSBA
  let flickerOk : Bool :=
    exileBatches.size == 3 &&
    exileBatches[0]! == exileBatches[1]! && exileBatches[1]! == exileBatches[2]! &&
    returnBatches.size == 2 &&
    returnBatches[0]! == returnBatches[1]! &&
    exileBatches[0]! != returnBatches[0]! &&
    gF1.battlefield.any (·.name == bear.name) &&
    gF1.battlefield.any (·.name == hero.name) &&
    !gF1.battlefield.any (·.name == "Phase16 Ephemeral Token") &&
    stayId == exTokId &&
    (gF1Stay.object! exTokId).zone == Zone.exile &&
    (gF2.findObject? exTokId).isNone

  mustHold16 "7.flickerOk" flickerOk &&
  mustHold16 "7.replay" ([gF1Stay, gF2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 603.10 `.creatureCardsPutIntoYourGy` (`after.creature && !after.token`) & CR 701.17c `ZoneVerb.mill`.
#guard
  let animArtMoved := GameEvent.moved 1
    { id := some ⟨200⟩, controller := some me, owner := me, types := #[.artifact, .creature] }
    .battlefield (.graveyard me)
    (after := some { id := some ⟨201⟩, owner := me, zone := .graveyard me, types := #[.artifact] })
    (cause := testCause)
  let impCreaMoved := GameEvent.moved 1
    { id := some ⟨202⟩, controller := some me, owner := me, types := #[.enchantment] }
    .battlefield (.graveyard me)
    (after := some { id := some ⟨203⟩, owner := me, zone := .graveyard me, types := #[.enchantment, .creature] })
    (cause := testCause)
  let tokCreaMoved := GameEvent.moved 1
    { id := some ⟨204⟩, controller := some me, owner := me, types := #[.creature], token := true }
    .battlefield (.graveyard me)
    (after := some { id := some ⟨205⟩, owner := me, zone := .graveyard me, types := #[.creature], token := true })
    (cause := testCause)
  let gyTriggerOk : Bool :=
    !animArtMoved.matchesTriggerPattern me none .creatureCardPutIntoYourGy &&
    impCreaMoved.matchesTriggerPattern me none .creatureCardPutIntoYourGy &&
    !tokCreaMoved.matchesTriggerPattern me none .creatureCardPutIntoYourGy

  let gM0 : Game := quiet afterDraw
  let lib0 := (gM0.player me).library
  let cMillEx := lib0.back!
  let cSurveilGy := lib0[lib0.size - 2]!
  let gM1 : Game := gM0.createEffect
    (.replacement { id := { kind := .finalityCounterExile, object := some cMillEx },
                    affectedPlayer := me, kind := .exileInsteadOfGraveyard (some cMillEx) false })
    (cause := some testCause)
  let gM2 : Game := gM1.mill me 1 (cause := some testCause)
  let (gM3, _) : Game × ObjectId := gM2.move cSurveilGy (.graveyard me) none (verb := some .put) (cause := some testCause)
  let millVerbOk : Bool :=
    GameEvent.milled gM3.events gM3.turnNumber me == 1 &&
    (gM3.followMilledPublic? cMillEx).any (fun o => o.zone == Zone.exile) &&
    (gM3.followMilledPublic? cSurveilGy).isNone
  let gMReplay : Game := (afterDraw.createEffect
    (.replacement { id := { kind := .finalityCounterExile, object := some ((afterDraw.player me).library.back!) },
                    affectedPlayer := me,
                    kind := .exileInsteadOfGraveyard (some ((afterDraw.player me).library.back!)) false })
    (cause := some testCause)).mill me 1 (cause := some testCause)

  mustHold16 "8a.gyTriggerOk" gyTriggerOk &&
  mustHold16 "8b.millVerbOk" millVerbOk &&
  mustHold16 "8.replay" (Game.replayEvents gMReplay.events == gMReplay && allRulesEventsClassified gMReplay)

-- 9. CR 800.4a/h leave-game continuation handling (3-player).
#guard
  let (gSacLeft, gWheelLeft, gRepLeft, gTrigTgtLeft, step9LeaveOk) :=
    let threeCfg16 : StartConfig := {
      seats := #[
        { name := "Chandra", deck := testRedDeck },
        { name := "Nissa", deck := testGreenDeck },
        { name := "Liliana", deck := testRedDeck }
      ]
      format := .constructed
      seed := 16
      startingPlayer := some 0
    }
    let g3 : Game :=
      match Start.start threeCfg16 with
      | .ok g => keepOpeningHands g 12
      | .error e => panic! e
    let p0 : PlayerId := ⟨0⟩
    let p1 : PlayerId := ⟨1⟩
    let p2 : PlayerId := ⟨2⟩
    -- 9a. `.chooseSacrificeCreature`: `p0` already chose `b0`, then last remaining chooser `p1` concedes ->
    --     `finishChosenSacrifices` runs and sacrifices `b0`!
    let gS0 := addPermanent (addPermanent g3 bear p0 p0) hero p1 p1
    let b0 := (gS0.battlefield.filter (fun o => o.name == bear.name && o.controller == some p0))[0]!.id
    let gS1 := gS0.change (.pending (.chooseSacrificeCreature p1 #[b0] #[]))
    let gS2 := gS1.concede p1
    let sacFinishOk :=
      gS2.pending == .none &&
      !(gS2.findObject? b0).any (·.isOnBattlefield)
    -- 9b. Multi-player `FraChoice` (`.mayWheel 2 #[p2]` on `p1`): `p1` conceding advances prompt to `p2`!
    let gW1 := g3.change (.pending (.fraChoice p1 (.mayWheel 2 #[p2])))
    let gW2 := gW1.concede p1
    let wheelAdvOk := gW2.pending == .fraChoice p2 (.mayWheel 2 #[])
    -- 9c. `.chooseReplacement`: `p1` conceding while `Pending.chooseReplacement p1 ...` is open during `p0`'s effect
    --     resumes `pendingReplacement` (putting counters on `p0`'s Bear) instead of wiping `pendingReplacement := none`!
    let gR0 := addPermanent (addPermanent g3 bear p0 p0) samsonDef16 p1 p1
    let bR0 := (gR0.battlefield.filter (fun o => o.name == bear.name && o.controller == some p0))[0]!.id
    let docR1 := (gR0.battlefield.filter (·.name == "Phase16 Doc Samson"))[0]!.id
    let idD1 : ReplacementId := { kind := .multiplyCountersPut, object := some docR1 }
    let idD2 : ReplacementId := { kind := .extraCounterOnPermanents, object := some docR1, counterKind := some .plusOnePlusOne }
    let gR0 := (gR0.createEffect
      (.replacement { id := idD1, source := some docR1, controller := some p1, affectedPlayer := p1,
                      kind := .modifyCountersPut (some bR0) none 0 2 }) (cause := some testCause)).createEffect
      (.replacement { id := idD2, source := some docR1, controller := some p1, affectedPlayer := p1,
                      kind := .modifyCountersPut (some bR0) none 1 1 }) (cause := some testCause)
    -- Prompt `p1` on `pendingReplacement` for `addPlusOnePlusOneTo` on `bR0`:
    let gRP := gR0.promptChooseReplacement p1 #[idD1, idD2]
      (.addPlusOnePlusOneTo bR0 2 false (some p0) (some testCause))
    let gRLeft := gRP.concede p1
    let repResumeOk :=
      gRLeft.pending == .none &&
      gRLeft.pendingReplacement.isNone &&
      -- `p1`'s replacement effects left with `docR1`, and `pendingReplacement` resumed so `bR0` got its 2 `+1/+1` counters!
      (gRLeft.object! bR0).status.plusOnePlusOne == 2
    -- 9d. `.chooseTargets p1` for a triggered ability while `p0` has an unrelated `proposalCheckpoint` does NOT pop `p0`'s checkpoint,
    --     and when `p0` concedes during `p0`'s own spell `.chooseTargets p0`, `.clearProposalCheckpoint` is emitted ONCE (not twice)!
    let gC0 := (g3.change .saveProposalCheckpoint).change (.pending (.chooseTargets p1))
    let gC1 := gC0.concede p1
    let unrelatedCpKept := gC1.proposalCheckpoint.isSome
    let gC1Clean := gC1.change .clearProposalCheckpoint
    let pingDef9 : CardDef := {
      lightningBolt with
      name := "Phase16 Target Bolt"
      manaCost := ManaCost.empty
    }
    let gOwn0 := insertObject g3 pingDef9 p0 (.hand p0)
    let boltH := (gOwn0.player p0).hand.back!
    let gOwn1 := mustApply gOwn0 p0 (.cast boltH)
    let preConcedeIdx := gOwn1.events.size
    let gOwn2 := gOwn1.concede p0
    let clearCpCount :=
      (gOwn2.events.extract preConcedeIdx gOwn2.events.size).filter (fun e =>
        e.change == .engine .clearProposalCheckpoint) |>.size
    let cpLeaveOk := unrelatedCpKept && gOwn2.proposalCheckpoint.isNone && clearCpCount == 1
    -- 9e. `.discardTwo`: an opponent leaving the game before discarding (CR 800.4) does NOT increment `draws`!
    let gD0 := (insertObject (insertObject g3 bear p2 (.hand p2)) bear p2 (.hand p2)).continueDiscardTwo p0 #[p1, p2] 0
    let p0HandBefore := (gD0.player p0).hand.size
    let gD1 := gD0.concede p1
    let p2Bears := ((gD1.player p2).hand.filter (fun id => (gD1.object! id).name == bear.name)).extract 0 2
    let gD2 := mustApply gD1 p2 (.choosePermanents p2Bears)
    let gDLast0 := g3.change (.pending (.fraChoice p1 (.discardTwo p0 #[] 1)))
    let gDLast1 := gDLast0.concede p1
    let discardTwoLeaveOk :=
      gD1.pending == .fraChoice p2 (.discardTwo p0 #[] 0) &&
      (gD2.player p0).hand.size == p0HandBefore &&
      (gDLast1.player p0).hand.size == (g3.player p0).hand.size + 1 &&
      [gD1, gD2, gDLast1].all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)
    (gS2, gW2, gRLeft, gC1Clean, sacFinishOk && wheelAdvOk && repResumeOk && cpLeaveOk && discardTwoLeaveOk &&
      Game.replayEvents gOwn2.events == gOwn2 && allRulesEventsClassified gOwn2)
  let step9AllOk :=
    step9LeaveOk &&
    [gSacLeft, gWheelLeft, gRepLeft, gTrigTgtLeft].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)
  mustHold16 "step9AllOk" step9AllOk

-- 10. CR 702.131a/b/d `citysBlessing` / `enduringStory` batch evaluation & `Option BatchId` envelope fidelity.
#guard
  let (gAscendPerm, gAscendSpellStack, gAscendSpellRes, step10BatchAndDesigOk) :=
    -- 10a. Player controls 10 permanents without Ascend; turning a 10th face-down Ascend creature face-up
    --      (no `ZoneEvent.moved` / `ZoneEvent.created` entry!) grants `citysBlessing` in `Core.closeBatch`!
    let ascendMorphDef : CardDef := {
      bear with
      name := "Phase16 Ascend Morph"
      keywords := #[Keyword.ascend, .morph CostSpec.empty]
    }
    let gAs0 := (List.range 9).foldl (fun g _ => addPermanent g bear me me) afterDraw
    let gAs0 := addPermanent gAs0 ascendMorphDef me me
    let amId := (gAs0.battlefield.filter (·.name == "Phase16 Ascend Morph"))[0]!.id
    let gAs0 := setFaceDown gAs0 amId true
    let noBlessingWhileFaceDown := !(gAs0.player me).citysBlessing && gAs0.permanentCount me == 10
    let gAs1 := mustApply gAs0 me (.activate amId 0)
    let blessingOnTurnFaceUp := (gAs1.player me).citysBlessing
    -- 10b. Instant/sorcery with `ascend` while controlling 10 permanents: does NOT grant `citysBlessing` on stack,
    --      DOES grant `citysBlessing` when `resolveTop` resolves it (CR 702.131a)!
    let ascendSpellDef : CardDef := {
      name := "Phase16 Ascend Insight"
      manaCost := ManaCost.empty
      types := #[.sorcery]
      keywords := #[Keyword.ascend]
      spellEffect := some (Effect.draw 1)
    }
    let gSp0 := (List.range 10).foldl (fun g _ => addPermanent g bear me me) afterDraw
    let gSp0 := insertObject gSp0 ascendSpellDef me (.hand me)
    let spH := (gSp0.player me).hand.back!
    let gSpCast := mustApply gSp0 me (.cast spH)
    let notOnStackOk := !(gSpCast.player me).citysBlessing
    let gSpRes := gSpCast.resolveTop
    let onResOk := (gSpRes.player me).citysBlessing
    -- 10c. `Option BatchId` envelope fidelity:
    --      - Unbatched / proposed `GameEvent`s carry `batch == none`.
    --      - Unstamped `.engine` changes carry `batch == none`.
    --      - The very first committed rules batch of a fresh game (`Start.start`) carries `some ⟨0⟩` (`!= none`)!
    let unbatchedProposed : GameEvent := GameEvent.drew 1 me ⟨9⟩ 1 (cause := testCause)
    let unstampedEngine : GameEvent := GameEvent.engine 1 (.logMsg "note")
    let firstRulesBatch :=
      afterDraw.events.findSome? fun e =>
        match e.change with
        | .rules _ => e.batch
        | _ => none
    let batchEnvelopeOk :=
      unbatchedProposed.batch == none &&
      unstampedEngine.batch == none &&
      firstRulesBatch == some ⟨0⟩ &&
      (unbatchedProposed.withBatch ⟨0⟩).batch == some ⟨0⟩ &&
      unbatchedProposed.batch != (unbatchedProposed.withBatch ⟨0⟩).batch
    (gAs1, gSpCast, gSpRes,
     noBlessingWhileFaceDown && blessingOnTurnFaceUp && notOnStackOk && onResOk && batchEnvelopeOk)
  let step10AllOk :=
    step10BatchAndDesigOk &&
    [gAscendPerm, gAscendSpellStack, gAscendSpellRes].all (fun g =>
      Game.replayEvents g.events == g && allRulesEventsClassified g)
  mustHold16 "step10AllOk" step10AllOk

end Phase16EventAlignment

/-! ### Phase 17 Event Alignment Isolation Tests (CR 500.4–5 / 514.3 / 603.3c–d / 603.4 / 608.2a–c / 608.3b–c,f / 610.3 / 611.2a / 704.3 / 704.5d–e,j / 707.10 / 707.12 / 733.1 / 800.4)

1. Nested-batch `currentBatch` replay & shared `EffectId` fidelity across `Pending.chooseReplacement`.
2. CR 733.1 `reverseToProposalCheckpoint?` filtering of `.waitingTriggers` and `DelayedTriggerEvent.consumed`.
3. Pause-safe continuations (`putShadowCounter`, `applyPut` `.asArtifact`, `untapUnblockable`, `finishPlaceSearched`, `factOrFictionGyLoop`, `castFreeCopy`, `pass`/`concede` `consecutivePasses` & `pendingPriority`) and `0`-counter log parity.
4. CR 603.3c–d modal trigger stack announcement (`chooseUpToXModes`, `stackHydeMode`, `oneUnused` / `oneUnusedThisTurn`), mandatory target removal (`putQueuedTrigger`), CR 707.10 stack-copy mode preservation, and CR 113.7a LKI resolution.
5. CR 603.4 / 608.2a intervening-`"if"` & trigger checks (`gingerbrute`, `obAngel`, `tamiyoStun`, `windcragSiege`, `copySelfNonlegendary`).
6. CR 704.5d–e / 707.10 / 707.12 card & permanent spell copy lifecycle (`.uldarosCopies`), CR 608.2b / 608.3b–c / 303.4a,c Aura resolution (`secretInvasion`, hexproof fizzle, copy cease), and multi-target retargeting validation.
7. CR 704.3 / 704.5j recursive `keepLegend` `preBf`, CR 610.3 post-departure `linkedExile` separate batch, CR 303.4f two-pass simultaneous entry Aura `preBattlefield` check (`placeSearchedBatch` & `returnLinkedExileLoop`), and *Worlds Within Worlds* separate sequential CR 608.2c batches.
8. CR 800.4 `mayThen` departure decline & pregame concessions (`declareMulligan` & `.mayBeginOnBattlefield`), silent cleanup `finishPostSbaCleanup` routing through `beginTurn`, and step/phase `EffectDuration` expiry (`CR 500.4–5 / 511.2 / 611.2a`). -/
section Phase17EventAlignment

private def samsonDef17 : CardDef :=
  { bear with name := "Phase17 Doc Samson", staticAbilities := #[.extraCounterOnPermanents] }

private def misterHydeDef17 : CardDef :=
  creature "Mister Hyde, Monster Within" { symbols := #[.generic 2, .colored .green] } #["Human", "Villain"] 2 2
    (supertypes := #[.legendary])
    (oracleText := "At the beginning of your upkeep, choose one —\n• Put a +1/+1 counter on Mister Hyde.\n• Remove a counter from a creature you control. If you do, draw a card.")

private def wreckingCrewDef17 : CardDef :=
  creature "The Ruinous Wrecking Crew" { symbols := #[.x, .colored .black, .colored .red] } #["Human", "Villain"] 2 2
    (supertypes := #[.legendary])
    (oracleText := "The Ruinous Wrecking Crew enters with X +1/+1 counters on it.\nWhen The Ruinous Wrecking Crew enters, choose up to X —\n• Discard a card, then draw a card.\n• Target opponent loses 2 life.\n• Destroy target token.\n• Each player sacrifices a creature of their choice.")

private def windcragDef17 : CardDef :=
  enchantment "Windcrag Siege" ManaCost.empty
    "As this enchantment enters, choose Mardu or Jeskai.\n• Mardu — If a creature attacking causes a triggered ability of a permanent you control to trigger, that ability triggers an additional time.\n• Jeskai — At the beginning of your upkeep, create a 1/1 red Goblin creature token. It gains lifelink and haste until end of turn."

private def secretInvasionDef17 : CardDef :=
  aura "Secret Invasion" ManaCost.empty "Enchant creature you control"

private def worldsDef17 : CardDef :=
  sorcery "Worlds Within Worlds" ManaCost.empty
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."

private def mustHold17 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 17 guard failed: {label}"

-- 1. Nested-batch `currentBatch` replay & shared `EffectId` fidelity across `Pending.chooseReplacement`.
#guard
  let gN0 : Game := addPermanent (addPermanent afterDraw bear me me) samsonDef17 me me
  let bId := (gN0.battlefield.filter (·.name == bear.name))[0]!.id
  let docId := (gN0.battlefield.filter (·.name == "Phase17 Doc Samson"))[0]!.id
  let idDocPlus : ReplacementId := { kind := .extraCounterOnPermanents, object := some docId, counterKind := some .plusOnePlusOne }
  let idCntDbl : ReplacementId := { kind := .multiplyCountersPut, object := some bId }
  let gN0 : Game := gN0.createEffect
    (.replacement { id := idCntDbl, source := some bId, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut none (some .plusOnePlusOne) 0 2 }) (cause := some testCause)
  let gOuterPaused : Game :=
    gN0.withBatch none fun g =>
      g.addPlusOnePlusOneTo (g.object! bId) 1 (cause := some testCause)
  let outerOk : Bool :=
    match gOuterPaused.currentBatch, gOuterPaused.pending with
    | some (_, none), .chooseReplacement p cs => p == me && cs.size == 2
    | _, _ => false
  let nextEffBefore := gN0.nextEffectId
  let gNestedPaused : Game :=
    gN0.withBatch none fun g =>
      g.withBatch (some (.oneShotEffect none (some docId) (some me))) fun g =>
        let g := g.pumpPermanent (g.object! bId) 2 2
        g.addPlusOnePlusOneTo (g.object! bId) 1
  let mintedEffId : EffectId := ⟨nextEffBefore⟩
  let innerBatchOk : Bool :=
    (match gNestedPaused.currentBatch with
     | some (_, some (.oneShotEffect (some eid) (some s) (some c))) =>
       eid == mintedEffId && s == docId && c == me
     | _ => false) &&
    gNestedPaused.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.continuousEffect (.created _ _)), some (.oneShotEffect (some eid) (some s) (some c)) =>
        eid == mintedEffId && s == docId && c == me
      | _, _ => false)
  let gNestedResumed : Game := mustApply gNestedPaused me (.chooseReplacement idDocPlus)
  let resumedOk : Bool :=
    gNestedResumed.pending == .none &&
    gNestedResumed.currentBatch.isNone &&
    (gNestedResumed.object! bId).status.plusOnePlusOne == 4

  mustHold17 "1.outerOk" outerOk &&
  mustHold17 "1.innerBatchOk" innerBatchOk &&
  mustHold17 "1.resumedOk" resumedOk &&
  mustHold17 "1.replay" ([gOuterPaused, gNestedPaused, gNestedResumed].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. CR 733.1 `reverseToProposalCheckpoint?` filtering of `.waitingTriggers` & `DelayedTriggerEvent.consumed`.
#guard
  let deathWatcherAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger .creatureYouControlDies
      { body := Instruction.gainLifeFixed 2, phrase := "You gain 2 life" }
  let watcherDef : CardDef :=
    { bear with name := "Phase17 Watcher", triggeredAbilities := #[deathWatcherAb] }
  let gR0 : Game := addPermanent (addPermanent afterDraw watcherDef me me) hero me me
  let heroId := (gR0.battlefield.filter (·.name == hero.name))[0]!.id
  let dtSpec : DelayedTrigger := {
    controller := me
    kind := .copyNextInstantSorceryThisTurn
    cause := testCause
  }
  let gR0 : Game := gR0.record (GameEvent.delayedTriggerCreated gR0.turnNumber dtSpec)
  let gCkpt : Game := gR0.change .saveProposalCheckpoint
  let gAct0 : Game :=
    gCkpt.withProposalAction .costAction fun g =>
      let g := g.moveToOwnerGraveyard (g.object! heroId) "dies" (verb := some .sacrifice) (cause := some testCause)
      let g := g.change (.waitingTriggers g.waitingTriggers)
      g.record (GameEvent.delayedTriggerConsumed g.turnNumber dtSpec)
  let topLib := (gAct0.player me).library.back!
  let gAct1 : Game :=
    gAct0.withProposalAction .manaAbility fun g =>
      let g := g.record (GameEvent.revealed g.turnNumber me #[topLib] (cause := some (.gameRule .spellCast)))
      g.addMana me (.colored .red) (cause := some (.gameRule .spellCast))
  let preRevHasTrigAndConsumed : Bool :=
    gAct1.waitingTriggers.size == 1 && gAct1.delayedTriggers.isEmpty
  let gRev : Game :=
    match gAct1.reverseToProposalCheckpoint? with
    | .ok g => g
    | .error e => panic! e
  let revFilteredOk : Bool :=
    preRevHasTrigAndConsumed &&
    (gRev.findObject? heroId).any (·.isOnBattlefield) &&
    (gRev.player me).manaPool.red == 1 &&
    gRev.waitingTriggers.isEmpty &&
    gRev.delayedTriggers.contains dtSpec

  mustHold17 "2.revFilteredOk" revFilteredOk &&
  mustHold17 "2.replay" ([gAct1, gRev].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. Pause-safe continuations & `0`-counter log parity.
#guard
  -- 3a. `putShadowCounter` across `Pending.chooseReplacement` and `0`-counter replacement guard.
  let gSh0 : Game := addPermanent (addPermanent afterDraw bear me me) samsonDef17 me me
  let shBear := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let docSh := (gSh0.battlefield.filter (·.name == "Phase17 Doc Samson"))[0]!.id
  let idDocSh : ReplacementId := { kind := .extraCounterOnPermanents, object := some docSh, counterKind := some .shadow }
  let idDblSh : ReplacementId := { kind := .multiplyCountersPut, object := some shBear }
  let gSh1 : Game := gSh0.createEffect
    (.replacement { id := idDblSh, source := some shBear, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut (some shBear) (some .shadow) 0 2 }) (cause := some testCause)
  let logBeforeSh := gSh1.log.size
  let gShPaused : Game := gSh1.putShadowCounter (gSh1.object! shBear)
  let shPausedOk : Bool :=
    (match gShPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    !(gShPaused.currentSubtypes (gShPaused.object! shBear)).contains .wraith &&
    !(gShPaused.log.extract logBeforeSh gShPaused.log.size).any (·.contains "shadow counter")
  let gShDone : Game := mustApply gShPaused me (.chooseReplacement idDocSh)
  let shDoneOk : Bool :=
    gShDone.pending == .none &&
    (gShDone.object! shBear).status.counterCount .shadow == 4 &&
    (gShDone.currentSubtypes (gShDone.object! shBear)).contains .wraith &&
    (gShDone.log.extract logBeforeSh gShDone.log.size).any (·.contains "gets a shadow counter")

  -- `0`-counter replacement guard for both `putShadowCounter` and `addPlusOnePlusOneTo`:
  let gZero0 : Game := addPermanent afterDraw bear me me
  let zBear := (gZero0.battlefield.filter (·.name == bear.name))[0]!.id
  let idZero : ReplacementId := { kind := .multiplyCountersPut, object := some zBear }
  let gZero1 : Game := gZero0.createEffect
    (.replacement { id := idZero, source := some zBear, controller := some me, affectedPlayer := me,
                    kind := .modifyCountersPut (some zBear) none 0 0 }) (cause := some testCause)
  let logBeforeZ := gZero1.log.size
  let gZero2 : Game := (gZero1.putShadowCounter (gZero1.object! zBear)).addPlusOnePlusOneTo (gZero1.object! zBear) 2 (cause := some testCause)
  let zeroCounterGuardOk : Bool :=
    (gZero2.object! zBear).status.plusOnePlusOne == 0 &&
    (gZero2.object! zBear).status.counterCount .shadow == 0 &&
    !(gZero2.currentSubtypes (gZero2.object! zBear)).contains .wraith &&
    gZero2.log.size == logBeforeZ

  -- 3b. `applyPut` (`.source, .asArtifact, .none`) across `Pending.chooseReplacement` & exile redirect.
  let oddHeroDef : CardDef := { hero with name := "Phase17 Odd Hero", staticAbilities := #[.asEntersChooseOddEven] }
  let gArt0 : Game := insertObject afterDraw oddHeroDef me (.graveyard me)
  let gyHero := (gArt0.player me).graveyard.back!
  let logBeforeArt := gArt0.log.size
  let gArtPaused : Game := gArt0.applyPut me (.onEnterDraw 1) (some gyHero) #[] .source .asArtifact .none
  let artPausedOk : Bool :=
    (match gArtPaused.pending with | .chooseReplacement p _ => p == me | _ => false) &&
    !(gArtPaused.log.extract logBeforeArt gArtPaused.log.size).any (·.contains "returns as an artifact")
  let gArtDone : Game := mustApply gArtPaused me (.chooseMode 0)
  let enteredHero := (gArtDone.battlefield.filter (·.name == "Phase17 Odd Hero"))[0]!
  let artDoneOk : Bool :=
    gArtDone.pending == .none &&
    (gArtDone.types enteredHero).contains .artifact &&
    (gArtDone.log.extract logBeforeArt gArtDone.log.size).any (·.contains "returns as an artifact")

  -- 3c. `applyFra` `.untapUnblockable` across stun-counter `Pending.chooseReplacement`.
  let gUU0 : Game := addPermanent (addPermanent afterDraw bear me me) hero me me
  let uuBear := (gUU0.battlefield.filter (·.name == bear.name))[0]!.id
  let uuHero := (gUU0.battlefield.filter (·.name == hero.name))[0]!.id
  let idStunSelf : ReplacementId := { kind := .stunCounterUntap, object := some uuBear }
  let idStunExt : ReplacementId := { kind := .stunCounterUntap, object := some uuHero }
  let gUU1 : Game :=
    ((gUU0.becomeTapped (gUU0.object! uuBear) (cause := some testCause)).recordPutCounters
      uuBear .stun 1 (some me) (cause := some testCause)).createEffect
      (.replacement { id := idStunExt, source := some uuHero, controller := some me, affectedPlayer := me,
                      kind := .stunCounterUntap uuBear }) (cause := some testCause)
  let uuEff : Effect := {
    targeting := .of .creature
    body := .seq #[
      Instruction.untap (.target 0),
      Instruction.cantBeBlocked (.target 0)
    ]
  }
  let gUUPaused : Game := gUU1.applyEffect me uuEff #[Target.permanent uuBear] (sourceId := some uuHero)
  let uuPausedOk : Bool :=
    (match gUUPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    !gUUPaused.hasCantBeBlocked (gUUPaused.object! uuBear)
  let gUUDone : Game := mustApply gUUPaused me (.chooseReplacement idStunSelf)
  let uuDoneOk : Bool :=
    gUUDone.pending == .none &&
    (gUUDone.object! uuBear).status.tapped &&
    (gUUDone.object! uuBear).status.stun == 0 &&
    gUUDone.hasCantBeBlocked (gUUDone.object! uuBear)

  -- 3d. `factOrFictionGyLoop` across competing graveyard-exile replacements.
  let gFoF0 : Game := insertObject (insertObject afterDraw bear me (.library me)) hero me (.library me)
  let libFoF := (gFoF0.player me).library
  let fofC1 := libFoF.back!
  let fofC2 := libFoF[libFoF.size - 2]!
  let idExA : ReplacementId := { kind := .finalityCounterExile, object := some fofC1 }
  let idExB : ReplacementId := { kind := .exileOppDeath, object := some fofC1 }
  let gFoF1 : Game := (gFoF0.createEffect
    (.replacement { id := idExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some fofC1) false })
    (cause := some testCause)).createEffect
    (.replacement { id := idExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some fofC1) false })
    (cause := some testCause)
  let gFoFPaused : Game := gFoF1.factOrFictionGyLoop me #[fofC1, fofC2]
  let fofPausedOk : Bool :=
    (match gFoFPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gFoFPaused.object! fofC2).zone == .library me
  let gFoFDone : Game := mustApply gFoFPaused me (.chooseReplacement idExA)
  let fofDoneOk : Bool :=
    gFoFDone.pending == .none &&
    (gFoFDone.followMovedToZone? fofC1 (· == .exile)).isSome &&
    (gFoFDone.followMovedToZone? fofC2 (· == .graveyard me)).isSome

  -- 3e. `PriorityActions.pass` resets `consecutivePasses` before `resolveTop`.
  let instDrawDef : CardDef := {
    name := "Phase17 Quick Draw"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some (Effect.draw 1)
  }
  let gPass0 : Game := insertObject afterDraw instDrawDef me (.hand me)
  let qdId := (gPass0.player me).hand.back!
  let gPass1 : Game := mustApply gPass0 me (.cast qdId)
  let gPass2 : Game := mustApply (mustApply gPass1 me .pass) opp .pass
  let passResetOk : Bool := gPass2.consecutivePasses == 0 && gPass2.stack.isEmpty

  mustHold17 "3a.shPausedOk" shPausedOk &&
  mustHold17 "3a.shDoneOk" shDoneOk &&
  mustHold17 "3a.zeroCounterGuardOk" zeroCounterGuardOk &&
  mustHold17 "3b.artPausedOk" artPausedOk &&
  mustHold17 "3b.artDoneOk" artDoneOk &&
  mustHold17 "3c.uuPausedOk" uuPausedOk &&
  mustHold17 "3c.uuDoneOk" uuDoneOk &&
  mustHold17 "3d.fofPausedOk" fofPausedOk &&
  mustHold17 "3d.fofDoneOk" fofDoneOk &&
  mustHold17 "3e.passResetOk" passResetOk &&
  mustHold17 "3.replay" ([gShPaused, gShDone, gZero2, gArtPaused, gArtDone, gUUPaused, gUUDone, gFoFPaused, gFoFDone, gPass2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 603.3c–d modal trigger stack announcement, mandatory target removal, stack-copy mode preservation, & LKI resolution.
#guard
  -- 4a. Mandatory-target non-FRA triggered ability with zero legal targets is removed in `putQueuedTrigger` (CR 603.3d).
  let mandTargetAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.gainLife .you)
      { targeting := .of .oppCreature, body := Instruction.destroy (.target 0), phrase := "Destroy target creature an opponent controls." }
  let mandWatcherDef : CardDef := { bear with name := "Phase17 Mandatory Watcher", triggeredAbilities := #[mandTargetAb] }
  let gMand0 : Game := addPermanent afterDraw mandWatcherDef me me
  let logBeforeMand := gMand0.log.size
  let gMand1 : Game := (gMand0.gainLife me 1 (cause := some testCause)).receivePriority me
  let mandRemovedOk : Bool :=
    gMand1.stack.isEmpty &&
    gMand1.waitingTriggers.isEmpty &&
    (gMand1.log.extract logBeforeMand gMand1.log.size).any (·.contains "no legal target")

  -- 4b. `.oneUnused` (`gollumMode`): announces mode on stack placement, copies preserve announced mode (CR 707.10),
  --     resolves using LKI even after source left `.battlefield` (CR 113.7a), and once all 3 modes are chosen,
  --     a 4th placement removes the ability with `noLegalMode` and WITHOUT `StackObjectEvent.resolved`!
  let gollumTrigAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.ofTrigger .gollumMode)
  let gollumTestDef : CardDef := { bear with name := "Phase17 Gollum Test", triggeredAbilities := #[gollumTrigAb] }
  let gGol0 : Game := addPermanent afterDraw gollumTestDef me me
  let golId := (gGol0.battlefield.filter (·.name == "Phase17 Gollum Test"))[0]!.id
  -- Trigger 1: choose mode 2 (draw a card), copy stack ability, destroy source before resolving, then resolve both!
  let gGolStack0 : Game := gGol0.putTriggeredAbilityOnStack me (gGol0.object! golId) gollumTrigAb "triggers" (eventCause := some testCause)
  let golPromptedOnStack : Bool :=
    match gGolStack0.pending with
    | .fraChoice p (.stackTriggerUnusedMode _ (some sid) avail true) => p == me && sid == golId && avail == #[0, 1, 2]
    | _ => false
  let gGolChosen0 : Game := mustApply gGolStack0 me (.chooseMode 2)
  let stackAbId := gGolChosen0.stack.back!.objectId
  let announcedOnStackOk : Bool := gGolChosen0.chosenModesOf (gGolChosen0.object! stackAbId) == #[2]
  let gGolCopied : Game := gGolChosen0.copyStackAbility (gGolChosen0.object! stackAbId) me
  let copyAbId := gGolCopied.stack.back!.objectId
  let copyPreservedModeOk : Bool := gGolCopied.chosenModesOf (gGolCopied.object! copyAbId) == #[2]
  -- Destroy `golId` before resolving either the copy or the original ability (CR 113.7a LKI):
  let gGolSrcDead : Game := gGolCopied.moveToOwnerGraveyard (gGolCopied.object! golId) "dies" (verb := some .destroy) (cause := some testCause)
  let handBeforeGol := (gGolSrcDead.player me).hand.size
  let gGolResBoth : Game := gGolSrcDead.resolveTop.resolveTop
  let golLkiAndCopyResOk : Bool := (gGolResBoth.player me).hand.size == handBeforeGol + 2

  -- Re-add a fresh source, choose modes 0, 1, and 2 across 3 placements, then verify a 4th placement is removed via `noLegalMode` without `resolved`:
  let gEx0 : Game := addPermanent afterDraw gollumTestDef me me
  let exSrc := (gEx0.battlefield.filter (·.name == "Phase17 Gollum Test"))[0]!.id
  let placeAndChoose (g : Game) (m : Nat) : Game :=
    let g1 := g.putTriggeredAbilityOnStack me (g.object! exSrc) gollumTrigAb "triggers" (eventCause := some testCause)
    (mustApply g1 me (.chooseMode m)).resolveTop
  let gEx3 : Game := placeAndChoose (placeAndChoose (placeAndChoose gEx0 0) 1) 2
  let preFourthIdx := gEx3.events.size
  let gEx4 : Game := gEx3.putTriggeredAbilityOnStack me (gEx3.object! exSrc) gollumTrigAb "triggers" (eventCause := some testCause)
  let fourthSlice := gEx4.events.extract preFourthIdx gEx4.events.size
  let fourthNoLegalModeOk : Bool :=
    gEx4.stack.isEmpty &&
    fourthSlice.any (fun e => e.cause? == some (.gameRule .noLegalMode)) &&
    !fourthSlice.any (fun e => match e.change with | .rules (.stackObject (.resolved ..)) => true | _ => false)

  -- 4c. *Mister Hyde* (`.stackHydeMode`) and *The Ruinous Wrecking Crew* (`.upToTriggerModes`):
  let gHyde0 : Game := addPermanent afterDraw misterHydeDef17 me me
  let hydeId := (gHyde0.battlefield.filter (·.name == misterHydeDef17.name))[0]!.id
  let hydeAb := misterHydeDef17.triggeredAbilities[0]!
  let gHydeStack : Game := gHyde0.putTriggeredAbilityOnStack me (gHyde0.object! hydeId) hydeAb "combat" (eventCause := some testCause)
  let hydePromptOk : Bool := gHydeStack.pending == .fraChoice me (.stackHydeMode gHydeStack.stack.back!.objectId)
  let gHydeMode0 : Game := (mustApply gHydeStack me (.chooseMode 0)).resolveTop
  let hydeResolvedOk : Bool := (gHydeMode0.object! hydeId).status.plusOnePlusOne == 1

  let gCrew0 : Game := insertObject afterDraw wreckingCrewDef17 me (.hand me)
  let crewHandId := (gCrew0.player me).hand.back!
  let gCrewMana : Game := ((gCrew0.addMana me (.colored .black) 2 (cause := some testCause)).addMana
    me (.colored .red) 2 (cause := some testCause))
  let gCrewCast : Game := mustApply (mustApply (mustApply gCrewMana me (.cast crewHandId)) me (.chooseX 2)) me .pay
  let gCrewEntered : Game := gCrewCast.resolveTop.receivePriority me
  let crewPromptOnStackOk : Bool :=
    match gCrewEntered.pending with
    | .fraChoice p (.upToTriggerModes _ 2 #[]) => p == me
    | _ => false
  let oppLifeBefore := (gCrewEntered.player opp).life
  -- Mode 1 is `"Target opponent loses 2 life"`, then decline 2nd mode (`choose up to X`) and target `opp`:
  let gCrewMode1 : Game := mustApply (mustApply (mustApply gCrewEntered me (.chooseMode 1)) me .decline) me (.target (.player opp))
  let gCrewResolved : Game := gCrewMode1.resolveTop
  let crewResolvedOk : Bool := (gCrewResolved.player opp).life == oppLifeBefore - 2

  mustHold17 "4a.mandRemovedOk" mandRemovedOk &&
  mustHold17 "4b.golPromptedOnStack" golPromptedOnStack &&
  mustHold17 "4b.announcedOnStackOk" announcedOnStackOk &&
  mustHold17 "4b.copyPreservedModeOk" copyPreservedModeOk &&
  mustHold17 "4b.golLkiAndCopyResOk" golLkiAndCopyResOk &&
  mustHold17 "4b.fourthNoLegalModeOk" fourthNoLegalModeOk &&
  mustHold17 "4c.hydePromptOk" hydePromptOk &&
  mustHold17 "4c.hydeResolvedOk" hydeResolvedOk &&
  mustHold17 "4c.crewPromptOnStackOk" crewPromptOnStackOk &&
  mustHold17 "4c.crewResolvedOk" crewResolvedOk &&
  mustHold17 "4.replay" ([gMand1, gGolChosen0, gGolCopied, gGolResBoth, gEx4, gHydeMode0, gCrewEntered, gCrewResolved].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 603.4 / 608.2a intervening-`"if"` & trigger checks (`gingerbrute`, `obAngel`, `tamiyoStun`, `windcragSiege`, `copySelfNonlegendary`).
#guard
  -- 5a. Gingerbrute monarch trigger: requires `isMonarch` on both trigger and resolution.
  let gingerAb : TriggeredAbility := TriggeredAbility.ofPattern .stepYourUpkeep
    "At the beginning of your upkeep, if you're the monarch, create a Gingerbrute token."
    (Instruction.ifThen (.playerPred .you .isMonarch) (Instruction.createTokensFixed .gingerbrute 1))
    (interveningIf? := some TriggeredAbility.condYouAreMonarch)
  let gingerSrcDef : CardDef := { bear with name := "Phase17 Ginger Court", triggeredAbilities := #[gingerAb] }
  let gGin0 : Game := addPermanent afterDraw gingerSrcDef me me
  let gGinNoMonarch : Game := gGin0.record (GameEvent.stepped gGin0.turnNumber .upkeep me)
  let gGinMonarch0 : Game := gGin0.becomeMonarch me
  let gGinTrig : Game := (gGinMonarch0.record (GameEvent.stepped gGinMonarch0.turnNumber .upkeep me)).receivePriority me
  let gGinLostMonarch : Game := (gGinTrig.becomeMonarch opp).resolveTop
  let gGinKeptMonarch : Game := gGinTrig.resolveTop
  let gingerOk : Bool :=
    gGinNoMonarch.waitingTriggers.isEmpty &&
    gGinTrig.stack.size == 1 &&
    !(gGinLostMonarch.permanentsOf me).any (·.name == "Gingerbrute") &&
    gGinLostMonarch.events.any (fun e => match e.change with | .rules (.stackObject (.removedOnResolution ..)) => true | _ => false) &&
    (gGinKeptMonarch.permanentsOf me).any (·.name == "Gingerbrute")

  -- 5b. Ob Nixilis Angel trigger: requires `loggedLifeGained > 0` on trigger and resolution.
  let obAb : TriggeredAbility := TriggeredAbility.ofPattern .stepEachEndStep
    "At the beginning of each end step, if you gained life this turn, ..."
    (Instruction.ifThen (TriggeredAbility.condGainedLifeAtLeast 1) (Instruction.createTokensFixed .angel44white 1))
    (interveningIf? := some (TriggeredAbility.condGainedLifeAtLeast 1))
  let obSrcDef : CardDef := { bear with name := "Phase17 Angelic Watcher", triggeredAbilities := #[obAb] }
  let gOb0 : Game := addPermanent afterDraw obSrcDef me me
  let gObNoLife : Game := gOb0.record (GameEvent.stepped gOb0.turnNumber .end me)
  let gObLife : Game := (gOb0.gainLife me 1 (cause := some testCause)).record (GameEvent.stepped gOb0.turnNumber .end me)
  let obOk : Bool := gObNoLife.waitingTriggers.isEmpty && gObLife.waitingTriggers.size == 1

  -- 5c. Tamiyo stun trigger: triggers ONLY if `me` is monarch at combat damage, does NOT recheck `isMonarch` at resolution,
  --     and taps + stuns ALL creatures that dealt combat damage to `me` in that batch!
  let tamAb : TriggeredAbility := TriggeredAbility.ofPattern
    (.whenCond .combatDamageToYou TriggeredAbility.condYouAreMonarch)
    "Whenever one or more creatures deal combat damage to you, if you were the monarch..."
    (Instruction.tapAndStun .triggerSubject) (grouping := .oncePerBatch)
  let tamSrcDef : CardDef := { bear with name := "Phase17 Tamiyo Watcher", triggeredAbilities := #[tamAb] }
  let gTam0 : Game := addPermanent (addPermanent (addPermanent afterDraw tamSrcDef me me) bear opp opp) hero opp opp
  let oppBear := (gTam0.battlefield.filter (fun o => o.name == bear.name && o.controller == some opp))[0]!.id
  let oppHero := (gTam0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
  let combatCause : EventCause := .turnBased (.dealCombatDamage false)
  let dealCombatBatch (g : Game) : Game :=
    g.withBatch (some combatCause) fun (g : Game) =>
      let g : Game := g.record (GameEvent.damagedPlayer g.turnNumber
        (g.snapshotDamageSource (g.object! oppBear)) me 2 true (cause := combatCause))
      g.record (GameEvent.damagedPlayer g.turnNumber
        (g.snapshotDamageSource (g.object! oppHero)) me 2 true (cause := combatCause))
  let gTamNoMonarch : Game := dealCombatBatch gTam0
  let gTamMonarch0 : Game := (dealCombatBatch (gTam0.becomeMonarch me)).receivePriority me
  let gTamMonarch : Game := mustApply gTamMonarch0 me (.stackTriggers #[0, 1, 2])
  -- Top two of stack are the inherent per-creature monarch triggers (`opp` steals the monarchy); `tamiyoStun` STILL resolves next and stuns BOTH `oppBear` and `oppHero`!
  let gTamRes1 : Game := gTamMonarch.resolveTop.resolveTop
  let gTamRes : Game := gTamRes1.resolveTop
  let tamiyoOk : Bool :=
    gTamNoMonarch.waitingTriggers.isEmpty &&
    gTamMonarch.stack.size == 3 &&
    (gTamRes1.player opp).isMonarch &&
    (gTamRes.object! oppBear).status.tapped && (gTamRes.object! oppBear).status.stun == 1 &&
    (gTamRes.object! oppHero).status.tapped && (gTamRes.object! oppHero).status.stun == 1

  -- 5d. *Windcrag Siege* (`windcragDef17`): `"Mardu"` does not trigger upkeep Goblin; `"Jeskai"` does!
  let putSiegeWithMode (modeIdx : Nat) : Game :=
    let g0 := insertObject afterDraw windcragDef17 me (.hand me)
    let cid := (g0.player me).hand.back!
    let (g1, _) := g0.putOntoBattlefield cid me (cause := some testCause)
    mustApply g1 me (.chooseMode modeIdx)
  let gMardu : Game := putSiegeWithMode 0
  let gMarduUpkeep : Game := gMardu.record (GameEvent.stepped gMardu.turnNumber .upkeep me)
  let gJeskai : Game := putSiegeWithMode 1
  let gJeskaiUpkeep : Game := ((gJeskai.record (GameEvent.stepped gJeskai.turnNumber .upkeep me)).receivePriority me).resolveTop
  let windcragOk : Bool :=
    gMarduUpkeep.waitingTriggers.isEmpty &&
    (gJeskaiUpkeep.permanentsOf me).any (fun o => o.printed.isToken && gJeskaiUpkeep.hasSubtype o .goblin)

  -- 5e. `copySelfNonlegendary`: nontoken triggers & resolves via LKI even if source left `.battlefield`, while token copy does NOT trigger!
  let selfCopyAb : TriggeredAbility := SharedTrigger.copySelfNonlegendary.toTriggeredAbility
  let selfCopyDef : CardDef := { bear with name := "Phase17 Clone Legend", supertypes := #[.legendary], triggeredAbilities := #[selfCopyAb] }
  let gSC0 : Game := insertObject afterDraw selfCopyDef me (.hand me)
  let scHandId := (gSC0.player me).hand.back!
  let (gSC1, scPermId) := gSC0.putOntoBattlefield scHandId me (cause := some testCause)
  let gSC1 := gSC1.afterPermanentEnters (gSC1.object! scPermId) |>.receivePriority me
  -- Destroy `scPermId` before its ETB resolves -> LKI still creates two nonlegendary token copies, and neither token copy re-triggers `selfCopyAb`!
  let gSC2 : Game := (gSC1.moveToOwnerGraveyard (gSC1.object! scPermId) "dies" (verb := some .destroy) (cause := some testCause)).resolveTop
  let tokenClones := (gSC2.permanentsOf me).filter (fun o => o.name == "Phase17 Clone Legend" && o.printed.isToken)
  let selfCopyOk : Bool :=
    tokenClones.size == 2 &&
    tokenClones.all (fun o => !(gSC2.supertypes o).contains .legendary) &&
    gSC2.waitingTriggers.isEmpty

  mustHold17 "5a.gingerOk" gingerOk &&
  mustHold17 "5b.obOk" obOk &&
  mustHold17 "5c.tamiyoOk" tamiyoOk &&
  mustHold17 "5d.windcragOk" windcragOk &&
  mustHold17 "5e.selfCopyOk" selfCopyOk &&
  mustHold17 "5.replay" ([gGinLostMonarch, gGinKeptMonarch, gObLife, gTamRes, gMarduUpkeep, gJeskaiUpkeep, gSC2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 704.5d–e / 707.10 / 707.12 card & permanent spell copy lifecycle, CR 608.2b / 608.3b–c / 303.4a,c Aura resolution, & retargeting.
#guard
  -- 6a. `.uldarosCopies`: exiled card copies have `isToken == false && isCopy == true`, survive `checkSBA` in `.exile` and `.stack`,
  --     permanent card copies resolve onto `.battlefield` with `isToken == true` (CR 608.3f / 707.10f), instant/sorcery copies
  --     cease to exist on resolution, and declining remaining exiled copies sweeps them via CR 704.5e `copiesOutside`!
  let freeInstDef : CardDef := {
    name := "Phase17 Free Bolt"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellEffect := some (Effect.gainLife 3)
  }
  let gUl0 : Game := insertObject (insertObject afterDraw bear me (.graveyard me)) freeInstDef me (.graveyard me)
  let gyBear := ((gUl0.player me).graveyard.filter (fun id => (gUl0.object! id).name == bear.name))[0]!
  let gyInst := ((gUl0.player me).graveyard.filter (fun id => (gUl0.object! id).name == "Phase17 Free Bolt"))[0]!
  let uldEff : Effect := { uldarosTheorix.triggeredAbilities[0]!.effect with targeting := {} }
  let gUl1 : Game := gUl0.applyAbilityEffect me uldEff #[Target.card gyBear, Target.card gyInst]
  let exCopies := gUl1.objects.filter (fun o => o.zone == .exile && o.isCopy)
  let exileCopyStateOk : Bool :=
    exCopies.size == 2 && exCopies.all (fun o => !o.printed.isToken && o.isCopy)
  let bearCopyExId := (exCopies.filter (·.name == bear.name))[0]!.id
  let instCopyExId := (exCopies.filter (·.name == "Phase17 Free Bolt"))[0]!.id
  -- Cast the permanent card copy (`bearCopyExId`), decline the exiled instant copy, and also verify `checkSBA` sweeps
  -- non-token `isCopy` objects outside `.stack`/`.battlefield` (CR 704.5e) while keeping `stackBearCopy` on `.stack`!
  let gUlCastBear : Game := mustApply gUl1 me (.cast bearCopyExId)
  let gUlAfterDecline : Game := mustApply gUlCastBear me .decline
  let strayGyCopyId : ObjectId := ⟨gUlAfterDecline.nextObjectId⟩
  let strayGyCopyObj : GameObject := {
    id := strayGyCopyId
    printed := freeInstDef
    owner := me
    zone := .graveyard me
    timestamp := gUlAfterDecline.timestamp + 1
    isCopy := true
  }
  let gUlWithStrayGyCopy : Game :=
    gUlAfterDecline.record (GameEvent.created gUlAfterDecline.turnNumber me (gUlAfterDecline.snapshot strayGyCopyObj) (cause := testCause))
  let gUlAfterSba : Game := gUlWithStrayGyCopy.checkSBA
  let stackBearCopy := (gUlAfterSba.objects.filter (fun o => o.zone == .stack && o.name == bear.name))[0]!
  let stackAndSweptExileOk : Bool :=
    !stackBearCopy.printed.isToken &&
    stackBearCopy.isCopy &&
    !(gUlAfterSba.objects.any (fun o => o.zone == .exile && o.isCopy)) &&
    (gUlAfterSba.findObject? strayGyCopyId).isNone
  let gUlResolvedBear : Game := gUlAfterSba.resolveTop
  -- Also cast & resolve the instant copy (`instCopyExId`) + SBA check to verify non-permanent card copies cease to exist (CR 707.10a / 704.5e):
  let gUlResolvedInst : Game := (mustApply (mustApply gUl1 me (.cast instCopyExId)) me .decline).resolveTop.checkSBA
  let bfBearCopy := (gUlResolvedBear.permanentsOf me).filter (fun o => o.name == bear.name && o.printed.isToken)
  let bfTokenCopyOk : Bool :=
    bfBearCopy.size == 1 && bfBearCopy[0]!.printed.isToken && !bfBearCopy[0]!.isCopy &&
    (gUlResolvedInst.player me).life == (gUl1.player me).life + 3 &&
    !(gUlResolvedInst.objects.any (fun o => o.isCopy))

  -- 6b. Targeted Aura spell fizzles to graveyard with `removedOnResolution` when target gains hexproof (CR 608.2b / 608.3b),
  --     and *Secret Invasion* (`"Enchant creature you control"`) fizzles if target's controller changes to `opp`!
  let buffAuraDef : CardDef := aura "Phase17 Buff Aura" ManaCost.empty "Enchant creature"
  let gAu0 : Game := insertObject (addPermanent afterDraw bear opp opp) buffAuraDef me (.hand me)
  let oppBearId := (gAu0.battlefield.filter (·.name == bear.name))[0]!.id
  let auHandId := (gAu0.player me).hand.back!
  let gAuCast : Game := mustApply (mustApply gAu0 me (.cast auHandId)) me (.target (.permanent oppBearId))
  let gAuHex : Game := gAuCast.createEffect
    (.layered (.objects #[oppBearId]) (.abilities { keywords := #[Keyword.hexproof] } .none) .untilEndOfTurn)
    (cause := some testCause)
  let preAuRes := gAuHex.events.size
  let gAuFizzled : Game := gAuHex.resolveTop
  let auFizzleSlice := gAuFizzled.events.extract preAuRes gAuFizzled.events.size
  let auraHexproofFizzleOk : Bool :=
    !(gAuFizzled.permanentsOf me).any (·.name == "Phase17 Buff Aura") &&
    (gAuFizzled.player me).graveyard.any (fun id => (gAuFizzled.object! id).name == "Phase17 Buff Aura") &&
    auFizzleSlice.any (fun e => match e.change with | .rules (.stackObject (.removedOnResolution ..)) => true | _ => false)

  let gSI0 : Game := insertObject (addPermanent (addPermanent afterDraw bear me me) hero opp opp) secretInvasionDef17 me (.hand me)
  let myBearSI := (gSI0.battlefield.filter (fun o => o.name == bear.name && o.controller == some me))[0]!.id
  let oppHeroSI := (gSI0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
  let siHandId := (gSI0.player me).hand.back!
  let gSICast0 : Game := mustApply gSI0 me (.cast siHandId)
  let rejectOppCreatureOk : Bool :=
    match gSICast0.apply me (.target (.permanent oppHeroSI)) with
    | .error _ => true
    | .ok _ => false
  let gSICast1 : Game := mustApply gSICast0 me (.target (.permanent myBearSI))
  let gSIStolen : Game := (gSICast1.changeControl (gSICast1.object! myBearSI) opp (cause := some testCause)).resolveTop
  let secretInvasionCtrlOk : Bool :=
    rejectOppCreatureOk &&
    !(gSIStolen.permanentsOf me).any (·.name == secretInvasionDef17.name) &&
    (gSIStolen.player me).graveyard.any (fun id => (gSIStolen.object! id).name == secretInvasionDef17.name)

  -- 6c. Multi-target `setSpellTargetAt` enforces distinct-target constraints (`twoCreaturesOrLandsYouControl`).
  let twoTargetInst : CardDef := {
    name := "Phase17 Dual Rally"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { targeting := .of .twoCreaturesOrLandsYouControl, body := .noop, phrase := "Choose two target creatures and/or lands you control." }
  }
  let gMT0 : Game := insertObject (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) samsonDef17 me me) twoTargetInst me (.hand me)
  let cA := (gMT0.battlefield.filter (·.name == bear.name))[0]!.id
  let cB := (gMT0.battlefield.filter (·.name == hero.name))[0]!.id
  let cC := (gMT0.battlefield.filter (·.name == "Phase17 Doc Samson"))[0]!.id
  let dtHand := (gMT0.player me).hand.back!
  let gMTCast : Game := mustApply (mustApply gMT0 me (.cast dtHand)) me (.targets #[.permanent cA, .permanent cB])
  let spId := gMTCast.stack.back!.objectId
  let gMTDupRejected : Game := gMTCast.setSpellTargetAt spId 1 (.permanent cA)
  let gMTChanged : Game := gMTCast.setSpellTargetAt spId 1 (.permanent cC)
  let retargetDistinctOk : Bool :=
    (gMTDupRejected.stackEntry? spId).map (·.targets) == some #[.permanent cA, .permanent cB] &&
    (gMTChanged.stackEntry? spId).map (·.targets) == some #[.permanent cA, .permanent cC]

  mustHold17 "6a.exileCopyStateOk" exileCopyStateOk &&
  mustHold17 "6a.stackAndSweptExileOk" stackAndSweptExileOk &&
  mustHold17 "6a.bfTokenCopyOk" bfTokenCopyOk &&
  mustHold17 "6b.auraHexproofFizzleOk" auraHexproofFizzleOk &&
  mustHold17 "6b.secretInvasionCtrlOk" secretInvasionCtrlOk &&
  mustHold17 "6c.retargetDistinctOk" retargetDistinctOk &&
  mustHold17 "6.replay" ([gUl1, gUlAfterSba, gUlResolvedBear, gUlResolvedInst, gAuFizzled, gSIStolen, gMTDupRejected, gMTChanged].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 704.3 / 704.5j recursive `keepLegend` `preBf`, CR 610.3 post-departure `linkedExile` batch, CR 303.4f two-pass Aura entry, & *Worlds Within Worlds* batches.
#guard
  -- 7a. Recursive left-nested `.seq` in `keepLegend`: 3 simultaneous SBA actions alongside `chooseLegend` still preserve `preBf` LKI!
  let legWatcherAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger .anotherCreatureOrPlaneswalkerYouControlDies { body := Instruction.gainLifeFixed 4, phrase := "You gain 4 life." }
  let legDef17 : CardDef := { bear with name := "Phase17 Legend", supertypes := #[.legendary] }
  let zeroWatcher17 : CardDef := { creature "Phase17 Zero Watcher" ManaCost.empty #["Spirit"] 0 0 with triggeredAbilities := #[legWatcherAb] }
  let strayAura17 : CardDef := aura "Phase17 Stray Aura" ManaCost.empty "Enchant creature"
  let gLeg0 : Game :=
    addPermanent (addPermanent (addPermanent (addPermanent afterDraw legDef17 me me) legDef17 me me) zeroWatcher17 me me) strayAura17 me me
  let legs := gLeg0.battlefield.filter (·.name == "Phase17 Legend")
  let gyBeforeLeg := (gLeg0.player me).graveyard.size
  let gLegPaused : Game := gLeg0.finishCleanupStepAfterDiscard
  let rec leftNestedDepth? : PendingReplacement → Option Nat
    | .finishSbaSweep .. => some 0
    | .seq a _ => (· + 1) <$> leftNestedDepth? a
    | _ => none
  let nestedSeqPausedOk : Bool :=
    (gLegPaused.pendingReplacement.bind leftNestedDepth?).any (· >= 2)
  let gLegResumed : Game := mustApply gLegPaused me (.keepLegend legs[0]!.id)
  -- `zeroWatcher17` died in stage 0 yet still saw the unkept `Phase17 Legend` die via recursive `findSweepPreBf?`!
  let legNestedSeqOk : Bool :=
    nestedSeqPausedOk &&
    gLegResumed.stack.size == 1 &&
    (gLegResumed.player me).graveyard.size == gyBeforeLeg + 3

  -- 7b. Post-departure `linkedExile` separate batch (CR 610.3): simultaneous board wipe commits departures in batch B1 and `linkedExile` returns in batch B2 (`B1 != B2`)!
  let jailerDef : CardDef := { name := "Phase17 Jailer", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gLink0 : Game := addPermanent (addPermanent afterDraw jailerDef me me) hero me me
  let jailerId := (gLink0.battlefield.filter (·.name == "Phase17 Jailer"))[0]!.id
  let heroWipeId := (gLink0.battlefield.filter (·.name == hero.name))[0]!.id
  let gLink0 : Game := insertObject gLink0 bear opp (.exile)
  let exiledBearId := (gLink0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let gLink1 : Game := gLink0.changeObject jailerId (.pushLinkedExile exiledBearId)
  let preWipeIdx := gLink1.events.size
  let wipeCause : EventCause := .oneShotEffect (some ⟨1701⟩) none (some me)
  let gWiped : Game :=
    gLink1.withBatch (some wipeCause) fun g =>
      let g := g.moveToOwnerGraveyard (g.object! jailerId) "destroyed" (verb := some .destroy) (cause := some wipeCause)
      g.moveToOwnerGraveyard (g.object! heroWipeId) "destroyed" (verb := some .destroy) (cause := some wipeCause)
  let wipeSlice := gWiped.events.extract preWipeIdx gWiped.events.size
  let destroyBatches := wipeSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield (.graveyard _) _ _ _ _)) => e.batch
    | _ => none
  let returnBatches := wipeSlice.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .exile .battlefield _ _ _ _)) => e.batch
    | _ => none
  let linkedExileSeparateBatchOk : Bool :=
    destroyBatches.size == 2 &&
    destroyBatches[0]! == destroyBatches[1]! &&
    returnBatches.size == 1 &&
    returnBatches[0]! != destroyBatches[0]! &&
    (gWiped.permanentsOf opp).any (·.name == bear.name)

  -- 7c. Two-pass simultaneous entry Aura `preBattlefield` check (`placeSearchedBatch`, CR 303.4f):
  --     searching an Aura + creature onto an empty battlefield leaves the Aura in library (cannot attach to co-entering creature),
  --     whereas with an existing creature on `preBf`, both enter in the same batch with the Aura attached to the pre-existing creature!
  let searchAuraDef : CardDef := aura "Phase17 Search Aura" ManaCost.empty "Enchant creature"
  let gSrchEmpty0 : Game := insertObject (insertObject afterDraw bear me (.library me)) searchAuraDef me (.library me)
  let libE := (gSrchEmpty0.player me).library
  let srchAuraE := libE.back!
  let srchBearE := libE[libE.size - 2]!
  let gSrchEmpty1 : Game := gSrchEmpty0.placeSearchedBatch me #[srchBearE, srchAuraE] false (cause := some testCause)
  let emptyPreBfAuraStaysOk : Bool :=
    (gSrchEmpty1.permanentsOf me).any (·.name == bear.name) &&
    !(gSrchEmpty1.permanentsOf me).any (·.name == "Phase17 Search Aura") &&
    (gSrchEmpty1.object! srchAuraE).zone == .library me

  let gSrchHost0 : Game := insertObject (insertObject (addPermanent afterDraw hero me me) bear me (.library me)) searchAuraDef me (.library me)
  let preHostId := (gSrchHost0.battlefield.filter (·.name == hero.name))[0]!.id
  let libH := (gSrchHost0.player me).library
  let srchAuraH := libH.back!
  let srchBearH := libH[libH.size - 2]!
  let preSrchIdx := gSrchHost0.events.size
  let gSrchHost1 : Game := gSrchHost0.placeSearchedBatch me #[srchBearH, srchAuraH] false (cause := some testCause)
  let srchBatches := (gSrchHost1.events.extract preSrchIdx gSrchHost1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) .battlefield _ _ _ _)) => e.batch
    | _ => none
  let enteredSearchAura := (gSrchHost1.permanentsOf me).filter (·.name == "Phase17 Search Aura")
  let hostPreBfAuraAttachesOk : Bool :=
    srchBatches.size == 2 && srchBatches[0]! == srchBatches[1]! &&
    enteredSearchAura.size == 1 && enteredSearchAura[0]!.attachedTo == some preHostId

  -- 7d. *Worlds Within Worlds* (`worldsDef17`): creatures from hand, exiled cards to hand, and exiling the spell commit in 3 distinct batches!
  let gWWW0 : Game := insertObject (insertObject (addPermanent afterDraw bear me me) hero me (.hand me)) worldsDef17 me (.hand me)
  let wwwHand := (gWWW0.player me).hand.back!
  let heroInHand := ((gWWW0.player me).hand.filter (fun id => (gWWW0.object! id).name == hero.name))[0]!
  let gWWWCast : Game := mustApply gWWW0 me (.cast wwwHand)
  let preWWWRes := gWWWCast.events.size
  let gWWWPrmpt : Game := gWWWCast.resolveTop
  let gWWWDone : Game :=
    match gWWWPrmpt.pending with
    | .fraChoice p (.worldsPutCreatures _ _ _ _ _) => mustApply gWWWPrmpt p (.choosePermanents #[heroInHand])
    | _ => gWWWPrmpt
  let wwwSlice := gWWWDone.events.extract preWWWRes gWWWDone.events.size
  let bPutHandToBf := wwwSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ (.hand _) .battlefield ..)) => e.batch | _ => none
  let bExileToHand := wwwSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ .exile (.hand _) ..)) => e.batch | _ => none
  let bSpellToExile := wwwSlice.findSome? fun e =>
    match e.change with | .rules (.zone (.moved _ _ .stack .exile ..)) => e.batch | _ => none
  let wwwThreeBatchesOk : Bool :=
    bPutHandToBf.isSome && bExileToHand.isSome && bSpellToExile.isSome &&
    bPutHandToBf != bExileToHand && bExileToHand != bSpellToExile && bPutHandToBf != bSpellToExile &&
    gWWWDone.objects.any (fun o => o.name == worldsDef17.name && o.zone == .exile)

  mustHold17 "7a.legNestedSeqOk" legNestedSeqOk &&
  mustHold17 "7b.linkedExileSeparateBatchOk" linkedExileSeparateBatchOk &&
  mustHold17 "7c.emptyPreBfAuraStaysOk" emptyPreBfAuraStaysOk &&
  mustHold17 "7c.hostPreBfAuraAttachesOk" hostPreBfAuraAttachesOk &&
  mustHold17 "7d.wwwThreeBatchesOk" wwwThreeBatchesOk &&
  mustHold17 "7.replay" ([gLegPaused, gLegResumed, gWiped, gSrchEmpty1, gSrchHost1, gWWWDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 800.4 `mayThen` departure decline & pregame concessions, silent cleanup `beginTurn`, and step/phase `EffectDuration` expiry.
#guard
  let leylinesDef : CardDef := {
    name := "Phase17 Leyline"
    manaCost := ManaCost.ofGeneric 4
    types := #[.enchantment]
    anyNumberInDeck := true
    staticAbilities := #[.mayBeginOnBattlefield]
  }
  let leylineDeck : Array CardDef := Array.replicate 60 leylinesDef
  let threePregameCfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := leylineDeck },
      { name := "Nissa", deck := leylineDeck },
      { name := "Liliana", deck := testGreenDeck }
    ]
    format := .constructed
    seed := 17
    startingPlayer := some 0
  }
  let gPre0 : Game :=
    match Start.start threePregameCfg with
    | .ok g => g
    | .error e => panic! e
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  -- 8a1. `p0` concedes during `declareMulligan` -> `p1` and `p2` keep, `p1` gets `.mayBeginOnBattlefield`, and Turn 1 starts with `activePlayer == p1`!
  let gPre1 : Game := gPre0.concede p0
  let gPre2 : Game := keepOpeningHands gPre1 20
  let gPre3 : Game :=
    Id.run do
      let mut g := gPre2
      let mut fuel := 25
      while fuel > 0 do
        fuel := fuel - 1
        match g.pending with
        | .fraChoice q (.mayBeginOnBattlefield _) => g := mustApply g q .accept
        | _ => fuel := 0
      return g
  let pregameConcedeMulliganOk : Bool :=
    (gPre3.player p0).leftTheGame &&
    gPre3.activePlayer == p1 &&
    gPre3.turnNumber == 1 &&
    (gPre3.permanentsOf p1).any (·.name == "Phase17 Leyline")

  -- 8a2. `p0` keeps through mulligans so `.mayBeginOnBattlefield` opens for `p0`, THEN `p0` concedes during `.mayBeginOnBattlefield`!
  let gPreB0 : Game := keepOpeningHands gPre0 20
  let p0PromptedBeginOk : Bool :=
    match gPreB0.pending with
    | .fraChoice q (.mayBeginOnBattlefield _) => q == p0
    | _ => false
  let gPreB1 : Game := gPreB0.concede p0
  let gPreB2 : Game :=
    Id.run do
      let mut g := gPreB1
      let mut fuel := 25
      while fuel > 0 do
        fuel := fuel - 1
        match g.pending with
        | .fraChoice q (.mayBeginOnBattlefield _) => g := mustApply g q .decline
        | _ => fuel := 0
      return g
  let pregameConcedeBeginOk : Bool :=
    p0PromptedBeginOk &&
    gPreB2.pending == .none &&
    gPreB2.activePlayer == p1 &&
    gPreB2.turnNumber == 1

  -- 8a3. `mayThen` departure decline (CR 800.4f): `p2` conceding on `Pending.mayPayGeneric p2 ...` inside a sequence
  --      declines `"If you do"` (so `p1` does NOT lose 5 life)!
  let maySeq : TriggeredAbility.TriggerResolution :=
    .sequence [
      .may (.pay (CostSpec.ofGeneric 1)) (.loseLife (.fixed 5) .eachOpponent) .ifYouDo,
      .gainLife (.fixed 2) ]
  let gMay0 : Game := (addPermanent gPreB2 bear p1 p1).addMana p2 .colorless 1 (cause := some testCause)
  let bP1 := (gMay0.battlefield.filter (fun o => o.name == bear.name && o.controller == some p1))[0]!.id
  let gMaySt : Game := gMay0.putTriggeredAbilityOnStack p2 (gMay0.object! bP1) (.onEnterDraw 1) "enters"
    (eventCause := some testCause) (reflexiveResolution := some maySeq)
  let gMayPrompt : Game := gMaySt.resolveTop
  let p1LifeBefore := (gMayPrompt.player p1).life
  let gMayConceded : Game := gMayPrompt.concede p2
  let mayLeaveDeclinedOk : Bool := (gMayConceded.player p1).life == p1LifeBefore

  -- 8b. Silent cleanup `finishPostSbaCleanup false` routes through `beginTurn` and expires `.untilNextTurnOf opp`!
  let gProt0 : Game := (afterDraw.createEffect (.protectionFromEverything opp) (cause := some testCause)).createEffect
    (.lifeCantChange opp) (cause := some testCause)
  let protBeforeOk : Bool :=
    gProt0.activeEffects.any (fun (_, e) => match e with | .playerRule q .protectionFromEverything (.untilNextTurnOf _) => q == opp | _ => false)
  let gProtNextTurn : Game := gProt0.finishPostSbaCleanup false
  let silentCleanupExpiredOk : Bool :=
    protBeforeOk &&
    gProtNextTurn.activePlayer == opp &&
    !gProtNextTurn.activeEffects.any (fun (_, e) =>
      match e with
      | .playerRule _ .protectionFromEverything _ | .playerRule _ .lifeCantChange _ => true
      | _ => false) &&
    gProtNextTurn.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.continuousEffect (.expired ..)), some (.turnBased .expireAtStepBegin) => true
      | _, _ => false)

  -- 8c. Step/phase `EffectDuration` expiry (`CR 500.4–5 / 511.2 / 611.2a`):
  let gDur0 : Game := addPermanent afterDraw bear me me
  let dBear := (gDur0.battlefield.filter (·.name == bear.name))[0]!.id
  let eUpkeepEnd : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 1 1) (.untilEndOfStepOrPhase (.step .upkeep))
  let eMainBegin : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 2 2) (.untilStepOrPhase (.phase .precombatMain))
  let eEndCombat : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 3 3) (.untilEndOfCombat)
  let eNextTurnEnd : ContinuousEffectSpec := .layered (.objects #[dBear]) (.ptModify 4 4) (.untilEndOfNextTurnOf me)
  let gDur1 : Game := (((gDur0.createEffect eUpkeepEnd (cause := some testCause)).createEffect
    eMainBegin (cause := some testCause)).createEffect
    eEndCombat (cause := some testCause)).createEffect
    eNextTurnEnd (cause := some testCause)
  let pStart := gDur1.power (gDur1.object! dBear) -- 2 + 1 + 2 + 3 + 4 = 12
  let gDur2 : Game := gDur1.recordStepEnded .upkeep
  let pAfterUpkeepEnd := gDur2.power (gDur2.object! dBear) -- 11
  let gDur3 : Game := gDur2.recordPhaseBegan .precombatMain
  let pAfterMainBegin := gDur3.power (gDur3.object! dBear) -- 9
  let gDur4 : Game := gDur3.recordPhaseEnded .combat
  let pAfterCombatEnd := gDur4.power (gDur4.object! dBear) -- 6 (2 + 4)
  -- `clearEOT` on THIS turn does NOT expire `.untilEndOfNextTurnOf me` (`hasTurnBegunSince` is false),
  -- then after `turnBegan` for `me`, `clearEOT` DOES expire `.untilEndOfNextTurnOf me`!
  let gDur5 : Game := gDur4.clearEOT
  let pAfterThisEot := gDur5.power (gDur5.object! dBear) -- still 6!
  let gDur6 : Game := (gDur5.record (GameEvent.turnBegan (gDur5.turnNumber + 1) me)).clearEOT
  let pAfterNextTurnEot := gDur6.power (gDur6.object! dBear) -- back to 2!
  let durationsOk : Bool :=
    pStart == 12 &&
    pAfterUpkeepEnd == 11 &&
    pAfterMainBegin == 9 &&
    pAfterCombatEnd == 6 &&
    pAfterThisEot == 6 &&
    pAfterNextTurnEot == 2

  mustHold17 "8a1.pregameConcedeMulliganOk" pregameConcedeMulliganOk &&
  mustHold17 "8a2.pregameConcedeBeginOk" pregameConcedeBeginOk &&
  mustHold17 "8a3.mayLeaveDeclinedOk" mayLeaveDeclinedOk &&
  mustHold17 "8b.silentCleanupExpiredOk" silentCleanupExpiredOk &&
  mustHold17 "8c.durationsOk" durationsOk &&
  mustHold17 "8.replay" ([gPre3, gPreB2, gMayConceded, gProtNextTurn, gDur2, gDur3, gDur4, gDur5, gDur6].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 9. PR #602 review regression guards:
--    (a) Post-choice return logs in `runLinkedExileBatch`, `returnLinkedExileLoop`, and `finishWorldsWithinWorldsTail`.
--    (b) `tricksterLibrary` concession by `caster` clears the prompt and leaves the creature on `.battlefield` (CR 800.4a/g/h).
--    (c) `commitEnteringAttackItems` (`applyPut` `.revealed`) checks entering Auras against `preBattlefield` (CR 303.4f).
#guard
  -- 9a1. `runLinkedExileBatch` & `returnLinkedExileLoop` with competing `.exileInsteadOfGraveyard` replacements:
  --      neither logs `"returns to ...'s graveyard"` while paused OR when redirected to `.exile`,
  --      and BOTH log `"returns to ...'s graveyard"` post-choice when the graveyard move actually succeeds!
  let gLnk0 : Game := insertObject (insertObject (addPermanent afterDraw hero opp opp) bear me .exile) bear me .exile
  let oppSrc := (gLnk0.battlefield.filter (fun o => o.name == hero.name && o.controller == some opp))[0]!.id
  let exBearIds := (gLnk0.objects.filter (fun o => o.name == bear.name && o.zone == .exile)).map (·.id)
  let exGy1 := exBearIds[0]!
  let exGy2 := exBearIds[1]!
  let gLnk1 : Game := (gLnk0.changeObject exGy1 (.returnToZone (some (.graveyard me)))).changeObject
    exGy2 (.returnToZone (some (.graveyard me)))
  let idRep1A : ReplacementId := { kind := .finalityCounterExile, object := some exGy1 }
  let idRep1B : ReplacementId := { kind := .exileOppDeath, object := some exGy1 }
  let idRep2A : ReplacementId := { kind := .finalityCounterExile, object := some exGy2 }
  let idRep2B : ReplacementId := { kind := .exileOppDeath, object := some exGy2 }
  let gLnkRedir : Game := ((gLnk1.createEffect
    (.replacement { id := idRep1A, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy1) false })
    (cause := some testCause)).createEffect
    (.replacement { id := idRep1B, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy1) false })
    (cause := some testCause))
  let logBeforeBatch := gLnkRedir.log.size
  let gBatchPaused : Game := gLnkRedir.returnLinkedExileMoves #[exGy1]
  let gBatchRedirDone : Game := mustApply gBatchPaused me (.chooseReplacement idRep1A)
  let batchNoPrematureOrFalseLogOk : Bool :=
    !(gBatchPaused.log.extract logBeforeBatch gBatchPaused.log.size).any (·.contains "returns to") &&
    !(gBatchRedirDone.log.extract logBeforeBatch gBatchRedirDone.log.size).any (·.contains "returns to") &&
    (gBatchRedirDone.followMovedToZone? exGy1 (· == .exile)).isSome

  -- Scope the two competing replacements on `exGy2` to `oppSrc` so removing `oppSrc` while paused lets the resumed move enter `.graveyard me`!
  let gLnkLoop0 : Game := ((gLnk1.createEffect
    (.replacement { id := idRep2A, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy2) false }
      (.whileSourceOnBattlefield oppSrc))
    (cause := some testCause)).createEffect
    (.replacement { id := idRep2B, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some exGy2) false }
      (.whileSourceOnBattlefield oppSrc))
    (cause := some testCause))
  let logBeforeLoop := gLnkLoop0.log.size
  let gLoopPaused : Game := gLnkLoop0.withBatch none fun g => g.returnLinkedExileLoop #[exGy2]
  let loopPausedNoLogOk : Bool :=
    !(gLoopPaused.log.extract logBeforeLoop gLoopPaused.log.size).any (·.contains "returns to")
  let gLoopSrcGone : Game := gLoopPaused.expireWhileSourceEffects oppSrc
  let gLoopGyDone : Game := mustApply gLoopSrcGone me (.chooseReplacement idRep2A)
  let loopPostChoiceGyLogsOk : Bool :=
    loopPausedNoLogOk &&
    (gLoopGyDone.followMovedToZone? exGy2 (· == .graveyard me)).isSome &&
    (gLoopGyDone.log.extract logBeforeLoop gLoopGyDone.log.size).any (fun s =>
      s.contains "returns to " && s.contains "'s graveyard")

  -- 9a2. Hand return across an active `Pending.chooseReplacement` in `runLinkedExileBatch`, `returnLinkedExileLoop`, and `finishWorldsWithinWorldsTail`:
  let gHand0 : Game := insertObject (insertObject gLnkRedir hero me .exile) bear me .exile
  let exHeroHand := (gHand0.objects.filter (fun o => o.name == hero.name && o.zone == .exile))[0]!.id
  let exWWWHand := (gHand0.objects.filter (fun o => o.name == bear.name && o.zone == .exile)).back!.id
  let gHand1 : Game := gHand0.changeObject exHeroHand (.returnToZone (some (.hand me)))
  let gDummyPause : Game := gHand1.returnLinkedExileMoves #[exGy1]
  -- Chain `worldsReturnExiledLoop` behind `gDummyPause`'s `Pending.chooseReplacement`:
  let logBeforeWWW := gDummyPause.log.size
  let gWWWPaused : Game := gDummyPause.worldsReturnExiledLoop #[exWWWHand] none
  let wwwNoEarlyLogOk : Bool :=
    !(gWWWPaused.log.extract logBeforeWWW gWWWPaused.log.size).any (·.contains "returned to its owner's hand")
  let gWWWResumed : Game := mustApply gWWWPaused me (.chooseReplacement idRep1A)
  let wwwPostChoiceLogOk : Bool :=
    wwwNoEarlyLogOk &&
    (gWWWResumed.followMovedToZone? exWWWHand (· == .hand me)).isSome &&
    (gWWWResumed.log.extract logBeforeWWW gWWWResumed.log.size).any (·.contains "is returned to its owner's hand")

  let logBeforeLoopHand := gHand1.log.size
  let gLoopHandPaused : Game := gHand1.withBatch none fun g =>
    g.returnLinkedExileLoop #[exGy1, exHeroHand]
  let loopHandNoEarlyLogOk : Bool :=
    !(gLoopHandPaused.log.extract logBeforeLoopHand gLoopHandPaused.log.size).any (·.contains "returns to")
  let gLoopHandResumed : Game := mustApply gLoopHandPaused me (.chooseReplacement idRep1A)
  let loopHandPostChoiceOk : Bool :=
    loopHandNoEarlyLogOk &&
    (gLoopHandResumed.followMovedToZone? exHeroHand (· == .hand me)).isSome &&
    (gLoopHandResumed.log.extract logBeforeLoopHand gLoopHandResumed.log.size).any (·.contains s!"{hero.name} returns to {(gLoopHandResumed.player me).name}'s hand")

  -- 9b. `tricksterLibrary`: `caster` conceding while `q` is choosing clears `pending` and leaves `q`'s creature on `.battlefield`!
  let threeCfg9 : StartConfig := {
    seats := #[
      { name := "Caster", deck := testGreenDeck },
      { name := "Owner", deck := testGreenDeck },
      { name := "Third", deck := testGreenDeck }
    ]
    format := .constructed
    seed := 19
    startingPlayer := some 0
  }
  let gTr0 : Game :=
    match Start.start threeCfg9 with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let trCaster : PlayerId := ⟨0⟩
  let trOwner : PlayerId := ⟨1⟩
  let gTr1 : Game := addPermanent gTr0 bear trOwner trOwner
  let trBear := (gTr1.battlefield.filter (fun o => o.name == bear.name && o.owner == trOwner))[0]!.id
  let gTrPrompt : Game := gTr1.change (.pending (.fraChoice trOwner (.tricksterLibrary trCaster trBear none)))
  let gTrConceded : Game := gTrPrompt.concede trCaster
  let gTrNoopHelper : Game := gTrConceded.applyOwnerPutsLibraryThenConnive trCaster #[Target.permanent trBear]
  let tricksterCasterLeaveOk : Bool :=
    (gTrConceded.player trCaster).leftTheGame &&
    gTrConceded.pending == .none &&
    (gTrConceded.findObject? trBear).any (·.isOnBattlefield) &&
    !(gTrConceded.player trOwner).library.contains trBear &&
    (gTrNoopHelper.findObject? trBear).any (·.isOnBattlefield)

  -- 9c. `commitEnteringAttackItems` (`applyPut` `.revealed`): Aura checks `preBattlefield` per CR 303.4f!
  let revAuraDef : CardDef := aura "Phase17 Revealed Aura" ManaCost.empty "Enchant creature"
  -- 9c1. Empty `preBf`: revealed `[bear, revAuraDef]` leaves `revAuraDef` in `.library me` (does not enter unattached & die)!
  let gRevE0 : Game := insertObject (insertObject afterDraw bear me (.library me)) revAuraDef me (.library me)
  let libRevE := (gRevE0.player me).library
  let revAuraE := libRevE.back!
  let revBearE := libRevE[libRevE.size - 2]!
  let gRevE1 : Game := (gRevE0.change (.pushContinuationFrame { revealedIdsThisWay := #[revBearE, revAuraE] })).applyPut
    me (.onEnterDraw 0) none #[] .revealed .asPrinted .none
  let revEmptyAuraStaysOk : Bool :=
    (gRevE1.permanentsOf me).any (·.name == bear.name) &&
    !(gRevE1.permanentsOf me).any (·.name == "Phase17 Revealed Aura") &&
    (gRevE1.object! revAuraE).zone == .library me &&
    !(gRevE1.player me).graveyard.any (fun id => (gRevE1.object! id).name == "Phase17 Revealed Aura")

  -- 9c2. Non-empty `preBf` with `hero`: revealed `[bear, revAuraDef]` attaches `revAuraDef` to `hero` in the same batch!
  let gRevH0 : Game := insertObject (insertObject (addPermanent afterDraw hero me me) bear me (.library me)) revAuraDef me (.library me)
  let preHeroId := (gRevH0.battlefield.filter (·.name == hero.name))[0]!.id
  let libRevH := (gRevH0.player me).library
  let revAuraH := libRevH.back!
  let revBearH := libRevH[libRevH.size - 2]!
  let preRevHIdx := gRevH0.events.size
  let gRevH1 : Game := (gRevH0.change (.pushContinuationFrame { revealedIdsThisWay := #[revBearH, revAuraH] })).applyPut
    me (.onEnterDraw 0) none #[] .revealed .asPrinted .none
  let revHBatches := (gRevH1.events.extract preRevHIdx gRevH1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.library _) .battlefield _ _ _ _)) => e.batch
    | _ => none
  let enteredRevAura := (gRevH1.permanentsOf me).filter (·.name == "Phase17 Revealed Aura")
  let revHostAuraAttachesOk : Bool :=
    revHBatches.size == 2 && revHBatches[0]! == revHBatches[1]! &&
    enteredRevAura.size == 1 && enteredRevAura[0]!.attachedTo == some preHeroId

  -- 9c3. Paused `commitEnteringAttackItems` on empty `preBf`: co-entering `asEntersChooseOddEven` creature pausing first still keeps `preBf` empty for the Aura!
  let oddCreature9 : CardDef := { bear with name := "Phase17 Odd Striker", staticAbilities := #[.asEntersChooseOddEven] }
  let gPauseEnt0 : Game := insertObject (insertObject afterDraw oddCreature9 me (.hand me)) revAuraDef me (.hand me)
  let hPause := (gPauseEnt0.player me).hand
  let pauseAura := hPause.back!
  let pauseOdd := hPause[hPause.size - 2]!
  let itemOdd : EnteringAttackItem := .card pauseOdd me me false false #[] [] .putOntoBattlefield #[]
  let itemAura : EnteringAttackItem := .card pauseAura me me false false #[] [] .putOntoBattlefield #[]
  let gPauseEnt1 : Game := gPauseEnt0.commitEnteringAttackItems #[(itemOdd, none), (itemAura, none)] (cause := some testCause)
  let gPauseEntDone : Game := mustApply gPauseEnt1 me (.chooseMode 0)
  let pausedPreBfPreservedOk : Bool :=
    gPauseEntDone.pending == .none &&
    (gPauseEntDone.permanentsOf me).any (·.name == "Phase17 Odd Striker") &&
    !(gPauseEntDone.permanentsOf me).any (·.name == "Phase17 Revealed Aura") &&
    (gPauseEntDone.object! pauseAura).zone == .hand me

  mustHold17 "9a1.batchNoPrematureOrFalseLogOk" batchNoPrematureOrFalseLogOk &&
  mustHold17 "9a1.loopPostChoiceGyLogsOk" loopPostChoiceGyLogsOk &&
  mustHold17 "9a2.wwwPostChoiceLogOk" wwwPostChoiceLogOk &&
  mustHold17 "9a2.loopHandPostChoiceOk" loopHandPostChoiceOk &&
  mustHold17 "9b.tricksterCasterLeaveOk" tricksterCasterLeaveOk &&
  mustHold17 "9c1.revEmptyAuraStaysOk" revEmptyAuraStaysOk &&
  mustHold17 "9c2.revHostAuraAttachesOk" revHostAuraAttachesOk &&
  mustHold17 "9c3.pausedPreBfPreservedOk" pausedPreBfPreservedOk &&
  mustHold17 "9.replay" ([gBatchPaused, gBatchRedirDone, gLoopPaused, gLoopGyDone, gWWWPaused, gWWWResumed,
      gLoopHandPaused, gLoopHandResumed, gTrConceded, gRevE1, gRevH1, gPauseEnt1, gPauseEntDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase17EventAlignment

/-! ### Phase 18 Event Alignment Isolation Tests (CR 111.8 / 115.3 / 115.7d / 303.4f–g / 500.4 / 506.5 / 509.1g / 514.2 / 603.2d / 603.3c–d / 603.4 / 603.12 / 608.2b,h / 610.3 / 611.2a–b / 614.12 / 700.2 / 701.54 / 702.26b,d,f / 707.2 / 707.10c / 723.5 / 725.4 / 733.1 / 800.4)

1. Nested-batch `currentBatch` cause isolation, 0-event pause replay parity, and single-writer `PermanentEvent.designation _ .ringBearer false` on zone departure & `ceasedToExist`.
2. `outerPendingReplacements` / `endsWithPriorityGrant` priority deferral, `runLinkedExileBatch` Pass 2, `shuffleSourceIntoLibrary` replacement pause-safety, and reflexive-sacrifice pause-safety.
3. CR 733.1 `.crew` & `.zemoBoastExile` proposal reversal / `.costAction` batching, and `reverseToProposalCheckpoint?` scaffolding, interleaved-engine batch grouping, `.lookedAt` filtering, & `queuedLinkedExile` flush.
4. CR 603.2d / 603.3c–d sequential multi-copy modal trigger announcement, mandatory `count`-mode removal (`noLegalMode`), `tapOrUntapNonland` & `hawkeyeModes` stack-placement announcement, and `combineTriggerModes` `allowsZeroTargets` / `maxTargets`.
5. CR 506.5 `attacksAlonePlus2Indestructible` declared-attacker check, CR 603.4 / 608.2h `evalTriggerCond` LKI fallback, CR 702.26b `attachedEquipmentAtResolution` phased-out `0`, and CR 707.2 `.copySelfNonlegendary` `eo.copiable`.
6. CR 707.10c / 115.3 / 115.7d `.copyCauseSpell` & `.venserSpell` retargeting, cross-slot `[A, B] -> [B, A]` swaps (`.twoPlayers` & `.twoNonlandsSharingType` revert), and CR 608.2b multi-target per-slot legality.
7. CR 303.4f–g / 111.8 Aura entry & token-copy non-return, pre-batch host snapshots, and two-pass `createPermanentCopyTokens` simultaneous batching.
8. CR 800.4 / 725.4 / 509.1g / 723.5 multiplayer combat-damage departure safety, empty `defendingPlayers` blocker-skip, monarch succession, third-party leave prompt revalidation, blocker-retention, and `playerControl`.
9. CR 500.4 `beginTurn` turn-start expiry, CR 611.2a–b / 702.26f `durationActive` & counter/zone expiry, CR 800.4c,i,m phased-out control-expiry exile & departed-player `PlayerRule` / `.untilEndOfNextTurnOf` expiry, and CR 614.12 Arwen `preBfOk`. -/
section Phase18EventAlignment

private def opp18 : PlayerId := ⟨1⟩

private def mustHold18 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 18 guard failed: {label}"

private def mkThreePlayer18 (seed : UInt64 := 18) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 20).advanceStep
  | .error e => panic! e

-- 1. Nested-batch `currentBatch` cause isolation, 0-event pause replay parity, & single-writer `.ringBearer` clear.
#guard
  -- 1a. Outer `withBatch none` wrapping inner `withBatch (some innerCause)` restores `none` after inner batch finishes!
  let g0 : Game := addPermanent (addPermanent afterDraw bear me me) hero me me
  let bId := (g0.battlefield.filter (·.name == bear.name))[0]!.id
  let hId := (g0.battlefield.filter (·.name == hero.name))[0]!.id
  let innerCause : EventCause := .oneShotEffect (some ⟨77⟩) (some bId) (some me)
  let fallbackCause : EventCause := .oneShotEffect (some ⟨88⟩) (some hId) (some me)
  let preIdx := g0.events.size
  let gIso : Game :=
    g0.withBatch none fun g =>
      let g := g.withBatch (some innerCause) fun g =>
        g.becomeTapped (g.object! bId)
      g.becomeTapped (g.object! hId) (cause := some fallbackCause)
  let tappedCauses := (gIso.events.extract preIdx gIso.events.size).filterMap fun e =>
    match e.change with
    | .rules (.permanent (.tapped eo _)) => eo.id.map (·, e.cause?)
    | _ => none
  let nestedCauseIsoOk : Bool :=
    tappedCauses == #[(bId, some innerCause), (hId, some fallbackCause)] &&
    gIso.currentBatch.isNone

  -- 1b. 0-event pause replay parity (`withBatch` pausing on `chooseReplacement` before recording any `RulesEvent`):
  let idDrawA : ReplacementId := { kind := .drawTwoExceptFirstDrawStep, object := some bId }
  let idDrawB : ReplacementId := { kind := .drawThreeExceptFirstDrawStep, object := some hId }
  let gDr0 : Game :=
    (g0.createEffect
      (.replacement { id := idDrawA, source := some bId, controller := some me, affectedPlayer := me,
                      kind := .replaceDraw me 2 false }) (cause := some testCause)).createEffect
      (.replacement { id := idDrawB, source := some hId, controller := some me, affectedPlayer := me,
                      kind := .replaceDraw me 3 false }) (cause := some testCause)
  let preZeroIdx := gDr0.events.size
  let gZeroPaused : Game :=
    gDr0.withBatch (some testCause) fun g =>
      g.draw me 1 (cause := some testCause)
  let zeroRulesInSlice :=
    !(gZeroPaused.events.extract preZeroIdx gZeroPaused.events.size).any (fun e =>
      match e.change with | .rules _ => true | _ => false)
  let zeroPauseOk : Bool :=
    zeroRulesInSlice &&
    gZeroPaused.currentBatch.isSome &&
    (match gZeroPaused.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    Game.replayEvents gZeroPaused.events == gZeroPaused
  let gZeroResumed : Game :=
    let g1 := mustApply gZeroPaused me (.chooseReplacement idDrawA)
    match g1.pending with
    | .chooseReplacement _ cs => mustApply g1 me (.chooseReplacement cs[0]!)
    | _ => g1
  let zeroResumedOk : Bool :=
    gZeroResumed.pending == .none &&
    gZeroResumed.currentBatch.isNone

  -- 1c. Single-writer `PermanentEvent.designation _ .ringBearer false` on zone departure & token `ceasedToExist`:
  let gRb0 : Game := g0.setRingBearer me (some bId) (cause := some testCause)
  let rbPreMoveIdx := gRb0.events.size
  let (gRbMoved, _) := gRb0.move bId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let rbClearCountMove := (gRbMoved.events.extract rbPreMoveIdx gRbMoved.events.size).filter (fun e =>
    match e.change with
    | .rules (.permanent (.designation eo .ringBearer false)) => eo.id == some bId
    | _ => false) |>.size
  let gTok0 : Game := (g0.createToken me bear (cause := some testCause)).1
  let tokId := (gTok0.battlefield.filter (·.printed.isToken))[0]!.id
  let gTokRb : Game := gTok0.setRingBearer me (some tokId) (cause := some testCause)
  let tokPreCeaseIdx := gTokRb.events.size
  let gTokCeased : Game := gTokRb.ceaseToExist tokId (cause := some (.stateBased .tokenOutsideBattlefield))
  let rbClearCountCease := (gTokCeased.events.extract tokPreCeaseIdx gTokCeased.events.size).filter (fun e =>
    match e.change with
    | .rules (.permanent (.designation eo .ringBearer false)) => eo.id == some tokId
    | _ => false) |>.size
  let ringBearerSingleWriterOk : Bool :=
    rbClearCountMove == 1 && (gRbMoved.player me).ringBearerId.isNone &&
    rbClearCountCease == 1 && (gTokCeased.player me).ringBearerId.isNone

  mustHold18 "1a.nestedCauseIsoOk" nestedCauseIsoOk &&
  mustHold18 "1b.zeroPauseOk" zeroPauseOk &&
  mustHold18 "1b.zeroResumedOk" zeroResumedOk &&
  mustHold18 "1c.ringBearerSingleWriterOk" ringBearerSingleWriterOk &&
  mustHold18 "1.replay" ([gIso, gZeroPaused, gZeroResumed, gRbMoved, gTokCeased].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. `outerPendingReplacements` / `endsWithPriorityGrant`, `runLinkedExileBatch` Pass 2, `shuffleSourceIntoLibrary`, & reflexive-sacrifice pause-safety.
#guard
  -- 2a. `outerPendingReplacements` with `endsWithPriorityGrant`: inner `finishAndGrantPriority` defers priority grant!
  let gOut0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).change
      (.continuation (.pushOuterPendingReplacement (.receivePriority opp18)))
  let idCnt1 : ReplacementId := { kind := .extraCounterOnPermanents, object := some ⟨500⟩, counterKind := some .plusOnePlusOne }
  let idCnt2 : ReplacementId := { kind := .multiplyCountersPut, object := some ⟨501⟩ }
  let gOutB : Game := addPermanent gOut0 bear me me
  let outBear := (gOutB.battlefield.filter (·.name == bear.name))[0]!.id
  let gOutB : Game :=
    (gOutB.createEffect (.replacement { id := idCnt1, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1 }) (cause := some testCause)).createEffect
      (.replacement { id := idCnt2, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 0 3 }) (cause := some testCause)
  let gOutPaused : Game :=
    (gOutB.addPlusOnePlusOneTo (gOutB.object! outBear) 1 (cause := some testCause)).finishAndGrantPriority me
  let endsCheckOk : Bool :=
    PendingReplacement.endsWithPriorityGrant (.receivePriority opp18) &&
    PendingReplacement.endsWithPriorityGrant .finishFraChoice &&
    PendingReplacement.endsWithPriorityGrant (.seq (.gainLife me 1 none) (.receivePriority me)) &&
    !PendingReplacement.endsWithPriorityGrant (.gainLife me 1 none)
  let gOutDone : Game :=
    let g1 := mustApply gOutPaused me (.chooseReplacement idCnt1)
    match g1.pending with
    | .chooseReplacement _ cs => mustApply g1 me (.chooseReplacement cs[0]!)
    | _ => g1
  -- Non-granting oldest outer frame (`[0] = .gainLife`) + priority-granting newer outer frame (`[1]`) or inner `pendingReplacement`:
  -- `finishAndGrantPriority` must still see the existing priority grant and not append a duplicate `.receivePriority`.
  let gNewerOuter0 : Game :=
    ((afterDraw.change (.pushContinuationFrame {})).change
      (.continuation (.pushOuterPendingReplacement (.gainLife me 1 (some testCause))))).change
      (.continuation (.pushOuterPendingReplacement (.receivePriority opp18)))
  let gNewerOuterB : Game := addPermanent gNewerOuter0 bear me me
  let newerBear := (gNewerOuterB.battlefield.filter (·.name == bear.name))[0]!.id
  let gNewerOuterB : Game :=
    (gNewerOuterB.createEffect (.replacement { id := idCnt1, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1 }) (cause := some testCause)).createEffect
      (.replacement { id := idCnt2, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 0 3 }) (cause := some testCause)
  let gNewerOuterPaused : Game :=
    (gNewerOuterB.addPlusOnePlusOneTo (gNewerOuterB.object! newerBear) 1 (cause := some testCause)).finishAndGrantPriority me
  let newerPausedNoDup : Bool :=
    !gNewerOuterPaused.pendingReplacement.any PendingReplacement.endsWithPriorityGrant
  let gNewerOuterDone : Game :=
    let g1 := mustApply gNewerOuterPaused me (.chooseReplacement idCnt1)
    match g1.pending with
    | .chooseReplacement _ cs => mustApply g1 me (.chooseReplacement cs[0]!)
    | _ => g1
  let gInnerGrants0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).change
      (.continuation (.pushOuterPendingReplacement (.gainLife me 1 (some testCause))))
  let gInnerGrantsB : Game := addPermanent gInnerGrants0 bear me me
  let innerBear := (gInnerGrantsB.battlefield.filter (·.name == bear.name))[0]!.id
  let gInnerGrantsB : Game :=
    (gInnerGrantsB.createEffect (.replacement { id := idCnt1, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1 }) (cause := some testCause)).createEffect
      (.replacement { id := idCnt2, affectedPlayer := me, kind := .modifyCountersPut none (some .plusOnePlusOne) 0 3 }) (cause := some testCause)
  let gInnerGrantsPaused0 : Game :=
    (gInnerGrantsB.addPlusOnePlusOneTo (gInnerGrantsB.object! innerBear) 1 (cause := some testCause)).chainPendingReplacement (.receivePriority opp18)
  let gInnerGrantsPaused : Game := gInnerGrantsPaused0.finishAndGrantPriority me
  let innerNoDup : Bool :=
    gInnerGrantsPaused.pendingReplacement == gInnerGrantsPaused0.pendingReplacement
  let outerDeferPriorityOk : Bool :=
    endsCheckOk && gOutDone.priority == opp18 &&
    newerPausedNoDup && gNewerOuterDone.priority == opp18 &&
    innerNoDup

  -- 2b. `runLinkedExileBatch` Pass 2: returning a permanent with an ETB trigger via `linkedExile` runs Pass 2!
  let etbBearDef : CardDef := { bear with name := "Phase18 Linked ETB Bear", triggeredAbilities := #[.onEnterDraw 1] }
  let gLk0 : Game := addPermanent (insertObject afterDraw etbBearDef me .exile) hero me me
  let exBearId := (gLk0.objects.filter (fun o => o.name == "Phase18 Linked ETB Bear" && o.zone == .exile))[0]!.id
  let hostId := (gLk0.battlefield.filter (·.name == hero.name))[0]!.id
  let gLk1 : Game := gLk0.changeObject hostId (.linkedExile #[exBearId])
  let (gLk2, _) := gLk1.move hostId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let linkedPass2Ok : Bool :=
    (gLk2.permanentsOf me).any (·.name == "Phase18 Linked ETB Bear") &&
    gLk2.waitingTriggers.any (fun wt => wt.source.name == "Phase18 Linked ETB Bear")

  -- 2c. `shuffleSourceIntoLibrary` owner-based shuffle + draw continuation:
  let gSh0 : Game := addPermanent afterDraw bear opp18 me
  let shBear := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let gShDone : Game := gSh0.withBatch (some testCause) fun g =>
    g.shuffleSourceIntoLibrary (some shBear) (.draw me 1)
  let shuffleOwnerDrawOk : Bool :=
    gShDone.pending == .resolveRandom (.shuffleLibrary opp18) &&
    gShDone.afterRandom == .draw opp18 1 &&
    (gShDone.player opp18).library.any (fun id => (gShDone.object! id).name == bear.name)

  -- 2d. Reflexive-sacrifice (`TriggeredAbilities.applySacrifice` + `queueReflexive`) pauses on `chooseReplacement` BEFORE `putReflexiveTrigger`!
  let idDieA : ReplacementId := { kind := .finalityCounterExile, object := some ⟨601⟩ }
  let idDieB : ReplacementId := { kind := .exileOppDeath, object := some ⟨602⟩ }
  let planDef18 : CardDef := { name := "The Plan", types := #[.enchantment] }
  let gSac0 : Game := addPermanent (addPermanent afterDraw bear me me) planDef18 me me
  let sacPlanObj := (gSac0.battlefield.filter (·.name == "The Plan"))[0]!
  let sacPlan := sacPlanObj.id
  let gSac0 : Game :=
    (gSac0.createEffect (.replacement { id := idDieA, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some sacPlan) false }) (cause := some testCause)).createEffect
      (.replacement { id := idDieB, affectedPlayer := me, kind := .exileInsteadOfGraveyard (some sacPlan) true }) (cause := some testCause)
  let gSacStacked : Game :=
    gSac0.putTriggeredAbilityOnStack me sacPlanObj .onFourthPlanIndestructible "fourth" (eventCause := some testCause)
  let preRefIdx := gSacStacked.events.size
  let gSacChosen : Game := gSacStacked.resolveTop
  let sacPausedBeforeReflexive : Bool :=
    (match gSacChosen.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gSacChosen.waitingTriggers.isEmpty &&
    !(gSacChosen.events.extract preRefIdx gSacChosen.events.size).any (fun e =>
      match e.change with | .rules (.triggerQueue (.triggered ..)) => true | _ => false)
  let gSacAfterRep : Game := mustApply gSacChosen me (.chooseReplacement idDieA)
  let sacQueuedAfterRep : Bool :=
    gSacAfterRep.pending == .chooseTargets me &&
    gSacAfterRep.stack.size == 1

  mustHold18 "2a.outerDeferPriorityOk" outerDeferPriorityOk &&
  mustHold18 "2b.linkedPass2Ok" linkedPass2Ok &&
  mustHold18 "2c.shuffleOwnerDrawOk" shuffleOwnerDrawOk &&
  mustHold18 "2d.sacPausedBeforeReflexive" sacPausedBeforeReflexive &&
  mustHold18 "2d.sacQueuedAfterRep" sacQueuedAfterRep &&
  mustHold18 "2.replay" ([gOutPaused, gOutDone, gNewerOuterPaused, gNewerOuterDone, gInnerGrantsPaused, gLk2, gShDone, gSacChosen, gSacAfterRep].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. CR 733.1 `.crew` / `.zemoBoastExile` & `reverseToProposalCheckpoint?` batch/linkedExile/lookedAt fidelity.
#guard
  let boat18 : CardDef := {
    name := "Phase18 Skiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 4
    toughness := some 4
    keywords := #[.crew 2]
  }
  let gCr0 : Game := addPermanent (addPermanent afterDraw boat18 me me) bear me me
  let skiffId := (gCr0.battlefield.filter (·.name == "Phase18 Skiff"))[0]!.id
  let pilotId := (gCr0.battlefield.filter (·.name == bear.name))[0]!.id
  -- 3a. Accepting `.crew` taps `pilotId` inside a `.costAction` `EventCause.costPayment .tap` batch; declining reverses cleanly!
  let gCrAsk : Game := mustApply gCr0 me (.activate skiffId 0)
  let gCrPaid : Game := mustApply gCrAsk me (.choosePermanents #[pilotId])
  let crewPaidOk : Bool :=
    (gCrPaid.object! pilotId).status.tapped &&
    gCrPaid.stack.size == 1 &&
    gCrPaid.events.any (fun e =>
      match e.change, e.cause? with
      | .rules (.permanent (.tapped eo _)), some (.costPayment .tap p _) => eo.id == some pilotId && p == me
      | _, _ => false)
  let crewDeclineBlocked : Bool := !(gCrAsk.apply me .decline).isOk
  let gCrDec : Game := mustApply (gCrAsk.becomeTapped (gCrAsk.object! pilotId)) me .decline
  let crewDecOk : Bool :=
    crewDeclineBlocked &&
    gCrDec.stack.isEmpty &&
    gCrDec.proposedSpell.isNone &&
    gCrDec.nextObjectId == gCr0.nextObjectId

  -- 3b. Accepting `.zemoBoastExile` across TWO graveyard cards exiles both in a single `BatchId`!
  let zemo18 : CardDef := {
    name := "Phase18 Zemo"
    types := #[.creature]
    power := some 3
    toughness := some 3
    activatedAbilities := #[ActivatedAbility.zemoBoastAbility]
  }
  let blk8Def : CardDef := {
    name := "Phase18 Eight Black"
    manaCost := { symbols := Array.replicate 8 (.colored .black) }
    types := #[.creature]
    power := some 1
    toughness := some 1
  }
  let gZm0 : Game :=
    let g := addPermanent afterDraw zemo18 me me
    let g := insertObject (insertObject g blk8Def me (.graveyard me)) { blk8Def with name := "Phase18 Eight Black B" } me (.graveyard me)
    let z := (g.battlefield.filter (·.name == "Phase18 Zemo"))[0]!
    g.record (GameEvent.attacked g.turnNumber me (g.snapshot z) opp18)
  let zmId := (gZm0.battlefield.filter (·.name == "Phase18 Zemo"))[0]!.id
  let gy2 := (gZm0.player me).graveyard
  let preZmIdx := gZm0.events.size
  let gZmPaid : Game := mustApply (mustApply gZm0 me (.activate zmId 0)) me (.choosePermanents gy2)
  let zmBatches := (gZmPaid.events.extract preZmIdx gZmPaid.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.graveyard _) .exile _ _ _ _)) => e.batch
    | _ => none
  let zemoBatchOk : Bool :=
    zmBatches.size == 2 && zmBatches[0]! == zmBatches[1]! && gZmPaid.stack.size == 1

  -- 3c. `reverseToProposalCheckpoint?`: kept irreversible action with consecutive `.engine` events inside one `BatchId`,
  --     `.lookedAt` filtering of non-library `cardIds`, and `queuedLinkedExile` flush!
  let gRev0 : Game := addPermanent (insertObject afterDraw bear me .exile) hero me me
  let linkedCard := (gRev0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let hostHero := (gRev0.battlefield.filter (·.name == hero.name))[0]!.id
  let gRev0 : Game := gRev0.changeObject hostHero (.linkedExile #[linkedCard])
  let liveTop := (gRev0.player me).library.back!
  let gRevCkpt : Game := gRev0.change .saveProposalCheckpoint
  let (gRevTmp, revTmpObj) := gRevCkpt.allocObject bear me .stack (some me)
  let gIrrev : Game :=
    gRevTmp.withProposalAction (.manaAbility (some hostHero)) fun g =>
      g.withBatchCore (some (.costPayment .sacrifice me (some hostHero))) fun g =>
        let (g, _) := g.move hostHero (.graveyard me) none (verb := some .sacrifice) (actor := some me)
          (cause := some (.costPayment .sacrifice me (some hostHero)))
        let g := (g.logMsg "interleaved log 1").logMsg "interleaved log 2"
        let g := g.addMana me (.colored .red) 1 (cause := some (.costPayment .sacrifice me (some hostHero)))
        g.record (GameEvent.lookedAt g.turnNumber me #[liveTop, revTmpObj.id] (cause := some (.costPayment .sacrifice me (some hostHero))))
  let gReversed : Game :=
    match gIrrev.reverseToProposalCheckpoint? with
    | .ok g' => g'
    | .error e => panic! s!"reverse failed: {e}"
  let keptMoveAndManaBatches := (gReversed.events.extract gRev0.events.size gReversed.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ .battlefield (.graveyard _) _ _ _ _))
    | .rules (.player (.manaAdded ..)) => e.batch
    | _ => none
  let lookedFiltered := (gReversed.events.extract gRev0.events.size gReversed.events.size).any fun e =>
    match e.change with
    | .rules (.player (.lookedAt _ ids)) => ids == #[liveTop]
    | _ => false
  let revKeepOk : Bool :=
    keptMoveAndManaBatches.size == 2 &&
    keptMoveAndManaBatches[0]! == keptMoveAndManaBatches[1]! &&
    lookedFiltered &&
    gReversed.queuedLinkedExile.isEmpty &&
    (gReversed.permanentsOf me).any (·.name == bear.name)

  mustHold18 "3a.crewPaidOk" crewPaidOk &&
  mustHold18 "3a.crewDecOk" crewDecOk &&
  mustHold18 "3b.zemoBatchOk" zemoBatchOk &&
  mustHold18 "3c.revKeepOk" revKeepOk &&
  mustHold18 "3.replay" ([gCrPaid, gCrDec, gZmPaid, gReversed].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 603.2d / 603.3c–d multi-copy modal triggers, mandatory `count`-mode removal, `tapOrUntapNonland`, `hawkeyeModes`, & `combineTriggerModes`.
#guard
  -- 4a. Sequential multi-copy modal trigger announcement via `extraTriggerAnotherYouControl`:
  let modalEtbDef : CardDef := {
    bear with
    name := "Phase18 Modal ETB"
    triggeredAbilities := #[
      TriggeredAbility.mkModal .thisEnters #[
        { body := Instruction.gainLifeFixed 3, phrase := "You gain 3 life" },
        { body := Instruction.drawFixed 1, phrase := "Draw a card" }
      ] (headerPhrase := "Choose one —")
    ]
  }
  let doublerDef : CardDef := {
    hero with
    name := "Phase18 Trigger Doubler"
    staticAbilities := #[.extraTriggerAnotherYouControl #[] #[.creature]]
  }
  let gMod0 : Game := insertObject (addPermanent afterDraw doublerDef me me) modalEtbDef me (.hand me)
  let modH := (gMod0.player me).hand.back!
  let (gMod1, _) := gMod0.putOntoBattlefield modH me (cause := some testCause)
  let gModP1 : Game := gMod1.receivePriority me
  let copy0PausedOk : Bool :=
    (match gModP1.pending with | .fraChoice p (.triggerModes _ 1 #[]) => p == me | _ => false) &&
    gModP1.stack.size == 1 &&
    gModP1.waitingTriggers.size == 1 &&
    gModP1.waitingTriggers[0]!.ordered
  let gModP2 : Game := mustApply gModP1 me (.chooseMode 0)
  let copy1PausedOk : Bool :=
    (match gModP2.pending with | .fraChoice p (.triggerModes _ 1 #[]) => p == me | _ => false) &&
    gModP2.stack.size == 2 &&
    gModP2.waitingTriggers.isEmpty
  let lifePreMod := (gMod0.player me).life
  let handPreMod := (gMod1.player me).hand.size
  let gModDone : Game := ((mustApply gModP2 me (.chooseMode 1)).resolveTop).resolveTop
  let bothResolvedOk : Bool :=
    (gModDone.player me).life == lifePreMod + 3 &&
    (gModDone.player me).hand.size == handPreMod + 1

  -- 4b. Mandatory `"choose two —"` (`chooseTriggerModes 2`) removed (`noLegalMode`) when only 1 mode is choosable!
  let oppEnchSpec : TargetSpec :=
    .ofDomain (.object .battlefield (ObjectPred.andAll #[.hasType .enchantment, .controlledBy .opponent]))
  let choose2Def : CardDef := {
    bear with
    name := "Phase18 Choose Two"
    triggeredAbilities := #[
      TriggeredAbility.mkModal .thisEnters #[
        { body := Instruction.gainLifeFixed 2, phrase := "You gain 2 life" },
        { targeting := .of .oppArtifact, body := Instruction.destroy (.target 0), phrase := "Destroy target artifact an opponent controls" },
        { targeting := .of oppEnchSpec, body := Instruction.destroy (.target 0), phrase := "Destroy target enchantment an opponent controls" }
      ] (headerPhrase := "Choose two —") (minModes := .const 2) (maxModes := .const 2)
    ]
  }
  let gCh2_0 : Game := addPermanent afterDraw choose2Def me me
  let ch2Src := (gCh2_0.battlefield.filter (·.name == "Phase18 Choose Two"))[0]!
  let preCh2 := gCh2_0.events.size
  let gCh2_1 : Game := gCh2_0.putTriggeredAbilityOnStack me ch2Src choose2Def.triggeredAbilities[0]! "enter" (eventCause := some testCause)
  let ch2RemovedOk : Bool :=
    gCh2_1.stack.isEmpty &&
    gCh2_1.pending == .none &&
    (gCh2_1.events.extract preCh2 gCh2_1.events.size).any (fun e => e.cause? == some (.gameRule .noLegalMode))

  -- 4c. `SharedTrigger.tapOrUntapNonland` announces mode + target ON STACK PLACEMENT (`CastEvent.announced`)!
  let tapUntapAb : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters (Effect.ofTrigger .tapOrUntapNonland)
  let tapUntapDef : CardDef := { bear with name := "Phase18 Twiddler", triggeredAbilities := #[tapUntapAb] }
  let gTw0 : Game := addPermanent (addPermanent afterDraw tapUntapDef me me) hero opp18 opp18
  let twSrc := (gTw0.battlefield.filter (·.name == "Phase18 Twiddler"))[0]!
  let oppHeroId := (gTw0.battlefield.filter (·.name == hero.name))[0]!.id
  let gTwStack : Game := gTw0.putTriggeredAbilityOnStack me twSrc tapUntapAb "enter" (eventCause := some testCause)
  let twModePromptOnStack : Bool :=
    match gTwStack.pending with
    | .fraChoice p (.triggerModes _ 1 #[]) => p == me
    | _ => false
  let gTwMode0 : Game := mustApply gTwStack me (.chooseMode 0)
  let twTargetPromptOnStack : Bool := gTwMode0.pending == .chooseTargets me
  let gTwTargeted : Game := mustApply gTwMode0 me (.target (.permanent oppHeroId))
  let gTwRes : Game := gTwTargeted.resolveTop
  let twOk : Bool := twModePromptOnStack && twTargetPromptOnStack && (gTwRes.object! oppHeroId).status.tapped

  -- 4d. Hawkeye Trick Arrows (`Resolution.mshReflexive .trickArrows 2`): prompts `.hawkeyeModes` on stack placement; declining keeps 0-mode ability on stack!
  let gHk0 : Game := addPermanent (addPermanent afterDraw bear me me) hero opp18 opp18
  let hkSrc := (gHk0.battlefield.filter (·.name == bear.name))[0]!
  let gHkStack : Game :=
    gHk0.putReflexiveTrigger me (some hkSrc.id)
      { resolution? := some (.mshReflexive .trickArrows 2), phrase := "Choose up to 2 Trick Arrows modes" }
  let hkPromptOnStack : Bool :=
    match gHkStack.pending with
    | .fraChoice p (.hawkeyeModes 2 #[] (some _)) => p == me
    | _ => false
  let gHkZero : Game := mustApply gHkStack me .decline
  let hkZeroStaysOnStack : Bool :=
    gHkZero.stack.size == 1 &&
    gHkZero.pending == .none &&
    gHkZero.events.any (fun e => match e.change with | .rules (.cast (.announced _ #[] none #[])) => true | _ => false)
  let gHkZeroRes : Game := gHkZero.resolveTop

  -- 4e. `combineTriggerModes`: preserves `allowsZeroTargets` & sums `maxTargets` across chosen modes!
  let mOpt1 : Effect := { targeting := .of .creature, allowsZeroTargets := true, maxTargets := 1, body := Instruction.tap (.target 0), phrase := "Tap up to one" }
  let mOpt2 : Effect := { targeting := .of .opponent, allowsZeroTargets := true, maxTargets := 2, body := Instruction.loseLifeFixed 1 (.target 0), phrase := "Up to two opps" }
  let mMand : Effect := { targeting := .of .creature, allowsZeroTargets := false, maxTargets := 1, body := Instruction.untap (.target 0), phrase := "Untap target" }
  let combBothOpt := Game.combineTriggerModes #[mOpt1, mOpt2] #[0, 1]
  let combMixed := Game.combineTriggerModes #[mOpt1, mMand] #[0, 1]
  let combineModesOk : Bool :=
    (match combBothOpt with | some e => e.allowsZeroTargets && e.maxTargets == 3 | none => false) &&
    (match combMixed with | some e => !e.allowsZeroTargets && e.maxTargets == 2 | none => false)

  mustHold18 "4a.copy0PausedOk" copy0PausedOk &&
  mustHold18 "4a.copy1PausedOk" copy1PausedOk &&
  mustHold18 "4a.bothResolvedOk" bothResolvedOk &&
  mustHold18 "4b.ch2RemovedOk" ch2RemovedOk &&
  mustHold18 "4c.twOk" twOk &&
  mustHold18 "4d.hkPromptOnStack" hkPromptOnStack &&
  mustHold18 "4d.hkZeroStaysOnStack" hkZeroStaysOnStack &&
  mustHold18 "4e.combineModesOk" combineModesOk &&
  mustHold18 "4.replay" ([gModP1, gModP2, gModDone, gCh2_1, gTwStack, gTwTargeted, gTwRes, gHkStack, gHkZero, gHkZeroRes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 506.5 `attacksAlonePlus2Indestructible`, CR 603.4 / 608.2h `evalTriggerCond` LKI, CR 702.26b `attachedEquipmentAtResolution`, & CR 707.2 `.copySelfNonlegendary`.
#guard
  -- 5a. CR 506.5: `attacksAlonePlus2Indestructible` checks declared attacker count (`decls.size == 1`)!
  let lonerAb : TriggeredAbility := TriggeredAbility.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible
  let lonerDef : CardDef := { bear with name := "Phase18 Loner", triggeredAbilities := #[lonerAb] }
  let gLn0 : Game := addPermanent (addPermanent afterDraw lonerDef me me) hero me me
  let lnId := (gLn0.battlefield.filter (·.name == "Phase18 Loner"))[0]!.id
  let hrId := (gLn0.battlefield.filter (·.name == hero.name))[0]!.id
  let gLnTwo : Game :=
    let g1 := gLn0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    mustApply g1 me (.declareAttackers #[lnId, hrId] none #[] #[])
  let gLnOne : Game :=
    let g1 := gLn0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    (mustApply g1 me (.declareAttackers #[lnId] none #[] #[])).resolveTop
  let lonerOk : Bool :=
    gLnTwo.stack.isEmpty &&
    gLnOne.power (gLnOne.object! lnId) == 4 &&
    gLnOne.hasIndestructible (gLnOne.object! lnId)

  -- 5b. CR 603.4 / 608.2h `evalTriggerCond` LKI fallback when `source` left `.battlefield`:
  let gLki0 : Game := addPermanent afterDraw bear me me
  let lkiId := (gLki0.battlefield.filter (·.name == bear.name))[0]!.id
  let gLki1 : Game := gLki0.recordPutCounters lkiId .plusOnePlusOne 1 (some me) (cause := some testCause)
  let snapWithCounter := gLki1.object! lkiId
  let (gLkiGone, _) := gLki1.move lkiId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let lkiCondOk : Bool :=
    gLkiGone.evalTriggerCond me (some snapWithCounter) none TriggeredAbility.condSourceHasCounters &&
    !gLkiGone.evalTriggerCond me (some (gLki0.object! lkiId)) none TriggeredAbility.condSourceHasCounters

  -- 5c. CR 702.26b: `attachedEquipmentAtResolution` returns `0` when the creature is phased out on `.battlefield` (not `lastKnownPower` 4)!
  let eqDef18 : CardDef := { name := "Phase18 Blade", manaCost := ManaCost.empty, types := #[.artifact], subtypes := #["Equipment"] }
  let gEq0 : Game := addPermanent (addPermanent afterDraw { bear with name := "Phase18 Wielder", power := some 4 } me me) eqDef18 me me
  let wldId := (gEq0.battlefield.filter (·.name == "Phase18 Wielder"))[0]!.id
  let bldId := (gEq0.battlefield.filter (·.name == "Phase18 Blade"))[0]!.id
  let gEq1 : Game := gEq0.record (GameEvent.attached gEq0.turnNumber (gEq0.snapshot (gEq0.object! bldId)) wldId (cause := testCause))
  let gEqPhased : Game := gEq1.phaseOut (gEq1.object! wldId) (cause := some testCause)
  let eqPhasedZeroOk : Bool :=
    gEq1.attachedEquipmentAtResolution (some wldId) (some 4) == 1 &&
    gEqPhased.attachedEquipmentAtResolution (some wldId) (some 4) == 0

  -- 5d. CR 707.2 `.copySelfNonlegendary`: uses `eo.copiable.getD eo.toCardDef` when source became a copy and left `.battlefield`!
  let selfCopyAb : TriggeredAbility := SharedTrigger.copySelfNonlegendary.toTriggeredAbility
  let templateHeroDef : CardDef := {
    hero with
    name := "Phase18 Legendary Template"
    supertypes := #[.legendary]
    power := some 5
    toughness := some 6
    triggeredAbilities := #[selfCopyAb]
  }
  let gCp0 : Game := addPermanent (addPermanent afterDraw bear me me) templateHeroDef me me
  let origBear := (gCp0.battlefield.filter (·.name == bear.name))[0]!.id
  let tmplId := (gCp0.battlefield.filter (·.name == "Phase18 Legendary Template"))[0]!.id
  let gCp1 : Game := gCp0.withBatch (some testCause) fun g =>
    g.becomeCopyOf (g.object! origBear) (g.object! tmplId)
  let gCpStack : Game := gCp1.putTriggeredAbilityOnStack me (gCp1.object! origBear) selfCopyAb "enter" (eventCause := some testCause)
  let (gCpGone, _) := gCpStack.move origBear (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let gCpRes : Game := gCpGone.resolveTop
  let cpTokens := (gCpRes.permanentsOf me).filter (fun o => o.printed.isToken && o.name == "Phase18 Legendary Template")
  let copyCopiableLkiOk : Bool :=
    cpTokens.size == 2 &&
    cpTokens.all (fun t => gCpRes.power t == 5 && gCpRes.toughness t == 6 && !(gCpRes.supertypes t).contains .legendary)

  mustHold18 "5a.lonerOk" lonerOk &&
  mustHold18 "5b.lkiCondOk" lkiCondOk &&
  mustHold18 "5c.eqPhasedZeroOk" eqPhasedZeroOk &&
  mustHold18 "5d.copyCopiableLkiOk" copyCopiableLkiOk &&
  mustHold18 "5.replay" ([gLnTwo, gLnOne, gLkiGone, gEqPhased, gCpRes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 707.10c / 115.3 / 115.7d `.copyCauseSpell` & `.venserSpell` retargeting, cross-slot `[A, B] -> [B, A]` swaps, & CR 608.2b multi-target legality.
#guard
  let pingDef18 : CardDef := { lightningBolt with name := "Phase18 Bolt", manaCost := ManaCost.empty }
  let gRt0 : Game := addPermanent (addPermanent afterDraw bear opp18 opp18) hero opp18 opp18
  let tBear := (gRt0.battlefield.filter (·.name == bear.name))[0]!.id
  let tHero := (gRt0.battlefield.filter (·.name == hero.name))[0]!.id
  let gRt0 : Game := insertObject gRt0 pingDef18 opp18 (.hand opp18)
  let boltH := (gRt0.player opp18).hand.back!
  let gRtCast : Game := mustApply (mustApply (gRt0.change (.priority opp18)) opp18 (.cast boltH)) opp18 (.target (.permanent tBear))
  let boltStackId := gRtCast.stack.back!.objectId

  -- 6a. Venser spell-copy mode copies opponent's targeted spell twice and prompts `.newTargetsForCopies #[c1, c2]`!
  let venserEff : Effect := venserFerventForger.triggeredAbilities[0]!.modeEffects[0]!
  let gVenPrompt : Game := gRtCast.applyAbilityEffect me venserEff #[Target.card boltStackId]
  let venCopiesPromptOk : Bool :=
    match gVenPrompt.pending with
    | .fraChoice p (.newTargetsForCopies cs) => p == me && cs.size == 2
    | _ => false
  let gVenRetargeted : Game :=
    let g1 := mustApply gVenPrompt me (.choosePermanents #[tHero])
    mustApply g1 me .decline

  -- Copy-cause-spell also prompts `.newTargetsForCopies #[copyId]`!
  let copyCauseEff : Effect := { body := .stack (.copyStackObject .triggerSubject (.const 1) true), phrase := "Copy that spell" }
  let abId : ObjectId := ⟨gRtCast.nextObjectId⟩
  let gCauseStacked : Game :=
    gRtCast.record (GameEvent.triggerPutOnStack gRtCast.turnNumber abId (gRtCast.snapshot (gRtCast.object! tBear)) me
      (spec := { abilityEffect := some copyCauseEff, sourceId := some tBear, fraCauseId := some boltStackId })
      (cause := testCause))
  let gCausePrompt : Game := gCauseStacked.resolveTop
  let copyCausePromptOk : Bool :=
    match gCausePrompt.pending with
    | .fraChoice p (.newTargetsForCopies cs) => p == me && cs.size == 1
    | _ => false
  let gCauseDone : Game := mustApply gCausePrompt me .decline

  -- 6b. Cross-slot `[A, B] -> [B, A]` swap on `.twoNonlandsSharingType`, plus revert when slot 1 is declined on incompatible type!
  let exchSpellDef : CardDef := {
    name := "Phase18 Swap Control"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      targeting := .of .twoNonlandsSharingType
      body := .installEffect (.applyContinuous .indefinite (.target 0) (.exchangeControl (.target 1)))
      phrase := "Exchange control of two target nonland permanents that share a card type"
    }
  }
  let relicOnlyDef : CardDef := { name := "Phase18 Pure Relic", manaCost := ManaCost.empty, types := #[.artifact] }
  let relicTwoDef : CardDef := { name := "Phase18 Pure Relic 2", manaCost := ManaCost.empty, types := #[.artifact] }
  let gSw0 : Game :=
    insertObject (addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear me me) hero opp18 opp18)
      relicOnlyDef me me) relicTwoDef opp18 opp18) exchSpellDef me (.hand me)
  let swBear := (gSw0.battlefield.filter (·.name == bear.name))[0]!.id
  let swHero := (gSw0.battlefield.filter (·.name == hero.name))[0]!.id
  let swRel1 := (gSw0.battlefield.filter (·.name == "Phase18 Pure Relic"))[0]!.id
  let swRel2 := (gSw0.battlefield.filter (·.name == "Phase18 Pure Relic 2"))[0]!.id
  let swCard := (gSw0.player me).hand.back!
  let gSwCast : Game :=
    mustApply (mustApply gSw0 me (.cast swCard)) me (.targets #[.permanent swBear, .permanent swHero])
  let swSpellId := gSwCast.stack.back!.objectId
  -- Swap `[swBear, swHero]` -> `[swHero, swBear]` via `.newTargetsForCopies`:
  let gSwPrompt : Game := gSwCast.beginFraChoice me (.newTargetsForCopies #[swSpellId]) "retarget"
  let gSwSwapped : Game :=
    mustApply (mustApply gSwPrompt me (.choosePermanents #[swHero])) me (.choosePermanents #[swBear])
  let swapTargetsOk : Bool :=
    (gSwSwapped.stackEntry? swSpellId).map (·.targets) == some #[Target.permanent swHero, Target.permanent swBear]
  -- Incomplete edit: pick `swRel1` (artifact only) for slot 0, then `.decline` slot 1 (`swBear` is creature only) => reverts to `[swHero, swBear]`!
  let gSwInc0 : Game := gSwSwapped.beginFraChoice me (.newTargetsForCopies #[swSpellId]) "retarget incomplete"
  let gSwReverted : Game :=
    mustApply (mustApply gSwInc0 me (.choosePermanents #[swRel1])) me .decline
  let revertIncompleteOk : Bool :=
    (gSwReverted.stackEntry? swSpellId).map (·.targets) == some #[Target.permanent swHero, Target.permanent swBear]
  -- Valid switch to `[swRel1, swRel2]` works:
  let gSwValidArt : Game :=
    let g1 := gSwReverted.beginFraChoice me (.newTargetsForCopies #[swSpellId]) "retarget artifacts"
    mustApply (mustApply g1 me (.choosePermanents #[swRel1])) me (.choosePermanents #[swRel2])
  let validArtRetargetOk : Bool :=
    (gSwValidArt.stackEntry? swSpellId).map (·.targets) == some #[Target.permanent swRel1, Target.permanent swRel2]

  -- 6c. CR 608.2b multi-target per-slot legality: destroy-all-targets skips target that gained hexproof while destroying remaining legal target!
  let destroyTwoEff : Effect := {
    targeting := .of (.ofDomain .oppCreatureOrPlaneswalker (.exact 2))
    body := Instruction.destroy .allTargets
    phrase := "Destroy two target creatures or planeswalkers an opponent controls"
  }
  let gMt0 : Game := addPermanent (addPermanent afterDraw bear opp18 opp18) hero opp18 opp18
  let mtBear := (gMt0.battlefield.filter (·.name == bear.name))[0]!.id
  let mtHero := (gMt0.battlefield.filter (·.name == hero.name))[0]!.id
  let gMtHex : Game := gMt0.createEffect (.keywordsUntilEot mtBear #[Keyword.hexproof]) (cause := some testCause)
  let gMtRes : Game := gMtHex.applyEffect me destroyTwoEff #[Target.permanent mtBear, Target.permanent mtHero]
  let multiTargetPerSlotOk : Bool :=
    (gMtRes.findObject? mtBear).any (·.isOnBattlefield) &&
    !(gMtRes.findObject? mtHero).any (·.isOnBattlefield)

  mustHold18 "6a.venCopiesPromptOk" venCopiesPromptOk &&
  mustHold18 "6a.copyCausePromptOk" copyCausePromptOk &&
  mustHold18 "6b.swapTargetsOk" swapTargetsOk &&
  mustHold18 "6b.revertIncompleteOk" revertIncompleteOk &&
  mustHold18 "6b.validArtRetargetOk" validArtRetargetOk &&
  mustHold18 "6c.multiTargetPerSlotOk" multiTargetPerSlotOk &&
  mustHold18 "6.replay" ([gVenPrompt, gVenRetargeted, gCauseDone, gSwSwapped, gSwReverted, gSwValidArt, gMtRes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 303.4f–g / 111.8 Aura entry & token-copy non-return, pre-batch host snapshots, & two-pass `createPermanentCopyTokens`.
#guard
  let aura18Def : CardDef := aura "Phase18 Aura" ManaCost.empty "Enchant creature"
  -- 7a1. Casting an Aura whose target leaves `.battlefield` before resolution fizzles (`removedOnResolution`), never entering unattached!
  let gAu0 : Game := insertObject (addPermanent afterDraw bear me me) aura18Def me (.hand me)
  let auHost := (gAu0.battlefield.filter (·.name == bear.name))[0]!.id
  let auCard := (gAu0.player me).hand.back!
  let gAuCast : Game := mustApply (mustApply gAu0 me (.cast auCard)) me (.target (.permanent auHost))
  let (gAuHostGone, _) := gAuCast.move auHost .exile none (cause := some testCause)
  let preAuRes := gAuHostGone.events.size
  let gAuFizzled : Game := gAuHostGone.resolveTop
  let auraFizzleOk : Bool :=
    !(gAuFizzled.permanentsOf me).any (·.name == "Phase18 Aura") &&
    (gAuFizzled.player me).graveyard.any (fun id => (gAuFizzled.object! id).name == "Phase18 Aura") &&
    (gAuFizzled.events.extract preAuRes gAuFizzled.events.size).any (fun e =>
      match e.change with | .rules (.stackObject (.removedOnResolution ..)) => true | _ => false)

  -- 7a2. CR 303.4f/g: `createPermanentCopyTokens` on an Aura template when NO creature is on `.battlefield` creates 0 tokens!
  let gAuTokEmpty : Game := afterDraw.createPermanentCopyTokens me aura18Def 2 (cause := some testCause)
  let auraTokenNoHostOk : Bool :=
    !(gAuTokEmpty.permanentsOf me).any (·.name == "Phase18 Aura")

  -- 7a3. CR 111.8: token `isCopy := true` exiled by `exileThenReturnYouControl` ceases to exist and does NOT return to `.battlefield`!
  let (gTk0, tokCopyObj) := afterDraw.createToken me bear (cause := some testCause)
  let gTkFlicker : Game :=
    gTk0.applyUnified me
      { targeting := .of .creatureYouControl
        body := Effect.exileThenReturnYouControl.body
        phrase := "Exile target creature you control, then return it to the battlefield" }
      #[Target.permanent tokCopyObj.id]
  let gTkChecked : Game := gTkFlicker.checkSBA
  let tokenCopyNoReturnOk : Bool :=
    !(gTkChecked.permanentsOf me).any (·.name == bear.name)

  -- 7c. Two-pass `createPermanentCopyTokens` (`remaining == 2`): both tokens enter in the same batch before Pass 2 haste + delayed sacrifice,
  --     and temporary `ContinuationFrame` is popped cleanly!
  let anotherEntersWatcherDef : CardDef := {
    hero with
    name := "Phase18 Co-Enter Copy"
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger .anotherCreatureYouControlEnters
        { body := Instruction.gainLifeFixed 1, phrase := "Whenever another creature you control enters, you gain 1 life" }
    ]
  }
  let preContSize := afterDraw.continuations.size
  let preCpBatchIdx := afterDraw.events.size
  let gTwoPass : Game := afterDraw.createPermanentCopyTokens me anotherEntersWatcherDef 2 (cause := some testCause)
  let createdBatches := (gTwoPass.events.extract preCpBatchIdx gTwoPass.events.size).filterMap fun e =>
    match e.change with
    | .rules (.zone (.created ..)) => e.batch
    | _ => none
  -- Both copies entered simultaneously in Pass 1, so each sees the OTHER enter (`waitingTriggers.size == 2`), both have haste, and 2 delayed triggers!
  let twoPassCopies := (gTwoPass.permanentsOf me).filter (·.name == "Phase18 Co-Enter Copy")
  let twoPassCopyOk : Bool :=
    gTwoPass.continuations.size == preContSize &&
    createdBatches.size == 2 && createdBatches[0]! == createdBatches[1]! &&
    twoPassCopies.size == 2 &&
    twoPassCopies.all (gTwoPass.hasHaste ·) &&
    gTwoPass.delayedTriggers.size == 2 &&
    gTwoPass.waitingTriggers.size == 2

  mustHold18 "7a1.auraFizzleOk" auraFizzleOk &&
  mustHold18 "7a2.auraTokenNoHostOk" auraTokenNoHostOk &&
  mustHold18 "7a3.tokenCopyNoReturnOk" tokenCopyNoReturnOk &&
  mustHold18 "7c.twoPassCopyOk" twoPassCopyOk &&
  mustHold18 "7.replay" ([gAuFizzled, gAuTokEmpty, gTkChecked, gTwoPass].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 800.4 / 725.4 / 509.1g / 723.5 multiplayer combat, monarch, prompt-revalidation, blocker-retention, & `playerControl`.
#guard
  let g3Base : Game := mkThreePlayer18 28
  -- 8a. `dealAssignedCombatDamage` survives a blocker's controller conceding during `Pending.assignCombatDamage _ false`!
  let multiBlkDef18 : CardDef := { bear with name := "Phase18 Multi Blocker", power := some 3, toughness := some 5 }
  let gCd0 : Game :=
    addPermanent (addPermanent (addPermanent (addPermanent g3Base bear ⟨0⟩ ⟨0⟩) hero ⟨0⟩ ⟨0⟩)
      multiBlkDef18 ⟨1⟩ ⟨1⟩) { bear with name := "Atk vs P2" } ⟨0⟩ ⟨0⟩
  let ca1 := (gCd0.battlefield.filter (·.name == bear.name))[0]!.id
  let ca2 := (gCd0.battlefield.filter (·.name == hero.name))[0]!.id
  let ca3 := (gCd0.battlefield.filter (·.name == "Atk vs P2"))[0]!.id
  let cmb := (gCd0.battlefield.filter (·.name == "Phase18 Multi Blocker"))[0]!.id
  let gCd1 : Game :=
    let g1 := gCd0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let g1 := mustApply g1 ⟨0⟩ (.declareAttackers #[ca1, ca2, ca3] none #[some ⟨1⟩, some ⟨1⟩, some ⟨2⟩] #[])
    let g1 := mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    let g1 := mustApply g1 ⟨1⟩ (.declareBlockers #[(cmb, ca1), (cmb, ca2)])
    let g1 := mustApply g1 ⟨2⟩ (.declareBlockers #[])
    mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
  -- `gCd1.pending == .assignCombatDamage ⟨1⟩ false`; now `⟨1⟩` concedes!
  let p2LifePre := (gCd1.player ⟨2⟩).life
  let gCdConcede : Game := gCd1.concede ⟨1⟩
  let combatDepartSafeOk : Bool :=
    gCd1.pending == .assignCombatDamage ⟨1⟩ false &&
    gCdConcede.pending == .none &&
    (gCdConcede.player ⟨2⟩).life == p2LifePre - 2

  -- 8b. `beginStep .declareBlockers` when attacked player `⟨1⟩` conceded before `.declareBlockers`: skips `Pending.declareBlockers`!
  let gDb0 : Game := addPermanent g3Base bear ⟨0⟩ ⟨0⟩
  let dbAtk := (gDb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gDb1 : Game :=
    let g1 := gDb0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply (mustApply g1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
    mustApply g1 ⟨0⟩ (.declareAttackers #[dbAtk] none #[some ⟨1⟩] #[])
  let gDbConceded : Game := gDb1.concede ⟨1⟩
  let gDbStep : Game := mustApply (mustApply gDbConceded ⟨0⟩ .pass) ⟨2⟩ .pass
  let skipBlockersEmptyDefOk : Bool :=
    gDbStep.step == .declareBlockers &&
    gDbStep.pending == .none &&
    gDbStep.blockersQueue.isEmpty

  -- 8c. CR 725.4 monarch succession on departure:
  -- (i) `⟨0⟩` active, `⟨1⟩` monarch -> `⟨1⟩` concedes => `⟨0⟩` (`activePlayer`) becomes monarch!
  let gMonA : Game := (g3Base.becomeMonarch ⟨1⟩).concede ⟨1⟩
  -- (ii) `⟨0⟩` active AND monarch -> `⟨0⟩` concedes => `⟨1⟩` (`nextLiving ⟨0⟩`) becomes monarch!
  let gMonB : Game := (g3Base.becomeMonarch ⟨0⟩).concede ⟨0⟩
  let monarchSuccessionOk : Bool :=
    (gMonA.player ⟨0⟩).isMonarch && !(gMonA.player ⟨1⟩).isMonarch &&
    (gMonB.player ⟨1⟩).isMonarch && !(gMonB.player ⟨0⟩).isMonarch

  -- 8d. Prompt revalidation on third-party departure (`redirectPendingAfterLeave` & `announceGift`):
  let giftSpellDef : CardDef := {
    name := "Phase18 Gift Card"
    manaCost := ManaCost.empty
    types := #[.instant]
    keywords := #[.gift .treasure]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let gGf0 : Game := (insertObject g3Base giftSpellDef ⟨0⟩ (.hand ⟨0⟩)).concede ⟨1⟩
  let gfH := (gGf0.player ⟨0⟩).hand.back!
  let gGfAsk : Game := mustApply gGf0 ⟨0⟩ (.cast gfH)
  let departedGiftRejected : Bool := !(gGfAsk.applyAction ⟨0⟩ (.announceGift (some ⟨1⟩))).isOk
  let gGfValid : Game := mustApply gGfAsk ⟨0⟩ (.announceGift (some ⟨2⟩))

  -- Stacked trigger waiting on `.chooseTargets ⟨0⟩` whose only legal target belonged to `⟨1⟩` is removed when `⟨1⟩` concedes!
  let killOppCrAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger .thisEnters { targeting := .of .oppCreature, body := Instruction.destroy (.target 0), phrase := "Destroy target creature an opponent controls" }
  let gTg0 : Game := addPermanent (addPermanent g3Base { bear with name := "Phase18 Hunter", triggeredAbilities := #[killOppCrAb] } ⟨0⟩ ⟨0⟩) bear ⟨1⟩ ⟨1⟩
  let hntObj := (gTg0.battlefield.filter (·.name == "Phase18 Hunter"))[0]!
  let gTgPrompt : Game := (gTg0.putTriggeredAbilityOnStack ⟨0⟩ hntObj killOppCrAb "enter" (eventCause := some testCause)).promptTriggerTargetsIfNeeded
  let gTgConceded : Game := gTgPrompt.concede ⟨1⟩
  let triggerTargetLeaveClearedOk : Bool :=
    gTgPrompt.pending == .chooseTargets ⟨0⟩ &&
    gTgConceded.pending == .none &&
    gTgConceded.stack.isEmpty

  -- 8e. CR 509.1g blocker-retention: after `blk` blocks `atk` and `atk` leaves combat, `!blk.status.blocking.isEmpty && (g.creaturesBlockedBy blk).isEmpty`!
  let gBr0 : Game := addPermanent (addPermanent afterDraw bear me me) hero opp18 opp18
  let brAtk := (gBr0.battlefield.filter (·.name == bear.name))[0]!.id
  let brBlk := (gBr0.battlefield.filter (·.name == hero.name))[0]!.id
  let gBr1 : Game :=
    let g1 := gBr0.beginStep .beginningOfCombat
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    let g1 := mustApply g1 me (.declareAttackers #[brAtk] none #[] #[])
    let g1 := mustApply (mustApply g1 me .pass) opp18 .pass
    mustApply g1 opp18 (.declareBlockers #[(brBlk, brAtk)])
  let (gBrExiled, _) := gBr1.move brAtk .exile none (cause := some testCause)
  let blkObj := gBrExiled.object! brBlk
  let blockerRetentionOk : Bool :=
    !blkObj.status.blocking.isEmpty &&
    (gBrExiled.creaturesBlockedBy blkObj).isEmpty &&
    (gBrExiled.blockersOf brAtk).isEmpty

  -- 8f. CR 723.5 `playerControl`: `⟨0⟩` controlling `⟨1⟩` makes `⟨1⟩`'s priority/choice decisions, while only `⟨1⟩` (`rawActor`) may concede `⟨1⟩`!
  let gPc0 : Game := (g3Base.createEffect (.playerControl ⟨0⟩ ⟨1⟩ false) (cause := some testCause)).change (.priority ⟨1⟩)
  let controlledActorOk : Bool :=
    gPc0.actor == some ⟨0⟩ &&
    gPc0.rawActor == some ⟨1⟩ &&
    !(gPc0.applyAction ⟨1⟩ .pass).isOk &&
    (gPc0.applyAction ⟨0⟩ .concede).isOk
  let gPcPassedByController : Game := mustApply gPc0 ⟨0⟩ .pass
  let gPcControlledConcedes : Game := mustApply gPc0 ⟨1⟩ .concede
  let playerControlOk : Bool :=
    controlledActorOk &&
    (gPcControlledConcedes.player ⟨1⟩).leftTheGame &&
    !(gPcControlledConcedes.player ⟨0⟩).leftTheGame

  mustHold18 "8a.combatDepartSafeOk" combatDepartSafeOk &&
  mustHold18 "8b.skipBlockersEmptyDefOk" skipBlockersEmptyDefOk &&
  mustHold18 "8c.monarchSuccessionOk" monarchSuccessionOk &&
  mustHold18 "8d.departedGiftRejected" departedGiftRejected &&
  mustHold18 "8d.triggerTargetLeaveClearedOk" triggerTargetLeaveClearedOk &&
  mustHold18 "8e.blockerRetentionOk" blockerRetentionOk &&
  mustHold18 "8f.playerControlOk" playerControlOk &&
  mustHold18 "8.replay" ([gCdConcede, gDbStep, gMonA, gMonB, gGfValid, gTgConceded, gBrExiled, gPcPassedByController, gPcControlledConcedes].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 9. CR 500.4 `beginTurn` turn-start expiry, CR 611.2a–b / 702.26f `durationActive` & counter/zone expiry, CR 800.4c,i,m phased-out control-expiry exile, & CR 614.12 Arwen `preBfOk`.
#guard
  -- 9a. CR 500.4: `.fraEmblemUntilTurnOf` and `goaded` expire in `beginTurn` BEFORE `phaseBegan .beginning`!
  let embCard : CardDef := { name := "Phase18 Sculptor Emblem", types := #[] }
  let gBt0 : Game := addPermanent (insertObject afterDraw embCard me .command) bear opp18 opp18
  let embId := (gBt0.objects.filter (fun o => o.name == "Phase18 Sculptor Emblem" && o.zone == .command))[0]!.id
  let goadBear := (gBt0.battlefield.filter (·.name == bear.name))[0]!.id
  let gBt1 : Game :=
    (gBt0.createEffect (.fraEmblemUntilTurnOf embId opp18) (cause := some testCause)).record
      (GameEvent.designation gBt0.turnNumber (gBt0.snapshot (gBt0.object! goadBear)) (.goaded opp18) true (cause := testCause))
  let preBtIdx := gBt1.events.size
  let gBt2 : Game := gBt1.startNextTurnCore true
  let btSlice := gBt2.events.extract preBtIdx gBt2.events.size
  let ceaseIdx? := btSlice.findIdx? (fun e => match e.change with | .rules (.zone (.ceasedToExist eo)) => eo.id == some embId | _ => false)
  let goadClearIdx? := btSlice.findIdx? (fun e => match e.change with | .rules (.permanent (.designation _ (.goaded p) false)) => p == opp18 | _ => false)
  let phaseBeganIdx? := btSlice.findIdx? (fun e => match e.change with | .rules (.turn (.phaseBegan .beginning)) => true | _ => false)
  let turnStartBeforePhaseOk : Bool :=
    match ceaseIdx?, goadClearIdx?, phaseBeganIdx? with
    | some ci, some gi, some pi => ci < pi && gi < pi && (gBt2.findObject? embId).isNone
    | _, _, _ => false

  -- 9b. CR 611.2b / 702.26f `durationActive` + `.whileSourceHasCounter` & `.whileInZone` expiration events:
  let gDu0 : Game := addPermanent (addPermanent (insertObject afterDraw lightningBolt me .exile) bear me me) hero opp18 opp18
  let duSrc := (gDu0.battlefield.filter (·.name == bear.name))[0]!.id
  let duTgt := (gDu0.battlefield.filter (·.name == hero.name))[0]!.id
  let duExCard := (gDu0.objects.filter (fun o => o.name == lightningBolt.name && o.zone == .exile))[0]!.id
  let gDu1 : Game := gDu0.recordPutCounters duSrc .plusOnePlusOne 1 (some me) (cause := some testCause)
  let gDu1 : Game :=
    ((gDu1.createEffect (.cantUntapWhileSource duTgt duSrc) (cause := some testCause)).createEffect
      (.layered (.objects #[duTgt]) (.ptModify 2 2) (.whileSourceHasCounter duSrc .plusOnePlusOne)) (cause := some testCause)).createEffect
      (.permission (some me) (.flashback duExCard) (.whileInZone duExCard .exile)) (cause := some testCause)
  let activePrePhase := gDu1.hostCantBecomeUntapped (gDu1.object! duTgt) && gDu1.power (gDu1.object! duTgt) == 4
  let gDuPhased : Game := gDu1.record (GameEvent.phasedOut gDu1.turnNumber (gDu1.snapshot (gDu1.object! duSrc)) false (cause := testCause))
  let inactiveWhilePhased := !gDuPhased.hostCantBecomeUntapped (gDuPhased.object! duTgt) && gDuPhased.power (gDuPhased.object! duTgt) == 2
  let gDuPhasedIn : Game := gDuPhased.record (GameEvent.phasedIn gDuPhased.turnNumber (gDuPhased.snapshot (gDuPhased.object! duSrc)) (cause := testCause))
  let gDuCounterRemoved : Game := gDuPhasedIn.recordRemoveCounters duSrc .plusOnePlusOne 1 (some me) (cause := some testCause)
  let (gDuExMoved, _) := gDuCounterRemoved.move duExCard (.graveyard me) none (cause := some testCause)
  let (gDuSrcMoved, _) := gDuExMoved.move duSrc (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let durationAndExpiryOk : Bool :=
    activePrePhase &&
    inactiveWhilePhased &&
    gDuCounterRemoved.power (gDuCounterRemoved.object! duTgt) == 2 &&
    gDuSrcMoved.activeEffects.isEmpty

  -- 9c. CR 800.4c,i,m & CR 702.26d: phased-out stolen permanent whose owner left is exiled at `clearEOT`,
  --     and departed player's `.untilEndOfTurn` `PlayerRule`s + `.untilEndOfNextTurnOf` copy effects expire!
  let g3Ph : Game := mkThreePlayer18 39
  let g3Ph0 : Game := addPermanent (addPermanent g3Ph bear ⟨0⟩ ⟨2⟩) hero ⟨0⟩ ⟨0⟩
  let p2Bear := (g3Ph0.battlefield.filter (·.name == bear.name))[0]!.id
  let p0Hero := (g3Ph0.battlefield.filter (·.name == hero.name))[0]!.id
  let g3Ph1 : Game :=
    (((g3Ph0.changeControl (g3Ph0.object! p2Bear) ⟨1⟩ (untilEot := true) (cause := some testCause)).createEffect
      (.playerRule ⟨2⟩ (.additionalLands 1) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[p0Hero]) (.copy bear) (.untilEndOfNextTurnOf ⟨2⟩)) (cause := some testCause))
  let g3Ph2 : Game := g3Ph1.concede ⟨2⟩
  -- Phase out `p2Bear` under `⟨1⟩`'s temporary control, then run `clearEOT` AND `expireUntilNextTurnEffects ⟨2⟩`:
  let g3Ph3 : Game := g3Ph2.record (GameEvent.phasedOut g3Ph2.turnNumber (g3Ph2.snapshot (g3Ph2.object! p2Bear)) false (cause := testCause))
  let g3PhEot : Game := g3Ph3.clearEOT
  let g3PhNext : Game := g3PhEot.expireUntilNextTurnEffects ⟨2⟩
  let phasedControlAndDepartedRulesOk : Bool :=
    (g3PhEot.object! (g3PhEot.followMoved p2Bear)).zone == .exile &&
    !g3PhNext.activeEffects.any (fun (_, s) =>
      match s with
      | .playerRule q _ _ => q == ⟨2⟩
      | .layered _ (.copy ..) (.untilEndOfNextTurnOf q) => q == ⟨2⟩
      | _ => false) &&
    (g3PhNext.object! p0Hero).name == hero.name

  -- 9d. CR 614.12 Arwen (`othersEnterWithPlusOneEqualToughness`) simultaneous batch vs subsequent entry:
  let arwen18 : CardDef := { bear with name := "Phase18 Arwen", toughness := some 3, staticAbilities := #[.othersEnterWithPlusOneEqualToughness] }
  let gArw0 : Game := insertObject (insertObject (insertObject afterDraw arwen18 me (.hand me)) bear me (.hand me))
    { bear with name := "Phase18 Later Bear" } me (.hand me)
  let hIds := (gArw0.player me).hand
  let laterId := hIds.back!
  let simBearId := hIds[hIds.size - 2]!
  let arwId := hIds[hIds.size - 3]!
  let gArwSim : Game :=
    gArw0.withBatch (some testCause) fun g =>
      let (g, _) := g.putOntoBattlefield arwId me (cause := some testCause)
      (g.putOntoBattlefield simBearId me (cause := some testCause)).1
  let (gArwSeq, _) := gArwSim.putOntoBattlefield laterId me (cause := some testCause)
  let simBearPerm := (gArwSeq.permanentsOf me).filter (·.name == bear.name)
  let laterBearPerm := (gArwSeq.permanentsOf me).filter (·.name == "Phase18 Later Bear")
  let arwenPreBfOk : Bool :=
    simBearPerm.size == 1 && simBearPerm[0]!.status.plusOnePlusOne == 0 &&
    laterBearPerm.size == 1 && laterBearPerm[0]!.status.plusOnePlusOne == 3

  -- 9e. CR 102.2 / 508.4c / 810.7 Two-Headed Giant with no living opponents: entering-attacking, `markAttacking`, `.leastPower`, and stamped player `AttackTarget`s never attack or damage self/teammate!
  let g2hgConceded : Game := (mkTwoHeadedGiant18.concede ⟨2⟩).concede ⟨3⟩
  let g2hgNoOpp : Game :=
    match Start.start {
      seats := #[
        { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
        { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ }
      ]
      format := .constructed
      seed := 180
      startingPlayer := some 0
    } with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let (g2hgTokCreated, createdTok2hg) := g2hgNoOpp.createOneToken ⟨0⟩ bear (attacking := true) (cause := some testCause)
  let g2hgHand1 : Game := insertObject g2hgTokCreated hero ⟨1⟩ (.hand ⟨1⟩)
  let h1CardId := (g2hgHand1.player ⟨1⟩).hand.back!
  let (g2hgPutAtk, putId2hg) := g2hgHand1.move h1CardId .battlefield (some ⟨1⟩) (attacking := true) (cause := some testCause)
  let g2hgMarked : Game := g2hgPutAtk.markAttacking putId2hg (cause := some testCause)
  let g2hgPrompted : Game :=
    g2hgMarked.promptEnteringAttackItems #[.token ⟨0⟩ .spirit false (g2hgMarked.legalEnteringAttackTargets ⟨0⟩)] (cause := some testCause)
  let g2hgSacStacked : Game :=
    g2hgPrompted.putTriggeredAbilityOnStack ⟨0⟩ (g2hgPrompted.object! createdTok2hg.id)
      (TriggeredAbility.mkTrigger .thisAttacks (Effect.ofTrigger .defenderSacsLeastPower)) "attack" (eventCause := some testCause)
  let g2hgAfterLeastSac : Game := g2hgSacStacked.resolveTop
  let noOppEnteringSafeOk : Bool :=
    g2hgConceded.over &&
    g2hgConceded.beginStep .declareBlockers == g2hgConceded &&
    !g2hgNoOpp.over &&
    (g2hgNoOpp.livingOpponents ⟨0⟩).isEmpty &&
    (g2hgNoOpp.livingOpponents ⟨1⟩).isEmpty &&
    (g2hgNoOpp.legalEnteringAttackTargets ⟨0⟩).isEmpty &&
    (g2hgNoOpp.legalEnteringAttackTargets ⟨1⟩).isEmpty &&
    !(g2hgTokCreated.object! createdTok2hg.id).status.attacking &&
    (g2hgTokCreated.object! createdTok2hg.id).status.attackingTarget.isNone &&
    !(g2hgPutAtk.object! putId2hg).status.attacking &&
    (g2hgPutAtk.object! putId2hg).status.attackingTarget.isNone &&
    !(g2hgMarked.object! putId2hg).status.attacking &&
    !g2hgPrompted.battlefield.any (·.status.attacking) &&
    (g2hgAfterLeastSac.permanentsOf ⟨0⟩).size == (g2hgPrompted.permanentsOf ⟨0⟩).size &&
    (g2hgAfterLeastSac.permanentsOf ⟨1⟩).size == (g2hgPrompted.permanentsOf ⟨1⟩).size
  let atk2hgNone : ObjectId := ⟨g2hgNoOpp.nextObjectId⟩
  let tokObjNone : GameObject := {
    id := atk2hgNone
    printed := { bear with isToken := true }
    owner := ⟨0⟩
    controller := some ⟨0⟩
    defaultController := some ⟨0⟩
    zone := .battlefield
    status := { summoningSick := true, attacking := true, attackingTarget := none }
    timestamp := g2hgNoOpp.timestamp + 1
  }
  let g2hgUntargetedAtk : Game :=
    g2hgNoOpp.record (GameEvent.created g2hgNoOpp.turnNumber ⟨0⟩ (g2hgNoOpp.snapshot tokObjNone) (cause := testCause))
  let atk2hgSelf : ObjectId := ⟨g2hgUntargetedAtk.nextObjectId⟩
  let tokObjSelf : GameObject := {
    tokObjNone with
    id := atk2hgSelf
    status := { summoningSick := true, attacking := true, attackingTarget := some (.player ⟨0⟩) }
    timestamp := g2hgUntargetedAtk.timestamp + 1
  }
  let g2hgStampedSelf : Game :=
    g2hgUntargetedAtk.record (GameEvent.created g2hgUntargetedAtk.turnNumber ⟨0⟩ (g2hgUntargetedAtk.snapshot tokObjSelf) (cause := testCause))
  let atk2hgMate : ObjectId := ⟨g2hgStampedSelf.nextObjectId⟩
  let tokObjMate : GameObject := {
    tokObjNone with
    id := atk2hgMate
    status := { summoningSick := true, attacking := true, attackingTarget := some (.player ⟨1⟩) }
    timestamp := g2hgStampedSelf.timestamp + 1
  }
  let g2hgStampedBoth : Game :=
    g2hgStampedSelf.record (GameEvent.created g2hgStampedSelf.turnNumber ⟨0⟩ (g2hgStampedSelf.snapshot tokObjMate) (cause := testCause))
  let p0LifePre := (g2hgStampedBoth.player ⟨0⟩).life
  let p1LifePre := (g2hgStampedBoth.player ⟨1⟩).life
  let g2hgBlockStep : Game := g2hgStampedBoth.beginStep .declareBlockers
  let g2hgCombatStep : Game := g2hgBlockStep.beginStep .combatDamage
  let twoHeadedNoOppSafeOk : Bool :=
    noOppEnteringSafeOk &&
    g2hgNoOpp.opponent ⟨0⟩ == ⟨0⟩ &&
    g2hgNoOpp.opponent ⟨1⟩ == ⟨1⟩ &&
    !(g2hgNoOpp.resolveAttackDestination ⟨0⟩ none).isOk &&
    !(g2hgNoOpp.resolveAttackDestination ⟨1⟩ none).isOk &&
    g2hgUntargetedAtk.defendingPlayer == ⟨0⟩ &&
    !g2hgStampedBoth.hasLiveAttackDestination (g2hgStampedBoth.object! atk2hgNone) &&
    !g2hgStampedBoth.hasLiveAttackDestination (g2hgStampedBoth.object! atk2hgSelf) &&
    !g2hgStampedBoth.hasLiveAttackDestination (g2hgStampedBoth.object! atk2hgMate) &&
    g2hgBlockStep.step == .declareBlockers &&
    g2hgBlockStep.blockersQueue.isEmpty &&
    g2hgBlockStep.pending == .none &&
    g2hgBlockStep.priority == ⟨0⟩ &&
    (g2hgCombatStep.player ⟨0⟩).life == p0LifePre &&
    (g2hgCombatStep.player ⟨1⟩).life == p1LifePre

  mustHold18 "9a.turnStartBeforePhaseOk" turnStartBeforePhaseOk &&
  mustHold18 "9b.durationAndExpiryOk" durationAndExpiryOk &&
  mustHold18 "9c.phasedControlAndDepartedRulesOk" phasedControlAndDepartedRulesOk &&
  mustHold18 "9d.arwenPreBfOk" arwenPreBfOk &&
  mustHold18 "9e.twoHeadedNoOppSafeOk" twoHeadedNoOppSafeOk &&
  mustHold18 "9.replay" ([gBt2, gDuPhased, gDuCounterRemoved, gDuSrcMoved, g3PhEot, g3PhNext, gArwSim, gArwSeq, g2hgConceded, g2hgNoOpp, g2hgTokCreated, g2hgMarked, g2hgPrompted, g2hgAfterLeastSac, g2hgStampedBoth, g2hgBlockStep, g2hgCombatStep].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase18EventAlignment

section Phase19EventAlignment

def opp19 : PlayerId := ⟨1⟩

def mustHold19 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 19 guard failed: {label}"

def mkThreePlayer19 (seed : UInt64 := 19) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 24).advanceStep
  | .error e => panic! e

def mkTwoHeadedGiant19 (seed : UInt64 := 219) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 30).advanceStep
  | .error e => panic! e

-- 1. `Damage.gainLife` 3-replacement pause/resume ordering & phased-out Ring-bearer retention.
#guard
  -- 1a. CR 616.1f–g: 3 competing `.modifyLifeGain` effects (`+ 3`, `* 2`, `* 4`) on gaining 2 life:
  --     picking `* 2` first (`2 * 2 = 4`, leaving non-commuting `{+ 3, * 4}`), then `+ 3` (`4 + 3 = 7`),
  --     then auto-applying `* 4` (`7 * 4 = 28`) yields `20 + 28 = 48` life without re-applying `* 2` or restarting from `2`!
  let idAdd3 : ReplacementId := { kind := .addLifeGain, object := some ⟨901⟩ }
  let idMul2 : ReplacementId := { kind := .multiplyLifeGain, object := some ⟨902⟩ }
  let idMul4 : ReplacementId := { kind := .multiplyLifeGain, object := some ⟨903⟩ }
  let gGl0 : Game :=
    ((afterDraw.createEffect
      (.replacement { id := idAdd3, affectedPlayer := me, kind := .modifyLifeGain me 3 1 })
      (cause := some testCause)).createEffect
      (.replacement { id := idMul2, affectedPlayer := me, kind := .modifyLifeGain me 0 2 })
      (cause := some testCause)).createEffect
      (.replacement { id := idMul4, affectedPlayer := me, kind := .modifyLifeGain me 0 4 })
      (cause := some testCause)
  let gGlPause1 : Game := gGl0.gainLife me 2 (cause := some testCause)
  let gGlPause2 : Game := mustApply gGlPause1 me (.chooseReplacement idMul2)
  let gGlDone : Game := mustApply gGlPause2 me (.chooseReplacement idAdd3)
  let gainLifeOrderOk : Bool :=
    (match gGlPause1.pending with | .chooseReplacement p cs => p == me && cs.size == 3 | _ => false) &&
    (match gGlPause2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 && !cs.contains idMul2 | _ => false) &&
    gGlDone.pending == .none &&
    (gGlDone.player me).life == 48

  -- 1b. CR 702.26b,g / 701.54a: phasing out a Ring-bearer keeps `ringBearerId` without emitting
  --     `PermanentEvent.designation _ .ringBearer false`, treats `isRingBearer` as `false` while phased out,
  --     and restores `isRingBearer == true` once phased in!
  let gRb0 : Game := addPermanent afterDraw bear me me
  let rbId := (gRb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gRb1 : Game := gRb0.setRingBearer me (some rbId) (cause := some testCause)
  let prePhaseIdx := gRb1.events.size
  let gRbPhased : Game :=
    gRb1.withBatch (some testCause) fun g =>
      g.record (GameEvent.phasedOut g.turnNumber (g.snapshot (g.object! rbId)) false (cause := testCause))
  let hadClearOnPhaseOut := (gRbPhased.events.extract prePhaseIdx gRbPhased.events.size).any fun e =>
    match e.change with
    | .rules (.permanent (.designation _ .ringBearer false)) => true
    | _ => false
  let gRbPhasedIn : Game :=
    gRbPhased.withBatch (some testCause) fun g =>
      g.record (GameEvent.phasedIn g.turnNumber (g.snapshot (g.object! rbId)) (cause := testCause))
  let phasedRingBearerOk : Bool :=
    gRb1.isRingBearer me (gRb1.object! rbId) &&
    !hadClearOnPhaseOut &&
    (gRbPhased.player me).ringBearerId == some rbId &&
    !gRbPhased.isRingBearer me (gRbPhased.object! rbId) &&
    (gRbPhasedIn.player me).ringBearerId == some rbId &&
    gRbPhasedIn.isRingBearer me (gRbPhasedIn.object! rbId)

  mustHold19 "1a.gainLifeOrderOk" gainLifeOrderOk &&
  mustHold19 "1b.phasedRingBearerOk" phasedRingBearerOk &&
  mustHold19 "1.replay" ([gGlPause1, gGlPause2, gGlDone, gRbPhased, gRbPhasedIn].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. Pause-safety of `applyRiddlesPiles`, `returnLinkedExileToHand`, multiplayer idle-priority `concede`, & `.payWard` decline.
#guard
  -- 2a. `applyRiddlesPiles` pauses cleanly per card on competing graveyard->exile replacements without dropping remaining cards!
  let idExA : ReplacementId := { kind := .exileOppDeath, object := some ⟨910⟩ }
  let idExB : ReplacementId := { kind := .exileOppDeath, object := some ⟨911⟩ }
  let gRid0 : Game :=
    (afterDraw.createEffect
      (.replacement { id := idExA, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)).createEffect
      (.replacement { id := idExB, affectedPlayer := me, kind := .exileInsteadOfGraveyard none false })
      (cause := some testCause)
  let lib := (gRid0.player me).library
  let c1 := lib[lib.size - 1]!
  let c2 := lib[lib.size - 2]!
  let c3 := lib[lib.size - 3]!
  let gRidP1 : Game := gRid0.applyRiddlesPiles me #[c1, c2] #[c3] true
  let gRidP2 : Game := mustApply gRidP1 me (.chooseReplacement idExA)
  let gRidDone : Game := mustApply gRidP2 me (.chooseReplacement idExB)
  let riddlesPauseOk : Bool :=
    (match gRidP1.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    (gRidP1.object! c2).zone == .library me &&
    (match gRidP2.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gRidDone.pending == .none &&
    (gRidDone.followMovedToZone? c1 (· == .exile)).isSome &&
    (gRidDone.followMovedToZone? c2 (· == .exile)).isSome &&
    (gRidDone.followMovedToZone? c3 (· == .hand me)).isSome

  -- 2b. `returnLinkedExileToHand` clears `linkedExile` across `Pending.chooseReplacement` only after arrival,
  --     and preserves `linkedExile` when an exiled token cannot move out of exile (CR 111.8)!
  let sagaDummy : CardDef := { name := "Phase19 Link Saga", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gLk0 : Game := addPermanent (insertObject afterDraw bear me .exile) sagaDummy me me
  let sagaId := (gLk0.battlefield.filter (·.name == "Phase19 Link Saga"))[0]!.id
  let exCardId := (gLk0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let gLk1 : Game := gLk0.change (.object sagaId (.pushLinkedExile exCardId))
  let gLkReturned : Game := gLk1.returnLinkedExileToHand (some sagaId)
  -- Exiled token (`CR 111.8`): `move` leaves it in exile, so `linkedExile` is not falsely cleared or logged returned!
  let (gTokLk0, tokLk) := (addPermanent afterDraw sagaDummy me me).createOneToken me { bear with name := "Phase19 Link Tok" }
    (cause := some testCause)
  let sagaTokId := (gTokLk0.battlefield.filter (·.name == "Phase19 Link Saga"))[0]!.id
  let (gTokLk1, exTokId) := gTokLk0.move tokLk.id .exile none (cause := some testCause)
  let gTokLk2 : Game := gTokLk1.change (.object sagaTokId (.pushLinkedExile exTokId))
  let gTokLkBlocked : Game := gTokLk2.returnLinkedExileToHand (some sagaTokId)
  let linkedReturnOk : Bool :=
    (gLkReturned.object! sagaId).linkedExile.isEmpty &&
    (gLkReturned.followMovedToZone? exCardId (· == .hand me)).isSome &&
    (gTokLkBlocked.object! sagaTokId).linkedExile == #[exTokId] &&
    (gTokLkBlocked.object! exTokId).zone == .exile

  -- 2c. Multiplayer idle-priority `concede`:
  --     (i) when `⟨0⟩` & `⟨1⟩` already passed (`consecutivePasses == 2`) and `⟨2⟩` concedes, step advances cleanly;
  --     (ii) when `⟨2⟩` controlled a legendary permanent owned by `⟨1⟩` and `⟨1⟩` already controls an identical legend,
  --          `concede ⟨2⟩` pauses on `chooseLegend` instead of advancing the step early!
  let g3Idle0 : Game := mkThreePlayer19 42
  let stepBefore := g3Idle0.step
  let g3Passed2 : Game := mustApply (mustApply g3Idle0 ⟨0⟩ .pass) ⟨1⟩ .pass
  let g3ConcedeAdv : Game := g3Passed2.concede ⟨2⟩
  let legDef19 : CardDef := { bear with name := "Phase19 Legend", supertypes := #[.legendary] }
  let g3Leg0 : Game := addPermanent (addPermanent (mkThreePlayer19 43) legDef19 ⟨1⟩ ⟨1⟩) legDef19 ⟨1⟩ ⟨1⟩
  let legIds := (g3Leg0.battlefield.filter (·.name == "Phase19 Legend")).map (·.id)
  let g3Leg1 : Game := g3Leg0.changeControl (g3Leg0.object! legIds[1]!) ⟨2⟩ (untilEot := true) (cause := some testCause)
  let g3LegPassed : Game := mustApply (mustApply g3Leg1 ⟨0⟩ .pass) ⟨1⟩ .pass
  let g3LegPaused : Game := g3LegPassed.concede ⟨2⟩
  let g3LegResolved : Game := mustApply g3LegPaused ⟨1⟩ (.keepLegend legIds[0]!)
  let concedeIdleOk : Bool :=
    g3ConcedeAdv.step != stepBefore &&
    g3LegPaused.step == g3LegPassed.step &&
    g3LegPaused.legendChoicePending? &&
    g3LegResolved.pending == .none

  -- 2d. `Decisions.decline` on `.payWard` clears `g.pending` and runs outer `pendingReplacement`!
  let gWd0 : Game := addPermanent (insertObject afterDraw lightningBolt me (.hand me)) bear opp19 opp19
  let boltId := (gWd0.player me).hand.back!
  let wardSrcId := (gWd0.battlefield.filter (·.name == bear.name))[0]!.id
  let (gWd1, boltStackId) := gWd0.move boltId .stack (some me) (verb := some .cast) (actor := some me)
    (cause := some (.gameRule .spellCast))
  let gWd1 : Game :=
    gWd1.change (.pushStack { objectId := boltStackId, controller := me, targets := #[Target.permanent wardSrcId], targetsAnnounced := true })
  let gWd2 : Game :=
    gWd1.changes #[
      .priority opp19,
      .pending (.payWard me boltStackId (CostSpec.ofGeneric 2)),
      .pendingReplacement (some (.receivePriority me))]
  let gWdDeclined : Game := mustApply gWd2 me .decline
  let wardDeclineOk : Bool :=
    gWdDeclined.pending == .none &&
    gWdDeclined.stack.isEmpty &&
    gWdDeclined.priority == me

  mustHold19 "2a.riddlesPauseOk" riddlesPauseOk &&
  mustHold19 "2b.linkedReturnOk" linkedReturnOk &&
  mustHold19 "2c.concedeIdleOk" concedeIdleOk &&
  mustHold19 "2d.wardDeclineOk" wardDeclineOk &&
  mustHold19 "2.replay" ([gRidP1, gRidP2, gRidDone, gLkReturned, gTokLkBlocked, g3ConcedeAdv, g3LegPaused, g3LegResolved, gWdDeclined].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. `Damage.markDamageOn` non-creature planeswalker damage, clamped loyalty removal, & lifelink provenance.
#guard
  -- 3a. Non-creature planeswalker dealt 2 damage loses 2 loyalty WITHOUT `DamageEvent.marked`, so animating into
  --     a 2/2 creature later in the turn does NOT destroy it via CR 704.5g!
  let pwDef19 : CardDef := {
    name := "Phase19 Walker"
    manaCost := ManaCost.empty
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 5
  }
  let gPw0 : Game := addPermanent afterDraw pwDef19 me me
  let pwId := (gPw0.battlefield.filter (·.name == "Phase19 Walker"))[0]!.id
  let gPw0 : Game := gPw0.recordPutCounters pwId .loyalty 5 (some me) (cause := some testCause)
  let gPwDmg : Game := gPw0.markDamageOn (gPw0.object! pwId) 2 "2 dmg to walker" (cause := some testCause)
  let gPwAnim : Game :=
    (gPwDmg.setUntilEotForm (gPwDmg.object! pwId) (2, 2) (#[] : Array KeywordAbility) "becomes 2/2 creature"
      (additionalCreature := true)).checkSBA
  -- 3b. Clamped loyalty removal: 2 loyalty dealt 5 damage removes 2 (not 5); 0 loyalty dealt 3 damage emits 0 counter events!
  let gPwClamp0 : Game := addPermanent afterDraw pwDef19 me me
  let pwClampId := (gPwClamp0.battlefield.filter (·.name == "Phase19 Walker"))[0]!.id
  let gPwClamp1 : Game := gPwClamp0.recordPutCounters pwClampId .loyalty 2 (some me) (cause := some testCause)
  let preClampIdx := gPwClamp1.events.size
  let gPwClamp2 : Game := gPwClamp1.markDamageOn (gPwClamp1.object! pwClampId) 5 "5 dmg to 2-loyalty walker" (cause := some testCause)
  let removedAmts := (gPwClamp2.events.extract preClampIdx gPwClamp2.events.size).filterMap fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .loyalty (.removed k) _)) => some k
    | _ => none
  let preZeroLoyIdx := gPwClamp2.events.size
  let gPwZeroLoy : Game := gPwClamp2.markDamageOn (gPwClamp2.object! pwClampId) 3 "3 dmg at 0 loyalty" (cause := some testCause)
  let zeroLoyEvents := (gPwZeroLoy.events.extract preZeroLoyIdx gPwZeroLoy.events.size).filter fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .loyalty (.removed _) _)) => true
    | _ => false
  let pwDamageAndLoyaltyOk : Bool :=
    (gPwDmg.object! pwId).status.counterCount .loyalty == 3 &&
    (gPwDmg.object! pwId).status.damage == 0 &&
    gPwAnim.battlefield.any (·.id == pwId) &&
    removedAmts == #[2] &&
    zeroLoyEvents.isEmpty

  -- 3c. Lifelink noncombat damage under `.multiplyDamage` passes `rep.cause` (`EventCause.replaced`) into `gainLife`!
  let llDef19 : CardDef := { bear with name := "Phase19 Lifelinker", keywords := #[Keyword.lifelink] }
  let gLl0 : Game := addPermanent afterDraw llDef19 me me
  let llId := (gLl0.battlefield.filter (·.name == "Phase19 Lifelinker"))[0]!.id
  let idMulDmg : ReplacementId := { kind := .multiplyDamage, object := some llId }
  let gLl1 : Game :=
    gLl0.createEffect (.replacement { id := idMulDmg, source := some llId, controller := some me,
                                      affectedPlayer := opp19, kind := .multiplyDamage (some llId) 2 })
      (cause := some testCause)
  let preLlIdx := gLl1.events.size
  let gLlDone : Game :=
    gLl1.dealDamageToPlayer opp19 2 (source := some (gLl1.object! llId)) (cause := some testCause)
  let gainedReplaced := (gLlDone.events.extract preLlIdx gLlDone.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.gained p 4)), some (.replaced r _) => p == me && r == idMulDmg
    | _, _ => false

  mustHold19 "3ab.pwDamageAndLoyaltyOk" pwDamageAndLoyaltyOk &&
  mustHold19 "3c.gainedReplaced" gainedReplaced &&
  mustHold19 "3.replay" ([gPwDmg, gPwAnim, gPwClamp2, gPwZeroLoy, gLlDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 118.9 `payLifeEqualManaValue`, CR 119.4b/8 `canPayLife` & `payLifeCost`, `forObject`, & `.library`/`.command` `fromZone`.
#guard
  -- 4a. CR 118.9 / 601.2g: 0-MV exiled spell with `payLifeEqualManaValue` casts for 0 life;
  --     2-MV exiled spell with `payLifeEqualManaValue` and 0 mana in pool proposes cleanly, opens
  --     `.activateManaAbilities me`, and pays 2 life with `forObject == some spellId` on `.pay`!
  let mv2Bear : CardDef := creature "Phase19 2MV Bear" (ManaCost.ofGeneric 2) #["Bear"] 2 2
  let gPl0 : Game := insertObject (insertObject afterDraw bear me .exile) mv2Bear me .exile
  let exZeroId := (gPl0.objects.filter (fun o => o.name == bear.name && o.zone == .exile))[0]!.id
  let exTwoId := (gPl0.objects.filter (fun o => o.name == "Phase19 2MV Bear" && o.zone == .exile))[0]!.id
  let gPl1 : Game :=
    (gPl0.createEffect
      (.playPermission exZeroId { player := me, whileExiled := true, payLifeEqualManaValue := true })
      (cause := some testCause)).createEffect
      (.playPermission exTwoId { player := me, whileExiled := true, payLifeEqualManaValue := true })
      (cause := some testCause)
  let gCastZero : Game := mustApply gPl1 me (.cast exZeroId)
  let gCastTwoProp : Game := mustApply gPl1 me (.cast exTwoId)
  let twoStackId := gCastTwoProp.stack.back!.objectId
  let preAcceptIdx := gCastTwoProp.events.size
  let gCastTwoPaid : Game := mustApply gCastTwoProp me .pay
  let paidForSpell := (gCastTwoPaid.events.extract preAcceptIdx gCastTwoPaid.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.lost p 2 false)), some (.costPayment .life payer (some oid)) =>
      p == me && payer == me && oid == twoStackId
    | _, _ => false
  let payLifeMvOk : Bool :=
    gCastZero.pending == .none &&
    (gCastZero.player me).life == 20 &&
    gCastZero.stack.size == 1 &&
    gCastTwoProp.pending == .activateManaAbilities me &&
    (gCastTwoPaid.player me).life == 18 &&
    paidForSpell

  -- 4b. CR 119.4b / 119.8: `canPayLife` & `payLifeCost` forbid `n > 0` under `lifeCantChange` / `lifeLocked` while allowing `0`!
  let gLc : Game := afterDraw.createEffect (.lifeCantChange me) (cause := some testCause)
  let lifeLockCostOk : Bool :=
    gLc.canPayLife me 0 &&
    !gLc.canPayLife me 1 &&
    (gLc.payLifeCost me 0).isOk &&
    !(gLc.payLifeCost me 1).isOk

  -- 4c. `offerMayPayPick` with `sourceId := none` never leaks `noSourceSentinelId` into `forObject`;
  --     `activateManaAbility` on a `tapPayLifeAddOneOf` land stamps `forObject := some landId`!
  let painLand19 : CardDef := {
    name := "Phase19 Pain Land"
    manaCost := ManaCost.empty
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.oneOf (.explicit #[.colored .red, .colored .green]) (.const 1))
      (CostSpec.ofItems #[.tapSelf, .payLife (.const 1)])]
  }
  let gMp0 : Game := addPermanent afterDraw painLand19 me me
  let landId := (gMp0.battlefield.filter (·.name == "Phase19 Pain Land"))[0]!.id
  let preLandIdx := gMp0.events.size
  let gLandPaid : Game := mustApply gMp0 me (.activateManaAbility landId 0 #[.colored .red] #[])
  let landForObjOk := (gLandPaid.events.extract preLandIdx gLandPaid.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.lost _ 1 false)), some (.costPayment .life _ (some oid)) => oid == landId
    | _, _ => false
  let discId := (afterDraw.player me).hand.back!
  let gSourceless0 : Game :=
    (afterDraw.change (.pushContinuationFrame {})).offerMayPayPick me none .discardACard "Discard a card?"
  let preSlIdx := gSourceless0.events.size
  let gSourcelessPaid : Game := mustApply gSourceless0 me (.choosePermanents #[discId])
  let sourcelessForObjOk := (gSourcelessPaid.events.extract preSlIdx gSourcelessPaid.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) ..)), some (.costPayment .discard _ forObj) => forObj == none
    | _, _ => false

  -- 4d. `CastEvent.spellCast` records actual `.library` `fromZone` when casting from top of library!
  let topCasterDef : CardDef := { bear with name := "Phase19 Top Caster", staticAbilities := #[.mayCastCreaturesFromTop] }
  let gLib0 : Game := insertObject (addPermanent afterDraw topCasterDef me me) bear me (.library me)
  let topBearId := (gLib0.player me).library.back!
  let preLibCastIdx := gLib0.events.size
  let gLibCast : Game := mustApply gLib0 me (.cast topBearId)
  let libFromZoneOk := (gLibCast.events.extract preLibCastIdx gLibCast.events.size).any fun e =>
    match e.change with
    | .rules (.cast (.spellCast _ p z)) => p == me && z == .library me
    | _ => false

  mustHold19 "4a.payLifeMvOk" payLifeMvOk &&
  mustHold19 "4b.lifeLockCostOk" lifeLockCostOk &&
  mustHold19 "4c.forObjOk" (landForObjOk && sourcelessForObjOk) &&
  mustHold19 "4d.libFromZoneOk" libFromZoneOk &&
  mustHold19 "4.replay" ([gCastZero, gCastTwoProp, gCastTwoPaid, gLc, gLandPaid, gSourcelessPaid, gLibCast].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. CR 603.3b–d per-trigger target prompting, departed-token `.stackTriggerUnusedMode`, 0-mode `announced`,
--    `applyHydeMode` Mode 1 on non-`+1/+1` counters, departed-opponent noncombat damage, & `.gainLifePlusOnes` protection.
#guard
  -- 5a. Ordered `putTriggerBatch` where trigger 1 requires a target and trigger 2 is untargeted:
  --     trigger 1 is placed on `g.stack` and prompts `chooseTargets me` BEFORE trigger 2 enters `g.stack`,
  --     and answering the target places trigger 2 without re-prompting `chooseTriggerToStack`!
  let tgtPingTrig : TriggeredAbility :=
    TriggeredAbility.mkTrigger .thisEnters {
      targeting := .of .opponent
      body := Instruction.dealDamageFixed (.targetSlot 0) 1
      phrase := "When this enters, deal 1 damage to target opponent."
    }
  let drawTrig : TriggeredAbility := .onEnterDraw 1
  let dualEnterDef : CardDef := {
    bear with
    name := "Phase19 Dual Enter"
    triggeredAbilities := #[tgtPingTrig, drawTrig]
  }
  let gTb0 : Game := insertObject afterDraw dualEnterDef me (.hand me)
  let deHandId := (gTb0.player me).hand.back!
  let gTbCast : Game := mustApply gTb0 me (.cast deHandId)
  let gTbOrderPrompt : Game := mustApply (mustApply gTbCast me .pass) opp19 .pass
  let gTbAfterOrder : Game := mustApply gTbOrderPrompt me (.stackTriggers #[0, 1])
  let gTbAfterTarget : Game := mustApply gTbAfterOrder me (.target (Target.player opp19))
  let perTriggerBatchOk : Bool :=
    gTbOrderPrompt.pending == .chooseTriggerToStack me &&
    gTbAfterOrder.pending == .chooseTargets me &&
    gTbAfterOrder.stack.size == 1 &&
    gTbAfterOrder.waitingTriggers.size == 1 &&
    gTbAfterOrder.waitingTriggers[0]!.ordered &&
    gTbAfterTarget.pending == .none &&
    gTbAfterTarget.stack.size == 2 &&
    gTbAfterTarget.waitingTriggers.isEmpty

  -- 5b. Departed-token `.stackTriggerUnusedMode` records `TriggerQueueEvent.modeChosen` even after `ceaseToExist`,
  --     and 0-mode `.chooseUpToXModes` (`chosenX := 0`) + `.upToTriggerModes` `.decline` emit `CastEvent.announced #[]`!
  let unusedAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.ofTrigger .gollumMode)
  let (gTokU0, tokU) := afterDraw.createOneToken me { bear with name := "Phase19 Mode Token", triggeredAbilities := #[unusedAb] }
    (cause := some testCause)
  let gTokU1 : Game := gTokU0.ceaseToExist tokU.id (cause := some testCause)
  let gTokU2 : Game := gTokU1.putTriggeredAbilityOnStack me tokU unusedAb "triggers" (eventCause := some testCause)
  let preUnusedIdx := gTokU2.events.size
  let gTokUModeChosen : Game := mustApply gTokU2 me (.chooseMode 0)
  let unusedModeRecorded := (gTokUModeChosen.events.extract preUnusedIdx gTokUModeChosen.events.size).any fun e =>
    match e.change with
    | .rules (.triggerQueue (.modeChosen sid 0 true)) => sid == tokU.id
    | _ => false
  let upToAb : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters Effect.enterChooseUpToXModes
  let xZeroSrc : GameObject := { (afterDraw.object! (afterDraw.player me).library[0]!) with chosenX := some 0 }
  let preX0Idx := afterDraw.events.size
  let gX0 : Game := afterDraw.putTriggeredAbilityOnStack me xZeroSrc upToAb "enters" (eventCause := some testCause)
  let x0Announced := (gX0.events.extract preX0Idx gX0.events.size).any fun e =>
    match e.change with
    | .rules (.cast (.announced _ #[] _ _)) => true
    | _ => false
  let xOneSrc : GameObject := { xZeroSrc with chosenX := some 1 }
  let gX1 : Game := afterDraw.putTriggeredAbilityOnStack me xOneSrc upToAb "enters" (eventCause := some testCause)
  let preDeclineIdx := gX1.events.size
  let gX1Declined : Game := mustApply gX1 me .decline
  let x1DeclineAnnounced := (gX1Declined.events.extract preDeclineIdx gX1Declined.events.size).any fun e =>
    match e.change with
    | .rules (.cast (.announced _ #[] _ _)) => true
    | _ => false

  -- 5c. `applyHydeMode` Mode 1 removes a non-`+1/+1` counter (`.shield`) from a creature and draws 1 card!
  let gHy0 : Game := addPermanent afterDraw bear me me
  let hyBear := (gHy0.battlefield.filter (·.name == bear.name))[0]!.id
  let gHy1 : Game := gHy0.recordPutCounters hyBear .shield 1 (some me) (cause := some testCause)
  let handBeforeHy := (gHy1.player me).hand.size
  let gHyDone : Game :=
    gHy1.withBatch (some testCause) fun g =>
      g.applyHydeMode me (some hyBear) 1 #[Target.permanent hyBear]
  let hydeShieldOk : Bool :=
    (gHyDone.object! hyBear).status.shield == 0 &&
    (gHyDone.player me).hand.size == handBeforeHy + 1

  -- 5d. CR 800.4i departed-opponent `condOpponentDealtNoncombatDamageLastTurn` & `.gainLifePlusOnes` `sourceId` protection!
  let g3Nc0 : Game := mkThreePlayer19 44
  let g3Nc1 : Game := g3Nc0.dealDamageToPlayer ⟨1⟩ 2 (cause := some testCause)
  let g3Nc2 : Game := (g3Nc1.concede ⟨1⟩).startNextTurnAndBegin
  let depOppHeld := g3Nc2.evalTriggerCond ⟨0⟩ none none TriggeredAbility.condOpponentDealtNoncombatDamageLastTurn
  let proWhiteBear : CardDef := { bear with name := "Phase19 ProWhite Bear", keywords := #[.protection (.color (.literal .white))] }
  let whiteWatcher : CardDef := {
    bear with
    name := "Phase19 White Watcher"
    manaCost := ManaCost.ofColor .white
    triggeredAbilities := #[TriggeredAbility.mkTrigger (.gainLife .you) (Effect.ofTrigger (.resource .gainLifePlusOnes))]
  }
  let gPwProt0 : Game := addPermanent (addPermanent afterDraw proWhiteBear me me) whiteWatcher me me
  let pwBearId := (gPwProt0.battlefield.filter (·.name == "Phase19 ProWhite Bear"))[0]!.id
  let wSrc := gPwProt0.battlefield.filter (·.name == "Phase19 White Watcher") |>.getD 0 default
  let protTargetingOk : Bool :=
    !(gPwProt0.legalTriggerTargets me wSrc.printed.triggeredAbilities[0]! (some wSrc.id)).contains (Target.permanent pwBearId)

  mustHold19 "5a.perTriggerBatchOk" perTriggerBatchOk &&
  mustHold19 "5b.modesAndAnnouncedOk" (unusedModeRecorded && x0Announced && x1DeclineAnnounced) &&
  mustHold19 "5c.hydeShieldOk" hydeShieldOk &&
  mustHold19 "5d.depOppAndProtOk" (depOppHeld && protTargetingOk) &&
  mustHold19 "5.replay" ([gTbOrderPrompt, gTbAfterOrder, gTbAfterTarget, gTokUModeChosen, gX0, gX1Declined, gHyDone, g3Nc2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 707.10c / 800.4d copy-retarget guards & CR 608.2b multi-target / shared-constraint legality.
#guard
  -- 6a. `copyCastTriggerSpell`: untargeted spell skips `.newTargetsForCopies`; `lost` controller skips `.newTargetsForCopies`;
  --     and a copy whose original target became hexproof may `.decline` to keep its illegal target (CR 707.10c)!
  let untargetedSorcery : CardDef := {
    name := "Phase19 Untargeted Draw"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card." }
  }
  let gCp0 : Game := addPermanent (insertObject afterDraw untargetedSorcery me (.hand me)) bear me me
  let cpSrc := (gCp0.battlefield.filter (·.name == bear.name))[0]!
  let uId := (gCp0.player me).hand.back!
  let (gCp1, uStackId) := gCp0.move uId .stack (some me) (verb := some .cast) (actor := some me) (cause := some testCause)
  let gCp1 : Game := gCp1.putStackEntry me uStackId
  let gCp1 : Game := gCp1.putTriggeredAbilityOnStack me cpSrc (.onEnterDraw 1) "cast"
    (cause := some (gCp1.object! uStackId)) (eventCause := some testCause)
  let gCp1 : Game := gCp1.changes #[.pushContinuationFrame {}, .resolvingAbility (some gCp1.stack.back!.objectId)]
  let gCpUntargeted : Game := gCp1.copyCastTriggerSpell me
  -- Targeted spell copied while original target gained hexproof: `.decline` keeps unchanged target!
  let gCpT0 : Game := addPermanent (addPermanent (insertObject afterDraw lightningBolt me (.hand me)) bear opp19 opp19) hero me me
  let cpTSrc := (gCpT0.battlefield.filter (·.name == hero.name))[0]!
  let bHand := (gCpT0.player me).hand.back!
  let oppBear := (gCpT0.battlefield.filter (·.name == bear.name))[0]!.id
  let (gCpT1, bStackId) := gCpT0.move bHand .stack (some me) (verb := some .cast) (actor := some me) (cause := some testCause)
  let gCpT1 : Game :=
    gCpT1.change (.pushStack { objectId := bStackId, controller := me, targets := #[Target.permanent oppBear], targetsAnnounced := true })
  let gCpT1 : Game := gCpT1.createEffect (.keywordsUntilEot oppBear #[Keyword.hexproof]) (cause := some testCause)
  let gCpT2 : Game := gCpT1.putTriggeredAbilityOnStack me cpTSrc (.onEnterDraw 1) "cast"
    (cause := some (gCpT1.object! bStackId)) (eventCause := some testCause)
  let gCpT2 : Game := gCpT2.changes #[.pushContinuationFrame {}, .resolvingAbility (some gCpT2.stack.back!.objectId)]
  let gCpTPrompt : Game := gCpT2.copyCastTriggerSpell me
  let gCpTDeclined : Game := mustApply gCpTPrompt me .decline
  -- `lost` controller skips `.newTargetsForCopies` (CR 800.4d):
  let gCpLost : Game :=
    (gCpT2.record (GameEvent.playerLost gCpT2.turnNumber me .conceded (cause := some testCause))).copyCastTriggerSpell me
  let copyGuardsOk : Bool :=
    gCpUntargeted.pending == Pending.none &&
    gCpUntargeted.stack.size == 3 &&
    (match gCpTPrompt.pending with | .fraChoice p (.newTargetsForCopies _) => p == me | _ => false) &&
    gCpTDeclined.pending == Pending.none &&
    gCpLost.pending == Pending.none

  -- 6b. CR 608.2b shared-constraint legality (`targetsAllIllegalForSpec` on `.twoNonlandsSharingType` &
  --     `.upToTwoCreaturesTotalMvAtMost 3`) + `putPalantirInfluence` player legality!
  let enchDef19 : CardDef := { name := "Phase19 Enchantment", manaCost := ManaCost.empty, types := #[.enchantment] }
  let gSh0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) hero me me) enchDef19 me me
  let shBear := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let shHero := (gSh0.battlefield.filter (·.name == hero.name))[0]!.id
  let shEnch := (gSh0.battlefield.filter (·.name == "Phase19 Enchantment"))[0]!.id
  let (gShOneLeft, _) := gSh0.move shHero (.graveyard me) none (cause := some testCause)
  let twoMvA : CardDef := creature "Phase19 2MV A" (ManaCost.ofGeneric 2) #["Bear"] 2 2
  let twoMvB : CardDef := creature "Phase19 2MV B" (ManaCost.ofGeneric 2) #["Bear"] 2 2
  let gMv0 : Game := addPermanent (addPermanent afterDraw twoMvA opp19 opp19) twoMvB opp19 opp19
  let mvAId := (gMv0.battlefield.filter (·.name == "Phase19 2MV A"))[0]!.id
  let mvBId := (gMv0.battlefield.filter (·.name == "Phase19 2MV B"))[0]!.id
  let gPal0 : Game := (addPermanent afterDraw { enchDef19 with name := "Phase19 Palantir" } me me).createEffect
    (.protectionFromEverything opp19) (cause := some testCause)
  let palId := (gPal0.battlefield.filter (·.name == "Phase19 Palantir"))[0]!.id
  let (gPalRefused, palRes) := gPal0.putPalantirInfluence palId (some opp19)
  let sharedLegalityOk : Bool :=
    !gSh0.targetsAllIllegalForSpec me .twoNonlandsSharingType #[Target.permanent shBear, Target.permanent shHero] &&
    gSh0.targetsAllIllegalForSpec me .twoNonlandsSharingType #[Target.permanent shBear, Target.permanent shEnch] &&
    !gShOneLeft.targetsAllIllegalForSpec me .twoNonlandsSharingType #[Target.permanent shBear, Target.permanent shHero] &&
    gMv0.targetsAllIllegalForSpec me (.upToTwoCreaturesTotalMvAtMost 3) #[Target.permanent mvAId, Target.permanent mvBId] &&
    !gMv0.targetsAllIllegalForSpec me (.upToTwoCreaturesTotalMvAtMost 4) #[Target.permanent mvAId, Target.permanent mvBId] &&
    palRes.isNone

  mustHold19 "6a.copyGuardsOk" copyGuardsOk &&
  mustHold19 "6b.sharedLegalityOk" sharedLegalityOk &&
  mustHold19 "6.replay" ([gCpUntargeted, gCpTPrompt, gCpTDeclined, gCpLost, gShOneLeft, gPalRefused].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 704.5e off-stack copy zone moves, CR 303.4f–g non-cast Aura `putOntoBattlefield`, & batched `Pumps`.
#guard
  -- 7a. CR 704.5e / 707.10f / 707.12:
  --     (i) permanent spell copy resolving onto `.battlefield` becomes a token (`isToken == true`) and survives `checkSBA`;
  --     (ii) countered spell copy moved again (`.graveyard` -> `.hand`) before `checkSBA` keeps `isCopy == true` and ceases to exist in `checkSBA`!
  let gSc0 : Game := insertObject afterDraw bear me (.hand me)
  let bCardId := (gSc0.player me).hand.back!
  let gScCast : Game := mustApply gSc0 me (.cast bCardId)
  let origSpellObj := gScCast.object! gScCast.stack.back!.objectId
  let (gScCopied, _) := gScCast.copyStackSpellWithId origSpellObj me
  let gScPermResolved : Game := (gScCopied.resolveTop).checkSBA
  -- Countered copy moved `.stack` -> `.graveyard` -> `.hand` before SBAs:
  let (gScCopied2, gyCopyOpt) := gScCast.copyStackSpellWithId origSpellObj me
  let gyCopyId := gyCopyOpt.getD ⟨0⟩
  let (gCopyGy, gyArrId) := gScCopied2.move gyCopyId (.graveyard me) none (cause := some testCause)
  let (gCopyHand, handArrId) := gCopyGy.move gyArrId (.hand me) none (cause := some testCause)
  let gCopySba : Game := gCopyHand.checkSBA
  let offStackCopyOk : Bool :=
    gyCopyOpt.isSome &&
    (gScPermResolved.permanentsOf me).any (fun o => o.name == bear.name && o.printed.isToken) &&
    (gCopyGy.object! gyArrId).isCopy &&
    (gCopyHand.object! handArrId).isCopy &&
    (gCopySba.findObject? handArrId).isNone &&
    !(gCopySba.player me).hand.contains handArrId

  -- 7b. CR 303.4f–g single-card non-cast Aura `putOntoBattlefield`:
  --     0 hosts -> stays in graveyard; 1 hexproof opponent host -> attaches without targeting; 2 hosts -> prompts `.asEntersAttachAura`!
  let testAura19 : CardDef := aura "Phase19 Aura" (ManaCost.ofColor .green) "Enchant creature"
  let hexBear19 : CardDef := { bear with name := "Phase19 Hex Host", keywords := #[Keyword.hexproof] }
  let gAuZero0 : Game := insertObject afterDraw testAura19 me (.graveyard me)
  let auZeroId := (gAuZero0.player me).graveyard.back!
  let (gAuZeroDone, _) := gAuZero0.putOntoBattlefield auZeroId me (cause := some testCause)
  let gAuOne0 : Game := addPermanent (insertObject afterDraw testAura19 me (.graveyard me)) hexBear19 opp19 opp19
  let auOneId := (gAuOne0.player me).graveyard.back!
  let hexHostId := (gAuOne0.battlefield.filter (·.name == "Phase19 Hex Host"))[0]!.id
  let (gAuOneDone, auEnteredId) := gAuOne0.putOntoBattlefield auOneId me (cause := some testCause)
  let gAuTwo0 : Game := addPermanent (insertObject gAuOne0 testAura19 me (.graveyard me)) bear me me
  let myHostId := (gAuTwo0.battlefield.filter (·.name == bear.name))[0]!.id
  let auTwoCardId := (gAuTwo0.player me).graveyard.back!
  let (gAuTwoPrompt, _) := gAuTwo0.putOntoBattlefield auTwoCardId me (cause := some testCause)
  let gAuTwoDone : Game :=
    match gAuTwoPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura myHostId) |>.getD cs[0]!
      mustApply gAuTwoPrompt me (.chooseReplacement pick)
    | _ => gAuTwoPrompt
  let singleAuraPutOk : Bool :=
    (gAuZeroDone.object! auZeroId).zone == .graveyard me &&
    (gAuOneDone.object! auEnteredId).isOnBattlefield &&
    (gAuOneDone.object! auEnteredId).attachedTo == some hexHostId &&
    (match gAuTwoPrompt.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gAuTwoDone.pending == .none &&
    gAuTwoDone.battlefield.any (fun o => o.name == "Phase19 Aura" && o.attachedTo == some myHostId)

  -- 7c. Batched `Pumps.pumpPermanent` (`trample := true`) & `Pumps.grantUntilEotKeywords` share one `BatchId`!
  let gPm0 : Game := addPermanent afterDraw bear me me
  let pmBear := (gPm0.battlefield.filter (·.name == bear.name))[0]!.id
  let prePmIdx := gPm0.events.size
  let gPm1 : Game := gPm0.pumpPermanent (gPm0.object! pmBear) 2 2 (trample := true)
  let pmBatches := (gPm1.events.extract prePmIdx gPm1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.continuousEffect (.created ..)) => some e.batch
    | _ => none
  let preKwIdx := gPm1.events.size
  let gPm2 : Game := gPm1.grantUntilEotKeywords (gPm1.object! pmBear) [Keyword.flying, Keyword.vigilance]
  let kwBatches := (gPm2.events.extract preKwIdx gPm2.events.size).filterMap fun e =>
    match e.change with
    | .rules (.continuousEffect (.created ..)) => some e.batch
    | _ => none
  let batchedPumpsOk : Bool :=
    pmBatches.size == 2 && pmBatches[0]!.isSome && pmBatches[0]! == pmBatches[1]! &&
    kwBatches.size == 2 && kwBatches[0]!.isSome && kwBatches[0]! == kwBatches[1]!

  mustHold19 "7a.offStackCopyOk" offStackCopyOk &&
  mustHold19 "7b.singleAuraPutOk" singleAuraPutOk &&
  mustHold19 "7c.batchedPumpsOk" batchedPumpsOk &&
  mustHold19 "7.replay" ([gScPermResolved, gCopyGy, gCopyHand, gCopySba, gAuZeroDone, gAuOneDone, gAuTwoPrompt, gAuTwoDone, gPm1, gPm2].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 701.15b goad & `leftoverFlyingRestriction`, CR 508.8 combat step-skip fidelity,
--    CR 810 Two-Headed Giant Hexproof/Ward, CR 723.1 `playerControl` window/expiry, & `hasActiveEffect` `durationActive`.
#guard
  -- 8a. CR 701.15b goad non-goader player attacks & `leftoverFlyingRestriction`:
  --     in a 3-player game (`⟨0⟩` active, `⟨1⟩` goader with planeswalker `pw1`, `⟨2⟩` other opponent),
  --     a creature goaded by `⟨1⟩` MUST attack `⟨2⟩` (attacking `pw1` or `⟨1⟩` is illegal while attacking `⟨2⟩` is legal)!
  let pwGoadDef : CardDef := {
    name := "Phase19 Goader PW"
    manaCost := ManaCost.empty
    supertypes := #[.legendary]
    types := #[.planeswalker]
    subtypes := #["Jace"]
    loyalty := some 3
  }
  let gGd0 : Game := addPermanent (addPermanent (mkThreePlayer19 45) { bear with keywords := #[Keyword.haste] } ⟨0⟩ ⟨0⟩) pwGoadDef ⟨1⟩ ⟨1⟩
  let gdAtk := (gGd0.battlefield.filter (·.name == bear.name))[0]!.id
  let gdPw := (gGd0.battlefield.filter (·.name == "Phase19 Goader PW"))[0]!.id
  let gGd0 : Game :=
    (gGd0.recordPutCounters gdPw .loyalty 3 (some ⟨1⟩) (cause := some testCause)).record
      (GameEvent.designation gGd0.turnNumber (gGd0.snapshot (gGd0.object! gdAtk)) (.goaded ⟨1⟩ true) true (cause := testCause))
  let gGd1 : Game := gGd0.beginStep .beginningOfCombat
  let gGd1 : Game := mustApply (mustApply (mustApply gGd1 ⟨0⟩ .pass) ⟨1⟩ .pass) ⟨2⟩ .pass
  let attackPwRejected := !(gGd1.apply ⟨0⟩ (.declareAttackers #[gdAtk] (some ⟨1⟩) #[] #[some gdPw])).isOk
  let attackGoaderRejected := !(gGd1.apply ⟨0⟩ (.declareAttackers #[gdAtk] (some ⟨1⟩) #[] #[none])).isOk
  let gGdAttackP2 : Game := mustApply gGd1 ⟨0⟩ (.declareAttackers #[gdAtk] (some ⟨2⟩) #[] #[none])
  -- `leftoverFlyingRestriction`: flying `.attacksEachCombatIfAble` creature is NOT forced to attack `opp` who has `.flyingCantAttackYouOrBlockYours`,
  -- unless `opp` controls a planeswalker (or when `opp` controls no planeswalker, `declareAttackers #[]` succeeds)!
  let moatLikeDef : CardDef := {
    name := "Phase19 AntiFlyer"
    manaCost := ManaCost.empty
    types := #[.enchantment]
    staticAbilities := #[.flyingCantAttackYouOrBlockYours]
  }
  let mustFlyerDef : CardDef := {
    bear with
    name := "Phase19 Must Flyer"
    keywords := #[Keyword.flying, Keyword.haste]
    staticAbilities := #[.attacksEachCombatIfAble]
  }
  let gFl0 : Game := addPermanent (addPermanent afterDraw mustFlyerDef me me) moatLikeDef opp19 opp19
  let gFl1 : Game := mustApply (mustApply (gFl0.beginStep .beginningOfCombat) me .pass) opp19 .pass
  let gFlNoAtk : Game := mustApply gFl1 me (.declareAttackers #[] none #[] #[])
  let goadAndFlyerOk : Bool :=
    attackPwRejected && attackGoaderRejected &&
    (gGdAttackP2.object! gdAtk).status.attackingTarget == some (.player ⟨2⟩) &&
    gFlNoAtk.pending == .none

  -- 8b. CR 508.8 / 509.1 / 510.1 combat step-skip fidelity:
  --     0 attackers declared skips to `.endOfCombat`, whereas 1 attacker declared then exiled during `.declareAttackers`
  --     priority still enters `.declareBlockers` and `.combatDamage` (with NO empty `CombatEvent.damageAssigned`)!
  let gSkZero : Game := mustApply (mustApply gFlNoAtk me .pass) opp19 .pass
  let gSk0 : Game := addPermanent afterDraw { bear with keywords := #[Keyword.haste] } me me
  let skAtk := (gSk0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSk1 : Game := mustApply (mustApply (gSk0.beginStep .beginningOfCombat) me .pass) opp19 .pass
  let gSk2 : Game := mustApply gSk1 me (.declareAttackers #[skAtk] none #[] #[])
  let (gSk3, _) := gSk2.move skAtk .exile none (cause := some testCause)
  let gSkBlk : Game := mustApply (mustApply gSk3 me .pass) opp19 .pass
  let preDmgStepIdx := gSkBlk.events.size
  let gSkDmg : Game := mustApply (mustApply gSkBlk me .pass) opp19 .pass
  let hadEmptyDmgAssigned := (gSkDmg.events.extract preDmgStepIdx gSkDmg.events.size).any fun e =>
    match e.change with
    | .rules (.combat (.damageAssigned ..)) => true
    | _ => false
  let combatSkipFidelityOk : Bool :=
    gSkZero.step == .endOfCombat &&
    gSkBlk.step == .declareBlockers &&
    gSkBlk.pending == .none &&
    gSkDmg.step == .combatDamage &&
    gSkDmg.pending == .none &&
    !hadEmptyDmgAssigned

  -- 8c. CR 810 Two-Headed Giant Hexproof / Ward teammate vs opponent checks!
  let wardBear19 : CardDef := { bear with name := "Phase19 Ward Bear", keywords := #[.ward (CostSpec.ofGeneric 2)] }
  let hexBear2hg : CardDef := { bear with name := "Phase19 2HG Hex", keywords := #[Keyword.hexproof] }
  let freePing19 : CardDef := { lightningBolt with name := "Phase19 Free Ping", manaCost := ManaCost.empty }
  let g2h0 : Game := addPermanent (addPermanent mkTwoHeadedGiant19 wardBear19 ⟨1⟩ ⟨1⟩) hexBear2hg ⟨2⟩ ⟨2⟩
  let wbId := (g2h0.battlefield.filter (·.name == "Phase19 Ward Bear"))[0]!.id
  let hbId := (g2h0.battlefield.filter (·.name == "Phase19 2HG Hex"))[0]!.id
  let g2hBoltMate0 : Game := insertObject g2h0 freePing19 ⟨0⟩ (.hand ⟨0⟩)
  let bMateCard := (g2hBoltMate0.player ⟨0⟩).hand.back!
  let g2hMateCast : Game := mustApply (mustApply g2hBoltMate0 ⟨0⟩ (.cast bMateCard)) ⟨0⟩ (.target (Target.permanent wbId))
  let g2hBoltOpp0 : Game := (insertObject g2h0 freePing19 ⟨2⟩ (.hand ⟨2⟩)).change (.priority ⟨2⟩)
  let bOppCard := (g2hBoltOpp0.player ⟨2⟩).hand.back!
  let g2hOppCast : Game := mustApply (mustApply g2hBoltOpp0 ⟨2⟩ (.cast bOppCard)) ⟨2⟩ (.target (Target.permanent wbId))
  let twoHeadedHexWardOk : Bool :=
    !g2h0.canBeTargetedBy ⟨0⟩ (g2h0.object! hbId) &&
    !g2h0.canBeTargetedBy ⟨1⟩ (g2h0.object! hbId) &&
    g2h0.canBeTargetedBy ⟨3⟩ (g2h0.object! hbId) &&
    g2hMateCast.pending == .none &&
    g2hMateCast.stack.size == 1 &&
    g2hOppCast.pending == .none &&
    g2hOppCast.stack.size == 2

  -- 8d. CR 723.1 `playerControl` (`onNextTurn == true` vs `false`) & `Core.hasActiveEffect` `durationActive`!
  let gPcNext0 : Game := afterDraw.createEffect (.playerControl me opp19 true) (cause := some testCause)
  let gPcNextOpp : Game := gPcNext0.startNextTurnAndBegin
  let gPcNextAfter : Game := gPcNextOpp.startNextTurnAndBegin
  let gPcNow0 : Game := afterDraw.createEffect (.playerControl me opp19 false) (cause := some testCause)
  let gPcNowEot : Game := gPcNow0.clearEOT
  let gHa0 : Game := addPermanent afterDraw bear me me
  let haSrc := (gHa0.battlefield.filter (·.name == bear.name))[0]!.id
  let addLandSpec : ContinuousEffectSpec := .playerRule me (.additionalLands 1) (.whileSourceOnBattlefield haSrc)
  let gHa1 : Game := gHa0.createEffect addLandSpec (cause := some testCause)
  let gHaPhased : Game := gHa1.record (GameEvent.phasedOut gHa1.turnNumber (gHa1.snapshot (gHa1.object! haSrc)) false (cause := testCause))
  let gHaPhasedIn : Game := gHaPhased.record (GameEvent.phasedIn gHaPhased.turnNumber (gHaPhased.snapshot (gHaPhased.object! haSrc)) (cause := testCause))
  let ctrlAndDurationActiveOk : Bool :=
    !gPcNext0.controlsPlayer me opp19 &&
    !gPcNext0.controlOnNextTakenTurn.isEmpty &&
    gPcNextOpp.controlsPlayer me opp19 &&
    !gPcNextAfter.controlsPlayer me opp19 &&
    gPcNextAfter.controlOnNextTakenTurn.isEmpty &&
    gPcNow0.controlsPlayer me opp19 &&
    !gPcNowEot.controlsPlayer me opp19 &&
    gHa1.hasActiveEffect addLandSpec &&
    !gHaPhased.hasActiveEffect addLandSpec &&
    gHaPhasedIn.hasActiveEffect addLandSpec

  mustHold19 "8a.goadAndFlyerOk" goadAndFlyerOk &&
  mustHold19 "8b.combatSkipFidelityOk" combatSkipFidelityOk &&
  mustHold19 "8c.twoHeadedHexWardOk" twoHeadedHexWardOk &&
  mustHold19 "8d.ctrlAndDurationActiveOk" ctrlAndDurationActiveOk &&
  mustHold19 "8.replay" ([gGdAttackP2, gFlNoAtk, gSkZero, gSkBlk, gSkDmg, g2hMateCast, g2hOppCast, gPcNext0, gPcNextOpp, gPcNextAfter, gPcNow0, gPcNowEot, gHa1, gHaPhased, gHaPhasedIn].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase19EventAlignment

section Phase20EventAlignment

def opp20 : PlayerId := ⟨1⟩

def mustHold20 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase 20 guard failed: {label}"

def mkThreePlayer20 (seed : UInt64 := 20) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck },
      { name := "Nissa", deck := testGreenDeck },
      { name := "Liliana", deck := testRedDeck }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 24).advanceStep
  | .error e => panic! e

def mkTwoHeadedGiant20 (seed : UInt64 := 220) : Game :=
  let cfg : StartConfig := {
    seats := #[
      { name := "Chandra", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "Nissa", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "Liliana", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "Jace", deck := testGreenDeck, teammate := some ⟨2⟩ }
    ]
    format := .constructed
    seed
    startingPlayer := some 0
  }
  match Start.start cfg with
  | .ok g => (keepOpeningHands g 30).advanceStep
  | .error e => panic! e

-- 1. Unified CR 303.4f–g,i `.asEntersAttachAura` across multi-card (`returnLinkedExile`),
--    token (`createToken`), CR 616.1c–d (`entersAsCopy` / `entersBackFaceUp`) Aura entries,
--    and Adventure spell copies (`obj.isCopy` ceasing to exist on `.stack` without `.playPermission`, CR 704.5e / 707.10 / 715.3d).
#guard
  let testAura20 : CardDef := aura "Phase20 Aura" (ManaCost.ofColor .green) "Enchant creature"
  let auraTokenDef20 : CardDef := { testAura20 with name := "Phase20 Aura Token", isToken := true }
  -- 1a. Multi-card `returnLinkedExile`: returning an Aura + a creature simultaneously when 2 hosts exist prompts `.asEntersAttachAura`!
  let gRet0 : Game :=
    addPermanent (addPermanent (addPermanent afterDraw bear me me) hero opp20 opp20)
      { bear with name := "Phase20 Jailer" } me me
  let hostA := (gRet0.battlefield.filter (·.name == bear.name))[0]!.id
  let hostB := (gRet0.battlefield.filter (·.name == hero.name))[0]!.id
  let jailerId := (gRet0.battlefield.filter (·.name == "Phase20 Jailer"))[0]!.id
  let gRet1 : Game := insertObject (insertObject gRet0 testAura20 me .exile) { bear with name := "Phase20 Returned Bear" } me .exile
  let exAuraId := (gRet1.objects.filter (fun o => o.name == "Phase20 Aura" && o.zone == .exile))[0]!.id
  let exBearId := (gRet1.objects.filter (fun o => o.name == "Phase20 Returned Bear" && o.zone == .exile))[0]!.id
  let gRet2 : Game := gRet1.changeObject jailerId (.linkedExile #[exAuraId, exBearId])
  let gRetPrompt : Game := gRet2.returnLinkedExile (gRet2.object! jailerId)
  let retPromptOk :=
    match gRetPrompt.pending with
    | .chooseReplacement p cs =>
      p == me && cs.any (fun r => r.kind == .asEntersAttachAura hostB)
    | _ => false
  let gRetDone : Game :=
    match gRetPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura hostB) |>.getD cs[0]!
      mustApply gRetPrompt me (.chooseReplacement pick)
    | _ => gRetPrompt
  let multiReturnAuraOk : Bool :=
    retPromptOk &&
    gRetDone.pending == .none &&
    gRetDone.battlefield.any (fun o => o.name == "Phase20 Aura" && o.attachedTo == some hostB) &&
    gRetDone.battlefield.any (fun o => o.name == "Phase20 Returned Bear")

  -- 1b. Token Aura via `createToken`: 0 hosts -> does NOT enter `.battlefield`; 2 hosts -> prompts `.asEntersAttachAura`!
  let (gTokZero, _) := afterDraw.createToken me auraTokenDef20 (cause := some testCause)
  let gTokTwo0 : Game := addPermanent (addPermanent afterDraw bear me me) hero opp20 opp20
  let tokHostB := (gTokTwo0.battlefield.filter (·.name == hero.name))[0]!.id
  let (gTokPrompt, _) := gTokTwo0.createToken me auraTokenDef20 (cause := some testCause)
  let gTokDone : Game :=
    match gTokPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura tokHostB) |>.getD cs[0]!
      mustApply gTokPrompt me (.chooseReplacement pick)
    | _ => gTokPrompt
  let tokenAuraOk : Bool :=
    !gTokZero.battlefield.any (·.name == "Phase20 Aura Token") &&
    (match gTokPrompt.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gTokDone.battlefield.any (fun o => o.name == "Phase20 Aura Token" && o.attachedTo == some tokHostB)

  -- 1c. CR 616.1c–d: non-Aura entering as a copy of `testAura20` (and DFC entering back-face-up as Aura) prompts `.asEntersAttachAura`!
  let gCopyAura0 : Game :=
    (insertObject gTokTwo0 bear me (.hand me)).createEffect
      (.replacement { id := { kind := .entersAsCopy }, affectedPlayer := me, kind := .entersAsCopy none testAura20 } .untilEndOfTurn)
      (cause := some testCause)
  let handBearId := (gCopyAura0.player me).hand.back!
  let (gCopyAuraPrompt, _) := gCopyAura0.putOntoBattlefield handBearId me (cause := some testCause)
  let gCopyAuraDone : Game :=
    match gCopyAuraPrompt.pending with
    | .chooseReplacement _ cs =>
      let pick := cs.find? (fun r => r.kind == .asEntersAttachAura hostA) |>.orElse
        (fun _ => cs.find? (fun r => r.kind == .asEntersAttachAura tokHostB)) |>.getD cs[0]!
      mustApply gCopyAuraPrompt me (.chooseReplacement pick)
    | _ => gCopyAuraPrompt
  let dfcBackAura : CardDef := { bear with name := "Phase20 Front Creature", otherFace := some testAura20 }
  let gBackZero0 : Game :=
    (insertObject afterDraw dfcBackAura me (.graveyard me)).createEffect
      (.replacement { id := { kind := .entersBackFaceUp }, affectedPlayer := me, kind := .entersBackFaceUp none } .untilEndOfTurn)
      (cause := some testCause)
  let backGyId := (gBackZero0.player me).graveyard.back!
  let (gBackZeroDone, _) := gBackZero0.putOntoBattlefield backGyId me (cause := some testCause)
  let copyAndBackAuraOk : Bool :=
    (match gCopyAuraPrompt.pending with | .chooseReplacement p cs => p == me && cs.size == 2 | _ => false) &&
    gCopyAuraDone.battlefield.any (fun o => o.name == "Phase20 Aura" && o.attachedTo.isSome) &&
    (gBackZeroDone.object! backGyId).zone == .graveyard me &&
    !gBackZeroDone.battlefield.any (·.name == "Phase20 Aura")

  -- 1d. Adventure spell copy (`obj.isCopy == true`) resolving ceases to exist on `.stack` without `.playPermission` (CR 704.5e / 707.10 / 715.3d)!
  let advSpellFace : AdventureFace := {
    name := "Phase20 Adv Instant"
    manaCost := ManaCost.empty
    types := #[.instant]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let advCardDef : CardDef := { bear with name := "Phase20 Adventurer", adventure := some advSpellFace }
  let gAdv0 : Game := insertObject afterDraw advCardDef me (.hand me)
  let advHandId := (gAdv0.player me).hand.back!
  let gAdvCast : Game := mustApply gAdv0 me (.castAdventure advHandId)
  let origAdvObj := gAdvCast.object! gAdvCast.stack.back!.objectId
  let (gAdvCopied, copyAdvId?) := gAdvCast.copyStackSpellWithId origAdvObj me
  let copyAdvId := copyAdvId?.getD ⟨0⟩
  let preCopyResEffects := gAdvCopied.activeEffects.size
  let gAdvCopyResolved : Game := gAdvCopied.resolveTop
  let gAdvOrigResolved : Game := gAdvCopyResolved.resolveTop
  let adventureCopyOk : Bool :=
    copyAdvId?.isSome &&
    (gAdvCopyResolved.findObject? copyAdvId).isNone &&
    gAdvCopyResolved.activeEffects.size == preCopyResEffects &&
    gAdvOrigResolved.objects.any (fun o => o.name == "Phase20 Adventurer" && o.zone == .exile && (gAdvOrigResolved.playPermission o).isSome)

  mustHold20 "1a.multiReturnAuraOk" multiReturnAuraOk &&
  mustHold20 "1b.tokenAuraOk" tokenAuraOk &&
  mustHold20 "1c.copyAndBackAuraOk" copyAndBackAuraOk &&
  mustHold20 "1d.adventureCopyOk" adventureCopyOk &&
  mustHold20 "1.replay" ([gRetPrompt, gRetDone, gTokZero, gTokPrompt, gTokDone, gCopyAuraPrompt, gCopyAuraDone, gBackZeroDone, gAdvCopied, gAdvCopyResolved, gAdvOrigResolved].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 2. CR 607.2a `leaveTriggerExile` vs CR 610.3 `linkedExile` (`exileSearchedLinked`),
--    departed-source LKI on `onLeaveReturnExiled`, `returnLinkedExileToHand`, and Currency Converter `.currencyReturn`.
#guard
  -- 2a. `exileSearchedLinked` stores `leaveTriggerExile` (NOT `linkedExile`), so source departure does NOT auto-return onto `.battlefield`!
  let gEx0 : Game := addPermanent (insertObject afterDraw plains me (.library me)) { name := "Phase20 Saga Box", types := #[.enchantment] } me me
  let sagaSrcId := (gEx0.battlefield.filter (·.name == "Phase20 Saga Box"))[0]!.id
  let libPlainsId := (gEx0.player me).library.back!
  let gEx1 : Game := gEx0.exileSearchedLinked me libPlainsId (some sagaSrcId) (cause := some testCause)
  let exPlainsId := (gEx1.objects.filter (fun o => o.name == plains.name && o.zone == .exile))[0]!.id
  let sagaObj1 := gEx1.object! sagaSrcId
  let (gSagaGone, _) := gEx1.move sagaSrcId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let leaveTriggerVsLinkedOk : Bool :=
    sagaObj1.leaveTriggerExile == #[exPlainsId] &&
    sagaObj1.linkedExile.isEmpty &&
    (gSagaGone.object! exPlainsId).zone == .exile &&
    !gSagaGone.battlefield.any (·.name == plains.name)

  -- 2b. Departed-source LKI: `returnLinkedExileToHand (some sagaSrcId)` & Currency Converter `.currencyReturn` find exiled cards after source departed!
  let gHandAfterDepart : Game := gSagaGone.returnLinkedExileToHand (some sagaSrcId)
  let gCur0 : Game := addPermanent (insertObject afterDraw plains me (.graveyard me)) { name := "Phase20 Currency Box", types := #[.artifact] } me me
  let curSrcId := (gCur0.battlefield.filter (·.name == "Phase20 Currency Box"))[0]!.id
  let gyPlainsId := (gCur0.player me).graveyard.back!
  let gCur1 : Game := gCur0.exileSearchedLinked me gyPlainsId (some curSrcId) (cause := some testCause)
  let curExId := (gCur1.objects.filter (fun o => o.name == plains.name && o.zone == .exile))[0]!.id
  let (gCurDeparted, _) := gCur1.move curSrcId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let gCurResolved : Game :=
    gCurDeparted.withResolvingContext (some curSrcId) me fun g =>
      g.applyAbilityEffect me currencyConverter.activatedAbilities[1]!.effect #[] (some curSrcId)
  let departedSagaAndCurrencyOk : Bool :=
    (gHandAfterDepart.player me).hand.any (fun id => (gHandAfterDepart.object! id).name == plains.name) &&
    !(gCurResolved.objects.any (fun o => o.id == curExId && o.zone == .exile)) &&
    gCurResolved.battlefield.any (fun o => gCurResolved.hasSubtype o .treasure)

  -- 2c. `onLeaveReturnExiled` reconstructs `leaveTriggerExile` via LKI when `sourceId` has already moved to `.graveyard`!
  let gFh0 : Game := addPermanent (addPermanent afterDraw { bear with name := "Phase20 Hunter" } me me) hero opp20 opp20
  let hunterId := (gFh0.battlefield.filter (·.name == "Phase20 Hunter"))[0]!.id
  let huntedObj := (gFh0.battlefield.filter (·.name == hero.name))[0]!
  let gFh1 : Game := gFh0.exileForLeaveTrigger (some hunterId) huntedObj (cause := some testCause)
  let (gFhDead, _) := gFh1.move hunterId (.graveyard me) none (verb := some .destroy) (cause := some testCause)
  let gFhReturned : Game :=
    gFhDead.withResolvingContext (some hunterId) me fun g =>
      g.applyTriggeredAbility me .onLeaveReturnExiled (some hunterId)
  let departedHunterLkiOk : Bool :=
    !gFhDead.battlefield.any (·.name == hero.name) &&
    gFhReturned.battlefield.any (fun o => o.name == hero.name && o.controller == some opp20)

  mustHold20 "2a.leaveTriggerVsLinkedOk" leaveTriggerVsLinkedOk &&
  mustHold20 "2b.departedSagaAndCurrencyOk" departedSagaAndCurrencyOk &&
  mustHold20 "2c.departedHunterLkiOk" departedHunterLkiOk &&
  mustHold20 "2.replay" ([gEx1, gSagaGone, gHandAfterDepart, gCur1, gCurDeparted, gCurResolved, gFh1, gFhDead, gFhReturned].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 3. `finishConcedePriority` `hasWaitingTriggers` & active-prompt preservation across `concede`,
--    `afterWardResolved` post-ward continuation chaining, and CR 122.1c SBA shield-counter destruction & CR 800.4a departure guards.
#guard
  -- 3a. Active prompt (`Pending.scry`) on `⟨0⟩` is preserved when `⟨1⟩` concedes in 3-player game,
  --     and a `WaitingTrigger` queued on `⟨0⟩` when `⟨2⟩` concedes is flushed onto `g.stack` by `finishConcedePriority`!
  let g3p0 : Game := mkThreePlayer20 301
  let g3pScry : Game := g3p0.beginScry ⟨0⟩ 1
  let g3pAfterConcedePrompt : Game := g3pScry.concede ⟨1⟩
  let promptPreservedOk : Bool :=
    match g3pAfterConcedePrompt.pending with
    | .scry p _ _ => p == ⟨0⟩
    | _ => false
  let diesWatcher : CardDef := {
    bear with
    name := "Phase20 Dies Watcher"
    triggeredAbilities := #[.onEnterDraw 1]
  }
  let g3pTrig0 : Game := addPermanent (addPermanent (mkThreePlayer20 302) diesWatcher ⟨0⟩ ⟨0⟩) bear ⟨0⟩ ⟨2⟩
  -- Give `⟨2⟩` priority and queue a waiting trigger before `⟨2⟩` concedes so `finishConcedePriority` sees `hasWaitingTriggers`:
  let watcherObj := (g3pTrig0.battlefield.filter (·.name == "Phase20 Dies Watcher"))[0]!
  let wtConcede : WaitingTrigger := {
    controller := ⟨0⟩
    source := watcherObj
    ability := .onEnterDraw 1
    pattern := .thisLeaves
    checked := true
    eventCause := testCause
  }
  let g3pTrig1 : Game := (g3pTrig0.change (.priority ⟨2⟩)).recordReflexiveTrigger wtConcede
  let g3pTrigConceded : Game := g3pTrig1.concede ⟨2⟩
  let concedeFlushedTriggersOk : Bool :=
    !g3pTrigConceded.hasWaitingTriggers &&
    g3pTrigConceded.stack.size == 1

  -- 3b. `afterWardResolved` / `finishWardAndDrain`: declining `.payWard` drains an outer `pendingReplacement` continuation!
  let wardTargetDef : CardDef := { bear with name := "Phase20 Ward Host", keywords := #[.ward (CostSpec.ofGeneric 2)] }
  let gWd0 : Game := addPermanent (insertObject afterDraw { lightningBolt with manaCost := ManaCost.empty } me (.hand me)) wardTargetDef opp20 opp20
  let wdHostId := (gWd0.battlefield.filter (·.name == "Phase20 Ward Host"))[0]!.id
  let wdBoltId := (gWd0.player me).hand.back!
  let gWdCast : Game := mustApply (mustApply gWd0 me (.cast wdBoltId)) me (.target (Target.permanent wdHostId))
  let wdTrigEntry := gWdCast.stack.back!
  let gWdPrompt0 : Game := gWdCast.resolveTop
  -- Push a post-ward log continuation into `outerPendingReplacements` and verify declining ward drains it!
  let gWdPrompt : Game := gWdPrompt0.change (.continuation (.pushOuterPendingReplacement (.logMessage "Phase20 post-ward continuation ran")))
  let gWdDeclined : Game := mustApply gWdPrompt me .decline
  let wardContinuationOk : Bool :=
    (gWdCast.object! wdTrigEntry.objectId).triggeredAbility.isSome &&
    gWdDeclined.pending == .none &&
    gWdDeclined.pendingReplacement.isNone &&
    gWdDeclined.outerPendingReplacements.isEmpty &&
    gWdDeclined.log.any (·.contains "Phase20 post-ward continuation ran")

  -- 3c. CR 122.1c SBA shield-counter destruction & CR 800.4a damage/life departure guards!
  let gSh0 : Game := addPermanent afterDraw bear me me
  let shBearId := (gSh0.battlefield.filter (·.name == bear.name))[0]!.id
  let gSh1 : Game :=
    (gSh0.recordPutCounters shBearId .shield 1 (some me) (cause := some testCause)).record
      (GameEvent.damageMarked gSh0.turnNumber shBearId 2 (cause := testCause))
  let preSbaIdx := gSh1.events.size
  let gShAfterSba : Game := gSh1.checkSBA
  let sbaSlice := gShAfterSba.events.extract preSbaIdx gShAfterSba.events.size
  let shieldRemovedIdx? := sbaSlice.findIdx? fun e =>
    match e.change with
    | .rules (.permanent (.counters _ .shield (.removed 1) _)) => true
    | _ => false
  let destroyedIdx? := sbaSlice.findIdx? fun e =>
    match e.change with
    | .rules (.zone (.moved before _ .battlefield (.graveyard _) .destroy _ _ _)) => before.id == some shBearId
    | _ => false
  -- Departure guards on `gainLife`, `loseLife`, `setLife`, `dealDamageToPlayer`:
  let gDep0 : Game := (mkThreePlayer20 303).concede ⟨2⟩
  let preDepEvs := gDep0.events.size
  let gDepAfter : Game :=
    (((gDep0.gainLife ⟨2⟩ 5 (cause := some testCause)).loseLife ⟨2⟩ 3 (cause := some testCause)).setLife
      ⟨2⟩ 10 "set departed" (cause := some testCause)).dealDamageToPlayer ⟨2⟩ 4 (cause := some testCause)
  let sbaShieldAndDepartedLifeOk : Bool :=
    (match shieldRemovedIdx?, destroyedIdx? with | some si, some di => si < di | _, _ => false) &&
    gShAfterSba.log.any (·.contains "A shield counter is removed") &&
    gDepAfter.events.size == preDepEvs

  mustHold20 "3a.promptPreservedOk" promptPreservedOk &&
  mustHold20 "3a.concedeFlushedTriggersOk" concedeFlushedTriggersOk &&
  mustHold20 "3b.wardContinuationOk" wardContinuationOk &&
  mustHold20 "3c.sbaShieldAndDepartedLifeOk" sbaShieldAndDepartedLifeOk &&
  mustHold20 "3.replay" ([g3pAfterConcedePrompt, g3pTrigConceded, gWdDeclined, gShAfterSba, gDepAfter].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 4. CR 601.2b,f,g pre-stack zone cost calculation (`announceX`), `payLife > 0` mana-ability window,
--    `Casting.canCast` (`payLifeEqualManaValue` & `cosmicAwarenessFlash`), and `forObject` provenance.
#guard
  -- 4a. Casting an `{X}{R}` spell from `.exile` while controlling `costReductionNotFromHand := 2`:
  --     `announceX` with `X = 2` evaluates `applyCastCostReductions` against `prop.original.zone == .exile` so `{2}{R}` reduces to `{R}`!
  let reducerDef : CardDef := { bear with name := "Phase20 Exile Reducer", staticAbilities := #[.costReductionNotFromHand 2] }
  let xBurnDef : CardDef := {
    name := "Phase20 X Burn"
    manaCost := { symbols := #[.x, .colored .red] }
    types := #[.sorcery]
    spellEffect := some { body := Instruction.drawFixed 1, phrase := "Draw a card" }
  }
  let gExX0 : Game :=
    (addPermanent (insertObject afterDraw xBurnDef me .exile) reducerDef me me).addMana
      me (.colored .red) 1 (cause := some testCause)
  let exBurnId := (gExX0.objects.filter (fun o => o.name == "Phase20 X Burn" && o.zone == .exile))[0]!.id
  let gExX1 : Game := gExX0.createEffect (.playPermission exBurnId { player := me } 1) (cause := some testCause)
  let gExXCast : Game := mustApply gExX1 me (.cast exBurnId)
  let gExXChosen : Game := mustApply gExXCast me (.chooseX 2)
  let gExXPaid : Game := mustApply gExXChosen me .pay
  let preStackZoneCostOk : Bool :=
    gExXPaid.pending == .none &&
    gExXPaid.stack.size == 1 &&
    (gExXPaid.object! gExXPaid.stack.back!.objectId).chosenX == some 2

  -- 4b. `payLifeEqualManaValue` (`canCast` respects `lifeLocked` / `life < mv`; targeted cast opens `.activateManaAbilities` window and records `forObject`)
  --     & `cosmicAwarenessFlash` checks departed opponents while excluding 2HG teammates!
  let twoMvPingDef : CardDef := {
    lightningBolt with
    name := "Phase20 TwoMV Ping"
    manaCost := ManaCost.ofGeneric 2
  }
  let gLifeCast0 : Game := insertObject afterDraw twoMvPingDef me .exile
  let lifePingId := (gLifeCast0.objects.filter (fun o => o.name == "Phase20 TwoMV Ping" && o.zone == .exile))[0]!.id
  let gLifeCast1 : Game := gLifeCast0.createEffect (.playPermission lifePingId { player := me, payLifeEqualManaValue := true } 1) (cause := some testCause)
  let gLifeLocked : Game := gLifeCast1.createEffect (.lifeCantChange me) (cause := some testCause)
  let gLifeTarget : Game := mustApply (mustApply gLifeCast1 me (.cast lifePingId)) me (.target (Target.player opp20))
  let openedPayWindow := gLifeTarget.pending == .activateManaAbilities me
  let stackedPingId := gLifeTarget.proposedSpell.map (·.spellId) |>.getD ⟨0⟩
  let gLifePaid : Game := mustApply gLifeTarget me .pay
  let lifeCostHasForObj := gLifePaid.events.any fun e =>
    match e.change, e.cause? with
    | .rules (.life (.lost p 2 false false)), some (.costPayment .life q (some oid)) =>
      p == me && q == me && oid == stackedPingId
    | _, _ => false
  -- `cosmicAwarenessFlash`:
  let flashGrantDef : CardDef := {
    name := "Phase20 Cosmic Grant"
    types := #[.enchantment]
    staticAbilities := #[StaticAbility.flashIfOpponentCastThisTurn]
  }
  let gFlash2hg0 : Game := addPermanent mkTwoHeadedGiant20 flashGrantDef ⟨0⟩ ⟨0⟩
  let gFlash2hgMateCast : Game :=
    let g := insertObject gFlash2hg0 { lightningBolt with manaCost := ManaCost.empty } ⟨1⟩ (.hand ⟨1⟩)
    let cid := (g.player ⟨1⟩).hand.back!
    mustApply (mustApply (g.change (.priority ⟨1⟩)) ⟨1⟩ (.cast cid)) ⟨1⟩ (.target (Target.player ⟨2⟩))
  let gFlash3p0 : Game := addPermanent (mkThreePlayer20 402) flashGrantDef ⟨0⟩ ⟨0⟩
  let gFlash3pOppCast : Game :=
    let g := insertObject gFlash3p0 { lightningBolt with manaCost := ManaCost.empty } ⟨2⟩ (.hand ⟨2⟩)
    let cid := (g.player ⟨2⟩).hand.back!
    (mustApply (mustApply (g.change (.priority ⟨2⟩)) ⟨2⟩ (.cast cid)) ⟨2⟩ (.target (Target.player ⟨1⟩))).concede ⟨2⟩
  let lifeCastAndFlashOk : Bool :=
    gLifeCast1.canCast me (gLifeCast1.object! lifePingId) &&
    !gLifeLocked.canCast me (gLifeLocked.object! lifePingId) &&
    openedPayWindow &&
    lifeCostHasForObj &&
    !gFlash2hgMateCast.cosmicAwarenessFlash ⟨0⟩ &&
    gFlash3pOppCast.cosmicAwarenessFlash ⟨0⟩

  -- 4c. Optional mana payment in `FraChoices` (`mayPaySymbolsThen`) threads `forObject := some srcId`!
  let gMayPay0 : Game :=
    (addPermanent afterDraw hero me me).addMana me (.colored .red) 1 (cause := some testCause)
  let mpHeroId := (gMayPay0.battlefield.filter (·.name == hero.name))[0]!.id
  let preMpEvs := gMayPay0.events.size
  let gMayPayDone : Game :=
    gMayPay0.withResolvingContext (some mpHeroId) me fun g =>
      let gPrompt := g.change (.pending (.fraChoice me (.mayPaySymbolsThen #[.colored .red] (.gainLife 1) mpHeroId)))
      match gPrompt.answerFraChoice me .accept with
      | .ok g' => g'
      | .error e => panic! e
  let manaSpentForObjOk := (gMayPayDone.events.extract preMpEvs gMayPayDone.events.size).any fun e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent p _ (some oid))), some (.costPayment .mana q (some oid2)) =>
      p == me && q == me && oid == mpHeroId && oid2 == mpHeroId
    | _, _ => false

  mustHold20 "4a.preStackZoneCostOk" preStackZoneCostOk &&
  mustHold20 "4b.lifeCastAndFlashOk" lifeCastAndFlashOk &&
  mustHold20 "4c.manaSpentForObjOk" manaSpentForObjOk &&
  mustHold20 "4.replay" ([gExXPaid, gLifeLocked, gLifeTarget, gLifePaid, gFlash2hgMateCast, gFlash3pOppCast, gMayPayDone].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 5. Modal `.activatedAbility` `CastEvent.announced`, non-ability modal spell `resolvingModes` cleanup,
--    and `!wt.checked` multi-copy (`prowessTriggers`) `TriggerQueueEvent.triggered`.
#guard
  -- 5a. Modal activated ability emits exactly one `CastEvent.announced` with `modes := #[1]` and respects `sourceId` protection in `modeIsChoosable`!
  let modalActDef : CardDef := {
    name := "Phase20 Modal Rod"
    manaCost := ManaCost.ofColor .red
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.mkModal CostSpec.empty #[
      {
        targeting := .of .creature
        body := Instruction.tap (.target 0)
        phrase := "Tap target creature"
      },
      {
        body := Instruction.drawFixed 1
        phrase := "Draw a card"
      }
    ]]
  }
  let protRedBear : CardDef := {
    bear with
    name := "Phase20 ProtRed Bear"
    keywords := #[.protection (.color (.literal .red))]
  }
  -- Only creature on battlefield has protection from red, so Mode 0 is unchoosable for `modalActDef` (`sourceId`), while Mode 1 is choosable!
  let gModAct0 : Game := addPermanent (addPermanent afterDraw modalActDef me me) protRedBear opp20 opp20
  let rodId := (gModAct0.battlefield.filter (·.name == "Phase20 Modal Rod"))[0]!.id
  let preActIdx := gModAct0.events.size
  let gModAct1 : Game := mustApply gModAct0 me (.activate rodId 0)
  let mode0Rejected := !(gModAct1.apply me (.chooseMode 0)).isOk
  let gModActChosen : Game := mustApply gModAct1 me (.chooseMode 1)
  let actAnnouncedModes := (gModActChosen.events.extract preActIdx gModActChosen.events.size).filterMap fun e =>
    match e.change with
    | .rules (.cast (.announced _ ms _ _)) => some ms
    | _ => none
  let modalActivatedOk : Bool :=
    mode0Rejected &&
    actAnnouncedModes == #[#[1]] &&
    gModActChosen.stack.size == 1

  -- 5b. Non-ability modal spell clears `g.resolvingModes` after resolution!
  let modalSorcery20 : CardDef := {
    name := "Phase20 Modal Sorcery"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellModes := #[
      { body := Instruction.drawFixed 1, phrase := "Draw a card" },
      { body := Instruction.gainLifeFixed 2, phrase := "Gain 2 life" }
    ]
  }
  let gModSp0 : Game := insertObject afterDraw modalSorcery20 me (.hand me)
  let modSpId := (gModSp0.player me).hand.back!
  let gModSpStacked : Game := mustApply (mustApply gModSp0 me (.cast modSpId)) me (.chooseMode 0)
  let gModSpResolved : Game := gModSpStacked.resolveTop
  let resolvingModesClearedOk : Bool :=
    gModSpResolved.resolvingModes.isNone &&
    gModSpResolved.stack.isEmpty

  -- 5c. Double prowess (`prowessInstances := 2`) emits 2 `TriggerQueueEvent.triggered` events!
  let dblProwessDef : CardDef := {
    (creature "Phase20 Twin Monk" ManaCost.empty #["Monk"] 1 2 (keywords := #[Keyword.prowess])) with
    keywords := #[Keyword.prowess, Keyword.prowess]
  }
  let gProw0 : Game := addPermanent (insertObject afterDraw modalSorcery20 me (.hand me)) dblProwessDef me me
  let monkId := (gProw0.battlefield.filter (·.name == "Phase20 Twin Monk"))[0]!.id
  let prowSpId := (gProw0.player me).hand.back!
  let preProwIdx := gProw0.events.size
  let gProwCast : Game := mustApply (mustApply gProw0 me (.cast prowSpId)) me (.chooseMode 1)
  let prowTriggeredCount := (gProwCast.events.extract preProwIdx gProwCast.events.size).filter (fun e =>
    match e.change with
    | .rules (.triggerQueue (.triggered s _ _ _)) => s.id == some monkId
    | _ => false) |>.size
  let doubleProwessTriggeredOk : Bool := prowTriggeredCount == 2

  mustHold20 "5a.modalActivatedOk" modalActivatedOk &&
  mustHold20 "5b.resolvingModesClearedOk" resolvingModesClearedOk &&
  mustHold20 "5c.doubleProwessTriggeredOk" doubleProwessTriggeredOk &&
  mustHold20 "5.replay" ([gModActChosen, gModSpStacked, gModSpResolved, gProwCast].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 6. CR 707.10c `.copySourceSpellXTimes`, `.damageUpToOneAndPlayer` skipped-slot indexing,
--    `Targeting.spellPaidTeamwork` isolation, and CR 701.14b fight/target legality.
#guard
  -- 6a. `copyThisSpellXTimesThenDamage` cast with `X = 2` creates 2 stack copies and offers `.newTargetsForCopies` for both!
  let pbbDef20 : CardDef := {
    name := "Phase20 Barrage"
    manaCost := { symbols := #[.x, .colored .red, .colored .red] }
    types := #[.sorcery]
    spellEffect := some (Effect.copyThisSpellXTimesThenDamage 1)
  }
  let gPbb0 : Game :=
    (addPermanent (addPermanent (insertObject afterDraw pbbDef20 me (.hand me)) bear opp20 opp20) hero opp20 opp20).addMana
      me (.colored .red) 4 (cause := some testCause)
  let pbbHandId := (gPbb0.player me).hand.back!
  let oppBearId := (gPbb0.battlefield.filter (fun o => o.name == bear.name && gPbb0.controlledBy o opp20))[0]!.id
  let oppHeroId := (gPbb0.battlefield.filter (fun o => o.name == hero.name && gPbb0.controlledBy o opp20))[0]!.id
  let gPbbCast : Game :=
    mustApply (mustApply (mustApply (mustApply gPbb0 me (.cast pbbHandId)) me (.chooseX 2)) me (.target (Target.permanent oppBearId))) me .pay
  let gPbbTrigRes : Game := gPbbCast.resolveTop
  let gPbbRetargeted : Game :=
    mustApply (mustApply gPbbTrigRes me (.choosePermanents #[oppHeroId])) me .decline
  let copyXTimesOk : Bool :=
    (match gPbbTrigRes.pending with
     | .fraChoice p (.newTargetsForCopies cs) => p == me && cs.size == 2
     | _ => false) &&
    gPbbRetargeted.pending == .none &&
    gPbbRetargeted.stack.size == 3

  -- 6b. Up-to-one + player damage with slot `0` skipped (`resolvingSkippedSlots := #[0]`) deals 2 damage to `opp20`!
  let upToOneAndPlEff : Effect := {
    targeting := .of (.ofSlots #[
      { domain := .creatureOrPlaneswalker, count := .upTo 1 },
      .of .anyPlayer
    ])
    body := Instruction.dealDamageFixed (.both (.target 0) (.target 1)) 2
    phrase := "Deal 2 damage to up to one target creature or planeswalker and 2 damage to target player"
  }
  let gSkip0 : Game := addPermanent afterDraw bear me me
  let skipSrcId := (gSkip0.battlefield.filter (·.name == bear.name))[0]!.id
  let oppPreLife := (gSkip0.player opp20).life
  let gSkip1 : Game :=
    gSkip0.withResolvingContext (some skipSrcId) me fun g =>
      (g.change (.resolvingSkippedSlots #[0])).applyAbilityEffect
        me upToOneAndPlEff #[Target.player opp20] (some skipSrcId)
  let skippedSlotDamageOk : Bool := (gSkip1.player opp20).life == oppPreLife - 2

  -- 6c. `Targeting.spellPaidTeamwork` returns `false` when an unrelated teamwork spell sits on `g.stack`, and `true` when retargeting a teamwork copy!
  let gTw0 : Game := insertObject afterDraw bear me .stack (some me)
  let twSpId := (gTw0.objects.filter (fun o => o.name == bear.name && o.zone == .stack))[0]!.id
  let gTw1 : Game :=
    (gTw0.putStackEntry me twSpId).record
      (GameEvent.announced gTw0.turnNumber twSpId (costs := #[.teamwork #[⟨10⟩, ⟨11⟩]]))
  let gTwCopyPrompt : Game := gTw1.change (.pending (.fraChoice me (.newTargetsForCopies #[twSpId])))
  let teamworkIsolationOk : Bool :=
    !gTw1.spellPaidTeamwork &&
    gTwCopyPrompt.spellPaidTeamwork

  -- 6d. CR 701.14b fight legality: non-creature artifact or hexproof opponent creature cannot fight!
  let nonCreatureArt : CardDef := { name := "Phase20 Relic", manaCost := ManaCost.empty, types := #[.artifact] }
  let hexOppDef : CardDef := { bear with name := "Phase20 Hex Fighter", keywords := #[Keyword.hexproof] }
  let gFg0 : Game := addPermanent (addPermanent (addPermanent afterDraw bear me me) nonCreatureArt opp20 opp20) hexOppDef opp20 opp20
  let myFighterId := (gFg0.battlefield.filter (fun o => o.name == bear.name && gFg0.controlledBy o me))[0]!.id
  let relicId := (gFg0.battlefield.filter (·.name == "Phase20 Relic"))[0]!.id
  let hexFighterId := (gFg0.battlefield.filter (·.name == "Phase20 Hex Fighter"))[0]!.id
  let gFgRelic : Game := gFg0.applyFight me (some myFighterId) #[Target.permanent relicId] .source .mutual
  let gFgHex : Game := gFg0.applyFight me (some myFighterId) #[Target.permanent hexFighterId] .source .mutual
  let fightLegalityOk : Bool :=
    (gFgRelic.object! myFighterId).status.damage == 0 &&
    gFgRelic.log.back? == some "The target is no longer legal" &&
    (gFgHex.object! myFighterId).status.damage == 0 &&
    gFgHex.log.back? == some "The target is no longer legal"

  mustHold20 "6a.copyXTimesOk" copyXTimesOk &&
  mustHold20 "6b.skippedSlotDamageOk" skippedSlotDamageOk &&
  mustHold20 "6c.teamworkIsolationOk" teamworkIsolationOk &&
  mustHold20 "6d.fightLegalityOk" fightLegalityOk &&
  mustHold20 "6.replay" ([gPbbCast, gPbbTrigRes, gPbbRetargeted, gSkip1, gTw1, gTwCopyPrompt, gFgRelic, gFgHex].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 7. CR 508.8 combat-phase bound, empty-assigner `beginCombatDamageAssignment`,
--    player-only `attackTaxPerCreature`, `Agent.choose` `mustAttackIfAble`, and CR 506.5 `attackingAlone?`.
#guard
  -- 7a. CR 508.8: token created attacking in `.beginningOfCombat` advances into `.declareBlockers` even when `declareAttackers #[]` declares 0;
  --     and an extra `.combat` phase after a prior combat with attackers skips `.declareBlockers` when 0 attack in the extra combat!
  let gBoc0 : Game := afterDraw.beginStep .beginningOfCombat
  let (gBoc1, bocTok) := gBoc0.createOneToken me bear (attacking := true) (cause := some testCause)
  let gBocExiled : Game := (gBoc1.move bocTok.id .exile none (cause := some testCause)).1
  let gBocDecl : Game := mustApply (mustApply gBocExiled me .pass) opp20 .pass
  let gBocZeroDecl : Game := mustApply gBocDecl me (.declareAttackers #[] none #[] #[])
  let gBocAfterDecl : Game := mustApply (mustApply gBocZeroDecl me .pass) opp20 .pass
  -- Extra combat phase after a combat where `skBear` attacked (and was exiled before extra combat):
  let gExCb0 : Game := addPermanent afterDraw { bear with keywords := #[Keyword.haste] } me me
  let exCbAtk := (gExCb0.battlefield.filter (·.name == bear.name))[0]!.id
  let gExCb1 : Game := mustApply (mustApply (gExCb0.beginStep .beginningOfCombat) me .pass) opp20 .pass
  let gExCb2 : Game := mustApply gExCb1 me (.declareAttackers #[exCbAtk] none #[] #[])
  let gExCb3 : Game := ((gExCb2.move exCbAtk .exile none (cause := some testCause)).1).record
    (GameEvent.extraPhaseAdded gExCb2.turnNumber .combat .current (cause := testCause))
  -- Advance out of first combat into postcombat / extra combat `.declareAttackers`:
  let gExCbBlk : Game := mustApply (mustApply gExCb3 me .pass) opp20 .pass
  let gExCbDmg : Game := mustApply (mustApply gExCbBlk me .pass) opp20 .pass
  let gExCbEoc : Game := mustApply (mustApply gExCbDmg me .pass) opp20 .pass
  let gExCb2Boc : Game := mustApply (mustApply gExCbEoc me .pass) opp20 .pass
  let gExCb2Decl : Game := mustApply (mustApply gExCb2Boc me .pass) opp20 .pass
  let gExCb2Zero : Game := mustApply gExCb2Decl me (.declareAttackers #[] none #[] #[])
  let gExCb2After : Game := mustApply (mustApply gExCb2Zero me .pass) opp20 .pass
  let combatPhaseBoundOk : Bool :=
    gBocAfterDecl.step == .declareBlockers &&
    gExCb2Boc.step.phase == .combat &&
    gExCb2Boc.step == .beginningOfCombat &&
    gExCb2After.step == .endOfCombat

  -- 7b. First-strike attacker (with no regular-damage assigners) deals damage in FS step and regular `.combatDamage` step grants priority without prompting!
  let fsHeroDef : CardDef := { bear with name := "Phase20 FS Hero", keywords := #[Keyword.firstStrike, Keyword.haste] }
  let gFs0 : Game := addPermanent afterDraw fsHeroDef me me
  let fsId := (gFs0.battlefield.filter (·.name == "Phase20 FS Hero"))[0]!.id
  let gFs1 : Game := mustApply (mustApply (gFs0.beginStep .beginningOfCombat) me .pass) opp20 .pass
  let gFs2 : Game := mustApply gFs1 me (.declareAttackers #[fsId] none #[] #[])
  let gFsBlk : Game := mustApply (mustApply gFs2 me .pass) opp20 .pass
  let gFsBlkDone : Game := mustApply gFsBlk opp20 (.declareBlockers #[])
  let gFsDmg1 : Game := mustApply (mustApply gFsBlkDone me .pass) opp20 .pass
  let gFsDmg2 : Game := mustApply (mustApply gFsDmg1 me .pass) opp20 .pass
  let fsEmptySecondStepOk : Bool :=
    gFsDmg1.step == .combatDamage &&
    gFsDmg1.pending == .none &&
    (gFsDmg1.player opp20).life == (gFs0.player opp20).life - 2 &&
    gFsDmg2.step == .combatDamage &&
    gFsDmg2.pending == .none &&
    (gFsDmg2.player opp20).life == (gFs0.player opp20).life - 2

  -- 7c. Player-only `attackTaxPerCreature` (attacking planeswalker is untaxed) & `Agent.choose` prioritizes `mustAttackIfAble`!
  let taxEnchDef : CardDef := {
    name := "Phase20 Tax Ench"
    types := #[.enchantment]
    staticAbilities := #[.creaturesCantAttackYouUnlessPayIfEnduringStory 2]
  }
  let pwDef20 : CardDef := {
    name := "Phase20 Target PW"
    types := #[.planeswalker]
    loyalty := some 3
  }
  let mustBearDef : CardDef := {
    bear with
    name := "Phase20 Must Bear"
    keywords := #[Keyword.haste]
    staticAbilities := #[.attacksEachCombatIfAble]
  }
  let gTax0 : Game :=
    (addPermanent (addPermanent (addPermanent (addPermanent afterDraw { bear with keywords := #[Keyword.haste] } me me) mustBearDef me me) taxEnchDef opp20 opp20) pwDef20 opp20 opp20).record
      (GameEvent.gainedDesignation afterDraw.turnNumber opp20 .enduringStory (cause := some testCause))
  let optAtkId := (gTax0.battlefield.filter (fun o => o.name == bear.name && gTax0.controlledBy o me))[0]!.id
  let mustAtkId := (gTax0.battlefield.filter (·.name == "Phase20 Must Bear"))[0]!.id
  let oppPwId := (gTax0.battlefield.filter (·.name == "Phase20 Target PW"))[0]!.id
  let gTax0 : Game := gTax0.recordPutCounters oppPwId .loyalty 3 (some opp20) (cause := some testCause)
  let gTaxDecl : Game := mustApply (mustApply (gTax0.beginStep .beginningOfCombat) me .pass) opp20 .pass
  -- With 0 mana: attacking `opp20` directly fails, while attacking `oppPwId` with both creatures succeeds without paying tax!
  let directPlayerTaxed := !(gTaxDecl.apply me (.declareAttackers #[mustAtkId] (some opp20) #[] #[none])).isOk
  let gPwUntaxed : Game := mustApply gTaxDecl me (.declareAttackers #[optAtkId, mustAtkId] (some opp20) #[] #[some oppPwId, some oppPwId])
  -- With Tomik (`planeswalkersAttackedByOneAtMost`) limiting `oppPwId` to 1 attacker and 0 mana in pool,
  -- `Agent.choose` prioritizes `mustAtkId` (which `mustAttackIfAble`) over `optAtkId`!
  let tomikDef : CardDef := { bear with name := "Phase20 Tomik", staticAbilities := #[.planeswalkersAttackedByOneAtMost] }
  let gTomikDecl : Game := addPermanent gTaxDecl tomikDef opp20 opp20
  let agentPickedMust : Bool :=
    match Agent.choose gTomikDecl me with
    | some act =>
      match gTomikDecl.apply me act with
      | .ok gAfter => (gAfter.object! mustAtkId).status.attacking && !(gAfter.object! optAtkId).status.attacking
      | .error _ => false
    | none => false
  let taxAndAgentOk : Bool :=
    gTaxDecl.attackTaxPerCreature opp20 == 2 &&
    directPlayerTaxed &&
    (gPwUntaxed.object! mustAtkId).status.attackingPlaneswalker? == some oppPwId &&
    agentPickedMust

  -- 7d. CR 506.5 `attackingAlone?`: in 2HG, when both `⟨0⟩` and teammate `⟨1⟩` control 1 attacking creature, neither attacks alone!
  let gAlone0 : Game := addPermanent (addPermanent mkTwoHeadedGiant20 { bear with keywords := #[Keyword.haste] } ⟨0⟩ ⟨0⟩) { hero with keywords := #[Keyword.haste] } ⟨1⟩ ⟨1⟩
  let a0 := (gAlone0.battlefield.filter (·.name == bear.name))[0]!.id
  let a1 := (gAlone0.battlefield.filter (·.name == hero.name))[0]!.id
  let gAloneOne : Game := gAlone0.markAttacking a0 (cause := some testCause)
  let gAloneBoth : Game := gAloneOne.markAttacking a1 (cause := some testCause)
  let attackingAlone2hgOk : Bool :=
    (gAloneOne.attackingAlone? ⟨0⟩).map (·.id) == some a0 &&
    (gAloneBoth.attackingAlone? ⟨0⟩).isNone &&
    (gAloneBoth.attackingAlone? ⟨1⟩).isNone

  mustHold20 "7a.combatPhaseBoundOk" combatPhaseBoundOk &&
  mustHold20 "7b.fsEmptySecondStepOk" fsEmptySecondStepOk &&
  mustHold20 "7c.taxAndAgentOk" taxAndAgentOk &&
  mustHold20 "7d.attackingAlone2hgOk" attackingAlone2hgOk &&
  mustHold20 "7.replay" ([gBocAfterDecl, gExCb2After, gFsDmg1, gFsDmg2, gPwUntaxed, gTomikDecl, gAloneOne, gAloneBoth].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

-- 8. CR 810 Two-Headed Giant win/loss/teammate & CR 800.4i departed-opponent queries,
--    CR 723.1 / 810.5 `playerControl` & self-control limits, and batched `createEffects` / multi-effect helpers.
#guard
  -- 8a. CR 810 Two-Headed Giant:
  --     - Opponent's `opponentsCantWin := true` blocks `.winTheGame` on `⟨0⟩`'s team;
  --     - Teammate's `.opponentsCantCastOnYourTurn` allows teammate `⟨1⟩` to cast while blocking opponent `⟨2⟩`;
  --     - `corruptedToxicLifelink` ignores teammate poison (`>= 3`) and activates on opponent poison (`>= 3`);
  --     - Departed opponent's `loggedNoncombatDamage` still grants `.flyingHasteIfOpponentDealtNoncombat` (CR 800.4i)!
  let cantWinDef : CardDef := { bear with name := "Phase20 NoWin Angel", staticAbilities := #[.cantLoseAndOpponentsCantWin] }
  let abolisherDef : CardDef := { bear with name := "Phase20 Teammate Abolisher", staticAbilities := #[.opponentsCantCastOnYourTurn] }
  let corruptedDef : CardDef := { bear with name := "Phase20 Corrupted Bear", keywords := #[.toxic 1], staticAbilities := #[.corruptedToxicLifelink] }
  let freeInstant20 : CardDef := { name := "Phase20 Free Opt", manaCost := ManaCost.empty, types := #[.instant], spellEffect := some { body := Instruction.gainLifeFixed 1, phrase := "Gain 1 life" } }
  let g2hWin0 : Game := addPermanent (addPermanent (addPermanent mkTwoHeadedGiant20 cantWinDef ⟨2⟩ ⟨2⟩) abolisherDef ⟨0⟩ ⟨0⟩) corruptedDef ⟨0⟩ ⟨0⟩
  let corId := (g2hWin0.battlefield.filter (·.name == "Phase20 Corrupted Bear"))[0]!.id
  let g2hTryWin : Game :=
    g2hWin0.withResolvingContext none ⟨0⟩ fun g =>
      g.applyTriggeredAbility ⟨0⟩ (.onEnterDraw 1) none (resolutionOverride := some .winTheGame)
  let g2hMateSpell0 : Game := (insertObject g2hWin0 freeInstant20 ⟨1⟩ (.hand ⟨1⟩)).change (.priority ⟨1⟩)
  let mateSpId := (g2hMateSpell0.player ⟨1⟩).hand.back!
  let g2hMateCastOk : Game := mustApply g2hMateSpell0 ⟨1⟩ (.cast mateSpId)
  let g2hOppSpell0 : Game := (insertObject g2hWin0 freeInstant20 ⟨2⟩ (.hand ⟨2⟩)).change (.priority ⟨2⟩)
  let oppSpId := (g2hOppSpell0.player ⟨2⟩).hand.back!
  let oppCastBlocked := !(g2hOppSpell0.apply ⟨2⟩ (.cast oppSpId)).isOk
  let g2hMatePoison : Game := g2hWin0.record (GameEvent.poisoned g2hWin0.turnNumber ⟨1⟩ 3 (cause := testCause))
  let g2hOppPoison : Game := g2hMatePoison.record (GameEvent.poisoned g2hMatePoison.turnNumber ⟨2⟩ 3 (cause := testCause))
  -- CR 800.4i departed-opponent `loggedNoncombatDamage`:
  let noncombatFlierDef : CardDef := {
    bear with
    name := "Phase20 Noncombat Flier"
    staticAbilities := #[.flyingHasteIfOpponentDealtNoncombat]
  }
  let gDepDmg0 : Game := addPermanent (mkThreePlayer20 801) noncombatFlierDef ⟨0⟩ ⟨0⟩
  let flierId := (gDepDmg0.battlefield.filter (·.name == "Phase20 Noncombat Flier"))[0]!.id
  let gDepDmg1 : Game := (gDepDmg0.dealDamageToPlayer ⟨2⟩ 1 (cause := some testCause)).concede ⟨2⟩
  let twoHeadedAndDepartedOk : Bool :=
    !g2hTryWin.over &&
    g2hMateCastOk.stack.size == 1 &&
    oppCastBlocked &&
    !g2hMatePoison.hasLifelink (g2hMatePoison.object! corId) &&
    g2hOppPoison.hasLifelink (g2hOppPoison.object! corId) &&
    gDepDmg1.hasFlying (gDepDmg1.object! flierId) &&
    gDepDmg1.hasHaste (gDepDmg1.object! flierId)

  -- 8b. CR 723.1 / 805.4 / 810.2,5 2HG shared-turn `playerControl` expiry, departed-teammate skip,
  --     extra-turn single-turn expiry, & self-control limits (`canChooseOutsideGame`, `canMakeTournamentDecision`)!
  let g2hCtrl0 : Game := mkTwoHeadedGiant20 802
  let g2hCtrl1 : Game :=
    g2hCtrl0.withResolvingContext none ⟨0⟩ fun g =>
      g.setPlayerControl ⟨0⟩ ⟨3⟩ (onNextTurn := true)
  -- `startNextTurnAndBegin` advances `⟨0⟩ -> ⟨1⟩` (still team 0/1), `⟨1⟩ -> ⟨2⟩` (teammate of `⟨3⟩`),
  -- `⟨2⟩ -> ⟨3⟩` (`⟨3⟩`'s own half of that shared turn), and `⟨3⟩ -> ⟨0⟩` (next opposing turn):
  let g2hCtrlMateTurn : Game := g2hCtrl1.startNextTurnAndBegin
  let g2hCtrlTeamSeat1 : Game := g2hCtrlMateTurn.startNextTurnAndBegin
  let g2hCtrlTeamSeat2 : Game := g2hCtrlTeamSeat1.startNextTurnAndBegin
  let g2hCtrlAfterTeamTurn : Game := g2hCtrlTeamSeat2.startNextTurnAndBegin
  -- Skipping a departed teammate `⟨2⟩` keeps `onNextTurn` control of still-living `⟨3⟩` for `⟨3⟩`'s turn:
  let g2hDepMate0 : Game := g2hCtrl1.playerLeavesGame ⟨2⟩
  let g2hDepMateTurn1 : Game := g2hDepMate0.startNextTurnAndBegin
  let g2hDepMateTargetTurn : Game := g2hDepMateTurn1.startNextTurnAndBegin
  let g2hDepMateAfter : Game := g2hDepMateTargetTurn.startNextTurnAndBegin
  -- Consecutive turns of the same non-teammate player (extra turn -> regular turn) still expire after 1 turn:
  let gExCtrl0 : Game :=
    (afterDraw.record (GameEvent.extraTurnAdded afterDraw.turnNumber opp20 .current (cause := testCause))).withResolvingContext none me fun g =>
      g.setPlayerControl me opp20 (onNextTurn := true)
  let gExCtrlTurn1 : Game := gExCtrl0.startNextTurnAndBegin
  let gExCtrlTurn2 : Game := gExCtrlTurn1.startNextTurnAndBegin
  let twoHeadedCtrlAndSelfOk : Bool :=
    g2hCtrl1.log.any (·.contains "Two-Headed Giant team") &&
    !g2hCtrlMateTurn.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat1.activePlayer == ⟨2⟩ &&
    g2hCtrlTeamSeat1.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat1.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    g2hCtrlTeamSeat2.activePlayer == ⟨3⟩ &&
    g2hCtrlTeamSeat2.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat2.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    g2hCtrlAfterTeamTurn.activePlayer == ⟨0⟩ &&
    !g2hCtrlAfterTeamTurn.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    !g2hCtrlAfterTeamTurn.controlsPlayer ⟨0⟩ ⟨2⟩ &&
    g2hCtrlAfterTeamTurn.controlOnNextTakenTurn.isEmpty &&
    !g2hDepMateTurn1.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    g2hDepMateTargetTurn.activePlayer == ⟨3⟩ &&
    g2hDepMateTargetTurn.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    !g2hDepMateAfter.controlsPlayer ⟨0⟩ ⟨3⟩ &&
    gExCtrlTurn1.controlsPlayer me opp20 &&
    !gExCtrlTurn2.controlsPlayer me opp20 &&
    gExCtrlTurn2.controlOnNextTakenTurn.isEmpty &&
    g2hCtrlTeamSeat1.canChooseOutsideGame ⟨0⟩ ⟨0⟩ &&
    !g2hCtrlTeamSeat1.canChooseOutsideGame ⟨0⟩ ⟨3⟩ &&
    g2hCtrlTeamSeat1.canMakeTournamentDecision ⟨0⟩ ⟨0⟩ &&
    !g2hCtrlTeamSeat1.canMakeTournamentDecision ⟨0⟩ ⟨3⟩

  -- 8c. `createEffects` with `effs.size > 1` stamps all created continuous effects with one shared `BatchId`!
  let gBatchEff0 : Game := addPermanent afterDraw bear me me
  let beId := (gBatchEff0.battlefield.filter (·.name == bear.name))[0]!.id
  let preBeIdx := gBatchEff0.events.size
  let gBatchEff1 : Game := gBatchEff0.createEffects #[
    .pump beId 1 1,
    .keywordsUntilEot beId #[Keyword.flying]
  ] (cause := some testCause)
  let beBatches := (gBatchEff1.events.extract preBeIdx gBatchEff1.events.size).filterMap fun e =>
    match e.change with
    | .rules (.continuousEffect (.created ..)) => some e.batch
    | _ => none
  let batchedCreateEffectsOk : Bool :=
    beBatches.size == 2 && beBatches[0]!.isSome && beBatches[0]! == beBatches[1]!

  mustHold20 "8a.twoHeadedAndDepartedOk" twoHeadedAndDepartedOk &&
  mustHold20 "8b.twoHeadedCtrlAndSelfOk" twoHeadedCtrlAndSelfOk &&
  mustHold20 "8c.batchedCreateEffectsOk" batchedCreateEffectsOk &&
  mustHold20 "8.replay" ([g2hTryWin, g2hMateCastOk, g2hMatePoison, g2hOppPoison, gDepDmg1, g2hCtrl1, g2hCtrlMateTurn, g2hCtrlTeamSeat1, g2hCtrlTeamSeat2, g2hCtrlAfterTeamTurn, g2hDepMate0, g2hDepMateTurn1, g2hDepMateTargetTurn, g2hDepMateAfter, gExCtrl0, gExCtrlTurn1, gExCtrlTurn2, gBatchEff1].all (fun g =>
    Game.replayEvents g.events == g && allRulesEventsClassified g))

end Phase20EventAlignment

end Mtg.Engine.EventTests
