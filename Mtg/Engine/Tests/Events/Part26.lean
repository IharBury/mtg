import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

/-! ### Phase 60 Item 1: `continuationSettlesControlFlow` `.seq` `alreadyOrderedCycle` +
`afterRandom`, `hasNestedManaAbilityPostStep` `.endProposalAction true` + `.restorePending` &
`advanceProbeOnResumeCore` nested-checkpoint reversal, `stepCanReverseProposal` stacked
`.restorePending .none true` / multi-frame `outerDepth` & reversing-leaf priority-flag
propagation, `followedByFinishChoice` non-active caster priority stash, semantic post-prompt
priority check replacing syntactic `endsWithPriorityGrant` & `!g.sbaPaused` stash parity,
`afterFlushed` `outerPendingReplacements`/`currentInterpWait?`, and paused `crewIds`
`isCreature`/power revalidation -/
section Phase60Item1EventAlignment

private def mustHold60i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase60Item1EventAlignment failed: {label}"

private def replayOk60i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let leyADef : CardDef := { name := "P60i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P60i1 LeyB", types := #[.enchantment] }
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

  -- 1a. `continuationSettlesControlFlow` `.seq a b` short-circuits to `true` when
  --     `prepareOpenedReplacementSeq` clears an `alreadyOrderedCycle` while `afterRandom != .none`.
  let gCycleRand :=
    gRep.changes #[.replacementOrder #[dRidA], .pushContinuationFrame { afterRandom := .draw p0 1 }]
  let cycleAfterRandSettlesOk :=
    gCycleRand.afterRandom != .none &&
    continuationSettlesControlFlow gCycleRand false
      (.seq (.restorePending (.chooseReplacement p0 #[dRidA, dRidB]) false)
        (.logMessage "after-cycle-rand"))

  -- 1b. `hasNestedManaAbilityPostStep` recognizes `.endProposalAction true` + `.restorePending`
  --     (and outer-delegated nested mana post-steps), and `advanceProbeOnResumeCore` detects
  --     nested-checkpoint reversal so `.seq` drops its trailing step on CR 734.1 reversal!
  let nonActSpell : CardDef := {
    name := "P60i1 NonActInstant"
    manaCost := ManaCost.ofColor .blue
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gNonAct0 :=
    ((insertObject (emptyHand g3 p0) nonActSpell p1 (.hand p1)).change (.priority p1)).change
      (.pendingPriority none)
  let naHandId := (gNonAct0.player p1).hand.back!
  let gOuterProp := mustApply gNonAct0 p1 (.cast naHandId)
  let outerSpellId := gOuterProp.proposedSpell.get!.spellId
  let gNestedCkpt :=
    (gOuterProp.change .saveProposalCheckpoint).change (.beginProposalAction .manaAbility)
  let gNestedUnpayable :=
    ((gNestedCkpt.change (.pending .none)).move outerSpellId (.graveyard p1) none (cause := some testCause)).1
  let nestedChain : PendingReplacement :=
    .seq (.endProposalAction true)
      (.restorePending (.activateManaAbilities p1) false none #[p1] none)
  let gNestedRev :=
    gNestedUnpayable.resumePendingReplacement
      (.seq nestedChain (.logMessage "p60-must-drop-nested-tail"))
  let nestedProbeGrant? :=
    (gNestedUnpayable.change (.pushContinuationFrame {
      pendingReplacement := some
        (.seq (.restorePending (.activateManaAbilities p1) false none #[p1] none) (.receivePriority p2))
    })).firstContinuationPriorityGrant?
  let nestedManaRevOk :=
    gNestedCkpt.hasActiveManaProposalCheckpoint &&
    gNestedRev.proposedSpell.isNone &&
    !gNestedRev.log.contains "p60-must-drop-nested-tail" &&
    nestedProbeGrant? == some (some p2)

  -- 1c. `stepCanReverseProposal` handles stacked identical `.restorePending .none true` frames
  --     across multi-frame `continuations` without desyncing `outerDepth`; AND reversing
  --     `.finishActivateManaAbilityPicks` (`prevPending != .none`) and `.resumeTriggerModesAfterLeave`
  --     preserve `followedByExplicitPriority?` / `followedByFinishChoice`!
  let gOuterLeft :=
    ((gOuterProp.change (.pending .none)).move outerSpellId (.graveyard p1) none (cause := some testCause)).1
  let gMultiFrame :=
    (gOuterLeft.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.restorePending (.activateManaAbilities p1) false none #[p1] none]
      },
      .pushContinuationFrame {
        outerPendingReplacements := #[.restorePending .none true]
      }
    ]).resumePendingReplacement
      (.seq (.restorePending .none true) (.logMessage "p60-must-drop-stacked-restore"))
  let gRevTrigPrioBase :=
    (gOuterProp.change (.pending .none)).record
      (.rules gOuterProp.turnNumber (.player (.leftGame p1)) (.gameRule .playerLeftGame))
  let trigRevSeq : PendingReplacement :=
    .seq (.finishPostStep (.resumeTriggerModesAfterLeave p1 ⟨99992⟩ 1 #[]))
      (.receivePriority p2)
  let gRevTrigPrio := gRevTrigPrioBase.resumePendingReplacement trigRevSeq
  let trigRevGrant? :=
    (gRevTrigPrioBase.change (.pushContinuationFrame { pendingReplacement := some trigRevSeq })).firstContinuationPriorityGrant?
  let manaRevPr : PendingReplacement :=
    .finishActivateManaAbilityPicks p1 ⟨99993⟩ "GoneRock" #[.colored .blue] #[] #[]
      false false (some 0) none 0 false (.activateManaAbilities p1)
  let manaRevSeq : PendingReplacement := .seq manaRevPr (.receivePriority p2)
  let gRevManaPrio := gRevTrigPrioBase.resumePendingReplacement manaRevSeq
  let manaRevGrant? :=
    (gRevTrigPrioBase.change (.pushContinuationFrame { pendingReplacement := some manaRevSeq })).firstContinuationPriorityGrant?
  let stackedAndFlagsOk :=
    gMultiFrame.proposedSpell.isNone &&
    !gMultiFrame.log.contains "p60-must-drop-stacked-restore" &&
    gRevTrigPrio.proposedSpell.isNone &&
    gRevTrigPrio.priority == p2 &&
    trigRevGrant? == some (some p2) &&
    gRevManaPrio.proposedSpell.isNone &&
    gRevManaPrio.priority == p2 &&
    manaRevGrant? == some (some p2)

  -- 1d. CR 117.3c non-active caster priority stash on `followedByFinishChoice` reversals
  --     (both idle `!g.sbaPaused` and `g.sbaPaused` in `.restorePending` and `reverseProposedSpell`).
  let gFcIdleRev :=
    gOuterLeft.resumePendingReplacement
      (.seq (.restorePending (.activateManaAbilities p1) false none #[p1] none)
        .finishResolutionChoice)
  let gFcAliveRev :=
    (gOuterProp.change (.pending .none)).resumePendingReplacement
      (.seq (.restorePending (.sacrificePermanent p1 naHandId) false)
        .finishResolutionChoice)
  let gFcSbaBase :=
    ((gOuterProp.change (.pending .none)).change (.pushContinuationFrame {})).changes #[
      .pending (.chooseReplacement p0 #[dRidA, dRidB])
    ]
  let gFcDirectRev :=
    gOuterProp.reverseProposedSpell (resumeContinuation := true) (followedByFinishChoice := true)
  let nonActFcStashOk :=
    gFcAliveRev.proposedSpell.isNone &&
    gFcAliveRev.playersReceivePriority &&
    gFcAliveRev.priority == p1 &&
    gFcDirectRev.proposedSpell.isNone &&
    gFcDirectRev.priority == p1 &&
    gFcIdleRev.proposedSpell.isNone &&
    gFcIdleRev.priority == p1 &&
    gFcSbaBase.sbaPaused

  -- 1e. Semantic post-prompt priority check replaces syntactic `endsWithPriorityGrant` on
  --     `sbaPaused` explicit-priority reversals (no duplicate `.receivePriority` when
  --     `.restorePending .none true` delegates to `outer = #[.receivePriority p2]`), and
  --     `!g.sbaPaused` with `pending != .none || afterRandom != .none` stashes `pendingPriority`
  --     instead of calling `finishAndGrantPriority`!
  let gSemBase0 :=
    gRep.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.restorePending .none true)
      }
    ]
  let gSemSba := gSemBase0.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))
  let semGrants :=
    !(gSemSba.pendingReplacement.any (·.endsWithPriorityGrant)) &&
    gSemSba.anyPostPromptContinuationGrantsPriority
  let gNonSbaRandBase :=
    ((insertObject (emptyHand g3 p0) nonActSpell p1 (.hand p1)).change (.priority p1)).change
      (.pending (.mayResolve p0))
  let naRandId := (gNonSbaRandBase.player p1).hand.back!
  let gNonSbaRandProp :=
    (gNonSbaRandBase.change .saveProposalCheckpoint).changes #[
      .proposedSpell (some {
        caster := p1, cost := ManaCost.ofColor .blue, spellId := naRandId,
        original := gNonSbaRandBase.object! naRandId,
        originalSnapshot := gNonSbaRandBase.snapshot (gNonSbaRandBase.object! naRandId) }),
      .pending .none
    ]
  let gNonSbaRandRev :=
    gNonSbaRandProp.resumePendingReplacement
      (.seq (.restorePending (.sacrificePermanent p1 naRandId) false) (.receivePriority p2))
  let semanticAndStashOk :=
    semGrants &&
    gNonSbaRandRev.proposedSpell.isNone &&
    !gNonSbaRandRev.sbaPaused &&
    gNonSbaRandRev.pending == .mayResolve p0 &&
    gNonSbaRandRev.pendingPriority == some p2

  -- 1f. `afterFlushed` walks `outerPendingReplacements` / `currentInterpWait?` on both
  --     idle arm (delegating trailing frames) and `else` arm (`pausedPromptSettles`).
  let gAfterFlushedOuter :=
    g3.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.restorePending .none false)
      }
    ]
  let gAfterFlushedBehindInner :=
    g3.changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.seq (.restorePending .none false) (.logMessage "after-flushed-inner"))
      }
    ]
  let gAfterFlushedRepl :=
    (gRep.change (.pending (.chooseReplacement p0 #[dRidA, dRidB]))).changes #[
      .pushContinuationFrame {
        outerPendingReplacements := #[.receivePriority p2]
        pendingReplacement := some (.restorePending .none false)
      }
    ]
  let afterFlushedOk :=
    gAfterFlushedOuter.anyContinuationSettlesControlFlow &&
    gAfterFlushedOuter.firstContinuationPriorityGrant? == some (some p2) &&
    gAfterFlushedBehindInner.anyContinuationSettlesControlFlow &&
    gAfterFlushedRepl.anyContinuationSettlesControlFlow

  -- 1g. Paused `crewIds` revalidation checks `g.isCreature` and total power (`crewPower?`):
  let crewManaDef : CardDef := {
    name := "P60i1 CrewManaRock"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let gCrew0 := addPermanent (addPermanent g3 crewManaDef p0 p0) bear p0 p0
  let rockId := (gCrew0.permanentsOf p0).find? (·.name == crewManaDef.name) |>.get!.id
  let crewBearId := (gCrew0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gCrewNonCreature := gCrew0.createEffect (ContinuousEffectSpec.onlyFoodArtifact crewBearId) (cause := some testCause)
  let gCrewWeak := gCrew0.createEffect (.layered (.objects #[crewBearId]) (.ptModify (-1) 0) .untilEndOfTurn) (cause := some testCause)
  let gCrewNonCreDone :=
    gCrewNonCreature.finishActivateManaAbilityPicks p0 rockId crewManaDef.name #[.colored .green]
      #[] #[] false false (some 0) none 0 false .none (crewIds := #[crewBearId]) (crewPower? := some 2)
  let gCrewWeakDone :=
    gCrewWeak.finishActivateManaAbilityPicks p0 rockId crewManaDef.name #[.colored .green]
      #[] #[] false false (some 0) none 0 false .none (crewIds := #[crewBearId]) (crewPower? := some 2)
  let gCrewValidDone :=
    gCrew0.finishActivateManaAbilityPicks p0 rockId crewManaDef.name #[.colored .green]
      #[] #[] false false (some 0) none 0 false .none (crewIds := #[crewBearId]) (crewPower? := some 2)
  let pausedCrewRevalOk :=
    (gCrewNonCreDone.player p0).manaPool.units.isEmpty &&
    !(gCrewNonCreDone.object! crewBearId).status.tapped &&
    (gCrewWeakDone.player p0).manaPool.units.isEmpty &&
    !(gCrewWeakDone.object! crewBearId).status.tapped &&
    (gCrewValidDone.player p0).manaPool.units.size == 1 &&
    (gCrewValidDone.object! crewBearId).status.tapped

  mustHold60i1 "1a_cycleAfterRandSettles" cycleAfterRandSettlesOk &&
  mustHold60i1 "1b_nestedManaRev" nestedManaRevOk &&
  mustHold60i1 "1c_stackedAndFlags" stackedAndFlagsOk &&
  mustHold60i1 "1d_nonActFcStash" nonActFcStashOk &&
  mustHold60i1 "1e_semanticAndStash" semanticAndStashOk &&
  mustHold60i1 "1f_afterFlushed" afterFlushedOk &&
  mustHold60i1 "1g_pausedCrewReval" pausedCrewRevalOk &&
  mustHold60i1 "1.replay"
    (replayOk60i1 #[gCycleRand, gNestedRev, gMultiFrame, gRevTrigPrio, gRevManaPrio,
      gFcAliveRev, gFcDirectRev, gNonSbaRandRev, gAfterFlushedOuter, gAfterFlushedRepl,
      gCrewNonCreDone, gCrewWeakDone, gCrewValidDone])

end Phase60Item1EventAlignment

/-! ### Phase 60 Item 2: `applyRiddlesToHandLoop` / `execInspectLibrary` batch closing &
`.sphinxsApproach` paused log, `markDamageOn` `healsOther` premature/duplicate
`damageMarkedCleared` & standalone unpreventable `.shield`+`.loyalty` deferral,
`fightCreatures` & mixed/`trackExcess` `execDamage` pause-safety/deferral, 6 missing
`isPlayFromExileDeferBoundaryLeaf` leaves & lower-frame `afterRandom` order,
`interpContAnyObjId` `.afterMoveLoop` 6th arg & `.afterMoveCountersPut` remapping,
`expireMatching` `some pre` / `payCostPick` `.custom (.tapObjects ..)` / `untapPermanent`
`sbaPaused` & lazy `emitExpiredPlayFromExileLogsLazy` loops -/
section Phase60Item2EventAlignment

private def mustHold60i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase60Item2EventAlignment failed: {label}"

private def replayOk60i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := emptyHand afterDraw p0

  -- 2a. `applyRiddlesToHandLoop` closes batch `B1` before moving `toGy` in a fresh batch `B2`,
  --     `execInspectLibrary` chains `.finishInspectLibraryRest` cleanly, and `.sphinxsApproach`
  --     handles exile log properly!
  let gRid0 := insertObject (insertObject g0 bear p0 .exile) hero p0 .exile
  let ridIds := gRid0.objects.filter (fun o => o.zone == .exile) |>.map (·.id)
  let ridHandId := ridIds[0]!
  let ridGyId := ridIds[1]!
  let gRidResumed :=
    gRid0.applyRiddlesToHandLoop p0 #[ridHandId] #[ridGyId]
  let ridBatchIds : Array BatchId :=
    gRidResumed.events.filterMap fun ev =>
      match ev.change with
      | .rules (.zone (.moved _ _ .exile (.hand _) ..))
      | .rules (.zone (.moved _ _ .exile (.graveyard _) ..)) => ev.batch
      | _ => none
  let gInsp0 := insertObject (insertObject (insertObject g0 bear p0 (.library p0)) hero p0 (.library p0)) forest p0 (.library p0)
  let gInspDone :=
    gInsp0.applyUnified p0
      { body := .player (.inspectLibrary {
          source := .topCards .you (.const 3) false
          action := .takeMatching (.hasType .creature) (.upTo (.const 1)) (.hand .controller)
          rest := .graveyard }) } #[]
  let gInspAns :=
    match gInspDone.pending with
    | .resolutionChoice q ch => mustApply gInspDone q (defaultChoiceAction gInspDone q ch)
    | _ => gInspDone
  let sphinxDef : CardDef := {
    name := "Sphinx's Approach", manaCost := ManaCost.ofGeneric 2, types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gSph0 :=
    insertObject (insertObject (insertObject (insertObject (insertObject g0
      sphinxDef p0 (.graveyard p0)) sphinxDef p0 (.graveyard p0)) sphinxDef p0 (.graveyard p0))
      sphinxDef p0 (.graveyard p0)) sphinxDef p0 (.graveyard p0)
  let sphReplA : ReplacementId := { kind := .addNoncombatDamage, object := some ⟨701⟩ }
  let sphReplB : ReplacementId := { kind := .multiplyDamage, object := some ⟨702⟩ }
  let gSphPausedBase :=
    (gSph0.change (.pending (.resolutionChoice p0 (.sphinxsApproach ⟨99995⟩)))).change
      (.pushContinuationFrame {
        pendingReplacement := some (.logMessage "after-sphinx")
      })
  let gSphDone := mustApply gSphPausedBase p0 .accept
  let sphExpectedLog := s!"{(g0.player p0).name} exiles five cards named Sphinx's Approach"
  let gSphRestCheck :=
    gInsp0.runPostStep (.finishInspectLibraryRest p0 .graveyard ((gInsp0.player p0).library.extract 0 2) testCause)
  let batchAndSphinxOk :=
    ridBatchIds.size == 2 &&
    ridBatchIds[0]! != ridBatchIds[1]! &&
    (gRidResumed.player p0).hand.size == 1 &&
    (gRidResumed.player p0).graveyard.size == 1 &&
    (gInspAns.player p0).hand.size == 1 &&
    (gInspAns.player p0).graveyard.size == 2 &&
    gSphDone.log.contains sphExpectedLog &&
    (gSphRestCheck.player p0).graveyard.size == 2

  -- 2b. `Damage.markDamageOn`: `healsOther` emits `damageMarkedCleared` exactly once on
  --     unpreventable hit and 0 times when target already departed; standalone unpreventable
  --     damage removes both `.shield` and `.loyalty` cleanly!
  let healPwDef : CardDef := {
    creature "P60i2 HealShieldPW" ManaCost.zero #["Bear"] 4 4 with
    types := #[.creature, .planeswalker]
    loyalty := some 3
    staticAbilities := #[
      .replacement none (.healOtherDamageWhenDealt .self)
    ]
  }
  let gDmg0 := addPermanent g0 healPwDef p0 p0
  let hpwId := (gDmg0.permanentsOf p0).find? (·.name == healPwDef.name) |>.get!.id
  let gDmg1 :=
    (gDmg0.recordPutCounters hpwId .shield 1 (byPlayer := some p0) (cause := some testCause)).recordPutCounters
      hpwId .loyalty 3 (byPlayer := some p0) (cause := some testCause)
  let gDmgHit :=
    gDmg1.markDamageOn (gDmg1.object! hpwId) 2 "takes 2 unpreventable"
      (unpreventable := true) (cause := some testCause)
  let healClearedCount :=
    (gDmgHit.events.filter fun ev =>
      match ev.change with | .rules (.damage (.markedCleared _)) => true | _ => false).size
  let (gDmgGone0, _) := gDmg1.move hpwId (.graveyard p0) none (cause := some testCause)
  let gDmgGoneHit :=
    gDmgGone0.resumePendingReplacement
      (.markDamageOn hpwId 2 "gone" false none false true (some testCause) false true none)
  let goneClearedCount :=
    (gDmgGoneHit.events.filter fun ev =>
      match ev.change with | .rules (.damage (.markedCleared _)) => true | _ => false).size
  let markDamageOk :=
    healClearedCount == 1 &&
    (gDmgHit.object! hpwId).status.shield == 0 &&
    (gDmgHit.object! hpwId).status.damage == 2 &&
    (gDmgHit.object! hpwId).status.counterCount .loyalty == 1 &&
    goneClearedCount == 0

  -- 2c. `fightCreatures` & mixed/`trackExcess` `execDamage` pause-safety & deferral:
  let bigBear : CardDef := creature "P60i2 BigBear" ManaCost.zero #["Bear"] 4 4
  let gFight0 := addPermanent (addPermanent g0 bigBear p0 p0) hero p1 p1
  let fSrcId := (gFight0.permanentsOf p0).find? (·.name == bigBear.name) |>.get!.id
  let fDstId := (gFight0.permanentsOf p1).find? (·.name == hero.name) |>.get!.id
  let gFightSba :=
    (gFight0.change (.pending (.chooseReplacement p0 #[sphReplA, sphReplB]))).fightCreatures
      (gFight0.object! fSrcId) (gFight0.object! fDstId) (cause := some testCause)
  let gFightDone := gFight0.fightCreatures (gFight0.object! fSrcId) (gFight0.object! fDstId) (cause := some testCause)
  let dmgRepA : ReplacementId := { kind := .addNoncombatDamage, object := some fSrcId }
  let dmgRepB : ReplacementId := { kind := .multiplyDamage, object := some fDstId }
  let gMix0 :=
    (gFight0.createEffect
      (.replacement {
        id := dmgRepA, source := some fSrcId, controller := some p0, affectedPlayer := p1,
        kind := .addNoncombatDamage none 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := dmgRepB, source := some fDstId, controller := some p0, affectedPlayer := p1,
        kind := .multiplyDamage none 2 }) (cause := some testCause)
  let excessVar : VarId := ⟨7⟩
  let gMixPaused :=
    gMix0.applyUnifiedAbility p0
      { body := .bind excessVar
          (.damage (.deal .this (.objects (.inZones .battlefield (.controlledBy .opponent))) (.const 5) { trackExcess := true }))
          (.life (.gain .you (.stepMetric .excessDamage excessVar))) } #[] (some fSrcId)
  let gMixDone :=
    match gMixPaused.pending with
    | .chooseReplacement q choices =>
      (mustApply gMixPaused q (.chooseReplacement choices[0]!)).drainPendingContinuations
    | _ => gMixPaused
  let fightAndMixedOk :=
    (match gFightSba.pendingReplacement with | some (.finishPostStep (.fightCreatures ..)) => true | _ => false) &&
    (gFightDone.object! fSrcId).status.damage == 2 &&
    (gFightDone.object! fDstId).status.damage == 4 &&
    (match gMixPaused.pending with | .chooseReplacement .. => true | _ => false) &&
    gMixDone.pending == .none &&
    (gMixDone.player p0).life > (20 : Int)

  -- 2d. 6 newly added `isPlayFromExileDeferBoundaryLeaf` leaves + lower-frame `afterRandom` order:
  let gEx0 := insertObject g0 bear p0 .exile
  let exId := (gEx0.objects.find? (fun o => o.zone == .exile && o.name == bear.name)).get!.id
  let gLowerRand :=
    (gEx0.createEffect (.permission (some p0) (.playFromExile exId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).changes #[
      .pushContinuationFrame {
        afterRandom := .draw p0 1
        pendingReplacement := some (.logMessage "after-lower-rand")
      },
      .pushContinuationFrame {}
    ]
  let lowerEffId := (gLowerRand.activeEffects.find? (fun (_, s) =>
    match s with | .permission _ (.playFromExile oid _) _ => oid == exId | _ => false)).get!.1
  let lowerStartIdx := gLowerRand.events.size
  let gLowerMid := gLowerRand.expireEffectById lowerEffId (deferPlayFromExileLogs := true)
  let gLowerEmit := Game.emitExpiredPlayFromExileLogs gLowerRand gLowerMid lowerStartIdx
  let pfeBoundariesOk :=
    (PendingReplacement.connive p0 none).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.continueConnives p0 #[]).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.createAndMarkTokensAttacking p0 (.predefined .treasure) 1 false false none none).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.finishSearchAfterPlace p0 exId (.exileLinked none) .none false #[] none).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.finishPostStep (.conniveTricksterTarget p0 none none)).isPlayFromExileDeferBoundaryLeaf &&
    (PendingReplacement.finishPostStep (.finishGrimaDirectCast p0 p1 exId #[] none)).isPlayFromExileDeferBoundaryLeaf &&
    gLowerEmit.continuations[0]!.pendingReplacement == some (.logMessage "after-lower-rand")

  -- 2e. `interpContAnyObjId` `.afterMoveLoop` (with 6th arg `some 42`) and `.afterMoveCountersPut`
  --     remapping verified end-to-end via proposal-reversal checkpoint replay!
  let moveLoopCont : InterpCont :=
    .afterMoveLoop #[fSrcId] .graveyard .put {} testCause (some 42)
  let moveCtrsCont : InterpCont :=
    .afterMoveCountersPut fSrcId #[(.plusOnePlusOne, 2)] testCause
  let contWaitState : InterpState :=
    { ctx := { controller := p0 }, queue := #[], stack := #[moveLoopCont, moveCtrsCont] }
  let gRemap0 :=
    ((gFight0.change .saveProposalCheckpoint).change
      (.proposedSpell (some {
        caster := p0, cost := ManaCost.ofColor .green, spellId := fSrcId,
        original := gFight0.object! fSrcId,
        originalSnapshot := gFight0.snapshot (gFight0.object! fSrcId) }))).change
      (.pushContinuationFrame { interpWait? := some contWaitState })
  let gRemapRev := gRemap0.reverseProposedSpell (resumeContinuation := false)
  let contObjIdOk :=
    gRemapRev.continuations.isEmpty &&
    gRemap0.currentInterpWait?.any (fun st => st.stack.size == 2)

  -- 2f. `expireMatching` passes `some pre`, `ActivationCosts.payCostPick` handles
  --     `.custom (.tapObjects ..)` as non-bf-sacrifice, and `Pumps.untapPermanent` chains on `sbaPaused`!
  let gExTwo0 := insertObject (insertObject g0 bear p0 .exile) hero p0 .exile
  let exTwoIds := gExTwo0.objects.filter (fun o => o.zone == .exile) |>.map (·.id)
  let gExTwo :=
    (gExTwo0.createEffect (.permission (some p0) (.playFromExile exTwoIds[0]! { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile exTwoIds[1]! { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let gExTwoDone := gExTwo.expireMatching fun s =>
    match s with | .permission _ (.playFromExile _ _) _ => true | _ => false
  let gUntSbaBase :=
    (gFight0.record (GameEvent.tapped gFight0.turnNumber (gFight0.snapshot (gFight0.object! fSrcId)) true (cause := testCause))).change
      (.pending (.chooseReplacement p0 #[sphReplA, sphReplB]))
  let gUntSba := gUntSbaBase.untapPermanent (gUntSbaBase.object! fSrcId) (cause := some testCause)
  let tapPickRes :=
    gFight0.payCostPick p0 none none (.custom (.tapObjects (.exact 1) (.hasType .creature))) #[fSrcId]
  let minorFixesOk :=
    (gExTwoDone.log.filter (·.endsWith "can no longer be played from exile")).size == 2 &&
    (gUntSba.object! fSrcId).status.tapped &&
    (match gUntSba.pendingReplacement with | some (.untapPermanent ..) => true | _ => false) &&
    (match tapPickRes with
     | .ok gTap => (gTap.object! fSrcId).isOnBattlefield && (gTap.object! fSrcId).status.tapped
     | .error _ => false)

  mustHold60i2 "2a_batchAndSphinx" batchAndSphinxOk &&
  mustHold60i2 "2b_markDamage" markDamageOk &&
  mustHold60i2 "2c_fightAndMixed" fightAndMixedOk &&
  mustHold60i2 "2d_pfeBoundaries" pfeBoundariesOk &&
  mustHold60i2 "2e_contObjId" contObjIdOk &&
  mustHold60i2 "2f_minorFixes" minorFixesOk &&
  mustHold60i2 "2.replay"
    (replayOk60i2 #[gRidResumed, gInspAns, gSphDone, gSphRestCheck, gDmgHit, gDmgGoneHit,
      gFightSba, gFightDone, gMixDone, gLowerEmit, gRemapRev, gExTwoDone, gUntSba])

end Phase60Item2EventAlignment

/-! ### Phase 60 Item 3: static-granted `.grantStatic` self-execution, expanded `Decayed`
end-of-combat sacrifice & `Myriad` non-defending-opponent end-of-combat exile, `PerObjHistState`
`.stack` `fd` / multi-player `.goaded` / Ring-bearer re-choice & control-change & `.ringTempted` /
`.command` emblem `rc?`, `wardCostsOn` face-down `.stack` Ward / `activatedAbilitiesOf` `.stack`
Morph / `coreSorceryTimingOk` Layer-6 statics / `.lki` face-down zone gate / `specAnyObjId`
`.playerRule`, and Layer-6 Flashback/Morph/Sneak + `applyKickerToProposed` `noSourceSentinelId` &
single-pass Layer-3 -/
section Phase60Item3EventAlignment

private def mustHold60i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase60Item3EventAlignment failed: {label}"

private def replayOk60i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g0 := emptyHand afterDraw p0
  let g3 := g0.change (.addPlayer { id := p2, name := "Liliana" })

  -- 3a. Static-granted `.grantStatic` self-execution on recipient `o` (both `currentKeywords`
  --     fast path `kwOnly == true` AND full `evalLayer6`).
  let selfFlyStatic : StaticAbility :=
    .continuous none { zones := .battlefield, pred := .sameAs .this } (.grantKeywords #[Keyword.flying])
  let grantStaticLord : CardDef := {
    name := "P60i3 GrantStaticLord"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .all #[.controlledBy .you, .hasType .creature] }
        (.grantStatic #[selfFlyStatic])
    ]
  }
  let gGs := addPermanent (addPermanent g0 grantStaticLord p0 p0) bear p0 p0
  let gsBearId := (gGs.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let grantStaticSelfExecOk :=
    (gGs.currentKeywords (gGs.object! gsBearId)).contains Keyword.flying &&
    !(gGs.staticAbilities (gGs.object! gsBearId)).isEmpty

  -- 3b. Expanded `Decayed` creates `.endOfCombatSacrifice` (no leaked command emblem) and
  --     sacrifices at `.endOfCombat`; expanded `Myriad` excludes defending player and creates
  --     `.endOfCombatExile` delayed trigger that exiles at `.endOfCombat`!
  let decayedDef : CardDef := {
    creature "P60i3 DecayedZombie" ManaCost.zero #["Zombie"] 2 2 with
    keywords := #[.simple .decayed]
  }
  let gDec0 := addPermanent g0 decayedDef p0 p0
  let decId := (gDec0.permanentsOf p0).find? (·.name == decayedDef.name) |>.get!.id
  let decTrig := (gDec0.triggeredAbilities (gDec0.object! decId))[0]!
  let gDecResolved := gDec0.applyUnifiedAbility p0 decTrig.effect #[] (some decId)
  let gDecEoc := gDecResolved.beginStep .endOfCombat
  let gDecAfter := if !gDecEoc.stack.isEmpty then gDecEoc.resolveTop else gDecEoc
  let myriadDef : CardDef := {
    creature "P60i3 MyriadKnight" ManaCost.zero #["Knight"] 3 3 with
    keywords := #[.simple .myriad]
  }
  -- 2-player game: defending player is `p1`, so NO other opponent exists -> Myriad creates 0 tokens!
  let gMyr2p0 := addPermanent g0 myriadDef p0 p0
  let myr2Id := (gMyr2p0.permanentsOf p0).find? (·.name == myriadDef.name) |>.get!.id
  let gMyr2Atk := gMyr2p0.record (GameEvent.attacked gMyr2p0.turnNumber p0 (gMyr2p0.snapshot (gMyr2p0.object! myr2Id)) p1)
  let myr2Trig := (gMyr2Atk.triggeredAbilities (gMyr2Atk.object! myr2Id))[0]!
  let gMyr2Res := gMyr2Atk.applyUnifiedAbility p0 myr2Trig.effect #[] (some myr2Id)
  -- 3-player game: attacking `p1` creates 1 token for `p2` and registers `.endOfCombatExile`!
  let gMyr3p0 := (addPermanent g3 myriadDef p0 p0).record (GameEvent.stepBegan g3.turnNumber .declareAttackers)
  let myr3Id := (gMyr3p0.permanentsOf p0).find? (·.name == myriadDef.name) |>.get!.id
  let gMyr3Atk := gMyr3p0.record (GameEvent.attacked gMyr3p0.turnNumber p0 (gMyr3p0.snapshot (gMyr3p0.object! myr3Id)) p1)
  let myr3Trig := (gMyr3Atk.triggeredAbilities (gMyr3Atk.object! myr3Id))[0]!
  let gMyr3Res := gMyr3Atk.applyUnifiedAbility p0 myr3Trig.effect #[] (some myr3Id)
  let gMyr3Accept :=
    match gMyr3Res.pending with
    | .mayResolve q => mustApply gMyr3Res q .accept
    | .resolutionChoice q _ => mustApply gMyr3Res q .accept
    | _ => gMyr3Res
  let gMyr3Tok :=
    match gMyr3Accept.pending with
    | .resolutionChoice q ch => mustApply gMyr3Accept q (defaultChoiceAction gMyr3Accept q ch)
    | _ => gMyr3Accept
  let gMyr3Eoc := gMyr3Tok.beginStep .endOfCombat
  let gMyr3After := if !gMyr3Eoc.stack.isEmpty then gMyr3Eoc.resolveTop else gMyr3Eoc
  let decayedAndMyriadOk :=
    gDecResolved.delayedTriggers.any (fun dt => dt.kind == .endOfCombatSacrifice decId) &&
    !(gDecResolved.objects.any (·.zone == .command)) &&
    !(gDecAfter.findObject? decId).any (·.isOnBattlefield) &&
    gMyr2Res.pending == .none &&
    (gMyr2Res.permanentsOf p0).size == 1 &&
    gMyr3Tok.delayedTriggers.any (fun dt => match dt.kind with | .endOfCombatExile _ => true | _ => false) &&
    (gMyr3Tok.permanentsOf p0).size == 2 &&
    (gMyr3After.permanentsOf p0).size == 1

  -- 3c. `HistGlobalState` / `PerObjHistState` LKI fixes:
  --     - Face-down Morph spell on `.stack` stays masked in `mkHistoricalGameAt`;
  --     - Multi-player `.goaded` reversal preserves earlier goaders;
  --     - Ring-bearer re-choice, control-change `.ringBearer false`, and `.ringTempted` preserve
  --       historical Ring-bearer state;
  --     - `.command` emblem `.created` sets `rc?` properly in `forwardStepHistGlobal`.
  let morphDef : CardDef := {
    creature "P60i3 MorphCard" (ManaCost.ofGenericAndColor 3 .green) #["Beast"] 4 4 with
    keywords := #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])]
  }
  let gStackFd0 := insertObject g0 morphDef p0 .stack
  let stFdId := (gStackFd0.objects.find? (fun o => o.zone == .stack)).get!.id
  let gStackFd1 := gStackFd0.record (GameEvent.turnedFaceDown gStackFd0.turnNumber (gStackFd0.snapshot (gStackFd0.object! stFdId)) (cause := testCause))
  let fdIdx := gStackFd1.events.size
  let gStackFd2 := gStackFd1.record (GameEvent.turnedFaceUp gStackFd1.turnNumber (gStackFd1.snapshot (gStackFd1.object! stFdId)) (cause := testCause))
  let gHistFd := gStackFd2.mkHistoricalGameAt fdIdx
  -- Multi-player & same-player repeated goad reversal (including pre-log goad & `untilNext` flips):
  let gGoad0 := addPermanent g3 bear p0 p0
  let goadId := (gGoad0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gGoad1 := gGoad0.record (GameEvent.designation gGoad0.turnNumber (gGoad0.snapshot (gGoad0.object! goadId)) (.goaded p1 true) true testCause)
  let goad1Idx := gGoad1.events.size
  let gGoad1Dup := gGoad1.record (GameEvent.designation gGoad1.turnNumber (gGoad1.snapshot (gGoad1.object! goadId)) (.goaded p1 true) true testCause)
  let goad1DupIdx := gGoad1Dup.events.size
  let gGoad1Perm := gGoad1Dup.record (GameEvent.designation gGoad1Dup.turnNumber (gGoad1Dup.snapshot (gGoad1Dup.object! goadId)) (.goaded p1 false) true testCause)
  let goad1PermIdx := gGoad1Perm.events.size
  let gGoad2 := gGoad1Perm.record (GameEvent.designation gGoad1Perm.turnNumber (gGoad1Perm.snapshot (gGoad1Perm.object! goadId)) (.goaded p2 true) true testCause)
  let gHistGoad1 := gGoad1Dup.mkHistoricalGameAt goad1Idx
  let gHistGoadDup := gGoad1Perm.mkHistoricalGameAt goad1DupIdx
  let gHistGoadPerm := gGoad2.mkHistoricalGameAt goad1PermIdx
  -- Pre-log goaded creature receiving a second goad from the same player `p1` (tests reverse-only inverse at idx 0):
  let gPreGoad0 : Game := { gGoad1 with events := #[] }
  let gPreGoadSame :=
    gPreGoad0.record (GameEvent.designation gPreGoad0.turnNumber (gPreGoad0.snapshot (gPreGoad0.object! goadId)) (.goaded p1 false) true testCause)
  let gHistPreGoad := gPreGoadSame.mkHistoricalGameAt 0
  -- Ring-bearer re-choice + control change + `.ringTempted`:
  let gRing0 := addPermanent g0 bear p0 p0
  let ringId := (gRing0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gRing1 := gRing0.setRingBearer p0 ringId
  let ring1Idx := gRing1.events.size
  let gRing2 := (gRing1.setRingBearer p0 ringId).record
    (GameEvent.ringTempted gRing1.turnNumber p0 (some ringId) 2 (cause := some testCause))
  let ring2Idx := gRing2.events.size
  let gRingCtrl :=
    (gRing2.createEffect (.control ringId p1) (cause := some testCause)).checkSBA
  let gHistRing1 := gRing2.mkHistoricalGameAt ring1Idx
  let gHistRing2 := gRingCtrl.mkHistoricalGameAt ring2Idx
  -- Command emblem `forwardStepHistGlobal`:
  let embDef : CardDef := { name := "P60i3 Emblem", types := #[] }
  let embId : ObjectId := ⟨g0.nextObjectId⟩
  let embObj : GameObject := {
    id := embId, printed := embDef, owner := p0, controller := some p0, zone := .command,
    timestamp := g0.timestamp + 1
  }
  let gEmb1 := g0.record (GameEvent.created g0.turnNumber p0 (g0.snapshot embObj) (cause := testCause))
  let embIdx := gEmb1.events.size
  let gEmb2 := gEmb1.gainLife p0 1 (cause := some testCause)
  let gHistEmb := gEmb2.mkHistoricalGameAt embIdx
  let histLkiOk :=
    (gHistFd.object! stFdId).status.faceDown &&
    gHistFd.name (gHistFd.object! stFdId) == "" &&
    (gHistGoad1.object! goadId).status.goaded &&
    (gHistGoad1.object! goadId).status.goadedBy == #[p1] &&
    (gHistGoad1.object! goadId).status.goadedUntilNextTurnOf == #[p1] &&
    (gHistGoadDup.object! goadId).status.goaded &&
    (gHistGoadDup.object! goadId).status.goadedBy == #[p1] &&
    (gHistGoadDup.object! goadId).status.goadedUntilNextTurnOf == #[p1] &&
    (gHistGoadPerm.object! goadId).status.goaded &&
    (gHistGoadPerm.object! goadId).status.goadedBy == #[p1] &&
    (gHistGoadPerm.object! goadId).status.goadedUntilNextTurnOf == #[] &&
    (gHistPreGoad.object! goadId).status.goaded &&
    (gHistPreGoad.object! goadId).status.goadedBy == #[p1] &&
    (gHistPreGoad.object! goadId).status.goadedUntilNextTurnOf == #[p1] &&
    (gHistRing1.player p0).ringBearerId == some ringId &&
    (gHistRing2.player p0).ringBearerId == some ringId &&
    (gHistEmb.object! embId).controller == some p0

  -- 3d. `wardCostsOn` face-down `.stack` Ward, `activatedAbilitiesOf` `.stack` Morph exclusion,
  --     `coreSorceryTimingOk` Layer-6 static, `.lki` face-down zone gate, and `.playerRule`
  --     `srcId?` proposal-reversal tracking (`specAnyObjId`)!
  let gStackWard :=
    gStackFd1.createEffect
      (.layered (.objects #[stFdId]) (.abilities { keywords := #[.ward (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let wardOnStackFd := gStackWard.wardCostsOn (gStackWard.object! stFdId)
  let actOnStackFd := gStackFd1.activatedAbilitiesOf (gStackFd1.object! stFdId)
  let sorcDef : CardDef := {
    name := "P60i3 SlowSorc", manaCost := ManaCost.ofGeneric 1, types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let selfFlashStatic : StaticAbility :=
    .ruleModifying none (.play (.castAsThoughFlash .you .anyObject true none))
  let gSorc0 :=
    ((insertObject g0 sorcDef p0 (.hand p0)).record (GameEvent.stepBegan g0.turnNumber .combatDamage)).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }])
  let sorcHandId := (gSorc0.player p0).hand.back!
  let gSorcFlash :=
    gSorc0.createEffect
      (.layered (.objects #[sorcHandId]) (.abilities { staticAbilities := #[selfFlashStatic] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let fdExileEo : EventObject := {
    id := some ⟨888⟩, owner := p0, zone := .exile, name := "VisibleExile",
    printed := some { bear with name := "VisibleExile", manaCost := ManaCost.ofGeneric 4 },
    manaValue := 4, keywords := #[Keyword.flying], faceDown := true
  }
  let fdLkiObj := lkiEventObjectAsGameObject fdExileEo
  let protRuleSpec : ContinuousEffectSpec :=
    .playerRule p0 (.protectionFrom (.color (.literal .red)) (some gsBearId) (some p0)) .untilEndOfTurn
  let gProtRuleProp :=
    ((gGs.change .saveProposalCheckpoint).change
      (.proposedSpell (some {
        caster := p0, cost := ManaCost.ofColor .red, spellId := gsBearId,
        original := gGs.object! gsBearId,
        originalSnapshot := gGs.snapshot (gGs.object! gsBearId) }))).createEffect
      protRuleSpec (cause := some testCause)
  let gProtRuleRev := gProtRuleProp.reverseProposedSpell (resumeContinuation := false)
  let faceDownAndFastPathOk :=
    wardOnStackFd.size == 1 &&
    actOnStackFd.isEmpty &&
    !gSorc0.timingAllowsCast p0 sorcDef (card? := some (gSorc0.object! sorcHandId)) &&
    gSorcFlash.timingAllowsCast p0 sorcDef (card? := some (gSorcFlash.object! sorcHandId)) &&
    fdLkiObj.printed.name == "VisibleExile" &&
    EvalExpr.viewManaCost g0 (.lki fdExileEo) == ManaCost.ofGeneric 4 &&
    EvalExpr.viewHasKeyword g0 (.lki fdExileEo) .flying &&
    gProtRuleRev.activeEffects.size == gGs.activeEffects.size

  -- 3e. Layer-6 Flashback (`Costs` + `Timing`), Layer-6 Morph (`mayPlayFromLibraryTop`),
  --     Layer-6 Sneak (`CastSpell.announceX`), and `applyKickerToProposed` `noSourceSentinelId`!
  let gySpellDef : CardDef := {
    name := "P60i3 GyBolt", manaCost := ManaCost.ofGenericAndColor 4 .red, types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gyFlashbackLord : CardDef := {
    name := "P60i3 GyFlashbackLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.graveyard], owner := .ofPlayer .you }, pred := .hasType .sorcery }
        (.grantKeywords #[.flashback (CostSpec.ofItems #[.mana (ManaCost.ofColor .red)])])
    ]
  }
  let gFb := insertObject (addPermanent g0 gyFlashbackLord p0 p0) gySpellDef p0 (.graveyard p0)
  let fbId := (gFb.player p0).graveyard.back!
  let fbObj := gFb.object! fbId
  let fbMana := gFb.playManaCost { fbObj with controller := some p0 } (gFb.baseCard fbObj)
  let libMorphLord : CardDef := {
    name := "P60i3 LibMorphLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.library], owner := .ofPlayer .you }, pred := .hasType .sorcery }
        (.grantKeywords #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])]),
      .ruleModifying none (.play (.mayPlayFrom .you .library (.hasType .creature) false))
    ]
  }
  let gLibMorph := insertObject (addPermanent g0 libMorphLord p0 p0) gySpellDef p0 (.library p0)
  let libTopObj := gLibMorph.object! (gLibMorph.player p0).library.back!
  let redTaxDef : CardDef := {
    name := "P60i3 RedTax", types := #[.enchantment]
    staticAbilities := #[
      .costModifier none (.spells .any (.hasColor (.literal .red))) (.increaseGeneric (.const 4))
    ]
  }
  let gMorphKick0 :=
    (insertObject (addPermanent g0 redTaxDef p0 p0) morphDef p0 (.hand p0)).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }])
  let mkHandId := (gMorphKick0.player p0).hand.back!
  let gMorphKickCol :=
    gMorphKick0.createEffect
      (.layered (.objects #[mkHandId]) (.colors .set (ColorSet.ofList [.red])) .indefinite)
      (cause := some testCause)
  let gMorphProposed := mustApply gMorphKickCol p0 (.cast mkHandId)
  let gMorphAnnounced := mustApply gMorphProposed p0 (.announceKicker true)
  let sneakXDef : CardDef := {
    creature "P60i3 SneakX" { symbols := #[.x, .colored .blue] } #["Ninja"] 2 2 with
    types := #[.creature]
  }
  let sneakLordDef : CardDef := {
    name := "P60i3 SneakLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.hand], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[.sneak (CostSpec.ofItems #[.mana { symbols := #[.x, .colored .black] }])])
    ]
  }
  let gSneak0 :=
    (addPermanent (insertObject (addPermanent g0 sneakLordDef p0 p0) sneakXDef p0 (.hand p0)) bear p0 p0).record
      (GameEvent.stepBegan g0.turnNumber .declareBlockers)
  let snHandId := (gSneak0.player p0).hand.back!
  let snBearId := (gSneak0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gSneakAtk :=
    gSneak0.record (GameEvent.attacked gSneak0.turnNumber p0 (gSneak0.snapshot (gSneak0.object! snBearId)) p1)
  let (gSneakStack, snStackId) := gSneakAtk.move snHandId .stack (some p0) (cause := some testCause)
  let gSneakProp :=
    (gSneakStack.change .saveProposalCheckpoint).changes #[
      .proposedSpell (some {
        caster := p0, cost := { symbols := #[.x, .colored .black] },
        spellId := snStackId, original := gSneakAtk.object! snHandId,
        originalSnapshot := gSneakAtk.snapshot (gSneakAtk.object! snHandId),
        sneakAttacker := some snBearId }),
      .pending (.chooseX p0)
    ]
  let gSneakX := mustApply gSneakProp p0 (.chooseX 2)
  let layer6CastingOk :=
    gFb.mayPlayFromGraveyard p0 fbObj &&
    fbMana == ManaCost.ofColor .red &&
    gLibMorph.mayPlayFromLibraryTop p0 libTopObj &&
    gMorphAnnounced.proposedSpell.any (fun pr => pr.cost == ManaCost.ofGeneric 3) &&
    gSneakX.proposedSpell.any (fun pr => pr.cost == { symbols := #[.generic 2, .colored .black] })

  mustHold60i3 "3a_grantStaticSelfExec" grantStaticSelfExecOk &&
  mustHold60i3 "3b_decayedAndMyriad" decayedAndMyriadOk &&
  mustHold60i3 "3c_histLki" histLkiOk &&
  mustHold60i3 "3d_faceDownAndFastPath" faceDownAndFastPathOk &&
  mustHold60i3 "3e_layer6Casting" layer6CastingOk &&
  mustHold60i3 "3.replay"
    (replayOk60i3 #[gGs, gDecAfter, gMyr2Res, gMyr3After, gStackFd2, gGoad2, gRingCtrl,
      gEmb2, gStackWard, gSorcFlash, gFb, gLibMorph, gMorphAnnounced, gSneakX])

end Phase60Item3EventAlignment

/-! ### Phase 60 Item 4: no-mana-cost `flashbackUntilEot` / taxed-without-alt `playManaCost`,
origin-zone Layer-6 Morph/Impending across `Part25.lean:917–938` & Layer-6
`beginResolutionCastTargets`, `solveHybridsPay` global multi-hybrid tier optimization, non-mana
`crewExcludesSelf`, `removeAnyNumberPlusOne` at `X = 0` & Layer-6 hand/gy mana abilities,
`PlayPermission.landsAllowed` `anyManaColor` & `mayCastStyle`, empty-option `defaultChoiceAction` /
`maxTimes == 0` / `.mayCastCards` `forcedPerm`, and `copyAndCast` `freeCast := false` /
`grantPlayPermToMoved` / `mayCastExiledElseDamage` / hand-graveyard `isDiscardableCard` -/
section Phase60Item4EventAlignment

private def mustHold60i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase60Item4EventAlignment failed: {label}"

private def replayOk60i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let g0 := emptyHand afterDraw p0

  -- 4a. No-mana-cost `flashbackUntilEot` and taxed-without-alt `playManaCost` both return
  --     unpayable `ManaCost.empty` (CR 118.6 / 702.34a / 601.2f).
  let noCostSpell : CardDef := {
    name := "P60i4 NoCostSorc", manaCost := ManaCost.empty, types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let taxAllDef : CardDef := {
    name := "P60i4 TaxAll", types := #[.enchantment]
    staticAbilities := #[
      .costModifier none (.spells .any .anyObject) (.increaseGeneric (.const 1))
    ]
  }
  let gNc0 := insertObject (addPermanent g0 taxAllDef p0 p0) noCostSpell p0 (.graveyard p0)
  let ncId := (gNc0.player p0).graveyard.back!
  let gNcFb := gNc0.createEffect (ContinuousEffectSpec.flashbackUntilEot ncId) (cause := some testCause)
  let ncObj := gNcFb.object! ncId
  let noCostHolesOk :=
    gNcFb.playManaCost { ncObj with controller := some p0 } noCostSpell == ManaCost.empty &&
    gNc0.playManaCost { ncObj with controller := some p0 } noCostSpell == ManaCost.empty

  -- 4b. Origin-zone Layer-6 Morph/Impending stays visible after moving to `.stack` (opening
  --     `.chooseKicker p0` and casting face-down cleanly), AND `beginResolutionCastTargets`
  --     reads Layer-6 granted `kicker`!
  let morphGrantExDef : CardDef := {
    name := "P60i4 MorphGrantEx", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.exile], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])])
    ]
  }
  let bigBearDef : CardDef := creature "P60i4 BigBear" (ManaCost.ofGeneric 7) #["Bear"] 5 5
  let gOrigMorph0 :=
    (insertObject (addPermanent g0 morphGrantExDef p0 p0) bigBearDef p0 .exile).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }])
  let bigExId := (gOrigMorph0.objects.find? (fun o => o.zone == .exile && o.name == bigBearDef.name)).get!.id
  let gOrigMorphPrompt :=
    gOrigMorph0.change (.pending (.resolutionChoice p0 (.mayCastCards #[bigExId] false false)))
  let gOrigMorphCast :=
    mustApply gOrigMorphPrompt p0 (defaultChoiceAction gOrigMorphPrompt p0 (.mayCastCards #[bigExId] false false))
  let gOrigMorphFaceDown := mustApply gOrigMorphCast p0 (.announceKicker true)
  let kickerLordDef : CardDef := {
    name := "P60i4 KickerLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.stack], owner := .ofPlayer .you }, pred := .hasType .instant }
        (.grantKeywords #[.kicker (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)])])
    ]
  }
  let plainInst : CardDef := {
    name := "P60i4 PlainInst", manaCost := ManaCost.zero, types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gResKick0 := insertObject (addPermanent g0 kickerLordDef p0 p0) plainInst p0 .exile
  let resKickId := (gResKick0.objects.find? (fun o => o.zone == .exile && o.name == plainInst.name)).get!.id
  let gResKickPrompt := gResKick0.castAsPartOfResolution p0 resKickId (withoutManaCost := true)
  let originMorphAndResKickOk :=
    gOrigMorphCast.pending == .chooseKicker p0 &&
    gOrigMorphFaceDown.proposedSpell.any (fun pr => (gOrigMorphFaceDown.object! pr.spellId).status.faceDown) &&
    gResKickPrompt.pending == .chooseKicker p0

  -- 4c. `solveHybridsPay` global multi-hybrid tier optimization:
  --     cost `{U/W}{U/B}`, pool `{W}(restricted), {U}(restricted), {B}(unrestricted)` spends
  --     BOTH restricted `{W}` (for `{U/W}`) and restricted `{U}` (for `{U/B}`), leaving `{B}`!
  let hybridCost : ManaCost := { symbols := #[.hybrid .blue .white, .hybrid .blue .black] }
  let restr : ManaSpendRestriction := .onlyForSpells (.hasType .instant)
  let pool : ManaPool := {
    units := #[
      { mana := .colored .white, restriction := some restr },
      { mana := .colored .blue, restriction := some restr },
      { mana := .colored .black }
    ]
  }
  let spendCtx : ManaSpend := { spell := true, types := #[.instant] }
  let globalHybridOk :=
    match pool.payUnits? hybridCost spendCtx with
    | some (remPool, _) => remPool.units == #[{ mana := .colored .black }]
    | none => false

  -- 4d. Non-mana `crewExcludesSelf`: custom `.tapObjects (.totalPowerAtLeast 2)` WITHOUT
  --     `.otherThan .this` allows a 2/2 creature to tap itself when `!ab.cost.tap`!
  let selfCrewDef : CardDef := {
    creature "P60i4 SelfCrew" ManaCost.zero #["Bear"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.gainLife 2
    }]
  }
  let gSelfCrew0 := addPermanent g0 selfCrewDef p0 p0
  let selfCrewId := (gSelfCrew0.permanentsOf p0).find? (·.name == selfCrewDef.name) |>.get!.id
  let gSelfCrewPrompt := mustApply gSelfCrew0 p0 (.activate selfCrewId 0)
  let gSelfCrewDone :=
    match gSelfCrewPrompt.pending with
    | .resolutionChoice q ch => mustApply gSelfCrewPrompt q (defaultChoiceAction gSelfCrewPrompt q ch)
    | _ => gSelfCrewPrompt
  let selfCrewOk :=
    (match gSelfCrewPrompt.pending with | .resolutionChoice _ (.crew ..) => true | _ => false) &&
    gSelfCrewDone.pending == .none &&
    (gSelfCrewDone.object! selfCrewId).status.tapped &&
    !gSelfCrewDone.stack.isEmpty

  -- 4e. `removeAnyNumberPlusOne` usable at `X = 0` (`LandsAndMana.hasUsableNonPlainManaAbility`) &
  --     Layer-6 hand/graveyard mana abilities (`LandsAndMana.hasUsableNonPlainManaAbility`)!
  let zeroPlusOneManaDef : CardDef := {
    name := "P60i4 ZeroPlusOneMana", types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .removeCounters .anyNumber (some .plusOnePlusOne) .self]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let gZpo0 := addPermanent g0 zeroPlusOneManaDef p0 p0
  let zpoId := (gZpo0.permanentsOf p0).find? (·.name == zeroPlusOneManaDef.name) |>.get!.id
  let zpoProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.ofColor .green
    spellId := zpoId
    original := gZpo0.object! zpoId
    originalSnapshot := gZpo0.snapshot (gZpo0.object! zpoId)
    sourceId := some zpoId
    removePlusOneX := true
  }
  let handManaGrantDef : CardDef := {
    name := "P60i4 HandManaGrant", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.hand], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantActivated #[{
          cost := CostSpec.ofItems #[.exile (.exact 1) .yourHand .self]
          effect := Effect.addMana #[.colored .red]
        }])
    ]
  }
  let gHandMana0 := insertObject (addPermanent g0 handManaGrantDef p0 p0) bear p0 (.hand p0)
  let zeroPlusAndHandManaOk :=
    gZpo0.hasUsableNonPlainManaAbility p0 &&
    gZpo0.hasUsableNonPlainManaAbility p0 (prop? := some zpoProp) &&
    gHandMana0.hasUsableNonPlainManaAbility p0

  -- 4f. `PlayPermission.landsAllowed` preserved with `anyManaColor := true` AND set to
  --     `!mayCastStyle` in `exileTopForPlayLoop`!
  let gExLandPlay0 := insertObject (insertObject g0 forest p0 .exile) mountain p0 .exile
  let gExLandAnyMana :=
    gExLandPlay0.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, anyManaColor := true, landsAllowed := true, freeCast := false }) } #[]
  let exLandPermCount :=
    (gExLandAnyMana.activeEffects.filter fun (_, s) =>
      match s with | .permission _ (.playFromExile _ pm) _ => pm.landsAllowed && pm.anyMana | _ => false).size
  let gExTopCast0 := insertObject g0 forest p0 (.library p0)
  let gExTopCast := gExTopCast0.exileTopForPlay p0 p0 1 (fun _ _ => "") (mayCastStyle := true)
  let exTopCastPerm :=
    gExTopCast.activeEffects.findSome? fun (_, s) =>
      match s with | .permission _ (.playFromExile _ pm) _ => some pm | _ => none
  let landsAllowedFixOk :=
    exLandPermCount == 2 &&
    exTopCastPerm.any (!·.landsAllowed)

  -- 4g. Empty-option `defaultChoiceAction` vs `answerResolutionChoice` (all 6 arms),
  --     `.mayPayManaForReflexive` with `maxTimes == 0`, and `.mayCastCards` `forcedPerm`!
  let emptyChoices : Array ResolutionChoice := #[
    .allianceMode ⟨99996⟩ #[],
    .gollumMode ⟨99996⟩ #[],
    .stackTriggerUnusedMode ⟨99996⟩ none #[] false,
    .visionMode ⟨99996⟩ #[],
    .chooseCards #[] 1 (.amassArmy .orc 1 none),
    .chooseTokenCopyObject #[] #[] 1 false false none #[] none none
  ]
  let emptyDeclineAllOk :=
    emptyChoices.all fun ch =>
      let gP := g0.change (.pending (.resolutionChoice p0 ch))
      let act := defaultChoiceAction gP p0 ch
      match gP.apply p0 act with
      | .ok gDone => gDone.pending == .none
      | .error _ => false
  let gRefZero :=
    g0.record (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }])
  let refZeroCh : ResolutionChoice :=
    .mayPayManaForReflexive #[.generic 1] 0 { body := .player (.drawCards .you (.const 1)) } none
  let refZeroAct := defaultChoiceAction gRefZero p0 refZeroCh
  let morphLandDef : CardDef := {
    name := "P60i4 ForcedMorphLand", manaCost := ManaCost.empty, types := #[.land]
    keywords := #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])]
  }
  let gForced0 :=
    (insertObject g0 morphLandDef p0 .exile).record
      (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }])
  let forcedExId := (gForced0.objects.find? (fun o => o.zone == .exile && o.name == morphLandDef.name)).get!.id
  let gForced1 :=
    gForced0.createEffect
      (.permission (some p0) (.playFromExile forcedExId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
      (cause := some testCause)
  let gForcedPrompt := gForced1.change (.pending (.resolutionChoice p0 (.mayCastCards #[forcedExId] false false)))
  let forcedDefAct := defaultChoiceAction gForcedPrompt p0 (.mayCastCards #[forcedExId] false false)
  let gForcedCast := mustApply gForcedPrompt p0 forcedDefAct
  let forcedManualErr :=
    match gForcedPrompt.apply p0 (.cast forcedExId) with
    | .error _ => true
    | .ok _ => false
  let choiceSoundnessOk :=
    emptyDeclineAllOk &&
    (match refZeroAct with | .decline => true | _ => false) &&
    (match forcedDefAct with | .decline => true | _ => false) &&
    forcedManualErr &&
    gForcedCast.pending == .none

  -- 4h. `copyAndCast` `freeCast := false` (both `.mayCastCopy` single-copy & `.castCopiesFree`
  --     multi-copy require paying mana!) and hand/graveyard `isDiscardableCard`!
  let paidCopySpell : CardDef := {
    name := "P60i4 PaidCopySpell", manaCost := ManaCost.ofGenericAndColor 1 .blue, types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gCopySingle0 := insertObject g0 paidCopySpell p0 .exile
  let gCopySinglePrompt :=
    gCopySingle0.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, copyAndCast := true, freeCast := false, maxCasts? := some 1 }) } #[]
  let gCopySingleAccept :=
    match gCopySinglePrompt.pending with
    | .resolutionChoice q (.mayCastCopy _) => mustApply gCopySinglePrompt q .accept
    | _ => gCopySinglePrompt
  let gCopyMulti0 := insertObject (insertObject g0 paidCopySpell p0 .exile) paidCopySpell p0 .exile
  let gCopyMultiPrompt :=
    gCopyMulti0.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, copyAndCast := true, freeCast := false }) } #[]
  let gCopyMultiCast :=
    match gCopyMultiPrompt.pending with
    | .resolutionChoice q (.castCopiesFree ids _ _) => mustApply gCopyMultiPrompt q (.cast ids[0]!)
    | _ => gCopyMultiPrompt
  let nonCardTok : CardDef := {
    creature "P60i4 NonCardTok" ManaCost.empty #["Goblin"] 1 1 with
    isToken := true
  }
  let (gTokZone0, tokObj) := g0.createOneToken p0 nonCardTok (cause := some testCause)
  let (gTokGy, tokGyId) := gTokZone0.move tokObj.id (.graveyard p0) none (cause := some testCause)
  let (gTokHand0, tokObj2) := g0.createOneToken p0 nonCardTok (cause := some testCause)
  let (gTokHand, _) := gTokHand0.move tokObj2.id (.hand p0) none (cause := some testCause)
  -- `grantPlayPermToMoved` skips non-castable tokens moved to exile:
  let gTokExGrant :=
    gTokZone0.applyUnified p0
      { body := .moveZone (.inZones .battlefield (.isToken true)) .exile .exile
          { grantPlayPerm? := some { duration := .untilEndOfTurn, landsAllowed := true } } } #[]
  -- `putToBattlefieldLoop` (`onlyFoodArtifact := true`) skips non-card tokens in graveyard (CR 111.8):
  let gTokFoodPut := gTokGy.putToBattlefieldLoop p0 #[tokGyId] (onlyFoodArtifact := true)
  -- `mayCastExiledElseDamage` respects `perm.filter?` and `perm.maxTotalManaValue?`:
  let gElseDmg0 := insertObject g0 paidCopySpell p0 .exile
  let gElseDmgFiltered :=
    gElseDmg0.applyUnified p0
      { body := .bind ⟨3⟩
          (.stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
            { duration := .untilEndOfTurn, filter? := some (.hasType .creature),
              maxTotalManaValue? := some (.const 1) }))
          (.ifCond (.not (.stepSucceeded ⟨3⟩))
            (.damage (.deal .this (.players (.matching .opponent .any)) (.const 2) {}))
            .noop) } #[]
  let copyAndDiscardableOk :=
    gCopySingleAccept.pending == .activateManaAbilities p0 &&
    gCopySingleAccept.proposedSpell.any (fun pr => pr.cost == ManaCost.ofGenericAndColor 1 .blue) &&
    gCopyMultiCast.pending == .activateManaAbilities p0 &&
    gCopyMultiCast.proposedSpell.any (fun pr => pr.cost == ManaCost.ofGenericAndColor 1 .blue) &&
    gTokGy.gyCreatureCards p0 == 0 &&
    EvalExpr.evalValue gTokGy { controller := p0 } (.playerMetric .graveyardSize .you) == 0 &&
    EvalExpr.evalValue gTokHand { controller := p0 } (.playerMetric .handSize .you) == 0 &&
    (EvalExpr.evalObjects gTokGy { controller := p0 } (.inZones { zones := #[.graveyard], owner := .ofPlayer .you } .anyObject)).isEmpty &&
    (EvalExpr.evalObjects gTokHand { controller := p0 } (.inZones { zones := #[.hand], owner := .ofPlayer .you } .anyObject)).isEmpty &&
    !(gTokExGrant.activeEffects.any fun (_, s) => match s with | .permission _ (.playFromExile _ _) _ => true | _ => false) &&
    (gTokFoodPut.permanentsOf p0).isEmpty &&
    gElseDmgFiltered.pending == .none &&
    (gElseDmgFiltered.player ⟨1⟩).life == (18 : Int)

  mustHold60i4 "4a_noCostHoles" noCostHolesOk &&
  mustHold60i4 "4b_originMorphAndResKick" originMorphAndResKickOk &&
  mustHold60i4 "4c_globalHybrid" globalHybridOk &&
  mustHold60i4 "4d_selfCrew" selfCrewOk &&
  mustHold60i4 "4e_zeroPlusAndHandMana" zeroPlusAndHandManaOk &&
  mustHold60i4 "4f_landsAllowedFix" landsAllowedFixOk &&
  mustHold60i4 "4g_choiceSoundness" choiceSoundnessOk &&
  mustHold60i4 "4h_copyAndDiscardable" copyAndDiscardableOk &&
  mustHold60i4 "4.replay"
    (replayOk60i4 #[gNcFb, gOrigMorphFaceDown, gResKickPrompt, gSelfCrewDone, gZpo0,
      gHandMana0, gExLandAnyMana, gExTopCast, gForcedCast, gCopySingleAccept,
      gCopyMultiCast, gTokGy, gTokHand, gTokExGrant, gTokFoodPut, gElseDmgFiltered])

end Phase60Item4EventAlignment

end Mtg.Engine.EventTests
