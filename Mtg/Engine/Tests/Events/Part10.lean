import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase42Item1EventAlignment

private def mustHold42i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase42Item1EventAlignment failed: {label}"

private def replayOk42i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with supertypes := #[.legendary] }
  let legHeroDef : CardDef := { hero with supertypes := #[.legendary] }
  let p2LandDef : CardDef := { name := "P42i1 Forest", types := #[.land] }
  let painLandDef : CardDef := {
    name := "P42i1 PainForge"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.oneOf (.explicit #[.colored .red, .colored .green]) (.const 1)) (damageYou := 1)]
  }
  let leyADef : CardDef := { name := "P42i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P42i1 LeyB", types := #[.enchantment] }
  let legAuraDef : CardDef := {
    name := "P42i1 LegendAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantedCreatureGetsHasAndTypes 1 1 {} #[.hero]]
  }
  let nonLegSubAuraDef : CardDef := {
    name := "P42i1 SpiritAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantedIsOnlySubtypeCantAttackOrBlock .spirit]
  }
  let constructAuraDef : CardDef := {
    name := "P42i1 ConstructAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantedIsConstruct55]
  }

  -- 1a. Cumulative multi-attachment departure invalidation in `Leaving.preBatchLegendSnapshotValid`:
  --     Two legend-granting Auras (`auraA`, `auraB`) departing together from non-legendary `b2`
  --     (via `ceasedToExist` when owned by `p2`, or via CR 800.4a `moved` when owned by `p0` under `p2`'s control)
  --     narrow the 3-copy `#[b1, b2, b3]` prompt to `#[b1, b3]`, while a surviving 3rd legend Aura or
  --     two non-legendary Spirit/Construct Auras keep the snapshot valid.
  let mkMultiAuraLegend (auraOwner : PlayerId) (addSurvivingLegendAura : Bool) :
      Game × ObjectId × ObjectId × ObjectId :=
    let g0 :=
      addPermanent
        (addPermanent
          (addPermanent
            (addPermanent (addPermanent g4 legBearDef p0 p0) bear p0 p0)
            legBearDef p0 p0)
          legAuraDef auraOwner p2)
        legAuraDef auraOwner p2
    let g0 := if addSurvivingLegendAura then addPermanent g0 legAuraDef p0 p0 else g0
    let p0Bears := (g0.permanentsOf p0).filter (·.name == bear.name)
    let b1 := p0Bears[0]!
    let b2 := p0Bears[1]!
    let b3 := p0Bears[2]!
    let p2Auras := (g0.permanentsOf p2).filter (·.name == legAuraDef.name)
    let g1 :=
      (g0.record (GameEvent.attached g0.turnNumber (g0.snapshot p2Auras[0]!) b2.id (cause := testCause))).record
        (GameEvent.attached g0.turnNumber (g0.snapshot p2Auras[1]!) b2.id (cause := testCause))
    let g2 :=
      if addSurvivingLegendAura then
        let p0Aura := (g1.permanentsOf p0).find? (·.name == legAuraDef.name) |>.get!
        g1.record (GameEvent.attached g1.turnNumber (g1.snapshot p0Aura) b2.id (cause := testCause))
      else g1
    (g2.checkSBA, b1.id, b2.id, b3.id)

  let (gTwoCease0, cb1, cb2, cb3) := mkMultiAuraLegend p2 false
  let gTwoCeaseAfter := mustApply gTwoCease0 p2 .concede
  let (gTwoMove0, mb1, mb2, mb3) := mkMultiAuraLegend p0 false
  let gTwoMoveAfter := mustApply gTwoMove0 p2 .concede
  let (gThreeKeep0, kb1, kb2, kb3) := mkMultiAuraLegend p2 true
  let gThreeKeepAfter := mustApply gThreeKeep0 p2 .concede

  let gNonLegTwo0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
        nonLegSubAuraDef p2 p2)
      constructAuraDef p2 p2
  let nlBears := (gNonLegTwo0.permanentsOf p0).filter (·.name == bear.name)
  let nlAuras := gNonLegTwo0.permanentsOf p2
  let gNonLegTwoPaused :=
    ((gNonLegTwo0.record
      (GameEvent.attached gNonLegTwo0.turnNumber (gNonLegTwo0.snapshot nlAuras[0]!) nlBears[0]!.id (cause := testCause))).record
      (GameEvent.attached gNonLegTwo0.turnNumber (gNonLegTwo0.snapshot nlAuras[1]!) nlBears[0]!.id (cause := testCause))).checkSBA
  let gNonLegTwoAfter := mustApply gNonLegTwoPaused p2 .concede

  let item1aOk :=
    gTwoCease0.pending == .chooseLegend p0 bear.name #[cb1, cb2, cb3] &&
    gTwoCeaseAfter.pending == .chooseLegend p0 bear.name #[cb1, cb3] &&
    (gTwoCeaseAfter.permanentsOf p0).any (·.id == cb2) &&
    gTwoMove0.pending == .chooseLegend p0 bear.name #[mb1, mb2, mb3] &&
    gTwoMoveAfter.pending == .chooseLegend p0 bear.name #[mb1, mb3] &&
    gThreeKeep0.pending == .chooseLegend p0 bear.name #[kb1, kb2, kb3] &&
    gThreeKeepAfter.pending == .chooseLegend p0 bear.name #[kb1, kb2, kb3] &&
    gNonLegTwoPaused.pending == .chooseLegend p0 bear.name #[nlBears[0]!.id, nlBears[1]!.id] &&
    gNonLegTwoAfter.pending == .chooseLegend p0 bear.name #[nlBears[0]!.id, nlBears[1]!.id]

  -- 1b. Mid-flush SBA re-pause post-`.closeBatch` slot rewriting (`flushedFromPending` & `!flushedFromPending`,
  --     with `deferRestore == false` and `deferRestore == true`), `mergeLeaveArgs`, and recursive leftmost `.seq` peeling:
  let gTwoGrpBase :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
        legHeroDef p0 p0)
      legHeroDef p0 p0
  let gTwoGrpPaused0 := gTwoGrpBase.checkSBA
  let origTwoBid := gTwoGrpPaused0.currentBatch.get!.1
  let (firstGrpName, firstGrpIds) :=
    match gTwoGrpPaused0.pending with | .chooseLegend _ nm ids => (nm, ids) | _ => ("", #[])
  let secondGrpName := if firstGrpName == bear.name then hero.name else bear.name
  -- Append an outer `.gainLife p1 5` AFTER `.closeBatch origTwoBid _` (after `.checkSBA`), exile one member of group 1 to invalidate it,
  -- and set `p1` at 0 life: with `deferRestore := false`, `.leavePlayersWhoLost` runs right after `.closeBatch` ahead of `.gainLife p1 5`
  -- (eliminating `p1` and pausing on `Pending.mayPayGeneric p0 1`); with `deferRestore := true`, `.checkSBA` is stripped after `.closeBatch`
  -- so `.gainLife p1 5` runs immediately and saves `p1` at 5 life before `keepLegend`'s `receivePriority` checks SBAs!
  let gRepausePend0 :=
    ((gTwoGrpPaused0.chainPendingReplacement (.gainLife p1 5 (some testCause))).setLifeTotal p1 0)
  let (gRepausePendInv, _) := gRepausePend0.move firstGrpIds[0]! .exile none (cause := some testCause)
  -- (i-a) `flushedFromPending == true`, `deferRestore := false`:
  let (gRepPendMid, repPendDid, repPendSaved?, repPendPop, repPendDep, repPendRw) :=
    gRepausePendInv.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (popOuterIn := false) (departedIn := #[p2]) (deferRestore := false)
  let secondKeepId := match gRepPendMid.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999999⟩
  let gRepPendDone := mustApply gRepPendMid p0 (.keepLegend secondKeepId)
  -- (i-b) `flushedFromPending == true`, `deferRestore := true` strips leading `.checkSBA` after `.closeBatch`:
  let (gRepPendDeferMid, _, _, _, _, _) :=
    gRepausePendInv.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (popOuterIn := false) (departedIn := #[p2]) (deferRestore := true)
  let gRepPendDeferDone := mustApply gRepPendDeferMid p0 (.keepLegend secondKeepId)
  -- (i-c) `flushedFromPending == false` (outer-stack `2858–2872` arm: `pendingReplacement := none`, `outerPendingReplacements` holds the paused batch cont):
  let pausedCont := gRepausePendInv.pendingReplacement.get!
  let gRepauseOuterInv :=
    gRepausePendInv.changes #[.pendingReplacement none, .pushOuterPendingReplacement pausedCont]
  let (gRepOuterMid, repOuterDid, _, repOuterPop, _, _) :=
    gRepauseOuterInv.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (popOuterIn := true) (departedIn := #[p2]) (deferRestore := false)
  let gRepOuterDone := mustApply gRepOuterMid p0 (.keepLegend secondKeepId)
  let (gRepOuterDeferMid, _, _, repOuterDeferPop, _, _) :=
    gRepauseOuterInv.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (popOuterIn := true) (departedIn := #[p2]) (deferRestore := true)
  let gRepOuterDeferDone := mustApply gRepOuterDeferMid p0 (.keepLegend secondKeepId)

  let repauseRewriteOk :=
    repPendDid && repPendSaved? == some (.mayPayGeneric p0 1) && repPendPop && repPendDep == #[p2] && repPendRw.isNone &&
    gRepPendMid.currentBatch.map Prod.fst == some origTwoBid &&
    (match gRepPendMid.pending with | .chooseLegend q nm ids => q == p0 && nm == secondGrpName && ids.size == 2 | _ => false) &&
    (gRepPendDone.player p1).leftTheGame &&
    gRepPendDone.pending == .mayPayGeneric p0 1 &&
    -- With `deferRestore := true`, `.checkSBA` was stripped so `.gainLife p1 5` ran right after `.closeBatch` and saved `p1` at 5 life:
    !(gRepPendDeferDone.player p1).leftTheGame &&
    (gRepPendDeferDone.player p1).life == 5 &&
    repOuterDid && repOuterPop &&
    gRepOuterMid.currentBatch.map Prod.fst == some origTwoBid &&
    (gRepOuterDone.player p1).leftTheGame &&
    gRepOuterDone.pending == .mayPayGeneric p0 1 &&
    repOuterDeferPop &&
    !(gRepOuterDeferDone.player p1).leftTheGame &&
    (gRepOuterDeferDone.player p1).life == 5

  -- (ii) `mergeLeaveArgs` in `checkSBACountedWithLeavesCore`, `rewriteRepausedPostCloseBatch`, and `checkSBACounted`:
  let gMerge0 :=
    g4.changes #[
      .pending (.chooseLegend p0 "Stale" #[⟨999999⟩]),
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq
        (.leavePlayersWhoLost (some (.scry p0 1)) false #[p2] none)
        (.gainLife p0 3 (some testCause)))) ]
  let (gMerged1, _, mSaved1, mPop1, mDep1, mRw1) :=
    gMerge0.checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := false) (departedIn := #[p3]) (rewindProposalIn := none)
      (deferRestore := true)
  -- Collision where BOTH `s0` (`some (.scry p0 1)`) and `savedIn` (`some (.mayPayGeneric p0 1)`) are non-`.none`:
  let (gMergedBoth, _, mSavedBoth, mPopBoth, mDepBoth, _) :=
    gMerge0.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (popOuterIn := false) (departedIn := #[p3]) (rewindProposalIn := none)
      (deferRestore := true)
  -- `rw0 <|> rewindProposalIn` (`some false <|> some true == some false`) on mid-flush re-pause:
  let closeOnly := match gTwoGrpPaused0.pendingReplacement with | some (.seq cb _) => cb | _ => .checkSBA
  let gRepMerge0 :=
    gTwoGrpPaused0.change (.pendingReplacement (some (.seq
      closeOnly
      (.leavePlayersWhoLost (some (.scry p0 1)) false #[p2] (some false)))))
  let (gRepMergeInv, _) := gRepMerge0.move firstGrpIds[0]! .exile none (cause := some testCause)
  let (_, _, rmSaved, _, rmDep, rmRw) :=
    gRepMergeInv.checkSBACountedWithLeavesCore
      (savedIn := none) (popOuterIn := false) (departedIn := #[p3]) (rewindProposalIn := some true)
      (deferRestore := true)
  -- `checkSBACounted` peeling `.leavePlayersWhoLost` (with `p1` at 0 life) and re-chaining it ahead of `.gainLife p0 3`:
  let gCountedLeave0 := (gMerge0.setLifeTotal p1 0)
  let (gCountedLeave1, countedLeaveDid) := gCountedLeave0.checkSBACounted
  let gCountedLeaveDone := gCountedLeave1.drainPendingContinuations

  -- (iii) Recursive leftmost `.seq` peeling at depth 3 (both on `pendingReplacement` and on `outerPendingReplacements`):
  let deepSeq : PendingReplacement :=
    .seq
      (.seq
        (.seq .checkSBA (.gainLife p0 2 (some testCause)))
        (.gainLife p0 3 (some testCause)))
      (.gainLife p0 4 (some testCause))
  let gDeepPend0 :=
    g4.changes #[
      .pending (.chooseLegend p0 "Stale" #[⟨999999⟩]),
      .pushContinuationFrame {},
      .pendingReplacement (some deepSeq) ]
  let (gDeepPend1, _) := gDeepPend0.checkSBACounted
  let gDeepPendDone := gDeepPend1.drainPendingContinuations
  let gDeepOuter0 :=
    g4.changes #[
      .pending (.chooseLegend p0 "Stale" #[⟨999999⟩]),
      .pushContinuationFrame {},
      .pushOuterPendingReplacement deepSeq ]
  let (gDeepOuterDone, _, _, deepOuterPop, _, _) :=
    gDeepOuter0.checkSBACountedWithLeavesCore (popOuterIn := true) (deferRestore := false)

  let mergeAndPeelOk :=
    mSaved1 == some (.scry p0 1) && mPop1 && mDep1 == #[p2, p3] && mRw1.isNone &&
    gMerged1.currentBatch.isNone && gMerged1.pendingReplacement.isNone &&
    gMerged1.outerPendingReplacements == #[.gainLife p0 3 (some testCause)] &&
    gMergedBoth.currentBatch.isNone && gMergedBoth.pendingReplacement.isNone &&
    mSavedBoth == some (.scry p0 1) && mPopBoth && mDepBoth == #[p2, p3] &&
    gMergedBoth.outerPendingReplacements ==
      #[.seq (.gainLife p0 3 (some testCause))
             (.restorePending (.mayPayGeneric p0 1) false (departed := #[p2, p3]))] &&
    rmSaved == some (.scry p0 1) && rmDep == #[p2, p3] && rmRw == some false &&
    countedLeaveDid && (gCountedLeave1.player p1).lost && !(gCountedLeave1.player p1).leftTheGame &&
    (gCountedLeaveDone.player p1).leftTheGame &&
    gCountedLeaveDone.pending == .scry p0 1 &&
    gDeepPend1.pendingReplacement != some deepSeq &&
    (gDeepPendDone.player p0).life == (g4.player p0).life + 9 &&
    !deepOuterPop &&
    (gDeepOuterDone.player p0).life == (g4.player p0).life + 9
  let item1bOk := repauseRewriteOk && mergeAndPeelOk

  -- 1c. `ManaAbilities` priority deferral (`finishAndGrantPriorityFwd`, `anyContinuationGrantsPriorityFwd`, `isCarrierOnlyFrame`):
  --     Set `p1` at 0 life and non-active `p2` holding priority so any premature `receivePriority` eliminates `p1` before queued work!
  let gMana0 := ((addPermanent (addPermanent g4 p2LandDef p2 p2) painLandDef p2 p2).change (.priority p2)).setLifeTotal p1 0
  let p2Forest := (gMana0.permanentsOf p2).find? (·.name == p2LandDef.name) |>.get!
  let p2Pain := (gMana0.permanentsOf p2).find? (·.name == painLandDef.name) |>.get!
  -- (i) Unpaused mana ability with `outerPendingReplacements := #[.gainLife p1 5]` drains outer continuation BEFORE `receivePriority p2`:
  let gManaOuter0 :=
    gMana0.changes #[.pushContinuationFrame {}, .pushOuterPendingReplacement (.gainLife p1 5 (some testCause))]
  let gManaOuterDone :=
    gManaOuter0.finishActivateManaAbilityPostSac p2 p2Forest.id p2Forest.printed.name
      (gManaOuter0.snapshot p2Forest) #[.colorless] true (some 0) .none 0 false .none (wasPaused := false)
  -- (ii) Unpaused mana ability when `outerPendingReplacements` already grants priority (`.receivePriority p3`):
  let gManaOuterPrio0 :=
    (gMana0.setLifeTotal p1 20).changes #[.pushContinuationFrame {}, .pushOuterPendingReplacement (.receivePriority p3)]
  let gManaOuterPrioDone :=
    gManaOuterPrio0.finishActivateManaAbilityPostSac p2 p2Forest.id p2Forest.printed.name
      (gManaOuterPrio0.snapshot p2Forest) #[.colorless] true (some 0) .none 0 false .none (wasPaused := false)
  -- (iii) Unpaused mana ability with `interpWait?` (`gainLifeFixed 5` for `p1`):
  let interpWaitP1 : InterpState := {
    ctx := { controller := p1, sourceId := some p2Forest.id }
    queue := #[Instruction.gainLifeFixed 5]
    stack := #[]
  }
  let gManaTrigSeq0 :=
    gMana0.change (.pushContinuationFrame { interpWait? := some interpWaitP1 })
  let gManaTrigSeqDone :=
    gManaTrigSeq0.finishActivateManaAbilityPostSac p2 p2Forest.id p2Forest.printed.name
      (gManaTrigSeq0.snapshot p2Forest) #[.colorless] true (some 0) .none 0 false .none (wasPaused := false)
  let gManaMayRes0 :=
    gMana0.change (.pushContinuationFrame {
      interpWait? := some { interpWaitP1 with stack := #[.branchOnChoice (Instruction.gainLifeFixed 5) .noop], queue := #[] }
      stepEnv := #[(⟨999⟩, { succeeded := true })]
    })
  let gManaMayResDone :=
    gManaMayRes0.finishActivateManaAbilityPostSac p2 p2Forest.id p2Forest.printed.name
      (gManaMayRes0.snapshot p2Forest) #[.colorless] true (some 0) .none 0 false .none (wasPaused := false)
  -- (iv) Unpaused mana ability inside an active non-empty resolution frame (`resolvingAbility := some ab.id`) with no queued work:
  let (gManaResFrame0, activeAb) := gMana0.allocStackAbility p2Forest p2
  let gManaResFrame1 := gManaResFrame0.change (.pushContinuationFrame { resolvingAbility := some activeAb.id })
  let gManaResFrameDone :=
    gManaResFrame1.finishActivateManaAbilityPostSac p2 p2Forest.id p2Forest.printed.name
      (gManaResFrame1.snapshot p2Forest) #[.colorless] true (some 0) .none 0 false .none (wasPaused := false)
  -- (v) Pain-land `Pending.chooseReplacement` pause with `outerPendingReplacements := #[.gainLife p1 5]` on non-active `p2`:
  let gPain0 := addPermanent (addPermanent gMana0 leyADef p2 p2) leyBDef p2 p2
  let pLeyA := (gPain0.permanentsOf p2).find? (·.name == leyADef.name) |>.get!.id
  let pLeyB := (gPain0.permanentsOf p2).find? (·.name == leyBDef.name) |>.get!.id
  let pRidA : ReplacementId := { kind := .addNoncombatDamage, object := some pLeyA }
  let pRidB : ReplacementId := { kind := .multiplyDamage, object := some pLeyB }
  let gPainReady :=
    (((gPain0.createEffect
      (.replacement { id := pRidA, source := some pLeyA, controller := some p2, affectedPlayer := p2, kind := .addNoncombatDamage none 1 })
      (cause := some testCause)).createEffect
      (.replacement { id := pRidB, source := some pLeyB, controller := some p2, affectedPlayer := p2, kind := .multiplyDamage none 2 })
      (cause := some testCause)).changes #[
        .pushContinuationFrame {},
        .pushOuterPendingReplacement (.gainLife p1 5 (some testCause)) ])
  let painIdx := (gPainReady.manaAbilityDefs (gPainReady.object! p2Pain.id)).findIdx? (fun d => d.damageYou > 0) |>.get!
  let gPainPaused : Game :=
    match gPainReady.activateManaAbility p2 p2Pain.id painIdx #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gPainResumed := mustApply gPainPaused p2 (.chooseReplacement pRidA)
  -- Pain-land inside an active `resolvingAbility` frame with no queued work does NOT chain `.receivePriority`:
  let gPainInRes0 :=
    (((gPain0.createEffect
      (.replacement { id := pRidA, source := some pLeyA, controller := some p2, affectedPlayer := p2, kind := .addNoncombatDamage none 1 })
      (cause := some testCause)).createEffect
      (.replacement { id := pRidB, source := some pLeyB, controller := some p2, affectedPlayer := p2, kind := .multiplyDamage none 2 })
      (cause := some testCause)).change (.pushContinuationFrame { resolvingAbility := some activeAb.id }))
  let gPainInResPaused :=
    gPainInRes0.finishActivateManaAbilityPostSac p2 p2Pain.id p2Pain.printed.name
      (gPainInRes0.snapshot p2Pain) #[.colored .red] true (some painIdx) .none 1 false .none (wasPaused := false)
  let gPainInResResumed := mustApply gPainInResPaused p2 (.chooseReplacement pRidA)
  -- (vi) `abortDepartedManaAbilityCont` when `p2` already departed while `outerPendingReplacements` holds `.gainLife p1 5`:
  let gAbortDep0 :=
    ((gMana0.record (GameEvent.playerLost gMana0.turnNumber p2 .conceded (cause := some testCause))).record
      (GameEvent.playerLeftGame gMana0.turnNumber p2 (cause := some testCause))).changes #[
        .pushContinuationFrame {},
        .pushOuterPendingReplacement (.gainLife p1 5 (some testCause)) ]
  let gAbortDepDone :=
    gAbortDep0.finishActivateManaAbilityPostSac p2 p2Forest.id p2Forest.printed.name
      (gAbortDep0.snapshot p2Forest) #[.colorless] true (some 0) .none 0 false .none (wasPaused := true)

  let item1cOk :=
    !(gManaOuterDone.player p1).lost && (gManaOuterDone.player p1).life == 5 && gManaOuterDone.priority == p2 &&
    gManaOuterPrioDone.priority == p3 &&
    !(gManaTrigSeqDone.player p1).lost && (gManaTrigSeqDone.player p1).life == 5 && gManaTrigSeqDone.priority == p2 &&
    !(gManaMayResDone.player p1).lost && (gManaMayResDone.player p1).life == 5 && gManaMayResDone.priority == p2 &&
    !(gManaResFrameDone.player p1).lost && gManaResFrameDone.continuations.size == 1 &&
    gPainPaused.pendingPriority == some p2 &&
    !(gPainResumed.player p1).lost && (gPainResumed.player p1).life == 5 && gPainResumed.priority == p2 &&
    !(gPainInResResumed.player p1).lost &&
    !(gAbortDepDone.player p1).lost && (gAbortDepDone.player p1).life == 5 && gAbortDepDone.priority == p0

  mustHold42i1 "1a.cumulativeLegendAtt" item1aOk &&
  mustHold42i1 "1b.repauseMergePeel" item1bOk &&
  mustHold42i1 "1c.manaOuterPriorityDeferral" item1cOk &&
  mustHold42i1 "1.replay"
    (replayOk42i1 #[gTwoCeaseAfter, gTwoMoveAfter, gThreeKeepAfter, gNonLegTwoAfter,
      gRepPendMid, gRepPendDone, gRepPendDeferDone, gRepOuterMid, gRepOuterDone, gRepOuterDeferDone,
      gCountedLeaveDone, gDeepPendDone, gDeepOuterDone,
      gManaOuterDone, gManaOuterPrioDone, gManaTrigSeqDone, gManaMayResDone,
      gPainPaused, gPainResumed, gAbortDepDone])

end Phase42Item1EventAlignment

section Phase42Item2EventAlignment

private def mustHold42i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase42Item2EventAlignment failed: {label}"

private def replayOk42i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let stealerDef : CardDef := { name := "P42i2 Stealer", types := #[.artifact] }
  let relicDef : CardDef := { name := "P42i2 Relic", types := #[.artifact] }
  let auraDef : CardDef := { name := "P42i2 Aura", types := #[.enchantment], subtypes := #["Aura"] }
  let embDef : CardDef := { name := "P42i2 FraEmblem", types := #[] }
  let ltbWatcherDef : CardDef := {
    creature "P42i2 LTBWatcher" ManaCost.empty #["Cleric"] 2 2 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger (.permanentLeaves (.all #[.hasType .creature, .controlledBy .you]))
        { body := Instruction.gainLifeFixed 3 }
    ]
  }

  -- 2a. Pre-`playerLeftGame` `preLeave` `ceasedToExist` LKI + CR 603.10a trigger, departing-attachment
  --     `unattachFrom` suppression, and pre-leave dynamic `.control` combat/`.ringBearer` reconciliation
  --     without mislabeling zero-control-effect CR 800.4a exiles as CR 800.4c:
  -- (i) `o1` (`p2Stealer`, owned by `p2`) precedes `o2` (`p2Relic`, owned by `p2`, animated & controlled by `p0`
  --     via `.whileSourceOnBattlefield o1.id`), plus `o3` (`p2Bear`, owned & default-controlled by `p2`):
  let gLki0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 ltbWatcherDef p0 p0) stealerDef p2 p2)
        relicDef p2 p2)
      bear p2 p2
  let p2Stealer := (gLki0.permanentsOf p2).find? (·.name == stealerDef.name) |>.get!
  let p2Relic := (gLki0.permanentsOf p2).find? (·.name == relicDef.name) |>.get!
  let p2PlainBear := (gLki0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let gLki1 :=
    (((gLki0.recordPutCounters p2Relic.id .charge 1 (some p0) (cause := some testCause)).createEffect
      (.layered (.objects #[p2Relic.id]) (.control p0) (.whileSourceOnBattlefield p2Stealer.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[p2Relic.id]) (.types .add #[.creature] #[.construct] #[]) (.whileSourceOnBattlefield p2Stealer.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[p2Relic.id]) (.ptSet 3 3) (.whileSourceOnBattlefield p2Stealer.id))
      (cause := some testCause)
  let preLkiEvIdx := gLki1.events.size
  let gLkiAfter := mustApply gLki1 p2 .concede
  let lkiSlice := gLkiAfter.events.extract preLkiEvIdx gLkiAfter.events.size
  let ceasedSnap? (oid : ObjectId) : Option EventObject :=
    lkiSlice.findSome? fun ev =>
      match ev.change with
      | .rules (.zone (.ceasedToExist eo)) => if eo.id == some oid then some eo else none
      | _ => none
  let relicCeased? := ceasedSnap? p2Relic.id
  let bearCeased? := ceasedSnap? p2PlainBear.id
  let preLeaveLkiOk :=
    relicCeased?.any (fun eo => eo.controller == some p0 && eo.creature && eo.power == some 3) &&
    bearCeased?.any (fun eo => eo.controller == some p2) &&
    -- Surviving `p0`'s CR 603.10a `.creatureYouControlLeaves` trigger fired and went onto the stack!
    gLkiAfter.stack.size == 1

  -- (ii) Departing-attachment `unattachFrom` suppression (`skipIds`):
  --      `hostP2` (owned by `p2`) has `auraP2` (owned by `p2`, added AFTER `hostP2`) and `auraP0` (owned by `p0`):
  let gUnatt0 :=
    addPermanent (addPermanent (addPermanent g4 bear p2 p2) auraDef p2 p2) auraDef p0 p0
  let hostP2 := (gUnatt0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let auraP2 := (gUnatt0.permanentsOf p2).find? (·.name == auraDef.name) |>.get!
  let auraP0 := (gUnatt0.permanentsOf p0).find? (·.name == auraDef.name) |>.get!
  let gUnatt1 :=
    (gUnatt0.record (GameEvent.attached gUnatt0.turnNumber (gUnatt0.snapshot auraP2) hostP2.id (cause := testCause))).record
      (GameEvent.attached gUnatt0.turnNumber (gUnatt0.snapshot auraP0) hostP2.id (cause := testCause))
  let preUnattEvIdx := gUnatt1.events.size
  let preUnattLogIdx := gUnatt1.log.size
  let gUnattAfter := mustApply gUnatt1 p2 .concede
  let unattEvents :=
    (gUnattAfter.events.extract preUnattEvIdx gUnattAfter.events.size).filterMap fun ev =>
      match ev.change with
      | .rules (.permanent (.unattached eo hostId)) => some (eo.id, hostId)
      | _ => none
  let unattLogs :=
    (gUnattAfter.log.extract preUnattLogIdx gUnattAfter.log.size).filter (·.contains "becomes unattached")
  let skipUnattachOk :=
    unattEvents == #[(some auraP0.id, hostP2.id)] &&
    unattLogs.size == 1

  -- (iii) Dynamic `.creaturesControlledBy p2` `.control p0` clears combat & `.ringBearer` on `cDyn` (`owner := p0, defaultController := p2`),
  --       while `cPlain` (`relicDef` artifact, `owner := p0, defaultController := p2`, zero control effects in Layer 2) is exiled under CR 800.4a (NOT CR 800.4c):
  let gDyn0 := addPermanent (addPermanent g4 bear p0 p2) relicDef p0 p2
  let cDyn := (gDyn0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let cPlain := (gDyn0.permanentsOf p2).find? (·.name == relicDef.name) |>.get!
  let gDyn1 :=
    (((gDyn0.createEffect (.layered (.creaturesControlledBy p2) (.control p0) .indefinite)
      (cause := some testCause)).record
      (GameEvent.designation gDyn0.turnNumber (gDyn0.snapshot cDyn) .ringBearer true (cause := testCause))).record
      (GameEvent.attacked gDyn0.turnNumber p0 (gDyn0.snapshot cDyn) p1 (cause := testCause)))
  let preDynEvIdx := gDyn1.events.size
  let preDynLogIdx := gDyn1.log.size
  let gDynAfter := mustApply gDyn1 p2 .concede
  let dynEvSlice := gDynAfter.events.extract preDynEvIdx gDynAfter.events.size
  let dynLogs := gDynAfter.log.extract preDynLogIdx gDynAfter.log.size
  let dynControlAnd8004aOk :=
    (gDynAfter.player p0).ringBearerId.isNone &&
    dynEvSlice.any (fun ev => match ev.change with | .rules (.combat (.removedFromCombat eo)) => eo.id == some cDyn.id | _ => false) &&
    (gDynAfter.followMovedToZone? cDyn.id (· == .exile)).isSome &&
    (gDynAfter.followMovedToZone? cPlain.id (· == .exile)).isSome &&
    dynLogs.any (fun s => s.contains relicDef.name && s.contains "(CR 800.4a)") &&
    !dynLogs.any (fun s => s.contains relicDef.name && s.contains "(CR 800.4c)")
  let item2aOk := preLeaveLkiOk && skipUnattachOk && dynControlAnd8004aOk

  -- 2b. Reachable `"<emblem> ends"` logging and `.commandEmblem` / `.whileInZone` expiry in `Turns.expireUntilTurnCommandEffects`:
  let gEmb0 := insertObject (addPermanent g4 bear p0 p0) embDef p2 .command (some p2)
  let embBear := (gEmb0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let embObj := (gEmb0.objects.filter (·.zone == .command))[0]!
  let gEmb1 :=
    (gEmb0.createEffect (.gameRule (.commandEmblem embObj.id) (.untilNextTurnOf p0)) (cause := some testCause)).createEffect
      (.layered (.objects #[embBear.id]) (.ptModify 2 2) (.whileInZone embObj.id .command)) (cause := some testCause)
  let gEmbAfter := gEmb1.expireUntilTurnCommandEffects p0
  let item2bOk :=
    (gEmbAfter.findObject? embObj.id).isNone &&
    gEmbAfter.activeEffects.isEmpty &&
    gEmbAfter.log.any (· == s!"{embDef.name} ends")

  -- 2c. 2HG ending-shared-turn guard (regular & extra shared turns when `seats == #[⟨0⟩]`) and
  --     simultaneous dead-team single-batch expiry (including `.untilNextTurnOf` & `.untilEndOfNextTurnOf` copies):
  let cfg3Teams : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "C0", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "C1", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed := 422
    startingPlayer := some 0
  }
  let gTeams0 : Game :=
    match Start.start cfg3Teams with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  let gTeamsBears := addPermanent (addPermanent gTeams0 bear ⟨2⟩ ⟨2⟩) bear ⟨2⟩ ⟨2⟩
  let tbBears := (gTeamsBears.permanentsOf ⟨2⟩).filter (·.name == bear.name)
  let tb1 := tbBears[0]!
  let tb2 := tbBears[1]!
  -- (i) Regular shared turn (`activePlayer == ⟨0⟩`, `seats == #[⟨0⟩]`): Team A concedes on `⟨0⟩`:
  let gRegEffs :=
    ((((gTeamsBears.createEffect (.layered (.objects #[tb1.id]) (.copy hero) (.untilNextTurnOf ⟨1⟩))
      (cause := some testCause)).createEffect
      (.layered (.objects #[tb2.id]) (.copy hero) (.untilEndOfNextTurnOf ⟨0⟩))
      (cause := some testCause)).createEffect
      (.layered (.objects #[tb1.id]) (.ptModify 1 1) (.untilNextTurnOf ⟨0⟩))
      (cause := some testCause)).createEffect
      (.layered (.objects #[tb2.id]) (.ptModify 2 2) (.untilEndOfNextTurnOf ⟨1⟩))
      (cause := some testCause))
  let gRegConceded := mustApply gRegEffs ⟨0⟩ .concede
  -- Advance to Team B (`⟨2⟩`): Team A's current shared turn just ended, so NO `.untilNextTurnOf` / `.untilEndOfNextTurnOf` of `⟨0⟩` or `⟨1⟩` expires yet!
  let gTeamBBegan := gRegConceded.startNextTurnAndBegin
  let stillActiveOnTeamB :=
    gTeamBBegan.activePlayer == ⟨2⟩ &&
    gTeamBBegan.name (gTeamBBegan.object! tb1.id) == hero.name &&
    gTeamBBegan.name (gTeamBBegan.object! tb2.id) == hero.name &&
    gTeamBBegan.activeEffects.size == 4
  -- Finish Team B (`⟨2⟩` -> `⟨3⟩`) and Team C (`⟨4⟩` -> `⟨5⟩`), then skip dead Team A (`⟨0⟩, ⟨1⟩`) as `⟨5⟩` -> `⟨2⟩`:
  let gTeamCC1 := ((gTeamBBegan.startNextTurnAndBegin).startNextTurnAndBegin).startNextTurnAndBegin
  let preSkipEvIdx := gTeamCC1.events.size
  let gAfterDeadTeamSkip := gTeamCC1.startNextTurnAndBegin
  let skipSlice := gAfterDeadTeamSkip.events.extract preSkipEvIdx gAfterDeadTeamSkip.events.size
  let expiredBatches :=
    skipSlice.filterMap fun ev =>
      match ev.change with
      | .rules (.continuousEffect (.expired ..)) => ev.batch
      | _ => none
  let singleBatchDeadTeamOk :=
    stillActiveOnTeamB &&
    gTeamCC1.activePlayer == ⟨5⟩ &&
    gTeamCC1.activeEffects.size == 4 &&
    gAfterDeadTeamSkip.activePlayer == ⟨2⟩ &&
    gAfterDeadTeamSkip.activeEffects.isEmpty &&
    gAfterDeadTeamSkip.name (gAfterDeadTeamSkip.object! tb1.id) == bear.name &&
    gAfterDeadTeamSkip.name (gAfterDeadTeamSkip.object! tb2.id) == bear.name &&
    expiredBatches.size == 4 &&
    expiredBatches.all (· == expiredBatches[0]!)

  -- (ii) Shared EXTRA turn (`seats == #[⟨0⟩]`, `seatsExtra == true`, `extraTurns == #[⟨1⟩]`): Team A concedes on `⟨0⟩`:
  let gExPrep :=
    ((gTeamsBears.startNextTurnAndBegin).record
      (GameEvent.extraTurnAdded gTeamsBears.turnNumber ⟨0⟩ (cause := testCause))).startNextTurnAndBegin
  let gExEffs :=
    (gExPrep.createEffect (.layered (.objects #[tb1.id]) (.ptModify 1 1) (.untilNextTurnOf ⟨1⟩))
      (cause := some testCause)).createEffect
      (.layered (.objects #[tb2.id]) (.copy hero) (.untilEndOfNextTurnOf ⟨1⟩))
      (cause := some testCause)
  let gExTeamB := (mustApply gExEffs ⟨0⟩ .concede).startNextTurnAndBegin
  let extraSharedGuardOk :=
    gExPrep.activePlayer == ⟨0⟩ &&
    gExPrep.currentSharedTurnIsExtra &&
    gExPrep.extraTurns == #[⟨1⟩] &&
    gExTeamB.activePlayer == ⟨2⟩ &&
    gExTeamB.activeEffects.any (fun (_, e) => e.duration == .untilNextTurnOf ⟨1⟩) &&
    gExTeamB.name (gExTeamB.object! tb2.id) == hero.name

  -- (iii) Living teammate (`!departed` on `beginTurn`): `.untilNextTurnOf ⟨5⟩` copy ends when `⟨4⟩`'s shared turn begins,
  --       while `.untilEndOfNextTurnOf ⟨5⟩` copy stays active during that turn!
  let gLiv0 :=
    ((gTeamsBears.startNextTurnAndBegin).startNextTurnAndBegin) -- now on `⟨2⟩`
  let gLivEffs :=
    (gLiv0.createEffect (.layered (.objects #[tb1.id]) (.copy hero) (.untilNextTurnOf ⟨5⟩))
      (cause := some testCause)).createEffect
      (.layered (.objects #[tb2.id]) (.copy hero) (.untilEndOfNextTurnOf ⟨5⟩))
      (cause := some testCause)
  let gLivTeamCBegan := (gLivEffs.startNextTurnAndBegin).startNextTurnAndBegin -- `⟨2⟩` -> `⟨3⟩` -> `⟨4⟩` (teammate of `⟨5⟩`)
  let livingTeammateCopyOk :=
    gLivTeamCBegan.activePlayer == ⟨4⟩ &&
    gLivTeamCBegan.name (gLivTeamCBegan.object! tb1.id) == bear.name &&
    gLivTeamCBegan.name (gLivTeamCBegan.object! tb2.id) == hero.name
  let item2cOk := singleBatchDeadTeamOk && extraSharedGuardOk && livingTeammateCopyOk

  mustHold42i2 "2a.preLeaveLkiAndUnattach" item2aOk &&
  mustHold42i2 "2b.reachableFraEmblemEnds" item2bOk &&
  mustHold42i2 "2c.twoHgSharedTurnExpiry" item2cOk &&
  mustHold42i2 "2.replay"
    (replayOk42i2 #[gLkiAfter, gUnattAfter, gDynAfter, gEmbAfter,
      gTeamBBegan, gAfterDeadTeamSkip, gExTeamB, gLivTeamCBegan])

end Phase42Item2EventAlignment

section Phase42Item3EventAlignment

private def mustHold42i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase42Item3EventAlignment failed: {label}"

private def replayOk42i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let srcDefA : CardDef := creature "P42i3 SrcA" ManaCost.empty #["Construct"] 3 3
  let srcDefB : CardDef := creature "P42i3 SrcB" ManaCost.empty #["Construct"] 3 3
  let noTrampleScope : ObjectScope := .creaturesWithout #[Keyword.trample]

  -- 3a. `durationActiveContinuouslySince`, `ZoneEvent.created` `eo.zone`, in-place `.materializeObject` guard,
  --     and pre-`events[0]` phasing helpers in `Core.lean`:
  let gCont0 :=
    addPermanent (addPermanent (addPermanent g4 bear p0 p0) srcDefA p0 p0) srcDefB p0 p0
  let phBear := (gCont0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let srcA := (gCont0.permanentsOf p0).find? (·.name == srcDefA.name) |>.get!
  let srcB := (gCont0.permanentsOf p0).find? (·.name == srcDefB.name) |>.get!
  -- Both `srcA` (on battlefield, phased in) and `srcB` (1 `.charge` counter) ARE active when `phBear` phases out at `pIdx`:
  let gCont1 :=
    (((gCont0.recordPutCounters srcB.id .charge 1 (some p0) (cause := some testCause)).createEffect
      (.layered (.objects #[phBear.id]) (.control p2) (.whileSourceOnBattlefield srcA.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[phBear.id]) (.copy srcDefB) (.whileSourceHasCounter srcB.id .charge))
      (cause := some testCause))
  let pIdx := gCont1.events.size
  let gContOut := gCont1.phaseOut (gCont1.object! phBear.id) (cause := some testCause)
  -- Toggle `srcA` out & back in, and drop `srcB` to 0 `.charge` counters & back to 1 (via `PermanentEvent.counters`
  -- so `.whileSourceHasCounter srcB.id .charge` remains in `activeEffects`) while `phBear` stays phased out:
  let gContAOut := gContOut.phaseOut (gContOut.object! srcA.id) (cause := some testCause)
  let gContAIn := gContAOut.phaseIn (gContAOut.object! srcA.id) (cause := some testCause)
  let gContBZero :=
    gContAIn.record (GameEvent.rules gContAIn.turnNumber
      (.permanent (.counters (.object (gContAIn.snapshot (gContAIn.object! srcB.id))) .charge (.removed 1) (some p0)))
      testCause)
  let gContToggled := gContBZero.recordPutCounters srcB.id .charge 1 (some p0) (cause := some testCause)
  let gContBearIn := gContToggled.phaseIn (gContToggled.object! phBear.id) (cause := some testCause)
  let contDurOk :=
    !gContToggled.durationActiveContinuouslySince (.whileSourceOnBattlefield srcA.id) (pIdx + 1) &&
    !gContToggled.durationActiveContinuouslySince (.whileSourceHasCounter srcB.id .charge) (pIdx + 1) &&
    -- While phased out, CR 702.26f ended both effects on `phBear` and CR 702.26b prevented re-application:
    gContToggled.controllerOf (gContToggled.object! phBear.id) == some p0 &&
    gContToggled.name (gContToggled.object! phBear.id) == bear.name &&
    -- Once `phBear` phases back in, both active dynamic effects apply again:
    gContBearIn.controllerOf (gContBearIn.object! phBear.id) == some p2 &&
    gContBearIn.name (gContBearIn.object! phBear.id) == srcDefB.name

  -- `ZoneEvent.created` in `.exile` (even with `phasedOut := true` on snapshot) is NOT treated as battlefield phased-out:
  let gExCr0 := insertObject g4 bear p0 .exile
  let exObj := (gExCr0.objects.filter (·.zone == .exile))[0]!
  let exSnap : EventObject := { (gExCr0.snapshot exObj) with zone := .exile, phasedOut := true }
  let gExCr1 := gExCr0.record (GameEvent.created gExCr0.turnNumber p0 exSnap (cause := testCause))
  let exileCreatedOk :=
    gExCr1.objectZoneAndPhasedOutAt? exObj.id gExCr1.events.size == some (Zone.exile, false) &&
    !gExCr1.objectWasPhasedOutAt exObj gExCr1.events.size &&
    (gExCr1.latestPhaseOutIdxOf? (gExCr1.object! exObj.id)).isNone

  -- In-place `.materializeObject` while `mBear` is already phased out does NOT advance `latestPhaseOutIdxOf?`:
  let gInPlace0 := addPermanent g4 bear p0 p0
  let mBear := (gInPlace0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let pIdxMat := gInPlace0.events.size
  let gInPlaceOut := gInPlace0.phaseOut mBear (cause := some testCause)
  let gInPlaceEff :=
    gInPlaceOut.createEffect (.layered noTrampleScope (.ptModify 4 4) .untilEndOfTurn) (cause := some testCause)
  let curMBear := gInPlaceEff.object! mBear.id
  let gInPlaceRemat := gInPlaceEff.change (.materializeObject curMBear)
  let inPlaceMatOk :=
    gInPlaceRemat.latestPhaseOutIdxOf? (gInPlaceRemat.object! mBear.id) == some pIdxMat &&
    gInPlaceRemat.power (gInPlaceRemat.object! mBear.id) == 2

  -- Pre-`events[0]` (`quiet`) phasing helpers & `phaseOutIdx? == some 0`:
  let gPreQuiet0 :=
    quiet
      ((gCont0.recordPutCounters srcB.id .charge 2 (some p0) (cause := some testCause)).phaseOut
        phBear (cause := some testCause))
  let gPreQuietPostEff :=
    gPreQuiet0.createEffect (.layered noTrampleScope (.ptModify 5 5) .untilEndOfTurn) (cause := some testCause)
  let preQuietHelpersOk :=
    gPreQuietPostEff.objectZoneAndPhasedOutAt? phBear.id 0 == some (Zone.battlefield, true) &&
    gPreQuietPostEff.objectWasPhasedOutAt (gPreQuietPostEff.object! phBear.id) 0 &&
    gPreQuietPostEff.objectCounterCountAt srcB.id .charge 0 == 2 &&
    -- Post-`events[0]` non-explicit `oneShotEffect` does NOT affect pre-`events[0]` phased-out `phBear`:
    gPreQuietPostEff.power (gPreQuietPostEff.object! phBear.id) == 2
  let item3aOk := contDurOk && exileCreatedOk && inPlaceMatOk && preQuietHelpersOk

  -- 3b. `Core.hasSummoningSickness`: phased-out controller check, `leftTheGame` vs `lost`,
  --     `.whileSourceHasCounter`, and DFC `PermanentEvent.transformed`:
  -- (i) Creature phased out under `p1`'s control at start of `p0`'s turn (including `quiet` `effStartIdx? == none`),
  --     then phased in under `p0`'s static `.control p0` -> HAS summoning sickness!
  --     And creature controlled by `p0` since turn start that phases out, briefly reverts to `p1` while phased out
  --     (when `stSrc` phases out & back in), and phases in -> HAS summoning sickness!
  let gPhCtrl0 := readyControlledForTurn (addPermanent g4 bear p1 p1) p0
  let p1PhBear := (gPhCtrl0.permanentsOf p1)[0]!
  let gPhUnderP1 := gPhCtrl0.phaseOut p1PhBear (cause := some testCause)
  let gP0TurnBegan := (gPhUnderP1.record (GameEvent.turnBegan 2 p0 (extra := false)))
  let gStolenIn :=
    (gP0TurnBegan.createEffect (.layered noTrampleScope (.control p0) .indefinite)
      (cause := some (.gameRule .staticAbility))).phaseIn (gP0TurnBegan.object! p1PhBear.id) (cause := some testCause)
  let gQuietPhUnderP1 :=
    ((quiet gPhUnderP1).createEffect (.layered noTrampleScope (.control p0) .indefinite)
      (cause := some (.gameRule .staticAbility)))
  let gQuietPhIn := gQuietPhUnderP1.phaseIn (gQuietPhUnderP1.object! p1PhBear.id) (cause := some testCause)

  let gMidPh0 := addPermanent (addPermanent g4 bear p1 p1) srcDefA p0 p0
  let midBear := (gMidPh0.permanentsOf p1)[0]!
  let midSrc := (gMidPh0.permanentsOf p0).find? (·.name == srcDefA.name) |>.get!
  let gMidPh1 :=
    readyControlledForTurn
      (gMidPh0.createEffect (.layered (.objects #[midBear.id]) (.control p0) (.whileSourceOnBattlefield midSrc.id))
        (cause := some testCause)) p0
  let gMidPhOut1 := gMidPh1.phaseOut (gMidPh1.object! midBear.id) (cause := some testCause)
  let gMidPhOut2 := gMidPhOut1.phaseOut (gMidPhOut1.object! midSrc.id) (cause := some testCause)
  let gMidPhIn1 := gMidPhOut2.phaseIn (gMidPhOut2.object! midSrc.id) (cause := some testCause)
  let gMidPhToggled := gMidPhIn1.phaseIn (gMidPhIn1.object! midBear.id) (cause := some testCause)

  -- (ii) `leftTheGame` vs `lost` in historical slice (`controllerOfAt`):
  --      Between `playerLost p2` and `playerLeftGame p2`, `pl.leftTheGame` is still `false`, so `cDefP2` (`defaultController := some p2`)
  --      still has `controllerOfAt == some p2` before `playerLeftGame` and `none` after `playerLeftGame`!
  let gLostVsLeft0 := addPermanent g4 bear p0 p2
  let cDefP2 := (gLostVsLeft0.permanentsOf p2)[0]!
  let gAfterLostOnly := gLostVsLeft0.record (GameEvent.playerLost gLostVsLeft0.turnNumber p2 .conceded (cause := some testCause))
  let betweenEvLen := gAfterLostOnly.events.size
  let gAfterLeft := gAfterLostOnly.record (GameEvent.playerLeftGame gAfterLostOnly.turnNumber p2 (cause := some testCause))

  -- (iii) `.whileSourceHasCounter` Layer 2 control in `hasSummoningSickness` (created in log and pre-`events[0]` + expired):
  let gCntSick0 := addPermanent (addPermanent g4 bear p1 p1) srcDefB p0 p0
  let cntBear := (gCntSick0.permanentsOf p1)[0]!
  let cntSrc := (gCntSick0.permanentsOf p0).find? (·.name == srcDefB.name) |>.get!
  let gCntSick1 :=
    readyControlledForTurn
      ((gCntSick0.recordPutCounters cntSrc.id .charge 1 (some p0) (cause := some testCause)).createEffect
        (.layered (.objects #[cntBear.id]) (.control p0) (.whileSourceHasCounter cntSrc.id .charge))
        (cause := some testCause)) p0
  let cntReadyBefore := !gCntSick1.hasSummoningSickness (gCntSick1.object! cntBear.id)
  let gCntToggled :=
    (gCntSick1.recordRemoveCounters cntSrc.id .charge 1 (some p0) (cause := some testCause)).recordPutCounters
      cntSrc.id .charge 1 (some p0) (cause := some testCause)

  -- Pre-`events[0]` `.whileSourceHasCounter` `.control p1` effect on `p0`'s creature that toggles on mid-turn and then expires:
  let gPreCnt0 :=
    quiet
      (readyControlledForTurn
        ((addPermanent (addPermanent g4 bear p0 p0) srcDefB p0 p0)) p0)
  let preCntBearId := (gPreCnt0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let preCntSrcId := (gPreCnt0.permanentsOf p0).find? (·.name == srcDefB.name) |>.get!.id
  let gPreCnt1 :=
    quiet
      (gPreCnt0.createEffect
        (.layered (.objects #[preCntBearId]) (.control p1) (.whileSourceHasCounter preCntSrcId .charge))
        (cause := some testCause))
  let preCntReadyBefore := !gPreCnt1.hasSummoningSickness (gPreCnt1.object! preCntBearId)
  let gPreCntTurnedOn := gPreCnt1.recordPutCounters preCntSrcId .charge 1 (some p0) (cause := some testCause)
  let (gPreCntExpired, _) := gPreCntTurnedOn.move preCntSrcId (.graveyard p0) none

  -- (iv) DFC `PermanentEvent.transformed` in `hasSummoningSickness`:
  --      Front face has `trample := false` (stolen by `noTrampleScope` `.control p0`), back face has `trample := true` (reverts to `p1`!):
  let dfcBackTrample : CardDef := { bear with name := "P42i3 TrampleBack", keywords := #[Keyword.trample] }
  let dfcFrontNoTrample : CardDef := { bear with name := "P42i3 PlainFront", otherFace := some dfcBackTrample }
  let gDfc0 :=
    readyControlledForTurn
      ((addPermanent g4 dfcFrontNoTrample p1 p1).createEffect
        (.layered noTrampleScope (.control p0) .indefinite) (cause := some (.gameRule .staticAbility))) p0
  let dfcId := (gDfc0.permanentsOf p0).find? (·.name == dfcFrontNoTrample.name) |>.get!.id
  let dfcReadyBefore := !gDfc0.hasSummoningSickness (gDfc0.object! dfcId)
  let gDfcBackAndForth :=
    (gDfc0.transformPermanent p0 (some dfcId) (cause := some testCause)).transformPermanent
      p0 (some dfcId) (cause := some testCause)

  let item3bOk :=
    gStolenIn.hasSummoningSickness (gStolenIn.object! p1PhBear.id) &&
    gQuietPhIn.hasSummoningSickness (gQuietPhIn.object! p1PhBear.id) &&
    gMidPhToggled.hasSummoningSickness (gMidPhToggled.object! midBear.id) &&
    gAfterLeft.controllerOfAt (gAfterLeft.object! cDefP2.id) betweenEvLen == some p2 &&
    gAfterLeft.controllerOfAt (gAfterLeft.object! cDefP2.id) gAfterLeft.events.size == none &&
    cntReadyBefore && gCntToggled.hasSummoningSickness (gCntToggled.object! cntBear.id) &&
    preCntReadyBefore &&
    gPreCntExpired.activeEffects.isEmpty &&
    gPreCntExpired.controllerOf (gPreCntExpired.object! preCntBearId) == some p0 &&
    gPreCntExpired.hasSummoningSickness (gPreCntExpired.object! preCntBearId) &&
    dfcReadyBefore && gDfcBackAndForth.hasSummoningSickness (gDfcBackAndForth.object! dfcId)

  -- 3c. `Phasing.phaseInControlled` historical `Core.controllerOfAt` lookup:
  --     (i) `matStealId` materialized phased out while controlled by `p1` via `p1`'s `srcDefA` (which leaves when `p1` concedes,
  --         so current `g.controllerOf` is `some p0` and `appliedControlEffectIds` is empty!), PLUS a later `.control p2` effect
  --         created AFTER `matStealId` arrived phased out;
  --     (ii) `preId` already phased out under `p1`'s `.whileSourceOnBattlefield p0Src.id` control before `events[0]` (`quiet`),
  --          plus `concedePreId` & `revPreId` exercising real `concede` (`ctrlEids` expiration of pre-log `.control p1` effects
  --          with both earlier and later surviving pre-log `.control p2` timestamps)!
  let gHist0 := addPermanent g4 srcDefA p1 p1
  let p1Src := (gHist0.permanentsOf p1)[0]!
  let gHist1 :=
    gHist0.createEffect (.layered noTrampleScope (.control p1) (.whileSourceOnBattlefield p1Src.id))
      (cause := some (.gameRule .staticAbility))
  let gHist2 :=
    insertObject gHist1 bear p0 .battlefield (some p0) { summoningSick := false, phasedOut := true }
  let matStealId := gHist2.objects.back!.id
  -- Create a LATER static `.control p2` after `matStealId` arrived phased out, and emit an in-place `.materializeObject` while phased out:
  let gHist3 :=
    gHist2.createEffect (.layered (.objects #[matStealId]) (.control p2) .indefinite)
      (cause := some (.gameRule .staticAbility))
  let curMatSteal := gHist3.object! matStealId
  let gHist4 := gHist3.change (.materializeObject curMatSteal)
  let gHistAfterP1Concede := (mustApply gHist4 p1 .concede).startNextTurnAndBegin

  -- Pre-`events[0]` (`quiet`) phased-out permanent controlled at `evLen = 0` by `p1` via `.whileSourceOnBattlefield p0Src.id`,
  -- then `p0Src` phases out after `events[0]`:
  let gPre0 := addPermanent (addPermanent g4 bear p0 p0) srcDefA p0 p0
  let preId := (gPre0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let p0SrcId := (gPre0.permanentsOf p0).find? (·.name == srcDefA.name) |>.get!.id
  let gPre1 :=
    quiet
      ((gPre0.createEffect (.layered (.objects #[preId]) (.control p1) (.whileSourceOnBattlefield p0SrcId))
        (cause := some testCause)).phaseOut (gPre0.object! preId) (cause := some testCause))
  let gPreSrcOut := gPre1.phaseOut (gPre1.object! p0SrcId) (cause := some testCause)
  let gPreExpiredAndSkip := (mustApply gPreSrcOut p1 .concede).startNextTurnAndBegin

  -- Real `concede p1` (`ctrlEids` expiration) on a quiet position where `concedePreId` had an earlier `.control p2`
  -- and a later `.control p1` before `events[0]`, and `revPreId` had an earlier `.control p1` and a later `.control p2`:
  let gRealPre0 := addPermanent (addPermanent g4 bear p0 p0) hero p0 p0
  let concedePreId := (gRealPre0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let revPreId := (gRealPre0.permanentsOf p0).find? (·.name == hero.name) |>.get!.id
  let gRealPre1 :=
    quiet
      ((((((gRealPre0.createEffect (.layered (.objects #[concedePreId]) (.control p2) .indefinite)
            (cause := some testCause)).createEffect
          (.layered (.objects #[concedePreId]) (.control p1) .indefinite)
          (cause := some testCause)).createEffect
        (.layered (.objects #[revPreId]) (.control p1) .indefinite)
        (cause := some testCause)).createEffect
      (.layered (.objects #[revPreId]) (.control p2) .indefinite)
      (cause := some testCause)).phaseOut (gRealPre0.object! concedePreId) (cause := some testCause)).phaseOut
      (gRealPre0.object! revPreId) (cause := some testCause))
  let gAfterRealConcede := mustApply gRealPre1 p1 .concede
  let gAfterRealConcedeSkip := gAfterRealConcede.startNextTurnAndBegin

  let item3cOk :=
    gHistAfterP1Concede.activePlayer == p2 &&
    !(gHistAfterP1Concede.object! matStealId).status.phasedOut &&
    gPreSrcOut.controllerOf (gPreSrcOut.object! preId) == some p0 &&
    gPreSrcOut.controllerOfAt (gPreSrcOut.object! preId) 0 == some p1 &&
    gPreExpiredAndSkip.activePlayer == p2 &&
    !(gPreExpiredAndSkip.object! preId).status.phasedOut &&
    !gAfterRealConcede.activeEffects.any (fun (_, s) => s == .layered (.objects #[concedePreId]) (.control p1) .indefinite) &&
    gAfterRealConcede.controllerOf (gAfterRealConcede.object! concedePreId) == some p2 &&
    gAfterRealConcede.controllerOfAt (gAfterRealConcede.object! concedePreId) 0 == some p1 &&
    gAfterRealConcede.controllerOfAt (gAfterRealConcede.object! revPreId) 0 == some p2 &&
    gAfterRealConcedeSkip.activePlayer == p2 &&
    !(gAfterRealConcedeSkip.object! concedePreId).status.phasedOut

  mustHold42i3 "3a.continuousPhasingHelpers" item3aOk &&
  mustHold42i3 "3b.summoningSicknessHistorical" item3bOk &&
  mustHold42i3 "3c.phaseInHistoricalCtrl" item3cOk &&
  mustHold42i3 "3.replay"
    (replayOk42i3 #[gContToggled, gContBearIn, gExCr1, gInPlaceRemat,
      gStolenIn, gMidPhToggled, gAfterLeft, gCntToggled, gDfcBackAndForth, gHistAfterP1Concede])

end Phase42Item3EventAlignment

section Phase42Item4EventAlignment

private def mustHold42i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase42Item4EventAlignment failed: {label}"

private def replayOk42i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let g2 := afterDraw
  let canAct0 (g0 : Game) (oid : ObjectId) : Bool :=
    let o := g0.object! oid
    g0.canActivate p0 o (g0.activatedAbilitiesOf o)[0]!
  let stillPayable (g0 : Game) : Bool :=
    g0.sourceStillPayable g0.proposedSpell.get!

  -- 4a. Resolving stack-object `abId` (`g.resolvingAbility <|> g.resolvingSpell`) before `resolvingForObj` (`o.sourceId`)
  --     in `ResolutionChoices` `.mayPayPickThen`:
  --     Save `proposalCheckpoint`, record a same-checkpoint `.costPayment .tap p0 (some dorkObj.id)`, untap `dorkObj`,
  --     and resolve `.mayPayPickThen .tapUntappedCreature` under `resolvingAbility := some trigAb.id` (whose `o.sourceId == some dorkObj.id`!)
  --     and under `resolvingSpell := some spellObj.id`:
  let gAb0 := readyControlledForTurn (addPermanent g2 bear p0 p0) p0
  let dorkObj := (gAb0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let gSameCkptTap :=
    setTapped
      ((gAb0.change .saveProposalCheckpoint).becomeTapped dorkObj
        (cause := some (.costPayment .tap p0 (some dorkObj.id))))
      dorkObj.id false
  let (gWithTrigAb, trigAb) := gSameCkptTap.allocStackAbility (gSameCkptTap.object! dorkObj.id) p0
  let preAbTapEvIdx := gWithTrigAb.events.size
  let gFraAbPrompt :=
    gWithTrigAb.changes #[
      .pushContinuationFrame { resolvingAbility := some trigAb.id },
      .pending (.resolutionChoice p0 (.mayPayPickThen .tapUntappedCreature (Instruction.gainLifeFixed 2) (some dorkObj.id))) ]
  let gFraAbPaid := mustApply gFraAbPrompt p0 (.choosePermanents #[dorkObj.id])
  let abTappedForTrigId :=
    (gFraAbPaid.events.extract preAbTapEvIdx gFraAbPaid.events.size).any fun ev =>
      match ev with
      | .rules _ (.permanent (.tapped snap true)) (.costPayment .tap q (some fid)) _ =>
        snap.id == some dorkObj.id && q == p0 && fid == trigAb.id && fid != dorkObj.id
      | _ => false

  let gSpellBase := setTapped gSameCkptTap dorkObj.id false
  let gSpellIns := insertObject gSpellBase bear p0 .stack (some p0)
  let spellObj := (gSpellIns.objects.filter (·.zone == .stack)).back!
  let preSpTapEvIdx := gSpellIns.events.size
  let gFraSpPrompt :=
    gSpellIns.changes #[
      .pushContinuationFrame { resolvingSpell := some spellObj.id },
      .pending (.resolutionChoice p0 (.mayPayPickThen .tapUntappedCreature (Instruction.gainLifeFixed 2) (some dorkObj.id))) ]
  let gFraSpPaid := mustApply gFraSpPrompt p0 (.choosePermanents #[dorkObj.id])
  let spTappedForSpellId :=
    (gFraSpPaid.events.extract preSpTapEvIdx gFraSpPaid.events.size).any fun ev =>
      match ev with
      | .rules _ (.permanent (.tapped snap true)) (.costPayment .tap q (some fid)) _ =>
        snap.id == some dorkObj.id && q == p0 && fid == spellObj.id && fid != dorkObj.id
      | _ => false
  let item4aOk :=
    abTappedForTrigId && (gFraAbPaid.object! dorkObj.id).status.tapped && gFraAbPaid.pending == .none &&
    spTappedForSpellId && (gFraSpPaid.object! dorkObj.id).status.tapped && gFraSpPaid.pending == .none

  -- 4b. `removeStoryCounter`, `removeIndestructibleCounter`, and graveyard/hand cost-zone legality
  --     in `Activation.validateActivation` (`canActivate`) & `Choices.sourceStillPayable`:
  let storyCardDef : CardDef := {
    name := "P42i4 StorySaga"
    types := #[.enchantment]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .removeCounters (.exact 1) (some .story) .self]
      effect := Effect.gainLife 1
    }]
  }
  let indCardDef : CardDef := {
    creature "P42i4 ArwenLike" ManaCost.empty #["Elf", "Noble"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .removeCounters (.exact 1) (some .indestructible) .self]
      effect := Effect.gainLife 1
    }]
  }
  let gyExileCardDef : CardDef := {
    name := "P42i4 GyRelic"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .exile (.exact 1) .yourGraveyard .self]
      effect := Effect.gainLife 2
    }]
  }
  let handDiscCardDef : CardDef := {
    creature "P42i4 Channeler" ManaCost.empty #["Spirit"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .discard (.exact 1) .self]
      effect := Effect.gainLife 2
    }]
  }
  let handExileCardDef : CardDef := {
    creature "P42i4 HandExiler" ManaCost.empty #["Elemental"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .exile (.exact 1) .yourHand .self]
      effect := Effect.gainLife 2
    }]
  }

  let gCntAct0 := (addPermanent (addPermanent g2 storyCardDef p0 p0) indCardDef p0 p0).addMana p0 .colorless 2
  let storyObj := (gCntAct0.permanentsOf p0).find? (·.name == storyCardDef.name) |>.get!
  let indObj := (gCntAct0.permanentsOf p0).find? (·.name == indCardDef.name) |>.get!
  let zeroCountersRejected :=
    !canAct0 gCntAct0 storyObj.id &&
    (gCntAct0.activateAbility p0 storyObj.id 0).toOption.isNone &&
    !canAct0 gCntAct0 indObj.id &&
    (gCntAct0.activateAbility p0 indObj.id 0).toOption.isNone
  let gCntActWith :=
    (gCntAct0.recordPutCounters storyObj.id .story 1 (some p0) (cause := some testCause)).recordPutCounters
      indObj.id .indestructible 1 (some p0) (cause := some testCause)
  let withCountersAllowed :=
    canAct0 gCntActWith storyObj.id &&
    canAct0 gCntActWith indObj.id
  let gStoryProp := mustApply gCntActWith p0 (.activate storyObj.id 0)
  let gStoryLostCnt := gStoryProp.recordRemoveCounters storyObj.id .story 1 (some p0) (cause := some testCause)
  let gStoryActivated := mustApply gStoryProp p0 .pay
  let gIndProp := mustApply gCntActWith p0 (.activate indObj.id 0)
  let gIndLostCnt := gIndProp.recordRemoveCounters indObj.id .indestructible 1 (some p0) (cause := some testCause)
  let gIndActivated := mustApply gIndProp p0 .pay

  -- Zone-cost legality across `.battlefield`, `.graveyard`, and `.hand` + `Choices.sourceStillPayable`:
  let gZones0 :=
    (insertObject
      (insertObject
        (insertObject
          (addPermanent
            (addPermanent (addPermanent g2 gyExileCardDef p0 p0) handDiscCardDef p0 p0)
            handExileCardDef p0 p0)
          gyExileCardDef p0 (.graveyard p0))
        handDiscCardDef p0 (.hand p0))
      handExileCardDef p0 (.hand p0)).addMana p0 .colorless 3
  let bfGyObj := (gZones0.permanentsOf p0).find? (·.name == gyExileCardDef.name) |>.get!
  let bfDiscObj := (gZones0.permanentsOf p0).find? (·.name == handDiscCardDef.name) |>.get!
  let bfHexObj := (gZones0.permanentsOf p0).find? (·.name == handExileCardDef.name) |>.get!
  let gyId := (gZones0.player p0).graveyard.back!
  let handIds := (gZones0.player p0).hand
  let handDiscId := handIds.find? (fun oid => (gZones0.object! oid).name == handDiscCardDef.name) |>.get!
  let handExileId := handIds.find? (fun oid => (gZones0.object! oid).name == handExileCardDef.name) |>.get!

  let wrongZonesRejected :=
    !canAct0 gZones0 bfGyObj.id &&
    !canAct0 gZones0 bfDiscObj.id &&
    !canAct0 gZones0 bfHexObj.id &&
    (gZones0.activateAbility p0 bfGyObj.id 0).toOption.isNone &&
    (gZones0.activateAbility p0 bfDiscObj.id 0).toOption.isNone &&
    (gZones0.activateAbility p0 bfHexObj.id 0).toOption.isNone
  let rightZonesAllowed :=
    canAct0 gZones0 gyId &&
    canAct0 gZones0 handDiscId &&
    canAct0 gZones0 handExileId

  -- Propose `.activate` (pauses at `.pay` for `{1}`), check `sourceStillPayable` before & if moved out of zone, then pay `{1}`:
  let gGyProposed := mustApply gZones0 p0 (.activate gyId 0)
  let (gGyMovedAway, _) := gGyProposed.move gyId .exile none (cause := some testCause)
  let gGyPaid := mustApply gGyProposed p0 .pay
  let gHandDiscProposed := mustApply gZones0 p0 (.activate handDiscId 0)
  let (gHandDiscMovedAway, _) := gHandDiscProposed.move handDiscId .exile none (cause := some testCause)
  let gHandDiscPaid := mustApply gHandDiscProposed p0 .pay
  let gHandExileProposed := mustApply gZones0 p0 (.activate handExileId 0)
  let (gHandExileMovedAway, _) := gHandExileProposed.move handExileId (.graveyard p0) none (cause := some testCause)
  let gHandExilePaid := mustApply gHandExileProposed p0 .pay

  let item4bOk :=
    zeroCountersRejected && withCountersAllowed &&
    stillPayable gStoryProp && !stillPayable gStoryLostCnt &&
    (gStoryActivated.object! storyObj.id).status.story == 0 && gStoryActivated.stack.size == 1 &&
    stillPayable gIndProp && !stillPayable gIndLostCnt &&
    (gIndActivated.object! indObj.id).status.indestructibleCounters == 0 && gIndActivated.stack.size == 1 &&
    wrongZonesRejected && rightZonesAllowed &&
    stillPayable gGyProposed && !stillPayable gGyMovedAway &&
    (gGyPaid.followMovedToZone? gyId (· == .exile)).isSome && gGyPaid.stack.size == 1 &&
    stillPayable gHandDiscProposed && !stillPayable gHandDiscMovedAway &&
    (gHandDiscPaid.followMovedToZone? handDiscId (· == .graveyard p0)).isSome && gHandDiscPaid.stack.size == 1 &&
    stillPayable gHandExileProposed && !stillPayable gHandExileMovedAway &&
    (gHandExilePaid.followMovedToZone? handExileId (· == .exile)).isSome && gHandExilePaid.stack.size == 1

  mustHold42i4 "4a.mayPayPickStackAbId" item4aOk &&
  mustHold42i4 "4b.counterAndZoneCostLegality" item4bOk &&
  mustHold42i4 "4.replay"
    (replayOk42i4 #[gFraAbPaid, gFraSpPaid, gStoryActivated, gIndActivated,
      gGyProposed, gGyPaid, gHandDiscPaid, gHandExilePaid])

end Phase42Item4EventAlignment

section Phase43Item1EventAlignment

private def mustHold43i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase43Item1EventAlignment failed: {label}"

private def replayOk43i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with supertypes := #[.legendary] }
  let fragileLordDef : CardDef := creature "P43i1 FragileLord" ManaCost.empty #["Wizard"] 1 0
  let nonAttGrantorDef : CardDef := { name := "P43i1 RelicGrantor", types := #[.artifact] }
  let attGrantorDef : CardDef := { name := "P43i1 EqGrantor", types := #[.artifact], subtypes := #["Equipment"] }
  let shockBearDef : CardDef := { bear with staticAbilities := #[.entersTappedUnlessPayLife 2] }
  let p2LandDef : CardDef := { name := "P43i1 Forest", types := #[.land], activatedAbilities := #[ActivatedAbility.manaAbility (.fixed #[.colored .green])] }
  let painLandDef : CardDef := {
    name := "P43i1 PainLand"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.oneOf (.explicit #[.colored .red, .colored .green]) (.const 1)) (damageYou := 1)]
  }

  -- 1a. Dismissed-batch SBA flushing in `concede` (`finishConcedePriority` preserving non-active `savedPendingPrio`)
  --     and `queuedLinkedExile` re-pause rewriting (`newBid != origBid` in `rewriteRepausedPostCloseBatch`
  --     for both `deferRestore == false` and `deferRestore == true`), plus `checkSBACounted` non-pausing
  --     re-chaining / `contHasLeave` merging and `combineOuterContinuations` `O_0 >> rest >> O_caller` ordering:
  -- (i) `concede` on a stale paused batch (`.chooseLegend p2 ...` with non-active `pendingPriority := some p3`
  --     and `.checkSBA` in `pendingReplacement` after `.closeBatch`): `p2` conceding flushes the dismissed batch,
  --     peels `.checkSBA`, runs SBAs (killing 1/0 `fragileLordDef`), and grants priority to `p3` (NOT `p0`)!
  let gP2LegPaused :=
    (addPermanent (addPermanent g4 legBearDef p2 p2) legBearDef p2 p2).receivePriority p3
  let gWithZeroToughness := addPermanent gP2LegPaused fragileLordDef p0 p0
  let zeroToughId := (gWithZeroToughness.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!.id
  let gAfterP2Concede := mustApply gWithZeroToughness p2 .concede
  let concedeFlushOk :=
    gP2LegPaused.pendingPriority == some p3 &&
    gAfterP2Concede.currentBatch.isNone &&
    gAfterP2Concede.pending == .none &&
    (gAfterP2Concede.followMovedToZone? zeroToughId (· == .graveyard p0)).isSome &&
    gAfterP2Concede.priority == p3

  -- (ii) `queuedLinkedExile` `newBid != origBid` re-pause in `checkSBACountedWithLeavesCore`:
  --      Pause on a 2-copy legend batch `origQBid` for `p0`, queue an exiled creature `exBear` (`entersTappedUnlessPayLife := some 2`)
  --      in `queuedLinkedExile`, chain `.gainLife p1 5` after `.closeBatch`, set `p1` at 0 life, and exile one legend copy
  --      so `origQBid` flushes and `returnQueuedLinkedExile` re-pauses on `newBid != origQBid`:
  let gQBase0 :=
    insertObject
      (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
      shockBearDef p0 .exile
  let exBearId := (gQBase0.objects.filter (·.zone == .exile))[0]!.id
  let gQPaused0 := gQBase0.checkSBA
  let origQBid := gQPaused0.currentBatch.get!.1
  let qLegId0 := match gQPaused0.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999999⟩
  let gQQueued :=
    ((gQPaused0.change (.queueLinkedExile #[exBearId])).chainPendingReplacement
      (.gainLife p1 5 (some testCause))).setLifeTotal p1 0
  let (gQInv, _) := gQQueued.move qLegId0 .exile none (cause := some testCause)
  let (gQRepFalse, qDidFalse, qSavedFalse, _, qDepFalse, _) :=
    gQInv.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (departedIn := #[p2]) (deferRestore := false)
  let newQBid := gQRepFalse.currentBatch.get!.1
  let qRidFalse := match gQRepFalse.pending with | .chooseReplacement _ rids => rids[0]! | _ => { kind := .entersTappedDeclinePayLife }
  let gQRepFalseDone := mustApply gQRepFalse p0 (.chooseReplacement qRidFalse)
  let (gQRepTrue, _, _, qPoTrue, _, _) :=
    gQInv.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (departedIn := #[p2]) (deferRestore := true)
  let qRidTrue := match gQRepTrue.pending with | .chooseReplacement _ rids => rids[0]! | _ => { kind := .entersTappedDeclinePayLife }
  let gQRepTrueDone := mustApply gQRepTrue p0 (.chooseReplacement qRidTrue)
  let gQRepTrueDrained := gQRepTrueDone.drainPendingContinuations
  let queuedRepauseOk :=
    qDidFalse && qSavedFalse == some (.mayPayGeneric p0 1) && qDepFalse == #[p2] &&
    newQBid != origQBid &&
    (match gQRepFalse.pending with | .chooseReplacement q _ => q == p0 | _ => false) &&
    -- `deferRestore := false`: `.leavePlayersWhoLost` ran right after `newQBid` closed (ahead of `.gainLife p1 5`), so `p1` left and `.mayPayGeneric` restored:
    (gQRepFalseDone.player p1).leftTheGame &&
    gQRepFalseDone.pending == .mayPayGeneric p0 1 &&
    -- `deferRestore := true`: `.checkSBA` / `.leavePlayersWhoLost` was NOT chained on `newQBid`, and `.gainLife p1 5` was stashed on `outerPendingReplacements` (`qPoTrue == true`):
    qPoTrue &&
    !(gQRepTrueDone.player p1).leftTheGame &&
    !(gQRepTrueDrained.player p1).leftTheGame &&
    (gQRepTrueDrained.player p1).life == 5

  -- (iii) `checkSBACounted` non-pausing re-chaining (peeled `.leavePlayersWhoLost none false #[] none` with pre-existing
  --       `lost && !leftTheGame` player `p1`, and peeled `.checkSBA` when `changed == true`) + `chainOrMergeLeave` upgrade
  --       of post-`.closeBatch` `.checkSBA` + `combineOuterContinuations` (`O_0 >> rest >> O_caller` ordering):
  let gPreLost0 :=
    (g4.record (GameEvent.playerLost g4.turnNumber p1 .conceded (cause := some testCause))).changes #[
      .pending (.chooseLegend p0 "Stale" #[⟨999999⟩]),
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.leavePlayersWhoLost none false #[] none) (.gainLife p0 4 (some testCause)))) ]
  let (gPreLost1, _) := gPreLost0.checkSBACounted
  let gPreLostDone := gPreLost1.drainPendingContinuations

  let gPeelSba0 :=
    (addPermanent g4 fragileLordDef p0 p0).changes #[
      .pending (.chooseLegend p0 "Stale" #[⟨999999⟩]),
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq .checkSBA (.gainLife p0 6 (some testCause)))) ]
  let (gPeelSba1, peelSbaDid) := gPeelSba0.checkSBACounted
  -- `peelSbaDid == true` (`fragileLordDef` died), so `.checkSBA` was re-chained ahead of `.gainLife p0 6`:
  let gPeelSbaDone := gPeelSba1.drainPendingContinuations

  -- `combineOuterContinuations` ordering (`O_0 >> rest >> O_caller` when `po0 == true` and `popOuterCaller == true`):
  let gOrder0 :=
    g4.changes #[
      .pending (.chooseLegend p0 "Stale" #[⟨999999⟩]),
      .pushContinuationFrame {},
      -- Outer stack bottom-to-top: push inner `O_0` (`+2`) first, then outer `O_caller` (`+5`) on top so `back?` pops `O_caller` then `O_0`!
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)),
      .pushOuterPendingReplacement (.gainLife p0 5 (some testCause)),
      .pendingReplacement (some (.seq (.leavePlayersWhoLost none true #[] none) (.gainLife p0 3 (some testCause)))) ]
  let preOrdEvIdx := gOrder0.events.size
  let (gOrderDone, _, _, _, _, _) :=
    gOrder0.checkSBACountedWithLeavesCore (popOuterIn := true) (deferRestore := false)
  let ordGains :=
    (gOrderDone.events.extract preOrdEvIdx gOrderDone.events.size).filterMap fun ev =>
      match ev.change with
      | .rules (.life (.gained q amt)) => if q == p0 then some amt else none
      | _ => none
  let rechainingAndOrderOk :=
    (gPreLostDone.player p1).leftTheGame &&
    (gPreLostDone.player p0).life == (g4.player p0).life + 4 &&
    peelSbaDid &&
    (match gPeelSba1.pendingReplacement with | some (.seq .checkSBA _) => true | _ => false) &&
    (gPeelSbaDone.player p0).life == (g4.player p0).life + 6 &&
    ordGains == #[2, 3, 5]
  let item1aOk := concedeFlushOk && queuedRepauseOk && rechainingAndOrderOk

  -- 1b. `Leaving.preBatchLegendSnapshotValid` & `normalizePendingLegendChoice`:
  --     (i) 2-group snapshot-backed SBA sweep (`fragileLordDef` dies granting `.legendary` to both 2 bears and 2 heroes):
  --         answering `keepLegend` for Group 1 puts Group 1's other copy into the graveyard after `startIdx`, which MUST NOT
  --         invalidate Group 2's snapshot-backed `.chooseLegend` prompt!
  let gSnap2Grp0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0) hero p0 p0)
        hero p0 p0)
      fragileLordDef p0 p0
  let s2Bears := ((gSnap2Grp0.permanentsOf p0).filter (·.name == bear.name)).map (·.id)
  let s2Heroes := ((gSnap2Grp0.permanentsOf p0).filter (·.name == hero.name)).map (·.id)
  let s2Lord := (gSnap2Grp0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
  let gSnap2GrpPaused1 :=
    (gSnap2Grp0.createEffect
      (.layered (.objects (s2Bears ++ s2Heroes)) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield s2Lord.id))
      (cause := some testCause)).checkSBA
  let (grp1Name, grp1Ids) :=
    match gSnap2GrpPaused1.pending with | .chooseLegend _ nm ids => (nm, ids) | _ => ("", #[])
  let expectedGrp2Name := if grp1Name == bear.name then hero.name else bear.name
  let gSnap2GrpPaused2 := mustApply gSnap2GrpPaused1 p0 (.keepLegend grp1Ids[0]!)
  let grp2KeepId := match gSnap2GrpPaused2.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999999⟩
  let gSnap2GrpDone := mustApply gSnap2GrpPaused2 p0 (.keepLegend grp2KeepId)

  --     (ii) 3-copy narrowing (`#[b1, b2, b3]` -> `#[b2, b3]`): both snapshot-backed on `p2` departure AND printed-legendary
  --          via `normalizePendingLegendChoice`:
  let gThreeSnap0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent g4 bear p2 p0) bear p0 p0) bear p0 p0)
      fragileLordDef p0 p0
  let tsIds := ((gThreeSnap0.permanentsOf p0).filter (·.name == bear.name)).map (·.id)
  let tsLord := (gThreeSnap0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
  let gThreeSnapPaused :=
    (gThreeSnap0.createEffect
      (.layered (.objects tsIds) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield tsLord.id))
      (cause := some testCause)).checkSBA
  let gThreeSnapAfterDep := mustApply gThreeSnapPaused p2 .concede
  let gThreeSnapKept := mustApply gThreeSnapAfterDep p0 (.keepLegend tsIds[1]!)

  let gThreePrinted0 :=
    (addPermanent (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0) legBearDef p0 p0).checkSBA
  let tpIds := match gThreePrinted0.pending with | .chooseLegend _ _ ids => ids | _ => #[]
  let (gThreePrintedMoved, _) := gThreePrinted0.move tpIds[0]! .exile none (cause := some testCause)
  let (gThreePrintedNorm, narrowedPrinted, clearedPrinted) := gThreePrintedMoved.normalizePendingLegendChoice

  --     (iii) Cumulative `curPreG` departure updates (non-attachment legend source + `.unattached` + `.expired`
  --           in `preBatchLegendSnapshotValid`) AND controller-scoped `.legendRuleOff` (`p2`'s `.legendRuleOff`
  --           expiring on `p2`'s departure does NOT invalidate `p0`'s legend prompt!):
  let gCum0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0) fragileLordDef p0 p0)
        nonAttGrantorDef p0 p0)
      attGrantorDef p0 p0
  let cBears := ((gCum0.permanentsOf p0).filter (·.name == bear.name)).map (·.id)
  let cLord := (gCum0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
  let cNonAtt := (gCum0.permanentsOf p0).find? (·.name == nonAttGrantorDef.name) |>.get!
  let cAtt := (gCum0.permanentsOf p0).find? (·.name == attGrantorDef.name) |>.get!
  let gCum1 :=
    ((((gCum0.record (GameEvent.attached gCum0.turnNumber (gCum0.snapshot cAtt) cBears[0]! (cause := testCause))).createEffect
      -- Fragile lord grants `.legendary` to `cBears[0]`, `cNonAtt` grants `.legendary` to `cBears[1]`, and `p2` has `.legendRuleOff`:
      (.layered (.objects #[cBears[0]!]) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield cLord.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[cBears[1]!]) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield cNonAtt.id))
      (cause := some testCause)).createEffect
      (.playerRule p2 .legendRuleOff .untilEndOfTurn)
      (cause := some testCause)).checkSBA
  -- First, `p2` concedes: `p2`'s `.legendRuleOff` expires, which MUST NOT invalidate `p0`'s `.chooseLegend` prompt!
  let gCumAfterP2 := mustApply gCum1 p2 .concede
  -- Next, unattach `cAtt` (harmless) AND exile `cNonAtt` (which granted `.legendary` to `cBears[1]`!) -> now invalidates `p0`'s prompt!
  let (gCumAfterNonAttLeft, _) := gCumAfterP2.move cNonAtt.id .exile none (cause := some testCause)
  let (gCumFlushed, _, _) := gCumAfterNonAttLeft.checkSBACountedWithLeaves

  let item1bOk :=
    (match gSnap2GrpPaused2.pending with | .chooseLegend q nm ids => q == p0 && nm == expectedGrp2Name && ids.size == 2 | _ => false) &&
    gSnap2GrpDone.pending == .none && gSnap2GrpDone.currentBatch.isNone &&
    (gSnap2GrpDone.permanentsOf p0).size == 2 &&
    tsIds.size == 3 &&
    gThreeSnapAfterDep.pending == .chooseLegend p0 bear.name #[tsIds[1]!, tsIds[2]!] &&
    gThreeSnapKept.pending == .none && gThreeSnapKept.currentBatch.isNone &&
    (gThreeSnapKept.permanentsOf p0).map (·.id) == #[tsIds[1]!] &&
    narrowedPrinted && !clearedPrinted &&
    gThreePrintedNorm.pending == .chooseLegend p0 bear.name #[tpIds[1]!, tpIds[2]!] &&
    gCumAfterP2.pending == .chooseLegend p0 bear.name cBears &&
    gCumFlushed.pending == .none && gCumFlushed.currentBatch.isNone

  -- 1c. `.finishResolutionChoice` `pendingPriority` stamping (`Decisions.finishAndGrantPriority` & `ManaAbilities`),
  --     unpaused non-carrier `ContinuationFrame` draining in `ManaAbilities`, and `prevPending == .none`
  --     outer-continuation stashing + checkpoint-before-clear ordering in `activateManaAbility`:
  -- (i) `finishAndGrantPriority p2` when `outerPendingReplacements` has `.gainLife p0 2` (does NOT grant priority):
  --     `pendingPriority` is stamped to `some p2` before chaining `.finishResolutionChoice`, so `p2` (NOT `activePlayer == p0`) receives priority!
  let gFgp0 :=
    (g4.change (.priority p2)).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)) ]
  let gFgpDone := gFgp0.finishAndGrantPriority p2
  -- (ii) Unpaused mana ability inside a non-carrier `ContinuationFrame` (`resolvingAbility := some ab.id`) with
  --      `outerPendingReplacements := #[.gainLife p1 5]` on non-active `p2` (`p1` at 0 life): drains `outerPendingReplacements`
  --      synchronously and grants priority to `p2`!
  let gManaBase := ((addPermanent (addPermanent g4 p2LandDef p2 p2) painLandDef p2 p2).change (.priority p2)).setLifeTotal p1 0
  let p2Forest := (gManaBase.permanentsOf p2).find? (·.name == p2LandDef.name) |>.get!
  let (gNonCarrier0, dummyAb) := gManaBase.allocStackAbility p2Forest p2
  let gNonCarrier1 :=
    gNonCarrier0.changes #[
      .pushContinuationFrame { resolvingAbility := some dummyAb.id },
      .pushOuterPendingReplacement (.gainLife p1 5 (some testCause)) ]
  let gNonCarrierDone : Game :=
    match gNonCarrier1.activateManaAbility p2 p2Forest.id 0 #[.colored .green] with
    | .ok g => g
    | .error e => panic! e
  -- (iii) `activateManaAbility` with `prevPending == .none` and pre-existing `pendingReplacement := some (.gainLife p1 5)`:
  --       stashes `pendingReplacement` onto `outerPendingReplacements` AFTER `saveProposalCheckpoint` (so checkpoint holds original
  --       `pendingReplacement`), drains `.gainLife p1 5` before `receivePriority p2`, and leaves `pendingReplacement == none`!
  let gStash0 :=
    gManaBase.chainPendingReplacement (.gainLife p1 5 (some testCause))
  let gStashDone : Game :=
    match gStash0.activateManaAbility p2 p2Forest.id 0 #[.colored .green] with
    | .ok g => g
    | .error e => panic! e

  let item1cOk :=
    (gFgpDone.player p0).life == (g4.player p0).life + 2 &&
    gFgpDone.priority == p2 &&
    !(gNonCarrierDone.player p1).lost && (gNonCarrierDone.player p1).life == 5 && gNonCarrierDone.priority == p2 &&
    !(gStashDone.player p1).lost && (gStashDone.player p1).life == 5 &&
    gStashDone.pendingReplacement.isNone && gStashDone.priority == p2

  mustHold43i1 "1a.concedeFlushRepauseAndOrder" item1aOk &&
  mustHold43i1 "1b.legendSnapshotMultiAndNarrow" item1bOk &&
  mustHold43i1 "1c.finishFraPrioAndManaDrain" item1cOk &&
  mustHold43i1 "1.replay"
    (replayOk43i1 #[gAfterP2Concede, gQRepFalse, gQRepFalseDone, gQRepTrueDone, gQRepTrueDrained,
      gPreLostDone, gPeelSbaDone, gOrderDone,
      gSnap2GrpPaused2, gSnap2GrpDone, gThreeSnapAfterDep, gThreeSnapKept, gThreePrintedNorm,
      gCumAfterP2, gCumFlushed, gFgpDone, gNonCarrierDone, gStashDone])

end Phase43Item1EventAlignment

section Phase43Item2EventAlignment

private def mustHold43i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase43Item2EventAlignment failed: {label}"

private def replayOk43i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let auraDef : CardDef := { name := "P43i2 Aura", types := #[.enchantment], subtypes := #["Aura"] }
  let eqDef : CardDef := { name := "P43i2 Sword", types := #[.artifact], subtypes := #["Equipment"] }
  let embDef : CardDef := { name := "P43i2 TempEmblem", types := #[] }
  let ltbWatcherDef : CardDef := {
    creature "P43i2 LTBWatcher" ManaCost.empty #["Cleric"] 2 2 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger (.permanentLeaves (.all #[.hasType .creature, .controlledBy .you]))
        { body := Instruction.gainLifeFixed 3 }
    ]
  }

  -- 2a. Unbatched CR 800.4c `lkiController?` (`before.controller == some p0` LKI + CR 603.10a trigger
  --     + multi-permanent single-batch wrapping + `replaceZoneMove` living `lkiController?` CR 616.1 chooser)
  --     + active-only CR 800.4c vs CR 800.4a classification + co-exiled/co-departing `skipUnattachIds`
  --     + `Attachments.unattachFrom` `preState?` + `restoreCopiesUntilSourceLeaves` `suppressLog`:
  -- (i) `p1` owns `stBear`, `stHero`, and `stEq` (`defaultController := p2`, `stEq` attached to `stBear`, counters on creatures),
  --     all stolen by `p0` under `.untilEndOfTurn`; `p2` concedes (staying on battlefield under `p0`), then `clearEOT` ends all 3 `.control p0` effects:
  --     - all 3 exile in ONE batch (`ev.batch` shared),
  --     - `ZoneEvent.moved.before.controller == some p0` (firing `p0`'s `.creatureYouControlLeaves` trigger twice!),
  --     - `stEq` does NOT emit `.unattached` before co-exiling with `stBear`!
  let g8004c0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 ltbWatcherDef p0 p0) bear p1 p2)
        hero p1 p2)
      eqDef p1 p2
  let stBear := (g8004c0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let stHero := (g8004c0.permanentsOf p2).find? (·.name == hero.name) |>.get!
  let stEq := (g8004c0.permanentsOf p2).find? (·.name == eqDef.name) |>.get!
  let g8004c1 :=
    ((((((g8004c0.recordPutCounters stBear.id .plusOnePlusOne 1 (some p0) (cause := some testCause)).recordPutCounters
      stHero.id .plusOnePlusOne 1 (some p0) (cause := some testCause)).record
      (GameEvent.attached g8004c0.turnNumber (g8004c0.snapshot stEq) stBear.id (cause := testCause))).createEffect
      (.layered (.objects #[stBear.id]) (.control p0) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[stHero.id]) (.control p0) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[stEq.id]) (.control p0) .untilEndOfTurn) (cause := some testCause))
  let g8004cAfterLeave := mustApply g8004c1 p2 .concede
  let preEotEvIdx := g8004cAfterLeave.events.size
  let g8004cEot := g8004cAfterLeave.clearEOT
  let eotSlice := g8004cEot.events.extract preEotEvIdx g8004cEot.events.size
  let movedExiles :=
    eotSlice.filterMap fun ev =>
      match ev.change with
      | .rules (.zone (.moved before _ .battlefield .exile ..)) => some (before.id, before.controller, ev.batch)
      | _ => none
  let eotUnattached :=
    eotSlice.filter fun ev =>
      match ev.change with | .rules (.permanent (.unattached ..)) => true | _ => false

  -- `replaceZoneMove` living `lkiController?` CR 616.1 chooser when `g.controllerOf old == none` (`defaultController := p2` already departed):
  let rLeyA := (addPermanent (addPermanent g8004cAfterLeave auraDef p1 p1) eqDef p1 p1)
  let rIdA := (rLeyA.permanentsOf p1).find? (·.name == auraDef.name) |>.get!.id
  let rIdB := (rLeyA.permanentsOf p1).find? (·.name == eqDef.name) |>.get!.id
  let zRidA : ReplacementId := { kind := .exileOppDeath, object := some rIdA }
  let zRidB : ReplacementId := { kind := .exileOppDeath, object := some rIdB }
  let gLkiChoose0 :=
    ((rLeyA.expireMatching (fun
      | .layered (.objects ids) (.control _) _ => ids.contains stBear.id
      | _ => false) (cause := some testCause) (reconcileControl := false)).createEffect
      (.replacement { id := zRidA, source := some rIdA, controller := some p1, affectedPlayer := p0, kind := .exileInsteadOfGraveyard (some stBear.id) false }) (cause := some testCause)).createEffect
      (.replacement { id := zRidB, source := some rIdB, controller := some p1, affectedPlayer := p0, kind := .exileInsteadOfGraveyard (some stBear.id) false }) (cause := some testCause)
  let (gLkiChoosePaused, _) :=
    gLkiChoose0.move stBear.id (.graveyard p1) none (cause := some testCause) (lkiController? := some p0)

  -- (ii) Active-only CR 800.4c vs CR 800.4a classification:
  --      `cPrior` (`owner := p0, defaultController := p2`) had a `.control p1` effect that ALREADY expired on an earlier turn;
  --      when `p2` concedes now, `cPrior` has NO active control-changing effect and must log `(CR 800.4a)` (NOT `(CR 800.4c)`)!
  --      Also attach `coDepEq` (`owner := p0, defaultController := p2`) to `p2Host` (`owner := p2`): both depart in `playerLeavesGameCore`,
  --      so `coDepEq` is in `coDepartingIds` and emits NO `.unattached`!
  --      And attach `survivingEq` (`owner := p0, defaultController := p0`, pumped by `p2Host`'s `.whileSourceOnBattlefield`) to `p2Host`
  --      and copy `cPrior` via `.whileSourceOnBattlefield p2Host.id`: `survivingEq`'s `.unattached` snapshot preserves pre-leave state,
  --      and `cPrior` (co-exiled when `p2` leaves) does NOT emit a stale `"is no longer a copy"` log!
  let gPrior0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 bear p0 p2) eqDef p0 p2)
        bear p2 p2)
      eqDef p0 p0
  let cPrior := ((gPrior0.permanentsOf p2).filter (·.name == bear.name)).find? (·.owner == p0) |>.get!
  let coDepEq := ((gPrior0.permanentsOf p2).filter (·.name == eqDef.name))[0]!
  let p2Host := ((gPrior0.permanentsOf p2).filter (·.name == bear.name)).find? (·.owner == p2) |>.get!
  let survivingEq := (gPrior0.permanentsOf p0).find? (·.name == eqDef.name) |>.get!
  let gPrior1 :=
    ((((((gPrior0.createEffect (.layered (.objects #[cPrior.id]) (.control p1) .untilEndOfTurn)
        (cause := some testCause)).clearEOT).record
        (GameEvent.attached gPrior0.turnNumber (gPrior0.snapshot coDepEq) p2Host.id (cause := testCause))).record
        (GameEvent.attached gPrior0.turnNumber (gPrior0.snapshot survivingEq) p2Host.id (cause := testCause))).createEffect
        (.layered (.objects #[survivingEq.id]) (.copy hero) (.whileSourceOnBattlefield p2Host.id))
        (cause := some testCause)).createEffect
        (.layered (.objects #[cPrior.id]) (.copy hero) (.whileSourceOnBattlefield p2Host.id))
        (cause := some testCause))
  let prePriorEvIdx := gPrior1.events.size
  let prePriorLogIdx := gPrior1.log.size
  let gPriorAfter := mustApply gPrior1 p2 .concede
  let priorSlice := gPriorAfter.events.extract prePriorEvIdx gPriorAfter.events.size
  let priorLogs := gPriorAfter.log.extract prePriorLogIdx gPriorAfter.log.size
  let priorUnatt :=
    priorSlice.filterMap fun ev =>
      match ev.change with
      | .rules (.permanent (.unattached eo _)) => some (eo.id, eo.name)
      | _ => none

  let item2aOk :=
    movedExiles.size == 3 &&
    movedExiles.all (fun (_, ctrl, b) => ctrl == some p0 && b.isSome && b == movedExiles[0]!.2.2) &&
    eotUnattached.isEmpty &&
    g8004cEot.waitingTriggers.size == 2 &&
    gLkiChoose0.controllerOf (gLkiChoose0.object! stBear.id) == none &&
    (match gLkiChoosePaused.pending with | .chooseReplacement q rids => q == p0 && rids.size == 2 | _ => false) &&
    priorLogs.any (fun s => s.contains "(CR 800.4a)") &&
    !priorLogs.any (fun s => s.contains "(CR 800.4c)") &&
    !priorLogs.any (fun s => s.contains s!"{bear.name} is no longer a copy") &&
    priorLogs.any (fun s => s.contains s!"{eqDef.name} is no longer a copy") &&
    priorUnatt == #[(some survivingEq.id, hero.name)]

  -- 2b. Multi-effect & orphaned `.commandEmblem` expiry in `Turns.expireUntilTurnCommandEffects` + cease-first
  --     `"<embName> ends"` logging across `expireEffectsByDuration` / `clearEOT` / `expireUntilNextTurnEffects`,
  --     and `(reconcileControl := false)` in `expireUntilNextTurnEffects`:
  -- (i) Multi-effect `embShared` referenced by an earlier `.untilNextTurnOf p0` AND a later `.untilNextTurnOf p1`
  --     (which previously shadowed `p0`), plus orphaned `orphanEmbId` (object already absent before expiry):
  --     expiring `p0`'s turn matches the earlier `.untilNextTurnOf p0`, ceases `embShared` BEFORE `effectExpired`,
  --     logs `"<embName> ends"`, and cleans up `orphanEmbId`'s orphaned `.commandEmblem` effect!
  let gMultiEmb0 := insertObject g4 embDef p0 .command (some p0)
  let embShared := (gMultiEmb0.objects.filter (·.zone == .command))[0]!
  let orphanEmbId : ObjectId := ⟨999888⟩
  let gMultiEmb1 :=
    (((gMultiEmb0.createEffect (.gameRule (.commandEmblem embShared.id) (.untilNextTurnOf p0))
      (cause := some testCause)).createEffect
      (.gameRule (.commandEmblem embShared.id) (.untilNextTurnOf p1))
      (cause := some testCause)).createEffect
      (.gameRule (.commandEmblem orphanEmbId) (.untilNextTurnOf p0))
      (cause := some testCause))
  let preEmbP0Idx := gMultiEmb1.events.size
  let gMultiEmbAfterP0 := gMultiEmb1.expireUntilTurnCommandEffects p0
  let embP0Slice := gMultiEmbAfterP0.events.extract preEmbP0Idx gMultiEmbAfterP0.events.size
  let ceasePos? := embP0Slice.findIdx? (fun ev =>
    match ev.change with | .rules (.zone (.ceasedToExist eo)) => eo.id == some embShared.id | _ => false)
  let expPos? := embP0Slice.findIdx? (fun ev =>
    match ev.change with | .rules (.continuousEffect (.expired ..)) => true | _ => false)

  -- (ii) `.commandEmblem` with `.untilEndOfTurn` in `clearEOT` also ceases the command-zone emblem and logs `"<embName> ends"`:
  let gEotEmb0 := insertObject g4 embDef p0 .command (some p0)
  let embEot := (gEotEmb0.objects.filter (·.zone == .command))[0]!
  let gEotEmb1 :=
    (gEotEmb0.createEffect (.gameRule (.commandEmblem embEot.id) .untilEndOfTurn) (cause := some testCause)).clearEOT

  let item2bOk :=
    (gMultiEmbAfterP0.findObject? embShared.id).isNone &&
    gMultiEmbAfterP0.activeEffects.isEmpty &&
    gMultiEmbAfterP0.log.any (· == s!"{embDef.name} ends") &&
    (match ceasePos?, expPos? with | some cIdx, some eIdx => cIdx < eIdx | _, _ => false) &&
    (gEotEmb1.findObject? embEot.id).isNone &&
    gEotEmb1.log.any (· == s!"{embDef.name} ends")

  -- 2c. 2HG multi-round extra-turn `inProgress` splice (`#[⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨1⟩]` with `⟨0⟩` departed:
  --     on Extra Turn 1 at `⟨1⟩`, adding Team B extra turn splices `#[⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩]`),
  --     decoupled `.untilEndOfNextTurnOf ⟨1⟩` vs `.untilNextTurnOf ⟨1⟩` when `⟨0⟩` departed and `⟨1⟩` lives,
  --     and departed 2HG CR 800.4i `.untilEndOfTurn` `.playFromExile` expiry:
  let cfg2hg : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "C0", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "C1", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed := 432
    startingPlayer := some 0
  }
  let gT0 : Game :=
    match Start.start cfg2hg with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  -- Move to Team B (`⟨2⟩`), add TWO extra turns for Team A (`#[⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨1⟩]`), eliminate `⟨0⟩` ONLY (`playerLost` + `playerLeftGame` on `⟨0⟩` in 2HG? No, in 2HG teammates lose together on `concede`, so test individual departed seat via `playerLost`/`playerLeftGame` OR test 2 rounds with both alive `#[⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨1⟩]` while on `⟨0⟩`!):
  -- Even better: with BOTH `⟨0⟩` and `⟨1⟩` alive on Extra Turn 1 (`activePlayer == ⟨0⟩`, `seats == #[⟨0⟩]`, `extraTurns == #[⟨1⟩, ⟨0⟩, ⟨1⟩]`),
  -- adding an extra turn for Team B (`⟨2⟩`) MUST splice after `inProgress == 1` (`#[⟨1⟩]`), producing `#[⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩]`
  -- (NOT consuming round 2's `#[⟨0⟩, ⟨1⟩]` into `inProgress == 3` `#[⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]`)!
  let gTwoRounds0 :=
    (((gT0.startNextTurnAndBegin).record
      (GameEvent.extraTurnAdded gT0.turnNumber ⟨0⟩ (cause := testCause))).record
      (GameEvent.extraTurnAdded gT0.turnNumber ⟨0⟩ (cause := testCause))).startNextTurnAndBegin
  -- Now on Extra Turn 1 of Team A: `activePlayer == ⟨0⟩`, `extraTurns == #[⟨1⟩, ⟨0⟩, ⟨1⟩]`:
  let gSplicedTeamB :=
    gTwoRounds0.record (GameEvent.extraTurnAdded gTwoRounds0.turnNumber ⟨2⟩ (cause := testCause))
  -- Advance across `⟨1⟩` (finishes Team A Extra Turn 1) -> next turn MUST be Team B (`⟨2⟩`), NOT Team A's Round 2 `⟨0⟩`!
  let gAfterA1 := (gSplicedTeamB.startNextTurnAndBegin).startNextTurnAndBegin

  -- Departed 2HG CR 800.4i `.untilEndOfTurn` `.playFromExile`: Team A concedes on `⟨2⟩`'s turn; when Team A's next turn
  -- would have begun (after Team C finishes), `expireUntilNextTurnEffects` expires `.playFromExile` `.untilEndOfTurn` for `⟨0⟩` and `⟨1⟩`!
  let gExPerm0 := insertObject (gT0.startNextTurnAndBegin) bear ⟨0⟩ .exile -- now on `⟨2⟩`
  let exCard0 := (gExPerm0.objects.filter (·.zone == .exile))[0]!.id
  let gExPerm1 :=
    (mustApply
      (gExPerm0.createEffect
        (.permission (some ⟨1⟩) (.playFromExile exCard0 { player := ⟨1⟩ }) .untilEndOfTurn)
        (cause := some testCause))
      ⟨0⟩ .concede)
  -- Advance `⟨2⟩ -> ⟨3⟩ -> ⟨4⟩ -> ⟨5⟩ -> ⟨2⟩` (skipping departed Team A `⟨0⟩, ⟨1⟩`):
  let gExPermAfterSkip :=
    (((gExPerm1.startNextTurnAndBegin).startNextTurnAndBegin).startNextTurnAndBegin).startNextTurnAndBegin

  let item2cOk :=
    gTwoRounds0.activePlayer == ⟨0⟩ &&
    gTwoRounds0.extraTurns == #[⟨1⟩, ⟨0⟩, ⟨1⟩] &&
    gSplicedTeamB.extraTurns == #[⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩] &&
    gAfterA1.activePlayer == ⟨2⟩ &&
    !gExPermAfterSkip.activeEffects.any (fun (_, e) =>
      match e with | .permission _ (.playFromExile ..) _ => true | _ => false)

  mustHold43i2 "2a.lkiCtrl8004cAndUnattach" item2aOk &&
  mustHold43i2 "2b.multiEmblemAndEndsLog" item2bOk &&
  mustHold43i2 "2c.twoHgExtraSpliceAndPlayPerm" item2cOk &&
  mustHold43i2 "2.replay"
    (replayOk43i2 #[g8004cAfterLeave, g8004cEot, gLkiChoosePaused, gPriorAfter,
      gMultiEmbAfterP0, gEotEmb1,
      gSplicedTeamB, gAfterA1, gExPermAfterSkip])

end Phase43Item2EventAlignment

section Phase43Item3EventAlignment

private def mustHold43i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase43Item3EventAlignment failed: {label}"

private def replayOk43i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let noTrampleScope : ObjectScope := .creaturesWithout #[Keyword.trample]
  let constructScope : ObjectScope := .permanentsOfSubtype p0 .construct
  let constructDef : CardDef := creature "P43i3 Construct" ManaCost.empty #["Construct"] 2 2

  -- 3a. Historical-slice `Core.controlChanged`:
  --     (i) Pre-`events[0]` (`quiet`) filter `.control p1` (`noTrampleScope`) on `p0`'s `bear` that expires at `events[0]` (`clearEOT`):
  --         `g.controllerOf` is `some p0` now, yet `controlChanged` is `true` (while a `hero` with printed `trample := true` has `controlChanged == false`!)
  let trampleHeroDef : CardDef := { hero with keywords := #[Keyword.trample] }
  let gCtrlPre0 :=
    quiet
      ((addPermanent (addPermanent g4 bear p0 p0) trampleHeroDef p0 p0).createEffect
        (.layered noTrampleScope (.control p1) .untilEndOfTurn) (cause := some testCause))
  let preBearId := (gCtrlPre0.permanentsOf p1).find? (·.name == bear.name) |>.get!.id
  let preTrampleId := (gCtrlPre0.permanentsOf p0).find? (·.name == trampleHeroDef.name) |>.get!.id
  let gCtrlPreExpired := gCtrlPre0.clearEOT

  --     (ii) Pre-`events[0]` (`quiet`) `noTrampleScope` `.control p1` STILL in `activeEffects`, then `bear` copies `trampleHeroDef`
  --          in Layer 1 so current controller is `p0` again -> `controlChanged` is STILL `true`!
  let gCtrlStill0 :=
    quiet
      ((addPermanent g4 bear p0 p0).createEffect
        (.layered noTrampleScope (.control p1) .indefinite) (cause := some testCause))
  let stillBearId := (gCtrlStill0.permanentsOf p1)[0]!.id
  let gCtrlGainedTrample :=
    gCtrlStill0.createEffect
      (.layered (.objects #[stillBearId]) (.copy trampleHeroDef) .indefinite)
      (cause := some testCause)

  --     (iii) Creature enters in `g.events` under a pre-`events[0]` `.whileSourceOnBattlefield src.id` filter `.control p1`,
  --           and `src` later leaves the battlefield -> `controlChanged` is `true`!
  let gCtrlArr0 := addPermanent g4 constructDef p1 p1
  let ctrlSrcId := (gCtrlArr0.permanentsOf p1)[0]!.id
  let gCtrlArr1 :=
    quiet
      (gCtrlArr0.createEffect
        (.layered constructScope (.control p1) (.whileSourceOnBattlefield ctrlSrcId))
        (cause := some testCause))
  let gCtrlArr2 := addPermanent gCtrlArr1 constructDef p0 p0
  let arrivedConstructId :=
    ((gCtrlArr2.permanentsOf p1).filter (fun o => o.id != ctrlSrcId))[0]!.id
  let (gCtrlArrSrcGone, _) := gCtrlArr2.move ctrlSrcId (.graveyard p1) none (cause := some testCause)

  let item3aOk :=
    gCtrlPreExpired.controllerOf (gCtrlPreExpired.object! preBearId) == some p0 &&
    gCtrlPreExpired.controlChanged (gCtrlPreExpired.object! preBearId) &&
    !gCtrlPreExpired.controlChanged (gCtrlPreExpired.object! preTrampleId) &&
    gCtrlGainedTrample.controllerOf (gCtrlGainedTrample.object! stillBearId) == some p0 &&
    gCtrlGainedTrample.controlChanged (gCtrlGainedTrample.object! stillBearId) &&
    gCtrlArrSrcGone.controllerOf (gCtrlArrSrcGone.object! arrivedConstructId) == some p0 &&
    gCtrlArrSrcGone.controlChanged (gCtrlArrSrcGone.object! arrivedConstructId)

  -- 3b. Dead `before.id` cleanup (`after.id != some bid` leaves no ghost `missingObjs` entry in `toZ`)
  --     and pre-existence state (`controllerOfAt obj 0 == none` and `objectZoneAndPhasedOutAt? obj.id 0 == none`
  --     before `.created`, initial `.materializeObject`, or newly-allocated `.moved`, while same-ID `.moved` preserves pre-move state):
  -- (i) Token created after `events[0]`, initial `.materializeObject` after `events[0]`, and card moved `.hand -> .battlefield` after `events[0]`:
  let (gTokAfter0, tokObj) := g4.createOneToken p0 bear (cause := some testCause)
  let tokId := tokObj.id
  let gHand0 := insertObject (quiet g4) bear p0 (.hand p0)
  let handCardId := (gHand0.player p0).hand.back!
  let (gMovedAfter0, bfNewId) := gHand0.move handCardId .battlefield (some p0) (cause := some testCause)
  -- Dead `before.id` check: `src` on battlefield has `.whileInZone deadBid (.graveyard p0)` `.control p1`;
  -- moving `deadBid` from `.battlefield` to `.graveyard p0` allocates `newGyId != deadBid`, so `deadBid` is `.outside` (NOT in `.graveyard p0`!):
  let gDeadBid0 := quiet (addPermanent (addPermanent g4 bear p0 p0) hero p0 p0)
  let deadBid := (gDeadBid0.permanentsOf p0).find? (·.name == hero.name) |>.get!.id
  let watchBearId := (gDeadBid0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let (gDeadBid1, newGyId) := gDeadBid0.move deadBid (.graveyard p0) none (cause := some testCause)
  let gDeadBid2 :=
    gDeadBid1.createEffect
      (.layered (.objects #[watchBearId]) (.control p1) (.whileInZone deadBid (.graveyard p0)))
      (cause := some testCause)
  let postDeadIdx := gDeadBid2.events.size
  let gDeadBid3 := gDeadBid2.gainLife p0 1 (cause := some testCause)

  -- (ii) `isInitialMaterialize`:
  --      - Pre-existing object `preExistBear` referenced by `.designation` at `events[0]` BEFORE an in-place `.materializeObject`
  --        is NOT treated as initial (`objectZoneAndPhasedOutAt? preExistBear.id 0 == some (.battlefield, false)`);
  --      - Pre-existing object `olderPreBear` with SMALLER ID than `newerPreHero` (referenced at `events[0]`) followed by
  --        in-place `.materializeObject olderPreBear` is NOT treated as initial (`monotonic ID/timestamp` check)!
  let gMatRef0 := quiet (addPermanent (addPermanent g4 bear p0 p0) hero p0 p0)
  let olderPreBear := (gMatRef0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let newerPreHero := (gMatRef0.permanentsOf p0).find? (·.name == hero.name) |>.get!
  let gMatRef1 :=
    (gMatRef0.record (GameEvent.tapped gMatRef0.turnNumber (gMatRef0.snapshot newerPreHero) (cause := testCause))).change
      (.materializeObject olderPreBear)

  let item3bOk :=
    gTokAfter0.controllerOfAt (gTokAfter0.object! tokId) 0 == none &&
    gTokAfter0.objectZoneAndPhasedOutAt? tokId 0 == none &&
    gHand0.controllerOfAt (gHand0.object! handCardId) 0 == none &&
    gHand0.objectZoneAndPhasedOutAt? handCardId 0 == none &&
    gMovedAfter0.controllerOfAt (gMovedAfter0.object! bfNewId) 1 == none &&
    gMovedAfter0.objectZoneAndPhasedOutAt? bfNewId 1 == none &&
    newGyId != deadBid &&
    gDeadBid3.controllerOfAt (gDeadBid3.object! watchBearId) postDeadIdx == some p0 &&
    olderPreBear.id.raw < newerPreHero.id.raw &&
    gMatRef1.objectZoneAndPhasedOutAt? olderPreBear.id 0 == some (Zone.battlefield, false) &&
    gMatRef1.controllerOfAt (gMatRef1.object! olderPreBear.id) 0 == some p0

  -- 3c. `Phasing`:
  --     (i) Pre-`events[0]` (`sinceIdx? == none`) phased-out permanent under departed `p1` when `turnBegan` at `events[0]`
  --         skips `p1` (`p0 -> p2`, reconstructing `initAp := p0` backward across `events[0]`): phases in at `events[0]`!
  --     (ii) Pre-`events[0]` EXTRA turn (`turnBegan p2 (extra := true)` at `events[0]`): CR 500.7 `!extra` guard does NOT
  --          treat departed `p1`'s regular turn as skipped during `p2`'s extra turn!
  let gPhTmp := addPermanent (mustApply g4 p1 .concede) bear p0 p1
  let phTarget := (gPhTmp.objects.filter (fun o => o.zone == .battlefield && o.name == bear.name))[0]!
  let gPhSkip0 := quiet (gPhTmp.phaseOut phTarget (cause := some testCause))
  let phSkipId := phTarget.id
  let gPhSkipRegular :=
    (gPhSkip0.record (GameEvent.turnBegan (gPhSkip0.turnNumber + 1) p2 (extra := false))).phaseInControlled p2
  let gPhSkipOnExtra :=
    (gPhSkip0.record (GameEvent.turnBegan (gPhSkip0.turnNumber + 1) p2 (extra := true))).phaseInControlled p2

  let item3cOk :=
    (gPhSkip0.object! phSkipId).status.phasedOut &&
    gPhSkipRegular.activePlayer == p2 &&
    gPhSkipRegular.events.any (fun ev =>
      match ev.change with
      | .rules (.permanent (.phasedIn eo _)) => eo.id == some phSkipId
      | _ => false) &&
    (gPhSkipRegular.followMovedToZone? phSkipId (· == .exile)).isSome &&
    gPhSkipOnExtra.activePlayer == p2 &&
    (gPhSkipOnExtra.object! phSkipId).status.phasedOut

  let gFullHist3 :=
    ((addPermanent (addPermanent g4 bear p0 p0) trampleHeroDef p0 p0).createEffect
      (.layered noTrampleScope (.control p1) .untilEndOfTurn) (cause := some testCause)).clearEOT

  mustHold43i3 "3a.historicalControlChanged" item3aOk &&
  mustHold43i3 "3b.deadBeforeIdAndPreExistence" item3bOk &&
  mustHold43i3 "3c.phasingPreLogAndExtraGuard" item3cOk &&
  mustHold43i3 "3.replay"
    (replayOk43i3 #[gTokAfter0, gFullHist3])

end Phase43Item3EventAlignment

section Phase43Item4EventAlignment

private def mustHold43i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase43Item4EventAlignment failed: {label}"

private def replayOk43i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let g2 := afterDraw
  let canAct0 (g0 : Game) (oid : ObjectId) : Bool :=
    let o := g0.object! oid
    g0.canActivate p0 o (g0.activatedAbilitiesOf o)[0]!
  let stillPayable (g0 : Game) : Bool :=
    g0.sourceStillPayable g0.proposedSpell.get!

  -- 4a. Resolving stack-object `forObject` priority (`resolvingAbility` / `resolvingSpell` ahead of permanent `sourceId`
  --     in `Decisions.payGeneric` / `ResolutionChoices.mayPaySymbolsThen` / `Interpreter` `.nivPay`) AND `spellCast`-bounded
  --     `manaSpentOn`, `treasureManaSpentOn`, `legendaryManaSpentOn`, and `ancestryManaSpentOn`:
  let ancestryLandDef : CardDef := {
    name := "P43i4 PathOfAncestry"
    types := #[.land]
    triggeredAbilities := #[TriggeredAbility.onManaSpentCastCommanderTypeScry]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])]
  }
  let legManaArtifactDef : CardDef := {
    name := "P43i4 MoxRelic"
    supertypes := #[.legendary]
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])]
  }
  let treasureDef : CardDef := {
    name := "P43i4 Treasure"
    types := #[.artifact]
    subtypes := #["Treasure"]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self]
      effect := { Effect.addMana #[.colorless] with }
    }]
  }
  let gBound0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent g2 ancestryLandDef p0 p0) legManaArtifactDef p0 p0) treasureDef p0 p0)
      bear p0 .stack (some p0)
  let ancId := (gBound0.permanentsOf p0).find? (·.name == ancestryLandDef.name) |>.get!.id
  let legSrcId := (gBound0.permanentsOf p0).find? (·.name == legManaArtifactDef.name) |>.get!.id
  let trSrcId := (gBound0.permanentsOf p0).find? (·.name == treasureDef.name) |>.get!.id
  let castSpellObj := (gBound0.objects.filter (·.zone == .stack)).back!
  -- Cast `castSpellObj` spending ONLY 1 plain unattributed mana BEFORE `spellCast`, then spend Treasure, Legendary, and Ancestry mana
  -- with `forObject := some castSpellObj.id` AFTER `spellCast` (during resolution, e.g. `.mayPayGeneric`):
  let gPreCastSpent :=
    ((gBound0.addMana p0 .colorless 1).record
      (GameEvent.manaSpent gBound0.turnNumber p0 #[{ mana := .colorless }] (forObject := some castSpellObj.id)))
  let gCastRecorded :=
    gPreCastSpent.record
      (GameEvent.spellCast gPreCastSpent.turnNumber p0 (gPreCastSpent.snapshot castSpellObj) (.hand p0))
  let postUnits : Array ManaUnit := #[
    { mana := .colorless, source := some trSrcId, fromTreasure := true },
    { mana := .colorless, source := some legSrcId, restriction := some .legendarySpell },
    { mana := .colorless, source := some ancId }
  ]
  let gPostCastSpent :=
    (gCastRecorded.record (GameEvent.manaAdded gCastRecorded.turnNumber p0 postUnits)).record
      (GameEvent.manaSpent gCastRecorded.turnNumber p0 postUnits (forObject := some castSpellObj.id))

  -- Also check `Decisions.payGeneric` (`.mayPayGeneric p0 1`) under `resolvingAbility := some abObj.id` (`abObj.sourceId == some ancId`):
  let (gPayGen0, abObj) := (gBound0.addMana p0 .colorless 1).allocStackAbility (gBound0.object! ancId) p0
  let prePayGenIdx := gPayGen0.events.size
  let gPayGenPrompt :=
    gPayGen0.changes #[
      .pushContinuationFrame { resolvingAbility := some abObj.id },
      .pending (.mayPayGeneric p0 1) ]
  let gPayGenDone := mustApply gPayGenPrompt p0 .payGeneric
  let payGenAttributedToAb :=
    (gPayGenDone.events.extract prePayGenIdx gPayGenDone.events.size).any fun ev =>
      match ev.change with
      | .rules (.player (.manaSpent _ _ forObj)) => forObj == some abObj.id && forObj != some ancId
      | _ => false

  let item4aOk :=
    GameEvent.manaSpentOn gPostCastSpent.events castSpellObj.id == 1 &&
    !GameEvent.treasureManaSpentOn gPostCastSpent.events castSpellObj.id &&
    !GameEvent.legendaryManaSpentOn gPostCastSpent.events castSpellObj.id &&
    !gPostCastSpent.ancestryManaSpentOn castSpellObj.id &&
    payGenAttributedToAb

  -- 4b. Battlefield-source & mixed graveyard/hand cost-zone guards (`.crew` & `.zemoBoast` off-battlefield rejected,
  --     `fromGy && fromHand` and `(fromGy || fromHand) && needsBattlefieldSource` rejected, while graveyard
  --     `sacrificeAnotherCreatureOrArtifact` remains legal):
  let crewCardDef : CardDef := {
    name := "P43i4 Skiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some (.fixed 3)
    toughness := some (.fixed 3)
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapObjects (.totalPowerAtLeast (.const 1)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])]
      activeZones := #[.graveyard]
      effect := Effect.gainLife 1
    }]
  }
  let mixedGyHandDef : CardDef := {
    creature "P43i4 MixedGyHand" ManaCost.empty #["Spirit"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.exile (.exact 1) .yourGraveyard .self, .discard (.exact 1) .self]
      activeZones := #[.graveyard, .hand]
      effect := Effect.gainLife 1
    }]
  }
  let mixedGyTapDef : CardDef := {
    creature "P43i4 MixedGyTap" ManaCost.empty #["Zombie"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .mana (ManaCost.ofGeneric 1)]
      activeZones := #[.graveyard]
      effect := Effect.gainLife 1
    }]
  }
  let gySacOtherDef : CardDef := {
    creature "P43i4 GyAltars" ManaCost.empty #["Cleric"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))]
      activeZones := #[.graveyard]
      effect := Effect.gainLife 2
    }]
  }
  let gZoneGuards0 :=
    (insertObject
      (insertObject
        (insertObject
          (insertObject
            (insertObject (readyControlledForTurn (addPermanent g2 bear p0 p0) p0) crewCardDef p0 (.graveyard p0))
            mixedGyHandDef p0 (.graveyard p0))
          mixedGyHandDef p0 (.hand p0))
        mixedGyTapDef p0 (.graveyard p0))
      gySacOtherDef p0 (.graveyard p0)).addMana p0 .colorless 2
  let gyIds := (gZoneGuards0.player p0).graveyard
  let crewGyId := gyIds.find? (fun id => (gZoneGuards0.object! id).name == crewCardDef.name) |>.get!
  let mixGyId := gyIds.find? (fun id => (gZoneGuards0.object! id).name == mixedGyHandDef.name) |>.get!
  let mixTapGyId := gyIds.find? (fun id => (gZoneGuards0.object! id).name == mixedGyTapDef.name) |>.get!
  let gySacOtherId := gyIds.find? (fun id => (gZoneGuards0.object! id).name == gySacOtherDef.name) |>.get!
  let mixHandId := (gZoneGuards0.player p0).hand.find? (fun id => (gZoneGuards0.object! id).name == mixedGyHandDef.name) |>.get!
  let bfFodderId := (gZoneGuards0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gGySacProp := mustApply gZoneGuards0 p0 (.activate gySacOtherId 0)
  let gGySacPaying := mustApply gGySacProp p0 .pay
  let gGySacPaid := mustApply gGySacPaying p0 (.sacrifice bfFodderId)

  let item4bOk :=
    !canAct0 gZoneGuards0 crewGyId &&
    !canAct0 gZoneGuards0 mixGyId &&
    !canAct0 gZoneGuards0 mixHandId &&
    !canAct0 gZoneGuards0 mixTapGyId &&
    canAct0 gZoneGuards0 gySacOtherId &&
    gGySacPaid.stack.size == 1 &&
    (gGySacPaid.followMovedToZone? bfFodderId (· == .graveyard p0)).isSome

  -- 4c. `Timing.isManaActivation` & `ManaAbilities` parity (modal activated abilities, `fromGy`/`fromHand`, `removeStoryCounter`,
  --     `powerUp` + `activationManaCost` + `powerUpActivations`, `exhaust` + `exhaustUsed`, `timing := .sorcery`, `turnLimit?`)
  --     AND CR 601.2g self-sacrificing mana abilities (`isPlainTap == false`, `manaSourcesForProposed` source reservation,
  --     and `sourceStillPayable` + `Action.pay` succeeding after sacrificing `src` to a CR 601.2g mana ability):
  let modalAddManaAb : ActivatedAbility :=
    ActivatedAbility.mkModal (CostSpec.ofItems #[.tapSelf]) #[
      { Effect.addMana #[.colorless] with },
      Effect.gainLife 1
    ]
  let gyAddManaAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.exile (.exact 1) .yourGraveyard .self]
    activeZones := #[.graveyard]
    effect := { Effect.addMana #[.colorless] with }
  }
  let storyPowerExhaustDef : CardDef := {
    creature "P43i4 Dynamo" ManaCost.empty #["Construct"] 2 2 with
    activatedAbilities := #[
      -- idx 0: `removeStoryCounter` + `exhaust` mana ability
      { cost := CostSpec.ofItems #[.removeCounters (.exact 1) (some .story) .self]
        tag? := some .exhaust
        lifetimeLimit? := some 1
        effect := { Effect.addMana #[.colored .blue] with } },
      -- idx 1: `powerUp` + `timing := .sorcery` mana ability costing `{2}`
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)]
        tag? := some .powerUp
        lifetimeLimit? := some 1
        timing := .sorcery
        effect := { Effect.addMana #[.colored .red, .colored .red, .colored .red] with } }
    ]
  }
  let selfSacManaAndManaAbDef : CardDef := {
    name := "P43i4 LotusAltar"
    types := #[.artifact]
    staticAbilities := #[.otherPowerUpCostsLess 1]
    activatedAbilities := #[
      -- idx 0: mana-only activated ability `{2}: Gain 3 life.` (does NOT need battlefield source at CR 601.2h!)
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)]
        effect := Effect.gainLife 3 },
      -- idx 1: `{2}, {T}: Gain 3 life.` (DOES need battlefield source `{T}`!)
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf]
        effect := Effect.gainLife 3 },
      -- mana def 0: `{T}: Add {C}.`
      ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)]),
      -- mana def 1: `{T}, Sacrifice: Add three mana of any one color.`
      ActivatedAbility.manaAbility (.oneOf .anyColor (.const 3))
        (cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self])
    ]
  }

  -- Add only `{1}` colorless mana so `dynObj`'s `{2}` `powerUp` mana ability requires `altarObj`'s `.otherPowerUpCostsLess 1` reduction!
  let gParity0 :=
    ((addPermanent (addPermanent g2 storyPowerExhaustDef p0 p0) selfSacManaAndManaAbDef p0 p0).addMana p0 .colorless 1)
  let dynObj := (gParity0.permanentsOf p0).find? (·.name == storyPowerExhaustDef.name) |>.get!
  let altarObj := (gParity0.permanentsOf p0).find? (·.name == selfSacManaAndManaAbDef.name) |>.get!
  -- Without a story counter, mana ability 0 on `dynObj` fails; with 2 story counters it succeeds once and sets `exhaustUsed` so a 2nd try fails!
  let noStoryFails := (gParity0.activateManaAbility p0 dynObj.id 0 #[.colored .blue]).toOption.isNone
  let gWithStory := gParity0.recordPutCounters dynObj.id .story 2 (some p0) (cause := some testCause)
  let gExhaust1 : Game :=
    match gWithStory.activateManaAbility p0 dynObj.id 0 #[.colored .blue] with
    | .ok g => g
    | .error e => panic! e
  let exhaustSecondFails := (gExhaust1.activateManaAbility p0 dynObj.id 0 #[.colored .blue]).toOption.isNone
  -- `powerUp` + `onlyAsSorcery`: fails when `priority != p0` (non-sorcery), succeeds at sorcery speed paying reduced `{1}` (leaving `{U}` in pool!),
  -- increments `powerUpActivations`, and a 2nd `powerUp` try fails at `powerUpActivationLimit == 1`!
  let powerUpNonSorceryFails :=
    ((gExhaust1.change (.priority ⟨1⟩)).activateManaAbility p0 dynObj.id 1 #[.colored .red, .colored .red, .colored .red]).toOption.isNone
  let gPowerUp1 : Game :=
    match gExhaust1.activateManaAbility p0 dynObj.id 1 #[.colored .red, .colored .red, .colored .red] with
    | .ok g => g
    | .error e => panic! e
  let powerUpSecondFails :=
    (gPowerUp1.activateManaAbility p0 dynObj.id 1 #[.colored .red, .colored .red, .colored .red]).toOption.isNone

  -- CR 601.2g self-sacrificing mana ability on `altarObj` (mana def 0 is plain `{T}: Add {C}`, mana def 1 is `.tapSacrificeAddThreeOfOneColor`):
  let altarManaDef := (gParity0.manaAbilityDefs altarObj)[1]!
  -- Propose ability 0 (`{2}: Gain 3 life`, no `{T}`), check `manaSourcesForProposed` includes `altarId` (only `{C}`, NOT the self-sac colors!),
  -- sacrifice `altarObj` for `{W}{W}{W}` during CR 601.2g, check `stillPayable == true`, and `.pay`!
  let gAltarBase := addPermanent g2 selfSacManaAndManaAbDef p0 p0
  let altarId := (gAltarBase.permanentsOf p0).find? (·.name == selfSacManaAndManaAbDef.name) |>.get!.id
  let gAltarProp0 := mustApply gAltarBase p0 (.activate altarId 0)
  let prop0SourcesIncludeAltar :=
    (gAltarProp0.manaSourcesForProposed p0 gAltarProp0.proposedSpell.get!).any
      (fun (o, ts) => o.id == altarId && ts == #[.colorless])
  let gAltarSacForMana : Game :=
    match gAltarProp0.activateManaAbility p0 altarId 1 #[.colored .white, .colored .white, .colored .white] with
    | .ok g => g
    | .error e => panic! e
  let gAltarPaid := mustApply gAltarSacForMana p0 .pay
  -- By contrast, proposing ability 1 (`{2}, {T}: Gain 3 life`) reserves `altarId` so `manaSourcesForProposed` excludes `altarId`
  -- and `activateManaAbility` refuses to sacrifice `altarId`!
  let gAltarTapProp := mustApply gAltarBase p0 (.activate altarId 1)
  let prop1SourcesIncludeAltar :=
    (gAltarTapProp.manaSourcesForProposed p0 gAltarTapProp.proposedSpell.get!).any (fun (o, _) => o.id == altarId)
  let sacTapSourceRejected :=
    (gAltarTapProp.activateManaAbility p0 altarId 1 #[.colored .white, .colored .white, .colored .white]).toOption.isNone

  let item4cOk :=
    Game.isManaActivation modalAddManaAb &&
    Game.isManaActivation gyAddManaAb &&
    noStoryFails &&
    (gExhaust1.object! dynObj.id).status.story == 1 &&
    gExhaust1.exhaustUsed dynObj.id &&
    exhaustSecondFails &&
    powerUpNonSorceryFails &&
    gPowerUp1.powerUpActivations dynObj.id == 1 &&
    powerUpSecondFails &&
    !altarManaDef.isPlainTap &&
    prop0SourcesIncludeAltar &&
    stillPayable gAltarSacForMana &&
    gAltarPaid.stack.size == 1 &&
    (gAltarPaid.player p0).manaPool.total == 1 &&
    !prop1SourcesIncludeAltar &&
    sacTapSourceRejected

  -- 4d. `tapForMana` rejects unusable mana abilities (`"cannot produce"`) instead of falling back past `manaAbilityDefUsable`
  --     while still advancing to a later usable mana ability, AND `.crew` / `.zemoBoast` clear battlefield-source reservation once paid:
  let p1 : PlayerId := ⟨1⟩
  let cannotProduceErr (res : Except String Game) : Bool :=
    match res with
    | .error msg => mentions msg "cannot produce"
    | .ok _ => false
  let tapNoStoryCannotProduce := cannotProduceErr (gParity0.tapForMana p0 dynObj.id (.colored .blue))
  let tapExhaustedCannotProduce := cannotProduceErr (gExhaust1.tapForMana p0 dynObj.id (.colored .blue))
  let tapNonSorceryCannotProduce :=
    cannotProduceErr ((gExhaust1.change (.priority p1)).tapForMana p0 dynObj.id (.colored .red))
  let tapPowerUpUsedCannotProduce := cannotProduceErr (gPowerUp1.tapForMana p0 dynObj.id (.colored .red))
  let dualBlueDef : CardDef := {
    name := "P43i4 DualWell"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.tapSelf], tag? := some .exhaust, lifetimeLimit? := some 1
        effect := { Effect.addMana #[.colored .blue] with } },
      { cost := CostSpec.ofItems #[.tapSelf, .payLife (.const 1)]
        effect := { Effect.addMana #[.colored .blue] with } }
    ]
  }
  let gDual0 := addPermanent g2 dualBlueDef p0 p0
  let dualId := (gDual0.permanentsOf p0).find? (·.name == dualBlueDef.name) |>.get!.id
  let gDual1 := mustApply gDual0 p0 (.tapForMana dualId (.colored .blue))
  let gDualUntapped := gDual1.untapPermanent (gDual1.object! dualId) (cause := some testCause)
  let gDual2 := mustApply gDualUntapped p0 (.tapForMana dualId (.colored .blue))

  let crewManaChariotDef : CardDef := {
    name := "P43i4 ManaChariot"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some (.fixed 4)
    toughness := some (.fixed 4)
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 3 },
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 5 },
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapObjects (.totalPowerAtLeast (.const 0)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 1 },
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf, .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 7 },
      ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)]),
      ActivatedAbility.manaAbility (.oneOf .anyColor (.const 3))
        (cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self])
    ]
  }
  let gCrBase := addPermanent (addPermanent g2 crewManaChariotDef p0 p0) bear p0 p0
  let chariotId := (gCrBase.permanentsOf p0).find? (·.name == crewManaChariotDef.name) |>.get!.id
  let pilotId := (gCrBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gCrCombat := mustApply (mustApply gCrBase p0 .pass) p1 .pass
  let agentChoosesCrewMana :=
    match Agent.choose gCrCombat p0 with
    | some (.activate id 0) => id == chariotId
    | _ => false
  let gCrStep1 := mustApply gCrBase p0 (.activate chariotId 0)
  let crUnreservedAtMana := !gCrStep1.proposedNeedsBattlefieldSource gCrStep1.proposedSpell.get!
  let crInManaSources :=
    (gCrStep1.manaSourcesForProposed p0 gCrStep1.proposedSpell.get!).any (fun (o, _) => o.id == chariotId)
  let agentTapsChariot :=
    match Agent.choose gCrStep1 p0 with
    | some (.tapForMana id .colorless) => id == chariotId
    | _ => false
  let gCrStep2 := mustApply gCrStep1 p0 (.tapForMana chariotId .colorless)
  let gCrStep3 := mustApply gCrStep2 p0 .pay
  let gCrStep4 := mustApply gCrStep3 p0 (.choosePermanents #[pilotId])

  let gCrZero1 := mustApply gCrBase p0 (.activate chariotId 2)
  let gCrZero2 := mustApply gCrZero1 p0 (.tapForMana chariotId .colorless)
  let gCrZero3 := mustApply gCrZero2 p0 .pay
  let gCrZero4 := mustApply gCrZero3 p0 (.choosePermanents #[])

  let gCrTap1 := mustApply gCrBase p0 (.activate chariotId 3)
  let crTapStillReserved :=
    gCrTap1.proposedNeedsBattlefieldSource gCrTap1.proposedSpell.get! &&
    (gCrTap1.tapForMana p0 chariotId .colorless).toOption.isNone &&
    (gCrTap1.activateManaAbility p0 chariotId 1 #[.colored .red, .colored .red, .colored .red]).toOption.isNone

  let gCrSac1 := mustApply gCrBase p0 (.activate chariotId 1)
  let gCrSac2 : Game :=
    match gCrSac1.activateManaAbility p0 chariotId 1 #[.colored .red, .colored .red, .colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gCrSac3 := mustApply gCrSac2 p0 .pay
  let gCrSac4 := mustApply gCrSac3 p0 (.choosePermanents #[pilotId])

  let black15Def : CardDef :=
    creature "P43i4 Black15" { symbols := Array.replicate 15 (.colored .black) } #["Horror"] 2 2
  let boastManaZemoDef : CardDef := {
    creature "P43i4 ManaZemo" ManaCost.empty #["Human", "Villain"] 3 3 with
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .exile (.totalManaSymbolsAtLeast (some .black) (.const 15)) .yourGraveyard (.filter (.all #[.hasColor (.literal .black), .isKind .card]))], effect := Effect.gainLife 4, tag? := some .boast },
      ActivatedAbility.manaAbility (.oneOf .anyColor (.const 3))
        (cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self])
    ]
  }
  let gZm0 := insertObject (addPermanent g2 boastManaZemoDef p0 p0) black15Def p0 (.graveyard p0)
  let zemoObj := (gZm0.permanentsOf p0).find? (·.name == boastManaZemoDef.name) |>.get!
  let zemoId := zemoObj.id
  let black15Id := (gZm0.player p0).graveyard.back!
  let gZmBase := gZm0.record (GameEvent.attacked gZm0.turnNumber p0 (gZm0.snapshot zemoObj) p1)
  let gZm1 := mustApply gZmBase p0 (.activate zemoId 0)
  let zmUnreservedAtMana := !gZm1.proposedNeedsBattlefieldSource gZm1.proposedSpell.get!
  let gZm2 : Game :=
    match gZm1.activateManaAbility p0 zemoId 0 #[.colored .black, .colored .black, .colored .black] with
    | .ok g => g
    | .error e => panic! e
  let gZm3 := mustApply gZm2 p0 .pay
  let gZm4 := mustApply gZm3 p0 (.choosePermanents #[black15Id])

  let item4dOk :=
    tapNoStoryCannotProduce && tapExhaustedCannotProduce &&
    tapNonSorceryCannotProduce && tapPowerUpUsedCannotProduce &&
    (gDual1.player p0).life == 20 && gDual1.exhaustUsed dualId &&
    (gDual2.player p0).life == 19 && (gDual2.player p0).manaPool.blue == 2 &&
    agentChoosesCrewMana && crUnreservedAtMana &&
    crInManaSources && agentTapsChariot &&
    gCrStep4.stack.size == 1 && (gCrStep4.object! chariotId).status.tapped &&
    gCrZero4.stack.size == 1 && (gCrZero4.object! chariotId).status.tapped &&
    crTapStillReserved &&
    stillPayable gCrSac2 && stillPayable gCrSac3 &&
    gCrSac4.stack.size == 1 && (gCrSac4.player p0).manaPool.total == 1 &&
    zmUnreservedAtMana &&
    stillPayable gZm2 && stillPayable gZm3 &&
    gZm4.stack.size == 1 && gZm4.boastUsedThisTurn zemoId &&
    (gZm4.player p0).manaPool.total == 1

  mustHold43i4 "4a.forObjAndCastManaBounds" item4aOk &&
  mustHold43i4 "4b.zoneAndBattlefieldSourceGuards" item4bOk &&
  mustHold43i4 "4c.manaParityAndSelfSac6012g" item4cOk &&
  mustHold43i4 "4d.tapFallbackAndPostFraUnreserve" item4dOk &&
  mustHold43i4 "4.replay"
    (replayOk43i4 #[gPostCastSpent, gPayGenDone, gGySacPaid, gExhaust1, gPowerUp1,
      gAltarSacForMana, gAltarPaid, gAltarTapProp,
      gDual2, gCrStep4, gCrZero4, gCrTap1, gCrSac2, gCrSac3, gCrSac4, gZm2, gZm3, gZm4])

end Phase43Item4EventAlignment

section Phase44Item1EventAlignment

private def mustHold44i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase44Item1EventAlignment failed: {label}"

private def replayOk44i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with supertypes := #[.legendary] }
  let legHeroDef : CardDef := { hero with supertypes := #[.legendary] }
  let nonAttGrantorDef : CardDef := { name := "P44i1 RelicGrantor", types := #[.artifact] }
  let p2AnchorDef : CardDef := { name := "P44i1 P2Anchor", types := #[.artifact] }
  let leyADef : CardDef := { name := "P44i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P44i1 LeyB", types := #[.enchantment] }
  let p3LandDef : CardDef := { name := "P44i1 Forest", types := #[.land], activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])] }

  -- 1a(i). `!flushedFromPending && !deferRestore` in `rewriteRepausedPostCloseBatch`:
  --        Pause on 2-group legend batch (`grp1` + `grp2`), move `pausedCont` onto `outerPendingReplacements`,
  --        set `p1` to 0 life, and invalidate `grp1` so `checkSBACountedWithLeavesCore (deferRestore := false)`
  --        flushes `grp1` from `outerPendingReplacements` (`!flushedFromPending`) and re-pauses on `grp2`:
  --        `.leavePlayersWhoLost` MUST be chained directly onto `g.pendingReplacement` (NOT `outerPendingReplacements`),
  --        so a subsequent `flushedFromPending == true` invalidation of `grp2` still runs `.leavePlayersWhoLost`!
  let gTwoGrp0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
        legHeroDef p0 p0)
      legHeroDef p0 p0
  let gTwoPaused0 := gTwoGrp0.checkSBA
  let grp1CopyId := match gTwoPaused0.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999999⟩
  let pausedCont0 := gTwoPaused0.pendingReplacement.get!
  let (gGrp1Inv0, _) :=
    (gTwoPaused0.changes #[
      .pendingReplacement none,
      .pushOuterPendingReplacement pausedCont0 ]).setLifeTotal p1 0
      |>.move grp1CopyId .exile none (cause := some testCause)
  let (gRepMid1, repDid1, _, repPop1, _, _) :=
    gGrp1Inv0.checkSBACountedWithLeavesCore
      (savedIn := some (.mayPayGeneric p0 1)) (popOuterIn := true) (departedIn := #[p2]) (deferRestore := false)
  let grp2CopyId := match gRepMid1.pending with | .chooseLegend _ _ ids => ids[0]! | _ => ⟨999998⟩
  let (gGrp2Inv, _) := gRepMid1.move grp2CopyId .exile none (cause := some testCause)
  let (gRepAfterSecondFlush, _, _, _, _, _) :=
    gGrp2Inv.checkSBACountedWithLeavesCore (deferRestore := false)
  let gRepDrained := gRepAfterSecondFlush.drainPendingContinuations

  -- 1a(ii). `isPreProposalCheckpointBatch` across `flushDismissedPausedBatch`, `shouldFlush`, `.restorePending`,
  --         and `applyDeferredProposalRewind` when a proposal started inside an already-open batch `preCkptBid`
  --         is aborted by a departure that pauses on its own departure batch `depBid`:
  let preCkptBid : BatchId := ⟨9441⟩
  let gPreB0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 bear p3 p3) p2AnchorDef p2 p2)
          bear p2 p2)
        leyADef p0 p0)
      leyBDef p0 p0
  let preTargetBear := (gPreB0.permanentsOf p3)[0]!
  let preP2Anchor := (gPreB0.permanentsOf p2).find? (·.name == p2AnchorDef.name) |>.get!
  let preP2Bear := (gPreB0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let preLeyA := (gPreB0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let preLeyB := (gPreB0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let preRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some preLeyA, counterKind := some .plusOnePlusOne }
  let preRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some preLeyB, counterKind := some .plusOnePlusOne }
  let gPreBLink := addPermanent gPreB0 bear p0 p0
  let p0LinkBear := (gPreBLink.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let gPreB1 :=
    ((((gPreBLink.exileUntilSourceLeaves (some preP2Bear.id) p0LinkBear (cause := some testCause)).createEffect
      (.layered (.objects #[preTargetBear.id]) (.control p0) (.whileSourceOnBattlefield preP2Anchor.id))
      (cause := some testCause)).createEffect
      (.replacement {
        id := preRidA, source := some preLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := preRidB, source := some preLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
  let preBatchClose :=
    PendingReplacement.seq (.gainLife p0 7 (some testCause)) (.closeBatch preCkptBid gPreB1.events.size)
  let gPreBOpen :=
    gPreB1.changes #[
      .pauseBatch preCkptBid (some testCause) gPreB1.objects gPreB1.players gPreB1.activeEffects .none gPreB1.stack,
      .pushContinuationFrame {},
      .pendingReplacement (some preBatchClose),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement preBatchClose,
      .pendingReplacement none ]
  let (gPreB2, preAb) := gPreBOpen.putStackAbility preTargetBear p0 (abilityEffect := some (Effect.gainLife 1))
  let preProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := preAb.id, original := preAb
    originalSnapshot := gPreB2.snapshot preAb, kind := .activatedAbility
    sourceId := some preTargetBear.id, resolutionCast := true
  }
  let gPreBProposed := gPreB2.changes #[.proposedSpell (some preProp), .pending (.chooseX p0)]
  let gPreBPausedOnDep := mustApply gPreBProposed p2 .concede
  let depBatchId := gPreBPausedOnDep.currentBatch.map Prod.fst
  let gPreBResolved := mustApply gPreBPausedOnDep p0 (.chooseReplacement preRidA)

  let item1aOk :=
    repDid1 && !repPop1 &&
    gRepMid1.pendingReplacement.isSome &&
    gRepMid1.outerPendingReplacements.isEmpty &&
    (gRepDrained.player p1).leftTheGame &&
    gRepDrained.pending == .mayPayGeneric p0 1 &&
    depBatchId.isSome && depBatchId != some preCkptBid &&
    (gPreBResolved.player p2).leftTheGame &&
    gPreBResolved.proposedSpell.isNone &&
    gPreBResolved.proposalCheckpoint.isNone &&
    gPreBResolved.currentBatch.isNone &&
    (gPreBResolved.player p0).life == 27

  -- 1b. `Leaving.preBatchLegendSnapshotValid`:
  --     (i) Harmless Layer 5/7, non-static `.abilities` on filter/objects scopes, opponent filter-scope static effects,
  --         and `.player (.leftGame p2)` on `curPreG` keep `p0`'s snapshot-backed `.chooseLegend` valid!
  --     (ii) `openBatchPending` fallback when `g.pending` is `.none` and `false` on empty `promptIds`:
  let gLeg0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0)
          nonAttGrantorDef p0 p0)
        p2AnchorDef p2 p2)
      p2AnchorDef p1 p1
  let legBears := ((gLeg0.permanentsOf p0).filter (·.name == bear.name)).map (·.id)
  let p0Grantor := (gLeg0.permanentsOf p0).find? (·.name == nonAttGrantorDef.name) |>.get!
  let p2Src := (gLeg0.permanentsOf p2)[0]!
  let gLegPaused :=
    ((((((gLeg0.createEffect
      (.layered (.objects legBears) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield p0Grantor.id))
      (cause := some testCause)).createEffect
      (.layered (.creaturesControlledBy p0) (.ptModify 1 1) (.whileSourceOnBattlefield p2Src.id))
      (cause := some testCause)).createEffect
      (.layered (.objects legBears) (.colors .set { blue := true }) (.whileSourceOnBattlefield p2Src.id))
      (cause := some testCause)).createEffect
      (.layered (.creaturesControlledBy p0) (.abilities { keywords := #[Keyword.flying] } .none) (.whileSourceOnBattlefield p2Src.id))
      (cause := some testCause)).createEffect
      (.layered (.creaturesControlledBy p1) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield p2Src.id))
      (cause := some testCause)).checkSBA)
  let gLegAfterP2 := mustApply gLegPaused p2 .concede
  let stashedBid : BatchId := ⟨gLegAfterP2.nextBatchId + 40⟩
  let gStashedLegendBatch :=
    gLegAfterP2.changes #[
      .pending .none,
      .pauseBatch stashedBid (some testCause) gLegPaused.objects gLegPaused.players
        gLegPaused.activeEffects (.chooseLegend p0 bear.name legBears) gLegPaused.stack ]
  let openBatchFallbackValid := gStashedLegendBatch.preBatchLegendSnapshotValid
  let emptyBid : BatchId := ⟨gLegAfterP2.nextBatchId + 41⟩
  let gEmptyPromptBatch :=
    g4.changes #[
      .pauseBatch emptyBid (some testCause) g4.objects g4.players g4.activeEffects .none g4.stack ]
  let emptyPromptInvalid := !gEmptyPromptBatch.preBatchLegendSnapshotValid

  let item1bOk :=
    legBears.size == 2 &&
    gLegAfterP2.pending == .chooseLegend p0 bear.name legBears &&
    gLegAfterP2.preBatchLegendSnapshotValid &&
    openBatchFallbackValid &&
    emptyPromptInvalid

  -- 1c. `ensureEndsWithFinishResolutionChoice` `endsWithPriorityGrant` guard, `finishResolutionChoice` `alreadyGrants`,
  --     left-to-right `firstPriorityGrantRecipient?` / `hasImplicitPriorityContinuation`, and non-stale `pendingPriority` stamping:
  let explicitTail := PendingReplacement.seq (.gainLife p0 1 (some testCause)) (.receivePriority p3)
  let ensurePreservesExplicit := explicitTail.ensureEndsWithFinishResolutionChoice == explicitTail
  let gFraAlready :=
    (g4.changes #[.pushContinuationFrame {}, .pendingReplacement (some (.receivePriority p3))]).finishResolutionChoice
  let gImplicitBeforeExplicit :=
    g4.changes #[
      .pendingPriority (some p1),
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p2),
      .pendingReplacement (some .finishResolutionChoice) ]
  let implicitDetected := gImplicitBeforeExplicit.hasImplicitPriorityContinuation
  let gStampedOverStale := gImplicitBeforeExplicit.finishAndGrantPriority p3
  let gManaStale0 :=
    (addPermanent g4 p3LandDef p3 p3).changes #[
      .priority p3,
      .pendingPriority (some p1),
      .pushContinuationFrame {},
      .pushOuterPendingReplacement .finishResolutionChoice ]
  let p3LandId := (gManaStale0.permanentsOf p3)[0]!.id
  let gManaStamped := mustApply gManaStale0 p3 (.tapForMana p3LandId (.colored .green))

  let item1cOk :=
    ensurePreservesExplicit &&
    gFraAlready.priority == p3 &&
    implicitDetected &&
    gStampedOverStale.priority == p2 &&
    (gStampedOverStale.events.any fun ev =>
      ev.change == .engine (.pendingPriority (some p3))) &&
    gManaStamped.priority == p3 &&
    (gManaStamped.events.any fun ev =>
      ev.change == .engine (.pendingPriority (some p3)))

  mustHold44i1 "1a.repauseChainAndPreCkptBatch" item1aOk &&
  mustHold44i1 "1b.preBatchLegendSnapshotValid" item1bOk &&
  mustHold44i1 "1c.priorityContinuationGuards" item1cOk &&
  mustHold44i1 "1.replay"
    (replayOk44i1 #[gRepMid1, gRepDrained, gPreBPausedOnDep, gPreBResolved,
      gLegAfterP2, gStashedLegendBatch, gFraAlready, gStampedOverStale, gManaStamped])

end Phase44Item1EventAlignment

section Phase44Item2EventAlignment

private def mustHold44i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase44Item2EventAlignment failed: {label}"

private def replayOk44i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let eqDef : CardDef := { name := "P44i2 Eq", types := #[.artifact], subtypes := #["Equipment"] }
  let survEqDef : CardDef := { name := "P44i2 SurvEq", types := #[.artifact], subtypes := #["Equipment"] }
  let cmdCardDef : CardDef := { name := "P44i2 CmdRelic", types := #[.artifact] }
  let embDef : CardDef := { name := "P44i2 Emblem", types := #[] }

  -- 2a. `coDepartingIds` `.whileInZone` + `extraSkipIds` in `endControlEffectsSimultaneously` & `runEndControlExileLoop`,
  --     `skipLogIds` on co-departing copy restoration (while preserving copy-end log on surviving permanents),
  --     and `pre.name` in `Attachments.unattachFrom` + `(preState? := some board)` in `Movement.move`:
  let gP3Gone := mustApply g4 p3 .concede
  let gCo0 :=
    insertObject
      (addPermanent
        (addPermanent (addPermanent gP3Gone eqDef p0 p3) survEqDef p0 p0)
        bear p2 p2)
      bear p2 (.graveyard p2)
  let stolenEq := (gCo0.objects.filter (fun o => o.zone == .battlefield && o.name == eqDef.name))[0]!
  let survEq := (gCo0.permanentsOf p0).find? (·.name == survEqDef.name) |>.get!
  let p2Host := (gCo0.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let p2GyId := (gCo0.player p2).graveyard.back!
  let gCo1 :=
    (((((gCo0.createEffect
        (.layered (.objects #[stolenEq.id]) (.control p2) (.whileInZone p2GyId (.graveyard p2)))
        (cause := some testCause)).record
        (GameEvent.attached gCo0.turnNumber (gCo0.snapshot stolenEq) p2Host.id (cause := testCause))).record
        (GameEvent.attached gCo0.turnNumber (gCo0.snapshot survEq) p2Host.id (cause := testCause))).createEffect
        (.layered (.objects #[stolenEq.id]) (.copy hero) (.whileSourceOnBattlefield p2Host.id))
        (cause := some testCause)).createEffect
        (.layered (.objects #[survEq.id]) (.copy hero) (.whileSourceOnBattlefield p2Host.id))
        (cause := some testCause))
  let preCoEvIdx := gCo1.events.size
  let preCoLogIdx := gCo1.log.size
  let gCoAfter := mustApply gCo1 p2 .concede
  let coSlice := gCoAfter.events.extract preCoEvIdx gCoAfter.events.size
  let coLogs := gCoAfter.log.extract preCoLogIdx gCoAfter.log.size
  let coUnattachedIds :=
    coSlice.filterMap fun ev =>
      match ev.change with
      | .rules (.permanent (.unattached eo _)) => eo.id
      | _ => none

  -- `Movement.move` `(preState? := some board)` + `Attachments.unattachFrom` `pre.name`:
  let gMoveUn0 := addPermanent (addPermanent g4 bear p0 p0) eqDef p0 p0
  let muHost := (gMoveUn0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let muEq := (gMoveUn0.permanentsOf p0).find? (·.name == eqDef.name) |>.get!
  let gMoveUn1 :=
    (gMoveUn0.record (GameEvent.attached gMoveUn0.turnNumber (gMoveUn0.snapshot muEq) muHost.id (cause := testCause))).createEffect
      (.layered (.objects #[muEq.id]) (.copy hero) (.whileSourceOnBattlefield muHost.id))
      (cause := some testCause)
  let preMuLogIdx := gMoveUn1.log.size
  let (gMoveUnAfter, _) := gMoveUn1.move muHost.id (.graveyard p0) none (cause := some testCause)
  let muLogs := gMoveUnAfter.log.extract preMuLogIdx gMoveUnAfter.log.size

  let item2aOk :=
    (gCoAfter.followMovedToZone? stolenEq.id (· == .exile)).isSome &&
    coUnattachedIds == #[survEq.id] &&
    !coLogs.any (fun s => s.contains s!"{eqDef.name} is no longer a copy") &&
    coLogs.any (fun s => s.contains s!"{survEqDef.name} is no longer a copy") &&
    muLogs.any (· == s!"{hero.name} becomes unattached") &&
    !muLogs.any (· == s!"{eqDef.name} becomes unattached")

  -- 2b. Simultaneous `Turns.clearEOT` `preExpire` `.commandEmblem` expiry (preserving `.ringBearer`),
  --     cease-first `.commandEmblem` expiry in `Core.expireEffectById`, and controlled-not-owned `.command` departure:
  let gSimEmb0 := insertObject (addPermanent g4 bear p0 p0) embDef p1 .command (some p1)
  let myRingBear := (gSimEmb0.permanentsOf p0)[0]!
  let simEmb := (gSimEmb0.objects.filter (·.zone == .command))[0]!
  let gSimEmb1 :=
    ((((gSimEmb0.createEffect
      (.gameRule (.commandEmblem simEmb.id) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[myRingBear.id]) (.control p1) (.whileInZone simEmb.id .command))
      (cause := some testCause)).createEffect
      (.layered (.objects #[myRingBear.id]) (.control p0) .untilEndOfTurn)
      (cause := some testCause)).record
      (GameEvent.ringTempted gSimEmb0.turnNumber p0 (some myRingBear.id) 1 (cause := some testCause)))
  let gSimEmbAfter := gSimEmb1.clearEOT

  let gExpById0 := insertObject (addPermanent g4 eqDef p0 p0) embDef p0 .command (some p0)
  let expAnchor := (gExpById0.permanentsOf p0)[0]!
  let expEmb := (gExpById0.objects.filter (·.zone == .command))[0]!
  let gExpById1 :=
    gExpById0.createEffect
      (.gameRule (.commandEmblem expEmb.id) (.whileSourceOnBattlefield expAnchor.id))
      (cause := some testCause)
  let preExpByIdIdx := gExpById1.events.size
  let (gExpByIdAfter, _) := gExpById1.move expAnchor.id .exile none (cause := some testCause)
  let expSlice := gExpByIdAfter.events.extract preExpByIdIdx gExpByIdAfter.events.size
  let expCeasePos? := expSlice.findIdx? fun ev =>
    match ev.change with | .rules (.zone (.ceasedToExist eo)) => eo.id == some expEmb.id | _ => false
  let expEffPos? := expSlice.findIdx? fun ev =>
    match ev.change with | .rules (.continuousEffect (.expired ..)) => true | _ => false

  let gCmdDep0 :=
    insertObject
      (insertObject (mustApply g4 p3 .concede) embDef p0 .command (some p2))
      cmdCardDef p0 .command (some p2)
  let nonCardCmd := (gCmdDep0.objects.filter (fun o => o.zone == .command && o.name == embDef.name))[0]!
  let cardCmd := (gCmdDep0.objects.filter (fun o => o.zone == .command && o.name == cmdCardDef.name))[0]!
  let gCmdDepAfter := mustApply gCmdDep0 p2 .concede

  let item2bOk :=
    (gSimEmbAfter.findObject? simEmb.id).isNone &&
    (gSimEmbAfter.player p0).ringBearerId == some myRingBear.id &&
    (gExpByIdAfter.findObject? expEmb.id).isNone &&
    gExpByIdAfter.log.any (· == s!"{embDef.name} ends") &&
    (match expCeasePos?, expEffPos? with | some cIdx, some eIdx => cIdx < eIdx | _, _ => false) &&
    (gCmdDepAfter.findObject? nonCardCmd.id).isNone &&
    (gCmdDepAfter.followMovedToZone? cardCmd.id (· == .exile)).isSome

  -- 2c. 2HG departed higher-index teammate CR 800.4i expiry, `.playFromExile` `grantee` normalization & expiry logging,
  --     and CR 500.7 `lastRegularTurnSeat` regular-turn resumption:
  let cfg2hg : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "C0", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "C1", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed := 442
    startingPlayer := some 0
  }
  let gT0 : Game :=
    match Start.start cfg2hg with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  let gTWithBear := addPermanent gT0 bear ⟨0⟩ ⟨0⟩
  let a0BearId := (gTWithBear.permanentsOf ⟨0⟩)[0]!.id
  let (gB1Gone, _, _, _) :=
    (gTWithBear.record (GameEvent.playerLost gTWithBear.turnNumber ⟨3⟩ .lifeZeroOrLess)).playerLeavesGameCore ⟨3⟩
  let gB1Eff :=
    (gB1Gone.createEffect
      (.layered (.objects #[a0BearId]) (.ptModify 2 2) (.untilNextTurnOf ⟨3⟩))
      (cause := some testCause)).createEffect
      (.playerRule ⟨3⟩ (.additionalLands 1) .untilEndOfTurn)
      (cause := some testCause)
  -- Advance across both halves of Team A's shared turn (`⟨0⟩ -> ⟨1⟩ -> ⟨2⟩`) to Team B (`⟨2⟩`, whose higher-index teammate `⟨3⟩` already departed):
  let gAtTeamB := gB1Eff.startNextTurnAndBegin.startNextTurnAndBegin

  -- `.playFromExile` `grantee` normalization + expiry logging:
  let gPerm0 := insertObject (insertObject g4 bear p1 .exile) hero p1 .exile
  let exImpId := (gPerm0.objects.filter (fun o => o.zone == .exile && o.name == bear.name))[0]!.id
  let exWhileId := (gPerm0.objects.filter (fun o => o.zone == .exile && o.name == hero.name))[0]!.id
  let gPerm1 :=
    (gPerm0.createEffect
      (.permission (some p0) (.playFromExile exImpId { player := p1 }) (.untilNextTurnOf p0))
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile exWhileId { player := p1, whileExiled := true }) (.untilNextTurnOf p0))
      (cause := some testCause)
  let normPermOk :=
    (gPerm1.playPermissionOf? (gPerm1.object! exImpId)).any (·.player == p0) &&
    gPerm1.mayPlayFromExile p0 (gPerm1.object! exImpId) &&
    !gPerm1.mayPlayFromExile p1 (gPerm1.object! exImpId)
  let prePermExpLog := gPerm1.log.size
  let gPermExpired := gPerm1.expireUntilTurnCommandEffects p0
  let permExpLogs := gPermExpired.log.extract prePermExpLog gPermExpired.log.size

  -- CR 500.7 `lastRegularTurnSeat`: `p0` on regular turn, `p2` concedes, `p1` takes an extra turn ->
  -- after `p1`'s extra turn ends, regular turn order resumes from `lastRegularTurnSeat == p0` at `p1`'s regular turn
  -- (NOT advancing past `p1` to skip `p2` into `p3`!):
  let gReg0 := addPermanent g4 bear p0 p0
  let p2PhasedId := (gReg0.permanentsOf p0)[0]!.id
  let gRegStolen :=
    gReg0.createEffect (.layered (.objects #[p2PhasedId]) (.control p2) .indefinite)
      (cause := some testCause)
  let gReg1 :=
    (mustApply (gRegStolen.phaseOut (gRegStolen.object! p2PhasedId) (cause := some testCause)) p2 .concede).record
      (GameEvent.extraTurnAdded gReg0.turnNumber p1 (cause := testCause))
  let gInP1Extra := gReg1.startNextTurnAndBegin
  let gResumedP1Regular := gInP1Extra.startNextTurnAndBegin
  let gAfterP1RegularToP3 := gResumedP1Regular.startNextTurnAndBegin

  let item2cOk :=
    gAtTeamB.activePlayer == ⟨2⟩ &&
    !gAtTeamB.activeEffects.any (fun (_, s) =>
      match s with
      | .layered _ (.ptModify 2 2) (.untilNextTurnOf _) => true
      | .playerRule q (.additionalLands 1) .untilEndOfTurn => q == ⟨3⟩
      | _ => false) &&
    normPermOk &&
    permExpLogs.any (· == s!"{bear.name} can no longer be played from exile") &&
    !permExpLogs.any (· == s!"{hero.name} can no longer be played from exile") &&
    gInP1Extra.activePlayer == p1 &&
    gInP1Extra.lastRegularTurnSeat == p0 &&
    gResumedP1Regular.activePlayer == p1 &&
    (gResumedP1Regular.object! p2PhasedId).status.phasedOut &&
    gAfterP1RegularToP3.activePlayer == p3 &&
    !(gAfterP1RegularToP3.object! p2PhasedId).status.phasedOut

  mustHold44i2 "2a.coDepartingAndUnattachPreName" item2aOk &&
  mustHold44i2 "2b.clearEotEmblemAndCommandLeave" item2bOk &&
  mustHold44i2 "2c.twoHgGranteeAndLastRegularTurn" item2cOk &&
  mustHold44i2 "2.replay"
    (replayOk44i2 #[gCoAfter, gMoveUnAfter, gSimEmbAfter, gExpByIdAfter, gCmdDepAfter,
      gAtTeamB, gPermExpired, gResumedP1Regular, gAfterP1RegularToP3])

end Phase44Item2EventAlignment

section Phase44Item3EventAlignment

private def mustHold44i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase44Item3EventAlignment failed: {label}"

private def replayOk44i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let backFlyerDef : CardDef := { hero with name := "P44i3 BackFlyer", keywords := #[Keyword.flying] }
  let frontDfcDef : CardDef := { bear with name := "P44i3 FrontWalker", otherFace := some backFlyerDef }

  -- 3a. `Core.controlChanged`: off-battlefield `false`, inactive `.objects` `.control` `false`,
  --     and same-ID `.materializeObject` historical controller change `true`:
  let gHandCard := insertObject g3 bear p0 (.hand p0)
  let handObj := gHandCard.object! (gHandCard.player p0).hand.back!
  let gInact0 := addPermanent (addPermanent g3 bear p0 p0) hero p1 p1
  let inactTarget := (gInact0.permanentsOf p0)[0]!
  let inactSrc := (gInact0.permanentsOf p1)[0]!
  let gInact1 :=
    gInact0.createEffect
      (.layered (.objects #[inactTarget.id]) (.control p1) (.whileSourceHasCounter inactSrc.id .charge))
      (cause := some testCause)
  let gMatCtrl0 := addPermanent g3 bear p0 p1
  let matPerm := (gMatCtrl0.permanentsOf p1)[0]!
  let gMatCtrl1 :=
    gMatCtrl0.change (.materializeObject { matPerm with defaultController := some p0, controller := some p0 })

  let item3aOk :=
    !gHandCard.controlChanged handObj &&
    !gInact1.controlChanged (gInact1.object! inactTarget.id) &&
    gMatCtrl1.controllerOf (gMatCtrl1.object! matPerm.id) == some p0 &&
    gMatCtrl1.controlChanged (gMatCtrl1.object! matPerm.id)

  -- 3b. `objectCounterCountAt` `.tapped` pre-snapshot (`duringControllersTurn := true`) + non-initial `.materializeObject`,
  --     `objectZoneAndPhasedOutAt?` / `HistoricalSlice` non-initial `.materializeObject` rollback,
  --     `hasSummoningSickness` non-initial arrival onto `.battlefield`, and DFC `swapCardFace` in `HistoricalSlice`:
  let gCntBase := addPermanent g3 bear p0 p0
  let gCnt0 := quiet (gCntBase.addCounters (gCntBase.permanentsOf p0)[0]! .plusOnePlusOne 2 (cause := some testCause))
  let cntObj0 := (gCnt0.permanentsOf p0)[0]!
  let gCntTapped := gCnt0.becomeTapped cntObj0 (cause := some testCause)
  let cntTappedObj := gCntTapped.object! cntObj0.id
  let gCntMatZero := gCntTapped.change (.materializeObject { cntTappedObj with status := { cntTappedObj.status with counters := #[] } })

  let gNonInit0 := quiet (insertObject g3 bear p0 (.hand p0))
  let nonInitHandObj := gNonInit0.object! (gNonInit0.player p0).hand.back!
  -- Emit a pre-materialize event referencing `nonInitHandObj` in `.hand p0`, then materialize `nonInitHandObj` onto `.battlefield`:
  let gNonInit1 :=
    (gNonInit0.record
      (GameEvent.spellCast gNonInit0.turnNumber p0 { (gNonInit0.snapshot nonInitHandObj) with zone := .hand p0 } (.hand p0))).change
      (.materializeObject { nonInitHandObj with zone := .battlefield, defaultController := some p0, controller := some p0 })

  let gDfc0 :=
    quiet
      ((addPermanent g3 frontDfcDef p0 p0).createEffect
        (.layered (.creaturesWithout #[Keyword.flying]) (.control p1) .indefinite)
        (cause := some testCause))
  let dfcId := (gDfc0.permanentsOf p1)[0]!.id
  let gDfcTransformed := gDfc0.transformPermanent p0 (some dfcId) (cause := some testCause)

  let item3bOk :=
    gCntMatZero.objectCounterCountAt cntObj0.id .plusOnePlusOne 0 == 2 &&
    gCntMatZero.objectCounterCountAt cntObj0.id .plusOnePlusOne 1 == 2 &&
    gNonInit1.objectZoneAndPhasedOutAt? nonInitHandObj.id 0 == some (.hand p0, false) &&
    gNonInit1.controllerOfAt (gNonInit1.object! nonInitHandObj.id) 0 == none &&
    gNonInit1.hasSummoningSickness (gNonInit1.object! nonInitHandObj.id) &&
    gDfcTransformed.controllerOfAt (gDfcTransformed.object! dfcId) 0 == some p1 &&
    gDfcTransformed.controllerOf (gDfcTransformed.object! dfcId) == some p0 &&
    gDfcTransformed.controlChanged (gDfcTransformed.object! dfcId)

  -- 3c. `Core.isInitialMaterialize`:
  --     (i) `noSourceSentinelId` on a queued `WaitingTrigger` does NOT poison subsequent genuine `addPermanent`;
  --     (ii) same-ID `.moved` / mana `.abilityActivated` on pre-existing newer object does NOT mask pre-existence;
  --     (iii) pre-existing newer object that ceases after `matIdx` STILL proves `older` pre-existed (`createdSinceBound` scan);
  --     (iv) secondary `ObjectId` reference (`.cantUntap` source) before `matIdx` proves pre-existence:
  let sentinelTrig : WaitingTrigger := {
    controller := p0
    source := { id := noSourceSentinelId, printed := bear, owner := p0, zone := .battlefield }
    ability := default
  }
  let gSent0 := g3.change (.enqueueWaitingTriggers #[sentinelTrig])
  let preSentIdx := gSent0.events.size
  let gSent1 := addPermanent gSent0 bear p0 p0
  let freshAfterSentId := (gSent1.permanentsOf p0)[0]!.id

  let manaRelicDef : CardDef := { name := "P44i3 ManaRelic", types := #[.artifact], activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])] }
  let gNewerMana0 := quiet (addPermanent (addPermanent g3 bear p0 p0) manaRelicDef p0 p0)
  let olderBear := (gNewerMana0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let newerRelic := (gNewerMana0.permanentsOf p0).find? (·.name == manaRelicDef.name) |>.get!
  let gNewerMana1 := mustApply (gNewerMana0.change (.materializeObject olderBear)) p0 (.tapForMana newerRelic.id .colorless)

  let (gTokDep0, preNewerTok) := (addPermanent g3 bear p0 p0).createOneToken p0 hero (cause := some testCause)
  let gTokDepQuiet := quiet gTokDep0
  let olderBeforeTok := (gTokDepQuiet.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let gTokDep1 :=
    (gTokDepQuiet.change (.materializeObject olderBeforeTok)).ceaseToExist preNewerTok.id (cause := some testCause)

  let gSecRef0 := quiet (addPermanent (addPermanent g3 bear p0 p0) hero p0 p0)
  let secTgt := (gSecRef0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let secSrc := (gSecRef0.permanentsOf p0).find? (·.name == hero.name) |>.get!
  let gSecRef1 :=
    (gSecRef0.createEffect (.gameRule (.cantUntap secTgt.id secSrc.id) .untilEndOfTurn)
      (cause := some testCause)).change (.materializeObject secSrc)

  let item3cOk :=
    gSent1.objectZoneAndPhasedOutAt? freshAfterSentId preSentIdx == none &&
    gNewerMana1.objectZoneAndPhasedOutAt? olderBear.id 0 == some (.battlefield, false) &&
    gTokDep1.objectZoneAndPhasedOutAt? olderBeforeTok.id 0 == some (.battlefield, false) &&
    gSecRef1.objectZoneAndPhasedOutAt? secSrc.id 0 == some (.battlefield, false)

  -- 3d. Simultaneous phase-out batch pre-slice LKI in `Phasing.phaseOutPermanents` / `phaseInControlled`
  --     and 2HG shared-extra-turn `initAp` in `departedNextTurnWouldHaveBegunSince`:
  let gPhSim0 := addPermanent (addPermanent g3 hero p0 p0) bear p1 p1
  let phCtrlSrc := (gPhSim0.permanentsOf p0)[0]!
  let phStolen := (gPhSim0.permanentsOf p1)[0]!
  let gPhSimPre :=
    gPhSim0.createEffect
      (.layered (.objects #[phStolen.id]) (.control p0) (.whileSourceOnBattlefield phCtrlSrc.id))
      (cause := some testCause)
  let gPhSim1 :=
    gPhSimPre.phaseOutPermanents #[gPhSimPre.object! phCtrlSrc.id, gPhSimPre.object! phStolen.id] (cause := some testCause)
  let gPhAfterP1Untap := gPhSim1.phaseInControlled p1
  let gPhAfterP0Untap := gPhAfterP1Untap.phaseInControlled p0

  let cfg2hg3 : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "C0", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "C1", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed := 443
    startingPlayer := some 4
  }
  let g2hgInit0 : Game :=
    match Start.start cfg2hg3 with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  let g2hgTeamBGone := mustApply g2hgInit0 ⟨2⟩ .concede
  let g2hgWithPerm := addPermanent g2hgTeamBGone bear ⟨0⟩ ⟨2⟩
  let b0PhasedId := (g2hgWithPerm.objects.filter (fun o => o.zone == .battlefield && o.name == bear.name))[0]!.id
  let g2hgPhased := g2hgWithPerm.phaseOut (g2hgWithPerm.object! b0PhasedId) (cause := some testCause)
  -- Advance across Team C's regular turn (`⟨4⟩ -> ⟨5⟩`) into the first half of Team A's shared extra turn (`⟨0⟩`, `extraTurns == #[⟨1⟩]`):
  let g2hgExtraA0 :=
    (g2hgPhased.record
      (GameEvent.extraTurnAdded g2hgPhased.turnNumber ⟨0⟩ (cause := testCause))).startNextTurnAndBegin.startNextTurnAndBegin
  -- Pre-`turnBegan` slice in the middle of Team A's shared extra turn (`activePlayer == ⟨0⟩`, `startingPlayer == ⟨4⟩`):
  -- advancing `⟨0⟩` extra -> `⟨1⟩` extra -> `⟨0⟩` regular must keep `b0PhasedId` phased out until Team A finishes (`⟨0⟩ -> ⟨1⟩ -> ⟨4⟩`):
  let g2hgQuietSlice :=
    ((quiet g2hgExtraA0).record (GameEvent.stepBegan g2hgExtraA0.turnNumber .precombatMain ⟨0⟩)).startNextTurnAndBegin
  let g2hgResumeRegA0 := g2hgQuietSlice.startNextTurnAndBegin
  let preAfterTeamAIdx := g2hgResumeRegA0.events.size
  let g2hgAfterTeamAToC0 := g2hgResumeRegA0.startNextTurnAndBegin.startNextTurnAndBegin
  let afterTeamAEvents := g2hgAfterTeamAToC0.events.extract preAfterTeamAIdx g2hgAfterTeamAToC0.events.size

  let item3dOk :=
    (gPhSim1.object! phCtrlSrc.id).status.phasedOut &&
    (gPhSim1.object! phStolen.id).status.phasedOut &&
    (gPhAfterP1Untap.object! phStolen.id).status.phasedOut &&
    !(gPhAfterP0Untap.object! phStolen.id).status.phasedOut &&
    g2hgQuietSlice.activePlayer == ⟨1⟩ &&
    (g2hgQuietSlice.object! b0PhasedId).status.phasedOut &&
    g2hgResumeRegA0.activePlayer == ⟨0⟩ &&
    (g2hgResumeRegA0.object! b0PhasedId).status.phasedOut &&
    g2hgAfterTeamAToC0.activePlayer == ⟨4⟩ &&
    afterTeamAEvents.any (fun ev =>
      match ev.change with
      | .rules (.permanent (.phasedIn eo _)) => eo.id == some b0PhasedId
      | _ => false) &&
    (g2hgAfterTeamAToC0.followMovedToZone? b0PhasedId (· == .exile)).isSome

  let gFullSent := gSent1
  mustHold44i3 "3a.controlChangedGuards" item3aOk &&
  mustHold44i3 "3b.counterAndNonInitialSlice" item3bOk &&
  mustHold44i3 "3c.isInitialMaterializeCoverage" item3cOk &&
  mustHold44i3 "3d.simultaneousPhaseOutAnd2hgInitAp" item3dOk &&
  mustHold44i3 "3.replay"
    (replayOk44i3 #[gHandCard, gInact1, gMatCtrl1, gPhSim1, gPhAfterP0Untap, gFullSent])

end Phase44Item3EventAlignment

section Phase44Item4EventAlignment

private def mustHold44i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase44Item4EventAlignment failed: {label}"

private def replayOk44i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g2 := afterDraw

  -- 4a. CR 602.2b `.crew` target-before-cost ordering, `.crew` + `CostPick` handoff,
  --     and `ProposedSpell.abilityIdx` duplicate `onceEachTurn` tracking:
  let targetedCrewDef : CardDef := {
    name := "P44i4 TargetedSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some (.fixed 3)
    toughness := some (.fixed 3)
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.pump 1 1 },
      { cost := CostSpec.ofItems #[.sacrifice (.exact 1) .self, .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 2 }
    ]
  }
  let gTc0 := addPermanent (addPermanent g2 targetedCrewDef p0 p0) bear p0 p0
  let skiffId := (gTc0.permanentsOf p0).find? (·.name == targetedCrewDef.name) |>.get!.id
  let skiffPilotId := (gTc0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gTcStep1 := mustApply gTc0 p0 (.activate skiffId 0)
  let targetsFirst := gTcStep1.pending == .chooseTargets p0
  let gTcStep2 := mustApply gTcStep1 p0 (.target (.permanent skiffPilotId))
  let crewSecond :=
    match gTcStep2.pending with
    | .resolutionChoice q (.crew _ vid 2) => q == p0 && vid == skiffId
    | _ => false
  let gTcStep3 := mustApply gTcStep2 p0 (.choosePermanents #[skiffPilotId])

  -- Crew + `sacrificeSource` runs `completeActivation` (`skiffId` sacrificed to graveyard):
  let gCrewSac1 := mustApply gTc0 p0 (.activate skiffId 1)
  let gCrewSac2 := mustApply gCrewSac1 p0 (.choosePermanents #[skiffPilotId])

  -- Duplicate `turnLimit? := some 1` abilities (`abDup` at idx 0 AND idx 1): activating idx 1 marks idx 1 ONLY:
  let abDup : ActivatedAbility := {
    cost := CostSpec.empty
    effect := Effect.gainLife 1
    turnLimit? := some 1
  }
  let dupOnceDef : CardDef := {
    name := "P44i4 DupOnceRelic"
    types := #[.artifact]
    activatedAbilities := #[abDup, abDup]
  }
  let gDup0 := addPermanent g2 dupOnceDef p0 p0
  let dupId := (gDup0.permanentsOf p0)[0]!.id
  let gDup1 := mustApply gDup0 p0 (.activate dupId 1)
  let dupObj1 := gDup1.object! dupId

  let item4aOk :=
    targetsFirst && crewSecond &&
    gTcStep3.stack.size == 1 && (gTcStep3.object! skiffPilotId).status.tapped &&
    gCrewSac2.stack.size == 1 &&
    (gCrewSac2.followMovedToZone? skiffId (· == .graveyard p0)).isSome &&
    gDup1.abilitiesActivatedThisTurn dupId == #[1] &&
    gDup1.canActivate p0 dupObj1 abDup (idx? := some 0) &&
    !gDup1.canActivate p0 dupObj1 abDup (idx? := some 1)

  -- 4b. Plain-`{T}` `manaSourcesForProposed` & `Agent` non-`{T}` source usability,
  --     plus `Agent.chooseActivate` / `defaultChoiceAction` tap-cost mana-source conflict prevention:
  let selfTapSacRelicDef : CardDef := {
    name := "P44i4 Bauble"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .sacrifice (.exact 1) .self], effect := Effect.abilityDraw 1 },
      ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])
    ]
  }
  let gBauble0 := addPermanent g2 selfTapSacRelicDef p0 p0
  let baubleId := (gBauble0.permanentsOf p0)[0]!.id
  let gBaubleProp := mustApply gBauble0 p0 (.activate baubleId 0)
  let baubleInManaSources :=
    (gBaubleProp.manaSourcesForProposed p0 gBaubleProp.proposedSpell.get!).any (fun (o, _) => o.id == baubleId)
  let agentTapsBauble :=
    match Agent.choose gBaubleProp p0 with
    | some (.tapForMana id .colorless) => id == baubleId
    | _ => false
  let gBaublePaid := mustApply (mustApply gBaubleProp p0 (.tapForMana baubleId .colorless)) p0 .pay

  let dork22Def : CardDef := {
    creature "P44i4 ElfDork" ManaCost.empty #["Elf", "Druid"] 2 2 with
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])]
  }
  let crew1ManaVehDef : CardDef := {
    name := "P44i4 ManaSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some (.fixed 4)
    toughness := some (.fixed 4)
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 2 }
    ]
  }
  -- With ONLY `dork22Def` (`{T}: Add {G}`, summoned prior turn via `addPermanent`) and NO other creature or land,
  -- `{1}, Crew 2` needs `dork22Def` BOTH for `{1}` mana AND for `Crew 2` -> `Agent` must NOT propose `.activate`!
  let gConflictOnly := (addPermanent (addPermanent g2 crew1ManaVehDef p0 p0) dork22Def p0 p0)
  let gConflictCombat := mustApply (mustApply gConflictOnly p0 .pass) p1 .pass
  let conflictAvoided :=
    match Agent.choose gConflictCombat p0 with
    | some (.activate _ _) => false
    | _ => true
  -- Adding a non-mana `bear` lets `Agent` tap `dork22Def` for `{G}` and `defaultChoiceAction` crew with `bear`!
  let gNoConflict0 := addPermanent gConflictOnly bear p0 p0
  let ncVehId := (gNoConflict0.permanentsOf p0).find? (·.name == crew1ManaVehDef.name) |>.get!.id
  let ncDorkId := (gNoConflict0.permanentsOf p0).find? (·.name == dork22Def.name) |>.get!.id
  let ncBearId := (gNoConflict0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gNc1 := mustApply gNoConflict0 p0 (.activate ncVehId 0)
  let gNc2 := mustApply gNc1 p0 (.tapForMana ncDorkId (.colored .green))
  let gNc3 := mustApply gNc2 p0 .pay
  let defaultPicksNonManaBear :=
    match gNc3.defaultChoiceAction p0 (.crew gNc3.proposedSpell.get!.spellId ncVehId 2) with
    | .choosePermanents ids => ids == #[ncBearId]
    | _ => false
  let gNc4 := mustApply gNc3 p0 (.choosePermanents #[ncBearId])

  let item4bOk :=
    baubleInManaSources && agentTapsBauble && gBaublePaid.stack.size == 1 &&
    conflictAvoided && defaultPicksNonManaBear && gNc4.stack.size == 1

  -- 4c. Non-cast `Event.castEventBound` (`0` on activated abilities, `.turnFaceUp`, and uncast permanents)
  --     and `Core.treasureManaSpent` requiring `g.wasCast`:
  let treasureTokDef : CardDef := {
    name := "Treasure"
    types := #[.artifact]
    subtypes := #["Treasure"]
    isToken := true
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self]
      effect := { Effect.addMana #[.colorless] with }
    }]
  }
  let morphDef : CardDef := { bear with name := "P44i4 MorphBear", keywords := #[.morph (CostSpec.ofGeneric 1)] }
  let gTrCast0 :=
    addPermanent (addPermanent (addPermanent g2 morphDef p0 p0) treasureTokDef p0 p0) selfTapSacRelicDef p0 p0
  let morphId := (gTrCast0.permanentsOf p0).find? (·.name == morphDef.name) |>.get!.id
  let trId := (gTrCast0.permanentsOf p0).find? (·.name == treasureTokDef.name) |>.get!.id
  let actRelicId := (gTrCast0.permanentsOf p0).find? (·.name == selfTapSacRelicDef.name) |>.get!.id
  let gMorphDown := setFaceDown gTrCast0 morphId true
  let morphObj := gMorphDown.object! morphId
  let morphTurnUpIdx :=
    ((gMorphDown.activatedAbilitiesOf morphObj).findIdx?
      (fun ab => ab.effect.body == .permanent (.turnFaceUp .this))).getD 0
  let gMorphProp := mustApply gMorphDown p0 (.activate morphId morphTurnUpIdx)
  let gMorphMana : Game :=
    match gMorphProp.activateManaAbility p0 trId 0 #[.colorless] with
    | .ok g => g
    | .error e => panic! e
  let gMorphTurnedUp := mustApply gMorphMana p0 .pay

  let gAbTr0 := addPermanent gTrCast0 treasureTokDef p0 p0
  let trId2 := ((gAbTr0.permanentsOf p0).filter (·.name == treasureTokDef.name)).back!.id
  let gAbProp := mustApply gAbTr0 p0 (.activate actRelicId 0)
  let abStackId := gAbProp.proposedSpell.get!.spellId
  let gAbMana : Game :=
    match gAbProp.activateManaAbility p0 trId2 0 #[.colorless] with
    | .ok g => g
    | .error e => panic! e
  let gAbPaid := mustApply gAbMana p0 .pay

  let item4cOk :=
    !(gMorphTurnedUp.object! morphId).status.faceDown &&
    GameEvent.manaSpentOn gMorphTurnedUp.events morphId == 0 &&
    !GameEvent.treasureManaSpentOn gMorphTurnedUp.events morphId &&
    !gMorphTurnedUp.treasureManaSpent morphId &&
    GameEvent.manaSpentOn gAbPaid.events abStackId == 0 &&
    !GameEvent.treasureManaSpentOn gAbPaid.events abStackId &&
    !gAbPaid.treasureManaSpent abStackId

  -- 4d. `tapForMana` conditional-land fallback, Layer-6 `copiedFromGy` under `!retainsPrintedAbilities`,
  --     `.elf` subtype mana restriction, and `putStunCounterOnSource` / `sacrificeAnotherCreatureOrArtifact` mana abilities:
  let condLandWithGrantDef : CardDef := {
    name := "P44i4 CondLanternLand"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored .blue]) (.const 1))
        (condition? := some ActivatedAbility.condEnteredThisTurnOrControlBasicLand),
      { cost := CostSpec.ofItems #[.tapSelf], effect := { Effect.addAnyColor with } }
    ]
  }
  let condLandOnlyDef : CardDef := {
    name := "P44i4 CondOnlyLand"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored .blue]) (.const 1))
        (condition? := some ActivatedAbility.condEnteredThisTurnOrControlBasicLand)
    ]
  }
  let gCond0 := quiet (addPermanent (addPermanent g2 condLandWithGrantDef p0 p0) condLandOnlyDef p0 p0)
  let condGrantId := (gCond0.permanentsOf p0).find? (·.name == condLandWithGrantDef.name) |>.get!.id
  let condOnlyId := (gCond0.permanentsOf p0).find? (·.name == condLandOnlyDef.name) |>.get!.id
  let gCondTappedBlue := mustApply gCond0 p0 (.tapForMana condGrantId (.colored .blue))
  let condOnlyFails := (gCond0.tapForMana p0 condOnlyId (.colored .blue)).toOption.isNone

  -- `!retainsPrintedAbilities` + Layer-6 `.copyActivatedFromGySubtype .elf`:
  let gGyCopy0 := insertObject (addPermanent g2 bear p0 p0) dork22Def p0 (.graveyard p0)
  let gyTargetId := (gGyCopy0.permanentsOf p0)[0]!.id
  let gGyCopy1 :=
    (gGyCopy0.createEffect (.layered (.objects #[gyTargetId]) (.abilities {} .all) .indefinite)
      (cause := some testCause)).createEffect
      (.layered (.objects #[gyTargetId]) (.abilities { staticAbilities := #[.copyActivatedFromGySubtype .elf] } .none) .indefinite)
      (cause := some testCause)
  let gGyCopiedTapped := mustApply gGyCopy1 p0 (.tapForMana gyTargetId (.colored .green))

  -- `.addAnyColorSpendOnlySubtype .elf`, `putStunCounterOnSource`, and `sacrificeAnotherCreatureOrArtifact`:
  let stunElfManaDef : CardDef := {
    name := "P44i4 StunElfRelic"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.tapSelf, .putCounters (.const 1) .stun .self]
        effect := { Effect.addAnyColorSpendOnlySubtype "Elf" with } },
      { cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))]
        effect := { Effect.addMana #[.colored .black, .colored .black] with } }
    ]
  }
  let gStunSac0 := addPermanent (addPermanent g2 stunElfManaDef p0 p0) bear p0 p0
  let stunRelicId := (gStunSac0.permanentsOf p0).find? (·.name == stunElfManaDef.name) |>.get!.id
  let sacFodderId := (gStunSac0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gAfterStunMana : Game :=
    match gStunSac0.activateManaAbility p0 stunRelicId 0 #[.colored .green] with
    | .ok g => g
    | .error e => panic! e
  let elfPool := (gAfterStunMana.player p0).manaPool
  let gAfterSacOtherMana : Game :=
    match gAfterStunMana.activateManaAbility p0 stunRelicId 1 #[.colored .black, .colored .black] #[sacFodderId] with
    | .ok g => g
    | .error e => panic! e

  -- Unrelated cost payment (`choiceCostPaid`) does not waive `sourceId` battlefield presence or control,
  -- and `tapForMana` rejects tapped, summoning-sick, unaffordable, or proposal-reserved abilities:
  let crewDiscSkiffDef : CardDef := {
    name := "P44i4 CrewDiscSkiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some (.fixed 3)
    toughness := some (.fixed 3)
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.discard (.exact 1) .hand, .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 2 }
    ]
  }
  let filterManaRelicDef : CardDef := {
    name := "P44i4 FilterRelic"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)]
        effect := { Effect.addAnyColor with } },
      { cost := CostSpec.ofItems #[.tapSelf], effect := Effect.gainLife 1 }
    ]
  }
  let gCrewDisc0 := addPermanent (addPermanent g2 crewDiscSkiffDef p0 p0) bear p0 p0
  let cdSkiffId := (gCrewDisc0.permanentsOf p0).find? (·.name == crewDiscSkiffDef.name) |>.get!.id
  let cdPilotId := (gCrewDisc0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let cdHandCardId := (gCrewDisc0.player p0).hand[0]!
  let gCrewAfterTap :=
    mustApply (mustApply gCrewDisc0 p0 (.activate cdSkiffId 0)) p0 (.choosePermanents #[cdPilotId])
  let gCrewBounced := (gCrewAfterTap.move cdSkiffId (.hand p0) none (cause := some testCause)).1
  let gCrewBouncedRev := mustApply gCrewBounced p0 (.choosePermanents #[cdHandCardId])
  let gCrewStolen :=
    gCrewAfterTap.createEffect
      (.layered (.objects #[cdSkiffId]) (.control p1) .indefinite)
      (cause := some testCause)
  let gCrewStolenRev := mustApply gCrewStolen p0 (.choosePermanents #[cdHandCardId])
  let gSickDork := addSickPermanent g2 dork22Def p0 p0
  let sickDorkId := (gSickDork.permanentsOf p0)[0]!.id
  let gFilter0 := addPermanent (addPermanent g2 filterManaRelicDef p0 p0) condLandWithGrantDef p0 p0
  let filterRelicId := (gFilter0.permanentsOf p0).find? (·.name == filterManaRelicDef.name) |>.get!.id
  let gTapProp :=
    let tapRelicDef : CardDef := {
      name := "P44i4 TapReservedRelic"
      types := #[.artifact]
      activatedAbilities := #[
        { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf], effect := Effect.gainLife 1 },
        ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])
      ]
    }
    let g0 := addPermanent g2 tapRelicDef p0 p0
    let rid := (g0.permanentsOf p0)[0]!.id
    (mustApply g0 p0 (.activate rid 0), rid)
  let borrowedRelicDef : CardDef := {
    name := "P44i4 BorrowedRelic"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)], effect := Effect.gainLife 1 }
    ]
  }
  let p2 : PlayerId := ⟨2⟩
  let gCtrlEx00 :=
    addPermanent
      (addPermanent (g2.change (.addPlayer { id := p2, name := "Liliana" })) treasureTokDef p0 p0)
      borrowedRelicDef p2 p1
  let ctrlTrId := (gCtrlEx00.permanentsOf p0).find? (·.name == treasureTokDef.name) |>.get!.id
  let borrowedId := (gCtrlEx00.permanentsOf p1).find? (·.name == borrowedRelicDef.name) |>.get!.id
  let gCtrlEx0 :=
    (gCtrlEx00.createEffect
      (.layered (.objects #[borrowedId]) (.control p0) (.whileSourceOnBattlefield ctrlTrId))
      (cause := some testCause)).concede p1
  let gCtrlProp := mustApply gCtrlEx0 p0 (.activate borrowedId 0)
  let gCtrlAfterSacMana : Game :=
    match gCtrlProp.activateManaAbility p0 ctrlTrId 0 #[.colorless] with
    | .ok g => g
    | .error e => panic! e
  let gCtrlRev := mustApply gCtrlAfterSacMana p0 .pay

  let item4dOk :=
    (gCondTappedBlue.player p0).manaPool.blue == 1 &&
    condOnlyFails &&
    !gGyCopy1.retainsPrintedAbilities (gGyCopy1.object! gyTargetId) &&
    (gGyCopiedTapped.player p0).manaPool.green == 1 &&
    gAfterStunMana.stack.isEmpty &&
    (gAfterStunMana.object! stunRelicId).status.counterCount .stun == 1 &&
    elfPool.canPay (ManaCost.ofGeneric 1) (spend := ManaSpend.forSpell #[.creature] #[] #[.elf]) &&
    !elfPool.canPay (ManaCost.ofGeneric 1) &&
    gAfterSacOtherMana.stack.isEmpty &&
    (gAfterSacOtherMana.followMovedToZone? sacFodderId (· == .graveyard p0)).isSome &&
    (gAfterSacOtherMana.player p0).manaPool.black == 2 &&
    gCrewAfterTap.proposedSpell.any (·.choiceCostPaid) &&
    !gCrewBounced.sourceStillPayable (gCrewBounced.proposedSpell.get!) &&
    (gCrewBounced.payActivationExtraCosts p0 cdSkiffId false false 0 false
      (gCrewBounced.proposedSpell.get!.activation)).isOk == false &&
    gCrewBouncedRev.proposedSpell.isNone && gCrewBouncedRev.stack.isEmpty &&
    !gCrewStolen.sourceStillPayable (gCrewStolen.proposedSpell.get!) &&
    (gCrewStolen.payActivationExtraCosts p0 cdSkiffId false false 0 false
      (gCrewStolen.proposedSpell.get!.activation)).isOk == false &&
    gCrewStolenRev.proposedSpell.isNone && gCrewStolenRev.stack.isEmpty &&
    !gCtrlAfterSacMana.sourceRemovedByCostSince p0 borrowedId 0 &&
    !gCtrlAfterSacMana.sourceStillPayable (gCtrlAfterSacMana.proposedSpell.get!) &&
    (gCtrlAfterSacMana.payActivationExtraCosts p0 borrowedId false false 0 false
      (gCtrlAfterSacMana.proposedSpell.get!.activation)).isOk == false &&
    gCtrlRev.proposedSpell.isNone && gCtrlRev.stack.isEmpty &&
    (gCondTappedBlue.tapForMana p0 condGrantId (.colored .blue)).isOk == false &&
    (gSickDork.tapForMana p0 sickDorkId (.colored .green)).isOk == false &&
    (gFilter0.tapForMana p0 filterRelicId (.colored .blue)).isOk == false &&
    (gTapProp.1.tapForMana p0 gTapProp.2 .colorless).isOk == false

  mustHold44i4 "4a.crewOrderAndAbilityIdx" item4aOk &&
  mustHold44i4 "4b.plainTapAndAgentConflict" item4bOk &&
  mustHold44i4 "4c.nonCastManaSpentBounds" item4cOk &&
  mustHold44i4 "4d.manaAbilityParity" item4dOk &&
  mustHold44i4 "4.replay"
    (replayOk44i4 #[gTcStep3, gCrewSac2, gDup1, gBaublePaid, gNc4,
      gMorphTurnedUp, gAbPaid, gGyCopiedTapped, gAfterStunMana, gAfterSacOtherMana,
      gCrewBouncedRev, gCrewStolenRev, gCtrlRev])

end Phase44Item4EventAlignment

end Mtg.Engine.EventTests
