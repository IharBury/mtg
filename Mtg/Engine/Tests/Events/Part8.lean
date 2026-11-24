import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-! ### Phase 39 Item 1: Two-stage `revMap`/`liveObjMap` + `after.id == before.id` `ZoneEvent.moved` remapping, one-shot `allocDelayedCause` `EffectId` collision remapping, `reconcilePostReplayDepartures` + departed `stepEvent` guards, and quiet `finishOpenBatch` / `wasGameOver` vs `wasSuppressed` invariants -/
section Phase39Item1EventAlignment

private def mustHold39i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase39Item1EventAlignment failed: {label}"

private def replayOk39i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let p4 : PlayerId := ⟨4⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let cageDef : CardDef := { name := "P39i1 Cage", types := #[.enchantment] }
  let altarDef : CardDef := { name := "P39i1 Altar", types := #[.artifact] }
  let leyADef : CardDef := { name := "P39i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P39i1 LeyB", types := #[.enchantment] }
  let tokDef : CardDef := { bear with name := "P39i1 Token", isToken := true }

  -- 1a & 1b. Two-stage `revMap` / `liveObjMap` + same-id `ZoneEvent.moved` (`after.id == before.id`) remapping,
  --          AND one-shot `allocDelayedCause` `EffectId` collision remapping alongside `max`-clamped `createEffect`
  --          `bumpId?` in `Core.replayKeptStreamCore`:
  let gColBase0 :=
    insertObject
      (insertObject
        (addPermanent
          (addPermanent (addPermanent (addPermanent g4 cageDef p1 p1) altarDef p2 p2) bear p0 p0)
          bear p3 p3)
        bear p0 (.library p0))
      bear p0 (.hand p0)
  let p1Cage := (gColBase0.permanentsOf p1)[0]!
  let p2Altar := (gColBase0.permanentsOf p2)[0]!
  let p0Victim := (gColBase0.permanentsOf p0)[0]!
  let p3CloneTarget := (gColBase0.permanentsOf p3)[0]!
  let p0HandCard := (gColBase0.player p0).hand.back!
  let gCol0 :=
    ((gColBase0.exileUntilSourceLeaves (some p1Cage.id) p0Victim (cause := some testCause)).phaseOut
      (gColBase0.object! p1Cage.id) (cause := some testCause)).createEffect
      (.control p2Altar.id p0) (cause := some testCause)
  let exVictimId := (gCol0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!.id
  let copyExId : ReplacementId := {
    kind := .entersAsCopyCreatureUntilEot p3CloneTarget.id
    object := some exVictimId
  }
  let gColCkpt0 :=
    (gCol0.createEffect
      (.replacement {
        id := copyExId, source := some p3CloneTarget.id, controller := some p0, affectedPlayer := p0,
        kind := .entersAsCopyCreatureUntilEot exVictimId p3CloneTarget.id }) (cause := some testCause)).change
      .saveProposalCheckpoint
  let (gCol1, colPropAb) := gColCkpt0.putStackAbility p2Altar p0 (abilityEffect := some (Effect.gainLife 1))
  let colProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := colPropAb.id, original := colPropAb
    originalSnapshot := gCol1.snapshot colPropAb, kind := .activatedAbility, sourceId := some p2Altar.id
  }
  let gCol2 := gCol1.changes #[.proposedSpell (some colProp), .pending (.chooseX p0)]
  let depCause := some (EventCause.gameRule .playerLeftGame)
  let gColAfterB1 :=
    gCol2.withBatchCore depCause fun g =>
      let g := g.record (GameEvent.playerLeftGame g.turnNumber p1 (cause := depCause))
      g.objectLeavesTheGame (g.object! p1Cage.id) p1
  let gColPreB2 := gColAfterB1.change .clearQueuedLinkedExile
  let gColAfterB2 :=
    gColPreB2.withBatch (some testCause) fun g =>
      -- Move `p0HandCard` into `.library p0` (receiving the exact `ObjectId` slot `M` that `exVictimId`'s live return
      -- will claim during replay, so `liveObjMap` maps `M -> M'`), then emit a same-id `ZoneEvent.moved`
      -- (`after.id == before.id == M`, `.library p0 -> .library p0`), PLUS a token creation `tokDef` whose raw id
      -- collides with `M'` (so `revMap` maps `M' -> M''`, proving single-stage lookup does NOT transitively chain
      -- `M -> M' -> M''`!).
      let (g, libMovedId) := g.move p0HandCard (.library p0) none (cause := some testCause)
      let libSnap := g.snapshot (g.object! libMovedId)
      let g := g.record (GameEvent.moved g.turnNumber libSnap (.library p0) (.library p0)
        (after := some libSnap) (cause := testCause))
      let (g, createdTok) := g.createOneToken p0 tokDef (cause := some testCause)
      -- Allocate a one-shot `EffectId` via `allocDelayedCause` (which collides with `B_1`'s live `.copy` `EffectId`!),
      -- emit a `RulesEvent` carrying `EventCause.oneShotEffect`, and create a subsequent continuous effect via `createEffect`:
      let (g, oneShotCause) := g.allocDelayedCause (some p0) (some createdTok.id)
      let g := g.gainLife p0 2 (cause := some oneShotCause)
      g.createEffect (.layered (.objects #[createdTok.id]) (.ptModify 2 2) .untilEndOfTurn) (cause := some oneShotCause)
  let gColReversed := mustApply gColAfterB2 p2 .concede
  let allObjIds := gColReversed.objects.map (·.id)
  let allEffIds := gColReversed.activeEffects.map Prod.fst
  let oneShotEids : Array EffectId :=
    gColReversed.events.filterMap fun ev =>
      match ev.change, ev.cause? with
      | .rules (.life (.gained q 2)), some (.oneShotEffect (some eid) _ _) =>
        if q == p0 then some eid else none
      | _, _ => none
  let remappedLibId := gColReversed.followMoved p0HandCard
  let keptTokens :=
    gColReversed.permanentsOf p0 |>.filter (fun o => o.printed.isToken && o.name == tokDef.name)
  let returnedClones :=
    gColReversed.permanentsOf p0 |>.filter (fun o => !o.printed.isToken && o.id != p0Victim.id)
  let twoStageAndOneShotOk :=
    gColReversed.proposedSpell.isNone &&
    allObjIds.toList.eraseDups.length == allObjIds.size &&
    allEffIds.toList.eraseDups.length == allEffIds.size &&
    returnedClones.size == 1 &&
    keptTokens.size == 1 &&
    gColReversed.power keptTokens[0]! == 4 &&
    (gColReversed.findObject? remappedLibId).any (·.zone == .library p0) &&
    remappedLibId != keptTokens[0]!.id &&
    oneShotEids.size == 1 &&
    !allEffIds.contains oneShotEids[0]! &&
    allEffIds.all (fun eid => eid.raw < gColReversed.nextEffectId) &&
    oneShotEids[0]!.raw < gColReversed.nextEffectId

  -- 1c. Synchronous `reconcilePostReplayDepartures` (including teammate-aware `.controlsPlayer` expiry vs shared-team
  --     retention and CR 800.4c orphan exile) AND departed-player `stepEvent` guards:
  let g5 :=
    ((afterDraw.change (.addPlayer { id := p2, name := "Liliana", teammate := some p4 })).change
      (.addPlayer { id := p3, name := "Jace" })).change
      (.addPlayer { id := p4, name := "Chandra", teammate := some p2 })
  let gSyncBase := addPermanent (addPermanent g5 altarDef p3 p3) bear p0 p1
  let syncAltar := (gSyncBase.permanentsOf p3)[0]!
  let syncOrphan := (gSyncBase.permanentsOf p1)[0]!
  -- `p1` has a solo `.controlsPlayer p0 false` effect (should expire when `p1` departs), while `p0` has a shared-team
  -- `.controlsPlayer p4 false` effect (living teammate `p4` keeps it active when `p4`'s teammate `p2` departs!):
  let gSyncCkpt :=
    ((((gSyncBase.createEffect (.playerRule p1 (.controlsPlayer p0 false) .indefinite)
      (cause := some testCause)).createEffect
      (.playerRule p0 (.controlsPlayer p4 false) .indefinite)
      (cause := some testCause)).createEffect
      (.control syncAltar.id p0) (cause := some testCause)).createEffect
      (.layered (.objects #[syncOrphan.id]) (.control p3) .indefinite) (cause := some testCause)).change
      .saveProposalCheckpoint
  -- Proposal-time control effect (`p0` controls `syncOrphan`) keeps `syncOrphan` on `.battlefield` when `p1` concedes live,
  -- and is undone on reversal so `p3`'s departure leaves `syncOrphan` reverting to departed `p1` for `reconcilePostReplayDepartures`!
  let gSyncAct := gSyncCkpt.createEffect (.layered (.objects #[syncOrphan.id]) (.control p0) .indefinite) (cause := some testCause)
  let (gSync1, syncAb) := gSyncAct.putStackAbility syncAltar p0 (abilityEffect := some (Effect.gainLife 1))
  let syncProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := syncAb.id, original := syncAb
    originalSnapshot := gSync1.snapshot syncAb, kind := .activatedAbility, sourceId := some syncAltar.id
  }
  let gSyncReady := gSync1.changes #[.proposedSpell (some syncProp), .pending (.chooseX p0)]
  -- `p1` departs; then in `p2`'s departure batch a stale `PlayerEvent.manaAdded` on already-departed `p1` is recorded
  -- (must be skipped by `stepEvent`!); then `p3` concedes, aborting `syncProp` and running synchronous `reconcilePostReplayDepartures`!
  let gSyncAfterP1 := mustApply gSyncReady p1 .concede
  let gSyncAfterLeaves :=
    gSyncAfterP1.withBatch (some (.gameRule .playerLeftGame)) fun g =>
      let g := g.record (GameEvent.playerLeftGame g.turnNumber p2 (cause := some (.gameRule .playerLeftGame)))
      g.record (GameEvent.manaAdded g.turnNumber p1 #[{ mana := .colorless }] (cause := some (.gameRule .playerLeftGame)))
  let gSyncDone := mustApply gSyncAfterLeaves p3 .concede
  let hasSoloCtrlP1 :=
    gSyncDone.activeEffects.any (fun (_, e) =>
      match e with | .playerRule q (.controlsPlayer _ _) _ => q == p1 | _ => false)
  let hasTeamCtrlP4 :=
    gSyncDone.activeEffects.any (fun (_, e) =>
      match e with | .playerRule q (.controlsPlayer tgt _) _ => q == p0 && tgt == p4 | _ => false)
  let syncReconcileAndGuardsOk :=
    !hasSoloCtrlP1 &&
    hasTeamCtrlP4 &&
    (gSyncDone.player p1).manaPool.total == 0 &&
    (gSyncDone.followMovedToZone? syncOrphan.id (· == .exile)).isSome

  -- 1d. Quiet `finishOpenBatch` (`suppressInteractive`) AND split `wasGameOver` vs `wasSuppressed`
  --     (`g.suppressInteractiveReplay == true` while `!g.over` suppresses interactive replacement prompts during
  --     replay yet STILL restores `ckpt.pending` and `ckptOrigCont?`!):
  let gSup0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent (addPermanent g4 cageDef p1 p1) altarDef p2 p2) bear p0 p0)
          leyADef p0 p0)
        leyBDef p0 p0)
      bear p0 .exile
  let supCage := (gSup0.permanentsOf p1)[0]!
  let supAltar := (gSup0.permanentsOf p2)[0]!
  let supBear := (gSup0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let supLeyA := (gSup0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let supLeyB := (gSup0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let supExCard := (gSup0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!
  let supRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some supLeyA, counterKind := some .plusOnePlusOne }
  let supRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some supLeyB, counterKind := some .plusOnePlusOne }
  let supOuterPrompt : Pending := .mayCastExiledElseDamage p0 supExCard.id 0 none
  let supOrigCont : PendingReplacement := .gainLife p0 5 (some testCause)
  let supLifeBefore := (gSup0.player p0).life
  let gSupCkpt :=
    (((((gSup0.exileUntilSourceLeaves (some supCage.id) supBear (cause := some testCause)).createEffect
      (.control supCage.id p0) (cause := some testCause)).createEffect
      (.control supAltar.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := supRidA, source := some supLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := supRidB, source := some supLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pending supOuterPrompt,
      .pendingReplacement (some supOrigCont),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement supOrigCont,
      .pendingReplacement none ]
  let gSupAct0 := gSupCkpt.change (.beginProposalAction .costAction)
  let (gSupAct1, supAb) := gSupAct0.putStackAbility supAltar p0 (abilityEffect := some (Effect.gainLife 1))
  let supSacCause := some (EventCause.costPayment .sacrifice p0 (some supAb.id))
  let gSupSac :=
    gSupAct1.withBatch supSacCause fun g =>
      g.sacrificeToGraveyard (g.object! supCage.id) "sac" (cause := supSacCause)
  let gSupRet := mustApply gSupSac p0 (.chooseReplacement supRidA)
  let supProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := supAb.id, original := supAb
    originalSnapshot := gSupRet.snapshot supAb, kind := .activatedAbility
    sourceId := some supAltar.id, resolutionCast := true
  }
  let gSupReady :=
    (gSupRet.changes #[.proposedSpell (some supProp), .pending (.activateManaAbilities p0)]).change .endProposalAction
  let gSupAfterP1 :=
    (mustApply gSupReady p1 .concede).change
      (.pushContinuationFrame {
        pendingReplacement := some (.continueCheckpointReplay #[] #[] #[] #[] #[] 0 true #[]) })
  -- Reversing under `suppressInteractiveReplay == true` (while `!g.over`) suppresses `supRidA`/`supRidB` on `supBear`'s
  -- CR 610.3 return, clears `suppressInteractiveReplay` back to checkpoint's `false`, AND restores `supOuterPrompt` + `supOrigCont`!
  let gSupReversed := mustApply gSupAfterP1 p0 .pay
  let gSupDrained := (mustApply gSupReversed p0 .decline).drainPendingContinuations
  -- Queued `.runPostCastCleanup` continuation is also skipped when `g.suppressInteractiveReplay` holds (`!g.over`):
  let gSupCleanupQuiet :=
    (gSup0.change (.pushContinuationFrame {
      pendingReplacement := some (.continueCheckpointReplay #[] #[] #[] #[] #[] 0 true #[])
    })).resumePendingReplacement (.runPostCastCleanup (.cascadeBottom p0 supExCard.id #[]))
  let wasSuppressedSplitOk :=
    gSupAfterP1.suppressInteractiveReplay &&
    !gSupReversed.over &&
    !gSupReversed.suppressInteractiveReplay &&
    (gSupReversed.permanentsOf p0).any (·.name == bear.name) &&
    gSupReversed.pending == supOuterPrompt &&
    (gSupDrained.player p0).life == supLifeBefore + 5 &&
    gSupCleanupQuiet.suppressInteractiveReplay &&
    gSupCleanupQuiet.afterRandom == .none &&
    (gSupCleanupQuiet.findObject? supExCard.id).any (·.zone == .exile)

  mustHold39i1 "1ab.twoStageAndOneShot" twoStageAndOneShotOk &&
  mustHold39i1 "1c.syncReconcileAndGuards" syncReconcileAndGuardsOk &&
  mustHold39i1 "1d.wasSuppressedSplit" wasSuppressedSplitOk &&
  mustHold39i1 "1.replay"
    (replayOk39i1 #[gColReversed, gSyncDone, gSupReversed, gSupDrained, gSupCleanupQuiet])

end Phase39Item1EventAlignment

/-! ### Phase 39 Item 2: Unstamped-`.engine` `ckptPendingReplacementUntouchedBeforeLeave`, `.resolveRandom` `restoreCkptPending?` ordering & `resumeContinuation == false` draining, and cross-batch `preBatchLegendSnapshotValid` / `validLegendChoiceIds` -/
section Phase39Item2EventAlignment

private def mustHold39i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase39Item2EventAlignment failed: {label}"

private def replayOk39i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let auraDef : CardDef := { name := "P39i2 Aura", types := #[.enchantment] }
  let morphDef : CardDef := {
    creature "P39i2 Morph" ManaCost.empty #["Human"] 2 2 with keywords := #[.morph (CostSpec.ofGeneric 1)]
  }

  -- 2a. Unstamped-`.engine` `ckptPendingReplacementUntouchedBeforeLeave`:
  --     When `ckptOrigCont?` (`+6` life) was ALREADY consumed via an unstamped `.engine` `.pendingReplacement none`
  --     before `p2` left the game, reversing across:
  --     (i) `Leaving.rewindAbortedProposalOnLeave`,
  --     (ii) `Decisions.reverseOrResumePopped`, and
  --     (iii) standalone `Casting.reverseProposedSpellCore?`
  --     must NOT re-run the already-consumed `ckptOrigCont?`!
  let gBase :=
    addPermanent (addPermanent (addPermanent g4 bear p3 p3) auraDef p2 p2) morphDef p0 p0
  let p3Bear := (gBase.permanentsOf p3)[0]!
  let p2Aura := (gBase.permanentsOf p2)[0]!
  let morphId := (gBase.permanentsOf p0).find? (·.name == morphDef.name) |>.get!.id
  let gBaseFd := setFaceDown gBase morphId true
  let morphObj := gBaseFd.object! morphId
  let baseLife := (gBaseFd.player p0).life
  let origGain6 : PendingReplacement := .gainLife p0 6 (some testCause)
  -- `ckpt` saves `pendingReplacement := some origGain6`, and then `origGain6` is consumed via an UNSTAMPED
  -- `.pendingReplacement none` (plus `+6` life) BEFORE any player leaves!
  let gConsumedCkpt :=
    ((gBaseFd.createEffect
      (.layered (.objects #[p3Bear.id]) (.control p0) (.whileSourceOnBattlefield p2Aura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some origGain6),
      .saveProposalCheckpoint,
      .pendingReplacement none,
      .popContinuationFrame ]).gainLife p0 6 (cause := some testCause)

  -- Path (i): `Leaving.rewindAbortedProposalOnLeave` (`p2` concedes in a batch, aborting `ab1`):
  let (gC1, ab1) := gConsumedCkpt.putStackAbility p3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let prop1 : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := ab1.id, original := ab1
    originalSnapshot := gC1.snapshot ab1, kind := .activatedAbility, sourceId := some p3Bear.id
  }
  let gLeaveConsumed := mustApply (gC1.changes #[.proposedSpell (some prop1), .pending (.chooseX p0)]) p2 .concede

  -- Path (ii): `Decisions.reverseOrResumePopped`:
  let prop2 : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := morphObj.id, original := morphObj
    originalSnapshot := gConsumedCkpt.snapshot morphObj, kind := .turnFaceUp, sourceId := some morphObj.id
  }
  let gPopConsumed :=
    (((gConsumedCkpt.record (GameEvent.playerLeftGame gConsumedCkpt.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).createEffect
      (.control morphObj.id p2) (cause := some testCause)).change
      (.proposedSpell (some prop2))).resumePendingReplacement
      (.restorePending (.activateManaAbilities p0) false none #[p1] none)
      |>.drainPendingContinuations

  -- Path (iii): Standalone `Casting.reverseProposedSpellCore?`:
  let gStandAfterP1 :=
    mustApply (gConsumedCkpt.changes #[.proposedSpell (some prop2), .pending (.activateManaAbilities p0)]) p1 .concede
  let gStandConsumed := mustApply gStandAfterP1 p0 .pay

  -- Conversely, when `ckptOrigCont?` (`origGain6`) was NOT moved to `outerPendingReplacements` (`ckptMovedToOuter == false`)
  -- and remained untouched in `g.pendingReplacement` until `playerLeavesGameCore` emitted unstamped `.pendingReplacement none`
  -- immediately before batched `PlayerEvent.leftGame`, `ckptPendingReplacementUntouchedBeforeLeave` returns `true` and preserves `origGain6`:
  let gUntouchedCkpt :=
    (gBaseFd.createEffect
      (.layered (.objects #[p3Bear.id]) (.control p0) (.whileSourceOnBattlefield p2Aura.id))
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some origGain6),
      .saveProposalCheckpoint ]
  let (gU1, uAb1) := gUntouchedCkpt.putStackAbility p3Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let uProp1 : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := uAb1.id, original := uAb1
    originalSnapshot := gU1.snapshot uAb1, kind := .activatedAbility, sourceId := some p3Bear.id, resolutionCast := true
  }
  let gLeaveUntouched :=
    (mustApply (gU1.changes #[.proposedSpell (some uProp1), .pending (.chooseX p0)]) p2 .concede).drainPendingContinuations
  let uProp2 : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := morphObj.id, original := morphObj
    originalSnapshot := gUntouchedCkpt.snapshot morphObj, kind := .turnFaceUp, sourceId := some morphObj.id, resolutionCast := true
  }
  let gStandUntouchedAfterP1 :=
    mustApply (gUntouchedCkpt.changes #[.proposedSpell (some uProp2), .pending (.activateManaAbilities p0)]) p1 .concede
  let gStandUntouched := (mustApply gStandUntouchedAfterP1 p0 .pay).drainPendingContinuations

  let consumedNotRerunOk :=
    (gLeaveConsumed.player p0).life == baseLife &&
    (gPopConsumed.player p0).life == baseLife &&
    (gStandConsumed.player p0).life == baseLife &&
    (gLeaveUntouched.player p0).life == baseLife + 6 &&
    (gStandUntouched.player p0).life == baseLife + 6

  -- 2b. (i) `Decisions.reverseOrResumePopped` `.resolveRandom` `restoreCkptPending?`-before-`restored?` ordering, and
  --     (ii) `Casting.reverseProposedSpellCore?` `resumeContinuation := false` draining reconciled `.endControlExileLoop`:
  let origGain5 : PendingReplacement := .gainLife p0 5 (some testCause)
  let gRndCkpt :=
    gBaseFd.changes #[
      .pushContinuationFrame {},
      .pending (.resolveRandom (.shuffleLibrary p1)),
      .pendingReplacement (some origGain5),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement origGain5,
      .pendingReplacement none ]
  let gRndPostLeave :=
    (((gRndCkpt.record (GameEvent.playerLeftGame gRndCkpt.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).createEffect
      (.control morphObj.id p2) (cause := some testCause)).change
      (.proposedSpell (some prop2))).resumePendingReplacement
      (.restorePending (.activateManaAbilities p0) false none #[p1] none)
      |>.drainPendingContinuations
  -- (ii) `resumeContinuation := false` with `reconcilePostReplayDepartures` queuing `.endControlExileLoop`:
  let gDrainBase := addPermanent gBaseFd bear p0 p1
  let p1Orph := (gDrainBase.permanentsOf p1)[0]!
  let gDrainCkpt :=
    (gDrainBase.createEffect (.layered (.objects #[p1Orph.id]) (.control p1) .indefinite)
      (cause := some testCause)).change .saveProposalCheckpoint
  let gDrainPostLeave :=
    (gDrainCkpt.record (GameEvent.playerLeftGame gDrainCkpt.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).changes #[
      .proposedSpell (some prop2),
      .pending (.activateManaAbilities p0) ]
  let gDrainRev := gDrainPostLeave.reverseProposedSpell (resumeContinuation := false)
  let randomOrderAndDrainOk :=
    gRndPostLeave.pending == Pending.none &&
    (gRndPostLeave.player p0).life == baseLife + 5 &&
    gDrainRev.pendingReplacement.isNone &&
    (gDrainRev.followMovedToZone? p1Orph.id (· == .exile)).isSome

  -- 2c. Cross-batch `preBatchLegendSnapshotValid` / `validLegendChoiceIds` re-validation when a `.rules` change
  --     occurs AFTER `.pending (.chooseLegend ..)` while `g.currentBatch.isSome` is STILL `true`:
  let gLeg0 := addPermanent (addPermanent g4 bear p0 p0) bear p0 p0
  let legIds := (gLeg0.permanentsOf p0).map (·.id)
  let gLegWithEff :=
    gLeg0.createEffect (.layered (.objects legIds) (.types .add #[] #[] #[.legendary]) .indefinite)
      (cause := some testCause)
  let legEid := gLegWithEff.activeEffects.back!.1
  -- Open a paused batch (`openBatchEffects` captures `legEid`!) and open `.chooseLegend p0 bear.name legIds`:
  let pauseBid : BatchId := ⟨gLegWithEff.nextBatchId⟩
  let pauseStartIdx := gLegWithEff.events.size
  let gInBatch0 :=
    gLegWithEff.change (.pauseBatch pauseBid (some testCause)
      gLegWithEff.objects gLegWithEff.players gLegWithEff.activeEffects gLegWithEff.pending gLegWithEff.stack)
  let gInBatchPrompt := gInBatch0.change (.pending (.chooseLegend p0 bear.name legIds))
  let validBeforeExpiry :=
    gInBatchPrompt.preBatchLegendSnapshotValid &&
    (gInBatchPrompt.validLegendChoiceIds p0 bear.name legIds).size == 2
  -- Now expire `legEid` INSIDE the open batch (`currentBatch.isSome == true`, `openBatchEffects` still has `legEid`!):
  let gInBatchExpired := gInBatchPrompt.expireEffectById legEid (cause := some testCause)
  let invalidAfterExpiry :=
    !gInBatchExpired.preBatchLegendSnapshotValid &&
    (gInBatchExpired.validLegendChoiceIds p0 bear.name legIds).isEmpty &&
    !gInBatchExpired.batchPausePromptValid gInBatchExpired.pending
  let (_, redirInBatch) := gInBatchExpired.redirectPendingAfterLeave p3 (pending := gInBatchExpired.pending)
  let (gSbaInBatch, _) := gInBatchExpired.checkSBACounted
  let gKeepInBatch :=
    (match gInBatchExpired.keepLegend p0 legIds[0]! with | .ok g => g | .error e => panic! e)
  -- Close the open batch on `gSbaInBatch` / `gKeepInBatch` for clean end-of-test state:
  let gSbaClosed :=
    match gSbaInBatch.currentBatch with
    | some (b, _) => gSbaInBatch.finishOpenBatch b pauseStartIdx
    | none => gSbaInBatch
  let gKeepClosed :=
    match gKeepInBatch.currentBatch with
    | some (b, _) => gKeepInBatch.finishOpenBatch b pauseStartIdx
    | none => gKeepInBatch
  -- `nextQueuedPendingOnResume` / `continuationGrantsPriority` (`finishAndGrantPriority` `alreadyGrants`)
  -- also uses `validLegendChoiceIds` while `currentBatch.isSome` (`!preBatchLegendSnapshotValid`),
  -- inspecting `popOuter` when `liveIds.size < 2`:
  let pauseBid := (gInBatchExpired.currentBatch.get!).1
  let gPred0 :=
    gInBatchExpired.changes #[
      .pending .none,
      .priority p1,
      .pushContinuationFrame {},
      .pushOuterPendingReplacement
        (.restorePending (.chooseMode p2) false none #[p3] none),
      .pendingReplacement
        (some (.seq (.closeBatch pauseBid pauseStartIdx)
          (.seq (.restorePending (.chooseLegend p0 bear.name legIds) true none #[] none)
            (.finishTurnFaceUp p2 ⟨999998⟩ true)))) ]
  let gPredDone := gPred0.finishAndGrantPriority p0
  let crossBatchLegendOk :=
    validBeforeExpiry &&
    invalidAfterExpiry &&
    redirInBatch == Pending.none &&
    gSbaClosed.pending == Pending.none &&
    gKeepClosed.pending == Pending.none &&
    (gKeepClosed.permanentsOf p0).size == 2 &&
    gPredDone.currentBatch.isNone &&
    gPredDone.priority == p1

  mustHold39i2 "2a.consumedNotRerun" consumedNotRerunOk &&
  mustHold39i2 "2b.randomOrderAndDrain" randomOrderAndDrainOk &&
  mustHold39i2 "2c.crossBatchLegend" crossBatchLegendOk &&
  mustHold39i2 "2.replay"
    (replayOk39i2 #[gLeaveConsumed, gPopConsumed, gStandConsumed, gLeaveUntouched, gStandUntouched,
      gRndPostLeave, gDrainRev, gSbaClosed, gKeepClosed, gPredDone])

end Phase39Item2EventAlignment

/-! ### Phase 39 Item 3: Counter-put control reconciliation, simultaneous `endControlEffectsSimultaneously`, CR 610.3 `linkedExile` flushes, post-phase-out Layer 1/2 scopes (CR 611.2c / 702.26b), CR 702.26n departed-controller phase-in, and pause-safe `.untap` `untapStepAfterPhaseIn` -/
section Phase39Item3EventAlignment

private def mustHold39i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase39Item3EventAlignment failed: {label}"

private def replayOk39i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let hostDef : CardDef := { name := "P39i3 Host", types := #[.artifact] }
  let sagaDef : CardDef := {
    name := "P39i3 Saga", types := #[.enchantment], subtypes := #["Saga"]
    triggeredAbilities := #[TriggeredAbility.sagaChapter 2 (Effect.gainLife 1)]
  }
  let cageDef : CardDef := { name := "P39i3 Cage", types := #[.enchantment] }
  let leyADef : CardDef := { name := "P39i3 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P39i3 LeyB", types := #[.enchantment] }

  -- 3a. (i) `0 -> n'` `.whileSourceHasCounter` control reconciliation across `addFinalityTo`,
  --         `addIndestructibleCounter`, `addLifelinkCounter`, `addBurdenCounter`, `addCounters`,
  --         and `Triggers.addLoreCounters`, plus `FraAbilities` `.putCauseCountersOnSource` safety
  --         when `putCountersExceptPlusOne` exiles `o` via CR 800.4c before `st.plusOnePlusOne > 0` runs:
  let gCntBase := addPermanent (addPermanent (addPermanent g4 bear p2 p2) hostDef p0 p0) sagaDef p0 p0
  let cntAtk := (gCntBase.permanentsOf p2)[0]!
  let cntHost := (gCntBase.permanentsOf p0).find? (·.name == hostDef.name) |>.get!
  let cntSaga := (gCntBase.permanentsOf p0).find? (·.name == sagaDef.name) |>.get!
  let prepCounterSteal (srcId : ObjectId) (k : CounterKind) : Game :=
    (gCntBase.createEffect
      (.layered (.objects #[cntAtk.id]) (.control p0) (.whileSourceHasCounter srcId k))
      (cause := some testCause)).record
      (GameEvent.becameAttacking gCntBase.turnNumber (gCntBase.snapshot cntAtk) (.player p0) (cause := testCause))
  let gFin := (prepCounterSteal cntHost.id .finality).addFinalityTo cntHost 1 (cause := some testCause)
  let gInd := (prepCounterSteal cntHost.id .indestructible).addIndestructibleCounter cntHost 1 (cause := some testCause)
  let gLife := (prepCounterSteal cntHost.id .lifelink).addLifelinkCounter cntHost 1 (cause := some testCause)
  let gBur := (prepCounterSteal cntHost.id .burden).addBurdenCounter cntHost 1 (cause := some testCause)
  let gShield := (prepCounterSteal cntHost.id .shield).addCounters cntHost .shield 1 (cause := some testCause)
  let gLore := (prepCounterSteal cntSaga.id .lore).addLoreCounters cntSaga 1 (cause := some testCause)
  let stoleAndRemoved (g : Game) : Bool :=
    g.controllerOf (g.object! cntAtk.id) == some p0 && !(g.object! cntAtk.id).status.attacking
  let flyerCopyEarly : CardDef := { bear with name := "P39i3 FraFlyer", keywords := #[Keyword.flying] }
  let gFra0 := addPermanent g4 bear p3 p1
  let fraSrc := (gFra0.permanentsOf p1)[0]!
  let gFra1 :=
    (((gFra0.createEffect (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) .indefinite)
      (cause := some testCause)).concede p1).createEffect
      (.layered (.objects #[fraSrc.id]) (.copy flyerCopyEarly) (.whileSourceHasCounter fraSrc.id .charge))
      (cause := some testCause))
  let fraAbId : ObjectId := ⟨gFra1.nextObjectId⟩
  let gFra2 :=
    (gFra1.record (GameEvent.triggerPutOnStack gFra1.turnNumber fraAbId (gFra1.snapshot (gFra1.object! fraSrc.id)) p0
      (spec := {
        sourceId := some fraSrc.id
        triggerCauseId := some cntHost.id
        triggerCauseStatus := some { counters := #[(.charge, 1), (.plusOnePlusOne, 2)] } }))).changes
      #[.pushContinuationFrame {}, .resolvingAbility (some fraAbId)]
  let gFraPostExile :=
    gFra2.applyUnifiedAbility p0 { body := .permanent (.modifyCounters (.copyFromLki .triggerSubject) .this) } #[] (some fraSrc.id)
  let fraPostExileSafeOk :=
    (gFraPostExile.findObject? fraSrc.id).isNone &&
    (gFraPostExile.followMovedToZone? fraSrc.id (· == .exile)).any (·.status.plusOnePlusOne == 0)
  let counterReconcileOk :=
    stoleAndRemoved gFin && stoleAndRemoved gInd && stoleAndRemoved gLife &&
    stoleAndRemoved gBur && stoleAndRemoved gShield && stoleAndRemoved gLore &&
    fraPostExileSafeOk

  -- 3a. (ii) Simultaneous outer-`pre` `endControlEffectsSimultaneously` in `Turns.clearEOT` and `Turns.expireUntilNextTurnEffects`:
  --          `p2`-owned/defaultControlled `simBear` has an older `.untilEndOfTurn` `.control p1` (where `p1` later left the game!)
  --          AND a newer `.untilEndOfTurn` `.control p0`: expiring both simultaneously transitions `p0 -> p2` directly
  --          (keeping `simBear` on `.battlefield` under `p2` instead of exiling it through intermediate dead controller `p1`!),
  --          AND when `p0`-owned `keepBear` has `.untilEndOfTurn` `.control p2` overridden by `.untilEndOfTurn` `.control p0`
  --          (so pre-expiry and post-expiry controller are BOTH `p0`), cleanup does NOT remove `keepBear` from combat or strip its designation!
  let gSim0 := addPermanent (addPermanent g4 bear p2 p2) bear p0 p0
  let simBear := (gSim0.permanentsOf p2)[0]!
  let keepBear := (gSim0.permanentsOf p0)[0]!
  let gSim1 :=
    (((((gSim0.createEffect (.layered (.objects #[simBear.id]) (.control p1) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[simBear.id]) (.control p0) .untilEndOfTurn)
      (cause := some testCause)).concede p1).createEffect
      (.layered (.objects #[keepBear.id]) (.control p2) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.layered (.objects #[keepBear.id]) (.control p0) .untilEndOfTurn)
      (cause := some testCause)).record
      (GameEvent.designation gSim0.turnNumber (gSim0.snapshot keepBear) .ringBearer true (cause := testCause))
  let gSimCleaned := gSim1.clearEOT
  let simultaneousExpiryOk :=
    (gSimCleaned.findObject? simBear.id).any (fun o => o.isOnBattlefield && gSimCleaned.controlledBy o p2) &&
    (gSimCleaned.findObject? keepBear.id).any (fun o =>
      o.isOnBattlefield && gSimCleaned.controlledBy o p0 && (gSimCleaned.player p0).ringBearerId == some keepBear.id)

  -- 3b. CR 610.3 `linkedExile` flushes across unbatched `Movement.move`, batched `objectLeavesTheGame`,
  --     single-spec `Core.createEffects`, and outer `Core.putCountersExceptPlusOne`:
  let gLink0 := addPermanent (addPermanent g4 cageDef p1 p1) bear p0 p0
  let lkCage := (gLink0.permanentsOf p1)[0]!
  let lkBear := (gLink0.permanentsOf p0)[0]!
  let gLinked := gLink0.exileUntilSourceLeaves (some lkCage.id) lkBear (cause := some testCause)
  -- (i) Unbatched `Movement.move` out of `.battlefield` flushes `queuedLinkedExile` immediately:
  let (gMoveReturned, _) := gLinked.move lkCage.id .exile (cause := some testCause)
  -- (ii) `objectLeavesTheGame` inside an open `withBatch` returns `lkBear` to `p0`:
  let gBatchLeaveReturned :=
    gLinked.withBatch (some (.gameRule .playerLeftGame)) fun g =>
      let g := g.record (GameEvent.playerLeftGame g.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))
      g.objectLeavesTheGame (g.object! lkCage.id) p1
  -- (iii) Single-spec `Core.createEffects #[spec]` (`else applyAll g`) flushes `queuedLinkedExile`:
  let flyerCopy : CardDef := { bear with name := "P39i3 FlyCage", keywords := #[Keyword.flying] }
  let gSingleEff0 :=
    ((gLinked.createEffect (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) .indefinite)
      (cause := some testCause)).createEffect
      (.layered (.objects #[lkCage.id]) (.types .add #[.creature] #[] #[]) .indefinite)
      (cause := some testCause)).concede p1
  let gSingleEffReturned :=
    gSingleEff0.createEffects #[.layered (.objects #[lkCage.id]) (.copy flyerCopy) .untilEndOfTurn]
      (cause := some testCause)
  -- (iv) Outer unbatched `putCountersExceptPlusOne` flushes `queuedLinkedExile`:
  let gPutExHost := addPermanent gSingleEff0 hostDef p0 p0
  let putHostId := (gPutExHost.permanentsOf p0).find? (·.name == hostDef.name) |>.get!.id
  let gPutEx0 :=
    gPutExHost.createEffect
      (.layered (.objects #[lkCage.id]) (.copy flyerCopy) (.whileSourceHasCounter putHostId .charge))
      (cause := some testCause)
  let gPutExReturned := gPutEx0.putCountersExceptPlusOne putHostId { counters := #[(.charge, 1)] } (byPlayer := some p0)
  let linkedExileFlushesOk :=
    (gMoveReturned.permanentsOf p0).any (·.name == bear.name) &&
    (gBatchLeaveReturned.permanentsOf p0).any (·.name == bear.name) &&
    (gSingleEffReturned.permanentsOf p0).any (·.name == bear.name) &&
    (gPutExReturned.permanentsOf p0).any (·.name == bear.name)

  -- 3c. (i) CR 611.2c / CR 702.26b post-phase-out Layer 1/2 scope exclusion vs pre-phase-out retention:
  let gPhBase := addPermanent (addPermanent g4 bear p0 p0) bear p0 p0
  let phTargets := gPhBase.permanentsOf p0
  let phOutBear := phTargets[0]!
  let liveBear := phTargets[1]!
  let preCopyDef : CardDef := { bear with name := "PrePhaseClone", power := some (.fixed 4), toughness := some (.fixed 4) }
  let postCopyDef : CardDef := { bear with name := "PostPhaseClone", power := some (.fixed 7), toughness := some (.fixed 7) }
  -- Pre-phase-out Layer 1 effect (`eid < phEid`) applies to `phOutBear`, then `phOutBear` phases out, then
  -- post-phase-out Layer 1 (`.creaturesControlledBy p0` copy) and Layer 2 (`.creaturesControlledBy p0` `.control p2`) effects (`eid > phEid`) are created:
  let gPreScoped :=
    (gPhBase.createEffect (.layered (.creaturesControlledBy p0) (.copy preCopyDef) .indefinite) (cause := some testCause)).phaseOut
      phOutBear (cause := some testCause)
  let gPostScoped :=
    (gPreScoped.createEffect (.layered (.creaturesControlledBy p0) (.copy postCopyDef) .indefinite)
      (cause := some (.gameRule .staticAbility))).createEffect
      (.layered (.creaturesControlledBy p0) (.control p2) .indefinite)
      (cause := some (.gameRule .staticAbility))
  let gPhasedBackIn := gPostScoped.phaseInControlled p0
  let phaseScopeExclusionOk :=
    -- `liveBear` gets the post-phase-out `PostPhaseClone` copy AND `p2` control:
    gPostScoped.name (gPostScoped.object! liveBear.id) == "PostPhaseClone" &&
    gPostScoped.controllerOf (gPostScoped.object! liveBear.id) == some p2 &&
    -- `phOutBear` keeps `PrePhaseClone` + `p0` control while phased out (CR 611.2c / 702.26b,e),
    -- and dynamically picks up active `.indefinite` board scopes once phased back in (CR 611.3a)!
    gPostScoped.name (gPostScoped.object! phOutBear.id) == "PrePhaseClone" &&
    gPostScoped.controllerOf (gPostScoped.object! phOutBear.id) == some p0 &&
    !(gPhasedBackIn.object! phOutBear.id).status.phasedOut &&
    gPhasedBackIn.name (gPhasedBackIn.object! phOutBear.id) == "PostPhaseClone" &&
    gPhasedBackIn.controllerOf (gPhasedBackIn.object! phOutBear.id) == some p2

  -- 3c. (ii) CR 702.26n departed-controller multiplayer phase-in:
  --          Turn order `p0 -> p1 -> p2 -> p3`, active turn `p0`: `p2` controls `p1`-owned `borrowedId`, phases it out,
  --          and `p2` concedes during `p0`'s turn. At `p1`'s turn (`p0 -> p1`), `p2`'s turn has NOT yet come around, so
  --          `borrowedId` stays phased out; at `p3`'s turn (`p1 -> [departed p2] -> p3`), `p2`'s turn WOULD have begun,
  --          so `borrowedId` phases in under `p1`'s control!
  let gDepPh0 := addPermanent g4 bear p1 p1
  let borrowedId := (gDepPh0.permanentsOf p1)[0]!.id
  let gDepPh1 :=
    (((gDepPh0.createEffect (.layered (.objects #[borrowedId]) (.control p2) .indefinite)
      (cause := some testCause)).phaseOut (gDepPh0.object! borrowedId) (cause := some testCause)).concede p2)
  let gTurnP1 := gDepPh1.startNextTurnAndBegin
  let stillPhasedOutOnP1 := (gTurnP1.object! borrowedId).status.phasedOut
  let gTurnP3 := gTurnP1.startNextTurnAndBegin
  let phasedInOnP3 :=
    !(gTurnP3.object! borrowedId).status.phasedOut &&
    gTurnP3.controllerOf (gTurnP3.object! borrowedId) == some p1
  let cr70226nOk := stillPhasedOutOnP1 && phasedInOnP3

  -- 3c. (iii) Pause-safe CR 502.1,3 `.untap` `untapStepAfterPhaseIn`:
  let gUntapBase :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 bear p3 p1) bear p0 p0)
          hostDef p0 p0)
        leyADef p0 p0)
      leyBDef p0 p0
  let uJail := (gUntapBase.permanentsOf p1)[0]!
  let uVic := (gUntapBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let uPhHost := (gUntapBase.permanentsOf p0).find? (·.name == hostDef.name) |>.get!
  let uLeyA := (gUntapBase.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let uLeyB := (gUntapBase.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let uRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some uLeyA, counterKind := some .plusOnePlusOne }
  let uRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some uLeyB, counterKind := some .plusOnePlusOne }
  let gUntap0 :=
    ((((((((addPermanent gUntapBase hostDef p0 p0).exileUntilSourceLeaves (some uJail.id) uVic (cause := some testCause)).createEffect
      (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) .indefinite)
      (cause := some testCause)).concede p1).phaseOut uPhHost (cause := some testCause)).createEffect
      (.layered (.objects #[uJail.id]) (.copy flyerCopy) (.whileSourceOnBattlefield uPhHost.id))
      (cause := some testCause)).createEffect
      (.replacement {
        id := uRidA, source := some uLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := uRidB, source := some uLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
  let tappedKeepHost :=
    ((gUntap0.permanentsOf p0).filter (fun o => o.name == hostDef.name && o.id != uPhHost.id))[0]!
  let gUntapPre := gUntap0.becomeTapped tappedKeepHost (cause := some testCause)
  let gUntapPaused := gUntapPre.beginTurnAfterStartExpiry
  let pausedBeforeUntap :=
    gUntapPaused.step == .untap &&
    (gUntapPaused.object! tappedKeepHost.id).status.tapped &&
    match gUntapPaused.pending with | .chooseReplacement .. => true | _ => false
  let gUntapResumed := mustApply gUntapPaused p0 (.chooseReplacement uRidA)
  let resumedIntoUpkeep :=
    gUntapResumed.step == .upkeep &&
    !(gUntapResumed.object! tappedKeepHost.id).status.tapped &&
    gUntapResumed.priority == p0
  let untapAfterPhaseInOk := pausedBeforeUntap && resumedIntoUpkeep

  mustHold39i3 "3a.counterReconcile" counterReconcileOk &&
  mustHold39i3 "3a.simultaneousExpiry" simultaneousExpiryOk &&
  mustHold39i3 "3b.linkedExileFlushes" linkedExileFlushesOk &&
  mustHold39i3 "3c.phaseScopeExclusion" phaseScopeExclusionOk &&
  mustHold39i3 "3c.cr70226n" cr70226nOk &&
  mustHold39i3 "3c.untapAfterPhaseIn" untapAfterPhaseInOk &&
  mustHold39i3 "3.replay"
    (replayOk39i3 #[gFin, gInd, gLife, gBur, gShield, gLore, gFraPostExile, gSimCleaned,
      gMoveReturned, gBatchLeaveReturned, gSingleEffReturned, gPutExReturned,
      gPostScoped, gPhasedBackIn, gTurnP1, gTurnP3, gUntapPaused, gUntapResumed])

end Phase39Item3EventAlignment

/-! ### Phase 39 Item 4: End-to-end `[+X]` `LoyaltySymbol.plusX` & `Agent.choose`, `payCostPick` loyalty-to-stun pauses, resumed `ActivationCosts`/`ManaAbilities` re-validation & nested mana checkpoint reversal, continuation-safe `abortDepartedManaAbilityCont`, and `completeTurnFaceUp` hardening -/
section Phase39Item4EventAlignment

private def mustHold39i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase39Item4EventAlignment failed: {label}"

private def replayOk39i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let leyADef : CardDef := { name := "P39i4 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P39i4 LeyB", types := #[.enchantment] }
  let baubleDef : CardDef := { name := "P39i4 Bauble", types := #[.artifact] }

  -- 4a. End-to-end `[+X]` (`LoyaltySymbol.plusX`) activation & `Agent.choose`:
  let plusXPwDef : CardDef := {
    name := "P39i4 PlusXWalker", types := #[.planeswalker], supertypes := #[.legendary]
    loyalty := some 2
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.loyalty .plusX], effect := Effect.gainLife 2 },
      { cost := CostSpec.ofItems #[.mana { symbols := #[.x] }, .loyalty .plusX], effect := Effect.gainLife 2 },
      { cost := CostSpec.ofItems #[.loyalty .minusX], effect := Effect.gainLife 2 }
    ]
  }
  let gPw00 := addPermanent g3 plusXPwDef p0 p0
  let pwId := (gPw00.permanentsOf p0)[0]!.id
  let gPw0 := gPw00.recordPutCounters pwId .loyalty 2 (some p0) (cause := some testCause)
  -- Ability 0 (`[+X]` with empty mana cost): `Agent.choose` picks `.chooseX 1`, AND `announceX` accepts `x = 5 > loyalty (2)`!
  let gPlusXStarted := mustApply gPw0 p0 (.activate pwId 0)
  let agentFreeChoice := Agent.choose gPlusXStarted p0
  let gPlusXFive := mustApply gPlusXStarted p0 (.chooseX 5)
  -- Ability 1 (`{X}, [+X]` with 3 green mana in pool): `Agent.choose` picks `.chooseX 3` (`maxAffordableX`)!
  let gPwPool := gPw0.addMana p0 (.colored .green) 3
  let gPlusXManaStarted := mustApply gPwPool p0 (.activate pwId 1)
  let agentManaChoice := Agent.choose gPlusXManaStarted p0
  -- Ability 2 (`[-X]`): `announceX` STILL rejects `x = 5 > loyalty (2)`!
  let gMinusXStarted := mustApply gPw0 p0 (.activate pwId 2)
  let minusXOverRejected :=
    match gMinusXStarted.announceX p0 5 with
    | .error _ => true
    | .ok _ => false
  let plusXSupportOk :=
    gPw0.canActivate p0 (gPw0.object! pwId) plusXPwDef.activatedAbilities[0]! &&
    gPlusXStarted.pending == .chooseX p0 &&
    (match agentFreeChoice with | some (.chooseX 1) => true | _ => false) &&
    (match agentManaChoice with | some (.chooseX 3) => true | _ => false) &&
    (gPlusXFive.object! pwId).status.loyaltyCounters == 7 &&
    gPlusXFive.stack.size == 1 &&
    minusXOverRejected

  -- 4b. (i) `ActivationCosts.payCostPick` loyalty-to-stun replacement pauses:
  let loyStunPwDef : CardDef := {
    name := "P39i4 StunWalker", types := #[.artifact, .planeswalker], supertypes := #[.legendary]
    loyalty := some 3
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.loyalty (.plus 1), .putCounters (.const 1) .stun .self, .sacrifice (.exact 1) (.filter (.hasType .artifact))]
      effect := Effect.gainLife 1
    }]
  }
  let gLs00 := addPermanent g3 loyStunPwDef p0 p0
  let lsPwId := (gLs00.permanentsOf p0).find? (·.name == loyStunPwDef.name) |>.get!.id
  let gLs0 := gLs00.recordPutCounters lsPwId .loyalty 3 (some p0) (cause := some testCause)
  let cntAddSpec : ReplacementSpec := {
    id := { kind := .extraCounterOnPermanents, object := some lsPwId }
    source := some lsPwId, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none none 1 1
  }
  let cntMulSpec : ReplacementSpec := {
    id := { kind := .multiplyCountersPut, object := none }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none none 0 2
  }
  let gLs1 :=
    (gLs0.createEffect (.replacement cntAddSpec) (cause := some testCause)).createEffect
      (.replacement cntMulSpec) (cause := some testCause)
  let gLsPickPrompt := mustApply gLs1 p0 (.activate lsPwId 0)
  -- Choosing `lsPwId` as the sacrificed artifact runs `payLoyaltyCost` FIRST, pausing on `.chooseReplacement`
  -- BEFORE stun counter placement or sacrificing `lsPwId`!
  let gLsPausedLoyalty := mustApply gLsPickPrompt p0 (.choosePermanents #[lsPwId])
  let pausedBeforeStunAndSac :=
    (gLsPausedLoyalty.findObject? lsPwId).any (·.isOnBattlefield) &&
    (gLsPausedLoyalty.object! lsPwId).status.loyaltyCounters == 3 &&
    (gLsPausedLoyalty.object! lsPwId).status.counterCount .stun == 0 &&
    match gLsPausedLoyalty.pending with | .chooseReplacement _ cs => cs.size == 2 | _ => false
  -- Answering loyalty replacement (`(1 + 1) * 2 = 4` -> loyalty `3 + 4 = 7`) pauses on the stun counter
  -- replacement next (still BEFORE sacrificing `lsPwId`!):
  let gLsPausedStun := mustApply gLsPausedLoyalty p0 (.chooseReplacement cntAddSpec.id)
  let pausedAtStunBeforeSac :=
    (gLsPausedStun.findObject? lsPwId).any (·.isOnBattlefield) &&
    (gLsPausedStun.object! lsPwId).status.loyaltyCounters == 7 &&
    (gLsPausedStun.object! lsPwId).status.counterCount .stun == 0 &&
    match gLsPausedStun.pending with | .chooseReplacement _ cs => cs.size == 2 | _ => false
  -- Answering stun replacement (`(1 + 1) * 2 = 4` stun counters) finishes stun placement, sacrifices `lsPwId`
  -- to `.graveyard p0`, and puts the ability on `.stack`!
  let gLsCompleted := mustApply gLsPausedStun p0 (.chooseReplacement cntAddSpec.id)
  let stunPlaced4 :=
    gLsCompleted.events.any fun ev =>
      match ev.change with
      | .rules (.permanent (.counters (.object eo) .stun (.put 4) _)) => eo.id == some lsPwId
      | _ => false
  let loyaltyToStunPauseOk :=
    pausedBeforeStunAndSac &&
    pausedAtStunBeforeSac &&
    stunPlaced4 &&
    (gLsCompleted.findObject? lsPwId).isNone &&
    (gLsCompleted.followMovedToZone? lsPwId (· == .graveyard p0)).isSome &&
    gLsCompleted.stack.size == 1

  -- 4b. (ii) Resumed `ActivationCosts` (`finishActivationExtraCosts`) & nested/standalone `ManaAbilities`
  --          cost-item re-validation + checkpoint reversal:
  let sacManaAltarDef : CardDef := {
    name := "P39i4 SacManaAltar", types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.hasType .artifact)), .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let greenSpellDef : CardDef := {
    name := "P39i4 GreenGrowth", manaCost := { symbols := #[.colored .green] }, types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 3 }
  }
  let gMaNest0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent (addPermanent g3 sacManaAltarDef p0 p0) baubleDef p0 p0) bear p0 p0)
          leyADef p0 p0)
        leyBDef p0 p0)
      greenSpellDef p0 (.hand p0)
  let maAltarId := (gMaNest0.permanentsOf p0).find? (·.name == sacManaAltarDef.name) |>.get!.id
  let maBaubleId := (gMaNest0.permanentsOf p0).find? (·.name == baubleDef.name) |>.get!.id
  let maBearId := (gMaNest0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let maLeyA := (gMaNest0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let maLeyB := (gMaNest0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let greenCardId := (gMaNest0.player p0).hand.back!
  let sacRidA : ReplacementId := { kind := .exileOppDeath, object := some maLeyA }
  let sacRidB : ReplacementId := { kind := .exileOppDeath, object := some maLeyB }
  let gMaNest1 :=
    (gMaNest0.createEffect
      (.replacement {
        id := sacRidA, source := some maLeyA, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some maBaubleId) false }) (cause := some testCause)).createEffect
      (.replacement {
        id := sacRidB, source := some maLeyB, controller := some p0, affectedPlayer := p0,
        kind := .exileInsteadOfGraveyard (some maBaubleId) false }) (cause := some testCause)
  -- Cast `greenCardId` (saves outer spell checkpoint, opens `.activateManaAbilities p0`), then activate `maAltarId`'s
  -- mana ability with `#[maBaubleId, maBearId]` (saves nested mana checkpoint, pauses on `maBaubleId`'s sacrifice!):
  let gSpellWaitingMana := mustApply gMaNest1 p0 (.cast greenCardId)
  let gNestedMaPaused :=
    match gSpellWaitingMana.activateManaAbility p0 maAltarId 0 #[.colored .green] #[maBaubleId, maBearId] with
    | .ok g => g
    | .error e => panic! e
  let nestedCkptSaved :=
    gNestedMaPaused.outerProposalCheckpoints.size == 1 && gNestedMaPaused.hasActiveManaProposalCheckpoint
  -- Steal `maBearId` (`p2` gains control) during the replacement pause, then answer `sacRidA`:
  -- `finishActivateManaAbilityPicks` sees `maBearId` is no longer controlled by `p0`, reverses ONLY the nested mana
  -- checkpoint (`maBaubleId` returns to `.battlefield`, `maBearId` stays untapped, NO mana added), and restores
  -- the enclosing spell proposal at `.activateManaAbilities p0`!
  let gNestedMaStolen := gNestedMaPaused.createEffect (.control maBearId p2) (cause := some testCause)
  let gNestedMaReversed := mustApply gNestedMaStolen p0 (.chooseReplacement sacRidA)
  -- Also test `ActivationCosts.finishActivationExtraCosts`: if `lsPwId` is stolen during `gLsPausedLoyalty`, answering
  -- `cntAddSpec.id` reverses the planeswalker activation via `reverseProposedSpellFwd`!
  let gLsStolenMidPause := gLsPausedLoyalty.createEffect (.control lsPwId p2) (cause := some testCause)
  let gLsReversedOnSteal := mustApply gLsStolenMidPause p0 (.chooseReplacement cntAddSpec.id)
  let resumedCostRevalidationOk :=
    nestedCkptSaved &&
    gNestedMaReversed.proposedSpell.isSome &&
    gNestedMaReversed.outerProposalCheckpoints.isEmpty &&
    gNestedMaReversed.proposalCheckpoint.isSome &&
    gNestedMaReversed.pending == .activateManaAbilities p0 &&
    (gNestedMaReversed.permanentsOf p0).any (·.id == maBaubleId) &&
    !(gNestedMaReversed.object! maBearId).status.tapped &&
    (gNestedMaReversed.player p0).manaPool.total == 0 &&
    gLsReversedOnSteal.proposedSpell.isNone &&
    gLsReversedOnSteal.stack.isEmpty &&
    (gLsReversedOnSteal.object! lsPwId).status.loyaltyCounters == 3

  -- 4c. Continuation-safe `ManaAbilities.abortDepartedManaAbilityCont`:
  --     When an enclosing continuation (`outerPendingReplacements := #[.gainLife p1 4 ...]`) is active while `p0`
  --     pauses a standalone sacrifice mana ability on `.chooseReplacement` and concedes, `abortDepartedManaAbilityCont`
  --     reverses the standalone mana checkpoint AND drains `.gainLife p1 4` before granting priority to `p1`!
  let p1LifeBefore := (gMaNest1.player p1).life
  let gContMa0 :=
    gMaNest1.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p1 4 (some testCause)),
      .pending (.mayPayGeneric p0 1) ]
  let gContMaPaused :=
    match gContMa0.activateManaAbility p0 maAltarId 0 #[.colored .green] #[maBaubleId, maBearId] with
    | .ok g => g
    | .error e => panic! e
  let gContMaConceded := mustApply gContMaPaused p0 .concede
  let abortContSafeOk :=
    (gContMaConceded.player p0).leftTheGame &&
    (gContMaConceded.player p1).life == p1LifeBefore + 4 &&
    gContMaConceded.pending == Pending.none &&
    gContMaConceded.priority == p1

  -- 4d. `Casting.completeTurnFaceUp` entry guard (`g.over` / `!g.stillInGame caster`), `.chooseLegend` prompt preservation,
  --     post-reconcile `flushQueuedLinkedExile` + `.chooseReplacement` pause ordering, and `.finishTurnFaceUp` `callerShouldResume`:
  let flyerMorphDef : CardDef := {
    creature "P39i4 SkyMorph" ManaCost.empty #["Bird"] 2 2 with
    keywords := #[Keyword.flying, .morph (CostSpec.ofGeneric 1)]
  }
  let gTfBase :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g3 bear p0 p0) bear p0 p0)
          flyerMorphDef p0 p0)
        leyADef p0 p0)
      leyBDef p0 p0
  let tfBears := (gTfBase.permanentsOf p0).filter (·.name == bear.name)
  let tfMorphId := (gTfBase.permanentsOf p0).find? (·.name == flyerMorphDef.name) |>.get!.id
  let tfLeyA := (gTfBase.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let tfLeyB := (gTfBase.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let gTfFd := setFaceDown gTfBase tfMorphId true
  -- (i) `g.over` entry guard returns `(g, false)` untouched:
  let gTfOver := gTfFd.record (GameEvent.gameEnded gTfFd.turnNumber (.won p0) (cause := some testCause))
  let (gTfOverAfter, tfOverRes) := gTfOver.completeTurnFaceUp p0 tfMorphId
  -- (ii) `.chooseLegend` prompt on `p0` is preserved across `completeTurnFaceUp`:
  let gTfLegend0 :=
    (gTfFd.createEffect
      (.layered (.objects (tfBears.map (·.id))) (.types .add #[] #[] #[.legendary]) .indefinite)
      (cause := some testCause)).checkSBA
  let (gTfLegendAfter, tfLegendRes) := gTfLegend0.completeTurnFaceUp p0 tfMorphId
  -- (iii) Post-reconcile `flushQueuedLinkedExile` + `.chooseReplacement` pause ordering:
  --       `depMorphId` (owned by `p0`, defaultControlled by departed `p1`, printed with `flying := true`) is face down
  --       (so Layer 1 `baseCard` lacks `flying`) and controlled by `p0` via `.creaturesWithout #[Keyword.flying]`,
  --       holding `tfBears[0]!` in `linkedExile`. Turning `depMorphId` face up gives its Layer 1 `baseCard` `flying`,
  --       ending `p0`'s control and exiling `depMorphId` via CR 800.4c so `tfBears[0]!`'s CR 610.3 return pauses on `.chooseReplacement`!
  let gTfPause0 := addPermanent gTfBase flyerMorphDef p0 p1
  let depMorphId := (gTfPause0.permanentsOf p1)[0]!.id
  let tfRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some tfLeyA, counterKind := some .plusOnePlusOne }
  let tfRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some tfLeyB, counterKind := some .plusOnePlusOne }
  let gTfPause1 :=
    ((((((setFaceDown gTfPause0 depMorphId true).exileUntilSourceLeaves (some depMorphId) tfBears[0]!
      (cause := some testCause)).createEffect
      (.layered (.creaturesWithout #[Keyword.flying]) (.control p0) .indefinite)
      (cause := some testCause)).concede p1).createEffect
      (.replacement {
        id := tfRidA, source := some tfLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := tfRidB, source := some tfLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
  let (gTfPausedOnReturn, tfPausedCallerRes) := gTfPause1.completeTurnFaceUp p0 depMorphId
  let pausedAtReturnOk :=
    !tfPausedCallerRes &&
    (gTfPausedOnReturn.followMovedToZone? depMorphId (· == .exile)).isSome &&
    match gTfPausedOnReturn.pending with | .chooseReplacement .. => true | _ => false
  let gTfPauseResolved := mustApply gTfPausedOnReturn p0 (.chooseReplacement tfRidA)
  -- (iv) `.finishTurnFaceUp` `callerShouldResume` when `spellId` left `.battlefield` (no checkpoint) with an outer continuation:
  let tfResumeBaseLife := (gTfFd.player p0).life
  let (gTfGone0, _) := gTfFd.move tfMorphId .exile (cause := some testCause)
  let gTfGone1 :=
    (gTfGone0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 3 (some testCause))) ]).resumePendingReplacement
      (.finishTurnFaceUp p0 tfMorphId false)
  let completeTurnFaceUpOk :=
    !tfOverRes &&
    (gTfOverAfter.object! tfMorphId).status.faceDown &&
    !tfLegendRes &&
    !(gTfLegendAfter.object! tfMorphId).status.faceDown &&
    gTfLegendAfter.pending == gTfLegend0.pending &&
    pausedAtReturnOk &&
    ((gTfPauseResolved.permanentsOf p0).filter (·.name == bear.name)).size == 2 &&
    gTfPauseResolved.priority == p0 &&
    (gTfGone1.player p0).life == tfResumeBaseLife + 3

  mustHold39i4 "4a.plusXSupport" plusXSupportOk &&
  mustHold39i4 "4b.loyaltyToStunPause" loyaltyToStunPauseOk &&
  mustHold39i4 "4b.resumedCostRevalidation" resumedCostRevalidationOk &&
  mustHold39i4 "4c.abortContSafe" abortContSafeOk &&
  mustHold39i4 "4d.completeTurnFaceUp" completeTurnFaceUpOk &&
  mustHold39i4 "4.replay"
    (replayOk39i4 #[gPlusXStarted, gPlusXFive, gPlusXManaStarted, gMinusXStarted,
      gLsPausedLoyalty, gLsPausedStun, gLsCompleted,
      gSpellWaitingMana, gNestedMaPaused, gNestedMaReversed, gLsReversedOnSteal,
      gContMaPaused, gContMaConceded,
      gTfOverAfter, gTfLegendAfter, gTfPausedOnReturn, gTfPauseResolved, gTfGone1])

end Phase39Item4EventAlignment

section Phase40Item1EventAlignment

private def mustHold40i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase40Item1EventAlignment failed: {label}"

private def replayOk40i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let cageDef : CardDef := { name := "P40i1 Cage", types := #[.artifact] }
  let altarDef : CardDef := { name := "P40i1 Altar", types := #[.artifact] }
  let leyADef : CardDef := { name := "P40i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P40i1 LeyB", types := #[.enchantment] }
  let morphDef : CardDef := {
    creature "P40i1 Morph" ManaCost.empty #["Human"] 2 2 with keywords := #[.morph (CostSpec.ofGeneric 1)]
  }

  -- 1a. Quiet `reconcilePostReplayDepartures` (`continueCheckpointReplay ... true`), `wasSuppressed` preservation in
  --     `Casting.reverseProposedSpellCore?` & `Leaving.rewindAbortedProposalOnLeave`, simultaneous departed `.control`
  --     expiry (no false intermediate reversion log to departed `p1`), and departed `ckptPending` routing in
  --     `Core.reverseToProposalCheckpointCore?`:
  let gQ0 :=
    insertObject
      (insertObject
        (addPermanent
          (addPermanent
            (addPermanent
              (addPermanent (addPermanent g4 cageDef p0 p1) altarDef p3 p3)
              bear p0 p0)
            leyADef p0 p0)
          leyBDef p0 p0)
        hero p0 .exile)
      hero p0 .exile
  let qCage := (gQ0.permanentsOf p1)[0]!
  let qAltar := (gQ0.permanentsOf p3)[0]!
  let qBear := (gQ0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let qLeyA := (gQ0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let qLeyB := (gQ0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let qExHeroes := gQ0.objects.filter (fun o => o.zone == .exile && o.owner == p0)
  let qExHero := qExHeroes[0]!
  let qExHero2 := qExHeroes[1]!
  let qRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some qLeyA, counterKind := some .plusOnePlusOne }
  let qRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some qLeyB, counterKind := some .plusOnePlusOne }
  let gQCkpt :=
    (((((gQ0.exileUntilSourceLeaves (some qCage.id) qBear (cause := some testCause)).createEffect
      (.layered (.objects #[qCage.id]) (.control p3) .indefinite) (cause := some testCause)).createEffect
      (.control qAltar.id p0) (cause := some testCause)).createEffect
      (.replacement {
        id := qRidA, source := some qLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := qRidB, source := some qLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).changes #[
      .pushContinuationFrame { postCastCleanup := some (.cascadeBottom p0 qExHero.id #[qExHero.id, qExHero2.id]) },
      .saveProposalCheckpoint ]
  let gQReplayReady :=
    ((gQCkpt.restoreProposalCheckpoint gQCkpt.proposalCheckpoint.get!).record
      (GameEvent.playerLeftGame gQCkpt.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).record
      (GameEvent.playerLeftGame gQCkpt.turnNumber p3 (cause := some (.gameRule .playerLeftGame)))
  let gQAfterQuietCont :=
    (gQReplayReady.change (.pushContinuationFrame {})).resumePendingReplacement
      (.continueCheckpointReplay #[] #[] #[] #[] #[] 0 true #[])
  let (gQCast1, qAb) :=
    (gQCkpt.createEffect (.layered (.objects #[qCage.id]) (.control p0) .indefinite) (cause := some testCause)).putStackAbility
      qAltar p0 (abilityEffect := some (Effect.gainLife 1))
  let qProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := qAb.id, original := qAb
    originalSnapshot := gQCast1.snapshot qAb, kind := .activatedAbility, sourceId := some qAltar.id
  }
  let gQCastSup :=
    ((mustApply (gQCast1.changes #[.proposedSpell (some qProp), .pending (.activateManaAbilities p0)]) p1 .concede).change
      (.pushContinuationFrame {
        pendingReplacement := some (.continueCheckpointReplay #[] #[] #[] #[] #[] 0 true #[]) }))
  let gQCastRev := mustApply gQCastSup p0 .pay
  let qPropLeave : ProposedSpell := { qProp with cost := ManaCost.empty }
  let gQLeaveSup :=
    ((mustApply (gQCast1.changes #[.proposedSpell (some qPropLeave), .pending (.chooseX p0)]) p1 .concede).change
      (.pushContinuationFrame {
        pendingReplacement := some (.continueCheckpointReplay #[] #[] #[] #[] #[] 0 true #[]) }))
  let gQLeaveRev := mustApply gQLeaveSup p3 .concede
  let gSimCtrl0 :=
    ((gQ0.createEffect (.layered (.objects #[qBear.id]) (.control p1) .indefinite) (cause := some testCause)).createEffect
      (.layered (.objects #[qBear.id]) (.control p1) .indefinite) (cause := some testCause))
  let preSimLogs := gSimCtrl0.log.size
  let gSimCtrlAfter := mustApply gSimCtrl0 p1 .concede
  let newSimLogs := gSimCtrlAfter.log.extract preSimLogs gSimCtrlAfter.log.size
  let p1Name := (gSimCtrl0.player p1).name
  let noFalseDepartedCtrlLog :=
    !newSimLogs.any (fun s => (s.splitOn s!"{p1Name} regains control").length > 1 || (s.splitOn s!"returns to {p1Name}").length > 1)
  let gDepPendCkpt :=
    (g4.changes #[.pending (.mayPayGeneric p1 1), .saveProposalCheckpoint]).concede p1
  let gDepPendRev :=
    match gDepPendCkpt.reverseToProposalCheckpoint? with
    | .ok g => g
    | .error e => panic! e
  let quietAndDepartedCtrlOk :=
    gQAfterQuietCont.pending == .none &&
    (gQAfterQuietCont.permanentsOf p0).any (·.name == bear.name) &&
    gQCastRev.afterRandom == .none &&
    (gQCastRev.findObject? qExHero.id).any (·.zone == .exile) &&
    gQLeaveRev.afterRandom == .none &&
    (gQLeaveRev.findObject? qExHero.id).any (·.zone == .exile) &&
    noFalseDepartedCtrlLog &&
    gSimCtrlAfter.controlledBy (gSimCtrlAfter.object! qBear.id) p0 &&
    gDepPendRev.pending == .none

  -- 1b. Full-slice `ckptPendingReplacementUntouchedBeforeLeave` & `restoreCkptPending?`-before-`ckptOrigCont?` outer-bundle splitting:
  let gMorph0 := addPermanent (addPermanent g4 altarDef p2 p2) morphDef p0 p0
  let mAltar := (gMorph0.permanentsOf p2)[0]!
  let mId := (gMorph0.permanentsOf p0).find? (·.name == morphDef.name) |>.get!.id
  let gMorphFd := setFaceDown gMorph0 mId true
  let mObj := gMorphFd.object! mId
  let mBaseLife := (gMorphFd.player p0).life
  let origGain6 : PendingReplacement := .gainLife p0 6 (some testCause)
  let gCostStash0 :=
    (gMorphFd.createEffect (.control mAltar.id p0) (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some origGain6),
      .saveProposalCheckpoint,
      .beginProposalAction .costAction,
      .pendingReplacement none ]
  let gCostStash1 :=
    (gCostStash0.gainLife p0 1 (cause := some testCause)).changes #[
      .pendingReplacement (some origGain6),
      .endProposalAction ]
  let stashCkpt := gCostStash1.proposalCheckpoint.get!
  let costStashUntouchedOk := gCostStash1.ckptPendingReplacementUntouchedBeforeLeave stashCkpt #[]
  let gMultiAfterP1 := mustApply (gCostStash1.change (.pending (.mayPayGeneric p0 1))) p1 .concede
  let gMultiConsumed :=
    (gMultiAfterP1.changes #[.pending .none, .pendingReplacement none, .popContinuationFrame]).gainLife p0 6 (cause := some testCause)
  let multiCkpt := gMultiConsumed.proposalCheckpoint.get!
  let multiConsumedFalseOk := !(gMultiConsumed.ckptPendingReplacementUntouchedBeforeLeave multiCkpt #[p1])
  let (gMultiAb0, abMulti) := gMultiConsumed.putStackAbility mAltar p0 (abilityEffect := some (Effect.gainLife 1))
  let multiProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := abMulti.id, original := abMulti
    originalSnapshot := gMultiAb0.snapshot abMulti, kind := .activatedAbility, sourceId := some mAltar.id, resolutionCast := true
  }
  let gMultiAfterP2 :=
    (mustApply (gMultiAb0.changes #[.proposedSpell (some multiProp), .pending (.chooseX p0)]) p2 .concede).drainPendingContinuations
  let gOrderCkpt :=
    ((gMorphFd.record (GameEvent.playerLeftGame gMorphFd.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))).createEffect
      (.control mAltar.id p0) (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pending (.mayPayGeneric p0 1),
      .pendingReplacement (some origGain6),
      .saveProposalCheckpoint ]
  let orderProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := mObj.id, original := mObj
    originalSnapshot := gOrderCkpt.snapshot mObj, kind := .turnFaceUp, sourceId := some mObj.id, resolutionCast := true
  }
  let depPlus2 : PendingReplacement := .gainLife p0 2 (some testCause)
  let gOrderPopped :=
    ((((gOrderCkpt.createEffect (.control mObj.id p3) (cause := some testCause)).changes #[
      .proposedSpell (some orderProp),
      .pendingReplacement none,
      .pushOuterPendingReplacement (.seq depPlus2 origGain6) ])).resumePendingReplacement
      (.restorePending (.activateManaAbilities p0) true none #[p1] none))
  let orderBeforePromptOk :=
    gOrderPopped.pending == .mayPayGeneric p0 1 &&
    (gOrderPopped.player p0).life == mBaseLife + 2
  let gOrderAfterDecline := (mustApply gOrderPopped p0 .decline).drainPendingContinuations
  let (gOrdL0, abOrd) := gOrderCkpt.putStackAbility mAltar p0 (abilityEffect := some (Effect.gainLife 1))
  let ordLeaveProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := abOrd.id, original := abOrd
    originalSnapshot := gOrdL0.snapshot abOrd, kind := .activatedAbility, sourceId := some mAltar.id, resolutionCast := true
  }
  let gOrdLeavePaused := mustApply (gOrdL0.changes #[.proposedSpell (some ordLeaveProp), .pending (.chooseX p0)]) p2 .concede
  let ordLeaveBeforeOk :=
    gOrdLeavePaused.pending == .mayPayGeneric p0 1 &&
    (gOrdLeavePaused.player p0).life == mBaseLife
  let gOrdLeaveDrained := (mustApply gOrdLeavePaused p0 .decline).drainPendingContinuations
  let stateMachineAndOrderOk :=
    costStashUntouchedOk &&
    multiConsumedFalseOk &&
    (gMultiAfterP2.player p0).life == mBaseLife &&
    orderBeforePromptOk &&
    (gOrderAfterDecline.player p0).life == mBaseLife + 8 &&
    ordLeaveBeforeOk &&
    (gOrdLeaveDrained.player p0).life == mBaseLife + 6

  -- 1c. `.seq` inner sub-continuation & `afterRandom` ordering + `stepCanReverseProposal` (`.finishTurnFaceUp`, `.finishBecomeActivated`, `.finishPostLoyaltyActivated`):
  let gSeqRnd0 :=
    g4.changes #[
      .pushContinuationFrame { afterRandom := .draw p0 1 },
      .pushContinuationFrame {} ]
  let gSeqRnd1 :=
    gSeqRnd0.resumePendingReplacement
      (.seq (.restorePending .none false none #[] none) (.gainLife p0 4 (some testCause)))
  let seqAfterRandomOk :=
    gSeqRnd1.afterRandom != .none &&
    (gSeqRnd1.player p0).life == (gSeqRnd0.player p0).life &&
    gSeqRnd1.pendingReplacement == some (.gainLife p0 4 (some testCause))
  let gInner0 :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.seq (.gainLife p0 3 (some testCause)) (.gainLife p1 5 (some testCause))) ]
  let gInnerPreIdx := gInner0.events.size
  let gInnerDone :=
    gInner0.resumePendingReplacement
      (.seq (.restorePending .none true none #[] none) (.gainLife p2 7 (some testCause)))
  let innerGains : Array PlayerId :=
    (gInnerDone.events.extract gInnerPreIdx gInnerDone.events.size).filterMap fun ev =>
      match ev with
      | .rules _ (.life (.gained q _)) _ _ => some q
      | _ => none
  let gStepRevCkpt :=
    gMorphFd.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some origGain6),
      .saveProposalCheckpoint ]
  let stepRevProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := mObj.id, original := mObj
    originalSnapshot := gStepRevCkpt.snapshot mObj, kind := .turnFaceUp, sourceId := some mObj.id, resolutionCast := true
  }
  let gStepRevDone :=
    (((gStepRevCkpt.createEffect (.control mObj.id p2) (cause := some testCause)).changes #[
      .proposedSpell (some stepRevProp),
      .pendingReplacement none ]).resumePendingReplacement
      (.seq (.finishTurnFaceUp p0 mObj.id true) (.gainLife p0 9 (some testCause))))
      |>.drainPendingContinuations
  let seqAndStepRevOk :=
    seqAfterRandomOk &&
    innerGains == #[p0, p1, p2] &&
    (gStepRevDone.player p0).life == mBaseLife + 6

  -- 1d. `Pending.chooseLegend` spectator-departure preservation (including snapshot-only choices when `p2` owns
  --     non-prompted battlefield permanents / attachments / cards / mana / monarch vs prompted-legend or
  --     legend-source departure invalidation), `finishSbaSweep` live filtering + `leftTheGame` skip,
  --     shared `keepLegend`, and `Agent.choose` / `Game.applyIdle` live filtering:
  let legDef : CardDef := { bear with name := "P40i1 Legend", supertypes := #[.legendary] }
  let fragileLordDef : CardDef := creature "P40i1 FragileLord" ManaCost.empty #["Wizard"] 1 0
  let p2LandDef : CardDef := { name := "P40i1 Forest", types := #[.land] }
  let eqDef : CardDef := { name := "P40i1 Spear", types := #[.artifact], subtypes := #["Equipment"] }
  let gLeg0 :=
    (addPermanent (addPermanent (addPermanent g4 legDef p0 p0) legDef p0 p0) legDef p0 p0).checkSBA
  let legIds := match gLeg0.pending with | .chooseLegend _ _ ids => ids | _ => #[]
  let (gLegExiledOne, _) := gLeg0.move legIds[0]! .exile (cause := some testCause)
  let gLegAfterSpec := mustApply gLegExiledOne p2 .concede
  let specFilteredIds := match gLegAfterSpec.pending with | .chooseLegend _ _ ids => ids | _ => #[]
  let agentStalePickOk :=
    match Agent.choose gLegExiledOne p0 with
    | some (.keepLegend id) => id != legIds[0]! && specFilteredIds.contains id
    | _ => false
  let gIdleRes := applyIdle gLegExiledOne
  let gSnapSetup0 :=
    insertObject
      (insertObject
        (insertObject
          (insertObject
            (addPermanent
              (addPermanent
                (addPermanent
                  (addPermanent
                    (addPermanent
                      (addPermanent
                        (addPermanent (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0) fragileLordDef p0 p0)
                        p2LandDef p2 p2)
                      hero p2 p2)
                    eqDef p2 p2)
                  eqDef p1 p1)
                altarDef p1 p1)
              hero p1 p2)
            hero p2 (.library p2))
          hero p2 (.hand p2))
        hero p2 (.graveyard p2))
      hero p2 .exile
  let snapBears := (gSnapSetup0.permanentsOf p0).filter (·.name == bear.name)
  let sb1 := snapBears[0]!
  let sb2 := snapBears[1]!
  let sLord := (gSnapSetup0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
  let p2Host := (gSnapSetup0.permanentsOf p2).find? (fun o => o.name == hero.name && o.owner == p2) |>.get!
  let p2Eq := (gSnapSetup0.permanentsOf p2).find? (fun o => o.name == eqDef.name && o.owner == p2) |>.get!
  let p1Eq := (gSnapSetup0.permanentsOf p1).find? (·.name == eqDef.name) |>.get!
  let p1Altar := (gSnapSetup0.permanentsOf p1).find? (·.name == altarDef.name) |>.get!
  let p1Orph := (gSnapSetup0.permanentsOf p2).find? (fun o => o.name == hero.name && o.owner == p1) |>.get!
  let p2Ex := (gSnapSetup0.objects.filter (fun o => o.zone == .exile && o.owner == p2))[0]!
  let gSnap0 :=
    (((((((gSnapSetup0.record (GameEvent.attached gSnapSetup0.turnNumber (gSnapSetup0.snapshot p1Eq) p2Host.id (cause := testCause))).record
      (GameEvent.attached gSnapSetup0.turnNumber (gSnapSetup0.snapshot p2Eq) sb1.id (cause := testCause))).createEffect
      (.control p1Altar.id p2) (cause := some testCause)).record
      (GameEvent.manaAdded gSnapSetup0.turnNumber p2 #[{ mana := .colorless }] (cause := some testCause))).record
      (GameEvent.becameMonarch gSnapSetup0.turnNumber p2 none (cause := some testCause))).createEffect
      (.playPermission p2Ex.id { player := p2, whileExiled := true }) (cause := some testCause)).createEffect
      (.layered (.objects #[sb1.id, sb2.id]) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield sLord.id))
      (cause := some testCause)).checkSBA
  let preSpecEvIdx := gSnap0.events.size
  let gSnapAfterP2 := mustApply gSnap0 p2 .concede
  let bfCeasedCount :=
    (gSnapAfterP2.events.extract preSpecEvIdx gSnapAfterP2.events.size).foldl (fun acc ev =>
      match ev with
      | .rules _ (.zone (.ceasedToExist before)) _ _ =>
        if before.zone == .battlefield then acc + 1 else acc
      | _ => acc) 0
  let snapAgentPickOk :=
    match Agent.choose gSnapAfterP2 p0 with
    | some (.keepLegend id) => id == sb1.id || id == sb2.id
    | _ => false
  let gSnapKept := mustApply gSnapAfterP2 p0 (.keepLegend sb1.id)
  let gEqPromptSetup0 :=
    addPermanent
      (addPermanent (addPermanent (addPermanent g4 eqDef p0 p0) eqDef p0 p0) fragileLordDef p0 p0)
      hero p2 p2
  let snapEqs := (gEqPromptSetup0.permanentsOf p0).filter (·.name == eqDef.name)
  let se1 := snapEqs[0]!
  let se2 := snapEqs[1]!
  let eLord := (gEqPromptSetup0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
  let eP2Host := (gEqPromptSetup0.permanentsOf p2)[0]!
  let gEqPrompt0 :=
    ((gEqPromptSetup0.record
      (GameEvent.attached gEqPromptSetup0.turnNumber (gEqPromptSetup0.snapshot se1) eP2Host.id (cause := testCause))).createEffect
      (.layered (.objects #[se1.id, se2.id]) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield eLord.id))
      (cause := some testCause)).checkSBA
  let gEqPromptAfterP2 := mustApply gEqPrompt0 p2 .concede
  let gEqPromptKept := mustApply gEqPromptAfterP2 p0 (.keepLegend se1.id)
  let gPermSetup0 :=
    addPermanent (addPermanent (addPermanent g4 bear p2 p0) bear p0 p0) fragileLordDef p0 p0
  let permBears := (gPermSetup0.permanentsOf p0).filter (·.name == bear.name)
  let pbIds := permBears.map (·.id)
  let pLord := (gPermSetup0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
  let gPermSnap0 :=
    (gPermSetup0.createEffect
      (.layered (.objects pbIds) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield pLord.id))
      (cause := some testCause)).checkSBA
  let gPermLeft := mustApply gPermSnap0 p2 .concede
  let gLandSrcSetup0 :=
    addPermanent (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0) p2LandDef p2 p2
  let lbIds := ((gLandSrcSetup0.permanentsOf p0).filter (·.name == bear.name)).map (·.id)
  let p2SrcLand := (gLandSrcSetup0.permanentsOf p2)[0]!
  let gLandSrc0 :=
    (gLandSrcSetup0.createEffect
      (.layered (.objects lbIds) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield p2SrcLand.id))
      (cause := some testCause)).checkSBA
  let gLandSrcLeft := mustApply gLandSrc0 p2 .concede
  let snapSpectatorOk :=
    !gSnap0.treatedAsLegendary (gSnap0.object! sb1.id) &&
    gSnap0.pending == .chooseLegend p0 bear.name #[sb1.id, sb2.id] &&
    bfCeasedCount == 3 &&
    (gSnapAfterP2.findObject? p2Eq.id).isNone &&
    (gSnapAfterP2.followMovedToZone? p1Orph.id (· == .exile)).isSome &&
    gSnapAfterP2.pending == .chooseLegend p0 bear.name #[sb1.id, sb2.id] &&
    snapAgentPickOk &&
    gSnapKept.pending == .none &&
    gSnapKept.currentBatch.isNone &&
    (gSnapKept.permanentsOf p0).map (·.id) == #[sb1.id] &&
    (gSnapKept.followMovedToZone? sb2.id (· == .graveyard p0)).isSome &&
    !gEqPrompt0.treatedAsLegendary (gEqPrompt0.object! se1.id) &&
    (gEqPrompt0.object! se1.id).attachedTo == some eP2Host.id &&
    gEqPrompt0.pending == .chooseLegend p0 eqDef.name #[se1.id, se2.id] &&
    (gEqPromptAfterP2.object! se1.id).attachedTo == none &&
    gEqPromptAfterP2.pending == .chooseLegend p0 eqDef.name #[se1.id, se2.id] &&
    gEqPromptKept.pending == .none &&
    gEqPromptKept.currentBatch.isNone &&
    (gEqPromptKept.permanentsOf p0).map (·.id) == #[se1.id] &&
    (gEqPromptKept.followMovedToZone? se2.id (· == .graveyard p0)).isSome &&
    gPermSnap0.pending == .chooseLegend p0 bear.name pbIds &&
    gPermLeft.pending == .none &&
    gPermLeft.currentBatch.isNone &&
    (gPermLeft.permanentsOf p0).size == 1 &&
    gLandSrc0.pending == .chooseLegend p0 bear.name lbIds &&
    gLandSrcLeft.pending == .none &&
    gLandSrcLeft.currentBatch.isNone &&
    (gLandSrcLeft.permanentsOf p0).size == 2
  let legendAlignOk :=
    legIds.size == 3 &&
    specFilteredIds == #[legIds[1]!, legIds[2]!] &&
    agentStalePickOk &&
    ((gIdleRes.permanentsOf p0).filter (·.name == legDef.name)).size == 1 &&
    snapSpectatorOk

  mustHold40i1 "1a.quietAndDepartedCtrl" quietAndDepartedCtrlOk &&
  mustHold40i1 "1b.stateMachineAndOrder" stateMachineAndOrderOk &&
  mustHold40i1 "1c.seqAndStepRev" seqAndStepRevOk &&
  mustHold40i1 "1d.legendAlign" legendAlignOk &&
  mustHold40i1 "1.replay"
    (replayOk40i1 #[gQAfterQuietCont, gQCastRev, gQLeaveRev, gSimCtrlAfter, gDepPendRev,
      gMultiAfterP2, gOrderPopped, gOrderAfterDecline, gOrdLeavePaused, gOrdLeaveDrained,
      gSeqRnd1, gInnerDone, gStepRevDone, gLegAfterSpec, gIdleRes,
      gSnapAfterP2, gSnapKept, gEqPromptAfterP2, gEqPromptKept, gPermLeft, gLandSrcLeft])

end Phase40Item1EventAlignment

section Phase40Item2EventAlignment

private def mustHold40i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase40Item2EventAlignment failed: {label}"

private def replayOk40i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let srcDef : CardDef := creature "P40i2 Src" ManaCost.empty #["Construct"] 4 4
  let leyADef : CardDef := { name := "P40i2 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P40i2 LeyB", types := #[.enchantment] }
  let prepSpellFace : SubFace := { kind := .prepare, name := "P40i2 PrepSpell" }
  let prepCreatureDef : CardDef := {
    creature "P40i2 PrepMage" ManaCost.empty #["Wizard"] 2 2 with
    subFaces := #[prepSpellFace]
  }

  -- 2a. Simultaneous outer-`pre` control snapshots across `removeAllCountersFrom`, CR 704.5q (`+1/+1`/`-1/-1` SBA),
  --     `expireWhileSourceEffects` (via `move` & `ceaseToExist`), and `expireUntilTurnCommandEffects`:
  let gBase := addPermanent (addPermanent g3 bear p0 p0) srcDef p0 p0
  let rbBear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let srcPerm := (gBase.permanentsOf p0).find? (·.name == srcDef.name) |>.get!
  let gRem0a :=
    ((((gBase.record (GameEvent.counters gBase.turnNumber (some p0) (gBase.snapshot srcPerm) .lore 1 (cause := testCause))).record
      (GameEvent.counters gBase.turnNumber (some p0) (gBase.snapshot srcPerm) .charge 1 (cause := testCause))).createEffect
      (.layered (.objects #[rbBear.id]) (.control p2) (.whileSourceHasCounter srcPerm.id .lore)) (cause := some testCause)).createEffect
      (.layered (.objects #[rbBear.id]) (.control p0) (.whileSourceHasCounter srcPerm.id .charge)) (cause := some testCause))
  let gRem0 := gRem0a.record (GameEvent.designation gRem0a.turnNumber (gRem0a.snapshot (gRem0a.object! rbBear.id)) .ringBearer true (cause := testCause))
  let preRemLog := gRem0.log.size
  let gRemAfter := gRem0.removeAllCountersFrom srcPerm.id (cause := some testCause)
  let remLogs := gRemAfter.log.extract preRemLog gRemAfter.log.size
  let p2Name := (g3.player p2).name
  let remOk :=
    (gRemAfter.player p0).ringBearerId == some rbBear.id &&
    gRemAfter.controlledBy (gRemAfter.object! rbBear.id) p0 &&
    !remLogs.any (fun s => (s.splitOn p2Name).length > 1)
  let g704q0a :=
    ((((gBase.record (GameEvent.counters gBase.turnNumber (some p0) (gBase.snapshot srcPerm) .minusOneMinusOne 1 (cause := testCause))).record
      (GameEvent.counters gBase.turnNumber (some p0) (gBase.snapshot srcPerm) .plusOnePlusOne 1 (cause := testCause))).createEffect
      (.layered (.objects #[rbBear.id]) (.control p2) (.whileSourceHasCounter srcPerm.id .minusOneMinusOne)) (cause := some testCause)).createEffect
      (.layered (.objects #[rbBear.id]) (.control p0) (.whileSourceHasCounter srcPerm.id .plusOnePlusOne)) (cause := some testCause))
  let g704q0 := g704q0a.record (GameEvent.designation g704q0a.turnNumber (g704q0a.snapshot (g704q0a.object! rbBear.id)) .ringBearer true (cause := testCause))
  let g704qAfter := g704q0.checkSBA
  let q704Ok :=
    (g704qAfter.player p0).ringBearerId == some rbBear.id &&
    g704qAfter.controlledBy (g704qAfter.object! rbBear.id) p0
  let gSrcEffa :=
    ((gBase.createEffect
      (.layered (.objects #[rbBear.id]) (.control p2) (.whileSourceOnBattlefield srcPerm.id)) (cause := some testCause)).createEffect
      (.layered (.objects #[rbBear.id]) (.control p0) (.whileSourceOnBattlefield srcPerm.id)) (cause := some testCause))
  let gSrcEff := gSrcEffa.record (GameEvent.designation gSrcEffa.turnNumber (gSrcEffa.snapshot (gSrcEffa.object! rbBear.id)) .ringBearer true (cause := testCause))
  let preMoveLog := gSrcEff.log.size
  let (gSrcMoved, _) := gSrcEff.move srcPerm.id .exile (cause := some testCause)
  let moveLogs := gSrcMoved.log.extract preMoveLog gSrcEff.log.size
  let gSrcCeased := gSrcEff.ceaseToExist srcPerm.id (cause := some testCause)
  let srcLeaveOk :=
    (gSrcMoved.player p0).ringBearerId == some rbBear.id &&
    !moveLogs.any (fun s => (s.splitOn p2Name).length > 1) &&
    (gSrcCeased.player p0).ringBearerId == some rbBear.id
  let gFraTurn0a :=
    ((gBase.createEffect
      (.layered (.objects #[rbBear.id]) (.control p2) (.untilNextTurnOf p0)) (cause := some testCause)).createEffect
      (.layered (.objects #[rbBear.id]) (.control p0) (.untilNextTurnOf p0)) (cause := some testCause))
  let gFraTurn0 := gFraTurn0a.record (GameEvent.designation gFraTurn0a.turnNumber (gFraTurn0a.snapshot (gFraTurn0a.object! rbBear.id)) .ringBearer true (cause := testCause))
  let gFraSkip := gFraTurn0.expireUntilTurnCommandEffects p0 (skipControl := true)
  let gFraFull := gFraTurn0.expireUntilTurnCommandEffects p0 (skipControl := false)
  let fraTurnOk :=
    gFraSkip.activeEffects.size == 2 &&
    gFraFull.activeEffects.isEmpty &&
    (gFraFull.player p0).ringBearerId == some rbBear.id
  let simSnapshotsOk := remOk && q704Ok && srcLeaveOk && fraTurnOk

  -- 2b. Pause- & batch-safe `endControlEffectsSimultaneously` (empty `eids` with `preState?`, combined `candExileQueue ++ secondaryExileQueue`
  --     deferred across `.chooseReplacement` pause, and `hadOpenBatch` `queuedLinkedExile` preservation vs outermost flush):
  let gOrph0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g3 hero p0 p1) bear p0 p1)
          leyADef p0 p0)
        leyBDef p0 p0)
      srcDef p0 .exile
  let p1Perms := gOrph0.permanentsOf p1
  let orphCand := p1Perms[0]!
  let orphSec := p1Perms[1]!
  let pLeyA := (gOrph0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let pLeyB := (gOrph0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let exSrc := (gOrph0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!
  let pRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some pLeyA, counterKind := some .plusOnePlusOne }
  let pRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some pLeyB, counterKind := some .plusOnePlusOne }
  let gOrph1 :=
    ((((gOrph0.record (GameEvent.counters gOrph0.turnNumber (some p0) (gOrph0.snapshot orphSec) .charge 1 (cause := testCause))).createEffect
      (.layered (.objects #[orphCand.id]) (.control p0) .indefinite) (cause := some testCause)).createEffect
      (.layered (.objects #[orphSec.id]) (.control p0) (.whileSourceHasCounter orphSec.id .charge)) (cause := some testCause)).concede p1)
  let candEid := gOrph1.activeEffects[0]!.1
  -- (i) Empty `eids` with `preState?` + no open batch flushes `queuedLinkedExile` AND exiles `orphSec`:
  let gOrphRemoved :=
    (gOrph1.record (GameEvent.counters gOrph1.turnNumber (some p0) (gOrph1.snapshot (gOrph1.object! orphSec.id)) .charge 1
      (removed := true) (cause := testCause))).change (.queueLinkedExile #[exSrc.id])
  let gEmptySim := gOrphRemoved.endControlEffectsSimultaneously #[] (cause := some testCause) (preState? := some gOrph1)
  -- Inside an open batch (`hadOpenBatch == true`), `queuedLinkedExile` is NOT flushed prematurely inside the batch:
  let gInBatchHold :=
    gOrphRemoved.withBatchCore (some testCause) fun g =>
      let g' := g.endControlEffectsSimultaneously #[] (cause := some testCause) (preState? := some gOrph1)
      if g'.queuedLinkedExile.isEmpty then panic! "flushed inside open batch" else g'
  -- (ii) Non-empty `eids` (`#[candEid]`) + `orphSec` secondary orphan while `.chooseReplacement` is open queues BOTH into `.endControlExileLoop`
  --      until `.chooseReplacement` resolves:
  let gOrphWithRepl :=
    ((gOrphRemoved.createEffect
      (.replacement {
        id := pRidA, source := some pLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := pRidB, source := some pLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
  let (gPauseOpen, _) := gOrphWithRepl.createOneToken p0 hero (cause := some testCause)
  let gPauseDeferred :=
    gPauseOpen.endControlEffectsSimultaneously #[candEid] (cause := some testCause) (preState? := some gOrph1)
  let bothStillOnBfWhilePaused :=
    (gPauseDeferred.findObject? orphCand.id).any (·.zone == .battlefield) &&
    (gPauseDeferred.findObject? orphSec.id).any (·.zone == .battlefield)
  let gPauseResolved := mustApply (mustApply gPauseDeferred p0 (.chooseReplacement pRidA)) p0 (.chooseReplacement pRidA)
  let endControlPauseBatchOk :=
    (gEmptySim.followMovedToZone? orphSec.id (· == .exile)).isSome &&
    gEmptySim.queuedLinkedExile.isEmpty &&
    (gEmptySim.permanentsOf p0).any (·.name == srcDef.name) &&
    (gInBatchHold.followMovedToZone? orphSec.id (· == .exile)).isSome &&
    bothStillOnBfWhilePaused &&
    (gPauseResolved.followMovedToZone? orphCand.id (· == .exile)).isSome &&
    (gPauseResolved.followMovedToZone? orphSec.id (· == .exile)).isSome

  -- 2c. `Tokens` (`createOneToken`, `createTokenBatches`) & `Movement.becomePrepared` `linkedExile` flushes +
  --     `Leaving.addPlusOnePlusOneTo` `findObject?` guard:
  let gLink0 :=
    insertObject (addPermanent g3 prepCreatureDef p0 p0) bear p0 .exile
  let prepMage := (gLink0.permanentsOf p0)[0]!
  let exBear := (gLink0.objects.filter (fun o => o.zone == .exile && o.owner == p0))[0]!
  let gQueued := gLink0.change (.queueLinkedExile #[exBear.id])
  let (gTokFlush1, _) := gQueued.createOneToken p0 hero (cause := some testCause)
  let batchItem : ProposedTokenBatch := { controller := p0, printed := hero, count := 1 }
  let (gTokFlushBatch, _) := gQueued.createTokenBatches #[batchItem] (cause := some testCause)
  let gPrepFlush := gQueued.becomePrepared prepMage (cause := some testCause)
  let (gStale0, _) := gBase.move rbBear.id .exile (cause := some testCause)
  let preStaleEvs := gStale0.events.size
  let gStaleAfter := gStale0.addPlusOnePlusOneTo rbBear 2 (cause := some testCause)
  let noPhantomCounterEv :=
    !(gStaleAfter.events.extract preStaleEvs gStaleAfter.events.size).any (fun e =>
      match e with | .rules _ (.permanent (.counters ..)) _ _ => true | _ => false)
  let linkedFlushAndGuardsOk :=
    gTokFlush1.queuedLinkedExile.isEmpty &&
    (gTokFlush1.permanentsOf p0).any (·.name == bear.name) &&
    gTokFlushBatch.queuedLinkedExile.isEmpty &&
    (gTokFlushBatch.permanentsOf p0).any (·.name == bear.name) &&
    gPrepFlush.queuedLinkedExile.isEmpty &&
    (gPrepFlush.permanentsOf p0).any (·.name == bear.name) &&
    (gPrepFlush.object! prepMage.id).status.prepared &&
    noPhantomCounterEv

  mustHold40i2 "2a.simSnapshots" simSnapshotsOk &&
  mustHold40i2 "2b.endControlPauseBatch" endControlPauseBatchOk &&
  mustHold40i2 "2c.linkedFlushAndGuards" linkedFlushAndGuardsOk &&
  mustHold40i2 "2.replay"
    (replayOk40i2 #[gRemAfter, g704qAfter, gSrcMoved, gSrcCeased, gFraFull,
      gEmptySim, gInBatchHold, gPauseDeferred, gPauseResolved,
      gTokFlush1, gTokFlushBatch, gPrepFlush, gStaleAfter])

end Phase40Item2EventAlignment

section Phase40Item3EventAlignment

private def mustHold40i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase40Item3EventAlignment failed: {label}"

private def replayOk40i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let srcDef : CardDef := creature "P40i3 Src" ManaCost.empty #["Construct"] 3 3
  let leyADef : CardDef := { name := "P40i3 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P40i3 LeyB", types := #[.enchantment] }
  let noTrampleScope : ObjectScope := .creaturesWithout #[Keyword.trample]

  -- 3a. CR 611.2b–c resolving-effect (`oneShotEffect` & `isTimedResolvingDuration`) Layers 1–7 phase-out scope lock-in
  --     across phase-in vs CR 611.3a `.staticAbility` dynamic scopes & inactive-at-phase-out `.whileSourceHasCounter` exclusion:
  let gPh0 := addPermanent (addPermanent g3 bear p0 p0) srcDef p0 p0
  let phBear := (gPh0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let phSrc := (gPh0.permanentsOf p0).find? (·.name == srcDef.name) |>.get!
  let gPhPre :=
    ((gPh0.createEffect (.layered noTrampleScope (.ptModify 2 2) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[phBear.id]) (.control p2) (.whileSourceHasCounter phSrc.id .charge))
      (cause := some (.gameRule .staticAbility)))
  let gPhOut := gPhPre.phaseOut (gPhPre.object! phBear.id) (cause := some testCause)
  let gWhileOut :=
    ((((((((gPhOut.record (GameEvent.counters gPhOut.turnNumber (some p0) (gPhOut.snapshot (gPhOut.object! phSrc.id)) .charge 1
      (cause := testCause))).createEffect
      (.layered noTrampleScope (.types .add #[.artifact] #[] #[]) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered noTrampleScope (.colors .add { red := true }) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered noTrampleScope (.abilities { keywords := #[Keyword.flying] } .none) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered noTrampleScope (.ptModify 3 3) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered noTrampleScope (.control p1) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered noTrampleScope (.abilities { keywords := #[Keyword.vigilance] } .none) .indefinite)
      (cause := some (.gameRule .staticAbility))).createEffect
      (.layered noTrampleScope (.ptModify 1 1) .indefinite)
      (cause := some (.gameRule .staticAbility)))
  let inactiveAtPhaseOutExcludedWhileOut :=
    gWhileOut.controllerOf (gWhileOut.object! phBear.id) == some p0
  let gPhIn := gWhileOut.phaseIn (gWhileOut.object! phBear.id) (cause := some testCause)
  let phBearIn := gPhIn.object! phBear.id
  let phScopeLockOk :=
    inactiveAtPhaseOutExcludedWhileOut &&
    !phBearIn.status.phasedOut &&
    gPhIn.controllerOf phBearIn == some p2 &&
    !gPhIn.hasType phBearIn .artifact &&
    !(gPhIn.colors phBearIn).red &&
    !KeywordAbility.hasFlying (gPhIn.effectiveKeywords phBearIn) &&
    KeywordAbility.hasVigilance (gPhIn.effectiveKeywords phBearIn) &&
    gPhIn.power phBearIn == 5 &&
    gPhIn.toughness phBearIn == 5

  -- 3b. 2HG CR 702.26n / CR 805.4a `departedNextTurnWouldHaveBegunSince`:
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
    seed := 403
    startingPlayer := some 0
  }
  let gTeams0 : Game :=
    match Start.start cfg3Teams with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  let gTeams1 := addPermanent gTeams0 bear ⟨2⟩ ⟨2⟩
  let tBear := (gTeams1.permanentsOf ⟨2⟩)[0]!
  let gTeamsSteal :=
    (gTeams1.createEffect (.layered (.objects #[tBear.id]) (.control ⟨1⟩) .indefinite) (cause := some testCause))
  let gTeamsPhOut := gTeamsSteal.phaseOut (gTeamsSteal.object! tBear.id) (cause := some testCause)
  -- When `⟨1⟩` leaves during Team A's turn (`activePlayer == ⟨0⟩`) while teammate `⟨0⟩` remains alive,
  -- `tBear` does NOT falsely phase in on Team B (`⟨2⟩, ⟨3⟩`) or Team C (`⟨4⟩, ⟨5⟩`), and phases in on `⟨0⟩`'s next shared turn:
  let gMate1Left :=
    (gTeamsPhOut.record (GameEvent.playerLost gTeamsPhOut.turnNumber ⟨1⟩ .conceded (cause := some testCause))).record
      (GameEvent.playerLeftGame gTeamsPhOut.turnNumber ⟨1⟩ (cause := some testCause))
  let gTeamAliveMateB0 := gMate1Left.startNextTurnAndBegin
  let gTeamAliveMateB1 := gTeamAliveMateB0.startNextTurnAndBegin
  let gTeamAliveMateC0 := gTeamAliveMateB1.startNextTurnAndBegin
  let gTeamAliveMateC1 := gTeamAliveMateC0.startNextTurnAndBegin
  let gTeamAliveMateBack := gTeamAliveMateC1.startNextTurnAndBegin
  let phasedInOnLivingMateTurn :=
    gTeamAliveMateB0.activePlayer == ⟨2⟩ && (gTeamAliveMateB0.object! tBear.id).status.phasedOut &&
    gTeamAliveMateB1.activePlayer == ⟨3⟩ && (gTeamAliveMateB1.object! tBear.id).status.phasedOut &&
    gTeamAliveMateC0.activePlayer == ⟨4⟩ && (gTeamAliveMateC0.object! tBear.id).status.phasedOut &&
    gTeamAliveMateC1.activePlayer == ⟨5⟩ && (gTeamAliveMateC1.object! tBear.id).status.phasedOut &&
    gTeamAliveMateBack.activePlayer == ⟨0⟩ && !(gTeamAliveMateBack.object! tBear.id).status.phasedOut
  -- When BOTH `⟨0⟩` and `⟨1⟩` leave on Team A's turn (`concede ⟨0⟩` concedes the team per CR 810.8a),
  -- `endingCurrentShared` keeps `tBear` phased out through Team B (`⟨2⟩, ⟨3⟩`) and Team C (`⟨4⟩, ⟨5⟩`)
  -- and phases it in when departed Team A's next turn would have begun (before Team B's second turn):
  let gBothGone := mustApply gTeamsPhOut ⟨0⟩ .concede
  let gAfterTurnB0 := gBothGone.startNextTurnAndBegin
  let gAfterTurnB1 := gAfterTurnB0.startNextTurnAndBegin
  let outAcrossTeamB :=
    (gAfterTurnB0.object! tBear.id).status.phasedOut && gAfterTurnB0.activePlayer == ⟨2⟩ &&
    (gAfterTurnB1.object! tBear.id).status.phasedOut && gAfterTurnB1.activePlayer == ⟨3⟩
  let gAfterTurnC0 := gAfterTurnB1.startNextTurnAndBegin
  let gAfterTurnC1 := gAfterTurnC0.startNextTurnAndBegin
  let outAcrossTeamC :=
    (gAfterTurnC0.object! tBear.id).status.phasedOut && gAfterTurnC0.activePlayer == ⟨4⟩ &&
    (gAfterTurnC1.object! tBear.id).status.phasedOut && gAfterTurnC1.activePlayer == ⟨5⟩
  let gAfterWrapPastA := gAfterTurnC1.startNextTurnAndBegin
  let inAfterSkipTeamA :=
    !(gAfterWrapPastA.object! tBear.id).status.phasedOut && gAfterWrapPastA.activePlayer == ⟨2⟩
  let twoHgPhaseInOk :=
    phasedInOnLivingMateTurn &&
    outAcrossTeamB &&
    outAcrossTeamC &&
    inAfterSkipTeamA

  -- 3c. Mid-pause `nextP` departure in `Turns.continueStartNextTurn`, `g.over` entry guards across `Turns`,
  --     and `Turns.beginTurn` deferred protection/life-lock expiry across control-end pause & `pendingReplacement.isSome`:
  let gMid0 :=
    (g3.createEffect (.layered noTrampleScope (.ptModify 2 2) (.untilNextTurnOf p1)) (cause := some testCause)).concede p1
  let gMidNext := gMid0.continueStartNextTurn p1 #[] true
  let midNextOk :=
    gMidNext.activePlayer == p2 &&
    gMidNext.activeEffects.isEmpty
  let gOver := g3.record (GameEvent.gameEnded g3.turnNumber (.won p0) (cause := some testCause))
  let turnsOverGuardsOk :=
    gOver.expireUntilNextTurnEffects p0 == gOver &&
    gOver.continueStartNextTurn p1 #[] true == gOver &&
    gOver.runUntapStepAfterPhaseIn == gOver &&
    gOver.beginStep .upkeep == gOver &&
    gOver.beginTurnAfterStartExpiry == gOver &&
    gOver.beginTurn == gOver
  let gBt0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g3 srcDef p0 p1) bear p0 p0)
        leyADef p0 p0)
      leyBDef p0 p0
  let btCage := (gBt0.permanentsOf p1)[0]!
  let btBear := (gBt0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let btLeyA := (gBt0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let btLeyB := (gBt0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let btRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some btLeyA, counterKind := some .plusOnePlusOne }
  let btRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some btLeyB, counterKind := some .plusOnePlusOne }
  let gBtSetup :=
    (((((gBt0.createEffect
      (.layered (.objects #[btCage.id]) (.control p0) (.untilNextTurnOf p0)) (cause := some testCause)).createEffect
      (.protectionFromEverything p0) (cause := some testCause)).concede p1).createEffect
      (.replacement {
        id := btRidA, source := some btLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := btRidB, source := some btLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
  let (gBtPrePaused, _) :=
    (gBtSetup.move btBear.id .exile none (cause := some testCause)).1.move
      (gBtSetup.move btBear.id .exile none (cause := some testCause)).2 .battlefield (some p0) (cause := some testCause)
  let gBtPaused := gBtPrePaused.beginTurn
  let protStillActiveWhilePaused :=
    (match gBtPaused.pending with | .chooseReplacement .. => true | _ => false) &&
    gBtPaused.activeEffects.any (fun (_, e) => e == .protectionFromEverything p0)
  let gBtResumed := mustApply gBtPaused p0 (.chooseReplacement btRidA)
  let protExpiredAfterResume :=
    !gBtResumed.activeEffects.any (fun (_, e) => e == .protectionFromEverything p0) &&
    (gBtResumed.permanentsOf p0).all (·.id != btCage.id) &&
    gBtResumed.step == .upkeep
  let gBtContOnly :=
    ((g3.createEffect (.protectionFromEverything p0) (cause := some testCause)).chainPendingReplacement
      (.restorePending .none false (some "pre-beginTurn-cont"))).beginTurn
  let contOnlyDeferredOk :=
    gBtContOnly.activeEffects.any (fun (_, e) => e == .protectionFromEverything p0) &&
    gBtContOnly.pendingReplacement.isSome
  let gBtContResumed :=
    match gBtContOnly.pendingReplacement with
    | some cont => (gBtContOnly.change (.pendingReplacement none)).resumePendingReplacement cont
    | none => gBtContOnly
  let contOnlyResumedOk :=
    !gBtContResumed.activeEffects.any (fun (_, e) => e == .protectionFromEverything p0) &&
    gBtContResumed.step == .upkeep
  let turnsGuardsAndDeferOk :=
    midNextOk &&
    turnsOverGuardsOk &&
    protStillActiveWhilePaused &&
    protExpiredAfterResume &&
    contOnlyDeferredOk &&
    contOnlyResumedOk

  mustHold40i3 "3a.phScopeLock" phScopeLockOk &&
  mustHold40i3 "3b.twoHgPhaseIn" twoHgPhaseInOk &&
  mustHold40i3 "3c.turnsGuardsAndDefer" turnsGuardsAndDeferOk &&
  mustHold40i3 "3.replay"
    (replayOk40i3 #[gWhileOut, gPhIn, gTeamAliveMateBack,
      gAfterTurnB1, gAfterTurnC1, gAfterWrapPastA,
      gMidNext, gOver, gBtPaused, gBtResumed, gBtContOnly, gBtContResumed])

end Phase40Item3EventAlignment

section Phase40Item4EventAlignment

private def mustHold40i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase40Item4EventAlignment failed: {label}"

private def replayOk40i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 4a. `fid == sid` `source*ForCost` detection, `.tapTwoUntappedArtifacts` mid-batch unpayability,
  --     and mid-cost `findObject?` + single `outer?` synchronous reversal in `ActivationCosts` / `Casting`:
  let artDefA : CardDef := { name := "P40i4 ArtA", types := #[.artifact] }
  let storyAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.tapSelf, .removeCounters (.exact 1) (some .story) .self]
    effect := Effect.gainLife 2
  }
  let storyRelicDef : CardDef := {
    name := "P40i4 StoryRelic"
    types := #[.artifact]
    activatedAbilities := #[storyAb]
  }
  let gFid0 := addPermanent (insertObject g3 bear p0 (.hand p0)) artDefA p0 p0
  let fidArt := (gFid0.permanentsOf p0)[0]!
  let fidHandId := (gFid0.player p0).hand.back!
  let fidHandObj := gFid0.object! fidHandId
  let gTappedSelf := gFid0.becomeTapped fidArt (cause := some (.costPayment .tap p0 (some fidArt.id)))
  let gCntSelf :=
    gTappedSelf.recordPutCounters fidArt.id .charge 1 (some p0)
      (cause := some (.costPayment .removeCounters p0 (some fidArt.id)))
  let gSacSelf :=
    gCntSelf.sacrificeToGraveyard (gCntSelf.object! fidArt.id) "sac"
      (cause := some (.costPayment .sacrifice p0 (some fidArt.id)))
  let gDiscSelf :=
    (gSacSelf.move fidHandObj.id (.graveyard p0) none (verb := some .discard) (actor := some p0)
      (cause := some (.costPayment .discard p0 (some fidHandObj.id)))).1
  let fidEqSidOk :=
    gDiscSelf.sourceTappedForCost fidArt.id (some fidArt.id) &&
    gDiscSelf.sourceCounterCostPaidFor fidArt.id (some fidArt.id) .removeCounters &&
    gDiscSelf.sourceSacrificedForCost fidArt.id (some fidArt.id) &&
    gDiscSelf.sourceDiscardedFromHandForCost fidHandObj.id (some fidHandObj.id)

  -- `.tapTwoUntappedArtifacts` mid-batch failure closes batch cleanly and reverses proposal once:
  let gMarker0 := addPermanent g3 bear p2 p2
  let markerFromId := (gMarker0.permanentsOf p2)[0]!.id
  let (gMarkerEx, _) := gMarker0.move markerFromId .exile none (cause := some testCause)
  let gTap2Base := addPermanent gMarkerEx artDefA p0 p0
  let tap2Art := (gTap2Base.permanentsOf p0)[0]!
  let propTap2 : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := tap2Art.id
    sourceId := some tap2Art.id
    original := tap2Art
    originalSnapshot := gTap2Base.snapshot tap2Art
    kind := .activatedAbility
  }
  let outerTap2 : PendingReplacement := .finishPostStep (.logExiledIfInExile markerFromId "outer-tap2")
  let gTap2Pre :=
    (gTap2Base.chainPendingReplacement outerTap2).changes
      #[.saveProposalCheckpoint, .pendingReplacement none, .proposedSpell (some propTap2)]
  let (gTap2Abort, tap2PaidOk) :=
    gTap2Pre.payCostPickItemsChecked p0 (some tap2Art.id) (some tap2Art.id)
      .tapTwoUntappedArtifacts #[tap2Art.id, tap2Art.id]
      (outerToRestore? := some outerTap2)
  let tap2MidBatchAbortOk :=
    !tap2PaidOk &&
    gTap2Abort.currentBatch.isNone &&
    gTap2Abort.proposedSpell.isNone &&
    gTap2Abort.proposalCheckpoint.isNone &&
    !(gTap2Abort.object! tap2Art.id).status.tapped &&
    (gTap2Abort.log.filter (·.endsWith "outer-tap2")).size == 1

  -- Mid-cost counter removal exiling stolen source reverses cleanly via `requireLiveSource` without orphan `.endProposalAction`:
  let gStory0 := addPermanent gMarkerEx storyRelicDef p0 p1
  let storySrc := (gStory0.permanentsOf p1)[0]!
  let gStoryReady :=
    (((gStory0.recordPutCounters storySrc.id .story 1 (some p1) (cause := some testCause)).createEffect
      (.layered (.objects #[storySrc.id]) (.control p0) (.whileSourceHasCounter storySrc.id .story))
      (cause := some (.gameRule .staticAbility))).concede p1)
  let gStoryWithOuter :=
    gStoryReady.chainPendingReplacement (.finishPostStep (.logExiledIfInExile markerFromId "outer-story"))
  let gStoryAfterAct := mustApply gStoryWithOuter p0 (.activate storySrc.id 0)
  let midCostStoryAbortOk :=
    gStoryAfterAct.proposedSpell.isNone &&
    gStoryAfterAct.proposalCheckpoint.isNone &&
    (gStoryAfterAct.findObject? storySrc.id).isNone &&
    (gStoryAfterAct.log.filter (·.endsWith "outer-story")).size == 1 &&
    !gStoryAfterAct.events.back?.any (fun e => e.change == .engine .endProposalAction)
  let item4aOk :=
    mustHold40i4 "4a.fidEqSid" fidEqSidOk &&
    mustHold40i4 "4a.tap2MidBatch" tap2MidBatchAbortOk &&
    mustHold40i4 "4a.midCostStory" midCostStoryAbortOk

  -- 4b. `ManaAbilities`: synchronous unpayable second pick returns `.error`, and `abortDepartedManaAbilityCont`
  --     respects `hasFollowingSeq` & dead-player priority fallback:
  let comboManaAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.sacrifice (.exact 1) (.filter (.hasType .artifact)), .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
    effect := Effect.addMana #[.colorless]
  }
  let comboManaDef : CardDef := {
    name := "P40i4 ManaAltar"
    types := #[.enchantment]
    activatedAbilities := #[comboManaAb]
  }
  let gMana0 :=
    addPermanent (addPermanent (addPermanent gMarkerEx comboManaDef p0 p0) artDefA p0 p0) bear p1 p1
  let altarObj := (gMana0.permanentsOf p0).find? (·.name == comboManaDef.name) |>.get!
  let fodderArt := (gMana0.permanentsOf p0).find? (·.name == artDefA.name) |>.get!
  let stolenBear := (gMana0.permanentsOf p1)[0]!
  let gManaSteal :=
    gMana0.createEffect
      (.layered (.objects #[stolenBear.id]) (.control p0) (.whileSourceOnBattlefield fodderArt.id))
      (cause := some (.gameRule .staticAbility))
  let syncManaErrOk :=
    match gManaSteal.activateManaAbility p0 altarObj.id 0 #[.colorless] #[fodderArt.id, stolenBear.id] with
    | .error _ => true
    | .ok _ => false
  -- `hasFollowingSeq` in `resumePendingReplacement` `.seq` avoids granting priority before outer `rest` runs,
  -- and dead-player fallback grants priority to living `priorityInstead` (`p1`) instead of departed `p0`:
  let gSeqAbort0 := (gMana0.concede p0).change (.priority p2)
  let gSeqAborted :=
    gSeqAbort0.resumePendingReplacement
      (.seq
        (.finishActivateManaAbilityPostSac p0 altarObj.id altarObj.printed.name
          (gMana0.snapshot altarObj) #[.colorless] false (some 0) .none 0 false .none)
        (.finishPostStep (.logExiledIfInExile markerFromId "after-mana-abort-seq")))
  let hasFollowingSeqOk :=
    gSeqAborted.priority == p2 &&
    (gSeqAborted.log.filter (·.endsWith "after-mana-abort-seq")).size == 1
  let gDeadFallback :=
    ((g3.concede p0).change (.priority p0)).finishActivateManaAbilityPostSac
      p0 ⟨9999⟩ "GoneSrc" (gMana0.snapshot altarObj)
      #[.colorless] false none .none 0 false .none
  let deadPlayerFallbackOk :=
    gDeadFallback.priority == p1 &&
    gDeadFallback.stillInGame p1
  let item4bOk := syncManaErrOk && hasFollowingSeqOk && deadPlayerFallbackOk

  -- 4c. Zero-mana `.turnFaceUp`, `sacrificeForActivation` `needsDiscardCard`,
  --     and CR 116.2b `caster` priority across post-turn-face-up `linkedExile` `.chooseReplacement` pause:
  let morphZero : CardDef :=
    { creature "P40i4 ZeroMorph" ManaCost.empty #["Human"] 3 3 with keywords := #[.morph CostSpec.empty] }
  let leyADef4 : CardDef := { name := "P40i4 LeyA", types := #[.enchantment] }
  let leyBDef4 : CardDef := { name := "P40i4 LeyB", types := #[.enchantment] }
  let gMfZero0 := (addPermanent g3 morphZero p1 p1).change (.priority p1)
  let mfZeroId := (gMfZero0.permanentsOf p1)[0]!.id
  let gMfZeroDown := setFaceDown gMfZero0 mfZeroId true
  let gMfZeroActIdx :=
    ((gMfZeroDown.activatedAbilitiesOf (gMfZeroDown.object! mfZeroId)).findIdx?
      (fun ab => ab.effect.body == .permanent (.turnFaceUp .this))).getD 0
  let gMfZeroUp := mustApply gMfZeroDown p1 (.activate mfZeroId gMfZeroActIdx)
  let zeroMorphPrioOk :=
    !(gMfZeroUp.object! mfZeroId).status.faceDown &&
    gMfZeroUp.priority == p1 &&
    gMfZeroUp.proposalCheckpoint.isNone

  let gMfPause0 :=
    addPermanent (addPermanent (addPermanent (addPermanent g3 morphZero p1 p1) bear p1 p1) leyADef4 p1 p1) leyBDef4 p1 p1
  let mfPId := (gMfPause0.permanentsOf p1).find? (·.name == morphZero.name) |>.get!.id
  let mfPBear := (gMfPause0.permanentsOf p1).find? (·.name == bear.name) |>.get!
  let mfLeyA := (gMfPause0.permanentsOf p1).find? (·.name == leyADef4.name) |>.get!.id
  let mfLeyB := (gMfPause0.permanentsOf p1).find? (·.name == leyBDef4.name) |>.get!.id
  let mfRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some mfLeyA, counterKind := some .plusOnePlusOne }
  let mfRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some mfLeyB, counterKind := some .plusOnePlusOne }
  let (gMfExiled, exiledBearId) := gMfPause0.move mfPBear.id .exile none (cause := some testCause)
  let gMfPauseReady :=
    ((((setFaceDown gMfExiled mfPId true).createEffect
      (.replacement {
        id := mfRidA, source := some mfLeyA, controller := some p1, affectedPlayer := p1,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := mfRidB, source := some mfLeyB, controller := some p1, affectedPlayer := p1,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).changes
      #[.priority p1, .queueLinkedExile #[exiledBearId]])
  let (gMfTurnPaused, _) := gMfPauseReady.completeTurnFaceUp p1 mfPId
  let gMfTurnResumed := mustApply gMfTurnPaused p1 (.chooseReplacement mfRidA)
  let morphReconcileCasterPrioOk :=
    (match gMfTurnPaused.pending with | .chooseReplacement chooser _ => chooser == p1 | _ => false) &&
    !(gMfTurnResumed.object! mfPId).status.faceDown &&
    gMfTurnResumed.activePlayer == p0 &&
    gMfTurnResumed.priority == p1

  let gSacDisc0 := insertObject (addPermanent (addPermanent g3 morphZero p0 p0) bear p0 p0) hero p0 (.hand p0)
  let sdMorphId := (gSacDisc0.permanentsOf p0).find? (·.name == morphZero.name) |>.get!.id
  let sdFodderId := (gSacDisc0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let sdHandCardId := (gSacDisc0.player p0).hand.back!
  let gSacDiscDown := setFaceDown gSacDisc0 sdMorphId true
  let sdMorphObj := gSacDiscDown.object! sdMorphId
  let propSacDisc : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := sdMorphId
    sourceId := some sdMorphId
    original := sdMorphObj
    originalSnapshot := gSacDiscDown.snapshot sdMorphObj
    kind := .turnFaceUp
    needsSacrificeOther := true
    needsDiscardCard := true
  }
  let gSacDiscPrompt :=
    gSacDiscDown.changes #[.saveProposalCheckpoint, .proposedSpell (some propSacDisc), .pending (.sacrificePermanent p0 sdMorphId)]
  let gAfterSac := mustApply gSacDiscPrompt p0 (.sacrifice sdFodderId)
  let gAfterDisc := mustApply gAfterSac p0 (.discard sdHandCardId)
  let propTurnCp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := sdMorphId
    sourceId := some sdMorphId
    original := sdMorphObj
    originalSnapshot := gSacDiscDown.snapshot sdMorphObj
    kind := .turnFaceUp
  }
  let gTurnCp0 := gSacDiscDown.changes #[.saveProposalCheckpoint, .proposedSpell (some propTurnCp)]
  let gTurnCpDone : Game :=
    match gTurnCp0.continueCostPicks propTurnCp #[] false false (some false) with
    | .ok g' => g'
    | .error e => panic! e
  let gTurnFinDone : Game :=
    match gTurnCp0.finishProposedSpellCosts .finalize true false false with
    | .ok g' => g'
    | .error e => panic! e
  let turnCpAndFinOk :=
    !(gTurnCpDone.object! sdMorphId).status.faceDown &&
    gTurnCpDone.proposalCheckpoint.isNone &&
    !(gTurnFinDone.object! sdMorphId).status.faceDown &&
    gTurnFinDone.proposalCheckpoint.isNone
  let sacThenDiscardMorphOk :=
    gAfterSac.pending == .discardForAdditionalCost p0 &&
    (gAfterSac.object! sdMorphId).status.faceDown &&
    gAfterDisc.pending == .none &&
    !(gAfterDisc.object! sdMorphId).status.faceDown &&
    gAfterDisc.proposalCheckpoint.isNone
  let item4cOk := zeroMorphPrioOk && morphReconcileCasterPrioOk && sacThenDiscardMorphOk && turnCpAndFinOk

  -- 4d. Combined `loyaltyX` + `removePlusOneX` in `CastSpell.announceX` and `Agent.choose` / `Agent.maxAffordableX` `exclude`:
  let pwXAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty .minusX, .removeCounters .anyNumber (some .plusOnePlusOne) .self]
    effect := Effect.gainLife 1
  }
  let pwXDef : CardDef := {
    name := "P40i4 HybridPW"
    types := #[.planeswalker, .creature]
    subtypes := #["Construct"]
    power := some (.fixed 2)
    toughness := some (.fixed 2)
    loyalty := some 5
    activatedAbilities := #[pwXAb]
  }
  let gPw0 := addPermanent g3 pwXDef p0 p0
  let pwObj := (gPw0.permanentsOf p0)[0]!
  let gPwCounters :=
    (gPw0.recordPutCounters pwObj.id .loyalty 5 (some p0) (cause := some testCause)).recordPutCounters
      pwObj.id .plusOnePlusOne 2 (some p0) (cause := some testCause)
  let gPwChooseX := mustApply gPwCounters p0 (.activate pwObj.id 0)
  -- `loyaltyCounters >= 5`, `plusOnePlusOne == 2`: `announceX` rejects `x = 3` (`plusOnePlusOne < 3`),
  -- and `Agent.choose` clamps `min (loyalty - 1) 2 == 2`:
  let announceRejectsOverPlusOne :=
    match gPwChooseX.announceX p0 3 with
    | .error _ => true
    | .ok _ => false
  let agentClampsCombinedX :=
    match Agent.choose gPwChooseX p0 with
    | some (.chooseX 2) => true
    | _ => false

  -- `Agent.maxAffordableX` `exclude` excludes a `{T}` mana dork when tapping that dork for its own `{X}, {T}` ability:
  let tapXAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.mana { symbols := #[.x] }, .tapSelf]
    effect := Effect.plusOneX
  }
  let manaAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.tapSelf]
    effect := Effect.addMana #[.colored .green]
  }
  let dorkXDef : CardDef := {
    creature "P40i4 DorkX" ManaCost.empty #["Elf", "Druid"] 1 1 with
    keywords := #[Keyword.haste]
    activatedAbilities := #[manaAb, tapXAb]
  }
  let gDorkOnly := addPermanent g3 dorkXDef p0 p0
  let dorkObj := (gDorkOnly.permanentsOf p0)[0]!
  let gDorkChooseXTap := mustApply gDorkOnly p0 (.activate dorkObj.id 1)
  let gDorkChooseXNoTap :=
    gDorkChooseXTap.change (.proposedSpell (gDorkChooseXTap.proposedSpell.map (fun pr => { pr with tapSource := false })))
  let maxExclZero :=
    (match Agent.choose gDorkChooseXTap p0 with | some (.chooseX 0) => true | _ => false) &&
    (match Agent.choose gDorkChooseXNoTap p0 with | some (.chooseX 1) => true | _ => false)
  let dorkNoZeroPlusOneAct :=
    match Agent.choose gDorkOnly p0 with
    | some (.activate oid 1) => oid != dorkObj.id
    | _ => true
  let item4dOk :=
    announceRejectsOverPlusOne &&
    agentClampsCombinedX &&
    maxExclZero &&
    dorkNoZeroPlusOneAct

  mustHold40i4 "4a.fidAndMidCost" item4aOk &&
  mustHold40i4 "4b.manaAbortAndSyncErr" item4bOk &&
  mustHold40i4 "4c.turnFaceUpAndSacDiscard" item4cOk &&
  mustHold40i4 "4d.combinedXAndExclude" item4dOk &&
  mustHold40i4 "4.replay"
    (replayOk40i4 #[gDiscSelf, gTap2Abort, gStoryAfterAct, gManaSteal,
      gSeqAborted, gDeadFallback, gMfZeroUp, gMfTurnPaused, gMfTurnResumed,
      gAfterSac, gAfterDisc, gTurnCpDone, gTurnFinDone, gPwChooseX, gDorkOnly])

end Phase40Item4EventAlignment

end Mtg.Engine.EventTests
