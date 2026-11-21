import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase49Item1EventAlignment

private def mustHold49i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase49Item1EventAlignment failed: {label}"

private def replayOk49i1 (gs : Array Game) : Bool :=
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
    name := "P49i1 ZeroBolt"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellEffect := some (Effect.gainLife 1)
  }
  let bigSorcDef : CardDef := {
    name := "P49i1 HugeSorc"
    manaCost := ManaCost.ofGeneric 6
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 1)
  }
  let oddEvenDef : CardDef := {
    name := "P49i1 OddStatue"
    types := #[.artifact]
    staticAbilities := #[.asEntersChooseOddEven]
  }
  let zeroToughDef : CardDef := creature "P49i1 Germ" ManaCost.empty #["Germ"] 0 0

  -- 1a(i). `Decisions.chooseReplacement` invokes `finishFraChoice` when `reopenDeferredExileCasts`
  --        ceases an exhausted/uncastable `pendingFreeCopies` stash (`pending == .none`),
  --        running SBA (`0/0` Germ dies), stacking waiting triggers, and granting priority:
  let gCopy0 := insertObject (addPermanent g4 zeroToughDef p1 p1) bigSorcDef p0 (.hand p0)
  let germId := (gCopy0.permanentsOf p1)[0]!.id
  let (gCopy1, copyExId) :=
    gCopy0.move (gCopy0.player p0).hand.back! .exile none (isCopy := some true) (cause := some testCause)
  let gCopyAnchor := addPermanent gCopy1 ({ name := "P49i1 Anchor", types := #[.artifact] }) p0 p0
  let anchorObj := (gCopyAnchor.permanentsOf p0).back!
  let wtGain1 : WaitingTrigger := {
    controller := p0
    source := anchorObj
    ability := .triggered .youGainLife { resolution := .gainLife (.fixed 1), phrase := "Gain 1 life." }
    eventCause := some testCause
  }
  let gRepEmpty0 := insertObject gCopyAnchor oddEvenDef p0 (.hand p0)
  let (gRepEmptyPaused, _) :=
    gRepEmpty0.putOntoBattlefield (gRepEmpty0.player p0).hand.back! p0 (cause := some testCause)
  let gRepEmptyDone :=
    mustApply
      (gRepEmptyPaused.changes (
        #[.enqueueWaitingTriggers #[wtGain1]] ++
        (if gRepEmptyPaused.continuations.isEmpty then #[.pushContinuationFrame {}] else #[]) ++
        #[.continuation (.pendingFreeCopies (some (p0, #[copyExId], 0, 0)))]))
      p0 (.chooseMode 0)

  -- 1a(ii). `Leaving.playerLeavesGameCore` attaches `.finishFraChoice` onto `outerPendingReplacements`
  --         when departure pauses on a linked-exile return replacement (`oddEvenDef` returning to `p1`
  --         when `p2` concedes) while `p0` holds a surviving `pendingMayCastFromExile` stash:
  let gLink0 := addPermanent (insertObject g4 zeroInstDef p0 .exile) oddEvenDef p1 p1
  let exInstId := (gLink0.objects.filter (fun (o : GameObject) => o.zone == .exile)).back!.id
  let oddPerm := (gLink0.permanentsOf p1).back!
  let gLink1 := addPermanent gLink0 ({ name := "P49i1 Cage", types := #[.artifact] }) p2 p2
  let cageId := (gLink1.permanentsOf p2).back!.id
  let gLink2 := gLink1.exileUntilSourceLeaves (some cageId) oddPerm (cause := some testCause)
  let gLink3 :=
    gLink2.changes #[
      .pushContinuationFrame { pendingMayCastFromExile := some (p0, #[exInstId], 1) },
      .pending (.mayPayGeneric p2 1) ]
  let gLinkPaused := mustApply gLink3 p2 .concede
  let gLinkReopened := mustApply gLinkPaused p1 (.chooseMode 0)

  -- 1a(iii). `Casting.finishPostCast` & `Decisions` probes (`continuationGrantsPriority` /
  --          `priorityRecipientOfContinuation?`) preserve cross-seat `pendingMayCastFromExile`,
  --          intercept in `receivePriority`, and clear `pendingFreeCopies` before `beginFraChoice`:
  let gCross0 := insertObject (insertObject g4 zeroInstDef p0 .exile) zeroInstDef p1 (.hand p1)
  let crossExId := (gCross0.objects.filter (fun (o : GameObject) => o.zone == .exile)).back!.id
  let gCrossP1Prio :=
    (mustApply gCross0 p0 .pass).change
      (.pushContinuationFrame { pendingMayCastFromExile := some (p0, #[crossExId], 1) })
  let crossGrantsBefore :=
    gCrossP1Prio.continuationGrantsPriority false (.finishPostCast p1 true false false)
  let crossRecipBefore :=
    gCrossP1Prio.priorityRecipientOfContinuation? false (.finishPostCast p1 true false false)
  let gCrossAfterP1Cast := mustApply gCrossP1Prio p1 (.cast (gCrossP1Prio.player p1).hand.back!)

  let gEmptyStashP1 :=
    (mustApply gCross0 p0 .pass).change
      (.pushContinuationFrame { pendingMayCastFromExile := some (p0, #[], 1) })
  let emptyStashGrants :=
    gEmptyStashP1.continuationGrantsPriority false (.finishPostCast p1 true false false)
  let emptyStashRecip :=
    gEmptyStashP1.priorityRecipientOfContinuation? false (.finishPostCast p1 true false false)

  let gFreeCopyCast0 := insertObject (insertObject g4 zeroInstDef p0 (.hand p0)) zeroInstDef p0 (.hand p0)
  let (gFreeCopyCast1, freeCopyId) :=
    gFreeCopyCast0.move (gFreeCopyCast0.player p0).hand.back! .exile none (isCopy := some true) (cause := some testCause)
  let gFreeCopyCast2 :=
    gFreeCopyCast1.change (.pushContinuationFrame { pendingFreeCopies := some (p0, #[freeCopyId], 5, 1) })
  let gAfterP0CastFreeCopy := mustApply gFreeCopyCast2 p0 (.cast (gFreeCopyCast2.player p0).hand.back!)

  -- Departed grantee (`!g.stillInGame p2`): `finishPostCast p2 (grantPriority := false)` and
  -- `Decisions` probes clear `p2`'s own `pendingMayCastFromExile` / `pendingFreeCopies` stashes
  -- and cease leftover exiled copies without opening `.beginFraChoice`, letting `completeActiveResolutions` pop:
  let gDepStash0 := mustApply (insertObject (insertObject g4 zeroInstDef p0 .exile) zeroInstDef p0 (.hand p0)) p2 .concede
  let depExInstId := (gDepStash0.objects.filter (fun (o : GameObject) => o.zone == .exile)).back!.id
  let (gDepStash1, depFreeCopyId) :=
    gDepStash0.move (gDepStash0.player p0).hand.back! .exile none (isCopy := some true) (cause := some testCause)
  let gDepStash2 :=
    gDepStash1.change
      (.pushContinuationFrame {
        pendingMayCastFromExile := some (p2, #[depExInstId], 1)
        pendingFreeCopies := some (p2, #[depFreeCopyId], 5, 1)
      })
  let depStashGrants :=
    gDepStash2.continuationGrantsPriority false (.finishPostCast p2 true false false)
  let depStashRecip :=
    gDepStash2.priorityRecipientOfContinuation? false (.finishPostCast p2 true false true)
  let gDepPostCastDone :=
    (gDepStash2.finishPostCast p2 (grantPriority := false)).completeActiveResolutions

  let item1aOk :=
    mustHold49i1 "1a_chooseReplacementEmptyStashFinishFraChoice"
      ((gRepEmptyDone.findObject? copyExId).isNone &&
       (gRepEmptyDone.findObject? germId).isNone &&
       (gRepEmptyDone.player p1).graveyard.any (fun id => (gRepEmptyDone.object! id).name == zeroToughDef.name) &&
       gRepEmptyDone.stack.size == 1 &&
       gRepEmptyDone.pending == .none) &&
    mustHold49i1 "1a_leavingPostBodyReplacementDeferredReopen"
      ((match gLinkPaused.pending with | .chooseReplacement q _ => q == p1 | _ => false) &&
       gLinkReopened.pending == .fraChoice p0 (.mayCastUpToFromExile #[exInstId] 1)) &&
    mustHold49i1 "1a_crossSeatFinishPostCastAndFreeCopiesClear"
      (!crossGrantsBefore &&
       crossRecipBefore.isNone &&
       gCrossAfterP1Cast.pending == .fraChoice p0 (.mayCastUpToFromExile #[crossExId] 1) &&
       gCrossAfterP1Cast.pendingMayCastFromExile.isNone &&
       emptyStashGrants &&
       emptyStashRecip == some p1 &&
       gAfterP0CastFreeCopy.pending == .fraChoice p0 (.castCopiesFree #[freeCopyId] 5 1) &&
       gAfterP0CastFreeCopy.pendingFreeCopies.isNone &&
       depStashGrants &&
       depStashRecip == some p0 &&
       gDepPostCastDone.pending == .none &&
       gDepPostCastDone.pendingMayCastFromExile.isNone &&
       gDepPostCastDone.pendingFreeCopies.isNone &&
       (gDepPostCastDone.findObject? depFreeCopyId).isNone &&
       gDepPostCastDone.continuations.isEmpty)

  -- 1b(i). `StateBasedActions.checkSBACountedWithLeavesCore` folds `outerAfterIn?` AFTER
  --        restoring `saved?` (`Pending.mayPayGeneric p1 1`), rather than executing `outerAfterIn?` early:
  let gSbaOuter0 :=
    (g4.loseLife p2 20 (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pending (.mayPayGeneric p1 1) ]
  let (gSbaOuterPaused, _, _, _, _, _) :=
    gSbaOuter0.checkSBACountedWithLeavesCore (outerAfterIn? := some (.gainLife p0 3 (some testCause)))
  let gSbaOuterAfterDecline := mustApply gSbaOuterPaused p1 .decline

  -- 1b(ii). `Decisions` `.restorePending` probes on `.resolveRandom (.chooseObject #[onePermId, missingId])`
  --         (< 2 live objects -> non-pausing pop of outer `.receivePriority p1`) and `rewindProposal`:
  let gOnePerm := addPermanent g4 bear p0 p0
  let onePermId := (gOnePerm.permanentsOf p0)[0]!.id
  let gProbeRandomSingle :=
    gOnePerm.changes #[
      .pushContinuationFrame {
        afterRandom := .gainLife p0 1
        pendingReplacement := some (.restorePending (.resolveRandom (.chooseObject #[onePermId, ⟨999001⟩])) true none #[] none)
        outerPendingReplacements := #[.receivePriority p1]
      } ]
  let bigInstDef : CardDef := { bigSorcDef with name := "P49i1 HugeInst", types := #[.instant] }
  let gRewindBase0 := insertObject g4 bigInstDef p2 (.hand p2)
  let gRewindBaseP2 := gRewindBase0.change (.priority p2)
  let gRewindProposed := mustApply gRewindBaseP2 p2 (.cast (gRewindBaseP2.player p2).hand.back!)
  let gProbeRewind :=
    gRewindProposed.changes (
      #[.pending .none] ++
      (if gRewindProposed.continuations.isEmpty then #[.pushContinuationFrame {}] else #[]) ++
      #[.pushOuterPendingReplacement (.receivePriority p1),
        .pendingReplacement (some (.restorePending .none true none #[p2] (some false)))])

  -- 1b(iii). `PendingReplacement.move` & `.chooseReplacement` `replacementOrder` step-probe draining:
  let gMoveProbe0 := insertObject g4 oddEvenDef p0 (.hand p0)
  let handOddId := (gMoveProbe0.player p0).hand.back!
  let (gMovePaused, _) := gMoveProbe0.putOntoBattlefield handOddId p0 (cause := some testCause)
  let gMovePausedSeq :=
    match gMovePaused.pendingReplacement with
    | some movePr =>
      gMovePaused.change (.pendingReplacement (some (.seq movePr (.receivePriority p1))))
    | none => gMovePaused

  let item1bOk :=
    mustHold49i1 "1b_sbaOuterAfterFolding"
      (gSbaOuterPaused.pending == Pending.mayPayGeneric p1 1 &&
       (gSbaOuterPaused.player p0).life == 20 &&
       (gSbaOuterAfterDecline.player p0).life == 23) &&
    mustHold49i1 "1b_restorePendingRandomAndRewindProbes"
      (gProbeRandomSingle.firstContinuationPriorityGrant? == some (some p1) &&
       gProbeRewind.firstContinuationPriorityGrant? == some (some p1)) &&
    mustHold49i1 "1b_moveAndReplacementOrderProbeDraining"
      ((match gMovePausedSeq.pending with | .chooseReplacement q _ => q == p0 | _ => false) &&
       gMovePausedSeq.firstContinuationPriorityGrant? == some (some p1))

  mustHold49i1 "1a" item1aOk &&
  mustHold49i1 "1b" item1bOk &&
  mustHold49i1 "1.replay"
    (replayOk49i1 #[gRepEmptyDone, gLinkPaused, gLinkReopened, gCrossAfterP1Cast,
      gAfterP0CastFreeCopy, gDepPostCastDone, gSbaOuterPaused, gSbaOuterAfterDecline, gMovePausedSeq])

end Phase49Item1EventAlignment

section Phase49Item2EventAlignment

private def mustHold49i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase49Item2EventAlignment failed: {label}"

private def replayOk49i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustStepAgent49i2 (g : Game) (p : PlayerId) : Game :=
  match Agent.choose g p with
  | some act => mustApply g p act
  | none => panic! "Phase49Item2EventAlignment: Agent.choose returned none"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let toOffTurnP1 (g : Game) : Game :=
    (g.record (GameEvent.turnBegan g.turnNumber p1 false (cause := some testCause))).change (.priority p0)

  -- 2a(i). `Casting.paidResolutionOrigPerm?`:
  --        - Off-turn sorcery without `ignoreTiming` does NOT splice `anyMana`;
  --        - Continuous Flash (`Keywords.flash` granted via `.abilities`) allows splicing `anyMana` off-turn;
  --        - `asAdventure := true` rejects `fromAdventure := true` permissions (`!pm.fromAdventure`):
  let advKnightDef : CardDef := {
    bear with
    name := "P49i2 AdvKnight"
    manaCost := { symbols := #[.colored .red, .colored .red] }
    adventure := some {
      name := "P49i2 AdvQuest"
      manaCost := { symbols := #[.colored .red] }
      types := #[.instant]
      spellEffect := some (Effect.gainLife 1)
    }
  }
  let gPaid0 := insertObject (toOffTurnP1 g3) advKnightDef p0 .exile
  let paidExId := (gPaid0.objects.filter (fun (o : GameObject) => o.zone == .exile)).back!.id
  let gPaidAnySorc :=
    gPaid0.createEffect
      (.permission (some p0) (.playFromExile paidExId { player := p0, anyMana := true, fromAdventure := true }) .untilEndOfTurn)
      (cause := some testCause)
  let offTurnNoFlashPerm := gPaidAnySorc.paidResolutionOrigPerm? p0 (gPaidAnySorc.object! paidExId)
  let gPaidWithFlash :=
    gPaidAnySorc.createEffect
      (.layered (.objects #[paidExId]) (.abilities { keywords := #[Keyword.flash] } .none) .untilEndOfTurn)
      (cause := some testCause)
  let offTurnFlashCreaturePerm := gPaidWithFlash.paidResolutionOrigPerm? p0 (gPaidWithFlash.object! paidExId)
  let offTurnFromAdvRejected :=
    gPaidWithFlash.paidResolutionOrigPerm? p0 (gPaidWithFlash.object! paidExId)
      (face? := some (advKnightDef.adventure.get!.toCardDef))

  -- 2a(ii). `CastSpell` `hasMorphChoice` `prepareSource` guard:
  --         1. Prepared Morph creature in exile with legal front face casts front face directly (NOT `.chooseKicker`);
  --         2. Prepared Morph creature in exile with illegal front face (`castOnlyIfGraveyardAtLeast := some 3`) +
  --            clean `.playFromExile` falls back to Morph `.chooseKicker`:
  let prepHostDef : CardDef := {
    bear with
    name := "P49i2 PrepHost"
    prepareFace := some {
      name := "P49i2 PrepRally"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellEffect := some (Effect.gainLife 1)
    }
  }
  let morphLegalFrontDef : CardDef := {
    bear with
    name := "P49i2 MorphLegalFront"
    manaCost := ManaCost.ofGeneric 2
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let morphBlockedFrontDef : CardDef := {
    bear with
    name := "P49i2 MorphBlockedFront"
    manaCost := ManaCost.ofGeneric 2
    staticAbilities := #[.castOnlyIfGraveyardAtLeast 3]
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let gPrepBase0 := addPermanent g3 prepHostDef p0 p0
  let prepSrc := (gPrepBase0.permanentsOf p0).back!
  let gPrepBase1 :=
    insertObject (insertObject (gPrepBase0.becomePrepared prepSrc (cause := some testCause))
      morphLegalFrontDef p0 .exile) morphBlockedFrontDef p0 .exile
  let exMorphIds := (gPrepBase1.objects.filter (fun (o : GameObject) =>
    o.zone == .exile && (o.name == morphLegalFrontDef.name || o.name == morphBlockedFrontDef.name))).map (·.id)
  let legalPrepMorphId := exMorphIds[0]!
  let blockedPrepMorphId := exMorphIds[1]!
  let gPrepBoth :=
    (((gPrepBase1.createEffect
        (.permission (some p0) (.playFromExile legalPrepMorphId
          { player := p0, withoutManaCost := true, prepareSource := some prepSrc.id }) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile legalPrepMorphId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile blockedPrepMorphId
        { player := p0, withoutManaCost := true, prepareSource := some prepSrc.id }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile blockedPrepMorphId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let gPrepOkCast := mustApply gPrepBoth p0 (.cast legalPrepMorphId)
  let gPrepFbCast := mustApply gPrepBoth p0 (.cast blockedPrepMorphId)

  -- 2a(iii). `Costs.playManaCost` `freeRG` + `mayCastExiledBySource` `.asAnyMana` on colored `increase`
  --          (vs non-grant `exiledBy`), `playsWithoutPayingManaCost` with Null Summoner vs unpayable `payLife`,
  --          and `playPermissionFor?` `face?` mana-value parity on Adventure faces:
  let nullSummonerDef : CardDef := {
    bear with
    name := "P49i2 NullSummoner"
    staticAbilities := #[.castExiledWithSevenInGraveyard]
  }
  let rgCreatureDef : CardDef := {
    bear with
    name := "P49i2 GruulBoar"
    manaCost := { symbols := #[.colored .red, .colored .green] }
  }
  let gNull0 :=
    Id.run do
      let mut g := addPermanent (emptyHand g3 p0) nullSummonerDef p0 p0
      for _ in [0:7] do
        g := insertObject g bear p0 (.graveyard p0)
      return g
  let nullId := (gNull0.permanentsOf p0).find? (·.name == nullSummonerDef.name) |>.get!.id
  let gNullCage := addPermanent gNull0 ({ name := "P49i2 InertCage", types := #[.artifact] }) p0 p0
  let inertCageId := (gNullCage.permanentsOf p0).back!.id
  let gRgEx0 := insertObject (insertObject gNullCage rgCreatureDef p0 .exile) rgCreatureDef p0 .exile
  let rgExIds := (gRgEx0.objects.filter (fun (o : GameObject) => o.zone == .exile)).map (·.id)
  let rgByNullId := rgExIds[0]!
  let rgByCageId := rgExIds[1]!
  let gRgNoFree :=
    ((gRgEx0.changeObject rgByNullId (.exiledBy (some nullId))).changeObject
      rgByCageId (.exiledBy (some inertCageId))).loseLife p0 19
  let gRgEx1 :=
    gRgNoFree.createEffect (.pendingFreeRGCreatureThisTurn p0) (cause := some testCause)
  let costByNullWithBlueTax :=
    gRgEx1.playManaCost { gRgEx1.object! rgByNullId with controller := some p0 } rgCreatureDef
      (increase := { symbols := #[.colored .blue] })
  let costByCageWithBlueTax :=
    gRgEx1.playManaCost { gRgEx1.object! rgByCageId with controller := some p0 } rgCreatureDef
      (increase := { symbols := #[.colored .blue] })
  let gNullWithUnpayableLife :=
    gRgNoFree.createEffect
      (.permission (some p0) (.playFromExile rgByNullId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)

  let bigAdvDef : CardDef := {
    bear with
    name := "P49i2 GiantAdv"
    manaCost := ManaCost.ofGeneric 6
    adventure := some {
      name := "P49i2 TinySpark"
      manaCost := { symbols := #[.colored .red] }
      types := #[.instant]
      spellEffect := some (Effect.gainLife 1)
    }
  }
  let gAdvLife0 := (insertObject g3 bigAdvDef p0 .exile).loseLife p0 18 -- life == 2
  let advLifeExId := (gAdvLife0.objects.filter (fun (o : GameObject) => o.zone == .exile)).back!.id
  let gAdvLife1 :=
    (gAdvLife0.createEffect
      (.permission (some p0) (.playFromExile advLifeExId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile advLifeExId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let permCreatureAt2Life := gAdvLife1.playPermissionFor? p0 (gAdvLife1.object! advLifeExId)
  let permAdvAt2Life :=
    gAdvLife1.playPermissionFor? p0 (gAdvLife1.object! advLifeExId)
      (face? := some (bigAdvDef.adventure.get!.toCardDef))

  let item2aOk :=
    mustHold49i2 "2a_paidResolutionOrigPerm"
      (offTurnNoFlashPerm.isNone &&
       offTurnFlashCreaturePerm.any (fun pm => pm.anyMana && !pm.ignoreTiming) &&
       offTurnFromAdvRejected.isNone) &&
    mustHold49i2 "2a_prepareSourceMorphGuard"
      (gPrepOkCast.pending != .chooseKicker p0 &&
       gPrepOkCast.stack.size == 1 &&
       !(gPrepOkCast.object! gPrepOkCast.stack.back!.objectId).status.faceDown &&
       gPrepFbCast.pending == .chooseKicker p0) &&
    mustHold49i2 "2a_freeRGAnyManaMayCastExiledAndAdvFaceLife"
      ((ManaPool.empty.add (.colored .green) 1).canPay costByNullWithBlueTax &&
       !(ManaPool.empty.add (.colored .green) 1).canPay costByCageWithBlueTax &&
       !gNullWithUnpayableLife.playsWithoutPayingManaCost (gNullWithUnpayableLife.object! rgByNullId) &&
       permCreatureAt2Life.any (!·.payLifeEqualManaValue) &&
       permAdvAt2Life.any (·.payLifeEqualManaValue))

  -- 2b(i). `Agent.choose` (`chooseCast`) separates `canCastFrontFace` from `canCastAndPayMorphFaceDown`:
  let forbidFrontMorphDef : CardDef := {
    bear with
    name := "P49i2 ForbidFrontMorph"
    manaCost := ManaCost.ofGeneric 2
    staticAbilities := #[.castOnlyIfGraveyardAtLeast 3]
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let gAgMorph2 :=
    insertObject (addPermanent (addPermanent (emptyHand g3 p0) forest p0 p0) forest p0 p0)
      forbidFrontMorphDef p0 (.hand p0)
  let gAgMorph3 := addPermanent gAgMorph2 forest p0 p0
  let agAt2Passes :=
    match Agent.choose gAgMorph2 p0 with | some .pass => true | _ => false
  let agAt3Casts :=
    match Agent.choose gAgMorph3 p0 with
    | some (.cast id) => id == (gAgMorph3.player p0).hand.back!
    | _ => false
  let gAgMorphCastDone :=
    mustStepAgent49i2 (mustStepAgent49i2 (mustStepAgent49i2 (mustStepAgent49i2 (mustStepAgent49i2 (mustStepAgent49i2 gAgMorph3 p0) p0) p0) p0) p0) p0

  -- 2b(ii). Live non-stack `stackCtrl?` guard & `latestExileToStackAfterController?` stop on non-`.stack` moves:
  let gLkiAdv0 := insertObject g3 advKnightDef p0 .exile
  let lkiExId0 := (gLkiAdv0.objects.filter (fun (o : GameObject) => o.zone == .exile)).back!.id
  let (gLkiStack, lkiStackId) := gLkiAdv0.move lkiExId0 .stack (some p1) (cause := some testCause)
  let (gLkiBounced, lkiHandId) := gLkiStack.move lkiStackId (.hand p0) none (cause := some testCause)
  let (gLkiReExiled, lkiReExId) := gLkiBounced.move lkiHandId .exile none (cause := some testCause)
  let gLkiReExWithOwnerGrant :=
    gLkiReExiled.createEffect
      (.permission (some p0) (.playFromExile lkiReExId { player := p0, fromAdventure := true }) .untilEndOfTurn)
      (cause := some testCause)
  -- Same-`ObjectId` `.exile -> .stack (p1)` followed by `.stack -> .exile` on a non-live ghost object:
  let ghostId : ObjectId := ⟨777001⟩
  let ghostObj : GameObject := { id := ghostId, printed := advKnightDef, owner := p0, zone := .exile }
  let gSameId0 :=
    ((g3.record (GameEvent.moved g3.turnNumber
        { id := some ghostId, name := advKnightDef.name, owner := p0, zone := .exile }
        .exile .stack
        (after := some { id := some ghostId, name := advKnightDef.name, owner := p0, controller := some p1, zone := .stack })
        (cause := testCause))).record
      (GameEvent.moved g3.turnNumber
        { id := some ghostId, name := advKnightDef.name, owner := p0, controller := some p1, zone := .stack }
        .stack .exile
        (after := some { id := some ghostId, name := advKnightDef.name, owner := p0, zone := .exile })
        (cause := testCause))).createEffect
      (.permission (some p0) (.playFromExile ghostId { player := p0, fromAdventure := true }) .untilEndOfTurn)
      (cause := some testCause)

  -- 2b(iii). `Turns.expirePlayFromExileEffect` multi-stage `expireUntilNextTurnEffects` (Stage 1
  --          `expireFraUntilTurnEffects` emits `.expired` without logging while Stage 2 permission
  --          is still active; Stage 2 `expirePlayPermissions` then expires the final permission in
  --          the same `pre..g` slice and MUST still emit the log once) & `mayCastExiledBySource` guard:
  let gTwoStage0 := mustApply (insertObject g3 bear p0 .exile) p2 .concede
  let twoStageId := (gTwoStage0.objects.filter (fun (o : GameObject) => o.zone == .exile)).back!.id
  let gTwoStage1 :=
    (gTwoStage0.createEffect
      (.permission (some p0) (.playFromExile twoStageId { player := p0 }) (.untilNextTurnOf p2))
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile twoStageId { player := p0 }) (.untilEndOfNextTurnOf p2))
      (cause := some testCause)
  let gAfterTwoStageExp := gTwoStage1.expireUntilNextTurnEffects p2
  let logsAfterTwoStage :=
    gAfterTwoStageExp.events.filterMap fun
      | .engine _ (.logMsg m) _ => if m.endsWith "can no longer be played from exile" then some m else none
      | _ => none

  let gNullSuppExp :=
    (gRgEx1.createEffect
      (.permission (some p0) (.playFromExile rgByNullId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)).clearEOT
  let nullSuppLogs :=
    gNullSuppExp.events.filterMap fun
      | .engine _ (.logMsg m) _ => if m.endsWith "can no longer be played from exile" then some m else none
      | _ => none

  -- 2b(iv). Post-restore `acc.name cur` single-target return-control log when `.copy` + `.control` expire together:
  let dragonCopyDef : CardDef := creature "P49i2 MirrorDragon" (ManaCost.ofGeneric 4) #["Dragon"] 4 4
  let gCopyCtrl0 :=
    addPermanent (addPermanent g3 bear p0 p0)
      ({ name := "P49i2 Puppeteer", types := #[.creature], power := some 1, toughness := some 1 }) p1 p1
  let origBearObj := (gCopyCtrl0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let puppeteerObj := (gCopyCtrl0.permanentsOf p1).find? (·.name == "P49i2 Puppeteer") |>.get!
  let gCopyCtrl1 :=
    (gCopyCtrl0.createEffect
      (.layered (.objects #[origBearObj.id]) (.copy dragonCopyDef) (.whileSourceOnBattlefield puppeteerObj.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[origBearObj.id]) (.control p1) (.whileSourceOnBattlefield puppeteerObj.id))
      (cause := some testCause)
  let gCopyCtrlRestored := gCopyCtrl1.ceaseToExist puppeteerObj.id (cause := some testCause)
  let hasTrueRestoredNameLog :=
    gCopyCtrlRestored.events.any fun
      | .engine _ (.logMsg m) _ => m.contains "control" && m.contains bear.name
      | _ => false
  let hasStaleCopyNameControlLog :=
    gCopyCtrlRestored.events.any fun
      | .engine _ (.logMsg m) _ => m.contains "control" && m.contains dragonCopyDef.name
      | _ => false

  let item2bOk :=
    mustHold49i2 "2b_agentMorphSplit"
      (agAt2Passes &&
       agAt3Casts &&
       gAgMorphCastDone.stack.size == 1 &&
       (gAgMorphCastDone.object! gAgMorphCastDone.stack.back!.objectId).status.faceDown) &&
    mustHold49i2 "2b_liveNonStackAndLatestExileStackLki"
      ((gLkiReExWithOwnerGrant.playPermissionsFor p1 (gLkiReExWithOwnerGrant.object! lkiReExId)).isEmpty &&
       (gSameId0.playPermissionsFor p1 ghostObj).isEmpty) &&
    mustHold49i2 "2b_multiStageExpirePlayFromExileAndMayCastSuppression"
      (logsAfterTwoStage.size == 1 &&
       nullSuppLogs.isEmpty) &&
    mustHold49i2 "2b_postRestoreNameInReturnControlLog"
      (hasTrueRestoredNameLog && !hasStaleCopyNameControlLog)

  mustHold49i2 "2a" item2aOk &&
  mustHold49i2 "2b" item2bOk &&
  mustHold49i2 "2.replay"
    (replayOk49i2 #[gPrepOkCast, gPrepFbCast, gAgMorphCastDone, gLkiReExWithOwnerGrant,
      gAfterTwoStageExp, gNullSuppExp, gCopyCtrlRestored])

end Phase49Item2EventAlignment

section Phase49Item3EventAlignment

private def mustHold49i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase49Item3EventAlignment failed: {label}"

private def replayOk49i3 (gs : Array Game) : Bool :=
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
  let g5 := g4.change (.addPlayer { id := p4, name := "Chandra" })
  let oddEvenDef : CardDef := {
    name := "P49i3 OddStatue"
    types := #[.artifact]
    staticAbilities := #[.asEntersChooseOddEven]
  }

  -- 3a(i). Phased-out CR 800.4a unrelated-player guard (`owner == p3` living, `fallback == p0` already departed,
  --        `p2` concedes -> Bear phased out under `p1` is NOT exiled when unrelated `p2` leaves; then when `p1`
  --        leaves with `p3` & `p4` still alive, Bear IS exiled with `prevCtrl == some p1`!):
  let gPo0 := addPermanent g5 bear p3 p0
  let poBearId := (gPo0.permanentsOf p0)[0]!.id
  let gPoStolen :=
    (gPo0.createEffect (.layered (.objects #[poBearId]) (.control p1) .indefinite)
      (cause := some testCause)).phaseOut (gPo0.object! poBearId) (cause := some testCause)
  let gP0Conceded := mustApply gPoStolen p0 .concede -- default controller `p0` leaves; Bear stays phased out under `p1` (`fallback == p0` departed)
  let gP2Conceded := mustApply gP0Conceded p2 .concede -- unrelated `p2` leaves; `fallback == p0 != p2`, so Bear MUST remain phased out!
  let gP1Conceded := mustApply gP2Conceded p1 .concede -- controller `p1` leaves; now Bear IS exiled with `before.controller == some p1`!
  let p1LeaveExileSnapCtrl? :=
    gP1Conceded.events.findSomeRev? fun
      | .rules _ (.zone (.moved before _ .battlefield .exile ..)) _ _ =>
        if before.id == some poBearId then some before.controller else none
      | _ => none

  -- 3a(ii). `Leaving.endControlEffectsSimultaneously` `!applied.isEmpty` `appliedChangedInPreExpire` guard:
  --         Phased-out Bear owned by living `p3` with departed default controller `p2`, with BOTH `.copy` and
  --         `.control p1` `.untilEndOfTurn` effects: when `clearEOT` expires `.copy` + `.control p1` simultaneously
  --         on the phased-out permanent (`applied` empty), `!applied.isEmpty` prevents `appliedChangedInPreExpire`
  --         from falsely claiming survival, exiling under CR 800.4a!
  let cloneSrcDef : CardDef := creature "P49i3 CloneTemplate" (ManaCost.ofGeneric 3) #["Shapeshifter"] 3 3
  let gSim0 := addPermanent g4 bear p3 p2
  let simBearId := (gSim0.permanentsOf p2)[0]!.id
  let gSim1 :=
    ((gSim0.createEffect
        (.layered (.objects #[simBearId]) (.copy cloneSrcDef) .untilEndOfTurn)
        (cause := some testCause)).createEffect
      (.layered (.objects #[simBearId]) (.control p1) .untilEndOfTurn)
      (cause := some testCause)).phaseOut (gSim0.object! simBearId) (cause := some testCause)
  let gSimP2Gone := mustApply gSim1 p2 .concede -- default controller `p2` leaves; `simBearId` stays phased out under `p1`
  let gSimEot := gSimP2Gone.clearEOT -- `.copy` + `.control p1` expire simultaneously -> `fallback == p2` (departed) -> exiled!

  -- 3a(iii). `!phasedOut` LTB/ETB trigger suppression in `Core.matchTriggers` & `Event.matchesTrigger`:
  let ltbWatcherDef : CardDef := {
    bear with
    name := "P49i3 LeaveWatcher"
    triggeredAbilities := #[
      TriggeredAbility.fra (.fra .creatureYouControlLeaves) "Whenever a creature you control leaves, gain 2 life." (.gainLife 2)
    ]
  }
  let dyingPoDef : CardDef := {
    bear with
    name := "P49i3 PhasedVictim"
    triggeredAbilities := #[
      .triggered .leaving { resolution := .gainLife (.fixed 3), phrase := "When this leaves, gain 3 life." }
    ]
  }
  let gTrigPo0 := addPermanent (addPermanent g4 ltbWatcherDef p0 p0) dyingPoDef p0 p0
  let victimObj := (gTrigPo0.permanentsOf p0).find? (·.name == dyingPoDef.name) |>.get!
  let gTrigPo1 := gTrigPo0.phaseOut victimObj (cause := some testCause)
  let (gTrigPoMoved, _) := gTrigPo1.move victimObj.id .exile none (cause := some testCause)

  let item3aOk :=
    mustHold49i3 "3a_unrelatedPlayerGuardAndPrevCtrlLki"
      ((gP2Conceded.object! poBearId).isBattlefieldObject &&
       (gP2Conceded.object! poBearId).status.phasedOut &&
       (gP1Conceded.findObject? poBearId).isNone &&
       gP1Conceded.objects.any (fun o => o.zone == .exile && o.owner == p3) &&
       p1LeaveExileSnapCtrl? == some (some p1)) &&
    mustHold49i3 "3a_simultaneousPhasedOutCopyControlExpiryExiles"
      ((gSimP2Gone.object! simBearId).status.phasedOut &&
       (gSimEot.findObject? simBearId).isNone &&
       gSimEot.objects.any (fun o => o.zone == .exile && o.owner == p3)) &&
    mustHold49i3 "3a_phasedOutLtbTriggerSuppression"
      gTrigPoMoved.waitingTriggers.isEmpty

  -- 3b(i). `Phasing` entry `sbaPausedOnPhasing` batch deferral (`phaseOut`, `phaseInControlled`,
  --        and direct `phaseIn` on an indirectly phased-out attached permanent resuming with `currentBatch.isNone`):
  let gPhPause0 := insertObject (addPermanent g4 bear p0 p0) oddEvenDef p0 (.hand p0)
  let phBearId := (gPhPause0.permanentsOf p0)[0]!.id
  let (gPhPausedBase, _) :=
    gPhPause0.putOntoBattlefield (gPhPause0.player p0).hand.back! p0 (cause := some testCause)
  let gDeferredPhaseOut := gPhPausedBase.phaseOut (gPhPausedBase.object! phBearId) (cause := some testCause)
  let batchUnchangedWhilePaused := gDeferredPhaseOut.currentBatch == gPhPausedBase.currentBatch
  let bearStillPhasedInWhilePaused := !(gDeferredPhaseOut.object! phBearId).status.phasedOut
  let gAfterResumePhaseOut := mustApply gDeferredPhaseOut p0 (.chooseMode 0)

  let gPhInPaused0 := insertObject gAfterResumePhaseOut oddEvenDef p0 (.hand p0)
  let (gPhInPaused1, _) :=
    gPhInPaused0.putOntoBattlefield (gPhInPaused0.player p0).hand.back! p0 (cause := some testCause)
  let gDeferredPhaseInCtrl := gPhInPaused1.phaseInControlled p0
  let bearStillPhasedOutWhilePaused := (gDeferredPhaseInCtrl.object! phBearId).status.phasedOut
  let gAfterResumePhaseInCtrl := mustApply gDeferredPhaseInCtrl p0 (.chooseMode 0)

  let outerEqDef : CardDef := {
    name := "P49i3 Blade"
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  let subAuraDef : CardDef := {
    name := "P49i3 Polish"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantArtifactOrNonAuraEnchantment]
  }
  let gAtt0 :=
    addPermanent (addPermanent (addPermanent g4 bear p0 p0) outerEqDef p0 p0) subAuraDef p0 p0
  let attHostObj := (gAtt0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let attEqObj := (gAtt0.permanentsOf p0).find? (·.name == outerEqDef.name) |>.get!
  let attSubObj := (gAtt0.permanentsOf p0).find? (·.name == subAuraDef.name) |>.get!
  let gAttPhasedOut :=
    ((gAtt0.attachSourceTo attEqObj attHostObj (cause := some testCause)).attachSourceTo
      attSubObj attEqObj (cause := some testCause)).phaseOut attHostObj (cause := some testCause)
  let gAttPaused0 := insertObject gAttPhasedOut oddEvenDef p0 (.hand p0)
  let (gAttPaused1, _) :=
    gAttPaused0.putOntoBattlefield (gAttPaused0.player p0).hand.back! p0 (cause := some testCause)
  let gDeferredAttPhaseIn :=
    gAttPaused1.phaseIn (gAttPaused1.object! attEqObj.id) (cause := some testCause)
  let attEqStillPhasedOutWhilePaused := (gDeferredAttPhaseIn.object! attEqObj.id).status.phasedOut
  let gAfterResumeAttPhaseIn := mustApply gDeferredAttPhaseIn p0 (.chooseMode 0)

  -- 3b(ii). `Phasing.departedNextTurnWouldHaveBegunSince` `preLogRegSeat` mid-log departure handling:
  let gT2 := g4.startNextTurnAndBegin -- turn 2, `p1` active
  let gQuietT2 := quiet gT2
  let gMidDep0 := addPermanent gQuietT2 bear p0 p0
  let midBearId := (gMidDep0.permanentsOf p0)[0]!.id
  let gMidDep1 := mustApply gMidDep0 p1 .concede -- `p1` departs MID-LOG before any `turnBegan` in `gMidDep0.events`!
  let gMidDepT3 := gMidDep1.startNextTurnAndBegin -- turn 3 (`extra == false`), `p2` active (`p1` died mid-log!)
  let gMidDepStolen :=
    mustApply
      ((gMidDepT3.createEffect (.layered (.objects #[midBearId]) (.control p2) .indefinite)
          (cause := some testCause)).phaseOut (gMidDepT3.object! midBearId) (cause := some testCause))
      p2 .concede
  let gMidDepT4P3 := gMidDepStolen.startNextTurnAndBegin -- turn 4 (`p3` active): `p2`'s next turn hasn't begun yet!
  let gMidDepT5P0 := gMidDepT4P3.startNextTurnAndBegin -- turn 5 (`p0` active): still before `p2`'s seat!
  let gMidDepT6P3 := gMidDepT5P0.startNextTurnAndBegin -- turn 6 (`p3` active, passing `[p2]` after `p0`): NOW phases in!

  let item3bOk :=
    mustHold49i3 "3b_phasingEntryBatchDeferral"
      (batchUnchangedWhilePaused &&
       bearStillPhasedInWhilePaused &&
       (gAfterResumePhaseOut.object! phBearId).status.phasedOut &&
       bearStillPhasedOutWhilePaused &&
       !(gAfterResumePhaseInCtrl.object! phBearId).status.phasedOut &&
       attEqStillPhasedOutWhilePaused &&
       (gAfterResumeAttPhaseIn.object! attHostObj.id).status.phasedOut &&
       !(gAfterResumeAttPhaseIn.object! attEqObj.id).status.phasedOut &&
       !(gAfterResumeAttPhaseIn.object! attSubObj.id).status.phasedOut) &&
    mustHold49i3 "3b_midLogDeparturePreLogRegSeat"
      ((gMidDepT4P3.object! midBearId).status.phasedOut &&
       (gMidDepT5P0.object! midBearId).status.phasedOut &&
       !(gMidDepT6P3.object! midBearId).status.phasedOut)

  mustHold49i3 "3a" item3aOk &&
  mustHold49i3 "3b" item3bOk &&
  mustHold49i3 "3.replay"
    (replayOk49i3 #[gP2Conceded, gP1Conceded, gSimEot, gTrigPoMoved,
      gAfterResumePhaseOut, gAfterResumePhaseInCtrl, gAfterResumeAttPhaseIn])

end Phase49Item3EventAlignment

section Phase49Item4EventAlignment

private def mustHold49i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase49Item4EventAlignment failed: {label}"

private def replayOk49i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := emptyHand (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })) p0

  -- 4a(i). `availableManaExceptIds` unrestricted/higher-yield selection & `hasUsableNonPlainManaAbility`
  --        reserved-source (`propTapReservedIds` / `propBfSacReservedIds`) + `canPayFromSources` checks:
  let dragonRockDef : CardDef := {
    name := "P49i4 DragonLantern"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .red, .const 1)]) (restriction := some .dragonSpell)]
  }
  let lanternGrantDef : CardDef := {
    name := "P49i4 ChromaticOrb"
    types := #[.artifact]
    staticAbilities := #[.grantLandsTapAnyColor]
  }
  let gAvail0 := addPermanent (addPermanent g3 dragonRockDef p0 p0) lanternGrantDef p0 p0
  let availPaysGreen := (gAvail0.availableMana p0).canPay { symbols := #[.colored .green] }

  let tapCreatureManaArtDef : CardDef := {
    name := "P49i4 SpringleafDrum"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := { resolution := .addMana #[.colored .blue] (.fixed 1), phrase := "Add {U}." }
    }]
  }
  let gDrum0 := addPermanent (addPermanent g3 tapCreatureManaArtDef p0 p0) bear p0 p0
  let bearDrumId := (gDrum0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let drumUsableFree := gDrum0.hasUsableNonPlainManaAbility p0
  let dummyPropReservingBear : ProposedSpell := {
    caster := p0
    spellId := bearDrumId
    original := gDrum0.object! bearDrumId
    cost := ManaCost.ofGeneric 1
    teamworkCreatures := #[bearDrumId]
  }
  let gDrumReserved := gDrum0.change (.proposedSpell (some dummyPropReservingBear))
  let drumBlockedWhenReserved := !gDrumReserved.hasUsableNonPlainManaAbility p0 (prop? := some dummyPropReservingBear)

  -- 4a(ii). `Casting.hasCostPreservingPaymentSubset` Vehicle `prop.sourceId` `equivKey` soundness (>20 sources):
  let animVehicleManaDef : CardDef := {
    creature "P49i4 ManaSkiff" ManaCost.empty #["Vehicle"] 3 3 with
    types := #[.artifact, .creature]
    keywords := #[Keyword.haste]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 20), .tapObjects (.totalPowerAtLeast (.const 3)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])]
        effect := Effect.gainLife 2 },
      ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])
    ]
  }
  let onePowManaElfDef : CardDef := {
    llanowarElves with
    name := "P49i4 QuickElf"
    power := some 1
    toughness := some 1
    keywords := #[Keyword.haste]
  }
  let gSkiff0 :=
    Id.run do
      let mut g := addPermanent g3 animVehicleManaDef p0 p0
      for _ in [0:22] do
        g := addPermanent g onePowManaElfDef p0 p0
      return g
  let skiffId := (gSkiff0.permanentsOf p0).find? (·.name == animVehicleManaDef.name) |>.get!.id
  let gSkiffProp := mustApply gSkiff0 p0 (.activate skiffId 0)
  let skiffProp := gSkiffProp.proposedSpell.get!
  let skiffSubsetPreserves3Elves :=
    gSkiffProp.hasCostPreservingPaymentSubset ManaPool.empty (ManaCost.ofGeneric 20)
      (gSkiffProp.manaSourcesForProposed p0 skiffProp) (gSkiffProp.proposedManaSpend skiffProp)
      (prop? := some (p0, skiffProp))

  -- 4a(iii). `Agent.payGenericOrTapFirstSource` `.mountainExtraRed` on restricted-base Mountain permanent:
  let restrictedMtnOrbDef : CardDef := {
    name := "P49i4 SpellMountainOrb"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.manaAbility (.oneOf .anyColor (.const 1)) (restriction := some .instantOrSorcery)]
  }
  let gMtnOrb0 := addPermanent g3 restrictedMtnOrbDef p0 p0
  let mtnOrbId := (gMtnOrb0.permanentsOf p0)[0]!.id
  let gMtnOrb1 :=
    (gMtnOrb0.createEffect
      (.layered (.objects #[mtnOrbId]) (.types .add #[] #[.mountain] #[]) .untilEndOfTurn)
      (cause := some testCause)).createEffect
      (.playerRule p0 (.mountainExtraRed 1) .untilEndOfTurn) (cause := some testCause)
  let gMayPay1 := gMtnOrb1.change (.pending (.mayPayGeneric p0 1))
  let gMayPay2 := gMtnOrb1.change (.pending (.mayPayGeneric p0 2))
  let agPicksTruePeak :=
    (match Agent.choose gMayPay1 p0 with
     | some (.tapForMana id _) => id == mtnOrbId
     | _ => false) &&
    (match Agent.choose gMayPay2 p0 with
     | some .decline => true
     | _ => false)

  -- 4a(iv). `Agent` `.chooseX` (`maxAffordableX`) with `{1}` cost reduction at `0` mana (`chooseX 1`)
  --         AND mixed-color `.combination` source (`{X}{U}{R}` with `{U}`/`{R}` combination of 2 + `Forest` -> `chooseX 1`):
  let xSorcDef : CardDef := {
    name := "P49i4 MindBlaze"
    manaCost := { symbols := #[.x] }
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 1)
  }
  let gRedX0 :=
    insertObject (g3.grantTypeCostLessThisTurn p0 .sorcery 1) xSorcDef p0 (.hand p0)
  let gRedXProp := mustApply gRedX0 p0 (.cast (gRedX0.player p0).hand.back!)
  let redXChoseOne :=
    match Agent.choose gRedXProp p0 with | some (.chooseX 1) => true | _ => false

  let urComboLandDef : CardDef := {
    name := "P49i4 SteamFalls"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.combination (.explicit #[.colored .blue, .colored .red]) (.const 2))]
  }
  let xUrSorcDef : CardDef := {
    name := "P49i4 SteamX"
    manaCost := { symbols := #[.x, .colored .blue, .colored .red] }
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 1)
  }
  let gComboX0 :=
    insertObject (addPermanent (addPermanent g3 urComboLandDef p0 p0) forest p0 p0) xUrSorcDef p0 (.hand p0)
  let gComboXProp := mustApply gComboX0 p0 (.cast (gComboX0.player p0).hand.back!)
  let comboXChoseOne :=
    match Agent.choose gComboXProp p0 with | some (.chooseX 1) => true | _ => false

  let item4aOk :=
    mustHold49i4 "4a_availUnrestrictedAndNonPlainReserved"
      (availPaysGreen && drumUsableFree && drumBlockedWhenReserved) &&
    mustHold49i4 "4a_vehiclePropSourceEquivKey"
      skiffSubsetPreserves3Elves &&
    mustHold49i4 "4a_restrictedMountainExtraRedTapPick"
      agPicksTruePeak &&
    mustHold49i4 "4a_chooseXCostReducedAndCombination"
      (redXChoseOne && comboXChoseOne)

  -- 4b(i). `TriggeredAbilities` `TriggerRead.chosenX`, `FraAbilities.applyFraAbility` (`tapAndStunX`),
  --        and `applyUnified` -> `applyFraResolution?` -> `applyFra` -> `FrcResolve.spellX` (`warriorsX`):
  let xEtbLifeDef : CardDef := {
    creature "P49i4 XHydraLifegiver" { symbols := #[.x] } #["Hydra"] 2 2 with
    triggeredAbilities := #[
      .triggered .enter { resolution := .gainLife .chosenX, phrase := "When this enters, gain X life." }
    ]
  }
  let gXEtb0 := (insertObject g3 xEtbLifeDef p0 (.hand p0)).addMana p0 .colorless 4
  let gXEtbCast :=
    mustApply (mustApply (mustApply gXEtb0 p0 (.cast (gXEtb0.player p0).hand.back!)) p0 (.chooseX 4)) p0 .pay
  let gXEtbEntered := mustApply (mustApply (mustApply gXEtbCast p0 .pass) p1 .pass) p2 .pass
  let gXEtbResolved := mustApply (mustApply (mustApply gXEtbEntered p0 .pass) p1 .pass) p2 .pass

  let stunRodDef : CardDef := {
    name := "P49i4 StunWand"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana { symbols := #[.x] }]
      effect := { targeting := .of .creature, resolution := .tapAndStunX, phrase := "Tap target creature and put X stun counters on it." }
    }]
  }
  let gStun0 := (addPermanent (addPermanent g3 stunRodDef p0 p0) bear p1 p1).addMana p0 .colorless 3
  let wandId := (gStun0.permanentsOf p0).find? (·.name == stunRodDef.name) |>.get!.id
  let p1BearId := (gStun0.permanentsOf p1)[0]!.id
  let gStunAct :=
    mustApply (mustApply (mustApply (mustApply gStun0 p0 (.activate wandId 0)) p0 (.chooseX 3)) p0 (.target (.permanent p1BearId))) p0 .pay
  let gStunResolved := mustApply (mustApply (mustApply gStunAct p0 .pass) p1 .pass) p2 .pass

  let warriorsXEffect : Effect := { resolution := .frc .warriorsX, phrase := "Create X 1/1 Warrior creature tokens." }
  let gWarriorsX := g3.applyEffect p0 warriorsXEffect #[] (chosenX := some 2)

  -- 4b(ii). `EffectResolution.applyUnified` (`.or [r]`, `.«if»`, `.ifElse`), `beginMay`/`acceptMay`,
  --         `beginSpellOr`/`chooseSpellOr`, and `ModeledTriggers.applyModeledTrigger`/`offerVisionModes` LKI forwarding:
  let rPow : SpellResolution := .loseLife .equalSourcePower .eachOpponent
  let rTgh : SpellResolution := .loseLife .equalSourceToughness .eachOpponent
  let rChX : SpellResolution := .loseLife .chosenX .eachOpponent
  let mkSpellEff (sr : SpellResolution) : Effect := { resolution := .ofSpell sr, phrase := "Opponents lose life." }

  let gOrSingleton :=
    g3.applyEffect p0 (mkSpellEff (.or [rTgh])) #[] (lastKnownPower := some 4) (lastKnownToughness := some 6)
  let gIfGy :=
    g3.applyEffect p0 (mkSpellEff (.«if» .castFromGraveyard rPow)) #[]
      (castFromGraveyard := true) (lastKnownPower := some 4) (lastKnownToughness := some 6)
  let gIfElseGift :=
    g3.applyEffect p0 (mkSpellEff (.ifElse .giftPromised rChX (.loseLife (.fixed 1) .eachOpponent))) #[]
      (giftPromised := true) (chosenX := some 3) (lastKnownPower := some 4) (lastKnownToughness := some 6)

  let gMayPrompt :=
    g3.applyEffect p0 (mkSpellEff (.may rTgh (.sequence []) .ifYouDont)) #[]
      (chosenX := some 3) (lastKnownPower := some 4) (lastKnownToughness := some 6)
  let gMayAccepted := mustApply gMayPrompt p0 .accept

  let gSpellOrPrompt :=
    g3.applyEffect p0 (mkSpellEff (.or [rPow, rTgh])) #[]
      (chosenX := some 3) (lastKnownPower := some 4) (lastKnownToughness := some 6)
  let gSpellOrChosen :=
    match gSpellOrPrompt.chooseSpellOr p0 1 with
    | .ok g' => g'
    | .error msg => panic! s!"chooseSpellOr failed: {msg}"

  let gVis0 := addPermanent g3 bear p0 p0
  let visId := (gVis0.permanentsOf p0)[0]!.id
  let visAb : TriggeredAbility := .triggered .youCastSpell Effect.castingVisionModes
  let gVisOffered :=
    gVis0.applyModeledTrigger p0 visAb (some visId) #[] "Vision"
      (lastKnownPower := some 4) (lastKnownToughness := some 6)

  -- 4b(iii). `Event.isTreasureSourceInLog` phased-out (`PermanentEvent.phasedOut`) & `.battlefield` `created`,
  --          while rejecting non-`.battlefield` `abilityActivated`:
  let trArtDef : CardDef := { name := "P49i4 Chest", types := #[.artifact], subtypes := #["Treasure"] }
  let gPoTr0 := addPermanent g3 trArtDef p0 p0
  let poTrObj := (gPoTr0.permanentsOf p0)[0]!
  let gPoTr1 := (quiet gPoTr0).phaseOut poTrObj (cause := some testCause)
  let gPoTrMana := gPoTr1.addMana p0 (.colored .red) 1 (source := some poTrObj.id)

  let createdTrId : ObjectId := ⟨888001⟩
  let gCrTr0 :=
    (quiet g3).record (GameEvent.created g3.turnNumber p0
      { id := some createdTrId, name := "Treasure", owner := p0, controller := some p0,
        zone := .battlefield, types := #[.artifact], subtypes := #[.treasure], token := true }
      (cause := testCause))
  let gCrTrMana := gCrTr0.addMana p0 (.colored .blue) 1 (source := some createdTrId)

  let gGyTr0 := quiet (insertObject g3 trArtDef p0 (.graveyard p0))
  let gyTrId := (gGyTr0.player p0).graveyard.back!
  let gyTrSnap := gGyTr0.snapshot (gGyTr0.object! gyTrId)
  let gGyTrLogged :=
    gGyTr0.record (GameEvent.abilityActivated gGyTr0.turnNumber ⟨888002⟩ gyTrSnap p0 (.nonMana none false false false) (cause := some testCause))
  let gGyTrMana := gGyTrLogged.addMana p0 (.colored .black) 1 (source := some gyTrId)

  let item4bOk :=
    mustHold49i4 "4b_chosenXAcrossTriggerFraAndFrc"
      ((gXEtbResolved.player p0).life == 24 &&
       (gStunResolved.object! p1BearId).status.stun == 3 &&
       ((gWarriorsX.permanentsOf p0).filter (fun o => gWarriorsX.hasSubtype o .warrior || o.name.contains "Warrior")).size == 2) &&
    mustHold49i4 "4b_lkiForwardingAcrossUnifiedMaySpellOrAndVision"
      ((gOrSingleton.player p1).life == 14 &&
       (gIfGy.player p1).life == 16 &&
       (gIfElseGift.player p1).life == 17 &&
       (gMayAccepted.player p1).life == 14 &&
       (gSpellOrChosen.player p1).life == 14 &&
       gVisOffered.chooseModesRest.any (fun r => r.lastKnownPower == some 4 && r.lastKnownToughness == some 6)) &&
    mustHold49i4 "4b_treasureSourceInLogPhasedOutCreatedAndBfZone"
      (GameEvent.isTreasureSourceInLog gPoTr1.events poTrObj.id &&
       (gPoTrMana.player p0).manaPool.units.all (·.fromTreasure) &&
       GameEvent.isTreasureSourceInLog gCrTr0.events createdTrId &&
       (gCrTrMana.player p0).manaPool.units.all (·.fromTreasure) &&
       !GameEvent.isTreasureSourceInLog gGyTrLogged.events gyTrId &&
       (gGyTrMana.player p0).manaPool.units.all (!·.fromTreasure))

  mustHold49i4 "4a" item4aOk &&
  mustHold49i4 "4b" item4bOk &&
  mustHold49i4 "4.replay"
    (replayOk49i4 #[gSkiffProp, gXEtbResolved, gStunResolved, gWarriorsX,
      gOrSingleton, gIfGy, gIfElseGift, gMayAccepted, gSpellOrChosen, gVisOffered])

end Phase49Item4EventAlignment

section Phase1AbilityAlignmentReview

private def mustHoldP1Rev (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase1AbilityAlignmentReview failed: {label}"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := afterDraw

  -- 1. Incubator back face named "Phyrexian Token" (CR 111.10i)
  let gInc0 := g0.createKindTokens p0 .incubator 1
  let incObj := (gInc0.permanentsOf p0).find? (·.name == "Incubator") |>.get!
  let gIncTr := gInc0.withResolvingContext (some incObj.id) p0 (fun g =>
    g.applyFrc p0 default .transformIncubator #[] (some incObj.id))
  let incAfter := gIncTr.object! incObj.id
  let incubatorOk :=
    (Game.predefinedTokenPrinted .incubator).otherFace.map (·.name) == some "Phyrexian Token" &&
    incAfter.status.transformed &&
    incAfter.name == "Phyrexian Token" &&
    gIncTr.isArtifact incAfter && gIncTr.isCreature incAfter

  -- 2. Map token (CR 111.10s) & Explore (CR 701.44a / 701.44c):
  --    sorcery speed, targets creature you control, explores targeted creature;
  --    nonland puts +1/+1 counter BEFORE offering optional graveyard put;
  --    noncreature permanent exploring nonland still gets +1/+1 counter + may-graveyard;
  --    empty library still puts +1/+1 counter on exploring permanent;
  --    departed permanent uses LKI controller (CR 701.44c) and still reveals/offers choice.
  let mapDef := Game.predefinedTokenPrinted .map
  let mapAb := mapDef.activatedAbilities[0]!
  let gMap0 := addPermanent (g0.createKindTokens p0 .map 1) bear p0 p0
  let gMap0 := addPermanent gMap0 bear p1 p1
  let myBear := (gMap0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let oppBear := (gMap0.permanentsOf p1).find? (·.name == bear.name) |>.get!
  let mapTok := (gMap0.permanentsOf p0).find? (·.name == "Map") |>.get!
  -- Nonland on top -> +1/+1 counter on targeted creature BEFORE FraChoice.exploreMayGraveyard
  let gMapNonland0 :=
    let g := addPermanent gMap0 bear p0 p0
    let topId := g.battlefield.back!.id
    (g.move topId (.library p0) none (libraryPosition := some .top)).1
  let topNonlandId := (gMapNonland0.player p0).library.back!
  let gyBeforeMap := (gMapNonland0.player p0).graveyard.size
  let gMapNonland :=
    gMapNonland0.applyEffect p0 mapAb.effect #[.permanent myBear.id] (sourceId := some mapTok.id)
  let gMapNonlandAccept := mustApply gMapNonland p0 .accept
  let gMapNonlandDecline := mustApply gMapNonland p0 .decline
  -- Land on top -> land moved into hand, no graveyard prompt
  let gMapLand0 :=
    let g := addPermanent gMap0 forest p0 p0
    let topId := g.battlefield.back!.id
    (g.move topId (.library p0) none (libraryPosition := some .top)).1
  let handBeforeLand := (gMapLand0.player p0).hand.size
  let gMapLand :=
    gMapLand0.applyEffect p0 mapAb.effect #[.permanent myBear.id] (sourceId := some mapTok.id)
  -- Illegal target (opponent's creature) -> no counter added, no prompt
  let gMapIllegal :=
    gMapNonland0.applyEffect p0 mapAb.effect #[.permanent oppBear.id] (sourceId := some mapTok.id)
  let mapOk :=
    mapAb.timing == .sorcery &&
    mapAb.cost == CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf, .sacrifice (.exact 1) .self] &&
    mapAb.effect.targetSpec == .creatureYouControl &&
    (gMapNonland.object! myBear.id).status.plusOnePlusOne == 1 &&
    gMapNonland.pending == .fraChoice p0 (.exploreMayGraveyard topNonlandId) &&
    gMapNonlandAccept.pending == .none &&
    (gMapNonlandAccept.player p0).graveyard.size == gyBeforeMap + 1 &&
    (gMapNonlandAccept.player p0).library.back? != some topNonlandId &&
    gMapNonlandDecline.pending == .none &&
    (gMapNonlandDecline.player p0).graveyard.size == gyBeforeMap &&
    (gMapNonlandDecline.player p0).library.back? == some topNonlandId &&
    (gMapLand.player p0).hand.size == handBeforeLand + 1 &&
    gMapLand.pending == .none &&
    (gMapIllegal.object! oppBear.id).status.plusOnePlusOne == 0 &&
    gMapIllegal.pending == .none

  -- 2b. CR 701.44a noncreature & empty library; CR 701.44c departed permanent uses LKI controller
  let relicDef : CardDef := { name := "Explore Relic", types := #[.artifact] }
  let gRelic0 :=
    let g := addPermanent g0 relicDef p0 p0
    let g := addPermanent g bear p0 p0
    let topId := g.battlefield.back!.id
    (g.move topId (.library p0) none (libraryPosition := some .top)).1
  let relicObj := (gRelic0.permanentsOf p0).find? (·.name == "Explore Relic") |>.get!
  let relicTopId := (gRelic0.player p0).library.back!
  let gRelicExp := gRelic0.applyFrc p0 default .explore #[] (some relicObj.id)
  let gRelicExpAccept := mustApply gRelicExp p0 .accept
  let gEmptyLib0 :=
    let g := addPermanent g0 bear p0 p0
    (g.player p0).library.foldl (fun acc id => (acc.move id .exile none).1) g
  let emptyBear := (gEmptyLib0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let gEmptyExp := gEmptyLib0.applyFrc p0 default .explore #[] (some emptyBear.id)
  -- Departed permanent: owned by p0, controlled by p1 on battlefield before leaving;
  -- ability controller is p0, yet CR 701.44c reveals p1's library (LKI controller).
  let gStolen0 := addPermanent g0 bear p0 p1
  let stolenObj := (gStolen0.permanentsOf p1).find? (·.name == bear.name) |>.get!
  let (gDepartedBase, _) := gStolen0.move stolenObj.id (.graveyard p0) none
  let gDepNonland0 :=
    let g := addPermanent gDepartedBase bear p1 p1
    let topId := g.battlefield.back!.id
    (g.move topId (.library p1) none (libraryPosition := some .top)).1
  let p1TopNonland := (gDepNonland0.player p1).library.back!
  let p0LibSizeBefore := (gDepNonland0.player p0).library.size
  let p1GyBefore := (gDepNonland0.player p1).graveyard.size
  let gDepNonland := gDepNonland0.applyFrc p0 default .explore #[] (some stolenObj.id)
  let gDepNonlandAccept := mustApply gDepNonland p1 .accept
  let gDepLand0 :=
    let g := addPermanent gDepartedBase forest p1 p1
    let topId := g.battlefield.back!.id
    (g.move topId (.library p1) none (libraryPosition := some .top)).1
  let p1HandBefore := (gDepLand0.player p1).hand.size
  let gDepLand := gDepLand0.applyFrc p0 default .explore #[] (some stolenObj.id)
  -- CR 400.3: top card of p0's library owned by p1 goes to p1's hand (land) or p1's graveyard (nonland)
  let gOwnBase := addPermanent g0 bear p0 p0
  let ownExplorer := (gOwnBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let gOwnLand0 :=
    let g := addPermanent gOwnBase forest p1 p1
    let topId := g.battlefield.back!.id
    (g.move topId (.library p0) none (libraryPosition := some .top)).1
  let p0HandBeforeOwn := (gOwnLand0.player p0).hand.size
  let p1HandBeforeOwn := (gOwnLand0.player p1).hand.size
  let gOwnLand := gOwnLand0.applyFrc p0 default .explore #[] (some ownExplorer.id)
  let gOwnNonland0 :=
    let g := addPermanent gOwnBase bear p1 p1
    let topId := g.battlefield.back!.id
    (g.move topId (.library p0) none (libraryPosition := some .top)).1
  let p0GyBeforeOwn := (gOwnNonland0.player p0).graveyard.size
  let p1GyBeforeOwn := (gOwnNonland0.player p1).graveyard.size
  let gOwnNonland := gOwnNonland0.applyFrc p0 default .explore #[] (some ownExplorer.id)
  let gOwnNonlandAccept := mustApply gOwnNonland p0 .accept
  let exploreCr70144Ok :=
    !gRelic0.isCreature relicObj &&
    (gRelicExp.object! relicObj.id).status.plusOnePlusOne == 1 &&
    gRelicExp.pending == .fraChoice p0 (.exploreMayGraveyard relicTopId) &&
    (gRelicExpAccept.player p0).graveyard.size == (gRelic0.player p0).graveyard.size + 1 &&
    (gEmptyLib0.player p0).library.isEmpty &&
    (gEmptyExp.object! emptyBear.id).status.plusOnePlusOne == 1 &&
    gEmptyExp.pending == .none &&
    gDepNonland.pending == .fraChoice p1 (.exploreMayGraveyard p1TopNonland) &&
    (gDepNonlandAccept.player p1).graveyard.size == p1GyBefore + 1 &&
    (gDepNonlandAccept.player p0).library.size == p0LibSizeBefore &&
    (gDepLand.player p1).hand.size == p1HandBefore + 1 &&
    gDepLand.pending == .none &&
    (gOwnLand.player p1).hand.size == p1HandBeforeOwn + 1 &&
    (gOwnLand.player p0).hand.size == p0HandBeforeOwn &&
    gOwnLand.log.any (·.contains "'s hand") &&
    (gOwnNonlandAccept.player p1).graveyard.size == p1GyBeforeOwn + 1 &&
    (gOwnNonlandAccept.player p0).graveyard.size == p0GyBeforeOwn &&
    gOwnNonlandAccept.log.any (·.contains "'s graveyard")

  -- 3. Junk (CR 111.10t), Lander (CR 111.10u), Mutagen (CR 111.10v)
  let junkDef := Game.predefinedTokenPrinted .junk
  let junkAb := junkDef.activatedAbilities[0]!
  let gJunk0 := g0.createKindTokens p0 .junk 1
  let topLibId := (gJunk0.player p0).library.back!
  let gJunk := gJunk0.applyEffect p0 junkAb.effect #[]
  let junkMoved? := gJunk.followMovedToZone? topLibId (· == .exile)
  let junkExiled := junkMoved?.isSome
  let junkPlayableThisTurn :=
    match junkMoved? with
    | none => false
    | some moved =>
      gJunk.activeEffects.any fun (_, s) =>
        match s with
        | .permission _ (.playFromExile oid perm) .untilEndOfTurn => oid == moved.id && perm.player == p0
        | _ => false

  let landerDef := Game.predefinedTokenPrinted .lander
  let landerAb := landerDef.activatedAbilities[0]!
  let gLander := (g0.createKindTokens p0 .lander 1).applyEffect p0 landerAb.effect #[]
  let landerSearches := match gLander.pending with
    | .fraChoice q (.searchLibrary _ 1 (.battlefield true) _ _) => q == p0
    | _ => false

  let mutagenDef := Game.predefinedTokenPrinted .mutagen
  let mutagenAb := mutagenDef.activatedAbilities[0]!
  let gMut0 := addPermanent (g0.createKindTokens p0 .mutagen 1) bear p0 p0
  let mutBear := (gMut0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let gMut := gMut0.applyEffect p0 mutagenAb.effect #[.permanent mutBear.id]
  let junkLanderMutagenOk :=
    mustHoldP1Rev "3a.junk" (junkAb.timing == .sorcery &&
      junkAb.cost == CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self] &&
      junkExiled && junkPlayableThisTurn) &&
    mustHoldP1Rev "3b.lander" (landerAb.timing == .instant &&
      landerAb.cost == CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapSelf, .sacrifice (.exact 1) .self] &&
      landerSearches) &&
    mustHoldP1Rev "3c.mutagen" (mutagenAb.timing == .sorcery &&
      mutagenAb.cost == CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf, .sacrifice (.exact 1) .self] &&
      mutagenAb.effect.targetSpec == .creature &&
      (gMut.object! mutBear.id).status.plusOnePlusOne == 1)

  -- 4. Moloid .onAttackMayMill 1 (and generalized n = 2) wired onto printed CardDef & runtime
  let gMol0 := g0.createKindTokens p0 .moloid 1
  let molObj := (gMol0.permanentsOf p0).find? (·.name == "Moloid") |>.get!
  let molAb := molObj.printed.triggeredAbilities[0]!
  let gyBeforeMol := (gMol0.player p0).graveyard.size
  let gMolPrompt := gMol0.applyTriggeredAbility p0 molAb (some molObj.id) #[]
  let gMolAccept := mustApply gMolPrompt p0 .accept
  let gMolDecline := mustApply gMolPrompt p0 .decline
  let mill2Spec : TokenSpec :=
    TokenSpec.creature #[.minion] 1 1 (ColorSet.singleton .green)
      (name? := some "Big Moloid") (abilities := #[.onAttackMayMill 2])
  let gMol20 := g0.createKindTokens p0 mill2Spec 1
  let mol2Obj := (gMol20.permanentsOf p0).find? (·.name == "Big Moloid") |>.get!
  let gMol2Accept :=
    mustApply (gMol20.applyTriggeredAbility p0 mol2Obj.printed.triggeredAbilities[0]! (some mol2Obj.id) #[])
      p0 .accept
  let moloidOk :=
    molObj.printed.triggeredAbilities.size == 1 &&
    molAb.firesOn .attacking &&
    gMolPrompt.pending == .mayResolve p0 &&
    (gMolAccept.player p0).graveyard.size == gyBeforeMol + 1 &&
    (gMolDecline.player p0).graveyard.size == gyBeforeMol &&
    (gMol2Accept.player p0).graveyard.size == gyBeforeMol + 2

  -- 5. TokenSpec.copyOf: copies real object's copiable values + CR 707.9 mods (including 707.9d CDA strip);
  --    nonexistent object creates no tokens (CR 111.12); instant/sorcery copy creates no tokens unless
  --    CopyModification adds a permanent type (CR 111.5).
  let cdaLegendDef : CardDef := {
    name := "Multani Test"
    manaCost := ManaCost.ofGenericAndColors 2 [.green]
    supertypes := #[.legendary]
    types := #[.creature]
    subtypes := #["Elf"]
    power := some 0
    toughness := some 0
    staticAbilities := #[.powerToughnessEqualLandsYouControl]
  }
  let gCopy0 := addPermanent (addPermanent (addPermanent g0 cdaLegendDef p0 p0) forest p0 p0) forest p0 p0
  let origObj := (gCopy0.permanentsOf p0).find? (·.name == "Multani Test") |>.get!
  let copySpec : TokenSpec :=
    .copyOf .target #[
      .setName "Shadow Copy",
      .setBasePT 1 1,
      .removeSupertype .legendary,
      .addTypes #[.artifact],
      .addSubtypes #[.zombie],
      .addColors (ColorSet.singleton .black),
      .addKeywords #[Keyword.haste],
      .addAbilities #[.onAttackMayMill 1]
    ]
  let gCopyReal := gCopy0.createKindTokens p0 copySpec 1 (copyCtx := { targetId := some origObj.id })
  let copyTok? := (gCopyReal.permanentsOf p0).find? (·.name == "Shadow Copy")
  let copyRealOk :=
    match copyTok? with
    | none => false
    | some tok =>
      tok.printed.isToken &&
      !gCopyReal.isLegendary tok &&
      gCopyReal.isArtifact tok && gCopyReal.isCreature tok &&
      gCopyReal.hasSubtype tok .elf && gCopyReal.hasSubtype tok .zombie &&
      (gCopyReal.colors tok).contains .green && (gCopyReal.colors tok).contains .black &&
      gCopyReal.hasHaste tok &&
      gCopyReal.power tok == 1 && gCopyReal.toughness tok == 1 &&
      tok.printed.triggeredAbilities.size == 1
  let bfCountBeforeMissing := gCopy0.battlefield.size
  let gCopyMissing := gCopy0.createKindTokens p0 (.copyOf .target #[]) 2
  let gCopyBadId := gCopy0.createKindTokens p0 (.copyOf .target #[]) 2 (copyCtx := { targetId := some ⟨999999⟩ })
  let copyMissingOk :=
    (gCopy0.resolveTokenPrinted? (.copyOf .target #[]) 0 {}).isNone &&
    (Game.tokenPrinted? (.copyOf .target #[])).isNone &&
    gCopyMissing.battlefield.size == bfCountBeforeMissing &&
    gCopyMissing.recentTokenIds.isEmpty &&
    gCopyBadId.battlefield.size == bfCountBeforeMissing &&
    gCopyBadId.recentTokenIds.isEmpty

  -- 5b. CR 111.5 / 304.4 / 307.4: no token is created for a copy of an instant/sorcery
  --     (even with CopyModification.addTypes #[.creature]) or any token with instant/sorcery type
  let testInstDef : CardDef := {
    name := "Test Bolt"
    manaCost := ManaCost.ofColors [.red]
    types := #[.instant]
  }
  let testSorcDef : CardDef := {
    name := "Test Ritual"
    manaCost := ManaCost.ofColors [.black]
    types := #[.sorcery]
  }
  let gInst0 := insertObject (insertObject g0 testInstDef p0 (.graveyard p0)) testSorcDef p0 (.graveyard p0)
  let instId := (gInst0.player p0).graveyard[0]!
  let sorcId := (gInst0.player p0).graveyard[1]!
  let bfBeforeInst := gInst0.battlefield.size
  let gInstNone := gInst0.createKindTokens p0 (.copyOf .target #[]) 1 (copyCtx := { targetId := some instId })
  let gSorcNone := gInst0.createKindTokens p0 (.copyOf .target #[]) 1 (copyCtx := { targetId := some sorcId })
  let gInstWithCreatureNone :=
    gInst0.createKindTokens p0 (.copyOf .target #[.addTypes #[.creature], .setBasePT 2 2]) 1
      (copyCtx := { targetId := some instId })
  let gCreatureAddInstNone :=
    gCopy0.createKindTokens p0 (.copyOf .target #[.addTypes #[.instant]]) 1
      (copyCtx := { targetId := some origObj.id })
  let gCreatureAddSorcNone :=
    gCopy0.createKindTokens p0 (.copyOf .target #[.addTypes #[.sorcery]]) 1
      (copyCtx := { targetId := some origObj.id })
  let customInstSpec : TokenSpec := .custom {
    name? := some "Illegal Instant Token"
    types := #[.instant, .creature]
    power? := some (.const 1)
    toughness? := some (.const 1)
  }
  let gCustomInstNone := g0.createKindTokens p0 customInstSpec 1
  let copyInstantSorceryOk :=
    (gInst0.resolveTokenPrinted? (.copyOf .target #[]) 0 { targetId := some instId }).isNone &&
    (gInst0.resolveTokenPrinted? (.copyOf .target #[]) 0 { targetId := some sorcId }).isNone &&
    (gInst0.resolveTokenPrinted? (.copyOf .target #[.addTypes #[.creature], .setBasePT 2 2]) 0
      { targetId := some instId }).isNone &&
    (gCopy0.resolveTokenPrinted? (.copyOf .target #[.addTypes #[.instant]]) 0
      { targetId := some origObj.id }).isNone &&
    (gCopy0.resolveTokenPrinted? (.copyOf .target #[.addTypes #[.sorcery]]) 0
      { targetId := some origObj.id }).isNone &&
    (g0.resolveTokenPrinted? customInstSpec 0 {}).isNone &&
    gInstNone.battlefield.size == bfBeforeInst && gInstNone.recentTokenIds.isEmpty &&
    gSorcNone.battlefield.size == bfBeforeInst && gSorcNone.recentTokenIds.isEmpty &&
    gInstWithCreatureNone.battlefield.size == bfBeforeInst && gInstWithCreatureNone.recentTokenIds.isEmpty &&
    gCreatureAddInstNone.battlefield.size == bfCountBeforeMissing && gCreatureAddInstNone.recentTokenIds.isEmpty &&
    gCreatureAddSorcNone.battlefield.size == bfCountBeforeMissing && gCreatureAddSorcNone.recentTokenIds.isEmpty &&
    gCustomInstNone.battlefield.size == g0.battlefield.size && gCustomInstNone.recentTokenIds.isEmpty

  -- 6. ManaSpendRestriction.notFromZone across graveyard, exile, hand, and live proposedManaSpend
  let gyRestrPool :=
    ManaPool.empty.addUnit { mana := .colorless, restriction := some (.notFromZone .graveyard) }
  let exileRestrPool :=
    ManaPool.empty.addUnit { mana := .colorless, restriction := some (.notFromZone .exile) }
  let gCastGy0 := insertObject g0 bear p0 (.graveyard p0)
  let gyBearId := (gCastGy0.player p0).graveyard.back!
  let gyBearObj := gCastGy0.object! gyBearId
  let fakeProp : ProposedSpell := {
    kind := .spell
    spellId := gyBearId
    caster := p0
    original := gyBearObj
    cost := ManaCost.ofGeneric 1
  }
  let gySpend := gCastGy0.proposedManaSpend fakeProp
  let notFromZoneOk :=
    !gyRestrPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, castFromZone := some .graveyard }) &&
    gyRestrPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, castFromZone := some .exile }) &&
    gyRestrPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, fromHand := true, castFromZone := some .hand }) &&
    gyRestrPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := false }) &&
    !exileRestrPool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, castFromZone := some .exile }) &&
    gySpend.castFromZone == some .graveyard &&
    !gySpend.fromHand &&
    !gCastGy0.restrictionAllowsProposed (some (.notFromZone .graveyard)) fakeProp &&
    gCastGy0.restrictionAllowsProposed (some .notSpellsFromHand) fakeProp

  -- 7. CopyTokenContext propagation across createAndMarkTokensAttacking (both holds arms &
  --    across PendingReplacement pause), EffectResolution.createTokensLifeGained, and
  --    FraChoice.mayCreateTokens
  let atkCopyNoHolds :=
    gCopy0.createAndMarkTokensAttacking p0 copySpec 1 false false
      (copyCtx := { targetId := some origObj.id })
  let atkCopyHolds :=
    gCopy0.createAndMarkTokensAttacking p0 copySpec 1 true true
      (copyCtx := { targetId := some origObj.id })
  let atkCopySubjSpec : TokenSpec := .copyOf .triggerSubject #[.setName "Subject Copy", .setBasePT 2 2]
  let atkCopySubj :=
    gCopy0.createAndMarkTokensAttacking p0 atkCopySubjSpec 1 true true
      (copyCtx := { triggerSubjectId := some origObj.id })
  -- Replacement pause inside createAndMarkTokensAttacking preserves copyCtx across both
  -- promptChooseReplacement and chainPendingReplacement:
  let foodCopySpec : TokenSpec :=
    .copyOf .target #[.setName "Paused Copy", .setBasePT 1 1, .removeSupertype .legendary,
      .addTypes #[.artifact], .addSubtypes #[.food]]
  let chainedCopySpec : TokenSpec :=
    .copyOf .target #[.setName "Chained Copy", .setBasePT 3 3, .removeSupertype .legendary]
  let idPauseExtra : ReplacementId := { kind := .foodAlsoCreatesTreasure, player := some p0 }
  let idPauseBecome : ReplacementId := { kind := .artifactTokensBecome, player := some p0 }
  let bonusBearDef : CardDef := { bear with name := "Bonus Food Bear", isToken := true }
  let replacedArtDef : CardDef := { bear with name := "Replaced Artifact", isToken := true }
  let gPause0 :=
    (gCopy0.createEffect (.replacement {
      id := idPauseExtra, affectedPlayer := p0,
      kind := .createExtraTokenWithFood p0 bonusBearDef
    })).createEffect (.replacement {
      id := idPauseBecome, affectedPlayer := p0,
      kind := .artifactTokensBecome p0 replacedArtDef
    })
  let gPause1 :=
    gPause0.createAndMarkTokensAttacking p0 foodCopySpec 1 true true
      (copyCtx := { targetId := some origObj.id })
  let gPauseChained :=
    gPause1.createAndMarkTokensAttacking p0 chainedCopySpec 1 true true
      (copyCtx := { targetId := some origObj.id })
  let gPauseDone := mustApply gPauseChained p0 (.chooseReplacement idPauseExtra)
  -- Triggered sequence caller (`applyTriggeredAbility`) forwards targets into createAndMarkTokensAttacking:
  let atkSeqAb : TriggeredAbility :=
    TriggeredAbility.triggered .attack {
      targeting := .of .creature
      resolution := .sequence [
        .createTokens copySpec (.fixed 1) true .you .none,
        .«if» (.atLeast (.count .creaturesYouControl) (.fixed 1)) .markRecentTokensAttacking
      ]
    }
  let gSeqRes := gCopy0.applyTriggeredAbility p0 atkSeqAb none #[.permanent origObj.id]
  -- EffectResolution.createTokensLifeGained forwards copyCtx:
  let gLifeGain0 := gCopy0.gainLife p0 2
  let gLifeGainTok :=
    gLifeGain0.applyEffect p0 {
      targeting := .of .creature
      resolution := .createTokensLifeGained copySpec
    } #[.permanent origObj.id]
  let lifeGainCopies := (gLifeGainTok.permanentsOf p0).filter (·.name == "Shadow Copy")
  -- FraChoice.mayCreateTokens forwards copyCtx:
  let gMayTok0 :=
    gCopy0.beginFraChoice p0 (.mayCreateTokens copySpec 1 { targetId := some origObj.id })
  let gMayTokAccept := mustApply gMayTok0 p0 .accept
  let copyCtxSitesOk :=
    ((atkCopyNoHolds.permanentsOf p0).find? (·.name == "Shadow Copy")).any (fun o => !o.status.attacking) &&
    ((atkCopyHolds.permanentsOf p0).find? (·.name == "Shadow Copy")).any (fun o => o.status.attacking) &&
    ((atkCopySubj.permanentsOf p0).find? (·.name == "Subject Copy")).any (fun o => o.status.attacking) &&
    gPause1.pending == .chooseReplacement p0 #[idPauseExtra, idPauseBecome] &&
    ((gPauseDone.permanentsOf p0).find? (·.name == "Bonus Food Bear")).any (·.status.attacking) &&
    ((gPauseDone.permanentsOf p0).find? (·.name == "Replaced Artifact")).any (·.status.attacking) &&
    ((gPauseDone.permanentsOf p0).find? (·.name == "Chained Copy")).any (·.status.attacking) &&
    ((gSeqRes.permanentsOf p0).find? (·.name == "Shadow Copy")).any (fun o => o.status.attacking) &&
    lifeGainCopies.size == 2 &&
    ((gMayTokAccept.permanentsOf p0).find? (·.name == "Shadow Copy")).isSome

  let replayOk :=
    replayOk49i1 #[
      gMapNonland, gMapNonlandAccept, gMapNonlandDecline, gMapLand,
      gRelicExp, gRelicExpAccept, gEmptyExp,
      gDepNonland, gDepNonlandAccept, gDepLand,
      gOwnLand, gOwnNonland, gOwnNonlandAccept,
      gInstNone, gInstWithCreatureNone, gCreatureAddInstNone, gCustomInstNone,
      atkCopyNoHolds, atkCopyHolds, atkCopySubj, gPause1, gPauseDone, gSeqRes, gLifeGainTok,
      gMayTok0, gMayTokAccept
    ]

  mustHoldP1Rev "1.incubatorName" incubatorOk &&
  mustHoldP1Rev "2.mapToken" mapOk &&
  mustHoldP1Rev "2b.exploreCr70144" exploreCr70144Ok &&
  mustHoldP1Rev "3.junkLanderMutagen" junkLanderMutagenOk &&
  mustHoldP1Rev "4.moloidAttackMayMill" moloidOk &&
  mustHoldP1Rev "5.copyOfReal" copyRealOk &&
  mustHoldP1Rev "5.copyOfMissing" copyMissingOk &&
  mustHoldP1Rev "5b.copyOfInstantSorceryCr1115" copyInstantSorceryOk &&
  mustHoldP1Rev "6.notFromZone" notFromZoneOk &&
  mustHoldP1Rev "7.copyTokenContextSites" copyCtxSitesOk &&
  mustHoldP1Rev "8.replayEquivalence" replayOk

end Phase1AbilityAlignmentReview

end Mtg.Engine.EventTests
