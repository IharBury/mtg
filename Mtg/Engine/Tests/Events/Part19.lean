import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests

private def clearLibrary (g : Game) (p : PlayerId) : Game :=
  (g.player p).library.foldl (fun acc id => (acc.move id .exile none (cause := some testCause)).1) g

section Phase53Item1EventAlignment

private def mustHold53i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase53Item1EventAlignment failed: {label}"

private def replayOk53i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with name := "P53i1 LegBear", supertypes := #[.legendary] }
  let zeroInstDef : CardDef := {
    name := "P53i1 ZeroInst"
    manaCost := ManaCost.zero
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let twoDmgTrigDef : CardDef := {
    creature "P53i1 CombatTrig" ManaCost.empty #["Warrior"] 2 2 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger (.damageDealt (.sameAs .this) .any (combatOnly := true)) (Effect.gainLife 1),
      TriggeredAbility.mkTrigger (.damageDealt (.sameAs .this) .any (combatOnly := true)) (Effect.gainLife 2)
    ]
  }
  let lethalAtkDef : CardDef := creature "P53i1 Lethal" ManaCost.empty #["Giant"] 25 25

  -- 1a(i). `Entering.receivePriority` & `Decisions.finishAndGrantPriority` prompt-settling
  --        `pendingPriority` preservation: `.finishResolutionChoice` settles via
  --        `pendingMayCastFromExile` (`finishResolutionChoiceGrantsPriority == false`,
  --        `anyContinuationSettlesControlFlow == true`, `hasImplicitPendingPriorityContinuation == true`),
  --        so `receivePriority p2` and `finishAndGrantPriority p2` MUST preserve `pendingPriority == some p2`!
  let gEx0 := insertObject g4 zeroInstDef p0 .exile
  let exCardId := (gEx0.objects.filter (·.zone == .exile)).back!.id
  let gPromptSettleRep :=
    gEx0.changes #[
      .pushContinuationFrame {},
      .pendingMayCastFromExile (some (p0, #[exCardId], 1)),
      .pendingReplacement (some .finishResolutionChoice),
      .pending (.chooseReplacement p0 #[])
    ]
  let gAfterRecvPrompt := gPromptSettleRep.receivePriority p2
  let gAfterFinishGrantPrompt := gPromptSettleRep.finishAndGrantPriority p2

  -- 1a(ii). `Casting.finishPostCast` `.chooseReplacement` ordering:
  --         (a) With `hadOuterReplacement == true`, `finishPostCast` does NOT chain `.finishResolutionChoice`
  --             ahead of caller-owned outer continuation;
  --         (b) With `hadOuterReplacement == false` and already-settling `.chooseReplacement` continuation
  --             (`.finishResolutionChoice` with `pendingMayCastFromExile`), `finishPostCast` preserves
  --             `pendingPriority` without chaining a duplicate `.receivePriority`.
  let gPostCastOuter0 :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishPostStep (.logExiledIfInExile ⟨9999⟩ "tail"))),
      .pending (.chooseReplacement p0 #[])
    ]
  let gPostCastOuter1 := gPostCastOuter0.finishPostCast p0 (hadOuterReplacement := true)
  let gPostCastSettling1 := gPromptSettleRep.finishPostCast p2 (hadOuterReplacement := false)

  -- 1a(iii). `Decisions.advanceProbeOnResume` `proposedSpell` clearing on `.seq (.finishPostCast ..) .finishResolutionChoice`,
  --          and `hadOuter == true` `.finishProposedSpellCosts .finalize` prompt/reversal settlement:
  let gWithProp0 := insertObject g4 zeroInstDef p0 (.hand p0)
  let spellId0 := (gWithProp0.player p0).hand.back!
  let fakeProp0 : ProposedSpell := {
    caster := p0
    cost := ManaCost.zero
    spellId := spellId0
    original := gWithProp0.object! spellId0
  }
  let gStalePropSeq :=
    gWithProp0.changes #[
      .proposedSpell (some fakeProp0),
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishPostCast p0 true true false) .finishResolutionChoice)),
      .pending (.chooseReplacement p0 #[])
    ]
  let gFinalizeSacPrompt :=
    (addPermanent gWithProp0 bear p0 p0).changes #[
      .proposedSpell (some { fakeProp0 with needsSacrificeOther := true }),
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishProposedSpellCosts .finalize true true false) .finishResolutionChoice)),
      .pending (.chooseReplacement p0 #[])
    ]

  -- 1a(iv). `finishResolutionChoiceGrantsPriority` runtime alignment:
  --         (a) `afterRandom != .none` -> does NOT grant priority;
  --         (b) outer continuation is non-priority prompt `.beginStepCont .declareAttackers` -> does NOT grant;
  --         (c) duplicate legends on battlefield -> final `receivePriorityOutcome` opens `.chooseLegend` -> does NOT grant;
  --         (d) outer continuation is explicit `.receivePriority p2` -> `firstContinuationPriorityGrant? == some (some p2)`.
  let gFrcRand :=
    g4.changes #[
      .pushContinuationFrame {},
      .afterRandom (.draw p0 1),
      .pendingReplacement (some .finishResolutionChoice),
      .pending (.chooseReplacement p0 #[])
    ]
  let gFrcOuterPrompt :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.beginStepCont .declareAttackers),
      .pendingReplacement (some .finishResolutionChoice),
      .pending (.chooseReplacement p0 #[])
    ]
  let gFrcOuterExplicit :=
    g4.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p2),
      .pendingReplacement (some .finishResolutionChoice),
      .pending (.chooseReplacement p0 #[])
    ]
  let gFrcLegend :=
    (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0).changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some .finishResolutionChoice),
      .pending (.chooseReplacement p0 #[])
    ]

  -- 1b(i). `.draw` step probe (`stepPriorityRecipient?`):
  --        Empty library in 2-player game (turn 2) -> CR 704.5b loss -> game over (`none`);
  --        Empty library in 4-player game (turn 2) -> `p0` loses, next living `p1` gets priority (`some p1`);
  --        `g.skipsFirstDraw` preserved (turn 1, starting player `p0`) -> skips draw, enters `.precombatMain` (`some p0`).
  let gDrawEmpty2 := (clearLibrary afterDraw p0).record (GameEvent.turnBegan 2 p0)
  let gDrawEmpty4 := (clearLibrary g4 p0).record (GameEvent.turnBegan 2 p0)
  let gDrawSkip := (clearLibrary afterDraw p0).change (.startingPlayer p0)

  -- 1b(ii). `.combatDamage` step probe (`stepPriorityRecipient?`):
  --         Lethal unblocked attacker in 2-player game -> game over (`none`);
  --         Unblocked attacker with 2 simultaneous combat-damage triggers -> ordering prompt (`none`).
  let gCbtLethal0 := addPermanent afterDraw lethalAtkDef p0 p0
  let lethalId := (gCbtLethal0.permanentsOf p0)[0]!.id
  let gCbtLethal :=
    mustApply (mustApply (gCbtLethal0.beginStep .declareAttackers) p0 (.declareAttackers #[lethalId] none #[] #[]) |>.advanceStep)
      p1 (.declareBlockers #[])
  let gCbtTrig0 := addPermanent afterDraw twoDmgTrigDef p0 p0
  let trigAtkId := (gCbtTrig0.permanentsOf p0)[0]!.id
  let gCbtTrig :=
    mustApply (mustApply (gCbtTrig0.beginStep .declareAttackers) p0 (.declareAttackers #[trigAtkId] none #[] #[]) |>.advanceStep)
      p1 (.declareBlockers #[])

  -- 1b(iii). `drainProbeNonPriorityCont` unhandled leaf (`.dealDamageToPlayer`) is NOT dropped:
  let unhandledDmgCont : PendingReplacement :=
    .dealDamageToPlayer p1 3 none false none false
  let gUnhandledRep :=
    g4.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some unhandledDmgCont),
      .pending (.chooseReplacement p0 #[])
    ]

  -- 1b(iv). `wasAssigningCombatDamage = some false` in `classifyFinishConcedePriority`:
  --         p0 attacks with a bear, p1 blocks it cleanly (no multi-attacker ambiguity),
  --         so `continueBlockerCombatAssignment` finishes without prompt and grants priority to `p0`!
  let gBlk0 := addPermanent (addPermanent g4 bear p0 p0) bear p1 p1
  let atkAId := (gBlk0.permanentsOf p0)[0]!.id
  let blkId := (gBlk0.permanentsOf p1)[0]!.id
  let gBlkAtk :=
    mustApply (gBlk0.beginStep .declareAttackers) p0 (.declareAttackers #[atkAId] (some p1) #[] #[])
  let gBlkDone :=
    mustApply gBlkAtk.advanceStep p1 (.declareBlockers #[(blkId, atkAId)])
  let fcCombatDone : PendingReplacement :=
    .finishConcede false none (some false) none false #[] none

  -- 1b(v). Sneak discard/sacrifice probes with opponent-owned attacker + `linkedExile` & caster-owned attacker:
  let sneakDiscDef : CardDef := {
    bear with
    name := "P53i1 SneakDisc"
    manaCost := ManaCost.ofGeneric 3
    spellAbility := some { additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.discardCard] }
    keywords := #[.sneak CostSpec.empty]
  }
  let gSnkOpp0 :=
    let g := emptyHand (emptyHand afterDraw p0) p1
    -- Spell already moved to `.stack` (CR 601.2a) so `p0`'s hand is empty!
    let g := insertObject g sneakDiscDef p0 .stack
    -- Opponent-owned bear stolen by p0, with a linked-exile card owned by p0!
    let g := addPermanent g bear p1 p0
    let g := insertObject g bear p0 .exile
    let atkId := (g.permanentsOf p0)[0]!.id
    let linkedId := (g.objects.filter (·.zone == .exile)).back!.id
    let g := g.change (.object atkId (.linkedExile #[linkedId]))
    let g := mustApply (g.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
    mustApply g.advanceStep p1 (.declareBlockers #[])
  let snkOppAtkId := (gSnkOpp0.permanentsOf p0)[0]!.id
  let snkDiscId := (gSnkOpp0.objects.filter (·.zone == .stack)).back!.id
  let snkOppProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.zero
    spellId := snkDiscId
    original := gSnkOpp0.object! snkDiscId
    needsDiscardCard := true
    sneakAttacker := some snkOppAtkId
  }
  let gSnkOppWithProp := gSnkOpp0.change (.proposedSpell (some snkOppProp))
  -- Also test `probeAfterUnpaidSneak` returns `linkedExile` bear to p0's battlefield, making sacrifice available:
  let gSnkAfterOppProbe := gSnkOpp0.probeAfterUnpaidSneak snkOppProp
  -- And caster-owned attacker returns to p0's hand, making discard available from an empty hand:
  let gSnkOwn0 :=
    let g := emptyHand afterDraw p0
    let g := insertObject (addPermanent g bear p0 p0) sneakDiscDef p0 .stack
    let atkId := (g.permanentsOf p0)[0]!.id
    let g := mustApply (g.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
    mustApply g.advanceStep p1 (.declareBlockers #[])
  let snkOwnAtkId := (gSnkOwn0.permanentsOf p0)[0]!.id
  let snkOwnDiscId := (gSnkOwn0.objects.filter (·.zone == .stack)).back!.id
  let snkOwnProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.zero
    spellId := snkOwnDiscId
    original := gSnkOwn0.object! snkOwnDiscId
    needsDiscardCard := true
    sneakAttacker := some snkOwnAtkId
  }
  let gSnkOwnAfterProbe := gSnkOwn0.probeAfterUnpaidSneak snkOwnProp

  -- 1b(vi). Turn-face-up (`probeCompleteTurnFaceUpOutcome` / `advanceProbeOnResume`) `hadOuter := false`
  --         runtime parity (explicit `caster` grant, legend-rule SBA prompt, `flushQueuedLinkedExile`
  --         `.chooseReplacement` pause with `receivePriority caster` vs `hadOuter := true` `.finishResolutionChoice`,
  --         non-recursive classification under an already-open `.chooseReplacement`, and `.seq` tail propagation):
  let morphCleanDef : CardDef := {
    creature "P53i1 MorphClean" ManaCost.empty #["Human"] 3 3 with
    keywords := #[.morph CostSpec.empty]
  }
  let morphLegDef : CardDef := {
    creature "P53i1 MorphLeg" ManaCost.empty #["Human"] 3 3 with
    supertypes := #[.legendary]
    keywords := #[.morph CostSpec.empty]
  }
  let gMorphClean0 := addPermanent g4 morphCleanDef p1 p1
  let morphCleanId := (gMorphClean0.permanentsOf p1)[0]!.id
  let gMorphClean := setFaceDown gMorphClean0 morphCleanId true
  let gMorphCleanRun := gMorphClean.resumePendingReplacement (.finishTurnFaceUp p1 morphCleanId false)
  let morphCleanProp : ProposedSpell := {
    caster := p1
    cost := ManaCost.empty
    spellId := morphCleanId
    sourceId := some morphCleanId
    original := gMorphClean.object! morphCleanId
    originalSnapshot := gMorphClean.snapshot (gMorphClean.object! morphCleanId)
    kind := .turnFaceUp
  }
  let gMorphCleanProp := gMorphClean.changes #[.saveProposalCheckpoint, .proposedSpell (some morphCleanProp)]

  let gMorphLeg0 := addPermanent (addPermanent g4 morphLegDef p1 p1) morphLegDef p1 p1
  let morphLegId := (gMorphLeg0.permanentsOf p1)[1]!.id
  let gMorphLeg := setFaceDown gMorphLeg0 morphLegId true
  let gMorphLegRun := gMorphLeg.resumePendingReplacement (.finishTurnFaceUp p1 morphLegId false)

  let leyADef : CardDef := { name := "P53i1 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P53i1 LeyB", types := #[.enchantment] }
  let gMorphFlush0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent g4 morphCleanDef p1 p1) leyADef p0 p0) leyBDef p0 p0)
      bear p0 .exile
  let morphFlushId := (gMorphFlush0.permanentsOf p1)[0]!.id
  let leyAId := (gMorphFlush0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let leyBId := (gMorphFlush0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let exiledRetId := (gMorphFlush0.objects.filter (·.zone == .exile)).back!.id
  let ridA : ReplacementId := { kind := .entersWithExtraCounters, object := some leyAId, counterKind := some .plusOnePlusOne }
  let ridB : ReplacementId := { kind := .entersWithExtraCounters, object := some leyBId, counterKind := some .plusOnePlusOne }
  let gMorphFlush :=
    ((((setFaceDown gMorphFlush0 morphFlushId true).createEffect
      (.replacement {
        id := ridA, source := some leyAId, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := ridB, source := some leyBId, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause)).change
      (.queueLinkedExile #[exiledRetId]))
  let gMorphFlushRun := gMorphFlush.resumePendingReplacement (.finishTurnFaceUp p1 morphFlushId false)
  let gMorphFlushOuterRun := gMorphFlush.resumePendingReplacement (.finishTurnFaceUp p1 morphFlushId true)

  -- Face-up waiting under an already-open `.chooseReplacement` (both real sacrifice deferral and direct `.chooseReplacement`):
  let gMorphSac0 := addPermanent (addPermanent g4 morphCleanDef p1 p1) bear p1 p1
  let morphSacId := (gMorphSac0.permanentsOf p1).find? (·.name == morphCleanDef.name) |>.get!.id
  let morphFodId := (gMorphSac0.permanentsOf p1).find? (·.name == bear.name) |>.get!.id
  let idExMorphFod : ReplacementId := { kind := .untilEotExileIfDies, object := some morphFodId }
  let gMorphSac1 :=
    ((setFaceDown gMorphSac0 morphSacId true).createEffect
      (.replacement { id := idExMorphFod, affectedPlayer := p1, kind := .exileInsteadOfGraveyard (some morphFodId) false })
      (cause := some testCause)).recordPutCounters morphFodId .finality 1 (some p1) (cause := some testCause)
  let morphSacProp : ProposedSpell := {
    caster := p1
    cost := ManaCost.empty
    spellId := morphSacId
    sourceId := some morphSacId
    original := gMorphSac1.object! morphSacId
    originalSnapshot := gMorphSac1.snapshot (gMorphSac1.object! morphSacId)
    kind := .turnFaceUp
    needsSacrificeOther := true
  }
  let gMorphSacPrompt :=
    gMorphSac1.changes #[.saveProposalCheckpoint, .proposedSpell (some morphSacProp), .pending (.sacrificePermanent p1 morphSacId)]
  let gMorphSacPaused := mustApply gMorphSacPrompt p1 (.sacrifice morphFodId)
  let gMorphSacDone := mustApply gMorphSacPaused p1 (.chooseReplacement idExMorphFod)
  let gMorphOpenFalse :=
    gMorphClean.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishTurnFaceUp p1 morphCleanId false)),
      .pending (.chooseReplacement p0 #[])
    ]
  let gMorphOpenTrue :=
    gMorphClean.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishTurnFaceUp p1 morphCleanId true)),
      .pending (.chooseReplacement p0 #[])
    ]

  -- `.finishProposedSpellCosts` (`.turnFaceUp`):
  -- (a) while `.chooseReplacement` is open (`Decisions.lean:5511-5513`), resuming the leaf leaves
  --     `.chooseReplacement` open and the morph face down (deferred, no flip);
  -- (b) once `.chooseReplacement` is resolved (via `anyContinuation*` / `probeGameForPendingReplacement`)
  --     or when `pending` is a non-replacement prompt (`.activateManaAbilities`), the `Decisions.lean:5623` path clears
  --     `pending`, flips, and preserves non-self prefix/suffix nodes in `localOuter?`;
  -- (c) departed morph reverses immediately rather than probing turn-face-up.
  let morphLegProp : ProposedSpell := {
    caster := p1
    cost := ManaCost.empty
    spellId := morphLegId
    sourceId := some morphLegId
    original := gMorphLeg.object! morphLegId
    originalSnapshot := gMorphLeg.snapshot (gMorphLeg.object! morphLegId)
    kind := .turnFaceUp
  }
  let gMorphLegPropOpen :=
    gMorphLeg.changes #[.saveProposalCheckpoint, .proposedSpell (some morphLegProp), .pending (.chooseReplacement p0 #[])]
  let gMorphLegPropOpenRun :=
    gMorphLegPropOpen.resumePendingReplacement (.finishProposedSpellCosts .finalize true false false)
  let gMorphLegPropQueued :=
    gMorphLegPropOpen.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishProposedSpellCosts .finalize true true false) .finishResolutionChoice))
    ]
  let gMorphCleanPropOpen :=
    gMorphCleanProp.change (.pending (.chooseReplacement p0 #[]))
  let gMorphCleanPropOpenRun :=
    gMorphCleanPropOpen.resumePendingReplacement (.finishProposedSpellCosts .finalize true false false)
  let gMorphCleanPropQueued :=
    gMorphCleanPropOpen.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishProposedSpellCosts .finalize true false false))
    ]
  let gMorphCleanPropPayMana :=
    gMorphCleanProp.change (.pending (.activateManaAbilities p1))
  let gMorphPropPrefixSelf :=
    gMorphCleanProp.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.receivePriority p2) (.finishProposedSpellCosts .finalize true false false)))
    ]
  let gMorphPropPrefixSelfRun :=
    match gMorphPropPrefixSelf.finishProposedSpellCosts .finalize true false false with
    | .ok g => g
    | .error e => panic! s!"gMorphPropPrefixSelfRun failed: {e}"
  let gMorphPropPrefixOtherFaceUp :=
    gMorphCleanProp.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.receivePriority p2) (.finishTurnFaceUp p1 morphCleanId true)))
    ]
  let gMorphPropPrefixOtherFaceUpRun :=
    match gMorphPropPrefixOtherFaceUp.finishProposedSpellCosts .finalize true false false with
    | .ok g => g
    | .error e => panic! s!"gMorphPropPrefixOtherFaceUpRun failed: {e}"
  let gMorphPropOtherFaceUpThenRecv :=
    gMorphCleanProp.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishTurnFaceUp p1 morphCleanId true) (.receivePriority p2)))
    ]
  let gMorphPropOtherFaceUpThenRecvRun :=
    match gMorphPropOtherFaceUpThenRecv.finishProposedSpellCosts .finalize true false false with
    | .ok g => g
    | .error e => panic! s!"gMorphPropOtherFaceUpThenRecvRun failed: {e}"
  let gMorphGoneOpenRep :=
    ((gMorphCleanProp.move morphCleanId (.graveyard p1) none (verb := some .destroy) (cause := some testCause)).1).change
      (.pending (.chooseReplacement p0 #[]))
  let gMorphGoneOpenRepNoCkpt := gMorphGoneOpenRep.change .clearProposalCheckpoint

  -- Unstripped `.seq (.finishTurnFaceUp ..) tail` under an already-open `.chooseReplacement`:
  let gMorphLegOpenSeqFalse :=
    gMorphLeg.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishTurnFaceUp p1 morphLegId false) .finishResolutionChoice)),
      .pending (.chooseReplacement p0 #[])
    ]
  let gMorphLegOpenSeqTrue :=
    gMorphLeg.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishTurnFaceUp p1 morphLegId true) .finishResolutionChoice)),
      .pending (.chooseReplacement p0 #[])
    ]
  let gMorphCleanOpenSeqFalse :=
    gMorphClean.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishTurnFaceUp p1 morphCleanId false) (.receivePriority p2))),
      .pending (.chooseReplacement p0 #[])
    ]
  let gMorphCleanOpenSeqTrue :=
    gMorphClean.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.seq (.finishTurnFaceUp p1 morphCleanId true) (.receivePriority p2))),
      .pending (.chooseReplacement p0 #[])
    ]

  -- Post-resume `g1.priority` classification with pre-existing `pendingReplacement` vs `outerPendingReplacements`:
  let gMorphPreRecv :=
    gMorphClean.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.receivePriority p2))
    ]
  let gMorphPreRecvRun := gMorphPreRecv.resumePendingReplacement (.finishTurnFaceUp p1 morphCleanId false)
  let gMorphPreOuter :=
    gMorphClean.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p2),
      .pendingReplacement (some (.gainLife p0 1 (some testCause)))
    ]
  let gMorphPreOuterRun := gMorphPreOuter.resumePendingReplacement (.finishTurnFaceUp p1 morphCleanId false)
  let gMorphOnlyOuter :=
    gMorphClean.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.receivePriority p2)
    ]
  let gMorphOnlyOuterRun := gMorphOnlyOuter.resumePendingReplacement (.finishTurnFaceUp p1 morphCleanId false)

  let item1aOk :=
    mustHold53i1 "1a_receivePriorityPreservesPendingPriorityOnPromptSettle"
      (gAfterRecvPrompt.pendingPriority == some p2 &&
       gAfterRecvPrompt.pendingReplacement == some .finishResolutionChoice) &&
    mustHold53i1 "1a_finishAndGrantPriorityPreservesPendingPriorityOnPromptSettle"
      (gAfterFinishGrantPrompt.pendingPriority == some p2 &&
       gAfterFinishGrantPrompt.pendingReplacement == some .finishResolutionChoice) &&
    mustHold53i1 "1a_finishPostCastOuterDoesNotPrependFrc"
      (gPostCastOuter1.pendingReplacement == gPostCastOuter0.pendingReplacement) &&
    mustHold53i1 "1a_finishPostCastSettlingPreservesPendingPriority"
      (gPostCastSettling1.pendingPriority == some p2 &&
       gPostCastSettling1.pendingReplacement == some .finishResolutionChoice) &&
    mustHold53i1 "1a_advanceProbeClearsProposedSpellOnSeq"
      (gStalePropSeq.anyContinuationGrantsPriority &&
       gStalePropSeq.anyContinuationSettlesControlFlow &&
       !gFinalizeSacPrompt.anyContinuationGrantsPriority &&
       gFinalizeSacPrompt.anyContinuationSettlesControlFlow) &&
    mustHold53i1 "1a_finishResolutionChoiceRuntimeAlignment"
      (!gFrcRand.anyContinuationGrantsPriority &&
       !gFrcOuterPrompt.anyContinuationGrantsPriority &&
       gFrcOuterPrompt.anyContinuationSettlesControlFlow &&
       gFrcOuterExplicit.firstContinuationPriorityGrant? == some (some p2) &&
       !gFrcLegend.anyContinuationGrantsPriority &&
       gFrcLegend.anyContinuationSettlesControlFlow)

  let item1bOk :=
    mustHold53i1 "1b_drawStepProbes"
      (gDrawEmpty2.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .draw)) == none &&
       gDrawEmpty4.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .draw)) == some p1 &&
       gDrawSkip.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .draw)) == some p0) &&
    mustHold53i1 "1b_combatDamageStepProbes"
      (gCbtLethal.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .combatDamage)) == none &&
       gCbtTrig.priorityRecipientOfContinuation? false (.finishPostStep (.beginStepBody .combatDamage)) == none) &&
    mustHold53i1 "1b_unhandledDrainLeafNotDropped"
      (!gUnhandledRep.anyContinuationGrantsPriority &&
       gUnhandledRep.priorityRecipientOfContinuation? false unhandledDmgCont == none) &&
    mustHold53i1 "1b_wasAssigningCombatDamageGrantsWhenUnambiguous"
      (gBlkDone.continuationGrantsPriority false fcCombatDone &&
       gBlkDone.priorityRecipientOfContinuation? false fcCombatDone == some p0) &&
    mustHold53i1 "1b_sneakLinkedExileAndOwnerDiscardProbes"
      ((gSnkAfterOppProbe.player p0).hand.isEmpty && -- opp's attacker went to opp's hand, NOT p0's!
       !(gSnkAfterOppProbe.permanentsOf p0).isEmpty && -- linkedExile bear returned to p0!
       (gSnkOwnAfterProbe.player p0).hand.size == 1 && -- caster-owned attacker returned to p0's hand!
       !gSnkOppWithProp.continuationGrantsPriority false (.finishProposedSpellCosts .sneak true false false)) &&
    mustHold53i1 "1b_turnFaceUpHadOuterAndOpenReplacementProbes"
      (gMorphClean.continuationGrantsPriority false (.finishTurnFaceUp p1 morphCleanId false) &&
       gMorphClean.continuationSettlesControlFlow false (.finishTurnFaceUp p1 morphCleanId false) &&
       gMorphClean.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphCleanId false) == some p1 &&
       gMorphClean.firstPriorityGrantRecipient? false (.finishTurnFaceUp p1 morphCleanId false) == some (some p1) &&
       gMorphCleanRun.pending == .none &&
       gMorphCleanRun.priority == p1 &&
       !(gMorphCleanRun.object! morphCleanId).status.faceDown &&
       gMorphCleanProp.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p1 &&
       !gMorphLeg.continuationGrantsPriority false (.finishTurnFaceUp p1 morphLegId false) &&
       gMorphLeg.continuationSettlesControlFlow false (.finishTurnFaceUp p1 morphLegId false) &&
       gMorphLeg.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphLegId false) == none &&
       (match gMorphLegRun.pending with | .chooseLegend q _ _ => q == p1 | _ => false) &&
       !gMorphLeg.continuationGrantsPriority false (.seq (.finishTurnFaceUp p1 morphLegId false) .finishResolutionChoice) &&
       gMorphLeg.continuationSettlesControlFlow false (.seq (.finishTurnFaceUp p1 morphLegId false) .finishResolutionChoice) &&
       gMorphClean.priorityRecipientOfContinuation? false (.seq (.finishTurnFaceUp p1 morphCleanId true) (.receivePriority p2)) == some p2 &&
       gMorphFlush.continuationGrantsPriority false (.finishTurnFaceUp p1 morphFlushId false) &&
       gMorphFlush.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphFlushId false) == some p1 &&
       gMorphFlush.firstPriorityGrantRecipient? false (.finishTurnFaceUp p1 morphFlushId false) == some (some p1) &&
       (match gMorphFlushRun.pending with | .chooseReplacement q cs => q == p0 && cs.size == 2 | _ => false) &&
       gMorphFlushRun.firstContinuationPriorityGrant? == some (some p1) &&
       gMorphFlush.continuationGrantsPriority false (.finishTurnFaceUp p1 morphFlushId true) &&
       gMorphFlush.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphFlushId true) == none &&
       gMorphFlush.firstPriorityGrantRecipient? false (.finishTurnFaceUp p1 morphFlushId true) == some none &&
       (match gMorphFlushOuterRun.pending with | .chooseReplacement q cs => q == p0 && cs.size == 2 | _ => false) &&
       gMorphFlushOuterRun.firstContinuationPriorityGrant? == some none &&
       (match gMorphSacPaused.pending with | .chooseReplacement q cs => q == p1 && cs.size == 2 | _ => false) &&
       gMorphSacPaused.anyContinuationSettlesControlFlow &&
       gMorphSacPaused.anyContinuationGrantsPriority &&
       gMorphSacPaused.firstContinuationPriorityGrant? == some (some p1) &&
       gMorphSacPaused.continuationSettlesControlFlow false (.finishTurnFaceUp p1 morphSacId false) &&
       gMorphSacPaused.continuationGrantsPriority false (.finishTurnFaceUp p1 morphSacId false) &&
       (gMorphSacPaused.change (.pendingReplacement none)).priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphSacId false) == some p1 &&
       gMorphSacDone.pending == .none &&
       gMorphSacDone.priority == p1 &&
       !(gMorphSacDone.object! morphSacId).status.faceDown &&
       gMorphOpenFalse.anyContinuationSettlesControlFlow &&
       gMorphOpenFalse.anyContinuationGrantsPriority &&
       gMorphOpenFalse.firstContinuationPriorityGrant? == some (some p1) &&
       gMorphOpenFalse.continuationSettlesControlFlow false (.finishTurnFaceUp p1 morphCleanId false) &&
       gMorphOpenFalse.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphCleanId false) == some p1 &&
       !gMorphOpenTrue.anyContinuationSettlesControlFlow &&
       !gMorphOpenTrue.anyContinuationGrantsPriority &&
       !gMorphOpenTrue.continuationSettlesControlFlow false (.finishTurnFaceUp p1 morphCleanId true) &&
       -- `.finishProposedSpellCosts` (`.turnFaceUp`) deferred while `.chooseReplacement` is open (`Decisions.lean:5511-5513`):
       gMorphLegPropOpenRun.pending == .chooseReplacement p0 #[] &&
       (gMorphLegPropOpenRun.object! morphLegId).status.faceDown &&
       !gMorphLegPropOpen.continuationGrantsPriority false (.finishProposedSpellCosts .finalize true false false) &&
       gMorphLegPropOpen.continuationSettlesControlFlow false (.finishProposedSpellCosts .finalize true false false) &&
       !gMorphLegPropOpen.continuationGrantsPriority false (.seq (.finishProposedSpellCosts .finalize true false false) .finishResolutionChoice) &&
       gMorphLegPropOpen.continuationSettlesControlFlow false (.seq (.finishProposedSpellCosts .finalize true false false) .finishResolutionChoice) &&
       !gMorphLegPropOpen.continuationGrantsPriority false (.seq (.finishProposedSpellCosts .finalize true true false) .finishResolutionChoice) &&
       gMorphCleanPropOpenRun.pending == .chooseReplacement p0 #[] &&
       (gMorphCleanPropOpenRun.object! morphCleanId).status.faceDown &&
       !gMorphCleanPropOpen.continuationGrantsPriority false (.finishProposedSpellCosts .finalize true false false) &&
       gMorphCleanPropOpen.continuationSettlesControlFlow false (.finishProposedSpellCosts .finalize true false false) &&
       gMorphCleanPropOpen.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == none &&
       -- Once `.chooseReplacement` is resolved (via `anyContinuation*`) or on non-replacement `.activateManaAbilities` (`Decisions.lean:5623`):
       !gMorphLegPropQueued.anyContinuationGrantsPriority &&
       gMorphLegPropQueued.anyContinuationSettlesControlFlow &&
       gMorphCleanPropQueued.anyContinuationGrantsPriority &&
       gMorphCleanPropQueued.firstContinuationPriorityGrant? == some (some p1) &&
       gMorphCleanPropPayMana.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p1 &&
       gMorphCleanPropPayMana.priorityRecipientOfContinuation? false (.seq (.finishProposedSpellCosts .finalize true true false) (.receivePriority p2)) == some p2 &&
       -- Non-self prefix/suffix preservation in `localOuter?` (`removeExactPendingReplacement`):
       gMorphPropPrefixSelfRun.pending == .none &&
       gMorphPropPrefixSelfRun.priority == p2 &&
       gMorphPropPrefixSelf.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p2 &&
       gMorphPropPrefixOtherFaceUpRun.pending == .none &&
       gMorphPropPrefixOtherFaceUpRun.priority == p0 &&
       gMorphPropPrefixOtherFaceUp.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p0 &&
       gMorphPropOtherFaceUpThenRecvRun.pending == .none &&
       gMorphPropOtherFaceUpThenRecvRun.priority == p2 &&
       gMorphPropOtherFaceUpThenRecv.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p2 &&
       -- Departed morph under open `.chooseReplacement` classifies as proposal reversal:
       gMorphGoneOpenRep.priorityRecipientOfContinuation? false (.finishProposedSpellCosts .finalize true false false) == some p1 &&
       gMorphGoneOpenRep.continuationGrantsPriority false (.finishProposedSpellCosts .finalize false false false) &&
       !gMorphGoneOpenRepNoCkpt.continuationGrantsPriority false (.finishProposedSpellCosts .finalize true false false) &&
       !gMorphGoneOpenRepNoCkpt.continuationSettlesControlFlow false (.finishProposedSpellCosts .finalize true false false) &&
       -- Unstripped `.seq (.finishTurnFaceUp ..) tail` under open `.chooseReplacement`:
       !gMorphLegOpenSeqFalse.continuationGrantsPriority false (.seq (.finishTurnFaceUp p1 morphLegId false) .finishResolutionChoice) &&
       gMorphLegOpenSeqFalse.continuationSettlesControlFlow false (.seq (.finishTurnFaceUp p1 morphLegId false) .finishResolutionChoice) &&
       !gMorphLegOpenSeqFalse.anyContinuationGrantsPriority &&
       gMorphLegOpenSeqFalse.anyContinuationSettlesControlFlow &&
       !gMorphLegOpenSeqTrue.continuationGrantsPriority false (.seq (.finishTurnFaceUp p1 morphLegId true) .finishResolutionChoice) &&
       gMorphLegOpenSeqTrue.continuationSettlesControlFlow false (.seq (.finishTurnFaceUp p1 morphLegId true) .finishResolutionChoice) &&
       !gMorphLegOpenSeqTrue.anyContinuationGrantsPriority &&
       gMorphLegOpenSeqTrue.anyContinuationSettlesControlFlow &&
       gMorphCleanOpenSeqFalse.priorityRecipientOfContinuation? false (.seq (.finishTurnFaceUp p1 morphCleanId false) (.receivePriority p2)) == some p1 &&
       gMorphCleanOpenSeqFalse.firstContinuationPriorityGrant? == some (some p1) &&
       gMorphCleanOpenSeqTrue.priorityRecipientOfContinuation? false (.seq (.finishTurnFaceUp p1 morphCleanId true) (.receivePriority p2)) == some p2 &&
       gMorphCleanOpenSeqTrue.firstContinuationPriorityGrant? == some (some p2) &&
       -- Post-resume `g1.priority` with pre-existing `pendingReplacement` vs `outerPendingReplacements`:
       gMorphPreRecvRun.pending == .none &&
       gMorphPreRecvRun.priority == p0 &&
       gMorphPreRecv.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphCleanId false) == some p0 &&
       gMorphPreOuterRun.pending == .none &&
       gMorphPreOuterRun.priority == p2 &&
       gMorphPreOuter.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphCleanId false) == some p2 &&
       gMorphOnlyOuterRun.pending == .none &&
       gMorphOnlyOuterRun.priority == p1 &&
       gMorphOnlyOuter.priorityRecipientOfContinuation? false (.finishTurnFaceUp p1 morphCleanId false) == some p1)

  mustHold53i1 "1a" item1aOk &&
  mustHold53i1 "1b" item1bOk &&
  mustHold53i1 "1.replay"
    (replayOk53i1 #[
      gAfterRecvPrompt, gAfterFinishGrantPrompt, gPostCastOuter1, gPostCastSettling1,
      gStalePropSeq, gFinalizeSacPrompt, gFrcRand, gFrcOuterPrompt, gFrcOuterExplicit, gFrcLegend,
      gDrawEmpty2, gDrawEmpty4, gDrawSkip, gCbtLethal, gCbtTrig, gBlkDone, gSnkOpp0, gSnkOwn0,
      gMorphCleanRun, gMorphLegRun, gMorphFlushRun, gMorphFlushOuterRun, gMorphSacPaused, gMorphSacDone,
      gMorphLegPropOpenRun, gMorphCleanPropOpenRun, gMorphPropPrefixSelfRun, gMorphPropPrefixOtherFaceUpRun,
      gMorphPropOtherFaceUpThenRecvRun, gMorphPreRecvRun, gMorphPreOuterRun, gMorphOnlyOuterRun ])

end Phase53Item1EventAlignment

section Phase53Item2EventAlignment

private def mustHold53i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase53Item2EventAlignment failed: {label}"

private def replayOk53i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let copy1Def : CardDef := { bear with name := "P53i2 CopyOne" }
  let copy2Def : CardDef := { bear with name := "P53i2 CopyTwo" }
  let embDef : CardDef := { name := "P53i2 Emb", types := #[.enchantment] }
  let relicDef : CardDef := { name := "P53i2 Relic", types := #[.artifact] }
  let exCardDef : CardDef := {
    name := "P53i2 ExiledSpell", manaCost := ManaCost.ofGeneric 1,
    types := #[.instant], spellAbility := some { effect := Effect.gainLife 1 }
  }

  -- 2a(i). Deduplicated deferred `.playFromExile` logs (`PostStep.logExpiredPlayFromExile`
  --        with `startEventIdx`, `containsDeferredPlayFromExile`, and `hasPlayFromExileLoggedInSlice`
  --        across intervening `.expired` events):
  let gPfe0 := insertObject (addPermanent g4 relicDef p0 p0) exCardDef p0 .exile
  let pfeRelicId := (gPfe0.permanentsOf p0)[0]!.id
  let pfeCardId := (gPfe0.objects.filter (·.zone == .exile)).back!.id
  let gPfe1 :=
    (gPfe0.createEffect (.permission (some p0) (.playFromExile pfeCardId { player := p0 }) (.whileSourceOnBattlefield pfeRelicId))
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile pfeCardId { player := p0 }) .untilEndOfTurn)
      (cause := some testCause)
  let pfeStartIdx := gPfe1.events.size
  let pfePreLogs := gPfe1.log.size
  -- Move relic away AND expire EOT so both playFromExile effects expire; call `logExpiredPlayFromExileIds` twice:
  let (gPfe2, _) := gPfe1.move pfeRelicId .exile none (cause := some testCause)
  let gPfe3 := gPfe2.expireEffectsByDuration (fun _ d => d == .untilEndOfTurn) (some testCause)
  let gPfe4 := gPfe3.logExpiredPlayFromExileIds #[pfeCardId] pfeStartIdx
  let pfeLogCount :=
    (gPfe4.log.extract pfePreLogs gPfe4.log.size).filter
      (·.endsWith "can no longer be played from exile") |>.size
  -- Also verify `PendingReplacement.containsDeferredPlayFromExile` detects queued post-step:
  let deferredPr : PendingReplacement :=
    .seq (.finishPostStep (.logExpiredPlayFromExile #[pfeCardId] pfeStartIdx)) (.receivePriority p0)

  -- 2a(ii). Outer leave-game `.playFromExile` deferral: p1 owns TWO relics each granting `.playFromExile`
  --         on the same exiled card; when p1 leaves the game, only ONE expiry log is emitted!
  let gLeavePfe0 :=
    insertObject (addPermanent (addPermanent g4 relicDef p1 p1) relicDef p1 p1) exCardDef p0 .exile
  let lpRelic1 := (gLeavePfe0.permanentsOf p1)[0]!.id
  let lpRelic2 := (gLeavePfe0.permanentsOf p1)[1]!.id
  let lpCardId := (gLeavePfe0.objects.filter (·.zone == .exile)).back!.id
  let gLeavePfe1 :=
    (gLeavePfe0.createEffect (.permission (some p0) (.playFromExile lpCardId { player := p0 }) (.whileSourceOnBattlefield lpRelic1))
      (cause := some testCause)).createEffect
      (.permission (some p0) (.playFromExile lpCardId { player := p0 }) (.whileSourceOnBattlefield lpRelic2))
      (cause := some testCause)
  let lpPreLogs := gLeavePfe1.log.size
  let gLeavePfeAfter := mustApply gLeavePfe1 p1 .concede
  let lpLogCount :=
    (gLeavePfeAfter.log.extract lpPreLogs gLeavePfeAfter.log.size).filter
      (·.endsWith "can no longer be played from exile") |>.size

  -- 2a(iii). `Core.expireLeavingObjectEffectsWithLogs` `.whileInZone` command emblem regression:
  --          Anchor permanent `ancId` has a `.whileInZone ancId .battlefield` command emblem `embId`
  --          granting BOTH control of opponent's bear (`tgtCtrlId`) to `p0` AND `.copy copy1Def` on
  --          `tgtCopyId` (stacked with `.copy copy2Def` `.whileInZone ancId .battlefield`).
  --          When `ancId` leaves battlefield, `embId` ceases, control reverts to `p1`, and stacked copy logs collapse!
  let gWiz0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent g4 relicDef p0 p0) bear p1 p1) bear p2 p2)
      embDef p0 .command (some p0)
  let wizAncId := (gWiz0.permanentsOf p0)[0]!.id
  let wizCtrlId := (gWiz0.permanentsOf p1)[0]!.id
  let wizCopyId := (gWiz0.permanentsOf p2)[0]!.id
  let wizEmbId := (gWiz0.objects.filter (·.zone == .command)).back!.id
  let gWiz1 :=
    ((((gWiz0.createEffect (.gameRule (.commandEmblem wizEmbId) (.whileInZone wizAncId .battlefield))
        (cause := some testCause)).createEffect
      (.layered (.objects #[wizCtrlId]) (.control p0) (.whileInZone wizEmbId .command))
        (cause := some testCause)).createEffect
      (.layered (.objects #[wizCopyId]) (.copy copy1Def) (.whileInZone wizEmbId .command))
        (cause := some testCause)).createEffect
      (.layered (.objects #[wizCopyId]) (.copy copy2Def) (.whileInZone wizAncId .battlefield))
        (cause := some testCause))
  let wizPreLogs := gWiz1.log.size
  let (gWizAfter, _) := gWiz1.move wizAncId .exile none (cause := some testCause)
  let wizCopyEndLogs :=
    (gWizAfter.log.extract wizPreLogs gWizAfter.log.size).filter
      (fun s => mentions s "is no longer a copy of")

  -- 2a(iv). Sibling emblems ending together in `ceaseEndingCommandEmblemsWhere` collapse stacked copy logs:
  let gSib0 :=
    insertObject (insertObject (addPermanent g4 bear p0 p0) embDef p1 .command (some p1))
      embDef p1 .command (some p1)
  let sibTgtId := (gSib0.permanentsOf p0)[0]!.id
  let sibCmds := gSib0.objects.filter (·.zone == .command)
  let sibE1 := sibCmds[0]!.id
  let sibE2 := sibCmds[1]!.id
  let gSib1 :=
    ((((gSib0.createEffect (.gameRule (.commandEmblem sibE1) (.untilNextTurnOf p0)) (cause := some testCause)).createEffect
      (.gameRule (.commandEmblem sibE2) (.untilNextTurnOf p0)) (cause := some testCause)).createEffect
      (.layered (.objects #[sibTgtId]) (.copy copy1Def) (.whileInZone sibE1 .command)) (cause := some testCause)).createEffect
      (.layered (.objects #[sibTgtId]) (.copy copy2Def) (.whileInZone sibE2 .command)) (cause := some testCause))
  let sibPreLogs := gSib1.log.size
  let gSibAfter := gSib1.beginTurn
  let sibCopyEndLogs :=
    (gSibAfter.log.extract sibPreLogs gSibAfter.log.size).filter
      (fun s => mentions s "is no longer a copy of")

  -- 2a(v). Scoped `.copy` logs (`Core.restoreCopiesWhere` & `Turns.expireEffectsByDuration`):
  --        A scoped `.layered (.creaturesControlledBy p0) (.copy copy1Def) .untilEndOfTurn` expiring logs restoration!
  let gScoped0 := addPermanent (addPermanent g4 bear p0 p0) hero p0 p0
  let gScoped1 :=
    gScoped0.createEffect
      (.layered (.creaturesControlledBy p0) (.copy copy1Def) .untilEndOfTurn)
      (cause := some testCause)
  let scopedPreLogs := gScoped1.log.size
  let gScopedAfter := gScoped1.expireEffectsByDuration (fun _ d => d == .untilEndOfTurn) (some testCause)
  let scopedCopyEndLogs :=
    (gScopedAfter.log.extract scopedPreLogs gScopedAfter.log.size).filter
      (fun s => mentions s "is no longer a copy of")

  -- 2b(i). Non-bf/non-command `cmdInitSeeds` in `coDepartingIds`:
  --        An exiled card with a `.whileInZone exiledId .exile` command emblem includes the emblem!
  let gNonBfSeed0 := insertObject (insertObject g4 exCardDef p0 .exile) embDef p0 .command (some p0)
  let nbExId := (gNonBfSeed0.objects.filter (·.zone == .exile)).back!.id
  let nbEmbId := (gNonBfSeed0.objects.filter (·.zone == .command)).back!.id
  let gNonBfSeed1 :=
    gNonBfSeed0.createEffect (.gameRule (.commandEmblem nbEmbId) (.whileInZone nbExId .exile))
      (cause := some testCause)
  let nbCoDeps := gNonBfSeed1.coDepartingIds #[nbExId]

  -- 2b(ii). `Phasing.phaseInControlled` CR 702.26h orphaned indirect attachment timing:
  --         Host (controlled by p1) + Equipment (controlled by p0) phase out together;
  --         p1 concedes (host leaves game, orphaning the phased-out Equipment — sinceIdx advances
  --         to the host-departure event so it phases in on p0's untap)!
  let bladeDef : CardDef := { name := "P53i2 Blade", types := #[.artifact], subtypes := #["Equipment"] }
  let gOrph0 := addPermanent (addPermanent g4 bear p1 p1) bladeDef p0 p0
  let orphHostId := (gOrph0.permanentsOf p1)[0]!.id
  let orphBladeId := (gOrph0.permanentsOf p0)[0]!.id
  let gOrph1 := gOrph0.attachSourceTo (gOrph0.object! orphBladeId) (gOrph0.object! orphHostId) (cause := some testCause)
  let gOrph2 := gOrph1.phaseOut (gOrph1.object! orphHostId) (cause := some testCause)
  let gOrph3 := mustApply gOrph2 p1 .concede
  let gOrph4 := gOrph3.phaseInControlled p0

  let item2Ok :=
    mustHold53i2 "2a_dedupPlayFromExileLog" (pfeLogCount == 1 && deferredPr.containsDeferredPlayFromExile pfeCardId) &&
    mustHold53i2 "2a_outerLeaveGamePlayFromExileSingleLog" (lpLogCount == 1) &&
    mustHold53i2 "2a_whileInZoneEmblemControlRevertsAndCopyCollapses"
      ((gWizAfter.findObject? wizEmbId).isNone &&
       gWizAfter.controllerOf (gWizAfter.object! wizCtrlId) == some p1 &&
       wizCopyEndLogs.size == 1 &&
       mentions wizCopyEndLogs[0]! copy2Def.name) &&
    mustHold53i2 "2a_siblingEmblemsCollapseCopyLogs"
      (sibCopyEndLogs.size == 1 && mentions sibCopyEndLogs[0]! copy2Def.name) &&
    mustHold53i2 "2a_scopedCopyExpireLogsBothCreatures"
      (scopedCopyEndLogs.size == 2) &&
    mustHold53i2 "2b_nonBfCmdInitSeedsInCoDeparting"
      (nbCoDeps.contains nbEmbId) &&
    mustHold53i2 "2b_orphanedIndirectAttachmentPhasesIn"
      ((gOrph4.findObject? orphBladeId).any (!·.status.phasedOut))

  mustHold53i2 "2.all" item2Ok &&
  mustHold53i2 "2.replay"
    (replayOk53i2 #[gPfe4, gLeavePfeAfter, gWizAfter, gSibAfter, gScopedAfter, gNonBfSeed1, gOrph4])

end Phase53Item2EventAlignment

section Phase53Item3EventAlignment

private def mustHold53i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase53Item3EventAlignment failed: {label}"

private def replayOk53i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g2 := afterDraw

  -- 3a(i). `EvalExpr.lkiCombatWindow` blocked phased-out attacker (NOT misclassified as unblocked!):
  let gBlkPh0 := addPermanent (addPermanent g2 bear p0 p0) bear p1 p1
  let atkId := (gBlkPh0.permanentsOf p0)[0]!.id
  let blkId := (gBlkPh0.permanentsOf p1)[0]!.id
  let gBlkPh1 := mustApply (gBlkPh0.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
  let gBlkPh2 := mustApply gBlkPh1.advanceStep p1 (.declareBlockers #[(blkId, atkId)])
  let gBlkPhOut := gBlkPh2.phaseOut (gBlkPh2.object! atkId) (cause := some testCause)
  let atkEnv : EvalEnv := { controller := p0, sourceId := some atkId }
  let evalBlockedOk :=
    EvalExpr.evalCondition gBlkPhOut atkEnv (.exists (.filter .this (.combatRole .blocked))) &&
    !EvalExpr.evalCondition gBlkPhOut atkEnv (.exists (.filter .this (.combatRole .unblocked)))
  let coreBlockedOk :=
    gBlkPhOut.evalTriggerCond p0 (some (gBlkPhOut.object! atkId)) none
      (.exists (.filter .this (.combatRole .blocked))) &&
    !gBlkPhOut.evalTriggerCond p0 (some (gBlkPhOut.object! atkId)) none
      (.exists (.filter .this (.combatRole .unblocked)))

  -- 3a(ii). `Phasing.phaseOut` pre-host indirect attachment snapshots (CR 702.26g):
  --         Host has a static ability giving attached Equipment `Keyword.indestructible`,
  --         and phases out: indirect Equipment snapshot MUST retain host's static ability!
  let eqHostDef : CardDef := {
    bear with
    name := "P53i3 EqHost"
    staticAbilities := #[
      .continuous none { zones := .battlefield, pred := .attachedTo .this }
        (.grantKeywords #[Keyword.indestructible])
    ]
  }
  let plainEquipDef : CardDef := {
    name := "P53i3 PlainSword", types := #[.artifact], subtypes := #["Equipment"]
    activatedAbilities := #[Catalog.equipAbility (ManaCost.ofGeneric 1)]
  }
  let gInd0 := addPermanent (addPermanent g2 eqHostDef p0 p0) plainEquipDef p0 p0
  let indHostId := (gInd0.permanentsOf p0).find? (·.name == eqHostDef.name) |>.get!.id
  let indEqId := (gInd0.permanentsOf p0).find? (·.name == plainEquipDef.name) |>.get!.id
  let gInd1 := gInd0.attachSourceTo (gInd0.object! indEqId) (gInd0.object! indHostId) (cause := some testCause)
  let gIndPhOut := gInd1.phaseOut (gInd1.object! indHostId) (cause := some testCause)
  let indEqSnap? := GameEvent.lastKnownBefore? gIndPhOut.events indEqId
  let indEqLki := indEqSnap?.map Game.lkiEventObjectAsGameObject
  -- Also test `Core.evalTriggerCond` co-phased `.attachedTo` + `.inZones .battlefield`,
  -- pre-departure `wt.source`, and Equip `.hasKeyword` on `isLkiSnapshot`:
  let coreCoPhasedEqOk :=
    gIndPhOut.evalTriggerCond p0 (some (gIndPhOut.object! indHostId)) none
      (.exists (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .attachedTo .this])))
  let coreEquipKwLkiOk :=
    indEqLki.any fun lki =>
      gIndPhOut.evalTriggerCond p0 (some lki) none (.exists (.filter .this (.hasKeyword (.param .equip))))
  -- Pre-departure `wt.source` (non-phased-out object that already moved to graveyard):
  let (gDepSrc, _) := gInd1.move indEqId (.graveyard p0) none (cause := some testCause)
  let depEqObj := gInd1.object! indEqId
  let corePreDepFallbackOk :=
    gDepSrc.evalTriggerCond p0 (some depEqObj) none
      (.exists (.filter .this (.hasKeyword .indestructible)))

  -- 3a(iii). `Core.isAncestrySourceId` / `ancestryManaSpentOn` on phased-out Humility-stripped *Path of Ancestry*:
  let poaDef : CardDef := {
    name := "P53i3 PoA", types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .green))]
    triggeredAbilities := #[TriggeredAbility.onManaSpentCastCommanderTypeScry]
  }
  let gPoa0 := addPermanent g2 poaDef p0 p0
  let poaId := (gPoa0.permanentsOf p0)[0]!.id
  let gPoaStripped :=
    gPoa0.createEffect (.layered (.objects #[poaId]) (.abilities {} .all) .indefinite) (cause := some testCause)
  let gPoaPhOut := gPoaStripped.phaseOut (gPoaStripped.object! poaId) (cause := some testCause)

  -- 3a(iv). `Tokens.tokenBatchProbe` uses `noSourceSentinelId` (never `g.nextObjectId`):
  let probeTok := g2.tokenBatchProbe p0 bear
  -- 3a(v). `Damage.replaceDamage` LKI snapshot view:
  let redLkiSnap : EventObject := {
    id := some ⟨9991⟩, name := "P53i3 RedLki", owner := p0, controller := some p0,
    zone := .battlefield, types := #[.creature], colors := ColorSet.ofList [.red],
    power := some 3, toughness := some 3
  }
  let redLkiObj := Game.lkiEventObjectAsGameObject redLkiSnap

  -- 3b(i). `{X}{X}` & synthetic stack-LKI mana value:
  let xxSpellDef : CardDef := {
    name := "P53i3 XXFireball"
    manaCost := ⟨#[.x, .x, .colored .red]⟩
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let noXSpellDef : CardDef := {
    name := "P53i3 NoXSpell"
    manaCost := ⟨#[.generic 1, .colored .red]⟩
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gXx0 :=
    (insertObject (emptyHand g2 p0) xxSpellDef p0 (.hand p0)).addMana p0 (.colored .red) 1
      |>.addMana p0 .colorless 6
  let gXxCast :=
    mustApply (mustApply (mustApply gXx0 p0 (.cast (gXx0.player p0).hand.back!)) p0 (.chooseX 3)) p0 .pay
  let xxId := gXxCast.stack.back!.objectId
  let gXx1 := insertObject gXxCast noXSpellDef p0 .stack
  let noXId := (gXx1.objects.filter (·.name == noXSpellDef.name))[0]!.id
  let gXx1 := gXx1.record (GameEvent.rules gXx1.turnNumber
    (.cast (.announced noXId #[] (some 3) #[])) testCause)
  let xxObj := gXx1.object! xxId
  let noXObj := gXx1.object! noXId
  let staticXxMvOk :=
    gXx1.evalTriggerCond p0 (some xxObj) none (.exists (.filter .this (.stat .manaValue .eq (.const 7)))) &&
    gXx1.evalTriggerCond p0 (some noXObj) none (.exists (.filter .this (.stat .manaValue .eq (.const 2))))
  -- Synthetic stack LKI with `eo.manaValue := 5`, `eo.chosenX := none`, reusing `xxId` (which has `chosenXOf? == some 3`):
  let synthStackLki := Game.lkiEventObjectAsGameObject {
    id := some xxId, name := xxSpellDef.name, owner := p0, controller := some p0,
    zone := .stack, types := #[.sorcery], manaValue := 5, chosenX := none
  }

  -- 3b(ii). Non-re-expanded `changeling` LKI in `Core.evalLayer4Full` & `EvalExpr.viewHasSubtype`:
  let changelingNonCreatureLki : EventObject := {
    id := some ⟨9992⟩, name := "P53i3 NonCreatureChangeling", owner := p0, controller := some p0,
    zone := .battlefield, types := #[.artifact], subtypes := #[.food],
    keywords := #[Keyword.changeling]
  }
  let changelingLkiObj := Game.lkiEventObjectAsGameObject changelingNonCreatureLki
  let evalL4NoExpand := !(g2.hasSubtype changelingLkiObj .elf) && g2.hasSubtype changelingLkiObj .food
  let viewNoExpand :=
    !EvalExpr.evalObjectPred g2 { controller := p0 } (.lki changelingNonCreatureLki) (.hasSubtype (.literal .elf)) &&
    EvalExpr.evalObjectPred g2 { controller := p0 } (.lki changelingNonCreatureLki) (.hasSubtype (.literal .food))

  -- 3b(iii). `lkiEventObjectAsGameObject` DFC no double-swap & `retainsPrintedAbilities == some false`:
  let backFaceDef : CardDef := {
    creature "P53i3 BackFace" ManaCost.empty #["Wolf"] 4 4 with
    activatedAbilities := #[Catalog.equipAbility (ManaCost.ofGeneric 1)]
  }
  let frontDfcDef : CardDef := {
    creature "P53i3 FrontFace" (ManaCost.ofGeneric 2) #["Human"] 2 2 with
    otherFace := some backFaceDef
  }
  let swappedBack : CardDef := { backFaceDef with otherFace := some frontDfcDef }
  let dfcSnap : EventObject := {
    id := some ⟨9993⟩, name := backFaceDef.name, owner := p0, controller := some p0,
    zone := .battlefield, types := #[.creature], subtypes := #[.wolf],
    power := some 4, toughness := some 4, transformed := true,
    printed := some swappedBack,
    retainsPrintedAbilities := some false
  }
  let dfcLkiObj := Game.lkiEventObjectAsGameObject dfcSnap

  -- 3b(iv). Public Layer-6/7 `isLkiSnapshot` guards (`evalLayer6`, `pumpOf`, `setBasePT`, `hasCantBeBlocked`):
  let pumpBearSnap : EventObject := {
    id := some atkId, name := bear.name, owner := p0, controller := some p0,
    zone := .battlefield, types := #[.creature], subtypes := #[.bear],
    power := some 2, toughness := some 2
  }
  let pumpBearLki := Game.lkiEventObjectAsGameObject pumpBearSnap
  let gWithLiveBuffs :=
    ((g2.createEffect (.layered (.objects #[atkId]) (.ptModify 5 5) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.layered (.objects #[atkId]) (.ptSet 9 9) .untilEndOfTurn) (cause := some testCause)).createEffect
      (.cantBeBlockedUntilEot atkId) (cause := some testCause)

  let item3aOk :=
    mustHold53i3 "3a_lkiCombatWindowBlockedPhasedOut" (evalBlockedOk && coreBlockedOk) &&
    mustHold53i3 "3a_phaseOutPreHostIndirectAttachmentSnap"
      (indEqSnap?.any (fun s => s.keywords.contains Keyword.indestructible) &&
       coreCoPhasedEqOk && coreEquipKwLkiOk && corePreDepFallbackOk) &&
    mustHold53i3 "3a_ancestrySourceIdLkiNotPrinted" (!gPoaPhOut.isAncestrySourceId poaId) &&
    mustHold53i3 "3a_tokenBatchProbeSentinel" (probeTok.id == noSourceSentinelId) &&
    mustHold53i3 "3a_lkiSnapshotFlagSet" redLkiObj.isLkiSnapshot

  let item3bOk :=
    mustHold53i3 "3b_xxAndSyntheticStackManaValue"
      (gXx1.objectManaValue xxObj == 7 &&
       gXx1.objectManaValue noXObj == 2 &&
       staticXxMvOk &&
       gXx1.objectManaValue synthStackLki == 5) &&
    mustHold53i3 "3b_changelingLkiNoReExpansion" (evalL4NoExpand && viewNoExpand) &&
    mustHold53i3 "3b_lkiDfcNoDoubleSwapAndRetainsFalse"
      (dfcLkiObj.printed.name == backFaceDef.name &&
       dfcLkiObj.printed.activatedAbilities.isEmpty) &&
    mustHold53i3 "3b_publicLayer67LkiGuards"
      (gWithLiveBuffs.pumpOf pumpBearLki == (0, 0) &&
       gWithLiveBuffs.setBasePT pumpBearLki == none &&
       !gWithLiveBuffs.hasCantBeBlocked pumpBearLki &&
       (gWithLiveBuffs.evalLayer6 pumpBearLki).kw.isEmpty)

  mustHold53i3 "3a" item3aOk &&
  mustHold53i3 "3b" item3bOk &&
  mustHold53i3 "3.replay"
    (replayOk53i3 #[gBlkPhOut, gIndPhOut, gDepSrc, gPoaPhOut, gXx1, gWithLiveBuffs])

end Phase53Item3EventAlignment

section Phase53Item4EventAlignment

private def mustHold53i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase53Item4EventAlignment failed: {label}"

private def replayOk53i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := emptyHand afterDraw p0

  -- 4a(v). `LandsAndMana.hasUsableNonPlainManaAbility` `.tapObjects` & Crew coupling:
  -- (a) Sole non-creature enchantment producing `{C}` AND required for `.custom (.tapObjects ..)`
  --     on a non-plain mana ability costing `{1}` + tap an untapped enchantment -> FALSE with 1, TRUE with 2!
  let manaEnchDef : CardDef := {
    name := "P53i4 ManaEnch", types := #[.enchantment]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne .colorless)]
  }
  let tapEnchManaArtDef : CardDef := {
    name := "P53i4 TapEnchFilter", types := #[.artifact]
    activatedAbilities := #[{
      cost := {
        items := #[
          .mana (ManaCost.ofGeneric 1),
          .tapObjects (.exact 1) (.all #[.hasType .enchantment, .tapped false, .controlledBy .you])
        ]
      }
      effect := { body := .player (.addMana .you { spec := .fixedOne (.colored .red) }) }
    }]
  }
  let gTapObj1 := addPermanent (addPermanent gBase tapEnchManaArtDef p0 p0) manaEnchDef p0 p0
  let gTapObj2 := addPermanent gTapObj1 manaEnchDef p0 p0

  -- (b) Crew-coupled non-plain mana ability (`crewPower? := some 2` + `{1}` mana cost):
  --     Sole 2/2 mana dork CANNOT pay both `{1}` and Crew 2 -> FALSE with 1 dork, TRUE with 1 dork + Forest!
  let manaDorkDef : CardDef := {
    creature "P53i4 Dork" ManaCost.empty #["Elf"] 2 2 with
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .green))]
  }
  let crewManaVehDef : CardDef := {
    name := "P53i4 CrewFilter", types := #[.artifact], subtypes := #["Vehicle"]
    activatedAbilities := #[{
      cost := {
        items := #[
          .mana (ManaCost.ofGeneric 1),
          .tapObjects (.totalPowerAtLeast (.const 2))
            (.all #[.hasType .creature, .tapped false, .controlledBy .you])
        ]
      }
      effect := { body := .player (.addMana .you { spec := .fixedOne (.colored .red) }) }
    }]
  }
  let gCrew1 := addPermanent (addPermanent gBase crewManaVehDef p0 p0) manaDorkDef p0 p0
  let gCrew2 := addPermanent gCrew1 forest p0 p0

  -- 4b(i). Sneak-to-hand discard parity across `PriorityActions`, `Casting`, `LandsAndMana`, `Agent`:
  let sneakChoiceDiscDef : CardDef := {
    bear with
    name := "P53i4 SneakChoiceDisc"
    manaCost := ManaCost.ofGeneric 3
    spellAbility := some {
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.discardCardOrPayGeneric 2)]
    }
    keywords := #[.sneak CostSpec.empty]
  }
  let gSnkOwn :=
    let g := insertObject (addPermanent gBase bear p0 p0) sneakChoiceDiscDef p0 (.hand p0)
    let atkId := (g.permanentsOf p0)[0]!.id
    let g := mustApply (g.beginStep .declareAttackers) p0 (.declareAttackers #[atkId] none #[] #[])
    mustApply g.advanceStep p1 (.declareBlockers #[])
  let snkOwnAtkId := (gSnkOwn.permanentsOf p0)[0]!.id
  let snkChoiceCardId := (gSnkOwn.player p0).hand[0]!
  let gSnkChoicePrompt := mustApply gSnkOwn p0 (.castWithSneak snkChoiceCardId snkOwnAtkId)
  let snkChoiceProp := gSnkChoicePrompt.proposedSpell.get!
  let gSnkChoiceMana := mustApply gSnkChoicePrompt p0 (.chooseAdditionalCost false)
  let snkTapPreserves := gSnkChoiceMana.tapPreservesPostManaCosts p0 gSnkChoiceMana.proposedSpell.get! #[]
  let gSnkChoiceDisc := mustApply gSnkChoiceMana p0 .pay

  -- 4b(ii). `timingAllowsCast (card? := some o)` with Layer-3 text-changed self-flash:
  --         Card has "You may cast this spell as though it had flash if you control a Swamp";
  --         Layer-3 text change swaps Swamp -> Forest; p0 controls a Forest on opponent's turn -> canCastFrontFace == true!
  let selfFlashSwampDef : CardDef := {
    creature "P53i4 SwampFlash" ManaCost.zero #["Beast"] 2 2 with
    staticAbilities := #[
      .ruleModifying (some (.exists (.inZones { zones := #[.battlefield], owner := .ofPlayer .you } (.hasSubtype (.literal .swamp)))))
        (.play (.castAsThoughFlash .you .anyObject true none))
    ]
  }
  let gFlash0 :=
    ((insertObject (addPermanent gBase forest p0 p0) selfFlashSwampDef p0 (.hand p0)).record
      (GameEvent.turnBegan 2 p1)).change (.priority p0)
  let flashCardId := (gFlash0.player p0).hand[0]!
  let canFlashBefore := gFlash0.canCastFrontFace p0 (gFlash0.object! flashCardId)
  let gFlashTextChanged :=
    gFlash0.createEffect
      (.layered (.objects #[flashCardId]) (.text (.replaceCreatureType .swamp .forest)) .untilEndOfTurn)
      (cause := some testCause)
  let canFlashAfter := gFlashTextChanged.canCastFrontFace p0 (gFlashTextChanged.object! flashCardId)

  -- 4b(iii). `.behold` self-exclusion:
  let beholdDragonSpellDef : CardDef := {
    creature "P53i4 BeholdDragon" ManaCost.zero #["Dragon"] 3 3 with
    spellAbility := some {
      additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.beholdOrPayGeneric .dragon 2)]
    }
  }
  let gBehold1 := insertObject gBase beholdDragonSpellDef p0 (.hand p0)
  let bhId1 := (gBehold1.player p0).hand[0]!
  let gBehold2 := insertObject gBehold1 beholdDragonSpellDef p0 (.hand p0)
  let bhId2 := (gBehold2.player p0).hand[0]!

  -- 4b(iv). `Agent` `.tapObjects` exclusion in `Agent.choose`:
  --         Sole mana enchantment cannot pay BOTH `{1}` and `.tapObjects 1 (enchantment)` -> does NOT activate!
  --         With two mana enchantments -> DOES activate!
  let tapEnchActDef : CardDef := {
    name := "P53i4 TapEnchAct", types := #[.artifact]
    activatedAbilities := #[{
      cost := {
        items := #[
          .mana (ManaCost.ofGeneric 1),
          .tapObjects (.exact 1) (.all #[.hasType .enchantment, .tapped false, .controlledBy .you])
        ]
      }
      effect := Effect.gainLife 2
    }]
  }
  let gAgTap1 := addPermanent (addPermanent gBase tapEnchActDef p0 p0) manaEnchDef p0 p0
  let agArt1Id := (gAgTap1.permanentsOf p0).find? (·.name == tapEnchActDef.name) |>.get!.id
  let gAgTap2 := addPermanent gAgTap1 manaEnchDef p0 p0
  let agArt2Id := (gAgTap2.permanentsOf p0).find? (·.name == tapEnchActDef.name) |>.get!.id
  let isActivateArt (act : Option Action) (artId : ObjectId) : Bool :=
    match act with
    | some (.activate oid _) => oid == artId
    | _ => false

  let item4Ok :=
    mustHold53i4 "4a_nonPlainTapObjectsCoupling"
      (!gTapObj1.hasUsableNonPlainManaAbility p0 && gTapObj2.hasUsableNonPlainManaAbility p0) &&
    mustHold53i4 "4a_nonPlainCrewCoupling"
      (!gCrew1.hasUsableNonPlainManaAbility p0 && gCrew2.hasUsableNonPlainManaAbility p0) &&
    mustHold53i4 "4b_sneakToHandDiscardParity"
      (!gSnkChoicePrompt.additionalCostChoosesGeneric p0 snkChoiceProp &&
       snkTapPreserves &&
       gSnkChoiceDisc.pending == .discardForAdditionalCost p0) &&
    mustHold53i4 "4b_timingAllowsCastLayer3SelfFlash"
      (!canFlashBefore && canFlashAfter) &&
    mustHold53i4 "4b_beholdSelfExclusion"
      (!gBehold1.canPayAnnouncedAdditional p0 (gBehold1.object! bhId1) ManaPool.empty &&
       !gBehold1.canPayAnnouncedAdditionalFromSources p0 (gBehold1.object! bhId1) &&
       gBehold2.canPayAnnouncedAdditional p0 (gBehold2.object! bhId2) ManaPool.empty &&
       gBehold2.canPayAnnouncedAdditionalFromSources p0 (gBehold2.object! bhId2)) &&
    mustHold53i4 "4b_agentTapObjectsExclusion"
      (!isActivateArt (Agent.choose gAgTap1 p0) agArt1Id &&
       isActivateArt (Agent.choose gAgTap2 p0) agArt2Id)

  mustHold53i4 "4.all" item4Ok &&
  mustHold53i4 "4.replay"
    (replayOk53i4 #[
      gTapObj1, gTapObj2, gCrew1, gCrew2, gSnkChoicePrompt, gSnkChoiceMana, gSnkChoiceDisc,
      gFlashTextChanged, gBehold1, gBehold2, gAgTap1, gAgTap2 ])

end Phase53Item4EventAlignment

end Mtg.Engine.EventTests
