import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.Catalog.RealityFractureCommander

/-!
# Unified `Instruction` AST, `stepEnv`, & `Interpreter` Runtime Tests

Comprehensive gameplay `#guard` regression suite for the unified `Instruction`
AST and resumable interpreter (see `docs/card-and-ability-model.md` and
`docs/game-evaluation.md`, anchored to the 6 November 2026 CR):
1. `ContinuationFrame.stepEnv` across `Instruction.bind`, including CR 614.6
   prevented/replaced/doubled events and CR 616.1 `Pending.chooseReplacement`
   pause & resume.
2. Dynamic excess damage via `Instruction.bind` (`DamageFlags.trackExcess` +
   `ValueExpr.stepMetric .excessDamage`), including pre-marked damage lethal
   thresholds (CR 120.4a).
3. Compositional Recruit (`Instruction.recruit`: draw → bind discard → conditional
   1/1 Human Soldier token on nonland discard).
4. CR 701.44a/c & CR 400.3 Explore via unified `Interpreter` (land to hand,
   nonland +1/+1 counter + `.exploreMayGraveyard` accept/decline, departed
   explorer LKI without counter, and empty library).
5. Empower Jace folded into `spellEffect.body`: token creation, loyalty
   addition, modal mode-scoped empowering, and novel parsed spell execution.
6. Unified `Instruction.chooseModes` (`ModalSpec`) across spells (`Choose one or
   both`, teamwork `altCountIf?`, subtype `altCountIf?`), modal activated
   abilities (`ActivatedAbility.mkModal`), and modal triggered abilities
   (`TriggeredAbility.mkModal`), plus CR 613.1c Layer-3 `HasTextChange`
   propagation into `Instruction` and `GrantedAbility`.
7. Unified Saga chapters, FRA/FRC effects, and `GrantedAbility` tokens
   resolved through `Game/Interpreter.lean`.
8. Novel Stage-4 `Parser.parseInstructionEffect` spells parsed and executed
   end-to-end through `Interpreter` with full event-log replay fidelity.
9. `Instruction.forEach` pause/resume with non-zero `VarId` across players and
   objects, plus `Effect.worldsWithinWorlds` APNAP interactive choice execution.
10. Phase 9 unified trigger families (watch, step, casting, resource,
    enterOrAttack, attack, death, modal, reflexive), `CostSpec.bindVar?`
    cost-to-`stepEnv` binding, and `EvalEnv` copy-token tie prompting
    (`ResolutionChoice.chooseTokenCopyObject`).
-/

namespace Mtg.Engine.Tests.InterpreterSuite

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

private def p0 : PlayerId := ⟨0⟩
private def p1 : PlayerId := ⟨1⟩

private def testCause : EventCause := .oneShotEffect none none

private def mustParse (raw : String) : CardDef :=
  match parseOracleCard raw with
  | .ok c => c
  | .error e => panic! s!"parseOracleCard failed: {e}"

private def mustApply (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! s!"apply failed ({reprStr a}): {e}"

private def replayOk (gs : Array Game) : Bool :=
  gs.all fun g => Game.replayEvents g.events == g

private def resolveReplacements (g : Game) : Game := Id.run do
  let mut cur := g
  for _ in [0:16] do
    match cur.pending with
    | .chooseReplacement q cs =>
      match cs[0]? with
      | some cid => cur := mustApply cur q (.chooseReplacement cid)
      | none => break
    | _ => break
  return cur

private def emptyHand (g : Game) (p : PlayerId) : Game :=
  (g.player p).hand.foldl (fun acc id => (acc.move id (.graveyard p) none (cause := some testCause)).1) g

private def emptyLib (g : Game) (p : PlayerId) : Game :=
  (g.player p).library.foldl (fun acc id => (acc.move id (.graveyard p) none (cause := some testCause)).1) g

private def passBoth (g : Game) : Game :=
  let g := if g.hasPriority p0 then mustApply g p0 .pass else g
  if g.hasPriority p1 then mustApply g p1 .pass else g

private def bearDef : CardDef :=
  { name := "Phase8 Bear", manaCost := ManaCost.ofGeneric 2
    types := #[.creature], subtypes := #["Bear"], power := some (.fixed 2), toughness := some (.fixed 2) }

private def elfDef : CardDef :=
  { name := "Phase8 Elf", manaCost := ManaCost.ofGeneric 1
    types := #[.creature], subtypes := #["Elf"], power := some (.fixed 1), toughness := some (.fixed 1) }

private def relicDef : CardDef :=
  { name := "Phase8 Relic", manaCost := ManaCost.ofGeneric 1, types := #[.artifact] }

private def basicForest : CardDef :=
  { name := "Forest", types := #[.land], supertypes := #[.basic], subtypes := #["Forest"] }

private def basicIsland : CardDef :=
  { name := "Island", types := #[.land], supertypes := #[.basic], subtypes := #["Island"] }

/-! ## 1. `stepEnv` across `.bind`, CR 614.6 post-replacement outcomes, & CR 616.1 pause/resume -/

-- 1a. Exiling creatures bound to `VarId ⟨0⟩` feeds actual exiled object count into token creation;
--     and creating Food inside `.bind` under competing non-commuting CR 616.1 replacements
--     (`foodAlsoCreatesTreasure` + `artifactTokensBecomeDragons`) genuinely pauses on
--     `Pending.chooseReplacement` and preserves `stepEnv` across resume so step 2 draws cards
--     equal to the actual post-replacement `createdCount` (CR 614.6: 2 cards vs 1 card!).
#guard
  let exileAndMake : Effect := {
    body := .bind ⟨0⟩
      (.moveZone (.inZones .battlefield (.hasType .creature)) .exile .exile {})
      (.create (.tokens .you (.stepMetric .movedCount ⟨0⟩) .humanSoldier {}))
  }
  let g0 := addPermanent (addPermanent (emptyHand afterDraw p0) bearDef p0 p0) bearDef p1 p1
  let gNorm := g0.applyEffect p0 exileAndMake #[]
  let normSoldiers := (gNorm.permanentsOf p0).filter (·.name == "Human Soldier")
  let normOk :=
    gNorm.battlefield.all (·.name != bearDef.name) &&
    normSoldiers.size == 2 &&
    replayOk #[gNorm]

  let createFoodThenDraw : Effect := {
    body := .bind ⟨0⟩
      (.create (.tokens .you (.const 1) .food {}))
      (.player (.drawCards .you (.stepMetric .createdCount ⟨0⟩)))
  }
  let extraTreasure : ReplacementSpec := {
    id := { kind := .foodAlsoCreatesTreasure, object := some ⟨7001⟩ }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .createExtraTokenWithFood p0 Game.treasureToken
  }
  let toDragon : ReplacementSpec := {
    id := { kind := .artifactTokensBecomeDragons, object := some ⟨7002⟩ }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .artifactTokensBecome p0 Game.dragonToken
  }
  let gRep0 :=
    ((emptyHand afterDraw p0).createEffect (.replacement extraTreasure) (cause := some testCause)).createEffect
      (.replacement toDragon) (cause := some testCause)
  let gRepPaused := gRep0.applyEffect p0 createFoodThenDraw #[]
  let repPausedOk := match gRepPaused.pending with | .chooseReplacement .. => true | _ => false
  -- Path A: choose `foodAlsoCreatesTreasure` first → Food + Treasure → both become Dragons (2 tokens → draw 2)
  let gPathA := resolveReplacements (mustApply gRepPaused p0 (.chooseReplacement extraTreasure.id))
  -- Path B: choose `artifactTokensBecomeDragons` first → Food becomes Dragon (no longer Food → 1 token → draw 1)
  let gPathB := resolveReplacements (mustApply gRepPaused p0 (.chooseReplacement toDragon.id))
  let repOk :=
    repPausedOk &&
    gPathA.pending == .none && (gPathA.player p0).hand.size == 2 &&
    gPathB.pending == .none && (gPathB.player p0).hand.size == 1 &&
    replayOk #[gRepPaused, gPathA, gPathB]

  normOk && repOk

-- 1b. CR 614.6 prevented/replaced counter placement paused across CR 616.1:
--     Two competing counter replacements (add +1 vs multiply ×2) pause during step 1 of `.bind`;
--     choosing a replacement finishes step 1 and resumes step 2 cleanly with `stepEnv` intact.
#guard
  let g0 := addPermanent (emptyHand afterDraw p0) bearDef p0 p0
  let bid := (g0.permanentsOf p0)[0]!.id
  let cntAdd : ReplacementSpec := {
    id := { kind := .extraCounterOnPermanents, object := some bid, counterKind := some .plusOnePlusOne }
    source := some bid, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .plusOnePlusOne) 1 1
  }
  let cntMul : ReplacementSpec := {
    id := { kind := .multiplyCountersPut, object := none, counterKind := some .plusOnePlusOne }
    source := none, controller := some p0, affectedPlayer := p0
    kind := .modifyCountersPut none (some .plusOnePlusOne) 0 2
  }
  let gRep :=
    (g0.createEffect (.replacement cntAdd) (cause := some testCause)).createEffect
      (.replacement cntMul) (cause := some testCause)
  let eff : Effect := {
    targets := .creature
    body := .bind ⟨0⟩
      (Instruction.putPlusOne (.target 0) 1)
      (Instruction.gainLifeFixed 3)
  }
  let gPaused := gRep.applyEffect p0 eff #[.permanent bid]
  let pausedOk := match gPaused.pending with | .chooseReplacement .. => true | _ => false
  let gDone := resolveReplacements gPaused
  pausedOk &&
    gDone.pending == .none &&
    (gDone.object! bid).status.plusOnePlusOne >= 3 &&
    (gDone.player p0).life == 23 &&
    replayOk #[gPaused, gDone]

/-! ## 2. Dynamic excess damage via `.bind` (`trackExcess` + `.stepMetric .excessDamage`) -/

#guard
  let burnExcess : Effect := {
    targets := .creature
    body := .bind ⟨0⟩
      (.damage (.deal .this (.targetSlot 0) (.const 5) { trackExcess := true }))
      (Instruction.gainLife (.stepMetric .excessDamage ⟨0⟩))
  }
  -- Undamaged 2/2: lethal threshold = 2, 5 dealt → 3 excess life gained.
  let g0 := addPermanent (emptyHand afterDraw p0) bearDef p1 p1
  let bid := (g0.permanentsOf p1)[0]!.id
  let g1 := g0.applyEffect p0 burnExcess #[.permanent bid]
  -- Pre-damaged 2/2 (1 damage already marked): lethal threshold = 1, 5 dealt → 4 excess life gained.
  let gDamaged := g0.dealDamageFrom "Pre" (g0.object! bid) 1 (cause := some testCause)
  let g2 := gDamaged.applyEffect p0 burnExcess #[.permanent bid]
  (g1.player p0).life == 23 &&
    (g2.player p0).life == 24 &&
    replayOk #[g1, g2]

/-! ## 3. Compositional Recruit (`Instruction.recruit`) -/

#guard
  -- Nonland discard creates a 1/1 white Human Soldier token; land discard creates 0 tokens.
  let gBase := emptyLib (emptyHand afterDraw p0) p0
  let gNonland0 := insertObject (insertObject gBase bearDef p0 (.library p0)) bearDef p0 (.hand p0)
  let gNonlandAsk := gNonland0.applyEffect p0 Effect.recruit #[]
  let nonlandCard := (gNonlandAsk.player p0).hand[0]!
  let gNonlandDone := mustApply gNonlandAsk p0 (.discard nonlandCard)
  let nonlandSoldiers := (gNonlandDone.permanentsOf p0).filter (·.name == "Human Soldier")

  let gLand0 := insertObject (insertObject gBase basicForest p0 (.library p0)) basicForest p0 (.hand p0)
  let gLandAsk := gLand0.applyEffect p0 Effect.recruit #[]
  let landCard := (gLandAsk.player p0).hand[0]!
  let gLandDone := mustApply gLandAsk p0 (.discard landCard)
  let landSoldiers := (gLandDone.permanentsOf p0).filter (·.name == "Human Soldier")

  nonlandSoldiers.size == 1 &&
    landSoldiers.isEmpty &&
    replayOk #[gNonlandDone, gLandDone]

/-! ## 4. CR 701.44a/c & CR 400.3 Explore via unified `Interpreter` -/

#guard
  let exploreEff : Effect := { body := .player (.explore .this) }
  let gBase := addPermanent (emptyLib (emptyHand afterDraw p0) p0) bearDef p0 p0
  let bid := (gBase.permanentsOf p0)[0]!.id

  -- (a) Top card is a land → moved to hand, no +1/+1 counter.
  let gLand0 := insertObject gBase basicForest p0 (.library p0)
  let gLand1 := gLand0.applyAbilityEffect p0 exploreEff #[] (some bid)
  let landOk :=
    (gLand1.player p0).hand.any (fun id => (gLand1.object! id).name == "Forest") &&
    (gLand1.object! bid).status.plusOnePlusOne == 0 &&
    gLand1.pending == .none

  -- (b) Top card is a nonland → +1/+1 counter + `.exploreMayGraveyard` (accept mills, decline keeps on top).
  let gNonland0 := insertObject gBase bearDef p0 (.library p0)
  let gNonlandAsk := gNonland0.applyAbilityEffect p0 exploreEff #[] (some bid)
  let gNonlandAccept := mustApply gNonlandAsk p0 .accept
  let gNonlandDecline := mustApply gNonlandAsk p0 .decline
  let nonlandOk :=
    (match gNonlandAsk.pending with | .resolutionChoice q (.exploreMayGraveyard _) => q == p0 | _ => false) &&
    (gNonlandAsk.object! bid).status.plusOnePlusOne == 1 &&
    (gNonlandAccept.player p0).graveyard.any (fun id => (gNonlandAccept.object! id).name == bearDef.name) &&
    (gNonlandDecline.player p0).library.any (fun id => (gNonlandDecline.object! id).name == bearDef.name)

  -- (c) CR 701.44c: explorer left battlefield before resolution → still reveals land to hand without crashing.
  let (gDeparted, _) := gLand0.move bid (.graveyard p0) none (cause := some testCause)
  let gDepRes := gDeparted.applyAbilityEffect p0 exploreEff #[] (some bid)
  let departedOk :=
    (gDepRes.player p0).hand.any (fun id => (gDepRes.object! id).name == "Forest") &&
    gDepRes.pending == .none

  -- (d) Empty library → puts a +1/+1 counter on live explorer.
  let gEmptyRes := gBase.applyAbilityEffect p0 exploreEff #[] (some bid)
  let emptyOk := (gEmptyRes.object! bid).status.plusOnePlusOne == 1

  landOk && nonlandOk && departedOk && emptyOk &&
    replayOk #[gLand1, gNonlandAccept, gNonlandDecline, gDepRes, gEmptyRes]

/-! ## 5. Empower Jace folded into `spellEffect.body` -/

#guard
  let empowerSpell := mustParse
    "Jace's Bolt\n{1}{R}\nSorcery\nJace's Bolt deals 2 damage to target creature. Empower Jace 3."
  let g0 := insertObject (addPermanent (emptyHand afterDraw p0) bearDef p1 p1) empowerSpell p0 (.hand p0)
  let bid := (g0.permanentsOf p1)[0]!.id
  let sid := (g0.player p0).hand.back!
  let g1 := g0.addMana p0 (.colored .red) 2
  let gCast := mustApply (mustApply (mustApply g1 p0 (.cast sid)) p0 (.target (.permanent bid))) p0 .pay
  let gRes1 := passBoth gCast
  let jace1 := (gRes1.jacePlaneswalkerTokens p0)[0]!
  -- Second empower adds loyalty counters to the existing Jace token instead of creating a second one.
  let gRes2 := gRes1.applyEffect p0 { body := Instruction.empowerJace 2 } #[]
  let jace2 := (gRes2.jacePlaneswalkerTokens p0)[0]!
  empowerSpell.spellEffect.isSome &&
    (gRes1.jacePlaneswalkerTokens p0).size == 1 &&
    jace1.status.loyaltyCounters == 3 &&
    (gRes2.jacePlaneswalkerTokens p0).size == 1 &&
    jace2.status.loyaltyCounters == 5 &&
    !gRes1.battlefield.any (·.id == bid) &&
    replayOk #[gRes1, gRes2]

/-! ## 6. Unified `Instruction.chooseModes` (`ModalSpec`) & Layer-3 `HasTextChange` -/

#guard
  -- 6a. Modal spell (`Choose one or both`), modal activated (`ActivatedAbility.mkModal`),
  --     and modal triggered (`TriggeredAbility.mkModal`) all live inside `Instruction.chooseModes`.
  let bothSpell := mustParse
    "Twin Boon\n{1}{W}\nSorcery\nChoose one or both —\n• Draw a card.\n• You gain 3 life."
  let modalSpecOk :=
    bothSpell.modalSpec?.any (fun ms =>
      ms.minModes == .const 1 && ms.maxModes == .const 2 && ms.modes.size == 2)
  let g0 := insertObject (emptyHand afterDraw p0) bothSpell p0 (.hand p0)
  let sid := (g0.player p0).hand.back!
  let g1 := g0.addMana p0 (.colored .white) 2
  let gCast := mustApply (mustApply (mustApply (mustApply g1 p0 (.cast sid)) p0 (.chooseMode 0)) p0 (.chooseMode 1)) p0 .pay
  let gRes := passBoth gCast
  let bothResolvedOk :=
    (gRes.player p0).hand.size == 1 &&
    (gRes.player p0).life == 23

  -- 6b. Modal activated ability (`ActivatedAbility.mkModal`) chooses mode 1 cleanly:
  let rodDef : CardDef := {
    name := "Phase8 Modal Rod", types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.mkModal CostSpec.empty #[
      { body := Instruction.gainLifeFixed 1 },
      { body := Instruction.gainLifeFixed 4 }
    ]]
  }
  let gAct0 := addPermanent (emptyHand afterDraw p0) rodDef p0 p0
  let rodId := (gAct0.permanentsOf p0)[0]!.id
  let gAct1 := mustApply (mustApply gAct0 p0 (.activate rodId 0)) p0 (.chooseMode 1)
  let gActRes := passBoth gAct1
  let modalActOk := (gActRes.player p0).life == 24

  -- 6c. Layer-3 `HasTextChange` propagates through `Instruction.chooseModes` and `GrantedAbility`:
  let tc : Array TextChange := #[.replaceCreatureType .elf .goblin]
  let elfTokenInstr : Instruction := Instruction.createTokensFixed (.custom {
    types := #[.creature], subtypes := #[.elf], power? := some (.const 1), toughness? := some (.const 1)
    colors := ColorSet.singleton .green
    abilities := #[GrantedAbility.onGainLifePutPlusOne 1]
  }) 1
  let changed := HasTextChange.applyTextChanges tc elfTokenInstr
  let tcOk :=
    match changed with
    | .create (.tokens _ _ (.custom cs) _) => cs.subtypes == #[.goblin] && cs.abilities.size == 1
    | _ => false

  modalSpecOk && bothResolvedOk && modalActOk && tcOk && replayOk #[gRes, gActRes]

/-! ## 7. Saga chapters, FRA/FRC effects, and `GrantedAbility` tokens via `Interpreter` -/

#guard
  -- 7a. `GrantedAbility` on a custom token grants a live Layer-6 trigger:
  let lifeTokenSpec : TokenSpec := .custom {
    name? := some "Phase8 Soul Token"
    types := #[.creature], subtypes := #[.spirit]
    power? := some (.const 1), toughness? := some (.const 1)
    colors := ColorSet.singleton .white
    abilities := #[GrantedAbility.onGainLifePutPlusOne 1]
  }
  let gTok0 := (emptyHand afterDraw p0).applyEffect p0
    { body := .create (.tokens .you (.const 1) lifeTokenSpec {}) } #[]
  let tok := (gTok0.permanentsOf p0).find? (·.name == "Phase8 Soul Token") |>.get!
  let gGain := gTok0.gainLife p0 2 (cause := some testCause)
  let gTrigRes := passBoth (gGain.receivePriority p0)
  let grantedTokenOk :=
    (gTok0.triggeredAbilities tok).size == 1 &&
    (gTrigRes.object! tok.id).status.plusOnePlusOne == 1

  -- 7b. Saga chapter via unified `Interpreter` (`Effect.chapterAddMana` + lifelink damage forwarding):
  let gMana := afterDraw.applyAbilityEffect p0 (Effect.chapterAddMana (.colored .green)) #[] none
  let llSaga : CardDef := {
    name := "Phase8 Lifelink Saga", types := #[.enchantment], subtypes := #["Saga"]
    keywords := #[Keyword.lifelink]
  }
  let gSaga0 := addPermanent afterDraw llSaga p0 p0
  let sagaId := (gSaga0.permanentsOf p0).find? (·.name == llSaga.name) |>.get!.id
  let gSaga1 := gSaga0.applyAbilityEffect p0 (Effect.dealDamage 2) #[.player p1] (some sagaId)
  let sagaOk :=
    (gMana.player p0).manaPool.green == 1 &&
    (gSaga1.player p1).life == 18 &&
    (gSaga1.player p0).life == 22

  -- 7c. FRC `elspethSunsChampion` emblem via `Interpreter`:
  let gElsp0 := addPermanent afterDraw bearDef p0 p0
  let bid := (gElsp0.permanentsOf p0)[0]!.id
  let gElsp1 := gElsp0.applyAbilityEffect p0 elspethSunsChampion.activatedAbilities[2]!.effect #[] none
  let elspethOk :=
    gElsp1.power (gElsp1.object! bid) == 4 &&
    gElsp1.toughness (gElsp1.object! bid) == 4 &&
    gElsp1.hasFlying (gElsp1.object! bid)

  grantedTokenOk && sagaOk && elspethOk && replayOk #[gTrigRes, gMana, gSaga1, gElsp1]

/-! ## 8. Novel Stage-4 `Parser.parseInstructionEffect` spells executed end-to-end -/

#guard
  -- 8a. Novel two-sentence draw + life gain spell:
  let novelDrawLife :=
    match Parser.parseInstructionEffect "Draw two cards. You gain 3 life." with
    | some e => e
    | none => panic! "parseInstructionEffect failed on draw + gain life"
  let g0 := emptyHand afterDraw p0
  let g1 := g0.applyEffect p0 novelDrawLife #[]
  let drawLifeOk := (g1.player p0).hand.size == 2 && (g1.player p0).life == 23

  -- 8b. Novel targeted artifact removal + scry 2 spell:
  let novelShatterScry :=
    match Parser.parseInstructionEffect "Destroy target artifact. Scry 2." with
    | some e => e
    | none => panic! "parseInstructionEffect failed on destroy artifact + scry"
  let gArt0 := addPermanent g0 relicDef p1 p1
  let aid := (gArt0.permanentsOf p1)[0]!.id
  let gArt1 := gArt0.applyEffect p0 novelShatterScry #[.permanent aid]
  let artScryOk :=
    !gArt1.battlefield.any (·.id == aid) &&
    gArt1.pending == .scry p0 2

  -- 8c. Novel `"You may pay {2}. If you do, draw two cards."` parsed & resolved:
  let novelPayDraw :=
    match Parser.parseInstructionEffect "You may pay {2}. If you do, draw two cards." with
    | some e => e
    | none => panic! "parseInstructionEffect failed on optional pay draw"
  let payAstOk :=
    match novelPayDraw.body with
    | .optional .you (some _) (.player (.drawCards .you (.const 2))) .noop => true
    | _ => false

  drawLifeOk && artScryOk && payAstOk && replayOk #[g1, gArt1]

/-! ## 9. `Instruction.forEach` pause/resume with non-zero `VarId` & `Effect.worldsWithinWorlds` -/

#guard
  -- 9a. `.forEach (.eachPlayer .any) ⟨2⟩` pausing on interactive `Pending.chooseDiscard`
  --     for each player in APNAP order, then resuming the trailing instruction after the loop.
  let eachDiscardThenGain : Effect := {
    body := .seq #[
      .forEach (.eachPlayer .any) ⟨2⟩ (Instruction.discardFixed 1 (.stepPlayers ⟨2⟩)),
      Instruction.gainLifeFixed 4
    ]
  }
  let g0 :=
    insertObject (insertObject (insertObject (insertObject (emptyHand (emptyHand afterDraw p0) p1)
      bearDef p0 (.hand p0)) elfDef p0 (.hand p0))
      bearDef p1 (.hand p1)) elfDef p1 (.hand p1)
  let gAsk0 := g0.applyEffect p0 eachDiscardThenGain #[]
  let ask0Ok := match gAsk0.pending with | .chooseDiscardCard q _ => q == p0 | _ => false
  let gAsk1 := mustApply gAsk0 p0 (.discard (gAsk0.player p0).hand[0]!)
  let ask1Ok := match gAsk1.pending with | .chooseDiscardCard q _ => q == p1 | _ => false
  let gDone := mustApply gAsk1 p1 (.discard (gAsk1.player p1).hand[0]!)
  let forEachPlayerOk :=
    ask0Ok && ask1Ok &&
    gDone.pending == .none &&
    (gDone.player p0).hand.size == 1 &&
    (gDone.player p1).hand.size == 1 &&
    (gDone.player p0).life == 24

  -- 9b. `.forEach (.eachObject ...) ⟨2⟩` with non-zero `VarId` across multiple objects.
  let eachCreatureCounter : Effect := {
    body := .forEach (.eachObject (.inZones .battlefield (.hasType .creature))) ⟨2⟩
      (Instruction.putPlusOne (.stepObjects ⟨2⟩) 1)
  }
  let gObj0 := addPermanent (addPermanent afterDraw bearDef p0 p0) elfDef p1 p1
  let gObj1 := gObj0.applyEffect p0 eachCreatureCounter #[]
  let forEachObjOk :=
    (gObj1.permanentsOf p0).all (fun o => !gObj1.isCreature o || o.status.plusOnePlusOne == 1) &&
    (gObj1.permanentsOf p1).all (fun o => !gObj1.isCreature o || o.status.plusOnePlusOne == 1)

  -- 9c. `Effect.worldsWithinWorlds` resolved directly via `applyEffect` opens APNAP
  --     `ResolutionChoice.worldsPutCreatures` prompts, enters chosen creatures simultaneously,
  --     and returns the initially exiled battlefield creature to its owner's hand.
  let gW0 :=
    insertObject (insertObject
      (addPermanent (emptyHand (emptyHand afterDraw p0) p1) bearDef p0 p0)
      elfDef p0 (.hand p0))
      elfDef p1 (.hand p1)
  let gWAsk0 := gW0.applyEffect p0 Effect.worldsWithinWorlds #[]
  let wAsk0Ok := match gWAsk0.pending with
    | .resolutionChoice q (.worldsPutCreatures ..) => q == p0
    | _ => false
  let p0Elf := (gWAsk0.player p0).hand[0]!
  let gWAsk1 := mustApply gWAsk0 p0 (.choosePermanents #[p0Elf])
  let wAsk1Ok := match gWAsk1.pending with
    | .resolutionChoice q (.worldsPutCreatures ..) => q == p1
    | _ => false
  let p1Elf := (gWAsk1.player p1).hand[0]!
  let gWDone := mustApply gWAsk1 p1 (.choosePermanents #[p1Elf])
  let worldsOk :=
    wAsk0Ok && wAsk1Ok &&
    gWDone.pending == .none &&
    (gWDone.permanentsOf p0).any (·.name == elfDef.name) &&
    (gWDone.permanentsOf p1).any (·.name == elfDef.name) &&
    (gWDone.player p0).hand.any (fun id => (gWDone.object! id).name == bearDef.name)

  forEachPlayerOk && forEachObjOk && worldsOk && replayOk #[gAsk0, gAsk1, gDone, gObj1, gWDone]

/-! ## 10. Phase 9: Unified Trigger Families, `CostSpec.bindVar?`, & `EvalEnv` Copy-Token Tie Prompting -/

#guard
  -- 10a. Migrated trigger families (watch, step, death, attack, casting, resource, enterOrAttack,
  --      modal, reflexive) execute directly via unified `Instruction` in `Game/Interpreter.lean`.
  let g0 := addPermanent (addPermanent (emptyHand afterDraw p0) bearDef p0 p0) elfDef p1 p1
  let bearId := (g0.permanentsOf p0)[0]!.id
  let elfId := (g0.permanentsOf p1)[0]!.id
  -- Watch trigger: `watchTokensEnterMayDraw` pauses on `.mayResolve`, accept draws 1.
  let gWatchAsk := g0.applyTriggeredAbility p0 (.onWatch Effect.watchTokensEnterMayDraw) (some bearId)
  let gWatchYes := mustApply gWatchAsk p0 .accept
  let watchOk := gWatchAsk.pending == .mayResolve p0 && (gWatchYes.player p0).hand.size == 1
  -- Step trigger: `stepDrawToTen` draws up to 10 cards via `ValueExpr.binary .max`.
  let gStep := g0.applyTriggeredAbility p0 (.onStep Effect.stepDrawToTen) (some bearId)
  let stepOk := (gStep.player p0).hand.size == 10
  -- Casting trigger: `castingPlusOneEachOther` puts +1/+1 on each other creature you control.
  let gCast0 := addPermanent g0 elfDef p0 p0
  let p0ElfId := (gCast0.permanentsOf p0).find? (·.name == elfDef.name) |>.get!.id
  let gCast1 := gCast0.applyTriggeredAbility p0 (.onCasting Effect.castingPlusOneEachOther) (some bearId)
  let castingOk :=
    (gCast1.object! p0ElfId).status.plusOnePlusOne == 1 &&
    (gCast1.object! bearId).status.plusOnePlusOne == 0
  -- Resource trigger: `resourceSecondDrawDrain` drains opponent 1 and gains 1.
  let gRes := g0.applyTriggeredAbility p0 (.onResource Effect.resourceSecondDrawDrain) (some bearId)
  let resourceOk := (gRes.player p1).life == 19 && (gRes.player p0).life == 21
  -- Enter-or-attack trigger: `enterOrAttackCreateSquirrel` creates a 1/1 green Squirrel token.
  let gEoa := g0.applyTriggeredAbility p0 (.onEnterOrAttack Effect.enterOrAttackCreateSquirrel) (some bearId)
  let eoaOk := (gEoa.permanentsOf p0).any (·.name == "Squirrel")
  -- Attack trigger: `thisAttackDrawIfPower4` draws when source power >= 4 (not at 2).
  let gAtkSmall := g0.applyTriggeredAbility p0 (.onThisAttack Effect.thisAttackDrawIfPower4) (some bearId)
  let gAtkBig := (g0.recordPutCounters bearId .plusOnePlusOne 2).applyTriggeredAbility p0
    (.onThisAttack Effect.thisAttackDrawIfPower4) (some bearId)
  let attackOk := (gAtkSmall.player p0).hand.isEmpty && (gAtkBig.player p0).hand.size == 1
  -- Death trigger: `deathDeathtouchOppSac` opens nontoken sacrifice choice for opponent.
  let gDeath := g0.applyTriggeredAbility p0 (.onDeath Effect.deathDeathtouchOppSac) (some bearId)
  let deathOk := match gDeath.pending with | .resolutionChoice q (.sacrificeNontokenEach _ _) => q == p1 | _ => false
  -- Modal trigger: `triggerWolfPlusOneOrTreasure` resolves mode 1 (create Treasure token).
  let gMod0 := g0.change (.pushContinuationFrame { resolvingModes := some #[1] })
  let gMod1 := gMod0.applyTriggeredAbility p0 .onCombatDamageWolfPlusOneOrTreasure (some bearId)
  let modalOk := (gMod1.permanentsOf p0).any (·.name == "Treasure")
  -- Reflexive trigger: `triggerCreateAxe true` creates Axe and queues attach reflexive trigger.
  let gRef := g0.applyTriggeredAbility p0 .onEnterCreateAxeAttach (some bearId)
  let reflexiveOk :=
    (gRef.permanentsOf p0).any (·.name == "Axe") &&
    match gRef.pending with | .chooseTargets q => q == p0 | _ => false
  -- Prevent unused binding warning on `elfId` by checking opponent creature untouched.
  let oppOk := (gCast1.object! elfId).status.plusOnePlusOne == 0
  watchOk && stepOk && castingOk && resourceOk && eoaOk && attackOk && deathOk &&
    modalOk && reflexiveOk && oppOk &&
    replayOk #[gWatchAsk, gWatchYes, gStep, gCast1, gRes, gEoa, gAtkSmall, gAtkBig, gDeath, gMod1, gRef]

#guard
  -- 10b. `CostSpec.bindVar?` binds cost-paid power into `stepEnv` for an activated ability
  --      that sacrifices a creature and gains life equal to the sacrificed creature's power.
  let sacGainCard : CardDef := {
    name := "Phase9 Sac Altar"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { CostSpec.sacrificeCreature with bindVar? := some ⟨0⟩ }
      effect := { body := Instruction.gainLife (.stepMetric .sumPower ⟨0⟩) }
    }]
  }
  let bigBear : CardDef := { bearDef with name := "Phase9 Big Bear", power := some (.fixed 5), toughness := some (.fixed 5) }
  let g0 := addPermanent (addPermanent (emptyHand afterDraw p0) sacGainCard p0 p0) bigBear p0 p0
  let altarId := (g0.permanentsOf p0).find? (·.name == "Phase9 Sac Altar") |>.get!.id
  let bigId := (g0.permanentsOf p0).find? (·.name == "Phase9 Big Bear") |>.get!.id
  let gAct := mustApply g0 p0 (.activate altarId 0)
  let gPaid := mustApply gAct p0 (.choosePermanents #[bigId])
  let gRes := passBoth gPaid
  let bindCostOk :=
    !gRes.battlefield.any (·.id == bigId) &&
    (gRes.player p0).life == 25 &&
    replayOk #[gAct, gPaid, gRes]

  -- 10c. `EvalEnv` copy-token tie prompting (`ResolutionChoice.chooseTokenCopyObject`):
  --      Copying the creature you control with the greatest power when two 2/2 creatures tie
  --      pauses on `chooseTokenCopyObject` and creates a copy of the player's chosen creature.
  let bearA : CardDef := { bearDef with name := "Tied Bear Alpha" }
  let bearB : CardDef := { bearDef with name := "Tied Bear Beta" }
  let copyGreatest : Effect := {
    body := Instruction.createTokens
      (.copyOf (.extremum .max .power
        (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))) #[])
      (.const 1)
  }
  let gTie0 := addPermanent (addPermanent (emptyHand afterDraw p0) bearA p0 p0) bearB p0 p0
  let idB := (gTie0.permanentsOf p0).find? (·.name == "Tied Bear Beta") |>.get!.id
  let gTieAsk := gTie0.applyEffect p0 copyGreatest #[]
  let tieAskOk := match gTieAsk.pending with
    | .resolutionChoice q (.chooseTokenCopyObject ids ..) => q == p0 && ids.size == 2
    | _ => false
  let gTieDone := mustApply gTieAsk p0 (.choosePermanents #[idB])
  let betaCount := ((gTieDone.permanentsOf p0).filter (·.name == "Tied Bear Beta")).size
  let alphaCount := ((gTieDone.permanentsOf p0).filter (·.name == "Tied Bear Alpha")).size
  let copyTieOk :=
    tieAskOk && gTieDone.pending == .none &&
    betaCount == 2 && alphaCount == 1 &&
    replayOk #[gTieAsk, gTieDone]

  bindCostOk && copyTieOk

end Mtg.Engine.Tests.InterpreterSuite


