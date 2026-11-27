import Mtg.Engine.Tests.Helpers

/-!
# Compositional `CostSpec` & Parameterized `KeywordAbility` Runtime Tests

Comprehensive gameplay `#guard` regression suite for compositional costs and
parameterized keywords (see `docs/card-and-ability-model.md` and
`docs/game-evaluation.md`, anchored to the 6 November 2026 CR):
1. All 15 CR 122.1b keyword counters in Layer 6 gameplay (including `.decayed`,
   `.exalted`, `.hexproof`, CR 702.4b/702.7b `firstStrike` vs `doubleStrike`,
   and CR 613.7c timestamp ordering with `losesAbilitiesUntilEot`).
2. Layer 3 `HasTextChange` on `KeywordAbility` in gameplay (Islandwalk →
   Swampwalk via `TextChange.replaceCreatureType`; Protection from blue →
   Protection from red via `TextChange.replaceColorWord`).
3. CR 606.5 / 606.6 net loyalty calculation on multi-loyalty `CostSpec`
   (`[+1]` + `[-4]` → net `-3`, `[+3]` + `[-1]` → net `+2`, `[-X]` + `[+1]`).
4. `StaticAbility.cantBeBlocked` & `ContinuousEffectSpec.cantBeBlockedUntilEot`
   (CR 509.1b non-keyword evasion + Layer 6 timestamp interaction + Equipment).
5. Compositional `KeywordAbility.ward` payment across colored mana, pay life,
   arbitrary poison counters, `.or` choice, and CR 702.21b multiplicity.
6. Compositional `parseOracleCard` + `KeywordAbility.expand` on novel
   parameterized keywords and `CostSpec`s.
-/

namespace Mtg.Engine.Tests.CostKeywordsSuite

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

private def p0 : PlayerId := ⟨0⟩
private def p1 : PlayerId := ⟨1⟩

private def testCause : EventCause := .oneShotEffect none none

private def namedPerm (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing permanent {name}"

private def enterPerm (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let g := insertObject g card p (.hand p)
  let id := (g.player p).hand.back!
  (g.move id .battlefield (some p) (cause := some testCause)).1

/-! ### 1. All 15 CR 122.1b Keyword Counters in Gameplay -/

private def all15KeywordCounters : Array (CounterKind × KeywordAbility × KeywordTag) := #[
  (.flying, Keyword.flying, .flying),
  (.firstStrike, Keyword.firstStrike, .firstStrike),
  (.doubleStrike, Keyword.doubleStrike, .doubleStrike),
  (.deathtouch, Keyword.deathtouch, .deathtouch),
  (.decayed, Keyword.decayed, .decayed),
  (.exalted, Keyword.exalted, .exalted),
  (.haste, Keyword.haste, .haste),
  (.hexproof, Keyword.hexproof, .hexproof),
  (.indestructible, Keyword.indestructible, .indestructible),
  (.lifelink, Keyword.lifelink, .lifelink),
  (.menace, Keyword.menace, .menace),
  (.reach, Keyword.reach, .reach),
  (.shadow, Keyword.shadow, .shadow),
  (.trample, Keyword.trample, .trample),
  (.vigilance, Keyword.vigilance, .vigilance)
]

-- Every one of the 15 CR 122.1b keyword counters grants its KeywordAbility in Layer 6
-- and is visible to EvalExpr.evalObjectPred (.hasKeyword tag).
#guard
  all15KeywordCounters.all fun (ck, kw, tag) =>
    let g0 := addPermanent afterDraw grizzlyBears p0 p0
    let bearId := (namedPerm g0 "Grizzly Bears").id
    let g1 := g0.recordPutCounters bearId ck 1 (some p0) (cause := some testCause)
    let o := g1.object! bearId
    let env : EvalEnv := { controller := p0 }
    ck.grantedKeyword? == some kw &&
    (g1.currentKeywords o).contains kw &&
    EvalExpr.evalObjectPred g1 env (.live o) (.hasKeyword tag)

-- CR 702.4b / 702.7b: A double-strike counter grants double strike, NOT first strike,
-- in `EvalExpr.evalObjectPred (.hasKeyword .firstStrike)`.
#guard
  let g0 := addPermanent afterDraw grizzlyBears p0 p0
  let bearId := (namedPerm g0 "Grizzly Bears").id
  let g1 := g0.recordPutCounters bearId .doubleStrike 1 (some p0) (cause := some testCause)
  let o := g1.object! bearId
  let env : EvalEnv := { controller := p0 }
  EvalExpr.evalObjectPred g1 env (.live o) (.hasKeyword .doubleStrike) &&
    !EvalExpr.evalObjectPred g1 env (.live o) (.hasKeyword .firstStrike)

-- CR 702.147a: A `.decayed` counter prevents blocking in `Game.canBlock`.
#guard
  let g0 := addPermanent (addPermanent afterDraw grizzlyBears p0 p0) grayOgre p1 p1
  let atkId := (namedPerm g0 "Grizzly Bears").id
  let blkId := (namedPerm g0 "Gray Ogre").id
  let gAtk := g0.markAttacking atkId (some (.player p1))
  let canBlockBefore := gAtk.canBlock (gAtk.object! blkId) (gAtk.object! atkId)
  let gDec := gAtk.recordPutCounters blkId .decayed 1 (some p1) (cause := some testCause)
  let canBlockWithDecayed := gDec.canBlock (gDec.object! blkId) (gDec.object! atkId)
  canBlockBefore && gDec.hasDecayed (gDec.object! blkId) && !canBlockWithDecayed

-- CR 702.11b: A `.hexproof` counter blocks targeting by an opponent (while controller can still target).
#guard
  let g0 := addPermanent afterDraw grizzlyBears p0 p0
  let bearId := (namedPerm g0 "Grizzly Bears").id
  let gHex := g0.recordPutCounters bearId .hexproof 1 (some p0) (cause := some testCause)
  let bear := gHex.object! bearId
  gHex.hasHexproof bear && !gHex.canBeTargetedBy p1 bear && gHex.canBeTargetedBy p0 bear

-- CR 613.7c: Keyword counter placed BEFORE `losesAbilitiesUntilEot` is stripped;
-- keyword counter placed AFTER `losesAbilitiesUntilEot` still applies!
#guard
  let g0 := addPermanent afterDraw grizzlyBears p0 p0
  let bearId := (namedPerm g0 "Grizzly Bears").id
  let g1 := g0.recordPutCounters bearId .hexproof 1 (some p0) (cause := some testCause)
  let g2 := g1.createEffect (.losesAbilitiesUntilEot bearId) (cause := some testCause)
  let g3 := g2.recordPutCounters bearId .exalted 1 (some p0) (cause := some testCause)
  let o2 := g2.object! bearId
  let o3 := g3.object! bearId
  !g2.hasHexproof o2 && g2.canBeTargetedBy p1 o2 &&
    !g3.hasHexproof o3 && g3.hasExalted o3

/-! ### 2. Layer 3 `HasTextChange` on `KeywordAbility` in Gameplay -/

-- CR 612.2 / 613.1c / 702.14: Islandwalk text-changed to Swampwalk becomes
-- unblockable against a defending player with a Swamp and blockable against an Island!
#guard
  let walkerDef : CardDef := {
    creature "River Strider" ManaCost.empty #["Merfolk"] 2 2 with
    keywords := #[Keyword.islandwalk]
  }
  let gBase := addPermanent (addPermanent afterDraw walkerDef p0 p0) grayOgre p1 p1
  let wId := (namedPerm gBase "River Strider").id
  let blkId := (namedPerm gBase "Gray Ogre").id
  let gBase := gBase.markAttacking wId (some (.player p1))
  let gWithIsland := addPermanent gBase island p1 p1
  let gWithSwamp := addPermanent gBase swamp p1 p1
  let islandTc := ContinuousEffectSpec.layered (.objects #[wId])
    (.text (.replaceCreatureType .island .swamp)) .untilEndOfTurn
  let gIslandTc := gWithIsland.createEffect islandTc (cause := some testCause)
  let gSwampTc := gWithSwamp.createEffect islandTc (cause := some testCause)
  -- Before text change: unblockable vs Island, blockable vs Swamp.
  !gWithIsland.canBlock (gWithIsland.object! blkId) (gWithIsland.object! wId) &&
  gWithSwamp.canBlock (gWithSwamp.object! blkId) (gWithSwamp.object! wId) &&
  -- After Island → Swamp text change: blockable vs Island, unblockable vs Swamp!
  gIslandTc.canBlock (gIslandTc.object! blkId) (gIslandTc.object! wId) &&
  !gSwampTc.canBlock (gSwampTc.object! blkId) (gSwampTc.object! wId) &&
  (gSwampTc.currentKeywords (gSwampTc.object! wId)) == #[.landwalk (.hasSubtype (.literal .swamp))]

-- CR 612.2 / 702.16: Protection from blue text-changed to Protection from red
-- blocks red targeting and allows blue targeting!
#guard
  let proBlueDef : CardDef := {
    creature "Azure Knight" ManaCost.empty #["Human", "Knight"] 2 2 with
    keywords := #[.protection (.color (.literal .blue))]
  }
  let bluePing : CardDef := {
    name := "Blue Ping", manaCost := ManaCost.ofColor .blue, types := #[.instant]
    spellAbility := some { effect := Effect.dealDamage 1 }
  }
  let redPing : CardDef := {
    name := "Red Ping", manaCost := ManaCost.ofColor .red, types := #[.instant]
    spellAbility := some { effect := Effect.dealDamage 1 }
  }
  let g0 := addPermanent afterDraw proBlueDef p1 p1
  let kId := (namedPerm g0 "Azure Knight").id
  let g1 := insertObject (insertObject g0 bluePing p0 (.hand p0)) redPing p0 (.hand p0)
  let blueObj := g1.object! ((g1.player p0).hand.find? (fun id => (g1.object! id).name == "Blue Ping")).get!
  let redObj := g1.object! ((g1.player p0).hand.find? (fun id => (g1.object! id).name == "Red Ping")).get!
  let tc := ContinuousEffectSpec.layered (.objects #[kId])
    (.text (.replaceColorWord .blue .red)) .untilEndOfTurn
  let gTc := g1.createEffect tc (cause := some testCause)
  -- Before text change: protected from blue, vulnerable to red.
  g1.protectedFrom (g1.object! kId) blueObj &&
  !g1.protectedFrom (g1.object! kId) redObj &&
  !g1.canBeTargetedBy p0 (g1.object! kId) (some blueObj.id) &&
  g1.canBeTargetedBy p0 (g1.object! kId) (some redObj.id) &&
  -- After blue → red text change: vulnerable to blue, protected from red!
  !gTc.protectedFrom (gTc.object! kId) blueObj &&
  gTc.protectedFrom (gTc.object! kId) redObj &&
  gTc.canBeTargetedBy p0 (gTc.object! kId) (some blueObj.id) &&
  !gTc.canBeTargetedBy p0 (gTc.object! kId) (some redObj.id)

/-! ### 3. CR 606.5 / 606.6 Net Loyalty Calculation on Multi-Loyalty `CostSpec` -/

private def multiLoyaltyWalker : CardDef := {
  name := "Multi-Loyalty Walker"
  manaCost := ManaCost.ofGeneric 3
  types := #[.planeswalker]
  subtypes := #["Jace"]
  loyalty := some 2
  activatedAbilities := #[
    -- Ability 0: [+1], [-4] => net -3 (CR 606.5 / 606.6)
    { cost := CostSpec.ofItems #[.loyalty (.plus 1), .loyalty (.minus 4)]
      effect := Effect.gainLife 3 },
    -- Ability 1: [+3], [-1] => net +2
    { cost := CostSpec.ofItems #[.loyalty (.plus 3), .loyalty (.minus 1)]
      effect := Effect.gainLife 1 },
    -- Ability 2: [-X], [+1] => net (1 - X)
    { cost := CostSpec.ofItems #[.loyalty .minusX, .loyalty (.plus 1)]
      effect := Effect.gainLife 1 }
  ]
}

-- At 2 loyalty, net -3 (`[+1], [-4]`) is rejected (CR 606.6); at 3 loyalty it succeeds
-- and drops to 0 (CR 704.5i SBA moves it to graveyard); at 4 loyalty it drops to 1.
#guard
  let g2 := enterPerm afterDraw multiLoyaltyWalker p0
  let pw2 := namedPerm g2 "Multi-Loyalty Walker"
  let rejectedAt2 := (g2.apply p0 (.activate pw2.id 0)).toOption.isNone
  let g3 := g2.recordPutCounters pw2.id .loyalty 1 (some p0) (cause := some testCause)
  let gAct3 := mustApply g3 p0 (.activate pw2.id 0)
  let g4 := g3.recordPutCounters pw2.id .loyalty 1 (some p0) (cause := some testCause)
  let gAct4 := mustApply g4 p0 (.activate pw2.id 0)
  rejectedAt2 &&
    (gAct3.followMovedToZone? pw2.id (· == .graveyard p0)).isSome &&
    gAct3.stack.size == 1 &&
    (gAct4.object! pw2.id).status.loyaltyCounters == 1 &&
    gAct4.stack.size == 1

-- Net +2 (`[+3], [-1]`) adds 2 loyalty counters (2 -> 4).
#guard
  let g2 := enterPerm afterDraw multiLoyaltyWalker p0
  let pw2 := namedPerm g2 "Multi-Loyalty Walker"
  let gAct := mustApply g2 p0 (.activate pw2.id 1)
  (gAct.object! pw2.id).status.loyaltyCounters == 4 && gAct.stack.size == 1

-- Net (1 - X) (`[-X], [+1]`): X = 2 drops loyalty 2 -> 1; X = 3 drops 2 -> 0 (SBA to graveyard); X = 4 rejected!
#guard
  let g2 := enterPerm afterDraw multiLoyaltyWalker p0
  let pw2 := namedPerm g2 "Multi-Loyalty Walker"
  let gPrompt := mustApply g2 p0 (.activate pw2.id 2)
  let gX2 := mustApply gPrompt p0 (.chooseX 2)
  let gX3 := mustApply gPrompt p0 (.chooseX 3)
  let x4Rejected := (gPrompt.apply p0 (.chooseX 4)).toOption.isNone
  gPrompt.pending == .chooseX p0 &&
    (gX2.object! pw2.id).status.loyaltyCounters == 1 &&
    gX2.stack.size == 1 &&
    (gX3.followMovedToZone? pw2.id (· == .graveyard p0)).isSome &&
    gX3.stack.size == 1 &&
    x4Rejected

/-! ### 4. `StaticAbility.cantBeBlocked` & Layer 6 `cantBeBlockedUntilEot` (CR 509.1b) -/

-- Printed `StaticAbility.cantBeBlocked` is NOT in `currentKeywords`, prevents blocking,
-- is stripped by newer `losesAbilitiesUntilEot`, and restored by even newer `cantBeBlockedUntilEot`.
#guard
  let phantomDef : CardDef := {
    creature "Unseen Phantom" ManaCost.empty #["Spirit"] 2 2 with
    staticAbilities := #[.cantBeBlocked]
  }
  let g0 := addPermanent (addPermanent afterDraw phantomDef p0 p0) grayOgre p1 p1
  let phId := (namedPerm g0 "Unseen Phantom").id
  let blkId := (namedPerm g0 "Gray Ogre").id
  let g0 := g0.markAttacking phId (some (.player p1))
  let gLost := g0.createEffect (.losesAbilitiesUntilEot phId) (cause := some testCause)
  let gRegained := gLost.createEffect (.cantBeBlockedUntilEot phId) (cause := some testCause)
  (g0.currentKeywords (g0.object! phId)).isEmpty &&
    g0.hasCantBeBlocked (g0.object! phId) &&
    !g0.canBlock (g0.object! blkId) (g0.object! phId) &&
    !gLost.hasCantBeBlocked (gLost.object! phId) &&
    gLost.canBlock (gLost.object! blkId) (gLost.object! phId) &&
    gRegained.hasCantBeBlocked (gRegained.object! phId) &&
    !gRegained.canBlock (gRegained.object! blkId) (gRegained.object! phId)

-- Equipment `.equippedCreatureHasKeywordsAndCantBeBlocked #[Keyword.hexproof]` grants both
-- hexproof and `hasCantBeBlocked`, and losing abilities after attachment strips both.
#guard
  let cloakDef : CardDef := {
    name := "Shadow Cloak", types := #[.artifact], subtypes := #["Equipment"]
    staticAbilities := #[.equippedCreatureHasKeywordsAndCantBeBlocked #[Keyword.hexproof]]
  }
  let g0 := addPermanent (addPermanent afterDraw grizzlyBears p0 p0) cloakDef p0 p0
  let bId := (namedPerm g0 "Grizzly Bears").id
  let cId := (namedPerm g0 "Shadow Cloak").id
  let gAtt := g0.record (GameEvent.attached g0.turnNumber (g0.snapshot (g0.object! cId)) bId (cause := testCause))
  let gLost := gAtt.createEffect (.losesAbilitiesUntilEot bId) (cause := some testCause)
  gAtt.hasHexproof (gAtt.object! bId) &&
    gAtt.hasCantBeBlocked (gAtt.object! bId) &&
    !gLost.hasHexproof (gLost.object! bId) &&
    !gLost.hasCantBeBlocked (gLost.object! bId)

/-! ### 5. Compositional `KeywordAbility.ward` Payment (CR 702.21) -/

private def triggerWardPrompt (wardKws : Array KeywordAbility) : Game × ObjectId × ObjectId :=
  let hostDef : CardDef := {
    creature "Warded Host" ManaCost.empty #["Knight"] 3 3 with
    keywords := wardKws
  }
  let g0 := addPermanent afterDraw hostDef p1 p1
  let hostId := (namedPerm g0 "Warded Host").id
  let g1 := insertObject g0 shock p0 (.hand p0)
  let handId := (g1.player p0).hand.back!
  let g2 := g1.addMana p0 (.colored .red) 1
  let g3 := mustApply g2 p0 (.cast handId)
  let g4 := mustApply g3 p0 (.target (.permanent hostId))
  let g5 := mustApply g4 p0 .pay
  let stackSpellId := g5.stack[0]!.objectId
  let gPrompt := mustApply (mustApply g5 p0 .pass) p1 .pass
  (gPrompt, stackSpellId, hostId)

-- 5a. Colored mana ward (`Ward {B}{R}`): pay `{B}{R}` keeps spell on stack; decline counters it.
#guard
  let brCost := CostSpec.ofMana { symbols := #[.colored .black, .colored .red] }
  let (gPrompt, spId, _) := triggerWardPrompt #[.ward brCost]
  let promptOk := match gPrompt.pending with | .payWard q sid c _ => q == p0 && sid == spId && c == brCost | _ => false
  let gFunded := (gPrompt.addMana p0 (.colored .black) 1).addMana p0 (.colored .red) 1
  let gPaid := mustApply gFunded p0 .payGeneric
  let gDeclined := mustApply gPrompt p0 .decline
  promptOk &&
    gPaid.pending == .none && gPaid.stack.any (·.objectId == spId) &&
    (gPaid.player p0).manaPool.isEmpty &&
    gDeclined.pending == .none && !gDeclined.stack.any (·.objectId == spId)

-- 5b. Pay life ward (`Ward—Pay 3 life`): pay deducts 3 life and keeps spell; insufficient life fails; decline counters.
#guard
  let lifeCost := CostSpec.ofItem (.payLife (.const 3))
  let (gPrompt, spId, _) := triggerWardPrompt #[.ward lifeCost]
  let gPaid := mustApply gPrompt p0 .pay
  let gLowLife := gPrompt.loseLife p0 18 (cause := some testCause)
  let lowLifeErr := (gLowLife.apply p0 .pay).toOption.isNone
  let gDeclined := mustApply gPrompt p0 .decline
  (gPaid.player p0).life == 17 &&
    gPaid.pending == .none && gPaid.stack.any (·.objectId == spId) &&
    lowLifeErr &&
    gDeclined.pending == .none && !gDeclined.stack.any (·.objectId == spId)

-- 5c. Arbitrary poison counter count (`Ward—Get two poison counters`): pay adds 2 poison and keeps spell.
#guard
  let poison2 := CostSpec.getPoisonCounters 2
  let (gPrompt, spId, _) := triggerWardPrompt #[.ward poison2]
  let gPaid := mustApply gPrompt p0 .pay
  (gPaid.player p0).poison == 2 &&
    gPaid.pending == .none && gPaid.stack.any (·.objectId == spId)

-- 5d. Compositional `.or` ward (`Ward—Discard a card or pay {1}{U}`): pay either branch!
#guard
  let orCost := CostSpec.ofItem (.or #[
    CostSpec.discardCard,
    CostSpec.ofMana { symbols := #[.generic 1, .colored .blue] }
  ])
  let (gPrompt, spId, _) := triggerWardPrompt #[.ward orCost]
  let gWithCard := insertObject gPrompt forest p0 (.hand p0)
  let handId := (gWithCard.player p0).hand.back!
  let gDiscPaid := mustApply gWithCard p0 (.discard handId)
  let gManaFunded := (gPrompt.addMana p0 .colorless 1).addMana p0 (.colored .blue) 1
  let gManaPaid := mustApply gManaFunded p0 .payGeneric
  gDiscPaid.pending == .none && gDiscPaid.stack.any (·.objectId == spId) &&
    gManaPaid.pending == .none && gManaPaid.stack.any (·.objectId == spId) &&
    (gManaPaid.player p0).manaPool.isEmpty

-- 5e. CR 702.21b cumulative ward multiplicity: two wards queue 2 triggers and stack into 3 stack objects!
#guard
  let hostDef : CardDef := {
    creature "Double Warder" ManaCost.empty #["Knight"] 3 3 with
    keywords := #[.ward (CostSpec.ofGeneric 1), .ward (CostSpec.ofItem (.payLife (.const 2)))]
  }
  let g0 := addPermanent afterDraw hostDef p1 p1
  let hostId := (namedPerm g0 "Double Warder").id
  let g1 := insertObject g0 shock p0 (.hand p0)
  let handId := (g1.player p0).hand.back!
  let g2 := g1.addMana p0 (.colored .red) 1
  let g3 := mustApply (mustApply (mustApply g2 p0 (.cast handId)) p0 (.target (.permanent hostId))) p0 .pay
  let g4 := mustApply g3 p1 (.stackTriggers (g3.defaultTriggerSourceIds p1))
  g3.wardCostsOn (g3.object! hostId) == #[CostSpec.ofGeneric 1, CostSpec.ofItem (.payLife (.const 2))] &&
    g3.pending == .chooseTriggerToStack p1 &&
    g3.waitingTriggers.size == 2 &&
    g4.stack.size == 3 -- Shock + 2 distinct Ward triggers

/-! ### 6. Compositional `parseOracleCard` & `KeywordAbility.expand` on Novel Keywords -/

#guard
  match parseOracleCard
    "Bog Marauder\n{2}{B}\nCreature — Zombie Knight\n3/2\nSwampwalk, decayed, exalted\nWard—Pay 3 life\nToxic 2" with
  | .ok c =>
    c.keywords.contains (.landwalk (.hasSubtype (.literal .swamp))) &&
    KeywordAbility.hasDecayed c.keywords &&
    KeywordAbility.hasExalted c.keywords &&
    c.keywords.contains (.ward (CostSpec.ofItem (.payLife (.const 3)))) &&
    c.keywords.contains (.toxic 2) &&
    c.wardCosts == #[CostSpec.ofItem (.payLife (.const 3))] &&
    KeywordAbility.toxicTotal c.keywords == 2
  | .error _ => false

#guard
  let expWard := KeywordAbility.expand (.ward (CostSpec.ofItem (.payLife (.const 3))))
  let expCrew := KeywordAbility.expand (.crew 3)
  let expGift := KeywordAbility.expand (.gift .treasure)
  let expKicker := KeywordAbility.expand (.kicker (CostSpec.ofMana { symbols := #[.generic 1, .colored .blue] }))
  let expFlashback := KeywordAbility.expand (.flashback (CostSpec.ofMana { symbols := #[.generic 2, .colored .red] }))
  let expMorph := KeywordAbility.expand (.morph (CostSpec.ofMana { symbols := #[.generic 1, .colored .green] }))
  let expImpending := KeywordAbility.expand (.impending 4 (CostSpec.ofMana { symbols := #[.generic 1, .colored .white] }))
  let expCycling := KeywordAbility.expand (.cycling none (CostSpec.ofGeneric 2))
  let expTeamwork := KeywordAbility.expand (.teamwork 2)
  expWard.triggeredAbilities.size == 1 &&
    expCrew.activatedAbilities.size == 1 &&
    expCrew.activatedAbilities[0]!.cost.crewPower? == some 3 &&
    expGift.additionalCosts.size == 1 && expGift.additionalCosts[0]!.optional &&
    expKicker.additionalCosts.size == 1 && expKicker.additionalCosts[0]!.keywordTag? == some .kicker &&
    expFlashback.alternativeCosts.size == 1 && expFlashback.alternativeCosts[0]!.fromZones == #[.graveyard] &&
    expMorph.alternativeCosts.size == 1 && expMorph.alternativeCosts[0]!.faceDown &&
    expImpending.alternativeCosts.size == 1 && expImpending.alternativeCosts[0]!.keywordTag? == some .impending &&
    expCycling.activatedAbilities.size == 1 && expCycling.activatedAbilities[0]!.isFromHand &&
    expTeamwork.additionalCosts.size == 1 && expTeamwork.additionalCosts[0]!.keywordTag? == some .teamwork

/-! ### 7. Layer 3 Text-Changing Effects on `SpellAbility.additionalCosts` (CR 612 / 613.1c) -/

-- 7a. Mandatory subtype sacrifice additional cost (`sacrifice a Dragon`) is rewritten
-- by Layer 3 `TextChange.replaceCreatureType .dragon .goblin` across
-- `additionalCostsFor`, `mandatorySacrificeError?`, `sacrificeCreatureOrArtifactChoices`,
-- and `spellSacrificeCostPredFor?`.
#guard
  let sacDragonSpell : CardDef := {
    name := "Draconic Offering"
    manaCost := ManaCost.ofColor .red
    types := #[.sorcery]
    spellAbility := some {
      additionalCosts := #[{
        cost := CostSpec.ofItem (.sacrifice (.exact 1) (.filter (.hasSubtype (.literal .dragon))))
      }]
      effect := Effect.draw 2
    }
  }
  let goblinDef : CardDef := creature "Test Goblin" ManaCost.empty #["Goblin"] 1 1
  let g0 := addPermanent afterDraw goblinDef p0 p0
  let gobId := (namedPerm g0 "Test Goblin").id
  let g1 := insertObject g0 sacDragonSpell p0 (.hand p0)
  let handSpId := (g1.player p0).hand.back!
  let handSpObj := g1.object! handSpId
  let gStack := insertObject g1 sacDragonSpell p0 .stack (some p0)
  let stackSpId := (gStack.objects.find? (fun o => o.zone == .stack && o.name == "Draconic Offering")).get!.id
  let tcHand := ContinuousEffectSpec.layered (.objects #[handSpId])
    (.text (.replaceCreatureType .dragon .goblin)) .untilEndOfTurn
  let tcStack := ContinuousEffectSpec.layered (.objects #[stackSpId])
    (.text (.replaceCreatureType .dragon .goblin)) .untilEndOfTurn
  let gTc := (gStack.createEffect tcHand (cause := some testCause)).createEffect tcStack (cause := some testCause)
  let handSpObjTc := gTc.object! handSpId
  -- Before Layer 3 text change: requires Dragon, Goblin is ineligible.
  (gStack.mandatorySacrificeError? p0 handSpId (gStack.baseCard handSpObj)).isSome &&
    (gStack.sacrificeCreatureOrArtifactChoices p0 stackSpId).isEmpty &&
    gStack.spellSacrificeCostPredFor? handSpObj (gStack.baseCard handSpObj) == some (.hasSubtype (.literal .dragon)) &&
  -- After Layer 3 Dragon -> Goblin text change: Goblin satisfies sacrifice cost!
    (gTc.mandatorySacrificeError? p0 handSpId (gTc.baseCard handSpObjTc)).isNone &&
    (gTc.sacrificeCreatureOrArtifactChoices p0 stackSpId).map (·.id) == #[gobId] &&
    gTc.spellSacrificeCostPredFor? handSpObjTc (gTc.baseCard handSpObjTc) == some (.hasSubtype (.literal .goblin))

-- 7b. Choice additional cost (`behold a Dragon or pay {2}`) is rewritten by Layer 3
-- `TextChange.replaceCreatureType .dragon .goblin` across `additionalChoiceCostFor?`,
-- `canPayAnnouncedAdditional`, and stack-time `chooseAdditionalCost` -> `needsBehold = some .goblin`.
#guard
  let beholdOrPaySpell : CardDef := {
    name := "Draconic Command"
    manaCost := ManaCost.ofColor .red
    types := #[.instant]
    spellAbility := some {
      additionalCosts := #[{
        cost := CostSpec.ofItem (.or #[
          CostSpec.ofItem (.behold .dragon),
          CostSpec.ofGeneric 2
        ])
      }]
      effect := Effect.draw 1
    }
  }
  let goblinDef : CardDef := creature "Behold Goblin" ManaCost.empty #["Goblin"] 1 1
  let g0 := (addPermanent afterDraw goblinDef p0 p0).addMana p0 (.colored .red) 1
  let g1 := insertObject g0 beholdOrPaySpell p0 (.hand p0)
  let handId := (g1.player p0).hand.back!
  let handObj := g1.object! handId
  let tcHand := ContinuousEffectSpec.layered (.objects #[handId])
    (.text (.replaceCreatureType .dragon .goblin)) .untilEndOfTurn
  let gTcHand := g1.createEffect tcHand (cause := some testCause)
  let handObjTc := gTcHand.object! handId
  -- Before text change: cannot pay `{R}` + `{2}` and has no Dragon to behold.
  let beforeUnpayable :=
    !g1.canPayAnnouncedAdditional p0 handObj (g1.player p0).manaPool &&
    g1.additionalChoiceCostFor? handObj (g1.baseCard handObj) ==
      some #[CostSpec.ofItem (.behold .dragon), CostSpec.ofGeneric 2]
  -- After text change: `behold a Goblin` is payable with the battlefield Goblin!
  let afterPayable :=
    gTcHand.canPayAnnouncedAdditional p0 handObjTc (gTcHand.player p0).manaPool &&
    gTcHand.additionalChoiceCostFor? handObjTc (gTcHand.baseCard handObjTc) ==
      some #[CostSpec.ofItem (.behold .goblin), CostSpec.ofGeneric 2]
  -- On the stack during `.chooseAdditionalCost`, Layer 3 rewrites the required behold subtype
  -- to `.goblin` so `p0` can choose `.chooseAdditionalCost false` and cast without spending `{2}`:
  let gFunded := g1.addMana p0 .colorless 2
  let gAsked := mustApply gFunded p0 (.cast handId)
  let stackSpellId := gAsked.proposedSpell.get!.spellId
  let rejectedBeforeTc := (gAsked.apply p0 (.chooseAdditionalCost false)).toOption.isNone
  let tcStack := ContinuousEffectSpec.layered (.objects #[stackSpellId])
    (.text (.replaceCreatureType .dragon .goblin)) .untilEndOfTurn
  let gAskedTc := gAsked.createEffect tcStack (cause := some testCause)
  let gChoseBehold := mustApply gAskedTc p0 (.chooseAdditionalCost false)
  let gCast := mustApply gChoseBehold p0 .pay
  let stackFlowOk :=
    rejectedBeforeTc &&
    gChoseBehold.proposedSpell.bind (·.needsBehold) == some .goblin &&
    gChoseBehold.pending == .activateManaAbilities p0 &&
    gCast.stack.any (·.objectId == stackSpellId) &&
    (gCast.player p0).manaPool.total == 2
  beforeUnpayable && afterPayable && stackFlowOk

end Mtg.Engine.Tests.CostKeywordsSuite
