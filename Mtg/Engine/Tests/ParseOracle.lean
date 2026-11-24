import Mtg.Engine.Tests.Builders
import Mtg.Engine.Card.ParseOracle
import Mtg.Engine.Catalog.Supported

/-!
# Oracle parser checks

`#guard` regression tests for `parseOracleCard` and its helpers. They are kept
out of `Mtg.Engine.Card.ParseOracle` so they run the compiled parser and the
catalog does not wait for them.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open OracleNorm

/-- A stored line's cached normal forms equal normalizing it for the card,
whether or not the card's name occurs in the line. -/
def normLineAgrees (cardName line : String) : Bool :=
  let n := NormLine.of line
  n.unitFor cardName (nameKeys cardName) == normalizeUnit cardName line &&
    n.structuralFor cardName (nameKeys cardName) == normalizeStructural cardName line

#guard normLineAgrees "Shock" "Draw two cards."
#guard normLineAgrees "Shock" "Shock deals 2 damage to any target."
#guard normLineAgrees "Gandalf, Spark Starter" "Gandalf deals 2 damage to any target."
#guard normLineAgrees "Bilbo, Retired Burglar" "Put a +1/+1 counter on Bilbo's ally."
#guard normLineAgrees "Elven Raft-Steerer" "Other Elven creatures you control get +1/+1."
#guard normLineAgrees "Lightning Bolt"
  "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn. (Reminder.)"
#guard (NormLine.of "Draw two cards.").unit == normalizeUnit "Shock" "Draw two cards."
#guard mentionsNameKey (nameKeys "Shock") (NormLine.of "Shock deals 2 damage to any target.").base

#guard parseManaCost "{1}{G}" == some (ManaCost.ofGenericAndColor 1 .green)
#guard parseManaCost "{W}" == some (ManaCost.ofColor .white)
#guard parseManaCost "{G/U}" == some (ManaCost.ofHybrid .green .blue)
#guard (parseTypeLine "Legendary Creature — Dwarf Scout").toOption ==
  some (#[.legendary], #[.creature], #["Dwarf", "Scout"])
#guard parsePT "2/2" == some (.fixed 2, .fixed 2)
#guard parsePT "2/3" == some (.fixed 2, .fixed 3)
#guard parsePT "-1/-1" == some (.fixed (-1), .fixed (-1))
#guard parsePT "*/*" == some (.star 0, .star 0)
#guard parsePT "1/*" == some (.fixed 1, .star 0)
#guard parsePT "*/3" == some (.star 0, .fixed 3)
#guard parsePT "*/4" == some (.star 0, .fixed 4)
#guard parsePT "1+*/1+*" == some (.star 1, .star 1)
#guard parsePT "*+1/*+1" == parsePT "1+*/1+*"
#guard parsePT "1 + */1 + *" == parsePT "1+*/1+*"
#guard parsePT "*/1+*" == some (.star 0, .star 1)
#guard parsePT "2+*/2+*" == some (.star 2, .star 2)
#guard parsePT "*-1/*-1" == some (.star (-1), .star (-1))
#guard (parsePT "1+*/1+*").map (fun (p, t) => (p.undetermined, t.undetermined)) == some (1, 1)
#guard (parsePT "*/*").map (fun (p, t) => (p.undetermined, t.undetermined)) == some (0, 0)
#guard parsePT "+1/+1" == none
#guard parsePT "2*/2*" == none
#guard parsePT "1+/1" == none
#guard parsePT "*+/*+" == none
#guard parsePT "*1/*1" == none
#guard (parseOracleCard "Grizzly Bears\n{1}{G}\nCreature — Bear\n2/2").toOption.map
    (fun c => c.name == "Grizzly Bears" && c.manaCost == ManaCost.ofGenericAndColor 1 .green &&
      c.power == some (.fixed 2) && c.toughness == some (.fixed 2) &&
      c.isCreature && c.modellingError?.isNone) == some true

-- A line the engine does not recognize is rejected, and an effect that would
-- not resolve is rejected by `modellingError?`.
#guard
  match parseOracleCard "Bogus\n{R}\nInstant\nFrobnicate the widget." with
  | .error e => e.contains "unrecognized" || e.contains "unparsed" || e.contains "not fully modelled"
  | .ok _ => false
#guard
  let bogus : CardDef := {
    name := "Bogus"
    types := #[.instant]
    spellAbility := some { effect := { body := .noop } }
  }
  match bogus.modellingError? with
  | some e => e.contains "not fully modelled"
  | none => false

-- CR 208.2 / 208.2a: power and toughness may include a star. Lost Order of
-- Jarkeld is `1+*`. With no chosen player, the star is 0, so the card is 1/1.
-- `*+1` is that same printed value. A bare star is 0.
#guard (parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n1+*/1+*\nVigilance").toOption.map
    (fun c => c.power == some (.star 1) && c.toughness == some (.star 1) &&
      c.powerValue == some 1 && c.toughnessValue == some 1 && c.ptString == "1+*/1+*" &&
      KeywordAbility.hasVigilance c.keywords && c.hasSubtype .human && c.hasSubtype .knight) == some true
#guard (parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n*+1/*+1").toOption.map
    (fun c => c.power == some (.star 1) && c.toughness == some (.star 1) &&
      c.ptString == "1+*/1+*") == some true
#guard (parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n1 + * / 1 + *").toOption.map
    (fun c => c.ptString == "1+*/1+*" && c.powerValue == some 1) == some true
#guard
  match parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n1+*/1+*\nVigilance" with
  | .ok c =>
    match parseOracleCard (renderFullOracle c) with
    | .ok d => d == c && d.power == some (.star 1) && d.toughness == some (.star 1) &&
        d.ptString == "1+*/1+*" && KeywordAbility.hasVigilance d.keywords
    | .error _ => false
  | .error _ => false
#guard (parseOracleCard "Tarmogoyf\n{1}{G}\nCreature — Lhurgoyf\n*/1+*").toOption.map
    (fun c => c.power == some (.star 0) && c.toughness == some (.star 1) &&
      c.powerValue == some 0 && c.toughnessValue == some 1 && c.ptString == "*/1+*") == some true
#guard (parseOracleCard "Angry Mob\n{2}{W}{W}\nCreature — Human\n2+*/2+*").toOption.map
    (fun c => c.power == some (.star 2) && c.toughness == some (.star 2) &&
      c.powerValue == some 2 && c.ptString == "2+*/2+*") == some true
#guard (parseOracleCard "Maro\n{2}{G}{G}\nCreature — Elemental\n*/*").toOption.map
    (fun c => c.power == some (.star 0) && c.toughness == some (.star 0) &&
      c.powerValue == some 0 && c.toughnessValue == some 0 && c.ptString == "*/*") == some true
#guard (parseOracleCard "Namor the Sub-Mariner\n{1}{U}{U}\nLegendary Creature — Mutant Merfolk Villain\n*/4\nFlying").toOption.map
    (fun c => c.power == some (.star 0) && c.toughness == some (.fixed 4) &&
      c.ptString == "*/4" && KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Mountain\nBasic Land — Mountain\n({T}: Add {R}.)").toOption.map
    (fun c => c.isLand && c.hasSupertype .basic && c.hasSubtype .mountain &&
      c.activatedAbilities.isEmpty) == some true
#guard (parseOracleCard "Shock\n{R}\nInstant\nShock deals 5 damage to any target.").toOption.bind
    (·.spellEffect) == some (Effect.dealDamage 5)
#guard (parseOracleCard
    "Quiet\n{U}\nInstant\nCounter target spell. If that spell's mana value was 4 or less, recruit.").toOption.bind
    (·.spellEffect) == some (Effect.counterThenRecruitIfMvAtMost 4)
#guard (parseOracleCard "Insight\n{U}\nSorcery\nDraw seven cards.").toOption.bind
    (·.spellEffect) == some (Effect.draw 7)
#guard (parseOracleCard
    "Hour of Defeat\n{3}{B}\nInstant\nDestroy target creature. Surveil 1.").toOption.bind
    (·.spellEffect) == some Effect.destroyCreatureSurveil
#guard (parseOracleCard
    ("Depower\n{2}{U}\nInstant\nThis spell costs {2} less to cast if it targets an attacking creature.\n" ++
      "Target creature gets -4/-0 until end of turn.\nDraw a card.")).toOption.bind
    (fun c => c.spellEffect.map (·.body)) ==
    some (.seq #[Instruction.pumpFixed (.target 0) (-4) 0, Instruction.drawFixed 1])
#guard (parseOracleCard "Wander\n{G}\nInstant\nForestcycling {2}").toOption.map
    (fun c =>
      c.keywords == #[.cycling (some (.hasSubtype (.literal .forest))) (CostSpec.ofMana (ManaCost.ofGeneric 2))] &&
      c.allActivatedAbilities[0]? ==
        some (Catalog.typecyclingAbility "Forest" (ManaCost.ofGeneric 2))) == some true
#guard (parseOracleCard "Sword\n{2}\nArtifact — Equipment\nEquip {5}").toOption.map
    (fun c =>
      c.keywords == #[.equip (.all #[.hasType .creature, .controlledBy .you]) (CostSpec.ofMana (ManaCost.ofGeneric 5))] &&
      c.allActivatedAbilities[0]? == some (Catalog.equipAbility (ManaCost.ofGeneric 5))) == some true
#guard (parseOracleCard "Warren Chief\n{1}{R}\nCreature — Goblin\n2/2\nOther Goblin creatures you control get +2/+2.").toOption.bind
    (fun c => c.staticAbilities[0]?) == some (.otherCreaturesGet #[.goblin] 2 2)
#guard (parseOracleCard "Test Saga\n{2}{R}\nEnchantment — Saga\nI — Draw seven cards.").toOption.bind
    (fun c => (c.sagaChapters[0]?).map (·.effect.body)) ==
    some (Instruction.drawFixed 7)

#guard CardType.all.all fun t =>
  (parseTypeLine t.englishName).toOption == some (#[], #[t], #[])
#guard (parseTypeLine "Artifact Creature — Golem").toOption ==
  some (#[], #[.artifact, .creature], #["Golem"])
#guard (parseTypeLine "Kindred Enchantment — Faerie").toOption ==
  some (#[], #[.kindred, .enchantment], #["Faerie"])
#guard (parseTypeLine "kindred instant — goblin").toOption ==
  some (#[], #[.kindred, .instant], #["goblin"])
#guard (parseTypeLine "Legendary Planeswalker — Jace").toOption ==
  some (#[.legendary], #[.planeswalker], #["Jace"])
#guard (parseTypeLine "Battle — Siege").toOption ==
  some (#[], #[.battle], #["Siege"])
#guard (parseTypeLine "Dungeon — Undercity").toOption ==
  some (#[], #[.dungeon], #["Undercity"])
#guard Supertype.all.all fun s =>
  (parseTypeLine s!"{s} Creature").toOption == some (#[s], #[.creature], #[])
#guard Supertype.all.all fun s =>
  (parseTypeLine (s.englishName.map Char.toUpper ++ " Land")).toOption ==
    some (#[s], #[.land], #[])
#guard (parseTypeLine "Basic Snow Land — Island").toOption ==
  some (#[.basic, .snow], #[.land], #["Island"])
#guard (parseTypeLine "LEGENDARY snow Creature — Elemental").toOption ==
  some (#[.legendary, .snow], #[.creature], #["Elemental"])
#guard (parseTypeLine "World Enchantment — Aura").toOption ==
  some (#[.world], #[.enchantment], #["Aura"])
#guard (parseTypeLine "Legendary Sorcery").toOption ==
  some (#[.legendary], #[.sorcery], #[])
#guard (parseTypeLine "Legendary Instant").toOption ==
  some (#[.legendary], #[.instant], #[])
#guard (parseTypeLine "Ongoing Scheme").toOption ==
  some (#[.ongoing], #[.scheme], #[])
#guard (parseTypeLine "Plane — Bolas's Meditation Realm").toOption ==
  some (#[], #[.plane], #["Bolas's Meditation Realm"])
#guard (parseTypeLine "Phenomenon").toOption == some (#[], #[.phenomenon], #[])
#guard (parseTypeLine "Conspiracy").toOption == some (#[], #[.conspiracy], #[])
#guard (parseTypeLine "Vanguard").toOption == some (#[], #[.vanguard], #[])

#guard (parseOracleCard "Jace\n{2}{U}{U}\nLegendary Planeswalker — Jace\n3").toOption.map
    (fun c => c.isPlaneswalker && c.hasSubtype .jace && c.loyalty == some 3) == some true

-- CR 209.1: the loyalty number is the corner number, labeled or bare, and it
-- may follow the rules text. It is that planeswalker's loyalty off the
-- battlefield. CR 209.2 / 107.7: `[+N]`, `[-N]`, `[0]`, `[+X]`, and `[-X]`
-- (with or without brackets) are loyalty abilities.
#guard parseLoyaltyAbilityLine "+2: Draw a card." == some (.plus 2, "Draw a card.")
#guard parseLoyaltyAbilityLine "[+1]: Draw a card." == some (.plus 1, "Draw a card.")
#guard parseLoyaltyAbilityLine "−1: Scry 2." == some (.minus 1, "Scry 2.")
#guard parseLoyaltyAbilityLine "–2: Draw a card." == some (.minus 2, "Draw a card.")
#guard parseLoyaltyAbilityLine "[-X]: Draw a card." == some (.minusX, "Draw a card.")
#guard parseLoyaltyAbilityLine "[+X]: Scry 1." == some (.plusX, "Scry 1.")
#guard parseLoyaltyAbilityLine "0: Draw two cards." == some (.zero, "Draw two cards.")
#guard parseLoyaltyAbilityLine "[0]: Draw a card." == some (.zero, "Draw a card.")
#guard parseLoyaltyAbilityLine "+1/+1" == none
#guard parseLoyaltyAbilityLine "Draw a card." == none
#guard (LoyaltySymbol.plus 2).counters == some 2
#guard (LoyaltySymbol.minus 1).counters == some (-1)
#guard LoyaltySymbol.zero.counters == some 0
#guard LoyaltySymbol.plusX.counters == none
#guard LoyaltySymbol.minusX.counters == none
#guard (LoyaltySymbol.minus 3).toNotation == "[-3]"
#guard (LoyaltySymbol.zero).toNotation == "[0]"
#guard (parseOracleCard "Jace\n{2}{U}{U}\nLegendary Planeswalker — Jace\nloyalty: 2").toOption.map
    (·.loyalty) == some (some 2)
#guard (parseOracleCard "Jace\n{2}{U}{U}\nLegendary Planeswalker — Jace\n+1: Draw a card.\nLoyalty: 5").toOption.map
    (fun c => c.loyalty == some 5 && c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.isLoyaltyAbility &&
      c.activatedAbilities[0]!.cost.loyalty == some (.plus 1) &&
      c.activatedAbilities[0]!.effect == Effect.draw 1) == some true
#guard
  match parseOracleCard "Jace\n{2}{U}{U}\nLegendary Planeswalker — Jace\n+2: Draw a card.\n−1: Scry 2.\n0: Draw two cards.\n[+X]: Scry 1.\n[-X]: Draw a card.\n3" with
  | .ok c =>
    c.loyalty == some 3 &&
    c.activatedAbilities.map (fun ab => ab.cost.loyalty) ==
      #[some (.plus 2), some (.minus 1), some .zero, some .plusX, some .minusX] &&
    c.activatedAbilities[0]!.effect == Effect.draw 1 &&
    c.activatedAbilities[1]!.effect == Effect.scry 2 &&
    c.activatedAbilities[2]!.effect == Effect.draw 2 &&
    c.activatedAbilities[3]!.effect == Effect.scry 1 &&
    c.activatedAbilities[4]!.effect == Effect.draw 1 &&
    match parseOracleCard (renderFullOracle c) with
    | .ok d => d.loyalty == c.loyalty && d.activatedAbilities == c.activatedAbilities
    | .error _ => false
  | .error _ => false
#guard
  match parseOracleCard "Jace\n{U}\nLegendary Planeswalker — Jace\n3\nLoyalty: 4" with
  | .error e => e == "Jace has more than one loyalty number"
  | .ok _ => false
#guard
  match parseOracleCard "Jace\n{U}\nLegendary Planeswalker — Jace\n3\n+1: Draw a card.\n4" with
  | .error e => e == "Jace has more than one loyalty number"
  | .ok _ => false
#guard (parseOracleCard "Jace\n{U}\nLegendary Planeswalker — Jace\n+1: Draw a card.\nLoyalty: 6\n0: Scry 1.").toOption.map
    (fun c => c.loyalty == some 6 &&
      c.activatedAbilities.map (fun ab => ab.cost.loyalty) ==
        #[some (.plus 1), some .zero]) == some true
#guard
  match parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nLoyalty: 3" with
  | .ok _ => false
  | .error _ => true
#guard (parseOracleCard "Relic\n{1}\nArtifact\n+1: Draw a card.").toOption.map
    (fun c => c.loyalty.isNone && c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.isLoyaltyAbility &&
      c.activatedAbilities[0]!.cost.loyalty == some (.plus 1) &&
      c.activatedAbilities[0]!.effect == Effect.draw 1) == some true
#guard (parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\nDefense: 4").toOption.map
    (fun c => c.isBattle && c.hasSubtype .siege && c.defense == some 4 &&
      c.loyalty.isNone) == some true

-- CR 210.1: the defense number is the corner number, labeled or bare, and it
-- may follow the rules text. It is that battle's defense off the battlefield,
-- and the battle enters with that many defense counters.
#guard (parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\n4").toOption.map
    (fun c => c.isBattle && c.defense == some 4) == some true
#guard (parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\ndefense: 4").toOption.map
    (·.defense) == some (some 4)
#guard (parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\nFlying\nDefense: 4").toOption.map
    (fun c => c.defense == some 4 && KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\n4\nFlying").toOption.map
    (fun c => c.defense == some 4 && KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\nFlying\n4").toOption.map
    (·.defense) == some (some 4)
#guard
  match parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\nFlying\n4" with
  | .ok c =>
    c.defense == some 4 && KeywordAbility.hasFlying c.keywords &&
    match parseOracleCard (renderFullOracle c) with
    | .ok d => d.defense == c.defense && KeywordAbility.hasFlying d.keywords
    | .error _ => false
  | .error _ => false
#guard
  match parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\n4\nDefense: 5" with
  | .error e => e == "Invasion of Zendikar has more than one defense number"
  | .ok _ => false
#guard
  match parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\n4\nFlying\n5" with
  | .error e => e == "Invasion of Zendikar has more than one defense number"
  | .ok _ => false
#guard
  match parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\nDefense: 4\nDefense: 5" with
  | .error e => e == "Invasion of Zendikar has more than one defense number"
  | .ok _ => false
#guard
  match parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nDefense: 3" with
  | .ok _ => false
  | .error _ => true
#guard
  match parseOracleCard "Relic\n{1}\nArtifact\n4" with
  | .ok _ => false
  | .error _ => true
#guard
  match parseOracleCard "Invasion of Zendikar\n{2}{G}\nBattle — Siege\nFlying\n4\n//\nAwakened Skyclave\nCreature — Elemental\n4/4" with
  | .ok c =>
    c.defense == some 4 && KeywordAbility.hasFlying c.keywords &&
    match c.otherFace with
    | some back => back.isCreature && back.power == some (.fixed 4) && back.toughness == some (.fixed 4) &&
        back.defense.isNone && back.loyalty.isNone
    | none => false
  | .error _ => false
#guard (parseOracleCard "Urza\nVanguard\nHand +1, Life +10").toOption.map
    (fun c => c.hasType .vanguard && c.isVanguard && c.handModifier == some 1 &&
      c.lifeModifier == some 10) == some true

-- CR 211.1 / 212.1: the hand modifier is the lower-left corner and the life
-- modifier is the lower-right corner. Each is `+N`, `-N`, or `0`. Labels and
-- a bare pair may sit before the rules text or after it.
#guard parseModifier "0" == some 0
#guard parseModifier "+0" == some 0
#guard parseModifier "-0" == some 0
#guard parseModifier "−0" == some 0
#guard parseModifier "+2" == some 2
#guard parseModifier "-3" == some (-3)
#guard parseModifier "−4" == some (-4)
#guard parseModifier "–5" == some (-5)
#guard parseModifier "+ 6" == some 6
#guard parseModifier "2" == none
#guard parseModifier "+" == none
#guard parseModifier "1+*" == none
#guard parseHandLifeLine "Hand +1, Life +10" == some (1, 10)
#guard parseHandLifeLine "Life -2, Hand modifier: +1" == some (1, -2)
#guard parseHandLifeLine "hand: +0, life: 0" == some (0, 0)
#guard parseBareModifierPair "+1 -2" == some (1, -2)
#guard parseBareModifierPair "+1, 0" == some (1, 0)
#guard parseBareModifierPair "Hand +1, Life +10" == none
#guard (parseOracleCard "Urza\nVanguard\nHand: +1\nLife: -2").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some (-2)) == some true
#guard (parseOracleCard "Urza\nVanguard\nhand modifier: +1\nlife modifier: −2").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some (-2)) == some true
#guard (parseOracleCard "Urza\nVanguard\nLife +10, Hand +1").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some 10) == some true
#guard (parseOracleCard "Urza\nVanguard\n+1\n+10").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some 10 &&
      c.loyalty.isNone && c.defense.isNone) == some true
#guard (parseOracleCard "Urza\nVanguard\n+1 -2").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some (-2)) == some true
#guard (parseOracleCard "Urza\nVanguard\n0\n0").toOption.map
    (fun c => c.handModifier == some 0 && c.lifeModifier == some 0) == some true
#guard (parseOracleCard "Urza\nVanguard\nFlying\n+1\n-2").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some (-2) &&
      KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Urza\nVanguard\n+1\n-2\nFlying").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some (-2) &&
      KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Urza\nVanguard\nFlying\nHand: +1\nLife: 0").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some 0 &&
      KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Urza\nVanguard\n+1\nFlying\n-2").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some (-2) &&
      KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Urza\nVanguard\nHand: +1\nFlying\n-2").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some (-2) &&
      KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Urza\nVanguard\n+1\nFlying\nLife: +10").toOption.map
    (fun c => c.handModifier == some 1 && c.lifeModifier == some 10 &&
      KeywordAbility.hasFlying c.keywords) == some true
#guard (parseOracleCard "Urza\nVanguard\n+1: Draw a card.\n+2\n-3").toOption.map
    (fun c => c.handModifier == some 2 && c.lifeModifier == some (-3) &&
      c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.cost.loyalty == some (.plus 1) &&
      c.activatedAbilities[0]!.effect == Effect.draw 1) == some true
#guard (parseOracleCard "Urza\nVanguard\nFlying").toOption.map
    (fun c => c.handModifier.isNone && c.lifeModifier.isNone && KeywordAbility.hasFlying c.keywords) ==
    some true
#guard
  match parseOracleCard "Urza\nVanguard\nFlying\n+1\n-2" with
  | .ok c =>
    c.handModifier == some 1 && c.lifeModifier == some (-2) && KeywordAbility.hasFlying c.keywords &&
    match parseOracleCard (renderFullOracle c) with
    | .ok d => d.handModifier == c.handModifier && d.lifeModifier == c.lifeModifier &&
        KeywordAbility.hasFlying d.keywords && d.isVanguard
    | .error _ => false
  | .error _ => false
#guard
  match parseOracleCard "Urza\nVanguard\nHand: +1\nHand: +2" with
  | .error e => e == "Urza has more than one hand modifier"
  | .ok _ => false
#guard
  match parseOracleCard "Urza\nVanguard\nHand +1, Life +10\nLife: +3" with
  | .error e => e == "Urza has more than one life modifier"
  | .ok _ => false
#guard
  match parseOracleCard "Urza\nVanguard\n+1\n+10\nHand: +2" with
  | .error e => e == "Urza has more than one hand modifier"
  | .ok _ => false
#guard
  match parseOracleCard "Urza\nVanguard\n+1\n+2\nFlying\n+3\n+4" with
  | .error e => e == "Urza has more than one hand modifier"
  | .ok _ => false
#guard
  match parseOracleCard "Urza\nVanguard\n+1\n+2\n+3" with
  | .error e => e == "Urza has more than one hand modifier"
  | .ok _ => false
#guard
  match parseOracleCard "Urza\nVanguard\n+1" with
  | .error e => e == "Urza has only one of its hand and life modifiers"
  | .ok _ => false
#guard
  match parseOracleCard "Urza\nVanguard\nFlying\n-2" with
  | .error e => e == "Urza has only one of its hand and life modifiers"
  | .ok _ => false
#guard
  match parseOracleCard "Urza\nVanguard\nHand 2\nLife +1" with
  | .error e => e == "unrecognized Oracle line on Urza: Hand 2"
  | .ok _ => false
#guard
  match parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nHand +1, Life +10" with
  | .ok _ => false
  | .error _ => true
#guard
  match parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nHand: +1" with
  | .ok _ => false
  | .error _ => true
#guard
  match parseOracleCard "Relic\n{1}\nArtifact\n+1\n+10" with
  | .ok _ => false
  | .error _ => true
#guard (parseOracleCard "Undercity\nDungeon — Undercity").toOption.map
    (fun c => c.hasType .dungeon && c.hasSubtype .undercity) == some true
#guard (parseOracleCard "Tazeem\nPlane — Zendikar").toOption.map
    (fun c => c.hasType .plane && c.subtypes == #["Zendikar"]) == some true
#guard (parseOracleCard "Interplanar Tunnel\nPhenomenon").toOption.map
    (fun c => c.hasType .phenomenon && c.subtypes.isEmpty) == some true
#guard (parseOracleCard "All in Good Time\nOngoing Scheme").toOption.map
    (fun c => c.hasType .scheme && c.hasSupertype .ongoing) == some true
#guard (parseOracleCard "Snow-Covered Island\nBasic Snow Land — Island\n({T}: Add {U}.)").toOption.map
    (fun c => c.isLand && c.hasSupertype .basic && c.hasSupertype .snow &&
      c.hasSubtype .island && c.activatedAbilities.isEmpty &&
      c.typeLine == "Basic Snow Land — Island") == some true
#guard (parseOracleCard "Glacier\n{1}{U}\nSnow Creature — Elemental\n1/1").toOption.map
    (fun c => c.hasSupertype .snow && c.hasSubtype .elemental &&
      c.power == some (.fixed 1) && c.toughness == some (.fixed 1)) == some true
#guard (parseOracleCard "The Abyss\nWorld Enchantment").toOption.map
    (fun c => c.hasSupertype .world && c.isEnchantment && c.subtypes.isEmpty) == some true
#guard (parseOracleCard "Urza's Ruinous Blast\n{4}{W}{W}\nLegendary Sorcery").toOption.map
    (fun c => c.hasSupertype .legendary && c.isSorcery && !c.isCreature) == some true
#guard (parseOracleCard "Advantageous Proclamation\nConspiracy").toOption.map
    (fun c => c.hasType .conspiracy) == some true
#guard (parseOracleCard "Bitterblossom\n{1}{B}\nKindred Enchantment — Faerie").toOption.map
    (fun c => c.hasType .kindred && c.isEnchantment && c.hasSubtype .faerie) == some true

#guard CardType.all.all fun t =>
  match parseOracleCard s!"Relic\n\{1}\nArtifact\n{t} spells you cast cost \{{3}} less to cast." with
  | .ok c => c.staticAbilities[0]? == some (.typeSpellsCostLess t 3)
  | .error _ => false
#guard Supertype.all.all fun s =>
  match parseOracleCard s!"Relic\n\{1}\nArtifact\n{s} spells you cast cost \{{2}} less to cast." with
  | .ok c => c.staticAbilities[0]? == some (.supertypeSpellsCostLess s 2)
  | .error _ => false
#guard Supertype.all.all fun s =>
  match parseOracleCard s!"Surge\n\{R}\nSorcery\n{s} spells you cast this turn cost \{{3}} less to cast." with
  | .ok c => c.spellEffect.map (·.body) ==
      some (.installEffect (.applyRule .untilEndOfTurn
        (.costMod (.spells .you (.hasSupertype s)) (.reduceGeneric (.const 3)))))
  | .error _ => false
#guard (parseOracleCard "Walk\n{G}\nInstant\nSnowcycling {2}").toOption.map
    (fun c =>
      c.keywords == #[.cycling (some (.hasSupertype .snow)) (CostSpec.ofMana (ManaCost.ofGeneric 2))] &&
      c.allActivatedAbilities[0]? ==
        some (Catalog.typecyclingAbility "Snow" (ManaCost.ofGeneric 2))) == some true
#guard (parseOracleCard "Walk\n{G}\nInstant\nBasic landcycling {2}").toOption.map
    (fun c =>
      c.keywords == #[.cycling (some (.all #[.hasSupertype .basic, .hasType .land])) (CostSpec.ofMana (ManaCost.ofGeneric 2))] &&
      c.allActivatedAbilities[0]? ==
        some (Catalog.typecyclingAbility "Basic land" (ManaCost.ofGeneric 2))) == some true
#guard (parseOracleCard "Helm\n{1}\nArtifact\nVillain spells you cast cost {1} less to cast.").toOption.bind
    (fun c => c.staticAbilities[0]?) == some (.subtypeSpellsCostLess .villain 1)
#guard (parseOracleCard "Surge\n{R}\nSorcery\nPlaneswalker spells you cast this turn cost {2} less to cast.").toOption.bind
    (fun c => c.spellEffect.map (·.body)) ==
    some (.installEffect (.applyRule .untilEndOfTurn
      (.costMod (.spells .you (.hasType .planeswalker)) (.reduceGeneric (.const 2)))))

#guard artifactTypes.all fun s =>
  (parseTypeLine s!"Artifact — {s}").toOption == some (#[], #[.artifact], #[s])
#guard enchantmentTypes.all fun s =>
  (parseTypeLine s!"Enchantment — {s}").toOption == some (#[], #[.enchantment], #[s])
#guard landTypes.all fun s =>
  (parseTypeLine s!"Land — {s}").toOption == some (#[], #[.land], #[s])
#guard planeswalkerTypes.all fun s =>
  (parseTypeLine s!"Planeswalker — {s}").toOption == some (#[], #[.planeswalker], #[s])
#guard spellTypes.all fun s =>
  (parseTypeLine s!"Instant — {s}").toOption == some (#[], #[.instant], #[s])
#guard creatureTypes.all fun s =>
  (parseTypeLine s!"Creature — {s}").toOption == some (#[], #[.creature], #[s])
#guard planarTypes.all fun s =>
  (parseTypeLine s!"Plane — {s}").toOption == some (#[], #[.plane], #[s])
#guard (parseTypeLine "Dungeon — Undercity").toOption ==
  some (#[], #[.dungeon], #["Undercity"])
#guard (parseTypeLine "Battle — Siege").toOption ==
  some (#[], #[.battle], #["Siege"])
#guard (parseTypeLine "Creature — Human Time Lord").toOption ==
  some (#[], #[.creature], #["Human", "Time Lord"])
#guard (parseTypeLine "Kindred Instant — Time Lord").toOption ==
  some (#[], #[.kindred, .instant], #["Time Lord"])
#guard (parseTypeLine "Land — Urza’s Mine").toOption ==
  some (#[], #[.land], #["Urza's", "Mine"])

#guard (parseOracleCard "Romana\n{2}{U}\nCreature — Time Lord\n1/1\nOther Time Lord creatures you control get +1/+1.").toOption.bind
    (fun c => c.subtypes == #["Time Lord"] &&
      c.staticAbilities[0]? == some (.otherCreaturesGet #[.timeLord] 1 1)) == some true
#guard (parseOracleCard "Pack\n{1}{G}\nCreature — Mouse\n1/1\nOther Mice and Time Lords you control have trample.").toOption.bind
    (fun c => c.staticAbilities[0]?) ==
    some (.otherCreaturesHaveTrample #[.mouse, .timeLord])
#guard (parseOracleCard "Worker\n{3}\nArtifact Creature — Assembly-Worker\n2/2\nAssembly-Workercycling {4}").toOption.map
    (fun c => c.subtypes == #["Assembly-Worker"] &&
      c.keywords == #[.cycling (some (.hasSubtype (.literal .assemblyWorker))) (CostSpec.ofMana (ManaCost.ofGeneric 4))] &&
      c.allActivatedAbilities[0]? ==
        some (Catalog.typecyclingAbility "Assembly-Worker" (ManaCost.ofGeneric 4))) == some true
#guard (parseOracleCard "Doctor\n{U}\nCreature — Time Lord Doctor\n1/1\nTime Lordcycling {2}").toOption.map
    (fun c => c.subtypes == #["Time Lord", "Doctor"] &&
      c.keywords == #[.cycling (some (.hasSubtype (.literal .timeLord))) (CostSpec.ofMana (ManaCost.ofGeneric 2))] &&
      c.allActivatedAbilities[0]? ==
        some (Catalog.typecyclingAbility "Time Lord" (ManaCost.ofGeneric 2))) == some true
#guard (parseOracleCard "Helm\n{1}\nArtifact\nC'tan spells you cast cost {1} less to cast.").toOption.bind
    (fun c => c.staticAbilities[0]?) == some (.subtypeSpellsCostLess .ctan 1)
#guard (parseOracleCard "Walk\n{G}\nSorcery\nSearch your library for a Power-Plant card, reveal it, put it into your hand, then shuffle.").toOption.bind
    (fun c => c.spellEffect) == some (Effect.searchLandTypeToHand "Power-Plant")
#guard (parseOracleCard "Walk\n{G}\nSorcery\nSearch your library for a Bolas's Meditation Realm card, reveal it, put it into your hand, then shuffle.").toOption.bind
    (fun c => c.spellEffect) == some (Effect.searchLandTypeToHand "Bolas's Meditation Realm")
#guard (parseOracleCard "Saga\n{2}\nEnchantment — Saga\nI — This Saga deals 3 damage to each non-Time Lord creature and each opponent.").toOption.bind
    (fun c => (c.sagaChapters[0]?).map (·.effect.body)) ==
    some (Effect.chapterDealDamageToEachNonSubtypeAndOpponents 3 "Time Lord").body

-- CR 207.2c: ability words are not rules text. The ability parses as if the
-- word were absent, including multi-word words and words inside a quote.
#guard abilityWords.all fun w =>
  (parseOracleCard s!"Walk\n\{G}\nSorcery\n{w} — Draw seven cards.").toOption.bind
      (·.spellEffect) ==
    (parseOracleCard "Walk\n{G}\nSorcery\nDraw seven cards.").toOption.bind
      (·.spellEffect)
#guard (parseOracleCard "Cloud\n{4}{B}\nSorcery\nSpell Mastery — This spell costs {3} less to cast if a creature died this turn.").toOption.map
    (fun c => c.staticAbilities.contains (.costReductionIfCreatureDied 3)) == some true
#guard (parseOracleCard "Cloud\n{4}{B}\nSorcery\nThis spell costs {3} less to cast if a creature died this turn.").toOption.map
    (fun c => c.staticAbilities.contains (.costReductionIfCreatureDied 3)) == some true
#guard (parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nWill of the Council — Menace").toOption.map
    (fun c => KeywordAbility.hasMenace c.keywords) == some true
#guard (parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nFathomless Descent — Flying (This creature can't be blocked except by creatures with flying or reach.)").toOption.map
    (fun c => KeywordAbility.hasFlying c.keywords && !KeywordAbility.hasReach c.keywords && c.staticAbilities.isEmpty) ==
    some true
#guard (parseOracleCard "Tale\n{2}\nEnchantment — Saga\nI — Spell Mastery — Draw seven cards.").toOption.map
    (fun c =>
      c.sagaChapters.size == 1 &&
        (c.sagaChapters[0]?).any (fun ch => ch.chapterNumbers? == some #[1] && ch.effect.body == Instruction.drawFixed 7)) == some true
#guard (parseOracleCard "Tale\n{2}\nEnchantment — Saga\nII — This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"").toOption.bind
    (fun c => (c.sagaChapters[0]?).map (·.effect.body)) ==
    some Effect.chapterGainLandfallCreateElf.body
#guard (parseOracleCard "Tale\n{2}\nEnchantment — Saga\nII — Council's Dilemma — This Saga gains \"Whenever a land you control enters, create a 1/1 green Elf creature token.\"").toOption.bind
    (fun c => (c.sagaChapters[0]?).map (·.effect.body)) ==
    some Effect.chapterGainLandfallCreateElf.body

-- CR 207.4: the chaos symbol is not rules text. Towashi's chaos ability is the
-- text after the symbol, and a `{CHAOS}` that names a planar-die face stays.
private def towashiChaosAbility : String :=
  "Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control."

#guard
  match parseOracleCard s!"Towashi\nPlane — Kamigawa\nMenace\n\{CHAOS} {towashiChaosAbility}",
        parseOracleCard s!"Towashi\nPlane — Kamigawa\nMenace\n{towashiChaosAbility}" with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false
#guard (parseOracleCard "Towashi\nPlane — Kamigawa\n{CHAOS} Menace").toOption.map
    (fun c => c.hasType .plane && c.subtypes == #["Kamigawa"] && KeywordAbility.hasMenace c.keywords) ==
    some true
#guard (parseOracleCard "Towashi\nPlane — Kamigawa\n{chaos}\nMenace").toOption.map
    (fun c => KeywordAbility.hasMenace c.keywords) == some true
#guard (parseOracleCard "Towashi\nPlane — Kamigawa\n{CHAOS} Draw seven cards.").toOption.bind
    (·.spellEffect) ==
  (parseOracleCard "Towashi\nPlane — Kamigawa\nDraw seven cards.").toOption.bind
    (·.spellEffect)
#guard
  match parseOracleCard "Roll\nInstant\nWhenever you roll {CHAOS}, draw a card." with
  | .error e => e == "unrecognized Oracle line on Roll: Whenever you roll {CHAOS}, draw a card."
  | .ok _ => false
#guard (parseOracleCard "Tale\n{2}\nEnchantment — Saga\nII — This Saga gains \"{CHAOS} Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"").toOption.bind
    (fun c => (c.sagaChapters[0]?).map (·.effect.body)) ==
    some Effect.chapterGainLandfallCreateElf.body

-- CR 207.2a: reminder text is not rules text, on the ability's line or its own line.
#guard (parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nMenace (This creature can't be blocked except by two or more creatures.)").toOption.map
    (fun c => KeywordAbility.hasMenace c.keywords && c.staticAbilities.isEmpty && !c.staticAbilities.contains .cantBeBlocked) ==
    some true
#guard (parseOracleCard "Bear\n{1}{G}\nCreature — Bear\n2/2\nMenace\n(This creature can't be blocked except by two or more creatures.)").toOption.map
    (fun c => KeywordAbility.hasMenace c.keywords && c.staticAbilities.isEmpty && c.triggeredAbilities.isEmpty) ==
    some true
#guard (parseOracleCard "Mage\n{U}\nCreature — Human Wizard\n1/1\nProwess\n(Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)").toOption.map
    (fun c => KeywordAbility.hasProwess c.keywords && c.triggeredAbilities.isEmpty && c.staticAbilities.isEmpty) ==
    some true
#guard (parseOracleCard "Elf\n{G}\nCreature — Elf Druid\n1/1\n({T}: Add {G}.)").toOption.map
    (fun c => c.activatedAbilities.isEmpty) ==
    some true
#guard (parseOracleCard "Elf\n{G}\nCreature — Elf Druid\n1/1\n{T}: Add {G}.").toOption.map
    (fun c => c.manaAbilities == #[.colored .green] && c.activatedAbilities.size == 1) == some true
#guard (parseOracleCard "Steam\nLand — Island Mountain\n({T}: Add {U} or {R}.)").toOption.map
    (fun c => c.activatedAbilities.isEmpty &&
      c.basicLandMana == #[.blue, .red]) == some true
#guard (parseOracleCard "Kick\n{1}{R}\nSorcery\nKicker {1}{R} (You may pay an additional {2}{G} as you cast this spell.)").toOption.map
    (fun c => c.kicker == some (ManaCost.ofGenericAndColor 1 .red)) == some true
#guard (parseOracleCard "Tale\n{2}\nEnchantment — Saga\n(As this Saga enters and after your draw step, add a lore counter. Sacrifice after I.)\nI — Draw seven cards.\nII — Draw seven cards.\nIII — Draw seven cards.").toOption.map
    (fun c =>
      c.sagaChapters.size == 3 && c.finalChapterNumber == 3 &&
        (c.triggeredAbilities.filter (!·.isSagaChapter)).isEmpty) == some true

-- CR 702.14: `keywordLineAbilities` delegates to `Parser.parseKeywordLine`, so
-- nonbasic, legendary, and snow landwalk parse and round-trip identically on the
-- catalog path, while non-land `*walk` stems are rejected.
#guard ["Nonbasic landwalk", "Legendary landwalk", "Snow landwalk", "Flying, legendary landwalk"].all fun line =>
  match parseOracleCard s!"Walker\n\{2}\{G}\nCreature — Elf\n2/2\n{line}" with
  | .ok c =>
    match parseOracleCard (renderFullOracle c) with
    | .ok d => d.keywords == c.keywords && Parser.parseKeywordLine line == some c.keywords
    | .error _ => false
  | .error _ => false
#guard
  match parseOracleCard "Walker\n{2}{U}\nCreature — Wizard\n2/2\nWizardwalk" with
  | .error _ => true
  | .ok _ => false

-- Phase 5: Compositional `parseManaSpec` / `parseManaProductionSpec` /
-- `parseManaAbilityLine` and unified `ActivatedAbility` Oracle round-trips
-- (CR 106.6 / 106.7 / 201.5c / 305.6 / 602 / 605.1a).
private def roundTripsOracleCard (raw : String) : Bool :=
  match parseOracleCard raw with
  | .ok c =>
    match parseOracleCard (renderFullOracle c) with
    | .ok d => d == c
    | .error _ => false
  | .error _ => false

#guard [
  "Llanowar Elves\n{G}\nCreature — Elf Druid\n1/1\n{T}: Add {G}.",
  "Birds of Paradise\n{G}\nCreature — Bird\n0/1\nFlying\n{T}: Add one mana of any color.",
  "Delighted Halfling\n{G}\nCreature — Halfling Citizen\n1/2\n{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a legendary spell, and that spell can't be countered.",
  "Reflecting Pool\nLand\n{T}: Add one mana of any type that a land you control could produce.",
  "Exotic Orchard\nLand\n{T}: Add one mana of any color that a land an opponent controls could produce.",
  "Command Tower\nLand\n{T}: Add one mana of any color in your commander's color identity.",
  "Mox Amber\n{0}\nLegendary Artifact\n{T}: Add one mana of any color among legendary creatures and planeswalkers you control.",
  "Fetid Heath\nLand\n{T}: Add {C}.\n{W/B}, {T}: Add {W}{W}, {W}{B}, or {B}{B}.",
  "Battlefield Forge\nLand\n{T}: Add {C}.\n{T}: Add {R} or {W}. Battlefield Forge deals 1 damage to you.",
  "Sol Ring\n{1}\nArtifact\n{T}: Add {C}{C}.",
  "Elvish Archdruid\n{1}{G}{G}\nCreature — Elf Druid\n2/2\nOther Elf creatures you control get +1/+1.\n{T}: Add {G} for each Elf you control.",
  "Doc Samson, Super Psychiatrist\n{2}{G}\nLegendary Creature — Human Scientist\n2/4\n{T}: Add X mana of any one color, where X is Doc Samson's power.",
  -- Novel compositional cards never printed in the catalog:
  "Hall of Velocity\nLand\n{T}: Add {G}. If that mana is spent on a creature spell, it gains haste.",
  "Anvil of Growth\nLand\n{T}: Add {C}. If that mana is spent on a creature spell, that creature enters with two additional +1/+1 counters on it.",
  "Twice-Clock Conduit\n{2}\nArtifact\n{T}: Add {U}. Activate no more than two times each turn.",
  "Exhausted Sprout\n{G}\nCreature — Plant\n0/2\nExhaust — {T}: Add {G}{G}."
].all roundTripsOracleCard

-- Verify AST structure of novel Phase 5 cards parsed via `parseOracleCard`.
#guard
  match parseOracleCard "Hall of Velocity\nLand\n{T}: Add {G}. If that mana is spent on a creature spell, it gains haste." with
  | .ok c =>
    c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.isManaAbility &&
      (c.activatedAbilities[0]!.manaProduction?.map (·.riders)) == some #[.gainsHaste]
  | .error _ => false
#guard
  match parseOracleCard "Anvil of Growth\nLand\n{T}: Add {C}. If that mana is spent on a creature spell, that creature enters with two additional +1/+1 counters on it." with
  | .ok c =>
    c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.isManaAbility &&
      (c.activatedAbilities[0]!.manaProduction?.map (·.riders)) == some #[.entersWithPlusOneCounters 2]
  | .error _ => false
#guard
  match parseOracleCard "Twice-Clock Conduit\n{2}\nArtifact\n{T}: Add {U}. Activate no more than two times each turn." with
  | .ok c =>
    c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.isManaAbility &&
      c.activatedAbilities[0]!.turnLimit? == some 2
  | .error _ => false
#guard
  match parseOracleCard "Exhausted Sprout\n{G}\nCreature — Plant\n0/2\nExhaust — {T}: Add {G}{G}." with
  | .ok c =>
    c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.isManaAbility &&
      c.activatedAbilities[0]!.isExhaust &&
      c.activatedAbilities[0]!.lifetimeLimit? == some 1
  | .error _ => false

-- Phase 6: Stratified 6-constructor `StaticAbility` (CR 113.3d / 303.4a / 601.2f /
-- 604 / 613 / 614–616), migrated keywords (`Improvise`, `Extort`, `Sneak`, `Boast`),
-- Stage-4 compositional static parsers, and Layer 3 `HasTextChange` functoriality.
#guard [
  -- Characteristic-defining abilities (CR 604.3)
  "Tarmogoyf\n{1}{G}\nCreature — Lhurgoyf\n*/1+*\nTarmogoyf's power is equal to the number of card types among cards in all graveyards and its toughness is equal to that number plus 1.",
  "Land Cultivator\n{3}{G}\nCreature — Elemental\n*/*\nLand Cultivator's power and toughness are each equal to the number of lands you control.",
  -- Continuous abilities (Layers 4–7d) including stack keyword grants
  "Time Weaver\n{2}{U}\nCreature — Wizard\n2/2\nInstant and sorcery spells you control have split second.",
  "Gearsmith\n{2}{U}\nCreature — Artificer\n2/3\nNoncreature spells you cast have improvise.",
  "Ward Guardian\n{3}{W}\nArtifact\nAs Ward Guardian enters, choose a card type.\nYou and creatures you control have protection from the chosen card type.",
  "Toxic Priest\n{1}{W}\nCreature — Cleric\n2/2\nCorrupted — As long as an opponent has three or more poison counters, creatures you control with toxic have lifelink.",
  -- Rule-modifying abilities (Player / Play / Combat / Game)
  "Platinum Guardian\n{7}\nArtifact Creature — Angel\n4/4\nFlying\nYou can't lose the game and your opponents can't win the game.",
  "Life Blocker\n{2}{R}\nEnchantment\nYour opponents can't gain life.",
  "Combat Silence\n{2}{U}{B}\nCreature — Ninja\n2/3\nDuring combat, players can't cast spells or activate abilities that aren't mana abilities.",
  "Elvish Explorer\n{2}{G}\nCreature — Elf Scout\n2/2\nYou may play an additional land on each of your turns as long as you control another Elf.",
  "Dragon Ambush\n{2}{R}\nCreature — Dragon\n3/2\nYou may cast this spell as though it had flash if you control a Dragon.",
  "Phantom Striker\n{1}{U}\nCreature — Spirit\n1/1\nThis creature can't be blocked.",
  -- Cost modifiers (CR 601.2f) including command-zone Eminence and first-creature
  "Sphinx Sovereign\n{4}{U}{U}\nLegendary Creature — Sphinx\n5/5\nFlying\nEminence — Other Sphinx spells you cast cost {1} less to cast as long as this creature is in the command zone or on the battlefield.",
  "Wilderness Guide\n{2}{G}\nCreature — Elf\n2/3\nThe first creature spell you cast each turn costs {1} less to cast and can be cast as though it had flash.",
  "Exile Scholar\n{2}{U}\nCreature — Wizard\n2/2\nSpells you cast from anywhere other than your hand cost {1} less to cast.",
  "Commander's Grace\n{2}{W}\nInstant\nIf you control a commander, you may cast this spell without paying its mana cost.\nDraw a card.",
  -- Replacements / ETB / as-enters (CR 614–615)
  "Shocking Ground\nLand\nThis land enters tapped unless you pay 2 life.\n{T}: Add {R}.",
  "Dragon Haven\nLand\nAs this land enters, you may behold a Dragon. If you don't, it enters tapped.\n{T}: Add {R}.",
  "Doubling Shrine\n{3}{W}\nEnchantment\nIf one or more tokens would be created under your control, twice that many of those tokens are created instead.",
  "Colorless Reservoir\n{2}\nArtifact\nIf you would lose unspent mana, that mana becomes colorless instead.",
  -- Aura enchant restrictions (CR 303.4a)
  "Relic Seal\n{1}{W}\nEnchantment — Aura\nEnchant artifact or non-Aura enchantment\nEnchanted permanent is a Construct creature with base power and toughness 5/5 in addition to its other types.",
  "Loyal Aura\n{1}{G}\nEnchantment — Aura\nEnchant creature you control\nEnchanted creature gets +2/+2.",
  -- Migrated keywords (Improvise / Extort / Sneak) & Zemo Boast
  "Clockwork Automaton\n{4}{U}\nArtifact Creature — Construct\n3/3\nImprovise",
  "Syndicate Tithe\n{1}{W}\nCreature — Human Cleric\n2/2\nExtort",
  "Shadow Infiltrator\n{3}{U}\nCreature — Ninja\n3/2\nSneak {1}{U}",
  "Baron Helmut Zemo\n{2}{B}\nLegendary Creature — Human Villain\n3/3\nBoast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs. (Activate only if this creature attacked this turn and only once each turn.)",
  -- Null Summoner graveyard-threshold exile-casting static (both "seven" and rendered "7"):
  "Null Summoner\n{1}{B}\nCreature — Human Wizard\n2/2\nAs long as there are seven or more cards in your graveyard, you may cast the exiled card, and mana of any type can be spent to cast that spell.",
  "Null Summoner Digit\n{1}{B}\nCreature — Human Wizard\n2/2\nAs long as there are 7 or more cards in your graveyard, you may cast the exiled card, and mana of any type can be spent to cast that spell.",
  -- Novel compositional static cards never printed in the catalog:
  "Archmage Tutor\n{2}{U}\nCreature — Human Wizard\n2/2\nOther Wizard creatures you control get +2/+1 and have vigilance and lifelink.",
  "Menacing Aura\n{1}{B}\nEnchantment — Aura\nEnchant creature\nEnchanted creature gets +3/+2 and has menace.",
  "Goblin Costcutter\n{1}{R}\nCreature — Goblin Shaman\n1/1\nGoblin spells you cast cost {2} less to cast.",
  "Dampening Arbiter\n{2}{W}\nCreature — Human Advisor\n2/3\nNoncreature spells your opponents cast cost {2} more to cast.",
  "Dragonkin Warden\n{2}{R}\nCreature — Human Warrior\n2/2\nAs long as you control a Dragon, this creature gets +3/+3 and has flying and trample.",
  "Tripling Procession\n{4}{W}\nEnchantment\nIf one or more tokens would be created under your control, three times that many of those tokens are created instead.",
  "Ward of Permanence\n{1}{W}\nEnchantment — Aura\nEnchant nonland permanent\nEnchanted permanent has hexproof.",
  "Total Power Avatar\n{3}{G}\nCreature — Avatar\n*/2\nTotal Power Avatar's power is equal to the total power of creatures you control.",
  "Greatest Power Avatar\n{3}{G}\nCreature — Avatar\n*/2\nGreatest Power Avatar's power is equal to the greatest power among creatures you control.",
  "Mourning Banner\n{2}{B}\nEnchantment\nAs long as a creature died last turn, creatures you control get +1/+1.",
  "Soul Chorus\n{2}{W}\nEnchantment\nAs long as you gained life this turn, creatures you control get +1/+1.",
  "Sky Power Avatar\n{3}{U}\nCreature — Avatar\n*/2\nSky Power Avatar's power is equal to the total power of creatures you control with flying.",
  "Grounded Sanctuary\n{2}{G}\nEnchantment\nCreatures you control without flying get +1/+1 and have hexproof.",
  "Skywatch Banner\n{2}{W}\nEnchantment\nAs long as you control a creature with flying, creatures you control get +1/+1 and have vigilance.",
  "Defender's Anthem\n{2}{W}\nEnchantment\nCreatures the defending player controls get +1/+1.",
  "Defending Life Avatar\n{4}{B}\nCreature — Avatar\n*/2\nDefending Life Avatar's power is equal to the defending player's life total."
].all roundTripsOracleCard

-- Verify exact AST structure of migrated keywords, Zemo Boast, and novel Phase 6 cards.
#guard
  match parseOracleCard "Clockwork Automaton\n{4}{U}\nArtifact Creature — Construct\n3/3\nImprovise" with
  | .ok c => c.keywords == #[.simple .improvise] && c.staticAbilities.isEmpty
  | .error _ => false
#guard
  match parseOracleCard "Syndicate Tithe\n{1}{W}\nCreature — Human Cleric\n2/2\nExtort" with
  | .ok c => c.keywords == #[.simple .extort] && c.staticAbilities.isEmpty
  | .error _ => false
#guard
  match parseOracleCard "Shadow Infiltrator\n{3}{U}\nCreature — Ninja\n3/2\nSneak {1}{U}" with
  | .ok c => c.keywords == #[.sneak (CostSpec.ofMana (ManaCost.ofGenericAndColor 1 .blue))] &&
      c.staticAbilities.isEmpty
  | .error _ => false
#guard
  match parseOracleCard "Baron Helmut Zemo\n{2}{B}\nLegendary Creature — Human Villain\n3/3\nBoast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs." with
  | .ok c => c.activatedAbilities == #[ActivatedAbility.zemoBoastAbility] &&
      c.activatedAbilities[0]!.isBoast && c.staticAbilities.isEmpty
  | .error _ => false
#guard
  match parseOracleCard "Archmage Tutor\n{2}{U}\nCreature — Human Wizard\n2/2\nOther Wizard creatures you control get +2/+1 and have vigilance and lifelink." with
  | .ok c =>
    match c.staticAbilities with
    | #[.continuous none _ (.all #[.modifyPT (.const 2) (.const 1), .grantKeywords kws])] =>
      kws == #[Keyword.vigilance, Keyword.lifelink]
    | _ => false
  | .error _ => false
#guard
  match parseOracleCard "Goblin Costcutter\n{1}{R}\nCreature — Goblin Shaman\n1/1\nGoblin spells you cast cost {2} less to cast." with
  | .ok c =>
    c.staticAbilities == #[StaticAbility.subtypeSpellsCostLess .goblin 2]
  | .error _ => false
#guard
  match parseOracleCard "Dampening Arbiter\n{2}{W}\nCreature — Human Advisor\n2/3\nNoncreature spells your opponents cast cost {2} more to cast." with
  | .ok c =>
    c.staticAbilities == #[StaticAbility.opponentsNoncreatureSpellsCostMore 2]
  | .error _ => false
#guard
  match parseOracleCard "Dragonkin Warden\n{2}{R}\nCreature — Human Warrior\n2/2\nAs long as you control a Dragon, this creature gets +3/+3 and has flying and trample." with
  | .ok c =>
    c.staticAbilities == #[
      .continuous (some (StaticAbility.condControlSubtype .dragon)) StaticAbility.scopeSelf
        (.all #[.modifyPT (.const 3) (.const 3), .grantKeywords #[Keyword.flying, Keyword.trample]])
    ]
  | .error _ => false
#guard
  match parseOracleCard "Tripling Procession\n{4}{W}\nEnchantment\nIf one or more tokens would be created under your control, three times that many of those tokens are created instead." with
  | .ok c =>
    c.staticAbilities == #[.replacement none (.multiplyTokens .you 3)]
  | .error _ => false
#guard
  match parseOracleCard "Ward of Permanence\n{1}{W}\nEnchantment — Aura\nEnchant nonland permanent\nEnchanted permanent has hexproof." with
  | .ok c =>
    c.staticAbilities.size == 2 &&
      (c.staticAbilities[0]!.enchantRestriction?.isSome) &&
      c.staticAbilities[1]! ==
        .continuous none StaticAbility.scopeEnchantedPermanent (.grantKeywords #[Keyword.hexproof])
  | .error _ => false

-- Functorial Layer 3 `HasTextChange` on parsed stratified `StaticAbility` ASTs:
-- replacing `.goblin` → `.elf` and `.dragon` → `.sphinx` rewrites scopes, conditions,
-- cost targets, and replacements structurally.
#guard
  let tc : Array TextChange := #[.replaceCreatureType .goblin .elf]
  HasTextChange.applyTextChanges tc (StaticAbility.subtypeSpellsCostLess .goblin 2) ==
    StaticAbility.subtypeSpellsCostLess .elf 2 &&
  HasTextChange.applyTextChanges tc (StaticAbility.eminenceSubtypeSpellsCostLess .goblin 1) ==
    StaticAbility.eminenceSubtypeSpellsCostLess .elf 1 &&
  HasTextChange.applyTextChanges #[.replaceCreatureType .dragon .sphinx]
      (StaticAbility.entersTappedUnlessBehold .dragon) ==
    StaticAbility.entersTappedUnlessBehold .sphinx &&
  HasTextChange.applyTextChanges #[.replaceCreatureType .army .goblin]
      StaticAbility.armiesYouControlHaveTrample ==
    .continuous none (StaticAbility.scopeCreaturesOfSubtypeYouControl .goblin)
      (.grantKeywords #[Keyword.trample])

-- Phase 7: Unified `TriggerPattern`, Saga chapters in `triggeredAbilities`,
-- per-trigger `ModalSpec` modes, Path of Ancestry `isManaSpentCastScry`,
-- and novel compositional triggered abilities parsed by `Parser.parseNovelTriggeredAbilityLine`.
#guard [
  -- Novel compositional triggers never printed in the catalog:
  "Tap Scribe\n{1}{U}\nEnchantment\nWhenever a Wizard creature you control becomes tapped, you gain 2 life.",
  "Arcane Rebuke\n{2}{U}\nEnchantment\nWhenever a spell you control is countered, draw a card.",
  "Monarch's Goblin Shrine\n{2}{R}\nEnchantment\nWhenever a Goblin creature you control dies, if you're the monarch, you gain 3 life.",
  "Elven Watchtower\n{1}{G}\nEnchantment\nWhenever an Elf creature you control enters, scry 1. This ability triggers only once each turn.",
  -- Multi-chapter Saga round-trip (`I, II — ...` + `III — ...`):
  "Song of the Shire\n{2}{G}\nEnchantment — Saga\nI, II — Scry 1.\nIII — Draw two cards.",
  -- Path of Ancestry round-trip via `triggeredAbilities`:
  "Ancestral Path\nLand\nThis land enters tapped.\n{T}: Add one mana of any color in your commander's color identity. When that mana is spent to cast a creature spell that shares a creature type with your commander, scry 1."
].all roundTripsOracleCard

-- Saga chapters live directly in `triggeredAbilities` with `BatchGrouping.counterThreshold .lore`.
#guard
  match parseOracleCard "Song of the Shire\n{2}{G}\nEnchantment — Saga\nI, II — Scry 1.\nIII — Draw two cards." with
  | .ok c =>
    c.sagaChapters.size == 2 &&
      c.finalChapterNumber == 3 &&
      c.sagaChapters[0]!.chapterNumbers? == some #[1, 2] &&
      c.sagaChapters[1]!.chapterNumbers? == some #[3]
  | .error _ => false

-- Path of Ancestry parses onto `triggeredAbilities` (`isManaSpentCastScry == true`).
#guard
  match parseOracleCard "Ancestral Path\nLand\nThis land enters tapped.\n{T}: Add one mana of any color in your commander's color identity. When that mana is spent to cast a creature spell that shares a creature type with your commander, scry 1." with
  | .ok c =>
    c.triggeredAbilities.any (·.isManaSpentCastScry)
  | .error _ => false

-- Two distinct modal triggers on one card parse into independent `Instruction.chooseModes` arrays.
#guard
  match parseOracleCard
      ("Dual Modal Oracle\n{3}{U}\nCreature — Sphinx\n3/3\n" ++
        "When this creature enters, choose one —\n" ++
        "• You gain 2 life.\n" ++
        "• Draw a card.\n" ++
        "When this creature dies, choose one —\n" ++
        "• Scry 2.\n" ++
        "• Each opponent loses 2 life.") with
  | .ok c =>
    c.triggeredAbilities.size == 2 &&
      c.triggeredAbilities[0]!.pattern == .thisEnters &&
      c.triggeredAbilities[0]!.modeEffects.size == 2 &&
      c.triggeredAbilities[1]!.pattern == .thisDies &&
      c.triggeredAbilities[1]!.modeEffects.size == 2 &&
      c.triggeredAbilities[0]!.modeEffects != c.triggeredAbilities[1]!.modeEffects
  | .error _ => false

-- Novel compositional trigger ASTs: CR 603.10e look-back, CR 603.4 `interveningIf?`,
-- CR 603.2 `.whenCond`, `TriggerLimit.onceEachTurn`, and Layer 3 `HasTextChange`.
#guard
  match parseOracleCard "Arcane Rebuke\n{2}{U}\nEnchantment\nWhenever a spell you control is countered, draw a card." with
  | .ok c =>
    match c.triggeredAbilities with
    | #[ab] => ab.pattern.usesLookBack && ab.effect.body == Instruction.drawFixed 1
    | _ => false
  | .error _ => false
#guard
  match parseOracleCard "Monarch's Goblin Shrine\n{2}{R}\nEnchantment\nWhenever a Goblin creature you control dies, if you're the monarch, you gain 3 life." with
  | .ok c =>
    match c.triggeredAbilities with
    | #[ab] =>
      ab.pattern.usesLookBack &&
        ab.interveningIf? == some TriggeredAbility.condYouAreMonarch &&
        ab.effect.body == Instruction.gainLifeFixed 3
    | _ => false
  | .error _ => false
#guard
  match parseOracleCard "Elven Watchtower\n{1}{G}\nEnchantment\nWhenever an Elf creature you control enters, scry 1. This ability triggers only once each turn." with
  | .ok c =>
    match c.triggeredAbilities with
    | #[ab] =>
      !ab.pattern.usesLookBack &&
        ab.limit == .onceEachTurn &&
        ab.effect.body == Instruction.scryFixed 1 &&
        HasTextChange.applyTextChanges #[.replaceCreatureType .elf .goblin] ab.pattern ==
          TriggerPattern.permanentEnters (.all #[.hasSubtype (.literal .goblin), .hasType .creature, .controlledBy .you])
    | _ => false
  | .error _ => false
#guard
  match Parser.parseTriggerClause "Whenever this creature attacks while you're the monarch, you gain 2 life." "Test",
        Parser.parseTriggerClause "Whenever this creature attacks, if you're the monarch, you gain 2 life." "Test" with
  | some hWhile, some hIf =>
    (match hWhile.pattern with | .whenCond .thisAttacks _ => true | _ => false) &&
      hWhile.interveningIf?.isNone &&
      hIf.pattern == .thisAttacks &&
      hIf.interveningIf? == some TriggeredAbility.condYouAreMonarch
  | _, _ => false

-- Self-spell countered triggers activate from the stack (CR 603.10e / 113.6) and round-trip.
#guard
  match parseOracleCard "Unstoppable Insight\n{2}{U}\nSorcery\nDraw two cards.\nWhen this spell is countered, draw a card." with
  | .ok c =>
    match c.triggeredAbilities with
    | #[ab] =>
      ab.pattern == .spellCountered (.sameAs .this) &&
        ab.activeZones == #[.stack] &&
        ab.effect.body == Instruction.drawFixed 1 &&
        match parseOracleCard (renderFullOracle c) with
        | .ok c2 => c2 == c
        | .error _ => false
    | _ => false
  | .error _ => false

-- `while <cond>` over compound `"enters or attacks"` distributes `.whenCond` over `.or`.
#guard
  match parseOracleCard "Arcane Raider\n{2}{U}\nCreature — Human\n2/2\nWhenever this creature enters or attacks while you control a Wizard, draw a card." with
  | .ok c =>
    match c.triggeredAbilities with
    | #[ab] =>
      let disjs := ab.pattern.flattenDisjuncts
      disjs.size == 2 &&
        disjs[0]!.1 == .thisEnters && disjs[0]!.2.size == 1 &&
        disjs[1]!.1 == .thisAttacks && disjs[1]!.2.size == 1
    | _ => false
  | .error _ => false

-- Heterogeneous `"and when/whenever"` clauses split into independent abilities preserving
-- each clause's own `BatchGrouping`, `TriggerLimit`, and `activeZones`; homogeneous clauses
-- merge into one `.or` ability; heterogeneous clauses with a shared `onceEachTurn` cap are rejected.
#guard
  let hetGroupOk :=
    match parseOracleCard "Split Group\n{2}{G}\nEnchantment\nWhenever a creature enters and whenever one or more creatures die, draw a card." with
    | .ok c =>
      match c.triggeredAbilities with
      | #[a, b] => a.grouping == .perOccurrence && b.grouping == .oncePerBatch
      | _ => false
    | .error _ => false
  let hetLimitOk :=
    match parseOracleCard "Split Limit\n{2}{U}\nEnchantment\nWhenever a creature dies and whenever you draw your second card each turn, you gain 1 life." with
    | .ok c =>
      match c.triggeredAbilities with
      | #[a, b] => a.limit == .unlimited && b.limit == .nthEachTurn 2
      | _ => false
    | .error _ => false
  let hetZonesOk :=
    match parseOracleCard "Split Zones\n{2}{U}\nEnchantment\nWhen this spell is countered and whenever you draw a card, you gain 1 life." with
    | .ok c =>
      match c.triggeredAbilities with
      | #[a, b] =>
        a.word == .when && a.activeZones == #[.stack] &&
          b.word == .whenever && b.activeZones == #[.battlefield]
      | _ => false
    | .error _ => false
  let hetOnceRejected :=
    match parseOracleCard "Bad Shared Cap\n{2}{G}\nEnchantment\nWhenever a creature enters and whenever one or more creatures die, draw a card. This ability triggers only once each turn." with
    | .error _ => true
    | .ok _ => false
  let homMergedOk :=
    match parseOracleCard "Combat Mirror\n{2}{R}\nEnchantment\nWhenever one or more creatures you control deal combat damage to a player and whenever one or more creatures an opponent controls deal combat damage to a player, you gain 1 life." with
    | .ok c =>
      match c.triggeredAbilities with
      | #[ab] =>
        ab.grouping == .perPlayerInBatch &&
          (match ab.pattern with | .or _ _ => true | _ => false)
      | _ => false
    | .error _ => false
  hetGroupOk && hetLimitOk && hetZonesOk && hetOnceRejected && homMergedOk

-- Phase 8: Stage-4 compositional `Parser.parseInstructionEffect`, unified `ModalSpec`
-- (`Choose one or both`, teamwork `altCountIf?`, subtype `altCountIf?`), and folded
-- `"Empower Jace"` round-trip checks.
#guard
  (Parser.parseInstructionEffect "Draw two cards, then scry 1.").isSome &&
  (Parser.parseInstructionEffect "Destroy target creature. You gain 2 life.").isSome &&
  (Parser.parseInstructionEffect "Choose one or both — • Draw a card. • Each opponent loses 2 life.").isSome &&
  (Parser.parseInstructionEffect "You may pay {2}. If you do, draw two cards.").isSome

#guard [
  "Jace's Bolt\n{1}{R}\nSorcery\nJace's Bolt deals 2 damage to target creature. Empower Jace 3.",
  "Twin Boon\n{1}{W}\nSorcery\nChoose one or both —\n• Draw a card.\n• You gain 3 life.",
  "Teamwork Tactics\n{2}{U}\nSorcery\nTeamwork 2 (As you cast this spell, you may tap any number of untapped creatures you control with total power 2 or greater.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Draw a card.\n• You gain 2 life.",
  "Elf Boon\n{1}{G}\nSorcery\nChoose one. If you control an Elf, you may choose two instead.\n• Draw a card.\n• You gain 2 life."
].all roundTripsOracleCard

#guard
  let empowerOk :=
    match parseOracleCard "Jace's Bolt\n{1}{R}\nSorcery\nJace's Bolt deals 2 damage to target creature. Empower Jace 3." with
    | .ok c => c.empowerPlaneswalkerAmount? == some 3
    | .error _ => false
  let bothOk :=
    match parseOracleCard "Twin Boon\n{1}{W}\nSorcery\nChoose one or both —\n• Draw a card.\n• You gain 3 life." with
    | .ok c =>
      c.modalSpec?.any fun (ms : ModalSpec) =>
        ms.minModes == ValueExpr.const 1 && ms.maxModes == ValueExpr.const 2 && ms.modes.size == 2
    | .error _ => false
  let teamworkOk :=
    match parseOracleCard
        ("Teamwork Tactics\n{2}{U}\nSorcery\n" ++
          "Teamwork 2 (As you cast this spell, you may tap any number of untapped creatures you control with total power 2 or greater.)\n" ++
          "Choose one. If this spell was cast using teamwork, choose both instead.\n" ++
          "• Draw a card.\n• You gain 2 life.") with
    | .ok c =>
      c.modalSpec?.any fun (ms : ModalSpec) =>
        match ms.altCountIf? with
        | some (.castPred (.teamworkPaid .this), .const 2, .const 2) => ms.modes.size == 2
        | _ => false
    | .error _ => false
  let subtypeOk :=
    match parseOracleCard
        ("Elf Boon\n{1}{G}\nSorcery\n" ++
          "Choose one. If you control an Elf, you may choose two instead.\n" ++
          "• Draw a card.\n• You gain 2 life.") with
    | .ok c =>
      c.modalSpec?.any fun (ms : ModalSpec) =>
        ms.altCountIf?.isSome && ms.modes.size == 2
    | .error _ => false
  empowerOk && bothOk && teamworkOk && subtypeOk

-- Phase 10: Slim 21-field `CardDef`, `PrintedStat` (CR 208.1-2), `DeckLimit` (CR 100.2a),
-- unified `SubFace` (CR 715 Adventure / Prepare), `SpellAbility` functorial `HasTextChange`,
-- structural `BEq CardDef`, pure `Effect.targetPreference`, and canonical `ToOracle` regressions.
#guard
  let statOk :=
    PrintedStat.fixed 3 != PrintedStat.star 3 &&
    (PrintedStat.star 0).undeterminedValue == 0 &&
    (PrintedStat.star 1).undeterminedValue == 1 &&
    (PrintedStat.star 0).toOracleStr == "*" &&
    (PrintedStat.star 2).toOracleStr == "2+*" &&
    (PrintedStat.fixed (-1)).toOracleStr == "-1"
  let deckOk :=
    DeckLimit.unlimited.toOracleLine "Nazgûl" ==
      "A deck can have any number of cards named Nazgûl." &&
    (DeckLimit.maxCopies 9).toOracleLine "Nazgûl" ==
      "A deck can have up to 9 cards named Nazgûl."
  let sa : SpellAbility := {
    effect := Effect.draw 1
    additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.beholdOrPayGeneric .goblin 2)]
  }
  let saTc := HasTextChange.applyTextChanges #[.replaceCreatureType .goblin .elf] sa
  let saOk :=
    saTc.additionalCosts == #[AdditionalCostSpec.mandatory (CostSpec.beholdOrPayGeneric .elf 2)] &&
    saTc != sa
  let prefOk :=
    (Effect.pump 2 2).targetPreference == .own &&
    Effect.destroyCreature.targetPreference == .opponent &&
    (Effect.abilityTargetPlayerDraw 2).targetPreference == .selfPlayer
  let baseFace : CardDef := { name := "Front", types := #[.creature], power := some (.fixed 2), toughness := some (.fixed 2) }
  let backA : CardDef := { name := "BackA", types := #[.creature], power := some (.star 0), toughness := some (.star 0) }
  let backB : CardDef := { name := "BackB", types := #[.creature], power := some (.star 1), toughness := some (.star 1) }
  let beqOk :=
    ({ baseFace with otherFace := some backA } == { baseFace with otherFace := some backA }) &&
    ({ baseFace with otherFace := some backA } != { baseFace with otherFace := some backB }) &&
    ({ baseFace with deckLimitOverride := some .unlimited } != { baseFace with deckLimitOverride := some (.maxCopies 7) })
  statOk && deckOk && saOk && prefOk && beqOk

#guard [
  "Murmuring Volume\n{3}\nArtifact — Book\n{T}: Add one mana of any color.\n{2}, {T}, Discard a card: Draw a card.",
  "Jace, Reality Sculptor\n{3}{U}{U}\nLegendary Planeswalker — Jace\n+1: Empower Jace X, where X is the number of Islands you control.\n−3: Until your next turn, whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn.\n0: Exile all but the bottom card of each opponent's library. Activate only if there are twenty-five or more loyalty counters among Jaces you control.\nLoyalty: 5",
  "Way of the Deathbringer\n{2}{B}\nLegendary Enchantment\nWhen Way of the Deathbringer enters, empower Jace 5.\nPlaneswalkers you control have \"[−2]: You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample.\"",
  "My Precious\n{3}\nLegendary Artifact — Equipment\nEquipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life.\n//ADV//\nAllure of Power\n{1}{B}\nInstant — Adventure\nAs an additional cost to cast this spell, sacrifice a creature.\nDraw two cards.",
  "Five Relics\n{2}\nArtifact\nA deck can have up to five cards named Five Relics.",
  "Seven Dwarves\n{1}{R}\nCreature — Dwarf\n2/2\nA deck can have up to seven cards named Seven Dwarves.",
  "Nazgûl\n{2}{B}\nCreature — Wraith Knight\n1/2\nDeathtouch\nA deck can have up to 9 cards named Nazgûl."
].all roundTripsOracleCard

#guard
  let volumeOk :=
    match parseOracleCard
        "Murmuring Volume\n{3}\nArtifact — Book\n{T}: Add one mana of any color.\n{2}, {T}, Discard a card: Draw a card." with
    | .ok c =>
      c.activatedAbilities.size == 2 &&
      c.activatedAbilities[1]!.cost.items.any (fun | .discard _ .hand => true | _ => false) &&
      c.activatedAbilities[1]!.toNotation == "{2}, {T}, Discard a card: Draw a card."
    | .error _ => false
  let jaceOk :=
    match parseOracleCard
        ("Jace, Reality Sculptor\n{3}{U}{U}\nLegendary Planeswalker — Jace\n" ++
          "0: Exile all but the bottom card of each opponent's library. Activate only if there are twenty-five or more loyalty counters among Jaces you control.\n" ++
          "Loyalty: 5") with
    | .ok c =>
      c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.toNotation.contains "Exile all but the bottom card of each opponent's library."
    | .error _ => false
  let wayOk :=
    match parseOracleCard
        ("Way of the Deathbringer\n{2}{B}\nLegendary Enchantment\n" ++
          "Planeswalkers you control have \"[−2]: You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample.\"") with
    | .ok c =>
      match (c.staticAbilities[0]? : Option StaticAbility) with
      | some (.continuous _ _ (.grantActivated abs)) =>
        abs.size == 1 && abs[0]!.toNotation.contains "You may sacrifice a creature."
      | _ => false
    | .error _ => false
  let maxCopiesOk :=
    (parseOracleCard "Five Relics\n{2}\nArtifact\nA deck can have up to five cards named Five Relics.").toOption.map
      (·.deckLimitOverride) == some (some (.maxCopies 5)) &&
    (parseOracleCard "Seven Dwarves\n{1}{R}\nCreature — Dwarf\n2/2\nA deck can have up to seven cards named Seven Dwarves.").toOption.map
      (·.deckLimitOverride) == some (some (.maxCopies 7)) &&
    (parseOracleCard "Nazgûl\n{2}{B}\nCreature — Wraith Knight\n1/2\nDeathtouch\nA deck can have up to 9 cards named Nazgûl.").toOption.map
      (·.deckLimitOverride) == some (some (.maxCopies 9))
  volumeOk && jaceOk && wayOk && maxCopiesOk

-- Preserved regression `#guard`s migrated from legacy `ParseOracle.lean`:
#guard
  match parseOracleCard
      "Snack\n{B}\nSorcery\nPut a stun counter on up to one target creature. Target player gains 2 life." with
  | .ok c =>
    match c.spellEffect with
    | some e => e.body == (Effect.plusOneUpToOneAndPlayerGainsLife 2 .stun).body
    | none => false
  | .error _ => false

#guard
  match parseOracleCard
      "Snack\n{B}\nSorcery\nPut two first strike counters on up to one target creature. Target player gains 3 life." with
  | .ok c =>
    match c.spellEffect with
    | some e =>
      e.body == (Effect.plusOneUpToOneAndPlayerGainsLife 3 .firstStrike 2).body
    | none => false
  | .error _ => false

#guard
  match parseOracleCard
      "Tidings of War\n{R}\nSorcery\nAmass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead. (To amass Goblins X, put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nFlashback {3}{R} (You may cast this card from your graveyard for its flashback cost. Then exile it.)" with
  | .ok c =>
    c.flashback == some (ManaCost.ofGenericAndColor 3 .red) &&
      match c.spellEffect with
      | some e => e == Effect.amassGoblinsOrFromGy 1 3
      | none => false
  | .error _ => false

-- Phase 11: Full 981-card catalog structural `BEq CardDef` round-trip verification
-- (explicitly including `Catalog.realityFractureCommanderCards` and all 5 supported sets).
#guard supportedCatalogCards.size == 981
#guard !Catalog.realityFractureCommanderCards.isEmpty &&
  Catalog.realityFractureCommanderCards.all fun c =>
    (parseOracleCard (renderFullOracle c)).toOption == some c
#guard supportedCatalogCards.all fun c =>
  (parseOracleCard (renderFullOracle c)).toOption == some c

-- Phase 11: Open-ended compositional parser `#guard` tests across novel unseen
-- combinations of triggers, conditions, targets, instructions, recursive quoted
-- abilities, Equip/Cycling keyword expansion, CR 611.2a durations, and CR 608.2g
-- immediate cast permissions.
#guard [
  -- Novel cross-product trigger + condition + target + multi-sentence discourse:
  "Frostblade Sentinel\n{2}{U}{W}\nCreature — Elf Knight\n3/3\nWhenever an artifact you control enters, if you control a Plains, tap target creature an opponent controls and put a stun counter on it. Draw a card.",
  -- Novel trigger + optional cost + reflexive trigger (CR 603.12):
  "Cinder Archivist\n{1}{R}\nCreature — Dwarf Wizard\n2/1\nWhenever another creature you control dies, you may pay {1}{R}. When you do, exile target card from a graveyard and draw a card.",
  -- Novel CR 614.6 post-replacement discourse binding (`this way` / `that many`):
  "Ashen Reckoning\n{3}{B}{B}\nSorcery\nDestroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way.",
  -- Novel CR 611.2a indefinite continuous modification vs. EOT pump:
  "Eternal Wingcraft\n{2}{W}\nSorcery\nTarget creature you control gains flying and vigilance.",
  "Fleet Blessing\n{1}{W}\nInstant\nTarget creature you control gets +2/+2 and gains flying and lifelink until end of turn.",
  -- Novel recursive quoted `"..."` ability granted by a static ability:
  "Runic Forge\n{3}\nArtifact\nOther artifacts you control have \"{T}: Add {C}.\"",
  -- Novel Equip + Cycling unified onto `CardDef.keywords` + `allActivatedAbilities`:
  "Skyrunner Blade\n{2}\nArtifact — Equipment\nEquipped creature gets +2/+1 and has flying.\nEquip Elf {1}\nIslandcycling {2}",
  -- Novel multi-mode spell combining unseen modes + static cost modifier:
  "Arcane Synthesis\n{3}{U}\nInstant\nThis spell costs {1} less to cast if you control a Wizard.\nChoose one —\n• Scry 3, then draw a card.\n• Counter target noncreature spell.\n• Return target creature an opponent controls to its owner's hand."
].all roundTripsOracleCard

#guard
  -- Verify Equip & Typecycling live on `keywords` and expand into `allActivatedAbilities`:
  let eqCycOk :=
    match parseOracleCard
        "Skyrunner Blade\n{2}\nArtifact — Equipment\nEquipped creature gets +2/+1 and has flying.\nEquip Elf {1}\nIslandcycling {2}" with
    | .ok c =>
      c.activatedAbilities.isEmpty &&
      c.keywords.size == 2 &&
      c.allActivatedAbilities.size == 2 &&
      c.allActivatedAbilities.any (·.isEquip) &&
      c.allActivatedAbilities.any (·.isCycling)
    | .error _ => false
  -- Verify CR 611.2a indefinite duration (no `"until end of turn"`) vs. EOT duration:
  let durOk :=
    let indefOk :=
      match parseOracleCard "Eternal Wingcraft\n{2}{W}\nSorcery\nTarget creature you control gains flying and vigilance." with
      | .ok c =>
        match (c.spellEffect.map (·.body) : Option Instruction) with
        | some (.installEffect (.applyContinuous .indefinite (.target 0) (.grantKeywords ks))) =>
          ks == #[Keyword.vigilance, Keyword.flying]
        | _ => false
      | .error _ => false
    let eotOk :=
      match parseOracleCard "Fleet Blessing\n{1}{W}\nInstant\nTarget creature you control gets +2/+2 and gains flying and lifelink until end of turn." with
      | .ok c =>
        match (c.spellEffect.map (·.body) : Option Instruction) with
        | some (.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.all _))) => true
        | _ => false
      | .error _ => false
    indefOk && eotOk
  -- Verify CR 608.2g immediate `castNow := true` when no duration is stated vs. `castNow := false` when timed:
  let castNowOk :=
    let nowOk :=
      match parseOracleCard "Spontaneous Spark\n{2}{R}\nSorcery\nExile the top card of your library. You may cast it without paying its mana cost." with
      | .ok c =>
        match (c.spellEffect.map (·.body) : Option Instruction) with
        | some (.moveZone _ .exile .exile { grantPlayPerm? := some gpp, .. }) => gpp.castNow && gpp.freeCast
        | some (.bind _ _ (.stack (.mayCastOrPlay _ gpp))) => gpp.castNow && gpp.freeCast
        | _ => false
      | .error _ => false
    let timedOk :=
      match parseOracleCard "Measured Spark\n{1}{R}\nSorcery\nExile the top card of your library. Until end of turn, you may play it." with
      | .ok c =>
        match (c.spellEffect.map (·.body) : Option Instruction) with
        | some (.moveZone _ .exile .exile { grantPlayPerm? := some gpp, .. }) =>
          !gpp.castNow && gpp.duration == .untilEndOfTurn && gpp.landsAllowed
        | some (.bind _ _ (.stack (.mayCastOrPlay _ gpp))) =>
          !gpp.castNow && gpp.duration == .untilEndOfTurn && gpp.landsAllowed
        | _ => false
      | .error _ => false
    nowOk && timedOk
  -- Verify recursive quoted activated ability inside static grant:
  let quotedOk :=
    match parseOracleCard "Runic Forge\n{3}\nArtifact\nOther artifacts you control have \"{T}: Add {C}.\"" with
    | .ok c =>
      match (c.staticAbilities[0]? : Option StaticAbility) with
      | some (.continuous none _ (.grantActivated abs)) =>
        abs.size == 1 && abs[0]!.isManaAbility
      | _ => false
    | .error _ => false
  eqCycOk && durOk && castNowOk && quotedOk

-- Phase 11: Stage 1–5 unit & semantic-regression `#guard` coverage.
-- Stage 1 (`FrameSplit`): mana costs, type lines, P/T `PrintedStat`, color indicators, sub-faces, loyalty/defense.
#guard parseManaCost "{2}{W/U}{2/B}{X}{C}" == some { symbols := #[.generic 2, .hybrid .white .blue, .twobrid .black, .x, .colorless] }
#guard parsePT "3/4" == some (.fixed 3, .fixed 4)
#guard parsePT "*/*" == some (.star 0, .star 0)
#guard parsePT "1+*/2+*" == some (.star 1, .star 2)
#guard parsePT "*/1+*" == some (.star 0, .star 1)
#guard parseColorIndicator "Color indicator: Blue, Black" == some { blue := true, black := true }
#guard parseChapterHeader "I, II — Draw a card." == some ("I, II", "Draw a card.")
#guard parseChapterHeader "III — Destroy all creatures." == some ("III", "Destroy all creatures.")
#guard parseLoyaltyAbilityLine "[+1]: Draw a card." == some (.plus 1, "Draw a card.")
#guard parseLoyaltyAbilityLine "[-X]: Deal X damage to any target." == some (.minusX, "Deal X damage to any target.")
#guard parseHandLifeLine "Hand modifier: +1, Life modifier: -2" == some (1, -2)
#guard parseBareModifierPair "+0, +3" == some (0, 3)

-- Stage 2 (`Lexer`): reminder-text stripping, `{CHAOS}` stripping, mechanic labels, and quote-aware lexing.
#guard Parser.extractLeadingLabel "Power-up — {2}: Put a +1/+1 counter on this creature." == (some .powerUp, "{2}: Put a +1/+1 counter on this creature.")
#guard Parser.extractLeadingLabel "Exhaust — {4}{G}: Create two 1/1 green Elf tokens." == (some .exhaust, "{4}{G}: Create two 1/1 green Elf tokens.")
#guard Parser.extractLeadingLabel "Boast — {1}{R}: This creature deals 2 damage to any target." == (some .boast, "{1}{R}: This creature deals 2 damage to any target.")
#guard Parser.extractLeadingLabel "Eminence — Whenever you cast a Wizard spell, draw a card." == (some .eminence, "Whenever you cast a Wizard spell, draw a card.")
#guard Parser.extractLeadingLabel "Landfall — Whenever a land you control enters, gain 1 life." == (none, "Whenever a land you control enters, gain 1 life.")
#guard Parser.extractQuotedSpans "Other creatures have \"{T}: Add {G}.\" and vigilance." == #["{T}: Add {G}."]
#guard Parser.hasTopLevelColon "{2}, {T}: Draw a card."
#guard !(Parser.hasTopLevelColon "Other creatures you control have \"{T}: Add {G}.\"")
#guard Parser.splitTopLevelSentences "Target creature has \"{T}: Draw a card. Discard a card.\" Draw a card." ==
  #["Target creature has \"{T}: Draw a card. Discard a card.\"", "Draw a card"]

-- Stage 3 (`ParagraphClass`): deterministic paragraph classification and `DeckLimit` parsing.
#guard match parseOracleCard "Relentless Construct\n{2}\nArtifact Creature — Construct\n2/2\nA deck can have any number of cards named Relentless Construct." with
  | .ok c => c.deckLimitOverride == some .unlimited
  | .error _ => false
#guard match parseOracleCard "Sevenfold Mystic\n{1}{U}\nCreature — Wizard\n1/2\nA deck can have up to seven cards named Sevenfold Mystic." with
  | .ok c => c.deckLimitOverride == some (.maxCopies 7)
  | .error _ => false
#guard match parseOracleCard "Basic Grove\nBasic Land — Forest\n({T}: Add {G}.)" with
  | .ok c => c.activatedAbilities.isEmpty && c.hasSubtype .forest
  | .error _ => false
#guard match parseOracleCard "Split Blade\n{1}{W}\nCreature — Elf\n2/2\n//ADV//\nQuick Slash\n{W}\nInstant — Adventure\nTarget creature gets +1/+1 until end of turn." with
  | .ok c => c.subFaces.size == 1 && c.subFaces[0]!.kind == .adventure && c.subFaces[0]!.spellAbility.isSome
  | .error _ => false
#guard match parseOracleCard "Dual Aspect\n{1}{W}\nCreature — Human\n2/2\nVigilance\n//\nDark Aspect\nCreature — Zombie\n3/3\nColor indicator: Black\nMenace" with
  | .ok c => c.otherFace.isSome && c.otherFace.get!.name == "Dark Aspect" && c.otherFace.get!.colorIndicator == some { black := true } && c.otherFace.get!.keywords.contains (.simple .menace)
  | .error _ => false
#guard match parseOracleCard "Saga of Dawn\n{2}{W}\nEnchantment — Saga\nI, II — Create a 1/1 white Soldier creature token.\nIII — Creatures you control get +2/+2 until end of turn." with
  | .ok c => c.hasSagaChapters && c.triggeredAbilities.size == 2
  | .error _ => false

-- Stage 4 & 5 (`SubGrammars`, `TokenEmblemGrammar`, `InspectSearchGrammar`, `InstructionGrammar`, `AbilityGrammar`, `DiscourseBind`):
-- Unseen compositional combinations & semantic regressions.
#guard roundTripsOracleCard "Aether Tutor\n{2}{U}\nSorcery\nSearch your library for an instant or sorcery card, reveal it, put it into your hand, then shuffle."
#guard roundTripsOracleCard "Tidecaller's Decree\n{3}{U}{U}\nInstant\nCounter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled."
#guard roundTripsOracleCard "Emblem Architect\n{2}{W}{W}\nLegendary Planeswalker — Elspeth\n4\n[+1]: Create a 1/1 white Soldier creature token.\n[-2]: Exile target tapped creature.\n[-6]: You get an emblem with \"Creatures you control get +2/+2 and have flying.\""
#guard roundTripsOracleCard "Gilded Hoarder\n{3}{R}\nCreature — Dragon\n4/4\nFlying\nWhenever you cast a spell, if mana from a Treasure was spent to cast it, draw a card and lose 1 life."
#guard roundTripsOracleCard "Graveyard Siphon\n{2}{B}\nCreature — Warlock\n2/3\n{1}, Sacrifice another creature: Draw cards equal to the sacrificed creature's power, then discard a card."
#guard roundTripsOracleCard "Tempest Channeler\n{2}{U}{W}\nCreature — Wizard\n3/3\nWhenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn."
#guard roundTripsOracleCard "Arcane Scribe\n{2}{U}\nEnchantment\nWhenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards."
#guard roundTripsOracleCard "Bounty Hunter\n{2}{B}\nCreature — Assassin\n3/2\nWhen Bounty Hunter enters, you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls."
#guard roundTripsOracleCard "Gale Recall\n{1}{W}\nInstant\nKicker {2}{W}\nChoose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand."

-- Semantic AST checks on tricky Stage 4/5 bindings:
-- 1. `Thranduil's Decree` folds `ifPermanentMayCastFree := true` onto `StackOp.counterStack`.
#guard match Catalog.thranduilsDecree.spellEffect with
  | some e => e.body == .stack (.counterStack (.target 0) true true)
  | none => false
-- 2. `Smaug, Wicked Worm` folds `manaSpent? := some .fromTreasure` onto `TriggerPattern.castSpell`.
#guard Catalog.smaugWickedWorm.triggeredAbilities.any fun ab =>
  match ab.pattern with
  | .castSpell _ _ _ (some .fromTreasure) _ _ _ => ab.interveningIf?.isNone
  | _ => false
-- 3. `Tom, Bert, and William` binds `cost.bindVar?` when effect references `ObjectExpr.costPaidObjects`.
#guard Catalog.tomBertAndWilliam.activatedAbilities.any fun ab =>
  ab.cost.bindVar?.isSome
-- 4. `Storm, Windrider` resolves `"those creatures"` to `.filter (.targetsOf .triggerSubject) (.hasType .creature)`.
#guard Catalog.stormWindrider.triggeredAbilities.any fun ab =>
  match ab.effect.body with
  | .installEffect (.applyContinuous .untilEndOfTurn (.filter (.targetsOf .triggerSubject) (.hasType .creature)) _) => true
  | _ => false
-- 5. `Uncover the Moon-Letters` uses `ValueExpr.manaSpent .triggerSubject` (not `.eventAmount`).
#guard Catalog.uncoverTheMoonLetters.triggeredAbilities.any fun ab =>
  match ab.effect.body with
  | .optional .you none (.seq #[.player (.drawCards .you (.manaSpent .triggerSubject)), _]) .noop _ => true
  | _ => false
-- 6. `Killmonger, Scourge of Wakanda` uses standard `.thisEnters` reflexive marker (not Bolg's `.sacrifice`).
#guard Catalog.killmongerScourgeOfWakanda.triggeredAbilities.any fun ab =>
  match ab.effect.body with
  | .optional .you (some _) (.queueReflexiveTrigger refl) .noop _ => refl.pattern == .thisEnters
  | _ => false
-- 7. `Bolg of the North` preserves `.sacrifice` reflexive trigger with `cost.bindVar?`.
#guard Catalog.bolgOfTheNorth.triggeredAbilities.any fun ab =>
  match ab.effect.body with
  | .optional .you (some cost) (.queueReflexiveTrigger refl) .noop _ =>
    cost.bindVar?.isSome && match refl.pattern with | .sacrifice .. => true | _ => false
  | _ => false
-- 8. `The Eagles Are Coming!` encodes kicked target override via `altDomainIf?`.
#guard match Catalog.theEaglesAreComing.spellEffect with
  | some e =>
    match e.targets.slots[0]?.bind (·.altDomainIf?) with
    | some (Condition.castPred (.wasKicked .this), _) => true
    | _ => false
  | none => false
-- 9. `Moonstone, Harsh Mistress` preserves optional exile + play-until-end-of-next-turn binding.
#guard Catalog.moonstoneHarshMistress.triggeredAbilities.any fun ab =>
  match ab.effect.body with
  | .optional .you none (.bind _ (.moveZone .triggerSubject .exile .exile _) (.stack (.mayCastOrPlay (.stepObjects _) _))) .noop _ => true
  | _ => false
-- 10. `The Serpent Society` produces `forEach (.eachPlayer .opponent)` nontoken creature sacrifice.
#guard Catalog.theSerpentSociety.triggeredAbilities.any fun ab =>
  match ab.effect.body with
  | .forEach (.eachPlayer .opponent) _ (.moveZone _ .graveyard .sacrifice _) => true
  | _ => false

end Mtg.Engine.Tests
