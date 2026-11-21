import Mtg.Engine.Card.ParseOracle

/-!
# Oracle parser checks

`#guard` regression tests for `parseOracleCard` and its helpers. They are kept
out of `Mtg.Engine.Card.ParseOracle` so they run the compiled parser and the
catalog does not wait for them.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open OracleNorm
open OracleActivate
open OracleArgs
open OracleCandidates

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
#guard parsePT "2/2" == some ({ number := some 2 }, { number := some 2 })
#guard parsePT "2/3" == some ({ number := some 2 }, { number := some 3 })
#guard parsePT "-1/-1" == some ({ number := some (-1) }, { number := some (-1) })
#guard parsePT "*/*" == some ({ star := true }, { star := true })
#guard parsePT "1/*" == some ({ number := some 1 }, { star := true })
#guard parsePT "*/3" == some ({ star := true }, { number := some 3 })
#guard parsePT "*/4" == some ({ star := true }, { number := some 4 })
#guard parsePT "1+*/1+*" == some ({ number := some 1, star := true }, { number := some 1, star := true })
#guard parsePT "*+1/*+1" == parsePT "1+*/1+*"
#guard parsePT "1 + */1 + *" == parsePT "1+*/1+*"
#guard parsePT "*/1+*" == some ({ star := true }, { number := some 1, star := true })
#guard parsePT "2+*/2+*" == some ({ number := some 2, star := true }, { number := some 2, star := true })
#guard parsePT "*-1/*-1" == some ({ number := some (-1), star := true }, { number := some (-1), star := true })
#guard (parsePT "1+*/1+*").map (fun (p, t) => (p.undetermined, t.undetermined)) == some (1, 1)
#guard (parsePT "*/*").map (fun (p, t) => (p.undetermined, t.undetermined)) == some (0, 0)
#guard parsePT "+1/+1" == none
#guard parsePT "2*/2*" == none
#guard parsePT "1+/1" == none
#guard parsePT "*+/*+" == none
#guard parsePT "*1/*1" == none
#guard (parseOracleCard "Grizzly Bears\n{1}{G}\nCreature — Bear\n2/2").toOption.map
    (fun c => c.name == "Grizzly Bears" && c.manaCost == ManaCost.ofGenericAndColor 1 .green &&
      c.power == some 2 && c.toughness == some 2 && !c.powerStar && !c.toughnessStar &&
      c.isCreature && c.modellingError?.isNone) == some true

-- A line the engine does not recognize is rejected, including when the caller
-- asks to keep unrecognized text. An effect that would not resolve is rejected
-- even if the line was stored.
#guard
  match parseOracleCard "Bogus\n{R}\nInstant\nFrobnicate the widget." with
  | .error e => e.contains "unrecognized" || e.contains "unparsed" || e.contains "not fully modelled"
  | .ok _ => false
#guard
  match parseOracleCardKeeping "Bogus\n{R}\nInstant\nFrobnicate the widget." with
  | .error e => e.contains "unparsed" || e.contains "unrecognized" || e.contains "not fully modelled"
  | .ok _ => false
#guard
  let bogus : CardDef := {
    name := "Bogus"
    types := #[.instant]
    spellEffect := some { resolution := .unrecognized }
  }
  match bogus.modellingError? with
  | some e => e.contains "not fully modelled"
  | none => false

-- CR 208.2 / 208.2a: power and toughness may include a star. Lost Order of
-- Jarkeld is `1+*`. With no chosen player, the star is 0, so the card is 1/1.
-- `*+1` is that same printed value. A bare star is 0.
#guard (parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n1+*/1+*\nVigilance").toOption.map
    (fun c => c.power == some 1 && c.toughness == some 1 && c.powerStar && c.toughnessStar &&
      c.power.getD 0 == 1 && c.toughness.getD 0 == 1 && c.ptString == "1+*/1+*" &&
      KeywordAbility.hasVigilance c.keywords && c.hasSubtype .human && c.hasSubtype .knight) == some true
#guard (parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n*+1/*+1").toOption.map
    (fun c => c.power == some 1 && c.toughness == some 1 && c.powerStar && c.toughnessStar &&
      c.ptString == "1+*/1+*") == some true
#guard (parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n1 + * / 1 + *").toOption.map
    (fun c => c.ptString == "1+*/1+*" && c.power.getD 0 == 1) == some true
#guard
  match parseOracleCard "Lost Order of Jarkeld\n{3}{W}{U}\nCreature — Human Knight\n1+*/1+*\nVigilance" with
  | .ok c =>
    match parseOracleCard (renderFullOracle c) with
    | .ok d => d.power == some 1 && d.toughness == some 1 && d.powerStar && d.toughnessStar &&
        d.ptString == "1+*/1+*" && KeywordAbility.hasVigilance d.keywords
    | .error _ => false
  | .error _ => false
#guard (parseOracleCard "Tarmogoyf\n{1}{G}\nCreature — Lhurgoyf\n*/1+*").toOption.map
    (fun c => c.power.isNone && c.powerStar && c.toughness == some 1 && c.toughnessStar &&
      c.power.getD 0 == 0 && c.toughness.getD 0 == 1 && c.ptString == "*/1+*") == some true
#guard (parseOracleCard "Angry Mob\n{2}{W}{W}\nCreature — Human\n2+*/2+*").toOption.map
    (fun c => c.power == some 2 && c.toughness == some 2 && c.powerStar && c.toughnessStar &&
      c.power.getD 0 == 2 && c.ptString == "2+*/2+*") == some true
#guard (parseOracleCard "Maro\n{2}{G}{G}\nCreature — Elemental\n*/*").toOption.map
    (fun c => c.power.isNone && c.toughness.isNone && c.powerStar && c.toughnessStar &&
      c.power.getD 0 == 0 && c.toughness.getD 0 == 0 && c.ptString == "*/*") == some true
#guard (parseOracleCard "Namor the Sub-Mariner\n{1}{U}{U}\nLegendary Creature — Mutant Merfolk Villain\n*/4\nFlying").toOption.map
    (fun c => c.power.isNone && c.powerStar && c.toughness == some 4 && !c.toughnessStar &&
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
    (fun c => c.spellEffect.map (·.spellResolution)) ==
    some (some (SpellResolution.sequence
      [.onPermanent (.pump (-4) 0), .draw 1]))
#guard (parseOracleCard "Wander\n{G}\nInstant\nForestcycling {2}").toOption.bind
    (fun c => c.activatedAbilities[0]?) ==
    some (typecyclingAbility "Forest" (ManaCost.ofGeneric 2))
#guard (parseOracleCard "Sword\n{2}\nArtifact — Equipment\nEquip {5}").toOption.bind
    (fun c => c.activatedAbilities[0]?) == some (equipAbility (ManaCost.ofGeneric 5))
#guard (parseOracleCard "Warren Chief\n{1}{R}\nCreature — Goblin\n2/2\nOther Goblin creatures you control get +2/+2.").toOption.bind
    (fun c => c.staticAbilities[0]?) == some (.otherCreaturesGet #[.goblin] 2 2)
#guard (parseOracleCard "Test Saga\n{2}{R}\nEnchantment — Saga\nI — Draw seven cards.").toOption.bind
    (fun c => c.saga.bind fun s => (s.chapters[0]?).bind (·.chapterEffect)) ==
    some (Effect.chapterDraw 7)
#guard (indexedAbilities.get).any fun item =>
  match item.ability with
  | .spell e => e == Effect.draw 1
  | _ => false
#guard !(indexedAbilities.get).any fun item =>
  match item.ability with
  | .spell e => e == Effect.draw 2 || e == Effect.dealDamage 2
  | _ => false
#guard !(indexedAbilities.get).any fun item =>
  match item.ability with
  | .activated a => a == equipAbility (ManaCost.ofGeneric 1) || a == equipAbility (ManaCost.ofGeneric 2)
  | _ => false
#guard (indexedAbilities.get).any fun item =>
  match item.ability with
  | .activated a => a == equipAbility (ManaCost.ofGeneric 3)
  | _ => false

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
    | some back => back.isCreature && back.power == some 4 && back.toughness == some 4 &&
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
      c.power == some 1 && c.toughness == some 1) == some true
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
  | .ok c => c.spellEffect.map (·.resolution) ==
      some (.spellsCostLessThisTurn (.supertype s) 3)
  | .error _ => false
#guard (parseOracleCard "Walk\n{G}\nInstant\nSnowcycling {2}").toOption.bind
    (fun c => c.activatedAbilities[0]?) ==
    some (typecyclingAbility "Snow" (ManaCost.ofGeneric 2))
#guard (parseOracleCard "Walk\n{G}\nInstant\nBasic landcycling {2}").toOption.bind
    (fun c => c.activatedAbilities[0]?) ==
    some (typecyclingAbility "Basic land" (ManaCost.ofGeneric 2))
#guard (parseOracleCard "Helm\n{1}\nArtifact\nVillain spells you cast cost {1} less to cast.").toOption.bind
    (fun c => c.staticAbilities[0]?) == some (.subtypeSpellsCostLess .villain 1)
#guard (parseOracleCard "Surge\n{R}\nSorcery\nPlaneswalker spells you cast this turn cost {2} less to cast.").toOption.bind
    (fun c => c.spellEffect.map (·.resolution)) ==
    some (.spellsCostLessThisTurn (.cardType .planeswalker) 2)

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
#guard (parseOracleCard "Worker\n{3}\nArtifact Creature — Assembly-Worker\n2/2\nAssembly-Workercycling {4}").toOption.bind
    (fun c => c.subtypes == #["Assembly-Worker"] &&
      c.activatedAbilities[0]? ==
        some (typecyclingAbility "Assembly-Worker" (ManaCost.ofGeneric 4))) == some true
#guard (parseOracleCard "Doctor\n{U}\nCreature — Time Lord Doctor\n1/1\nTime Lordcycling {2}").toOption.bind
    (fun c => c.subtypes == #["Time Lord", "Doctor"] &&
      c.activatedAbilities[0]? ==
        some (typecyclingAbility "Time Lord" (ManaCost.ofGeneric 2))) == some true
#guard (parseOracleCard "Helm\n{1}\nArtifact\nC'tan spells you cast cost {1} less to cast.").toOption.bind
    (fun c => c.staticAbilities[0]?) == some (.subtypeSpellsCostLess .ctan 1)
#guard (parseOracleCard "Walk\n{G}\nSorcery\nSearch your library for a Power-Plant card, reveal it, put it into your hand, then shuffle.").toOption.bind
    (fun c => c.spellEffect) == some (Effect.searchLandTypeToHand "Power-Plant")
#guard (parseOracleCard "Walk\n{G}\nSorcery\nSearch your library for a Bolas's Meditation Realm card, reveal it, put it into your hand, then shuffle.").toOption.bind
    (fun c => c.spellEffect) == some (Effect.searchLandTypeToHand "Bolas's Meditation Realm")
#guard (parseOracleCard "Saga\n{2}\nEnchantment — Saga\nI — This Saga deals 3 damage to each non-Time Lord creature and each opponent.").toOption.bind
    (fun c => c.saga.bind fun s => (s.chapters[0]?).bind (·.chapterEffect)) ==
    some (Effect.chapterDealDamageToEachNonSubtypeAndOpponents 3 "Time Lord")

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
    (fun c => match c.saga with
      | some s => s.chapters.size == 1 &&
          (s.chapters[0]?).any (fun ch => ch.roman == "I" && ch.chapterEffect.isSome)
      | none => false) == some true
#guard (parseOracleCard "Tale\n{2}\nEnchantment — Saga\nII — This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"").toOption.bind
    (fun c => c.saga.bind fun s => s.chapters[0]?.bind (·.chapterEffect)) ==
    some (Effect.chapterGainLandfallCreateElf)
#guard (parseOracleCard "Tale\n{2}\nEnchantment — Saga\nII — Council's Dilemma — This Saga gains \"Whenever a land you control enters, create a 1/1 green Elf creature token.\"").toOption.bind
    (fun c => c.saga.bind fun s => s.chapters[0]?.bind (·.chapterEffect)) ==
    some (Effect.chapterGainLandfallCreateElf)

-- CR 207.4: the chaos symbol is not rules text. Towashi's chaos ability is the
-- text after the symbol, and a `{CHAOS}` that names a planar-die face stays.
private def towashiChaosAbility : String :=
  "Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control."

#guard
  match parseOracleCard s!"Towashi\nPlane — Kamigawa\nMenace\n\{CHAOS} {towashiChaosAbility}",
        parseOracleCard s!"Towashi\nPlane — Kamigawa\nMenace\n{towashiChaosAbility}" with
  | .ok a, .ok b => reprStr a == reprStr b
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
    (fun c => c.saga.bind fun s => s.chapters[0]?.bind (·.chapterEffect)) ==
    some (Effect.chapterGainLandfallCreateElf)

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
    (fun c => match c.saga with
      | some s => s.chapters.size == 3 && s.finalChapterNumber == 3 &&
          s.sacrificeAfter == "III" && c.triggeredAbilities.isEmpty
      | none => false) == some true

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
    | .ok d => reprStr d == reprStr c
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
      (c.activatedAbilities[0]!.mana?.map (·.riders)) == some #[.gainsHaste]
  | .error _ => false
#guard
  match parseOracleCard "Anvil of Growth\nLand\n{T}: Add {C}. If that mana is spent on a creature spell, that creature enters with two additional +1/+1 counters on it." with
  | .ok c =>
    c.activatedAbilities.size == 1 &&
      c.activatedAbilities[0]!.isManaAbility &&
      (c.activatedAbilities[0]!.mana?.map (·.riders)) == some #[.entersWithPlusOneCounters 2]
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
  -- Novel compositional static cards never printed in the catalog:
  "Archmage Tutor\n{2}{U}\nCreature — Human Wizard\n2/2\nOther Wizard creatures you control get +2/+1 and have vigilance and lifelink.",
  "Menacing Aura\n{1}{B}\nEnchantment — Aura\nEnchant creature\nEnchanted creature gets +3/+2 and has menace.",
  "Goblin Costcutter\n{1}{R}\nCreature — Goblin Shaman\n1/1\nGoblin spells you cast cost {2} less to cast.",
  "Dampening Arbiter\n{2}{W}\nCreature — Human Advisor\n2/3\nNoncreature spells your opponents cast cost {2} more to cast.",
  "Dragonkin Warden\n{2}{R}\nCreature — Human Warrior\n2/2\nAs long as you control a Dragon, this creature gets +3/+3 and has flying and trample.",
  "Tripling Procession\n{4}{W}\nEnchantment\nIf one or more tokens would be created under your control, three times that many of those tokens are created instead.",
  "Ward of Permanence\n{1}{W}\nEnchantment — Aura\nEnchant nonland permanent\nEnchanted permanent has hexproof."
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

end Mtg.Engine.Tests
