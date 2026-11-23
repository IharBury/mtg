import Mtg.Engine.Card

/-!
# Sample cards

A small Oracle-faithful catalog used by engine tests. The engine itself is
card-agnostic; these definitions just exercise the rules we model.

Cards from Magic: The Gathering | The Hobbit (HOB) live in
`Mtg.Engine.Catalog.Hobbit`. Cards from The Hobbit Eternal (HOC) live in
`Mtg.Engine.Catalog.HobbitEternal`. Cards from Marvel Super Heroes (MSH) live
in `Mtg.Engine.Catalog.MarvelSuperHeroes`. Cards from Reality Fracture (FRA)
live in `Mtg.Engine.Catalog.RealityFracture`. Cards from Reality Fracture
Commander (FRC) live in `Mtg.Engine.Catalog.RealityFractureCommander`.
Decklists that use them live in `Mtg.Demo`.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

/-- Build a `CardDef` by parsing the full printed card. `oracleText` is the
rules text and is not stored. When that text is empty, the modeled fields
passed with the header are kept so test fixtures without rules text still
work. A back face is attached from `otherFace`; it is not part of the front's
rules text. -/
-- `irreducible` stops `#guard` from unfolding this into the parser. The
-- compiled body is unchanged: nonempty rules text is still `parseOracleCard!`.
@[irreducible, noinline] def card (name : String) (types : Array CardType)
    (manaCost : ManaCost := ManaCost.empty) (subtypes : Array Subtype := #[])
    (oracleText : String := "") (power : Option Int := none)
    (toughness : Option Int := none) (keywords : Array KeywordAbility := #[])
    (supertypes : Array Supertype := #[])
    (spellEffect : Option Effect := none)
    (additionalCosts : Array AdditionalCostSpec := #[])
    (isToken : Bool := false)
    (colorIndicator : Option ColorSet := none)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (adventure : Option SubFace := none)
    (otherFace : Option CardDef := none) : CardDef :=
  let text :=
    formatPrintedCard name manaCost supertypes types subtypes
      (power.map .fixed) (toughness.map .fixed)
      colorIndicator isToken oracleText
  let parsed := { parseOracleCard! text with otherFace := otherFace }
  if (oracleText.trimAscii.copy).isEmpty then
    let spellAbility : Option SpellAbility :=
      match spellEffect with
      | some eff => some { effect := eff, additionalCosts }
      | none =>
        if additionalCosts.isEmpty then none
        else some { effect := {}, additionalCosts }
    let subFaces : Array SubFace :=
      match adventure with
      | some adv => #[adv]
      | none => #[]
    { parsed with
      keywords
      spellAbility
      staticAbilities
      triggeredAbilities
      activatedAbilities
      subFaces }
  else
    parsed

/-- Parse a card from its full printed text, one string per line.
The lines are the definition: name, mana cost, type line, power and
toughness, and rules. A line that is exactly `//` starts the back face. -/
@[irreducible, noinline] def fromOracle (lines : List String) : CardDef :=
  parseOracleCard! (String.intercalate "\n" lines)

/-- Parse printed text. Fails when a line is not fully parsed or an effect is
not fully modelled, the same as `fromOracle`. -/
@[irreducible, noinline] def fromOracleKeeping (lines : List String) : CardDef :=
  match parseOracleCardKeeping (String.intercalate "\n" lines) with
  | .ok c => c
  | .error e => panic! s!"parseOracleCardKeeping: {e}\n---\n{String.intercalate "\n" lines}"

/-- A basic land whose name is also its land type (CR 305.6). -/
@[irreducible, noinline] def basicLand (landName : String) (color : Color) : CardDef :=
  card landName #[.land] (subtypes := #[landName]) (supertypes := #[.basic])
    (oracleText := s!"(\{T}: Add \{{color.letter}}.)")

def plains : CardDef :=
  fromOracle [
    "Plains",
    "Basic Land — Plains",
    "({T}: Add {W}.)",
  ]
def island : CardDef :=
  fromOracle [
    "Island",
    "Basic Land — Island",
    "({T}: Add {U}.)",
  ]
def swamp : CardDef :=
  fromOracle [
    "Swamp",
    "Basic Land — Swamp",
    "({T}: Add {B}.)",
  ]
def mountain : CardDef :=
  fromOracle [
    "Mountain",
    "Basic Land — Mountain",
    "({T}: Add {R}.)",
  ]
def forest : CardDef :=
  fromOracle [
    "Forest",
    "Basic Land — Forest",
    "({T}: Add {G}.)",
  ]

/-- A creature used by engine tests and the Hobbit catalog. -/
@[irreducible, noinline] def creature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Array KeywordAbility := #[])
    (supertypes : Array Supertype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (adventure : Option SubFace := none)
    (colorIndicator : Option ColorSet := none)
    (isToken : Bool := false)
    (otherFace : Option CardDef := none) : CardDef :=
  card name #[.creature] manaCost subtypes oracleText (some power) (some toughness)
    keywords supertypes
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities) (adventure := adventure)
    (colorIndicator := colorIndicator) (isToken := isToken)
    (otherFace := otherFace)

/-- A legendary creature (CR 205.4 / 704.5j). -/
@[irreducible, noinline] def legendaryCreature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Array KeywordAbility := #[])
    (supertypes : Array Supertype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (adventure : Option SubFace := none)
    (otherFace : Option CardDef := none) : CardDef :=
  creature name manaCost subtypes power toughness oracleText
    (keywords := keywords)
    (supertypes := #[.legendary] ++ supertypes)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities) (adventure := adventure)
    (otherFace := otherFace)

/-- Instant or sorcery with an optional one-shot effect. -/
@[irreducible, noinline] def spellCard (cardType : CardType) (name : String) (manaCost : ManaCost)
    (oracleText : String) (spellEffect : Option Effect := none)
    (additionalCosts : Array AdditionalCostSpec := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (staticAbilities : Array StaticAbility := #[]) : CardDef :=
  card name #[cardType] manaCost (oracleText := oracleText)
    (spellEffect := spellEffect)
    (additionalCosts := additionalCosts)
    (activatedAbilities := activatedAbilities)
    (staticAbilities := staticAbilities)

/-- An instant, optionally with a one-shot effect. -/
@[irreducible, noinline] def instant (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : Option Effect := none)
    (additionalCosts : Array AdditionalCostSpec := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (staticAbilities : Array StaticAbility := #[]) : CardDef :=
  spellCard .instant name manaCost oracleText spellEffect
    (additionalCosts := additionalCosts)
    (activatedAbilities := activatedAbilities)
    (staticAbilities := staticAbilities)

/-- A sorcery, optionally with a one-shot effect. -/
@[irreducible, noinline] def sorcery (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : Option Effect := none)
    (additionalCosts : Array AdditionalCostSpec := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (staticAbilities : Array StaticAbility := #[]) : CardDef :=
  spellCard .sorcery name manaCost oracleText spellEffect
    (additionalCosts := additionalCosts)
    (activatedAbilities := activatedAbilities)
    (staticAbilities := staticAbilities)

/-- A non-Aura enchantment. -/
@[irreducible, noinline] def enchantment (name : String) (manaCost : ManaCost) (oracleText : String)
    (keywords : Array KeywordAbility := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[])
    (supertypes : Array Supertype := #[])
    (adventure : Option SubFace := none) : CardDef :=
  card name #[.enchantment] manaCost subtypes oracleText (keywords := keywords)
    (supertypes := supertypes)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)
    (adventure := adventure)

/-- A catalog Saga chapter `TriggeredAbility` with parsed Roman numerals (CR 714.2). -/
def chapter (roman _effect : String) (e : Effect) : TriggeredAbility :=
  TriggeredAbility.sagaChapters (parseChapterNumbers roman) e

/-- A Saga enchantment (CR 714). Final chapter is the greatest chapter number
across `chapters` (CR 714.2d). -/
@[irreducible, noinline] def saga (name : String) (manaCost : ManaCost) (oracleText : String)
    (_sacrificeAfter : String) (chapters : Array TriggeredAbility) : CardDef :=
  enchantment name manaCost oracleText
    (subtypes := #["Saga"])
    (triggeredAbilities := chapters)

/-- An Aura enchantment (CR 303.4). -/
@[irreducible, noinline] def aura (name : String) (manaCost : ManaCost) (oracleText : String)
    (keywords : Array KeywordAbility := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[]) : CardDef :=
  enchantment name manaCost oracleText keywords staticAbilities triggeredAbilities
    (subtypes := #["Aura"])

/-- An artifact, including Equipment. -/
@[irreducible, noinline] def artifact (name : String) (manaCost : ManaCost) (oracleText : String)
    (subtypes : Array Subtype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (isToken : Bool := false)
    (keywords : Array KeywordAbility := #[])
    (supertypes : Array Supertype := #[])
    (power : Option Int := none)
    (toughness : Option Int := none)
    (adventure : Option SubFace := none) : CardDef :=
  card name #[.artifact] manaCost subtypes oracleText
    (power := power) (toughness := toughness)
    (keywords := keywords)
    (supertypes := supertypes)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)
    (isToken := isToken)
    (adventure := adventure)

/-- An artifact creature, optionally legendary. -/
@[irreducible, noinline] def artifactCreature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Array KeywordAbility := #[])
    (supertypes : Array Supertype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (otherFace : Option CardDef := none) : CardDef :=
  card name #[.artifact, .creature] manaCost subtypes oracleText
    (some power) (some toughness) keywords
    supertypes
    (staticAbilities := staticAbilities)
    (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)
    (otherFace := otherFace)

/-- A nonbasic land. -/
@[irreducible, noinline] def land (name : String) (oracleText : String)
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[])
    (supertypes : Array Supertype := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (staticAbilities : Array StaticAbility := #[]) : CardDef :=
  card name #[.land] (subtypes := subtypes) (oracleText := oracleText)
    (supertypes := supertypes)
    (activatedAbilities := activatedAbilities)
    (triggeredAbilities := triggeredAbilities)
    (staticAbilities := staticAbilities)

/-- A legendary land. -/
@[irreducible, noinline] def legendaryLand (name : String) (oracleText : String)
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[])
    (staticAbilities : Array StaticAbility := #[]) : CardDef :=
  land name oracleText (supertypes := #[.legendary])
    (activatedAbilities := activatedAbilities) (subtypes := subtypes)
    (staticAbilities := staticAbilities)

/-- A Treasure token (CR 111 / 111.10a). -/
def treasureToken : CardDef :=
  fromOracle [
    "Treasure",
    "Artifact — Treasure",
    "Token",
    "{T}, Sacrifice this token: Add one mana of any color.",
  ]

/-- A creature token with a color indicator (CR 202.2e). -/
def tokenCreature (name : String) (subtypes : Array Subtype)
    (power toughness : Int) (color : Color)
    (keywords : Array KeywordAbility := #[]) : CardDef :=
  creature name ManaCost.empty subtypes power toughness
    (colorIndicator := some (ColorSet.singleton color))
    (keywords := keywords)
    (isToken := true)

/-- A 1/1 white Human Soldier creature token. -/
def humanSoldierToken : CardDef :=
  fromOracle [
    "Human Soldier",
    "Creature — Human Soldier",
    "1/1",
    "Color indicator: White",
    "Token",
  ]

/-- A Food token. -/
def foodToken : CardDef :=
  fromOracle [
    "Food",
    "Artifact — Food",
    "Token",
    "{2}, {T}, Sacrifice this token: You gain 3 life.",
  ]

def wolfToken : CardDef :=
  fromOracle [
    "Wolf",
    "Creature — Wolf",
    "2/2",
    "Color indicator: Green",
    "Token",
  ]

def dwarfToken : CardDef :=
  fromOracle [
    "Dwarf",
    "Creature — Dwarf",
    "2/2",
    "Color indicator: Red",
    "Token",
  ]

def bearToken : CardDef :=
  fromOracle [
    "Bear",
    "Creature — Bear",
    "2/2",
    "Color indicator: Green",
    "Token",
  ]

def elfToken : CardDef :=
  fromOracle [
    "Elf",
    "Creature — Elf",
    "1/1",
    "Color indicator: Green",
    "Token",
  ]

/-- An activated ability (CR 602.1). -/
def activated (effect : Effect) (mana : ManaCost := ManaCost.empty)
    (tap : Bool := false) (sacrificeSource : Bool := false)
    (sacrificeAnotherCreatureOrArtifact : Bool := false)
    (timing : ActivationTiming := .instant)
    (activeZones : Array ZoneKind := #[.battlefield])
    (turnLimit? : Option Nat := none)
    (lifetimeLimit? : Option Nat := none)
    (condition? : Option Condition := none)
    (costReductions : Array ActivationCostReduction := #[])
    (tag? : Option ActivationMechanicTag := none)
    (extraModes : Array Effect := #[]) (payLife : Nat := 0)
    (discardSource : Bool := false)
    (sacrificeAnotherSubtype : Option CardSubtype := none)
    (sacrificeAnotherCreature : Bool := false)
    (discardACard : Bool := false)
    (tapAnUntappedCreatureYouControl : Bool := false)
    (removeIndestructibleCounter : Bool := false)
    (sacrificeLegendaryArtifact : Bool := false)
    (discardLegendarySameName : Bool := false)
    (sacrificeArtifact : Bool := false)
    (sacrificeArtifactOrCreature : Bool := false)
    (sacrificeArtifactOrDiscardNonland : Bool := false)
    (removeAnyNumberPlusOne : Bool := false)
    (putStunCounterOnSource : Bool := false)
    (sacrificeEquipmentAttachedToSource : Bool := false) :
    ActivatedAbility :=
  OracleActivate.activated effect mana
    (tap := tap) (sacrificeSource := sacrificeSource)
    (sacrificeAnotherCreatureOrArtifact := sacrificeAnotherCreatureOrArtifact)
    (timing := timing) (activeZones := activeZones)
    (turnLimit? := turnLimit?) (lifetimeLimit? := lifetimeLimit?)
    (condition? := condition?) (costReductions := costReductions) (tag? := tag?)
    (extraModes := extraModes) (payLife := payLife)
    (discardSource := discardSource)
    (sacrificeAnotherSubtype := sacrificeAnotherSubtype)
    (sacrificeAnotherCreature := sacrificeAnotherCreature)
    (discardACard := discardACard)
    (tapAnUntappedCreatureYouControl := tapAnUntappedCreatureYouControl)
    (removeIndestructibleCounter := removeIndestructibleCounter)
    (sacrificeLegendaryArtifact := sacrificeLegendaryArtifact)
    (discardLegendarySameName := discardLegendarySameName)
    (sacrificeArtifact := sacrificeArtifact)
    (sacrificeArtifactOrCreature := sacrificeArtifactOrCreature)
    (sacrificeArtifactOrDiscardNonland := sacrificeArtifactOrDiscardNonland)
    (removeAnyNumberPlusOne := removeAnyNumberPlusOne)
    (putStunCounterOnSource := putStunCounterOnSource)
    (sacrificeEquipmentAttachedToSource := sacrificeEquipmentAttachedToSource)

/-- Equip `mana`: attach to target creature you control, only as a sorcery.
`subtype` restricts Equip to that creature type (e.g. Equip Human). -/
def equipAbility (mana : ManaCost) (subtype : Option CardSubtype := none) : ActivatedAbility :=
  OracleActivate.equipAbility mana (subtype := subtype)

/-- Equip worthy `mana` (MSH): attach only to a worthy creature. -/
def equipWorthyAbility (mana : ManaCost) : ActivatedAbility :=
  OracleActivate.equipWorthyAbility mana

/-- Equipment with a standard Equip cost (CR 301.5 / 702.6). -/
@[irreducible, noinline] def equipment (name : String) (manaCost : ManaCost) (oracleText : String)
    (equip : ManaCost)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (keywords : Array KeywordAbility := #[])
    (supertypes : Array Supertype := #[])
    (subtype : Option CardSubtype := none)
    (moreEquips : Array ActivatedAbility := #[])
    (adventure : Option SubFace := none) : CardDef :=
  artifact name manaCost oracleText
    (subtypes := #["Equipment"])
    (keywords := keywords)
    (supertypes := supertypes)
    (staticAbilities := staticAbilities)
    (triggeredAbilities := triggeredAbilities)
    (activatedAbilities :=
      #[equipAbility equip (subtype := subtype)] ++ moreEquips)
    (adventure := adventure)

/-- Typecycling `{cost}`: discard this card from hand, search for a `landType`
card, put it into your hand, then shuffle (CR 702.29). -/
def typecyclingAbility (landType : String) (mana : ManaCost := ManaCost.ofGeneric 1) :
    ActivatedAbility :=
  OracleActivate.typecyclingAbility landType mana

/-- Adventure characteristics used while the card is a spell (CR 715.2). -/
def adventure (name : String) (manaCost : ManaCost) (_oracleText : String)
    (spellEffect : Effect) (cardType : CardType := .sorcery)
    (additionalCosts : Array AdditionalCostSpec := #[]) : SubFace := {
  kind := .adventure
  name, manaCost, types := #[cardType], subtypes := #["Adventure"],
  spellAbility := some { effect := spellEffect, additionalCosts }
}

/-- A red instant that deals `amount` damage to any target. -/
@[irreducible, noinline] def damageInstant (name : String) (amount : Nat) : CardDef :=
  instant name (ManaCost.ofColor .red)
    s!"{name} deals {amount} damage to any target."
    (some (Effect.dealDamage amount))

def grizzlyBears : CardDef :=
  fromOracle [
    "Grizzly Bears",
    "{1}{G}",
    "Creature — Bear",
    "2/2",
  ]

def grayOgre : CardDef :=
  fromOracle [
    "Gray Ogre",
    "{2}{R}",
    "Creature — Ogre",
    "2/2",
  ]

def hillGiant : CardDef :=
  fromOracle [
    "Hill Giant",
    "{3}{R}",
    "Creature — Giant",
    "3/3",
  ]

def canyonMinotaur : CardDef :=
  fromOracle [
    "Canyon Minotaur",
    "{3}{R}",
    "Creature — Minotaur Warrior",
    "3/3",
  ]

def ragingGoblin : CardDef :=
  fromOracle [
    "Raging Goblin",
    "{R}",
    "Creature — Goblin Berserker",
    "1/1",
    "Haste (This creature can attack and {T} as soon as it comes under your control.)",
  ]

def llanowarElves : CardDef :=
  fromOracle [
    "Llanowar Elves",
    "{G}",
    "Creature — Elf Druid",
    "1/1",
    "{T}: Add {G}.",
  ]

def crawWurm : CardDef :=
  fromOracle [
    "Craw Wurm",
    "{4}{G}{G}",
    "Creature — Wurm",
    "6/4",
  ]

def centaurCourser : CardDef :=
  fromOracle [
    "Centaur Courser",
    "{2}{G}",
    "Creature — Centaur Warrior",
    "3/3",
  ]

def rumblingBaloth : CardDef :=
  fromOracle [
    "Rumbling Baloth",
    "{2}{G}{G}",
    "Creature — Beast",
    "4/4",
  ]

def giantSpider : CardDef :=
  fromOracle [
    "Giant Spider",
    "{3}{G}",
    "Creature — Spider",
    "2/4",
    "Reach (This creature can block creatures with flying.)",
  ]

def lightningBolt : CardDef :=
  fromOracle [
    "Lightning Bolt",
    "{R}",
    "Instant",
    "Lightning Bolt deals 3 damage to any target.",
  ]

def shock : CardDef :=
  fromOracle [
    "Shock",
    "{R}",
    "Instant",
    "Shock deals 2 damage to any target.",
  ]

def giantGrowth : CardDef :=
  fromOracle [
    "Giant Growth",
    "{G}",
    "Instant",
    "Target creature gets +3/+3 until end of turn.",
  ]

/-- Repeat a card `n` times. -/
def copies (n : Nat) (c : CardDef) : Array CardDef :=
  Array.replicate n c

/-- Activated ability that is a power-up (activate only once; reduced if
the source entered this turn). -/
def powerUpAbility (effect : Effect) (mana : ManaCost)
    (tap : Bool := false) : ActivatedAbility :=
  OracleActivate.powerUpAbility effect mana (tap := tap)

/-- `{T}: Add {A} or {B}.` for a dual land's two colors. -/
def dualAddClause (a b : Color) : String :=
  s!"\{T}: Add {manaSymbolsText #[.colored a, .colored b] " or "}."

/-- Dual land: enters tapped, gains 1 life, `{T}: Add` one of two colors.
The Oracle text is reconstructed from the colors. -/
@[irreducible, noinline] def gainLifeDualLand (name : String) (a b : Color) : CardDef :=
  land name
    s!"This land enters tapped.\nWhen this land enters, you gain 1 life.\n{dualAddClause a b}"
    (triggeredAbilities := #[.onEnterGainLife 1])
    (activatedAbilities := #[
      ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored a, .colored b]) (.const 1))])

/-- Dual land: `{T}: Add {C}` plus a two-color tap that requires this land
entered this turn or a basic land you control. The Oracle text is
reconstructed from the colors. -/
@[irreducible, noinline] def conditionalDualLand (name : String) (a b : Color) : CardDef :=
  land name
    s!"\{T}: Add \{C}.\n{dualAddClause a b} Activate only if this land entered this turn or if you control a basic land."
    (activatedAbilities := #[
      ActivatedAbility.manaSimple .colorless,
      ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored a, .colored b]) (.const 1))
        (condition? := some ActivatedAbility.condEnteredThisTurnOrControlBasicLand)])

#guard (gainLifeDualLand "Silent Plaza" .blue .black).manaAbilities ==
  #[.colored .blue, .colored .black]
#guard (gainLifeDualLand "Silent Plaza" .blue .black).triggeredAbilities ==
  #[.onEnterGainLife 1]
#guard ((gainLifeDualLand "Silent Plaza" .blue .black).summary.splitOn "you gain 1 life").length > 1
#guard ((gainLifeDualLand "Silent Plaza" .blue .black).summary.splitOn "{T}: Add {U} or {B}").length > 1
#guard (conditionalDualLand "Silent Lair" .blue .black).enteredOrBasicAddMana ==
  #[.colored .blue, .colored .black]
#guard (conditionalDualLand "Silent Lair" .blue .black).requiresEnteredOrBasicAdd
#guard ((conditionalDualLand "Silent Lair" .blue .black).summary.splitOn "{T}: Add {C}").length > 1
#guard ((conditionalDualLand "Silent Lair" .blue .black).summary.splitOn "entered this turn").length > 1
#guard (legendaryCreature "Silent Legend" ManaCost.empty #[] 1 1).hasSupertype .legendary
#guard (creature "Silent Legend" ManaCost.empty #[] 1 1 (supertypes := #[.legendary])).hasSupertype .legendary
#guard (legendaryLand "Silent Keep" "").hasSupertype .legendary
#guard (instant "Silent Bolt" (ManaCost.ofColor .red) "" (some (Effect.dealDamage 1))).isInstant
#guard (sorcery "Silent Flame" (ManaCost.ofColor .red) "" (some (Effect.dealDamage 1))).isSorcery
#guard mountain.colors.isColorless
#guard grizzlyBears.colors.isMonocolored
#guard grizzlyBears.hasSorcerySpeed
#guard !lightningBolt.hasSorcerySpeed
#guard !mountain.hasSorcerySpeed
#guard (ragingGoblin.summary.splitOn "haste").length > 1
#guard (llanowarElves.summary.splitOn "{T}: Add {G}").length > 1
#guard (lightningBolt.summary.splitOn "deals 3 damage").length > 1
#guard (lightningBolt.summary.splitOn "{R}").length > 1
#guard (mountain.summary.splitOn "{T}: Add {R}").length > 1
#guard (mountain.summary.splitOn "{0}").length == 1
#guard mountain.summary == "Mountain Basic Land — Mountain ({T}: Add {R}.)"
#guard (plains.summary.splitOn "({T}: Add {W}.)").length > 1
#guard (island.summary.splitOn "({T}: Add {U}.)").length > 1
#guard (swamp.summary.splitOn "({T}: Add {B}.)").length > 1
#guard (forest.summary.splitOn "({T}: Add {G}.)").length > 1
#guard ragingGoblin.hasSimpleKeyword .haste
#guard giantSpider.hasSimpleKeyword .reach
#guard (giantSpider.summary.splitOn "reach").length > 1
#guard giantGrowth.spellEffect == some (Effect.pump 3 3)
#guard giantGrowth.isInstant
#guard (equipAbility (ManaCost.ofGeneric 3)).isSorcerySpeed
#guard (equipAbility (ManaCost.ofGeneric 3)).effect ==
  Effect.attachToTargetCreatureYouControl
#guard (activated (Effect.sourceGets 2 2) (payLife := 2) (turnLimit? := some 1)).cost.payLife == 2
#guard (activated (Effect.sourceGets 2 2) (payLife := 2) (turnLimit? := some 1)).isOnceEachTurn
#guard (adventure "Spew Flame" (ManaCost.ofGenericAndColor 4 .red) ""
  (Effect.dealDamageToCreature 5)).subtypes.any (· == "Adventure")
#guard lightningBolt.hasType .instant
#guard !grizzlyBears.hasType .instant
#guard lightningBolt.hasCastKind .burn
#guard giantGrowth.hasCastKind .pump
#guard !lightningBolt.hasCastKind .pump
#guard (lightningBolt.spellEffect.map Effect.castKind) == some .burn
#guard (giantGrowth.spellEffect.map Effect.castKind) == some .pump
#guard (land "Silent Passage" "{T}: Add {C}.").isLand
#guard (artifact "Silent Spear" (ManaCost.ofGeneric 1) ""
  (subtypes := #["Equipment"])).isEquipment
#guard (equipment "Silent Blade" (ManaCost.ofGeneric 1) ""
  (ManaCost.ofGeneric 2)).isEquipment
#guard (equipment "Silent Blade" (ManaCost.ofGeneric 1) ""
  (ManaCost.ofGeneric 2)).activatedAbilities ==
  #[equipAbility (ManaCost.ofGeneric 2)]
#guard (artifactCreature "Silent Construct" ManaCost.empty #["Construct"] 1 1
  (supertypes := #[.legendary])).hasSupertype .legendary
#guard (artifactCreature "Silent Construct" ManaCost.empty #["Construct"] 1 1
  (supertypes := #[.legendary])).hasType .artifact
#guard (artifactCreature "Silent Construct" ManaCost.empty #["Construct"] 1 1
  (supertypes := #[.legendary])).hasType .creature
#guard (gainLifeDualLand "Silent Plaza" .blue .black).entersTappedUnconditionally
#guard (conditionalDualLand "Silent Keep" .blue .black).activatedAbilities[0]?.bind (·.manaProduction?) ==
  some { spec := .fixedOne .colorless }
#guard (powerUpAbility (Effect.putPlusOnePlusOneOnSource 1) (ManaCost.ofGeneric 3)).isPowerUp
#guard (KeywordAbility.mergeAll #[#[Keyword.flying], #[Keyword.trample], #[Keyword.haste]]) ==
  #[Keyword.flying, Keyword.trample, Keyword.haste]
#guard (aura "Silent Strands" (ManaCost.ofGenericAndColor 3 .green) "").isAura

end Mtg.Engine.Catalog
