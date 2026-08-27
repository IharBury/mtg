import Mtg.Engine.Card

/-!
# Sample cards

A small Oracle-faithful catalog used by engine tests. The engine itself is
card-agnostic; these definitions just exercise the rules we model.

Cards from Magic: The Gathering | The Hobbit Welcome Decks live in
`Mtg.Engine.Catalog.Hobbit`. Decklists that use them live in `Mtg.Demo`.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

/-- Fill a `CardDef` with the fields catalogs actually set. Type-specific
helpers (`creature`, `instant`, …) are thin wrappers so a new card is one
call instead of repeating `types`, `power := some`, and empty arrays. -/
def card (name : String) (types : Array CardType)
    (manaCost : ManaCost := ManaCost.empty) (subtypes : Array Subtype := #[])
    (oracleText : String := "") (power : Option Int := none)
    (toughness : Option Int := none) (keywords : Keywords := Keywords.none)
    (supertypes : Array Supertype := #[])
    (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0)
    (tapAddMana : Array ManaType := #[])
    (tapAddManaForEach : Array TapAddForEach := #[])
    (tapAddAnyColorEqualToPower : Bool := false)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (adventure : Option AdventureFace := none) : CardDef := {
  name, manaCost, types, subtypes, oracleText, power, toughness, keywords,
  supertypes, spellEffect, spellModes, additionalCostSacrificeArtifactOrCreature,
  additionalCostOrPayGeneric, costReductionIfCreatureDied, costReductionIfTargetDamaged,
  tapAddMana, tapAddManaForEach, tapAddAnyColorEqualToPower, staticAbilities,
  triggeredAbilities, activatedAbilities, adventure
}

/-- A basic land whose name is also its land type (CR 305.6). -/
def basicLand (landName : String) (color : Color) : CardDef :=
  card landName #[.land] (subtypes := #[landName]) (supertypes := #[.basic])
    (oracleText := s!"\{T}: Add \{{color.letter}}.")

def plains : CardDef := basicLand "Plains" .white
def island : CardDef := basicLand "Island" .blue
def swamp : CardDef := basicLand "Swamp" .black
def mountain : CardDef := basicLand "Mountain" .red
def forest : CardDef := basicLand "Forest" .green

/-- A creature used by engine tests and the Hobbit catalog. -/
def creature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Keywords := Keywords.none)
    (tapAddMana : Array ManaType := #[])
    (supertypes : Array Supertype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (tapAddManaForEach : Array TapAddForEach := #[])
    (tapAddAnyColorEqualToPower : Bool := false)
    (adventure : Option AdventureFace := none)
    (costReductionIfCreatureDied : Nat := 0) : CardDef :=
  card name #[.creature] manaCost subtypes oracleText (some power) (some toughness)
    keywords supertypes (tapAddMana := tapAddMana)
    (tapAddManaForEach := tapAddManaForEach)
    (tapAddAnyColorEqualToPower := tapAddAnyColorEqualToPower)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities) (adventure := adventure)
    (costReductionIfCreatureDied := costReductionIfCreatureDied)

/-- Instant or sorcery with an optional one-shot effect or modal modes. -/
def spellCard (cardType : CardType) (name : String) (manaCost : ManaCost)
    (oracleText : String) (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0) : CardDef :=
  card name #[cardType] manaCost (oracleText := oracleText)
    (spellEffect := spellEffect) (spellModes := spellModes)
    (additionalCostSacrificeArtifactOrCreature :=
      additionalCostSacrificeArtifactOrCreature)
    (additionalCostOrPayGeneric := additionalCostOrPayGeneric)
    (costReductionIfCreatureDied := costReductionIfCreatureDied)
    (costReductionIfTargetDamaged := costReductionIfTargetDamaged)

/-- An instant, optionally with a one-shot effect or modal modes. -/
def instant (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0) : CardDef :=
  spellCard .instant name manaCost oracleText spellEffect spellModes
    additionalCostSacrificeArtifactOrCreature additionalCostOrPayGeneric
    costReductionIfCreatureDied costReductionIfTargetDamaged

/-- A sorcery, optionally with a one-shot effect or modal modes. -/
def sorcery (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0) : CardDef :=
  spellCard .sorcery name manaCost oracleText spellEffect spellModes
    additionalCostSacrificeArtifactOrCreature additionalCostOrPayGeneric
    costReductionIfCreatureDied costReductionIfTargetDamaged

/-- A non-Aura enchantment. -/
def enchantment (name : String) (manaCost : ManaCost) (oracleText : String)
    (keywords : Keywords := Keywords.none)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[]) : CardDef :=
  card name #[.enchantment] manaCost subtypes oracleText (keywords := keywords)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)

/-- An Aura enchantment (CR 303.4). -/
def aura (name : String) (manaCost : ManaCost) (oracleText : String)
    (keywords : Keywords := Keywords.none)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[]) : CardDef :=
  enchantment name manaCost oracleText keywords staticAbilities triggeredAbilities
    (subtypes := #["Aura"])

/-- An artifact, including Equipment. -/
def artifact (name : String) (manaCost : ManaCost) (oracleText : String)
    (subtypes : Array Subtype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[]) : CardDef :=
  card name #[.artifact] manaCost subtypes oracleText
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)

/-- A nonbasic land. -/
def land (name : String) (oracleText : String)
    (tapAddMana : Array ManaType := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[]) : CardDef :=
  card name #[.land] (subtypes := subtypes) (oracleText := oracleText)
    (tapAddMana := tapAddMana) (activatedAbilities := activatedAbilities)

/-- An activated ability (CR 602.1). -/
def activated (effect : AbilityEffect) (mana : ManaCost := ManaCost.empty)
    (tap : Bool := false) (sacrificeSource : Bool := false)
    (sacrificeAnotherCreatureOrArtifact : Bool := false)
    (onlyAsSorcery : Bool := false) (onlyDuringYourTurn : Bool := false)
    (onceEachTurn : Bool := false)
    (otherModes : Array AbilityEffect := #[]) (payLife : Nat := 0)
    (activateFromGraveyard : Bool := false)
    (onlyIfYouControlLegendary : Bool := false) :
    ActivatedAbility := {
  cost := { mana, tap, sacrificeSource, sacrificeAnotherCreatureOrArtifact, payLife }
  effect, otherModes, onlyAsSorcery, onlyDuringYourTurn, onceEachTurn
  activateFromGraveyard, onlyIfYouControlLegendary
}

/-- Equip `mana`: attach to target creature you control, only as a sorcery. -/
def equipAbility (mana : ManaCost) : ActivatedAbility :=
  activated .attachToTargetCreatureYouControl mana (onlyAsSorcery := true)

/-- Adventure characteristics used while the card is a spell (CR 715.2). -/
def adventure (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : SpellEffect) : AdventureFace := {
  name, manaCost, types := #[.sorcery], subtypes := #["Adventure"],
  oracleText, spellEffect := some spellEffect
}

/-- A red instant that deals `amount` damage to any target. -/
def damageInstant (name : String) (amount : Nat) : CardDef :=
  instant name (ManaCost.ofColor .red)
    s!"{name} deals {amount} damage to any target."
    (some (.dealDamage amount))

def grizzlyBears : CardDef :=
  creature "Grizzly Bears" (ManaCost.ofGenericAndColor 1 .green) #["Bear"] 2 2

def grayOgre : CardDef :=
  creature "Gray Ogre" (ManaCost.ofGenericAndColor 2 .red) #["Ogre"] 2 2

def hillGiant : CardDef :=
  creature "Hill Giant" (ManaCost.ofGenericAndColor 3 .red) #["Giant"] 3 3

def canyonMinotaur : CardDef :=
  creature "Canyon Minotaur" (ManaCost.ofGenericAndColor 3 .red) #["Minotaur"] 3 3

def ragingGoblin : CardDef :=
  creature "Raging Goblin" (ManaCost.ofColor .red) #["Goblin"] 1 1
    (oracleText := "Haste") (keywords := Keyword.haste)

def llanowarElves : CardDef :=
  creature "Llanowar Elves" (ManaCost.ofColor .green) #["Elf", "Druid"] 1 1
    (oracleText := "{T}: Add {G}.") (tapAddMana := #[.colored .green])

def crawWurm : CardDef :=
  creature "Craw Wurm" (ManaCost.ofGenericAndColor 4 .green) #["Wurm"] 6 4

def centaurCourser : CardDef :=
  creature "Centaur Courser" (ManaCost.ofGenericAndColor 2 .green) #["Centaur"] 3 3

def rumblingBaloth : CardDef :=
  creature "Rumbling Baloth" (ManaCost.ofGenericAndColors 2 [.green, .green])
    #["Beast"] 4 4

def giantSpider : CardDef :=
  creature "Giant Spider" (ManaCost.ofGenericAndColor 3 .green) #["Spider"] 2 4
    (oracleText := "Reach") (keywords := Keyword.reach)

def lightningBolt : CardDef := damageInstant "Lightning Bolt" 3

def shock : CardDef := damageInstant "Shock" 2

def giantGrowth : CardDef :=
  instant "Giant Growth" (ManaCost.ofColor .green)
    "Target creature gets +3/+3 until end of turn."
    (some (.pump 3 3))

/-- Repeat a card `n` times. -/
def copies (n : Nat) (c : CardDef) : Array CardDef :=
  Array.replicate n c

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
#guard mountain.summary == "Mountain Basic Land — Mountain {T}: Add {R}."
#guard (giantSpider.summary.splitOn "reach").length > 1
#guard giantGrowth.spellEffect == some (.pump 3 3)
#guard giantGrowth.isInstant
#guard (equipAbility (ManaCost.ofGeneric 3)).onlyAsSorcery
#guard (equipAbility (ManaCost.ofGeneric 3)).effect == .attachToTargetCreatureYouControl
#guard (activated (.sourceGets 2 2) (payLife := 2) (onceEachTurn := true)).cost.payLife == 2
#guard (activated (.sourceGets 2 2) (payLife := 2) (onceEachTurn := true)).onceEachTurn
#guard (adventure "Spew Flame" (ManaCost.ofGenericAndColor 4 .red) ""
  (.dealDamageToCreature 5)).subtypes.any (· == "Adventure")
#guard lightningBolt.hasType .instant
#guard !grizzlyBears.hasType .instant
#guard lightningBolt.hasCastKind .burn
#guard giantGrowth.hasCastKind .pump
#guard !lightningBolt.hasCastKind .pump
#guard (lightningBolt.spellEffect.map SpellEffect.castKind) == some .burn
#guard (giantGrowth.spellEffect.map SpellEffect.castKind) == some .pump
#guard (land "Silent Passage" "{T}: Add {C}." (tapAddMana := #[.colorless])).isLand
#guard (artifact "Silent Spear" (ManaCost.ofGeneric 1) ""
  (subtypes := #["Equipment"])).isEquipment
#guard (aura "Silent Strands" (ManaCost.ofGenericAndColor 3 .green) "").isAura

end Mtg.Engine.Catalog
