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

/-- A basic land whose name is also its land type (CR 305.6). -/
def basicLand (landName : String) (color : Color) : CardDef := {
  name := landName
  types := #[.land]
  subtypes := #[landName]
  supertypes := #[.basic]
  oracleText := s!"\{T}: Add \{{color.letter}}."
}

def plains : CardDef := basicLand "Plains" .white
def island : CardDef := basicLand "Island" .blue
def swamp : CardDef := basicLand "Swamp" .black
def mountain : CardDef := basicLand "Mountain" .red
def forest : CardDef := basicLand "Forest" .green

def grizzlyBears : CardDef := {
  name := "Grizzly Bears"
  manaCost := ManaCost.ofGenericAndColor 1 .green
  types := #[.creature]
  subtypes := #["Bear"]
  oracleText := ""
  power := some 2
  toughness := some 2
}

def grayOgre : CardDef := {
  name := "Gray Ogre"
  manaCost := ManaCost.ofGenericAndColor 2 .red
  types := #[.creature]
  subtypes := #["Ogre"]
  power := some 2
  toughness := some 2
}

def hillGiant : CardDef := {
  name := "Hill Giant"
  manaCost := ManaCost.ofGenericAndColor 3 .red
  types := #[.creature]
  subtypes := #["Giant"]
  power := some 3
  toughness := some 3
}

def canyonMinotaur : CardDef := {
  name := "Canyon Minotaur"
  manaCost := ManaCost.ofGenericAndColor 3 .red
  types := #[.creature]
  subtypes := #["Minotaur"]
  power := some 3
  toughness := some 3
}

def ragingGoblin : CardDef := {
  name := "Raging Goblin"
  manaCost := ManaCost.ofColor .red
  types := #[.creature]
  subtypes := #["Goblin"]
  oracleText := "Haste"
  power := some 1
  toughness := some 1
  keywords := { Keywords.none with haste := true }
}

def llanowarElves : CardDef := {
  name := "Llanowar Elves"
  manaCost := ManaCost.ofColor .green
  types := #[.creature]
  subtypes := #["Elf", "Druid"]
  oracleText := "{T}: Add {G}."
  power := some 1
  toughness := some 1
  tapAddMana := #[.colored .green]
}

def crawWurm : CardDef := {
  name := "Craw Wurm"
  manaCost := ManaCost.ofGenericAndColor 4 .green
  types := #[.creature]
  subtypes := #["Wurm"]
  power := some 6
  toughness := some 4
}

def centaurCourser : CardDef := {
  name := "Centaur Courser"
  manaCost := ManaCost.ofGenericAndColor 2 .green
  types := #[.creature]
  subtypes := #["Centaur"]
  power := some 3
  toughness := some 3
}

def rumblingBaloth : CardDef := {
  name := "Rumbling Baloth"
  manaCost := ManaCost.ofGenericAndColors 2 [.green, .green]
  types := #[.creature]
  subtypes := #["Beast"]
  power := some 4
  toughness := some 4
}

def giantSpider : CardDef := {
  name := "Giant Spider"
  manaCost := ManaCost.ofGenericAndColor 3 .green
  types := #[.creature]
  subtypes := #["Spider"]
  oracleText := "Reach"
  power := some 2
  toughness := some 4
  keywords := { Keywords.none with reach := true }
}

def lightningBolt : CardDef := {
  name := "Lightning Bolt"
  manaCost := ManaCost.ofColor .red
  types := #[.instant]
  oracleText := "Lightning Bolt deals 3 damage to any target."
  spellEffect := some (.dealDamage 3)
}

def shock : CardDef := {
  name := "Shock"
  manaCost := ManaCost.ofColor .red
  types := #[.instant]
  oracleText := "Shock deals 2 damage to any target."
  spellEffect := some (.dealDamage 2)
}

def giantGrowth : CardDef := {
  name := "Giant Growth"
  manaCost := ManaCost.ofColor .green
  types := #[.instant]
  oracleText := "Target creature gets +3/+3 until end of turn."
  spellEffect := some (.pump 3 3)
}

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
#guard (mountain.summary.splitOn "{T}: Add {R}").length > 1
#guard (giantSpider.summary.splitOn "reach").length > 1

end Mtg.Engine.Catalog
