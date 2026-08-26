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

/-- A creature used by engine tests. -/
def creature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Keywords := Keywords.none)
    (tapAddMana : Array ManaType := #[]) : CardDef := {
  name, manaCost, types := #[.creature], subtypes, oracleText,
  power := some power, toughness := some toughness, keywords, tapAddMana
}

/-- A red instant that deals `amount` damage to any target. -/
def damageInstant (name : String) (amount : Nat) : CardDef := {
  name
  manaCost := ManaCost.ofColor .red
  types := #[.instant]
  oracleText := s!"{name} deals {amount} damage to any target."
  spellEffect := some (.dealDamage amount)
}

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
    (oracleText := "Haste") (keywords := { Keywords.none with haste := true })

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
    (oracleText := "Reach") (keywords := { Keywords.none with reach := true })

def lightningBolt : CardDef := damageInstant "Lightning Bolt" 3

def shock : CardDef := damageInstant "Shock" 2

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
