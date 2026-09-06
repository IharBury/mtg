import Mtg.Engine.Color

/-!
# Type line (CR 205, section 3)

A card’s type line contains its card type(s), any applicable subtypes, and
any applicable supertypes.
-/

namespace Mtg.Engine

/-- Card types listed in CR 300.1 / 205.2a, plus additional types from section 3. -/
inductive CardType where
  | artifact
  | battle
  | creature
  | enchantment
  | instant
  | land
  | planeswalker
  | sorcery
  | kindred
  | dungeon
  | plane
  | phenomenon
  | vanguard
  | scheme
  | conspiracy
deriving DecidableEq, Repr, Inhabited, BEq

namespace CardType

def englishName : CardType → String
  | .artifact => "Artifact"
  | .battle => "Battle"
  | .creature => "Creature"
  | .enchantment => "Enchantment"
  | .instant => "Instant"
  | .land => "Land"
  | .planeswalker => "Planeswalker"
  | .sorcery => "Sorcery"
  | .kindred => "Kindred"
  | .dungeon => "Dungeon"
  | .plane => "Plane"
  | .phenomenon => "Phenomenon"
  | .vanguard => "Vanguard"
  | .scheme => "Scheme"
  | .conspiracy => "Conspiracy"

instance : ToString CardType where
  toString := englishName

/-- Permanent types (CR 110.4). Instant and sorcery cards can’t be permanents. -/
def isPermanentType : CardType → Bool
  | .artifact | .battle | .creature | .enchantment | .land | .planeswalker => true
  | _ => false

/-- Instant and sorcery share “spell-speed” restrictions unless flash is present. -/
def isInstantOrSorcery : CardType → Bool
  | .instant | .sorcery => true
  | _ => false

end CardType

/-- Supertypes (CR 205.4). -/
inductive Supertype where
  | basic
  | legendary
  | ongoing
  | snow
  | world
deriving DecidableEq, Repr, Inhabited, BEq

/-- Printed-card alias for `Supertype` (CR 205.4). -/
abbrev CardSupertype := Supertype

namespace Supertype

def englishName : Supertype → String
  | .basic => "Basic"
  | .legendary => "Legendary"
  | .ongoing => "Ongoing"
  | .snow => "Snow"
  | .world => "World"

instance : ToString Supertype where
  toString := englishName

end Supertype

/-- Subtype as printed on the type line. Basic land types are the five listed in CR 305.6. -/
abbrev Subtype := String

/-- Named subtypes used when composing a `TraditionalCardDefinition`. -/
inductive CardSubtype where
  | adventure
  | advisor
  | alien
  | ape
  | arcane
  | archer
  | army
  | artificer
  | assassin
  | aura
  | avatar
  | barbarian
  | bard
  | bat
  | bear
  | beast
  | berserker
  | bird
  | cat
  | centaur
  | citizen
  | cleric
  | clue
  | demigod
  | detective
  | dinosaur
  | doctor
  | dog
  | dragon
  | druid
  | dwarf
  | elemental
  | elephant
  | elf
  | elk
  | equipment
  | eternal
  | food
  | forest
  | frog
  | gamma
  | gate
  | giant
  | goblin
  | god
  | halfling
  | hero
  | horror
  | horse
  | human
  | infinity
  | inhuman
  | insect
  | island
  | knight
  | kree
  | mercenary
  | merfolk
  | minotaur
  | mountain
  | mutant
  | nightmare
  | ninja
  | noble
  | ogre
  | orc
  | peasant
  | performer
  | pilot
  | pirate
  | plains
  | plan
  | rabbit
  | ranger
  | robot
  | rogue
  | saga
  | samurai
  | scientist
  | scout
  | shaman
  | shapeshifter
  | skrull
  | snake
  | soldier
  | sorcerer
  | spider
  | spirit
  | spy
  | squirrel
  | stone
  | swamp
  | troll
  | treasure
  | vampire
  | vehicle
  | villain
  | warlock
  | warrior
  | whale
  | wizard
  | wolf
  | wraith
  | wurm
  | zombie
deriving DecidableEq, Repr, Inhabited, BEq

namespace CardSubtype

def toString : CardSubtype → String
  | .adventure => "Adventure"
  | .advisor => "Advisor"
  | .alien => "Alien"
  | .ape => "Ape"
  | .arcane => "Arcane"
  | .archer => "Archer"
  | .army => "Army"
  | .artificer => "Artificer"
  | .assassin => "Assassin"
  | .aura => "Aura"
  | .avatar => "Avatar"
  | .barbarian => "Barbarian"
  | .bard => "Bard"
  | .bat => "Bat"
  | .bear => "Bear"
  | .beast => "Beast"
  | .berserker => "Berserker"
  | .bird => "Bird"
  | .cat => "Cat"
  | .centaur => "Centaur"
  | .citizen => "Citizen"
  | .cleric => "Cleric"
  | .clue => "Clue"
  | .demigod => "Demigod"
  | .detective => "Detective"
  | .dinosaur => "Dinosaur"
  | .doctor => "Doctor"
  | .dog => "Dog"
  | .dragon => "Dragon"
  | .druid => "Druid"
  | .dwarf => "Dwarf"
  | .elemental => "Elemental"
  | .elephant => "Elephant"
  | .elf => "Elf"
  | .elk => "Elk"
  | .equipment => "Equipment"
  | .eternal => "Eternal"
  | .food => "Food"
  | .forest => "Forest"
  | .frog => "Frog"
  | .gamma => "Gamma"
  | .gate => "Gate"
  | .giant => "Giant"
  | .goblin => "Goblin"
  | .god => "God"
  | .halfling => "Halfling"
  | .hero => "Hero"
  | .horror => "Horror"
  | .horse => "Horse"
  | .human => "Human"
  | .infinity => "Infinity"
  | .inhuman => "Inhuman"
  | .insect => "Insect"
  | .island => "Island"
  | .knight => "Knight"
  | .kree => "Kree"
  | .mercenary => "Mercenary"
  | .merfolk => "Merfolk"
  | .minotaur => "Minotaur"
  | .mountain => "Mountain"
  | .mutant => "Mutant"
  | .nightmare => "Nightmare"
  | .ninja => "Ninja"
  | .noble => "Noble"
  | .ogre => "Ogre"
  | .orc => "Orc"
  | .peasant => "Peasant"
  | .performer => "Performer"
  | .pilot => "Pilot"
  | .pirate => "Pirate"
  | .plains => "Plains"
  | .plan => "Plan"
  | .rabbit => "Rabbit"
  | .ranger => "Ranger"
  | .robot => "Robot"
  | .rogue => "Rogue"
  | .saga => "Saga"
  | .samurai => "Samurai"
  | .scientist => "Scientist"
  | .scout => "Scout"
  | .shaman => "Shaman"
  | .shapeshifter => "Shapeshifter"
  | .skrull => "Skrull"
  | .snake => "Snake"
  | .soldier => "Soldier"
  | .sorcerer => "Sorcerer"
  | .spider => "Spider"
  | .spirit => "Spirit"
  | .spy => "Spy"
  | .squirrel => "Squirrel"
  | .stone => "Stone"
  | .swamp => "Swamp"
  | .troll => "Troll"
  | .treasure => "Treasure"
  | .vampire => "Vampire"
  | .vehicle => "Vehicle"
  | .villain => "Villain"
  | .warlock => "Warlock"
  | .warrior => "Warrior"
  | .whale => "Whale"
  | .wizard => "Wizard"
  | .wolf => "Wolf"
  | .wraith => "Wraith"
  | .wurm => "Wurm"
  | .zombie => "Zombie"

instance : ToString CardSubtype where
  toString := CardSubtype.toString

instance : Coe CardSubtype Subtype where
  coe := toString

end CardSubtype

/-- The five basic land types (CR 305.6). -/
def basicLandTypes : List Subtype :=
  ["Plains", "Island", "Swamp", "Mountain", "Forest"]

/-- Artifact, enchantment, and land subtypes (CR 205.3g–i). A “becomes a
`[creature types] artifact creature`” effect keeps these and replaces
creature types (MSH 88). -/
def isNoncreatureSubtype (s : Subtype) : Bool :=
  s == "Equipment" || s == "Vehicle" || s == "Food" || s == "Clue" ||
    s == "Treasure" || s == "Blood" || s == "Gold" || s == "Map" ||
    s == "Powerstone" || s == "Aura" || s == "Saga" || s == "Plan" ||
    s == "Case" || s == "Role" || s == "Shrine" || s == "Class" ||
    s == "Background" || s == "Room" || s == "Lesson" || s == "Cartouche" ||
    s == "Curse" || s == "Rune" || s == "Shard" || s == "Sphere" ||
    basicLandTypes.any (· == s)

/-- Intrinsic mana produced by a basic land type (CR 305.6). -/
def manaForBasicLandType : Subtype → Option Color
  | "Plains" => some .white
  | "Island" => some .blue
  | "Swamp" => some .black
  | "Mountain" => some .red
  | "Forest" => some .green
  | _ => none

/-- Oracle-style type line from supertypes, types, and subtypes (CR 205.1). -/
def formatTypeLine (supertypes : Array Supertype) (types : Array CardType)
    (subtypes : Array Subtype) : String :=
  let super := String.intercalate " " (supertypes.toList.map toString)
  let types := String.intercalate " " (types.toList.map toString)
  let sub := String.intercalate " " subtypes.toList
  let head :=
    if super.isEmpty then types else s!"{super} {types}"
  if sub.isEmpty then head else s!"{head} — {sub}"

#guard isNoncreatureSubtype "Equipment"
#guard isNoncreatureSubtype "Plan"
#guard !isNoncreatureSubtype "Human"
#guard !isNoncreatureSubtype "Construct"
#guard basicLandTypes.length == 5
#guard CardType.creature.isPermanentType
#guard !CardType.instant.isPermanentType
#guard CardType.sorcery.isInstantOrSorcery
#guard formatTypeLine #[.basic] #[.land] #["Forest"] == "Basic Land — Forest"
#guard formatTypeLine #[] #[.creature] #["Bear"] == "Creature — Bear"
#guard formatTypeLine #[] #[.instant] #[] == "Instant"
#guard formatTypeLine #[] #[.creature] #[CardSubtype.toString .noble] ==
  "Creature — Noble"
#guard formatTypeLine #[] #[.enchantment] #[CardSubtype.toString .plan] ==
  "Enchantment — Plan"
#guard formatTypeLine #[] #[.enchantment] #[CardSubtype.toString .saga] ==
  "Enchantment — Saga"
#guard formatTypeLine #[.legendary] #[.land] #[CardSubtype.toString .gate] ==
  "Legendary Land — Gate"
#guard formatTypeLine #[] #[.instant] #[CardSubtype.toString .arcane] ==
  "Instant — Arcane"
#guard CardSubtype.toString .forest == "Forest"
#guard CardSubtype.toString .plains == "Plains"
#guard CardSubtype.toString .island == "Island"
#guard CardSubtype.toString .swamp == "Swamp"
#guard CardSubtype.toString .mountain == "Mountain"
#guard CardSubtype.toString .elephant == "Elephant"
#guard CardSubtype.toString .vehicle == "Vehicle"
#guard CardSubtype.toString .aura == "Aura"
#guard CardSubtype.toString .elemental == "Elemental"
#guard CardSubtype.toString .pilot == "Pilot"
#guard CardSubtype.toString .orc == "Orc"
#guard CardSubtype.toString .pirate == "Pirate"
#guard CardSubtype.toString .robot == "Robot"
#guard CardSubtype.toString .spirit == "Spirit"
#guard CardSubtype.toString .zombie == "Zombie"
#guard CardSubtype.toString .archer == "Archer"
#guard CardSubtype.toString .dinosaur == "Dinosaur"
#guard CardSubtype.toString .rabbit == "Rabbit"
#guard CardSubtype.toString .alien == "Alien"
#guard CardSubtype.toString .ape == "Ape"
#guard CardSubtype.toString .arcane == "Arcane"
#guard CardSubtype.toString .army == "Army"
#guard CardSubtype.toString .artificer == "Artificer"
#guard CardSubtype.toString .assassin == "Assassin"
#guard CardSubtype.toString .barbarian == "Barbarian"
#guard CardSubtype.toString .berserker == "Berserker"
#guard CardSubtype.toString .cat == "Cat"
#guard CardSubtype.toString .demigod == "Demigod"
#guard CardSubtype.toString .detective == "Detective"
#guard CardSubtype.toString .doctor == "Doctor"
#guard CardSubtype.toString .dog == "Dog"
#guard CardSubtype.toString .elk == "Elk"
#guard CardSubtype.toString .eternal == "Eternal"
#guard CardSubtype.toString .frog == "Frog"
#guard CardSubtype.toString .gamma == "Gamma"
#guard CardSubtype.toString .gate == "Gate"
#guard CardSubtype.toString .horse == "Horse"
#guard CardSubtype.toString .infinity == "Infinity"
#guard CardSubtype.toString .inhuman == "Inhuman"
#guard CardSubtype.toString .mercenary == "Mercenary"
#guard CardSubtype.toString .mutant == "Mutant"
#guard CardSubtype.toString .nightmare == "Nightmare"
#guard CardSubtype.toString .ninja == "Ninja"
#guard CardSubtype.toString .noble == "Noble"
#guard CardSubtype.toString .peasant == "Peasant"
#guard CardSubtype.toString .performer == "Performer"
#guard CardSubtype.toString .plan == "Plan"
#guard CardSubtype.toString .saga == "Saga"
#guard CardSubtype.toString .samurai == "Samurai"
#guard CardSubtype.toString .scientist == "Scientist"
#guard CardSubtype.toString .skrull == "Skrull"
#guard CardSubtype.toString .snake == "Snake"
#guard CardSubtype.toString .sorcerer == "Sorcerer"
#guard CardSubtype.toString .squirrel == "Squirrel"
#guard CardSubtype.toString .stone == "Stone"
#guard CardSubtype.toString .troll == "Troll"
#guard CardSubtype.toString .vampire == "Vampire"
#guard CardSubtype.toString .warlock == "Warlock"
#guard CardSubtype.toString .whale == "Whale"
#guard CardSubtype.toString .treasure == "Treasure"
#guard CardSubtype.toString .food == "Food"
#guard CardSubtype.toString .clue == "Clue"

end Mtg.Engine
