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

end Mtg.Engine
