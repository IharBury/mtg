import Std.Data.HashMap
import Mtg.Engine.Color

/-!
# Type line (CR 205, section 3)

A card’s type line contains its card type(s), any applicable subtypes, and
any applicable supertypes.
-/

namespace Mtg.Engine

/-- Card types, exactly the list in CR 205.2a / 300.1. -/
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

/-- Plural Oracle spelling of each card type (CR 205.2a). -/
def pluralName : CardType → String
  | .artifact => "artifacts"
  | .battle => "battles"
  | .conspiracy => "conspiracies"
  | .creature => "creatures"
  | .dungeon => "dungeons"
  | .enchantment => "enchantments"
  | .instant => "instants"
  | .kindred => "kindreds"
  | .land => "lands"
  | .phenomenon => "phenomena"
  | .plane => "planes"
  | .planeswalker => "planeswalkers"
  | .scheme => "schemes"
  | .sorcery => "sorceries"
  | .vanguard => "vanguards"

/-- Every card type in CR 205.2a, in that order. -/
def all : List CardType := [
  .artifact, .battle, .conspiracy, .creature, .dungeon, .enchantment, .instant,
  .kindred, .land, .phenomenon, .plane, .planeswalker, .scheme, .sorcery, .vanguard
]

/-- A printed card-type word, singular or plural, in any case. -/
def ofOracle? (s : String) : Option CardType :=
  let s := s.map Char.toLower
  all.find? fun t =>
    t.englishName.map Char.toLower == s || t.pluralName.map Char.toLower == s

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

/-- Every supertype in CR 205.4a, in that order. -/
def all : List Supertype :=
  [.basic, .legendary, .ongoing, .snow, .world]

/-- A printed supertype word, in any case. -/
def ofOracle? (s : String) : Option Supertype :=
  let s := s.map Char.toLower
  all.find? fun t => t.englishName.map Char.toLower == s

end Supertype

/-- Subtype as printed on the type line. -/
abbrev Subtype := String

/-- The five basic land types (CR 305.6), in the order used by mana abilities. -/
def basicLandTypes : List Subtype :=
  ["Plains", "Island", "Swamp", "Mountain", "Forest"]

/-- Which card type a CR 205.3 subtype belongs to.
`spell` is shared by instants and sorceries (205.3k). `creature` is shared by
creatures and kindreds (205.3m). -/
inductive SubtypeClass where
  | artifact
  | enchantment
  | land
  | planeswalker
  | spell
  | creature
  | planar
  | dungeon
  | battle
deriving DecidableEq, Repr, BEq

def artifactTypes : List String := [
  "Attraction", "Blood", "Bobblehead", "Book", "Clue", "Contraption",
  "Equipment", "Food", "Fortification", "Gold", "Heartwood", "Incubator",
  "Infinity", "Junk", "Lander", "Map", "Mutagen", "Powerstone",
  "Spacecraft", "Stone", "Treasure", "Vehicle", "Vibranium"
]

def enchantmentTypes : List String := [
  "Aura", "Background", "Cartouche", "Case", "Class", "Curse",
  "Plan", "Role", "Room", "Rune", "Saga", "Shard",
  "Shrine"
]

def landTypes : List String := [
  "Cave", "Desert", "Forest", "Gate", "Island", "Lair",
  "Locus", "Mine", "Mountain", "Plains", "Planet", "Power-Plant",
  "Sphere", "Swamp", "Tower", "Town", "Urza's"
]

def planeswalkerTypes : List String := [
  "Ajani", "Aminatou", "Angrath", "Arlinn", "Ashiok", "Bahamut",
  "Basri", "Bolas", "Calix", "Chandra", "Comet", "Dack",
  "Dakkon", "Daretti", "Davriel", "Dellian", "Dihada", "Domri",
  "Dovin", "Ellywick", "Elminster", "Elspeth", "Estrid", "Freyalise",
  "Garruk", "Gideon", "Grist", "Guff", "Huatli", "Jace",
  "Jared", "Jaya", "Jeska", "Kaito", "Karn", "Kasmina",
  "Kaya", "Kiora", "Koth", "Liliana", "Lolth", "Lukka",
  "Minsc", "Mordenkainen", "Nahiri", "Narset", "Niko", "Nissa",
  "Nixilis", "Oko", "Quintorius", "Ral", "Rowan", "Saheeli",
  "Samut", "Sarkhan", "Serra", "Sivitri", "Sorin", "Szat",
  "Tamiyo", "Tasha", "Teferi", "Teyo", "Tezzeret", "Tibalt",
  "Tyvar", "Ugin", "Urza", "Venser", "Vivien", "Vraska",
  "Vronos", "Will", "Windgrace", "Wrenn", "Xenagos", "Yanggu",
  "Yanling", "Zariel"
]

def spellTypes : List String := [
  "Adventure", "Arcane", "Lesson", "Omen", "Trap"
]

def creatureTypes : List String := [
  "Time Lord", "Advisor", "Aetherborn", "Alien", "Ally", "Angel",
  "Antelope", "Ape", "Archer", "Archon", "Armadillo", "Army",
  "Artificer", "Assassin", "Assembly-Worker", "Astartes", "Atog", "Aurochs",
  "Avatar", "Azra", "Badger", "Balloon", "Barbarian", "Bard",
  "Basilisk", "Bat", "Bear", "Beast", "Beaver", "Beeble",
  "Beholder", "Berserker", "Bird", "Bison", "Blinkmoth", "Boar",
  "Bringer", "Brushwagg", "Camarid", "Camel", "Capybara", "Caribou",
  "Carrier", "Cat", "Centaur", "Child", "Chimera", "Citizen",
  "Cleric", "Clown", "Cockatrice", "Construct", "Coward", "Coyote",
  "Crab", "Crocodile", "C'tan", "Custodes", "Cyberman", "Cyclops",
  "Dalek", "Dauthi", "Demigod", "Demon", "Deserter", "Detective",
  "Devil", "Dinosaur", "Djinn", "Doctor", "Dog", "Dragon",
  "Drake", "Dreadnought", "Drix", "Drone", "Druid", "Dryad",
  "Dwarf", "Echidna", "Efreet", "Egg", "Elder", "Eldrazi",
  "Elemental", "Elephant", "Elf", "Elk", "Employee", "Eternal",
  "Eye", "Faerie", "Ferret", "Fish", "Flagbearer", "Fox",
  "Fractal", "Frog", "Fungus", "Gamer", "Gamma", "Gargoyle",
  "Germ", "Giant", "Giraffe", "Gith", "Glimmer", "Gnoll",
  "Gnome", "Goat", "Goblin", "God", "Golem", "Gorgon",
  "Graveborn", "Gremlin", "Griffin", "Guest", "Hag", "Halfling",
  "Hamster", "Harpy", "Hedgehog", "Hellion", "Hero", "Hippo",
  "Hippogriff", "Homarid", "Homunculus", "Horror", "Horse", "Human",
  "Hydra", "Hyena", "Illusion", "Imp", "Incarnation", "Inhuman",
  "Inkling", "Inquisitor", "Insect", "Jackal", "Jellyfish", "Juggernaut",
  "Kangaroo", "Kavu", "Kirin", "Kithkin", "Knight", "Kobold",
  "Kor", "Kraken", "Kree", "Llama", "Lamia", "Lammasu",
  "Leech", "Lemur", "Leviathan", "Lhurgoyf", "Licid", "Lizard",
  "Lobster", "Manticore", "Masticore", "Mercenary", "Merfolk", "Metathran",
  "Minion", "Minotaur", "Mite", "Mole", "Monger", "Mongoose",
  "Monk", "Monkey", "Moogle", "Moonfolk", "Mount", "Mouse",
  "Mutant", "Myr", "Mystic", "Nautilus", "Necron", "Nephilim",
  "Nightmare", "Nightstalker", "Ninja", "Noble", "Noggle", "Nomad",
  "Nymph", "Octopus", "Ogre", "Ooze", "Orb", "Orc",
  "Orgg", "Otter", "Ouphe", "Ox", "Oyster", "Pangolin",
  "Peasant", "Pegasus", "Pentavite", "Performer", "Pest", "Phelddagrif",
  "Phoenix", "Phyrexian", "Pilot", "Pincher", "Pirate", "Plant",
  "Platypus", "Porcupine", "Possum", "Praetor", "Primarch", "Prism",
  "Processor", "Qu", "Rabbit", "Raccoon", "Ranger", "Rat",
  "Rebel", "Reflection", "Rhino", "Rigger", "Robot", "Rogue",
  "Sable", "Salamander", "Samurai", "Sand", "Saproling", "Satyr",
  "Scarecrow", "Scientist", "Scion", "Scorpion", "Scout", "Sculpture",
  "Seal", "Serf", "Serpent", "Servo", "Shade", "Shaman",
  "Shapeshifter", "Shark", "Sheep", "Shi'ar", "Siren", "Skeleton",
  "Skrull", "Skunk", "Slith", "Sliver", "Sloth", "Slug",
  "Snail", "Snake", "Soldier", "Soltari", "Sorcerer", "Spawn",
  "Specter", "Spellshaper", "Sphinx", "Spider", "Spike", "Spirit",
  "Splinter", "Sponge", "Spy", "Squid", "Squirrel", "Starfish",
  "Surrakar", "Survivor", "Symbiote", "Synth", "Tentacle", "Tetravite",
  "Thalakos", "Thopter", "Thrull", "Tiefling", "Toy", "Treefolk",
  "Trilobite", "Triskelavite", "Troll", "Turtle", "Tyranid", "Unicorn",
  "Utrom", "Vampire", "Varmint", "Vedalken", "Villain", "Volver",
  "Wall", "Walrus", "Warlock", "Warrior", "Weasel", "Weird",
  "Werewolf", "Whale", "Wizard", "Wolf", "Wolverine", "Wombat",
  "Worm", "Wraith", "Wurm", "Yeti", "Zombie", "Zubera",
]

def planarTypes : List String := [
  "The Abyss", "Alara", "Alfava Metraxis", "Amonkhet", "Androzani Minor", "Antausia",
  "Apalapucia", "Arcavios", "Arkhos", "Avishkar", "Azgol", "Belenon",
  "Bolas's Meditation Realm", "Capenna", "Cridhe", "The Dalek Asylum", "Darillium", "Dominaria",
  "Earth", "Echoir", "Eldraine", "Equilor", "Ergamon", "Fabacin",
  "Fiora", "Gallifrey", "Gargantikar", "Gobakhan", "Horsehead Nebula", "Ikoria",
  "Innistrad", "Iquatana", "Ir", "Ixalan", "Kaldheim", "Kamigawa",
  "Kandoka", "Karsus", "Kephalai", "Kinshala", "Kolbahan", "Kylem",
  "Kyneth", "The Library", "Lorwyn", "Luvion", "Mars", "Mercadia",
  "Mirrodin", "Moag", "Mongseng", "Moon", "Muraganda", "Necros",
  "New Earth", "New Phyrexia", "Outside Mutter's Spiral", "Phyrexia", "Pyrulea", "Rabiah",
  "Rath", "Ravnica", "Regatha", "Segovia", "Serra's Realm", "Shadowmoor",
  "Shandalar", "Shenmeng", "Skaro", "Spacecraft", "Tarkir", "Theros",
  "Time", "Trenzalore", "Ulgrotha", "Unknown Planet", "Valla", "Vryn",
  "Wildfire", "Xerex", "Zendikar", "Zhalfir"
]

def dungeonTypes : List String := [
  "Undercity"
]

def battleTypes : List String := [
  "Siege"
]

/-- One known subtype from CR 205.3g–q. -/
structure KnownSubtype where
  name : String
  plural : String
  kind : SubtypeClass
deriving Repr

/-- Fold curly apostrophes to `'` and lowercase. Apostrophes stay, so `Urza`
and `Urza's` remain different subtypes. -/
def subtypeKey (s : String) : String :=
  let rec go (cs : List Char) (acc : List Char) (sp : Bool) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      let c := if c == '\u2019' || c == '\u2018' then '\'' else c
      if c == ' ' || c == '\n' || c == '\t' then
        if sp || acc.isEmpty then go rest acc true else go rest (' ' :: acc) true
      else
        go rest (c.toLower :: acc) false
  String.ofList (go s.toList [] true)

/-- `subtypeKey` with apostrophes removed. Oracle normalization drops them
(`can't` → `cant`), so ability text for `Urza's` arrives as `urzas`. -/
def subtypeKeyStripped (s : String) : String :=
  String.ofList ((subtypeKey s).toList.filter (· != '\''))

def nameHasApostrophe (s : String) : Bool :=
  s.toList.any fun c => c == '\'' || c == '\u2019' || c == '\u2018'

def endsWithConsonantY (w : String) : Bool :=
  match w.toList.reverse with
  | 'y' :: c :: _ =>
    c != 'a' && c != 'e' && c != 'i' && c != 'o' && c != 'u'
  | _ => false

/-- Plural of one subtype word, using the irregular forms Oracle prints. -/
def pluralizeWord (w : String) : String :=
  match w with
  | "Elf" => "Elves"
  | "Dwarf" => "Dwarves"
  | "Wolf" => "Wolves"
  | "Werewolf" => "Werewolves"
  | "Hero" => "Heroes"
  | "Mouse" => "Mice"
  | "Ox" => "Oxen"
  | "Child" => "Children"
  | "Fungus" => "Fungi"
  | "Homunculus" => "Homunculi"
  | "Cyclops" => "Cyclopes"
  | "Leech" => "Leeches"
  | "Merfolk" => "Merfolk"
  | "Fish" | "Jellyfish" | "Starfish" => w
  | "Elk" | "Sheep" | "Bison" | "Caribou" => w
  | _ =>
    if w.endsWith "s" then w
    else if endsWithConsonantY w then (w.dropEnd 1).toString ++ "ies"
    else if w.endsWith "x" || w.endsWith "z" then w ++ "es"
    else w ++ "s"

/-- Plural of a subtype name. Only the last word changes (`Time Lord` → `Time Lords`). -/
def heuristicPlural (s : String) : String :=
  let parts := (s.splitOn " ").filter (· != "")
  match parts.getLast? with
  | none => s
  | some last =>
    String.intercalate " " (parts.dropLast ++ [pluralizeWord last])

def subtypesOf (kind : SubtypeClass) (names : List String) : List KnownSubtype :=
  names.map fun name => { name, plural := heuristicPlural name, kind }

/-- Every subtype in CR 205.3g–q. `Spacecraft` is both an artifact type and a
planar type; the artifact entry is kept. -/
def subtypeEntries : List KnownSubtype :=
  let raw :=
    subtypesOf .artifact artifactTypes ++
    subtypesOf .enchantment enchantmentTypes ++
    subtypesOf .land landTypes ++
    subtypesOf .planeswalker planeswalkerTypes ++
    subtypesOf .spell spellTypes ++
    subtypesOf .creature creatureTypes ++
    subtypesOf .planar planarTypes ++
    subtypesOf .dungeon dungeonTypes ++
    subtypesOf .battle battleTypes
  raw.foldl (fun acc e =>
    if acc.any (·.name == e.name) then acc else acc ++ [e]) []

/-- Singular and plural spellings, apostrophes kept. -/
def subtypeByKey : Thunk (Std.HashMap String KnownSubtype) :=
  Thunk.mk fun _ =>
    subtypeEntries.foldl (fun m e =>
      let m := m.insert (subtypeKey e.name) e
      m.insert (subtypeKey e.plural) e)
      ({} : Std.HashMap String KnownSubtype)

/-- Apostrophe-free spellings of subtypes whose names contain `'`.
Oracle text drops the apostrophe, so `urzas` means the land type `Urza's`
rather than the plural of the planeswalker type `Urza`. -/
def subtypeByStrippedApostrophe : Thunk (Std.HashMap String KnownSubtype) :=
  Thunk.mk fun _ =>
    subtypeEntries.foldl (fun m e =>
      if nameHasApostrophe e.name then
        let m := m.insert (subtypeKeyStripped e.name) e
        m.insert (subtypeKeyStripped e.plural) e
      else m)
      ({} : Std.HashMap String KnownSubtype)

/-- Canonical singular name for a printed singular or plural subtype, in any
case. A missing apostrophe still finds `C'tan`, `Shi'ar`, and `Urza's`. -/
def ofOracle? (s : String) : Option String :=
  let kept := subtypeKey s
  if !kept.toList.any (· == '\'') then
    match (subtypeByStrippedApostrophe.get).get? (subtypeKeyStripped s) with
    | some e => some e.name
    | none => (subtypeByKey.get).get? kept |>.map (·.name)
  else
    (subtypeByKey.get).get? kept |>.map (·.name)

/-- Oracle plural of a subtype. Unknown words use the same spelling rules. -/
def pluralizeName (s : String) : String :=
  match ofOracle? s with
  | some name =>
    match (subtypeByKey.get).get? (subtypeKey name) with
    | some e => e.plural
    | none => heuristicPlural name
  | none => heuristicPlural s

/-- Kept-apostrophe keys that would make two different subtypes the same word. -/
def subtypeClashes : List String :=
  Id.run do
    let mut seen : Std.HashMap String String := {}
    let mut bad : Array String := #[]
    for e in subtypeEntries do
      for key in [subtypeKey e.name, subtypeKey e.plural] do
        match seen.get? key with
        | some prev =>
          if prev != e.name then bad := bad.push s!"{key}: {prev} / {e.name}"
        | none => seen := seen.insert key e.name
    return bad.toList

def isCreatureType (s : String) : Bool :=
  match (subtypeByKey.get).get? (subtypeKey s) with
  | some e => e.kind == .creature
  | none => false

/-- A subtype that is not a creature type (CR 205.3g–k, 205.3n–q).
Changeling grants creature types only (CR 702.72). Unknown words stay
available to changeling, matching objects whose printed subtype is not in
the current rules list. -/
def isNoncreatureSubtype (s : Subtype) : Bool :=
  match (subtypeByKey.get).get? (subtypeKey s) with
  | some e => e.kind != .creature
  | none => false

def formMatches (e : KnownSubtype) (key : String) (plural : Bool) : Bool :=
  let target := if plural then e.plural else e.name
  subtypeKey target == key || subtypeKeyStripped target == subtypeKeyStripped key

/-- Longest leading singular (`plural = false`) or plural spelling. -/
def matchSubtypeForm (plural : Bool) (toks : List String) : Option (String × Nat) :=
  let rec go : Nat → Option (String × Nat)
    | 0 => none
    | n + 1 =>
      let got := toks.take (n + 1)
      if got.length != n + 1 then go n
      else
        let raw := String.intercalate " " got
        match ofOracle? raw with
        | some name =>
          match (subtypeByKey.get).get? (subtypeKey name) with
          | some e =>
            if formMatches e (subtypeKey raw) plural then some (e.name, n + 1) else go n
          | none => go n
        | none => go n
  go (min 4 toks.length)

/-- `non-Time Lord` is tokens `non-time` `lord` after normalization. -/
def matchNonSubtype (toks : List String) : Option (String × Nat) :=
  match toks with
  | t :: rest =>
    if t.startsWith "non-" && t.length > "non-".length then
      let stem := (t.drop "non-".length).toString
      match matchSubtypeForm false (stem :: rest) with
      | some (name, n) => some (name, n)
      | none => none
    else none
  | [] => none

/-- `Forestcycling` or `Time Lordcycling` (cycling glued to the last word). -/
def matchCyclingSubtype (toks : List String) : Option (String × Nat) :=
  let rec go : Nat → Option (String × Nat)
    | 0 => none
    | n + 1 =>
      let got := toks.take (n + 1)
      if got.length != n + 1 then go n
      else
        match got.getLast? with
        | some last =>
          if last.endsWith "cycling" && last.length > "cycling".length then
            let stem := (last.dropEnd "cycling".length).toString
            let words := got.dropLast ++ [stem]
            match matchSubtypeForm false words with
            | some (name, w) =>
              if w == words.length then some (name, n + 1) else go n
            | none => go n
          else go n
        | none => go n
  go (min 4 toks.length)

def normalizeApostrophes (s : String) : String :=
  String.ofList (s.toList.map fun c =>
    if c == '\u2019' || c == '\u2018' then '\'' else c)

def wordsMatchIgnoreCase (printed expected : List String) : Bool :=
  printed.length == expected.length &&
    (printed.zip expected).all fun (p, e) =>
      p.map Char.toLower == e.map Char.toLower

/-- Split the words after a type-line dash (CR 205.3b).
Planes keep every word as one subtype. Creatures and kindreds keep the
two-word creature type `Time Lord` together. Every other subtype is one word. -/
def splitPrintedSubtypes (types : Array CardType) (sub : String) : Array Subtype :=
  let sub := (normalizeApostrophes sub).trimAscii.copy
  if sub.isEmpty then #[]
  else if types.any (· == .plane) then #[sub]
  else
    let words := sub.splitOn " " |>.filter (· != "")
    let multis :=
      if types.any fun t => t == .creature || t == .kindred then
        creatureTypes.filter fun s => (s.splitOn " ").length > 1
      else []
    let rec go : Nat → List String → List String
      | 0, _ => []
      | _, [] => []
      | fuel + 1, ws =>
        match multis.find? fun m =>
          let mw := m.splitOn " " |>.filter (· != "")
          wordsMatchIgnoreCase (ws.take mw.length) mw
        with
        | some m =>
          let n := (m.splitOn " " |>.filter (· != "")).length
          let n := if n == 0 then 1 else n
          String.intercalate " " (ws.take n) :: go fuel (ws.drop n)
        | none =>
          match ws with
          | w :: rest => w :: go fuel rest
          | [] => []
    (go words.length words).toArray

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
#guard Supertype.all.length == 5
#guard Supertype.all == [.basic, .legendary, .ongoing, .snow, .world]
#guard Supertype.all.all fun s =>
  Supertype.ofOracle? s.englishName == some s &&
    Supertype.ofOracle? (s.englishName.map Char.toLower) == some s &&
    Supertype.ofOracle? (s.englishName.map Char.toUpper) == some s
#guard Supertype.ofOracle? "SNOW" == some .snow
#guard Supertype.ofOracle? "World" == some .world
#guard Supertype.ofOracle? "nonbasic" == none
#guard Supertype.ofOracle? "legendaries" == none
#guard Supertype.ofOracle? "Snow-Covered" == none
#guard CardType.all.length == 15
#guard CardType.all.all fun t =>
  CardType.ofOracle? t.englishName == some t &&
    CardType.ofOracle? t.pluralName == some t &&
    CardType.all.all fun u =>
      t == u || (t.pluralName != u.englishName && t.pluralName != u.pluralName)
#guard CardType.ofOracle? "Sorceries" == some .sorcery
#guard CardType.ofOracle? "conspiracies" == some .conspiracy
#guard CardType.ofOracle? "phenomena" == some .phenomenon
#guard CardType.ofOracle? "planeswalkers" == some .planeswalker
#guard CardType.ofOracle? "KINDREDS" == some .kindred
#guard CardType.creature.isPermanentType
#guard !CardType.instant.isPermanentType
#guard !CardType.kindred.isPermanentType
#guard !CardType.dungeon.isPermanentType
#guard !CardType.plane.isPermanentType
#guard !CardType.phenomenon.isPermanentType
#guard !CardType.vanguard.isPermanentType
#guard !CardType.scheme.isPermanentType
#guard !CardType.conspiracy.isPermanentType
#guard CardType.battle.isPermanentType
#guard CardType.planeswalker.isPermanentType
#guard CardType.sorcery.isInstantOrSorcery
#guard formatTypeLine #[.basic] #[.land] #["Forest"] == "Basic Land — Forest"
#guard formatTypeLine #[] #[.creature] #["Bear"] == "Creature — Bear"
#guard formatTypeLine #[] #[.instant] #[] == "Instant"


#guard artifactTypes.length == 23
#guard enchantmentTypes.length == 13
#guard landTypes.length == 17
#guard planeswalkerTypes.length == 80
#guard spellTypes.length == 5
#guard creatureTypes.length == 324
#guard planarTypes.length == 82
#guard dungeonTypes == ["Undercity"]
#guard battleTypes == ["Siege"]
#guard basicLandTypes.all fun s => landTypes.any (· == s)
#guard subtypeEntries.length == 545
#guard subtypeClashes == []
#guard subtypeEntries.all fun e =>
  ofOracle? e.name == some e.name &&
    pluralizeName e.name == e.plural &&
    -- `Urzas` is the plural of planeswalker type Urza and also `Urza's`
    -- after Oracle drops the apostrophe. The land type wins that spelling.
    (e.name == "Urza" || ofOracle? e.plural == some e.name)
#guard ofOracle? "ELVES" == some "Elf"
#guard ofOracle? "time lords" == some "Time Lord"
#guard ofOracle? "URZA'S" == some "Urza's"
#guard ofOracle? "urzas" == some "Urza's"
#guard ofOracle? "c'tan" == some "C'tan"
#guard ofOracle? "C\u2019tan" == some "C'tan"
#guard ofOracle? "bolass meditation realm" == some "Bolas's Meditation Realm"
#guard ofOracle? "power-plant" == some "Power-Plant"
#guard ofOracle? "assembly-workers" == some "Assembly-Worker"
#guard ofOracle? "mice" == some "Mouse"
#guard ofOracle? "siege" == some "Siege"
#guard ofOracle? "undercity" == some "Undercity"
#guard ofOracle? "phenomenon" == none
#guard pluralizeName "Mouse" == "Mice"
#guard pluralizeName "Ox" == "Oxen"
#guard pluralizeName "Harpy" == "Harpies"
#guard pluralizeName "Spy" == "Spies"
#guard pluralizeName "Monkey" == "Monkeys"
#guard pluralizeName "Sheep" == "Sheep"
#guard pluralizeName "Phoenix" == "Phoenixes"
#guard pluralizeName "Time Lord" == "Time Lords"
#guard pluralizeName "Werewolf" == "Werewolves"
#guard pluralizeName "Merfolk" == "Merfolk"
#guard isCreatureType "Time Lord"
#guard isCreatureType "C'tan"
#guard !isNoncreatureSubtype "Time Lord"
#guard isNoncreatureSubtype "Siege"
#guard isNoncreatureSubtype "Jace"
#guard isNoncreatureSubtype "Adventure"
#guard isNoncreatureSubtype "Undercity"
#guard isNoncreatureSubtype "Spacecraft"
#guard isNoncreatureSubtype "The Abyss"
#guard isNoncreatureSubtype "Urza's"
#guard isNoncreatureSubtype "Power-Plant"
#guard !isNoncreatureSubtype "NotARealType"
#guard splitPrintedSubtypes #[.creature] "Human Time Lord" == #["Human", "Time Lord"]
#guard splitPrintedSubtypes #[.creature] "Time Lord Human" == #["Time Lord", "Human"]
#guard splitPrintedSubtypes #[.artifact] "Time Lord" == #["Time", "Lord"]
#guard splitPrintedSubtypes #[.kindred, .sorcery] "Time Lord" == #["Time Lord"]
#guard splitPrintedSubtypes #[.plane] "Bolas\u2019s Meditation Realm" == #["Bolas's Meditation Realm"]
#guard splitPrintedSubtypes #[.land] "Urza\u2019s Power-Plant" == #["Urza's", "Power-Plant"]
#guard splitPrintedSubtypes #[.creature] "C\u2019tan" == #["C'tan"]
#guard splitPrintedSubtypes #[.creature] "Shi'ar" == #["Shi'ar"]

end Mtg.Engine
