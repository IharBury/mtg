import Mtg.Engine.Color

/-!
# Mana (CR 106, 107.4, 202)

Mana is the primary resource in the game. There are six types of mana: the
five colors and colorless (CR 106.1b). Players spend mana to pay costs.
-/

namespace Mtg.Engine

/-- A type of mana that can exist in a mana pool (CR 106.1b). -/
inductive ManaType where
  | manaTypeKind (color : Option Color := none)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaType

@[match_pattern] abbrev colored (color : Color) : ManaType := .manaTypeKind (some color)
@[match_pattern] abbrev colorless : ManaType := .manaTypeKind none

def letter : ManaType → String
  | .colored c => c.letter
  | .colorless => "C"

instance : ToString ManaType where
  toString
    | .colored c => toString c
    | .colorless => "colorless"

end ManaType

instance {α β : Type} [Inhabited α] : Inhabited (α ⊕ β) := ⟨.inl default⟩

/-- A symbol that can appear in a mana cost (subset of CR 107.4). -/
inductive ManaSymbol where
  | manaSymbolKind (k : Nat ⊕ (Color × Option (Option Color)) ⊕ Bool := .inl 0)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaSymbol

/-- Generic mana in costs, payable with any type (CR 107.4b). -/
@[match_pattern] abbrev generic (n : Nat) : ManaSymbol :=
  .manaSymbolKind (.inl n)
/-- One mana of a specific color (CR 107.4a). -/
@[match_pattern] abbrev colored (color : Color) : ManaSymbol :=
  .manaSymbolKind (.inr (.inl (color, none)))
/-- A monocolored hybrid symbol `{A/B}` (CR 107.4e). Payable with either color. -/
@[match_pattern] abbrev hybrid (a b : Color) : ManaSymbol :=
  .manaSymbolKind (.inr (.inl (a, some (some b))))
/-- A monocolored hybrid with generic mana `{2/C}` (CR 107.4f). Payable with
two mana of any type, or one mana of `c`. Mana value is 2. -/
@[match_pattern] abbrev twobrid (c : Color) : ManaSymbol :=
  .manaSymbolKind (.inr (.inl (c, some none)))
/-- The colorless mana symbol `{C}` (CR 107.4c). -/
@[match_pattern] abbrev colorless : ManaSymbol :=
  .manaSymbolKind (.inr (.inr false))
/-- The variable symbol `{X}` (CR 107.3). Treated as 0 off the stack (CR 107.3g). -/
@[match_pattern] abbrev x : ManaSymbol :=
  .manaSymbolKind (.inr (.inr true))

def toNotation : ManaSymbol → String
  | .generic n => s!"\{{n}}"
  | .colored c => s!"\{{c.letter}}"
  | .colorless => "{C}"
  | .hybrid a b => s!"\{{a.letter}/{b.letter}}"
  | .twobrid c => s!"\{2/{c.letter}}"
  | .x => "{X}"

/-- Color contributed by this symbol to an object’s color (CR 202.2). -/
def colorContribution : ManaSymbol → ColorSet
  | .colored c => ColorSet.singleton c
  | .hybrid a b => ColorSet.singleton a |>.union (ColorSet.singleton b)
  | .twobrid c => ColorSet.singleton c
  | .generic _ | .colorless | .x => ColorSet.empty

instance : ToString ManaSymbol where
  toString := toNotation

end ManaSymbol

/-- A mana cost printed on a card (CR 202). -/
structure ManaCost where
  symbols : Array ManaSymbol
deriving BEq, Repr, Inhabited

namespace ManaCost

def empty : ManaCost := { symbols := #[] }

/-- The payable zero mana cost `{0}` (CR 107.4d / 118.7). Distinct from
`empty`, which is no mana cost and cannot be paid (CR 202.1b / 118.6). -/
def zero : ManaCost := { symbols := #[.generic 0] }

def ofGeneric (n : Nat) : ManaCost :=
  if n == 0 then empty else { symbols := #[.generic n] }

def ofColor (c : Color) : ManaCost :=
  { symbols := #[.colored c] }

def ofGenericAndColor (n : Nat) (c : Color) : ManaCost :=
  if n == 0 then ofColor c
  else { symbols := #[.generic n, .colored c] }

def ofColors (cs : List Color) : ManaCost :=
  { symbols := cs.toArray.map ManaSymbol.colored }

def ofGenericAndColors (n : Nat) (cs : List Color) : ManaCost :=
  let colored := cs.toArray.map ManaSymbol.colored
  if n == 0 then { symbols := colored }
  else { symbols := #[.generic n] ++ colored }

/-- One monocolored hybrid symbol `{a/b}` (CR 107.4e). -/
def ofHybrid (a b : Color) : ManaCost :=
  { symbols := #[.hybrid a b] }

/-- `{n}` followed by `count` copies of `{a/b}`. -/
def ofGenericAndHybrids (n : Nat) (a b : Color) (count : Nat := 1) : ManaCost :=
  let hybrids := Array.replicate count (ManaSymbol.hybrid a b)
  if n == 0 then { symbols := hybrids }
  else { symbols := #[.generic n] ++ hybrids }

/-- Mana value is the total amount of mana in a mana cost (CR 202.3). `{X}` is 0. -/
def manaValue (cost : ManaCost) : Nat :=
  cost.symbols.foldl
    (fun acc s =>
      match s with
      | .generic n => acc + n
      | .colored _ => acc + 1
      | .colorless => acc + 1
      | .hybrid _ _ => acc + 1
      | .twobrid _ => acc + 2
      | .x => acc)
    0

/-- Whether paying this cost requires spending mana (CR 601.2g). `{X}` is 0 until chosen. -/
def includesManaPayment (cost : ManaCost) : Bool :=
  cost.manaValue > 0

/-- Whether this cost still has an unsubstituted `{X}` (CR 107.3a / 601.2b). -/
def containsX (cost : ManaCost) : Bool :=
  cost.symbols.any (fun
    | .x => true
    | _ => false)

/-- Replace each `{X}` with `{x}` generic mana. `{X}` chosen as 0 is dropped
(CR 107.3a / 107.3c). -/
def substituteX (cost : ManaCost) (x : Nat) : ManaCost :=
  { symbols := cost.symbols.foldl (fun acc s =>
      match s with
      | .x => if x == 0 then acc else acc.push (.generic x)
      | _ => acc.push s) (#[] : Array ManaSymbol) }

/-- How many dedicated `{C}` mana symbols of color `c` appear in this cost.
Hybrid symbols are not counted; use `symbolsIncludingColor` for Zemo's
boast and similar “black mana symbols” checks (MSH 128). -/
def coloredCount (cost : ManaCost) (c : Color) : Nat :=
  cost.symbols.foldl
    (fun n s =>
      match s with
      | .colored d => if d == c then n + 1 else n
      | .generic _ | .colorless | .hybrid _ _ | .twobrid _ | .x => n)
    0

/-- How many mana symbols include color `c`, counting `{c}` and `{c/x}`
hybrids (CR 107.4e / MSH 128). -/
def symbolsIncludingColor (cost : ManaCost) (c : Color) : Nat :=
  cost.symbols.foldl
    (fun n s =>
      match s with
      | .colored d => if d == c then n + 1 else n
      | .hybrid a b => if a == c || b == c then n + 1 else n
      | .twobrid d => if d == c then n + 1 else n
      | .generic _ | .colorless | .x => n)
    0

/-- Color of an object from the colored mana symbols in its mana cost (CR 202.2). -/
def colors (cost : ManaCost) : ColorSet :=
  cost.symbols.foldl (fun acc s => acc.union s.colorContribution) ColorSet.empty

/-- If `original` required mana and `result` has no symbols, the payable cost
is `{0}` rather than an empty (unpayable) cost (CR 107.4d / 118.7 / 202.1b). -/
def afterReduction (original result : ManaCost) : ManaCost :=
  if original.includesManaPayment && result.symbols.isEmpty then zero else result

/-- Total generic mana in this cost. -/
def genericCount (cost : ManaCost) : Nat :=
  cost.symbols.foldl (fun acc s => match s with | .generic n => acc + n | _ => acc) 0

/-- Reduce generic mana in this cost by `n`, dropping a `{0}` generic symbol
(CR 118.7d). Colored symbols are unchanged. -/
def reduceGeneric (cost : ManaCost) (n : Nat) : ManaCost :=
  let rec go (syms : List ManaSymbol) (left : Nat) : List ManaSymbol :=
    match syms with
    | [] => []
    | .generic g :: rest =>
      if left == 0 then .generic g :: go rest 0
      else if left ≥ g then go rest (left - g)
      else
        let g' := g - left
        (if g' == 0 then [] else [.generic g']) ++ go rest 0
    | s :: rest => s :: go rest left
  { symbols := (go cost.symbols.toList n).toArray }

/-- Remove up to `n` symbols of color `c`. Returns the leftover count. -/
def stripColored (cost : ManaCost) (c : Color) (n : Nat) : ManaCost × Nat :=
  Id.run do
    let mut left := n
    let mut out : Array ManaSymbol := #[]
    for s in cost.symbols do
      match s with
      | .colored d =>
        if d == c && left > 0 then
          left := left - 1
        else
          out := out.push s
      | _ => out := out.push s
    return ({ symbols := out }, left)

/-- Remove up to `n` `{C}` symbols. Returns the leftover count. -/
def stripColorless (cost : ManaCost) (n : Nat) : ManaCost × Nat :=
  Id.run do
    let mut left := n
    let mut out : Array ManaSymbol := #[]
    for s in cost.symbols do
      match s with
      | .colorless =>
        if left > 0 then
          left := left - 1
        else
          out := out.push s
      | _ => out := out.push s
    return ({ symbols := out }, left)

/-- Reduce `cost` by `byCost` as a power-up discount (CR 702.193b). Generic
mana in `byCost` reduces generic mana. Colored and colorless mana reduce the
same type; leftover amounts reduce generic. -/
def reduceByCost (cost byCost : ManaCost) : ManaCost :=
  let original := cost
  let rec stripColors (cost : ManaCost) (cs : List Color) (extra : Nat) : ManaCost × Nat :=
    match cs with
    | [] => (cost, extra)
    | c :: rest =>
      let n := byCost.coloredCount c
      let (cost, leftover) := cost.stripColored c n
      stripColors cost rest (extra + leftover)
  let (cost, extraColored) := stripColors cost Color.all 0
  let colorlessN :=
    byCost.symbols.foldl (fun acc s =>
      match s with
      | .colorless => acc + 1
      | _ => acc) 0
  let (cost, extraColorless) := cost.stripColorless colorlessN
  let generic :=
    byCost.symbols.foldl (fun acc s =>
      match s with
      | .generic n => acc + n
      | .hybrid _ _ => acc + 1
      | .twobrid _ => acc + 2
      | _ => acc) 0
  afterReduction original (cost.reduceGeneric (generic + extraColored + extraColorless))

/-- Concatenate two mana costs (additional costs such as kicker, CR 601.2f). -/
def addCost (a b : ManaCost) : ManaCost :=
  { symbols := a.symbols ++ b.symbols }

/-- Add `n` generic mana to this cost (CR 601.2b / 601.2f). -/
def addGeneric (cost : ManaCost) (n : Nat) : ManaCost :=
  if n == 0 then cost
  else
    match cost.symbols.findIdx? (fun s => match s with | .generic _ => true | _ => false) with
    | some i =>
      match cost.symbols[i]! with
      | .generic g => { symbols := cost.symbols.set! i (.generic (g + n)) }
      | _ => cost
    | none => { symbols := #[.generic n] ++ cost.symbols }

/-- Printed mana symbols (CR 202.1). An empty cost is not `{0}`: lands and
other cards with no mana cost have no symbols, and that cost cannot be paid
(CR 202.1b / 118.6). `{0}` is the generic zero symbol (CR 107.4d). -/
def toNotation (cost : ManaCost) : String :=
  String.join (cost.symbols.toList.map ManaSymbol.toNotation)

instance : ToString ManaCost where
  toString := toNotation

instance : BEq ManaCost where
  beq a b := a.symbols.toList == b.symbols.toList

#guard (ofGenericAndColor 1 .green).manaValue == 2
#guard (ofGenericAndColor 1 .green).includesManaPayment
#guard !ManaCost.empty.includesManaPayment
#guard ({ symbols := #[.x, .colored .blue, .colored .blue] } : ManaCost).containsX
#guard !({ symbols := #[.colored .blue, .colored .blue] } : ManaCost).containsX
#guard ({ symbols := #[.x, .colored .blue] } : ManaCost).substituteX 3 ==
  ({ symbols := #[.generic 3, .colored .blue] } : ManaCost)
#guard ({ symbols := #[.x, .x] } : ManaCost).substituteX 2 ==
  ({ symbols := #[.generic 2, .generic 2] } : ManaCost)
#guard ({ symbols := #[.x, .colored .blue] } : ManaCost).substituteX 0 ==
  ({ symbols := #[.colored .blue] } : ManaCost)
#guard (ofGenericAndColor 1 .green).colors.isMonocolored
#guard (ofGeneric 4).colors.isColorless
#guard (ofColors [.blue, .black]).colors.isColorPair
#guard toString ManaCost.empty == ""
#guard toString ManaCost.zero == "{0}"
#guard ManaCost.zero != ManaCost.empty
#guard !ManaCost.zero.includesManaPayment
#guard toString (ofGeneric 0) == ""
#guard toString ({ symbols := #[.generic 0] } : ManaCost) == "{0}"
#guard toString (ofGeneric 1) == "{1}"
#guard toString ((ofGenericAndColor 6 .red).reduceByCost (ofGenericAndColor 2 .red)) == "{4}"
#guard toString ((ofColors [.white, .blue, .black, .red, .green]).reduceByCost
  (ofColor .white)) == "{U}{B}{R}{G}"
#guard toString (ofColor .red) == "{R}"
#guard (ofGenericAndColor 4 .black).reduceGeneric 3 == ofGenericAndColor 1 .black
#guard (ofGenericAndColor 3 .black).reduceGeneric 3 == ofColor .black
#guard (ofGenericAndColor 1 .black).reduceGeneric 3 == ofColor .black
#guard afterReduction (ofGeneric 2) ((ofGeneric 2).reduceGeneric 2) == zero
#guard afterReduction empty empty == empty
#guard (ofColor .black).addGeneric 4 == ofGenericAndColor 4 .black
#guard (ofGenericAndColor 1 .black).addGeneric 4 == ofGenericAndColor 5 .black
#guard toString (ofHybrid .black .green) == "{B/G}"
#guard (ofGenericAndHybrids 3 .black .green 2).manaValue == 5
#guard (ofGenericAndHybrids 3 .black .green 2).colors.isColorPair

end ManaCost

/-- What a restricted mana ability's mana may be spent on (CR 106.6 / 106.10). -/
inductive ManaUse where
  /-- Parameterized mana spending restriction (CR 106.6 / 106.10): source/ability (`!cardTypeGroup && !handOrTreasureGroup && !bySubtype`), card-type/supertype spell (`cardTypeGroup && !handOrTreasureGroup && !bySubtype`), hand/Treasure/Dwarf-Equipment-Saga (`handOrTreasureGroup && !bySubtype`), or subtype spell/ability (`bySubtype`). -/
  | manaUseKind (subtype : String := "") (alt1 : Bool := false) (alt2 : Bool := false)
      (cardTypeGroup : Bool := false) (handOrTreasureGroup : Bool := false) (bySubtype : Bool := false)
      (restricted : Bool := true)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaUse

@[match_pattern] abbrev subtypeUse (subtype : String) (orAbility : Bool := false) : ManaUse :=
  .manaUseKind subtype orAbility false false false true true
@[match_pattern] abbrev sourceOrAbilityRestriction (cantNonartifact : Bool := false) (creatureOrEquip : Bool := false) : ManaUse :=
  .manaUseKind "" cantNonartifact creatureOrEquip false false false true
@[match_pattern] abbrev cardTypeOrSupertypeSpell (noncreature : Bool := false) (legendaryOrArtifact : Bool := false) : ManaUse :=
  .manaUseKind "" noncreature legendaryOrArtifact true false false true
@[match_pattern] abbrev handOrTreasureSpend (fromTreasure : Bool := false) (dwarfEquipmentSaga : Bool := false) : ManaUse :=
  .manaUseKind "" fromTreasure dwarfEquipmentSaga false true false true
@[match_pattern] abbrev subtypeSpell (subtype : String) : ManaUse := .subtypeUse subtype false
@[match_pattern] abbrev subtypeSpellOrAbility (subtype : String) : ManaUse := .subtypeUse subtype true
/-- Only casting Elf spells or activating abilities of Elf sources (Woodland Weavemaster). -/
@[match_pattern] abbrev elf : ManaUse := .subtypeSpellOrAbility "Elf"
/-- Only casting a Hero spell or activating an ability of a Hero source (Avengers Tower). -/
@[match_pattern] abbrev hero : ManaUse := .subtypeSpellOrAbility "Hero"
/-- Only casting a Villain spell or activating an ability of a Villain source (Villainous Hideout). -/
@[match_pattern] abbrev villain : ManaUse := .subtypeSpellOrAbility "Villain"
/-- Only casting Dragon spells (Desolation of Smaug). -/
@[match_pattern] abbrev dragonSpell : ManaUse := .subtypeSpell "Dragon"
/-- Only casting an instant or sorcery spell (Pelargir Survivor). -/
@[match_pattern] abbrev instantOrSorcery : ManaUse := .sourceOrAbilityRestriction false false
/-- Cannot be spent to cast a nonartifact spell (Vibranium tokens, Hydraulic Helper). -/
@[match_pattern] abbrev cantNonartifact : ManaUse := .sourceOrAbilityRestriction true false
/-- Only activating abilities of creature sources in any zone (Shang-Chi; MSH 75). -/
@[match_pattern] abbrev creatureSource : ManaUse := .sourceOrAbilityRestriction false true
/-- Only casting Equipment spells or activating equip abilities (Ronin, Shadow Stalker). -/
@[match_pattern] abbrev equipmentOrEquip : ManaUse := .sourceOrAbilityRestriction true true
/-- Only casting a planeswalker spell (Gideon's Memorial). -/
@[match_pattern] abbrev planeswalkerSpell : ManaUse := .cardTypeOrSupertypeSpell false false
/-- Only casting a noncreature spell (Chandra, Chill of Compliance). -/
@[match_pattern] abbrev noncreatureSpell : ManaUse := .cardTypeOrSupertypeSpell true false
/-- Only casting a legendary spell, which then can't be countered (Delighted Halfling). -/
@[match_pattern] abbrev legendarySpell : ManaUse := .cardTypeOrSupertypeSpell false true
/-- Only casting an artifact spell (Castle Doom). -/
@[match_pattern] abbrev artifactSpell : ManaUse := .cardTypeOrSupertypeSpell true true
/-- Anything except casting spells from your hand (Heartwood Crafter). -/
@[match_pattern] abbrev notSpellsFromHand : ManaUse := .handOrTreasureSpend false false
/-- No restriction; tracked so “if mana from a Treasure was spent” can be checked (Smaug, Wicked Worm). -/
@[match_pattern] abbrev fromTreasure : ManaUse := .handOrTreasureSpend true false
/-- Only casting Dwarf, Equipment, and Saga spells (Fíli and Kíli, Joyous). -/
@[match_pattern] abbrev dwarfEquipmentSagaSpell : ManaUse := .handOrTreasureSpend false true

end ManaUse

/-- Backward-compatible alias for `ManaUse` (CR 106.6). -/
abbrev FraManaUse := ManaUse

/-- How mana from a mana ability may be spent (CR 106.6 / 106.10), unified with `ManaUse`. -/
abbrev ManaRestriction := ManaUse

namespace ManaRestriction

@[match_pattern] abbrev none : ManaRestriction := .manaUseKind "" false false false false false false
@[match_pattern] abbrev only (u : ManaUse) : ManaRestriction := u
@[match_pattern] abbrev subtypeSpellOrAbility (subtype : String) : ManaRestriction := .only (.subtypeSpellOrAbility subtype)
@[match_pattern] abbrev elf : ManaRestriction := .only .elf
@[match_pattern] abbrev instantOrSorcery : ManaRestriction := .only .instantOrSorcery
@[match_pattern] abbrev hero : ManaRestriction := .only .hero
@[match_pattern] abbrev villain : ManaRestriction := .only .villain
@[match_pattern] abbrev cantNonartifact : ManaRestriction := .only .cantNonartifact
@[match_pattern] abbrev creatureSource : ManaRestriction := .only .creatureSource
@[match_pattern] abbrev fra (u : ManaUse) : ManaRestriction := .only u

end ManaRestriction

/-- True when `u` is one of the general `ManaSpend`-checked restrictions. -/
def ManaUse.isFra : ManaUse → Bool
  | .elf | .instantOrSorcery | .hero | .villain | .cantNonartifact | .creatureSource | .manaUseKind _ _ _ _ _ _ false => false
  | _ => true

/-- What a payment is for, as far as `ManaUse` restrictions care. The
default is an activated ability or another non-spell payment. -/
structure ManaSpend where
  spell : Bool := false
  fromHand : Bool := false
  planeswalker : Bool := false
  noncreature : Bool := false
  legendary : Bool := false
  artifact : Bool := false
  /-- Subtypes of the spell being cast. -/
  subtypes : Array String := #[]
  /-- Subtypes of the spell or ability source. -/
  sourceSubtypes : Array String := #[]
  /-- Activating an equip ability. -/
  equip : Bool := false
deriving DecidableEq, Repr, Inhabited, BEq

/-- Whether mana restricted to `u` may pay for `s`. -/
def ManaUse.allows : ManaUse → ManaSpend → Bool
  | .elf, _ | .instantOrSorcery, _ | .hero, _ | .villain, _
  | .cantNonartifact, _ | .creatureSource, _ => false
  | .subtypeSpellOrAbility sub, s => s.subtypes.contains sub || s.sourceSubtypes.contains sub
  | .notSpellsFromHand, s => !(s.spell && s.fromHand)
  | .planeswalkerSpell, s => s.spell && s.planeswalker
  | .noncreatureSpell, s => s.spell && s.noncreature
  | .fromTreasure, _ => true
  | .legendarySpell, s => s.spell && s.legendary
  | .dwarfEquipmentSagaSpell, s | .handOrTreasureSpend true true, s =>
    s.spell && (s.subtypes.contains "Dwarf" || s.subtypes.contains "Equipment" ||
      s.subtypes.contains "Saga")
  | .equipmentOrEquip, s => (s.spell && s.subtypes.contains "Equipment") || s.equip
  | .artifactSpell, s => s.spell && s.artifact
  | .subtypeSpell sub, s => s.spell && s.subtypes.contains sub
  | _, _ => false

/-- Short label for a restriction in pool notation. -/
def ManaUse.label : ManaUse → String
  | .subtypeSpellOrAbility sub => sub
  | .instantOrSorcery => "instant/sorcery"
  | .cantNonartifact => "not nonartifact spell"
  | .creatureSource => "creature source"
  | .notSpellsFromHand => "not spells from hand"
  | .planeswalkerSpell => "planeswalker spells"
  | .noncreatureSpell => "noncreature spells"
  | .fromTreasure => "Treasure"
  | .legendarySpell => "legendary spells"
  | .dwarfEquipmentSagaSpell | .handOrTreasureSpend true true => "Dwarf, Equipment, and Saga spells"
  | .equipmentOrEquip => "Equipment spells and equip abilities"
  | .artifactSpell => "artifact spells"
  | .subtypeSpell sub => s!"{sub} spells"
  | _ => ""

/-- A short note for the log describing `r`. -/
def ManaRestriction.note : ManaRestriction → String
  | .none | .fra .fromTreasure => ""
  | .subtypeSpellOrAbility sub => s!" ({sub} spells and abilities)"
  | .instantOrSorcery => " (instant or sorcery spells)"
  | .cantNonartifact => " (not a nonartifact spell)"
  | .creatureSource => " (abilities of creature sources)"
  | .only u => s!" ({u.label})"

/-- Spend restriction for spells of `subtype`. -/
def ManaUse.forSubtype (subtype : String) : ManaUse :=
  .subtypeSpell subtype

/-- Backward-compatible alias for `ManaUse.forSubtype`. -/
abbrev FraManaUse.forSubtype := ManaUse.forSubtype

/-- Unspent mana a player currently has (CR 106.4). Restricted mana (CR 106.10)
is a subset of the totals. -/
structure ManaPool where
  white : Nat := 0
  blue : Nat := 0
  black : Nat := 0
  red : Nat := 0
  green : Nat := 0
  colorless : Nat := 0
  /-- One entry per mana with a spending restriction (CR 106.6 / 106.10). These
  are included in the totals above. -/
  restricted : Array (ManaType × ManaUse) := #[]
deriving BEq, DecidableEq, Repr, Inhabited

namespace ManaPool

def empty : ManaPool := {}

def isEmpty (p : ManaPool) : Bool :=
  p.white == 0 && p.blue == 0 && p.black == 0 &&
  p.red == 0 && p.green == 0 && p.colorless == 0

def get (p : ManaPool) : ManaType → Nat
  | .colored .white => p.white
  | .colored .blue => p.blue
  | .colored .black => p.black
  | .colored .red => p.red
  | .colored .green => p.green
  | .colorless => p.colorless

def set (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colored .white => { p with white := n }
  | .colored .blue => { p with blue := n }
  | .colored .black => { p with black := n }
  | .colored .red => { p with red := n }
  | .colored .green => { p with green := n }
  | .colorless => { p with colorless := n }

/-- Count of restricted mana of type `t` with use restriction `u`. -/
def countRestricted (p : ManaPool) (t : ManaType) (u : ManaUse) : Nat :=
  (p.restricted.filter (· == (t, u))).size

/-- Set the count of restricted mana of type `t` with use restriction `u` to `n`. -/
def setRestricted (p : ManaPool) (t : ManaType) (u : ManaUse) (n : Nat) : ManaPool :=
  { p with restricted := p.restricted.filter (· != (t, u)) ++ Array.replicate n (t, u) }

/-- Spend one unit of restricted mana of type `t` matching `pred`, if available. -/
def spendRestricted? (p : ManaPool) (t : ManaType) (pred : ManaUse → Bool) : Option ManaPool :=
  match p.restricted.findIdx? (fun (t', u) => t' == t && pred u) with
  | some i => some { p.set t (p.get t - 1) with restricted := p.restricted.eraseIdx! i }
  | none => none

/-- Restricted Elf-only amount of this type. Colorless cannot be so restricted. -/
def getElf (p : ManaPool) : ManaType → Nat
  | .colorless => 0
  | t => p.countRestricted t .elf

def setElf (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colorless => p
  | _ => p.setRestricted t .elf n

/-- Restricted instant-or-sorcery-only amount of this type. -/
def getInst (p : ManaPool) : ManaType → Nat
  | .colorless => 0
  | t => p.countRestricted t .instantOrSorcery

def setInst (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colorless => p
  | _ => p.setRestricted t .instantOrSorcery n

/-- Restricted Hero-source amount of this type. -/
def getHero (p : ManaPool) : ManaType → Nat
  | .colorless => 0
  | t => p.countRestricted t .hero

def setHero (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colorless => p
  | _ => p.setRestricted t .hero n

/-- Restricted Villain-source amount of this type. -/
def getVillain (p : ManaPool) : ManaType → Nat
  | .colorless => 0
  | t => p.countRestricted t .villain

def setVillain (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colorless => p
  | _ => p.setRestricted t .villain n

/-- Restricted creature-source activation amount of this type. -/
def getCreature (p : ManaPool) : ManaType → Nat
  | .colorless => 0
  | t => p.countRestricted t .creatureSource

def setCreature (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colorless => p
  | _ => p.setRestricted t .creatureSource n

def elfWhite (p : ManaPool) : Nat := p.getElf (.colored .white)
def elfBlue (p : ManaPool) : Nat := p.getElf (.colored .blue)
def elfBlack (p : ManaPool) : Nat := p.getElf (.colored .black)
def elfRed (p : ManaPool) : Nat := p.getElf (.colored .red)
def elfGreen (p : ManaPool) : Nat := p.getElf (.colored .green)

def instWhite (p : ManaPool) : Nat := p.getInst (.colored .white)
def instBlue (p : ManaPool) : Nat := p.getInst (.colored .blue)
def instBlack (p : ManaPool) : Nat := p.getInst (.colored .black)
def instRed (p : ManaPool) : Nat := p.getInst (.colored .red)
def instGreen (p : ManaPool) : Nat := p.getInst (.colored .green)

def heroWhite (p : ManaPool) : Nat := p.getHero (.colored .white)
def heroBlue (p : ManaPool) : Nat := p.getHero (.colored .blue)
def heroBlack (p : ManaPool) : Nat := p.getHero (.colored .black)
def heroRed (p : ManaPool) : Nat := p.getHero (.colored .red)
def heroGreen (p : ManaPool) : Nat := p.getHero (.colored .green)

def villainWhite (p : ManaPool) : Nat := p.getVillain (.colored .white)
def villainBlue (p : ManaPool) : Nat := p.getVillain (.colored .blue)
def villainBlack (p : ManaPool) : Nat := p.getVillain (.colored .black)
def villainRed (p : ManaPool) : Nat := p.getVillain (.colored .red)
def villainGreen (p : ManaPool) : Nat := p.getVillain (.colored .green)

def creatureWhite (p : ManaPool) : Nat := p.getCreature (.colored .white)
def creatureBlue (p : ManaPool) : Nat := p.getCreature (.colored .blue)
def creatureBlack (p : ManaPool) : Nat := p.getCreature (.colored .black)
def creatureRed (p : ManaPool) : Nat := p.getCreature (.colored .red)
def creatureGreen (p : ManaPool) : Nat := p.getCreature (.colored .green)

def cantNonartifact (p : ManaPool) : Nat := p.countRestricted .colorless .cantNonartifact
def cantNonartifactBlue (p : ManaPool) : Nat := p.countRestricted (.colored .blue) .cantNonartifact

/-- Restricted Reality Fracture mana entries in this pool. -/
def fraRestricted (p : ManaPool) : Array (ManaType × ManaUse) :=
  p.restricted.filter (fun (_, u) => u.isFra)

/-- Restricted Reality Fracture mana of this type. -/
def fraCount (p : ManaPool) (t : ManaType) : Nat :=
  (p.restricted.filter (fun (t', u) => t' == t && u.isFra)).size

/-- Restricted Reality Fracture mana of this type that may pay for `spend`. -/
def fraUsable (p : ManaPool) (t : ManaType) (spend : ManaSpend) : Nat :=
  (p.restricted.filter (fun (t', u) => t' == t && u.isFra && u.allows spend)).size

/-- Mana of this type with no spending restriction. -/
def unrestricted (p : ManaPool) (t : ManaType) : Nat :=
  p.get t - (p.restricted.filter (·.1 == t)).size

/-- Amount of this type that may be spent under the given restrictions. -/
def usable (p : ManaPool) (t : ManaType) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) : Nat :=
  p.unrestricted t + p.fraUsable t spend +
    (if allowElfRestricted then p.getElf t else 0) +
    (if allowInstRestricted then p.getInst t else 0) +
    (if allowHeroRestricted then p.getHero t else 0) +
    (if allowVillainRestricted then p.getVillain t else 0) +
    (if allowCreatureRestricted then p.getCreature t else 0) +
    (if allowCantNonartifact && t == .colorless then p.cantNonartifact else 0) +
    (if allowCantNonartifact && t == .colored .blue then p.cantNonartifactBlue else 0)

def addWithUse (p : ManaPool) (t : ManaType) (u : ManaUse) (n : Nat := 1) : ManaPool :=
  let p := p.set t (p.get t + n)
  let valid : Bool :=
    match u with
    | .elf | .instantOrSorcery | .hero | .villain | .creatureSource => t != .colorless
    | .cantNonartifact => t == .colorless || t == .colored .blue
    | _ => true
  if valid then { p with restricted := p.restricted ++ Array.replicate n (t, u) } else p

def add (p : ManaPool) (t : ManaType) (n : Nat := 1) (elfRestricted : Bool := false)
    (instRestricted : Bool := false) (heroRestricted : Bool := false)
    (villainRestricted : Bool := false) (cantNonartifact : Bool := false)
    (creatureRestricted : Bool := false) (fra : Option ManaUse := none) : ManaPool :=
  let p := p.set t (p.get t + n)
  let push (p : ManaPool) (u : ManaUse) : ManaPool :=
    { p with restricted := p.restricted ++ Array.replicate n (t, u) }
  let p :=
    match fra with
    | some u => push p u
    | none => p
  let p := if elfRestricted && t != .colorless then push p .elf else p
  let p := if instRestricted && t != .colorless then push p .instantOrSorcery else p
  let p := if heroRestricted && t != .colorless then push p .hero else p
  let p := if villainRestricted && t != .colorless then push p .villain else p
  let p := if creatureRestricted && t != .colorless then push p .creatureSource else p
  if cantNonartifact && (t == .colorless || t == .colored .blue) then
    push p .cantNonartifact
  else p

def total (p : ManaPool) : Nat :=
  p.white + p.blue + p.black + p.red + p.green + p.colorless

/-- Try to spend one mana of the given type (CR 106.10). -/
def spendOne? (p : ManaPool) (t : ManaType) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) : Option ManaPool :=
  if p.get t == 0 then none
  else
    (p.spendRestricted? t (fun u => u.isFra && u.allows spend))
      |>.orElse (fun _ => if allowHeroRestricted then p.spendRestricted? t (· == .hero) else none)
      |>.orElse (fun _ => if allowVillainRestricted then p.spendRestricted? t (· == .villain) else none)
      |>.orElse (fun _ => if allowCreatureRestricted then p.spendRestricted? t (· == .creatureSource) else none)
      |>.orElse (fun _ => if allowElfRestricted then p.spendRestricted? t (· == .elf) else none)
      |>.orElse (fun _ => if allowInstRestricted then p.spendRestricted? t (· == .instantOrSorcery) else none)
      |>.orElse (fun _ =>
        if allowCantNonartifact && (t == .colorless || t == .colored .blue) then
          p.spendRestricted? t (· == .cantNonartifact)
        else none)
      |>.orElse (fun _ =>
        if p.unrestricted t > 0 then some (p.set t (p.get t - 1)) else none)

/-- Spend one mana of any type. Restricted Elf mana is spent first when allowed,
then instant/sorcery-restricted mana, then colorless, then WUBRG (CR 106.10). -/
def spendAny? (p : ManaPool) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) : Option ManaPool :=
  let colored : List ManaType :=
    [.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
  let order : List ManaType := [.colorless] ++ colored
  Id.run do
    if let some (t, _) := p.restricted.find? (fun (_, u) => u.isFra && u.allows spend) then
      if let some p' := p.spendOne? t (spend := spend) then
        return some p'
    if allowElfRestricted then
      for t in colored do
        if p.getElf t > 0 then
          if let some p' := p.spendOne? t true then
            return some p'
    if allowInstRestricted then
      for t in colored do
        if p.getInst t > 0 then
          if let some p' := p.spendOne? t false true then
            return some p'
    if allowHeroRestricted then
      for t in colored do
        if p.getHero t > 0 then
          if let some p' := p.spendOne? t false false true then
            return some p'
    if allowVillainRestricted then
      for t in colored do
        if p.getVillain t > 0 then
          if let some p' := p.spendOne? t false false false true then
            return some p'
    if allowCreatureRestricted then
      for t in colored do
        if p.getCreature t > 0 then
          if let some p' :=
              p.spendOne? t false false false false false true then
            return some p'
    for t in order do
      if let some p' := p.spendOne? t allowElfRestricted allowInstRestricted
          allowHeroRestricted allowVillainRestricted allowCantNonartifact
          allowCreatureRestricted spend then
        return some p'
    return none

/-- Pay a mana cost, requiring colored/colorless symbols first, then generic (CR 202).
`allowElfRestricted` permits mana that may be spent only on Elf spells and
abilities (CR 106.10). `allowInstRestricted` permits mana that may be spent
only on instant or sorcery spells. -/
def pay? (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) : Option ManaPool :=
  Id.run do
    let mut pool := p
    let mut unpaidTwobrid : Nat := 0
    -- Specific symbols first so leftover mana of other types can pay generic
    -- (e.g. `{U}×1 {R}×1` pays `{1}{U}`). Printed order would spend `{U}` on
    -- `{1}` via `spendAny?` and then fail the `{U}`.
    -- `{2/C}` prefers one mana of that color, then two mana of any type.
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOne? (.colored c) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' => pool := p'
        | none => return none
      | .colorless =>
        match pool.spendOne? .colorless allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' => pool := p'
        | none => return none
      | .hybrid a b =>
        match pool.spendOne? (.colored a) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' => pool := p'
        | none =>
          match pool.spendOne? (.colored b) allowElfRestricted allowInstRestricted
              allowHeroRestricted allowVillainRestricted allowCantNonartifact
              allowCreatureRestricted spend with
          | some p' => pool := p'
          | none => return none
      | .twobrid c =>
        match pool.spendOne? (.colored c) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' => pool := p'
        | none => unpaidTwobrid := unpaidTwobrid + 1
      | .generic _ | .x => pure () -- CR 107.3g: unpaid `{X}` is 0
    for _ in [0:unpaidTwobrid] do
      for _ in [0:2] do
        match pool.spendAny? allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' => pool := p'
        | none => return none
    for s in cost.symbols do
      match s with
      | .generic n =>
        for _ in [0:n] do
          match pool.spendAny? allowElfRestricted allowInstRestricted
              allowHeroRestricted allowVillainRestricted allowCantNonartifact
              allowCreatureRestricted spend with
          | some p' => pool := p'
          | none => return none
      | _ => pure ()
    return some pool

def canPay (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) : Bool :=
  (p.pay? cost allowElfRestricted allowInstRestricted
    allowHeroRestricted allowVillainRestricted allowCantNonartifact
    allowCreatureRestricted spend).isSome

/-- How much of `cost` this pool can cover, in mana (CR 202.3). Unpayable
symbols are skipped so leftover generic-capable mana still counts. -/
def coveredMana (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) : Nat :=
  Id.run do
    let mut pool := p
    let mut paid := 0
    let mut unpaidTwobrid : Nat := 0
    -- Match `pay?`: cover colored/colorless/hybrid first so leftover mana
    -- still counts toward generic.
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOne? (.colored c) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' =>
          pool := p'
          paid := paid + 1
        | none => pure ()
      | .colorless =>
        match pool.spendOne? .colorless allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' =>
          pool := p'
          paid := paid + 1
        | none => pure ()
      | .hybrid a b =>
        match pool.spendOne? (.colored a) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' =>
          pool := p'
          paid := paid + 1
        | none =>
          match pool.spendOne? (.colored b) allowElfRestricted allowInstRestricted
              allowHeroRestricted allowVillainRestricted allowCantNonartifact
              allowCreatureRestricted spend with
          | some p' =>
            pool := p'
            paid := paid + 1
          | none => pure ()
      | .twobrid c =>
        match pool.spendOne? (.colored c) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' =>
          pool := p'
          paid := paid + 2
        | none => unpaidTwobrid := unpaidTwobrid + 1
      | .generic _ | .x => pure ()
    for _ in [0:unpaidTwobrid] do
      for _ in [0:2] do
        match pool.spendAny? allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some p' =>
          pool := p'
          paid := paid + 1
        | none => pure ()
    for s in cost.symbols do
      match s with
      | .generic n =>
        for _ in [0:n] do
          match pool.spendAny? allowElfRestricted allowInstRestricted
              allowHeroRestricted allowVillainRestricted allowCantNonartifact
              allowCreatureRestricted spend with
          | some p' =>
            pool := p'
            paid := paid + 1
          | none => pure ()
      | _ => pure ()
    return paid

/-- One `{C}×n` fragment, plus optional restriction labels. -/
def poolPart (letter : String) (free elf inst : Nat) (hero := 0) (villain := 0)
    (cantNonartifact := 0) (creature := 0) : List String :=
  (if free > 0 then [s!"\{{letter}}×{free}"] else []) ++
  (if elf > 0 then [s!"\{{letter}}×{elf} (Elf)"] else []) ++
  (if inst > 0 then [s!"\{{letter}}×{inst} (instant/sorcery)"] else []) ++
  (if hero > 0 then [s!"\{{letter}}×{hero} (Hero)"] else []) ++
  (if villain > 0 then [s!"\{{letter}}×{villain} (Villain)"] else []) ++
  (if creature > 0 then [s!"\{{letter}}×{creature} (creature source)"] else []) ++
  (if cantNonartifact > 0 then [s!"\{{letter}}×{cantNonartifact} (not nonartifact spell)"] else [])

def toNotation (p : ManaPool) : String :=
  if p.isEmpty then "{}"
  else
    let parts :=
      poolPart "W" (p.unrestricted (.colored .white)) p.elfWhite p.instWhite
        p.heroWhite p.villainWhite 0 p.creatureWhite ++
      poolPart "U" (p.unrestricted (.colored .blue)) p.elfBlue p.instBlue
        p.heroBlue p.villainBlue 0 p.creatureBlue ++
      poolPart "B" (p.unrestricted (.colored .black)) p.elfBlack p.instBlack
        p.heroBlack p.villainBlack 0 p.creatureBlack ++
      poolPart "R" (p.unrestricted (.colored .red)) p.elfRed p.instRed
        p.heroRed p.villainRed 0 p.creatureRed ++
      poolPart "G" (p.unrestricted (.colored .green)) p.elfGreen p.instGreen
        p.heroGreen p.villainGreen 0 p.creatureGreen ++
      poolPart "C" (p.unrestricted .colorless) 0 0 0 0 p.cantNonartifact ++
      p.fraRestricted.toList.map (fun (t, u) => s!"\{{t.letter}} ({u.label})")
    String.intercalate " " parts

instance : ToString ManaPool where
  toString := toNotation

theorem empty_isEmpty : ManaPool.empty.isEmpty = true := rfl

#guard (ManaPool.empty.add (.colored .red) 2 |>.add .colorless 1).total == 3
#guard ((ManaPool.empty.add (.colored .green) 1 |>.add .colorless 1).pay?
         (ManaCost.ofGenericAndColor 1 .green)).isSome
#guard ((ManaPool.empty.add (.colored .green) 1).pay?
         (ManaCost.ofGenericAndColor 1 .green)).isNone
#guard
  let p := ManaPool.empty.add (.colored .blue) 1 |>.add (.colored .red) 1
  toString p == "{U}×1 {R}×1" &&
    (p.pay? (ManaCost.ofGenericAndColor 1 .blue)).isSome &&
    p.canPay (ManaCost.ofGenericAndColor 1 .blue) &&
    p.coveredMana (ManaCost.ofGenericAndColor 1 .blue) == 2
#guard
  let p := ManaPool.empty.add (.colored .red) 1 |>.add (.colored .green) 1
  (p.pay? (ManaCost.ofGenericAndColor 1 .blue)).isNone &&
    p.coveredMana (ManaCost.ofGenericAndColor 1 .blue) == 1
#guard
  let p := ManaPool.empty.add (.colored .green) 2 (elfRestricted := true)
  p.total == 2 && p.elfGreen == 2 && p.unrestricted (.colored .green) == 0 &&
    (p.pay? (ManaCost.ofColor .green)).isNone &&
    (p.pay? (ManaCost.ofColor .green) true).isSome
#guard
  let p := ManaPool.empty.add (.colored .green) 1 |>.add (.colored .green) 1
    (elfRestricted := true)
  (p.pay? (ManaCost.ofColor .green)).isSome &&
    ((p.pay? (ManaCost.ofColor .green)).getD p).elfGreen == 1 &&
    (p.pay? (ManaCost.ofGeneric 2)).isNone &&
    (p.pay? (ManaCost.ofGeneric 2) true).isSome
#guard (ManaPool.empty.add (.colored .green) 1).coveredMana (ManaCost.ofColor .red) == 0
#guard (ManaPool.empty.add (.colored .green) 1).coveredMana (ManaCost.ofGenericAndColor 1 .red) == 1
#guard (ManaPool.empty.add (.colored .red) 1).coveredMana (ManaCost.ofColor .red) == 1
#guard
  let p := ManaPool.empty.add (.colored .green) 1 (elfRestricted := true)
  p.coveredMana (ManaCost.ofColor .green) == 0 &&
    p.coveredMana (ManaCost.ofColor .green) true == 1 &&
    p.usable (.colored .green) == 0 &&
    p.usable (.colored .green) true == 1
#guard (ManaCost.ofGenericAndColor 1 .green).coloredCount .green == 1
#guard (ManaCost.ofGenericAndColor 1 .green).coloredCount .red == 0
#guard (ManaCost.ofHybrid .black .red).coloredCount .black == 0
#guard (ManaCost.ofHybrid .black .red).symbolsIncludingColor .black == 1
#guard (ManaCost.ofHybrid .black .red).symbolsIncludingColor .red == 1
#guard (ManaCost.ofHybrid .black .red).symbolsIncludingColor .green == 0
#guard toString (ManaPool.empty.add (.colored .green) 2 (elfRestricted := true)) ==
  "{G}×2 (Elf)"
#guard
  let p := ManaPool.empty.add (.colored .black) 1
  (p.pay? (ManaCost.ofHybrid .black .green)).isSome
#guard
  let p := ManaPool.empty.add (.colored .green) 1
  (p.pay? (ManaCost.ofHybrid .black .green)).isSome
#guard
  let p := ManaPool.empty.add (.colored .red) 1
  (p.pay? (ManaCost.ofHybrid .black .green)).isNone
#guard
  let p := ManaPool.empty.add (.colored .white) 1 (heroRestricted := true)
  p.heroWhite == 1 && (p.pay? (ManaCost.ofColor .white)).isNone &&
    (p.pay? (ManaCost.ofColor .white) false false true).isSome
#guard
  let p := ManaPool.empty.add .colorless 1 (cantNonartifact := true)
  (p.pay? (ManaCost.ofGeneric 1)).isNone &&
    (p.pay? (ManaCost.ofGeneric 1) false false false false true).isSome
#guard
  let p := ManaPool.empty.add (.colored .blue) 1 (cantNonartifact := true)
  (p.pay? (ManaCost.ofColor .blue)).isNone &&
    (p.pay? (ManaCost.ofColor .blue) false false false false true).isSome
#guard
  let p := ManaPool.empty.add (.colored .green) 2 (creatureRestricted := true)
  p.creatureGreen == 2 && (p.pay? (ManaCost.ofGeneric 2)).isNone &&
    (p.pay? (ManaCost.ofGeneric 2) false false false false false true).isSome

end ManaPool

end Mtg.Engine
