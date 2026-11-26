import Mtg.Engine.Card.ManaTypes

/-!
# Mana (CR 106, 107.4, 202)

Mana is the primary resource in the game. There are six types of mana: the
five colors and colorless (CR 106.1b). Players spend mana to pay costs.
Layer-0 runtime mana types (`ManaType`, `ManaOutput`, `ManaObjectPred`,
`ManaAbilityPred`, `SpellRiderSpec`, `ManaSpend`, `ManaSpendRestriction`)
live in `Mtg.Engine.Card.ManaTypes` and are re-exported here alongside
`ManaCost` and `ManaPool`; symbolic `ManaSpec` / `ManaPoolPalette` live in
`Mtg.Engine.Card.ManaSpec` above `Mtg.Engine.Card.Expr`.
-/

namespace Mtg.Engine

/-- A symbol that can appear in a mana cost (subset of CR 107.4). -/
inductive ManaSymbol where
  /-- Generic mana in costs, payable with any type (CR 107.4b). -/
  | generic (n : Nat)
  /-- One mana of a specific color (CR 107.4a). -/
  | colored (color : Color)
  /-- The colorless mana symbol `{C}` (CR 107.4c). -/
  | colorless
  /-- A monocolored hybrid symbol `{A/B}` (CR 107.4e). Payable with either color. -/
  | hybrid (a b : Color)
  /-- A monocolored hybrid with generic mana `{2/C}` (CR 107.4e). Payable with
  two mana of any type, or one mana of `c`. Mana value is 2. -/
  | twobrid (c : Color)
  /-- The variable symbol `{X}` (CR 107.3). Treated as 0 off the stack (CR 107.3g). -/
  | x
deriving DecidableEq, Repr, Inhabited

namespace ManaSymbol

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

/-- The payable zero mana cost `{0}` (CR 107.4d / 118.5). Distinct from
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

/-- Convert colored, colorless, hybrid, and twobrid mana symbols to `{1}` each
while preserving `{X}` symbols (CR 107.3 / 107.4e / 118.14 / 609.4b: spending
mana as though it were mana of any type/color). -/
def asAnyMana (cost : ManaCost) : ManaCost :=
  if cost.symbols.isEmpty then empty
  else
    let gen := cost.symbols.foldl
      (fun acc s =>
        match s with
        | .generic n => acc + n
        | .colored _ | .colorless | .hybrid _ _ | .twobrid _ => acc + 1
        | .x => acc)
      0
    let xs := cost.symbols.filter (· == .x)
    if gen == 0 && xs.isEmpty then zero
    else if gen == 0 then { symbols := xs }
    else { symbols := xs ++ #[.generic gen] }

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
(CR 118.7a). Colored symbols are unchanged. -/
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

/-- One unit of mana in a mana pool or mana event, with its type, producing
source, spending restriction, Treasure provenance, and spell riders
(CR 106.1 / 106.6). -/
structure ManaUnit where
  mana : ManaType
  source : Option ObjectId := none
  restriction : Option ManaSpendRestriction := none
  fromTreasure : Bool := false
  riders : Array SpellRiderSpec := #[]
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaUnit

/-- All spell riders carried by `u`, combining explicit `riders` with any riders
attached to `u.restriction` (CR 106.6). -/
def allRiders (u : ManaUnit) : Array SpellRiderSpec :=
  let fromRestr :=
    match u.restriction with
    | some r => r.riders
    | none => #[]
  u.riders.foldl (fun acc r => if acc.contains r then acc else acc.push r) fromRestr

/-- Whether `u` carries spell rider `r` (either directly or on its restriction). -/
def hasRider (u : ManaUnit) (r : SpellRiderSpec) : Bool :=
  u.riders.contains r ||
    match u.restriction with
    | some restr => restr.riders.contains r
    | none => false

end ManaUnit

/-- Unspent mana a player currently has, stored as individual `ManaUnit`s
preserving source, spending-restriction, and rider provenance (CR 106.4 / 106.6). -/
structure ManaPool where
  units : Array ManaUnit := #[]
deriving BEq, DecidableEq, Repr, Inhabited

namespace ManaPool

def empty : ManaPool := {}

def isEmpty (p : ManaPool) : Bool :=
  p.units.isEmpty

/-- Enumerate all mana units currently in `p` (CR 106.4). -/
@[inline] def toUnits (p : ManaPool) : Array ManaUnit :=
  p.units

def total (p : ManaPool) : Nat :=
  p.units.size

private def countWhere (p : ManaPool) (pred : ManaUnit → Bool) : Nat :=
  p.units.foldl (fun acc u => if pred u then acc + 1 else acc) 0

private def eraseFirst? {α : Type} (xs : Array α) (pred : α → Bool) : Option (Array α × α) :=
  match xs.findIdx? pred with
  | some i =>
    if h : i < xs.size then
      some (xs.eraseIdx i h, xs[i])
    else
      none
  | none => none

def get (p : ManaPool) (t : ManaType) : Nat :=
  p.countWhere (·.mana == t)

def white (p : ManaPool) : Nat := p.get (.colored .white)
def blue (p : ManaPool) : Nat := p.get (.colored .blue)
def black (p : ManaPool) : Nat := p.get (.colored .black)
def red (p : ManaPool) : Nat := p.get (.colored .red)
def green (p : ManaPool) : Nat := p.get (.colored .green)
def colorless (p : ManaPool) : Nat := p.get .colorless

def set (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  { units := p.units.filter (·.mana != t) ++ Array.replicate n { mana := t } }

def countRestricted (p : ManaPool) (t : ManaType) (r : ManaSpendRestriction) : Nat :=
  p.countWhere (fun u => u.mana == t && u.restriction == some r)

/-- Restricted Elf-only amount of this type. -/
def getElf (p : ManaPool) (t : ManaType) : Nat := p.countRestricted t .elf
def elfWhite (p : ManaPool) : Nat := p.getElf (.colored .white)
def elfGreen (p : ManaPool) : Nat := p.getElf (.colored .green)

/-- Restricted instant-or-sorcery-only amount of this type. -/
def getInst (p : ManaPool) (t : ManaType) : Nat := p.countRestricted t .instantOrSorcery

/-- Restricted Hero-source amount of this type. -/
def getHero (p : ManaPool) (t : ManaType) : Nat := p.countRestricted t .hero
def heroWhite (p : ManaPool) : Nat := p.getHero (.colored .white)

/-- Restricted Villain-source amount of this type. -/
def getVillain (p : ManaPool) (t : ManaType) : Nat := p.countRestricted t .villain
def villainBlack (p : ManaPool) : Nat := p.getVillain (.colored .black)

/-- Restricted creature-source activation amount of this type. -/
def getCreature (p : ManaPool) (t : ManaType) : Nat := p.countRestricted t .creatureSource
def creatureGreen (p : ManaPool) : Nat := p.getCreature (.colored .green)

/-- Colorless mana that cannot be spent to cast a nonartifact spell (Vibranium tokens). -/
def cantNonartifact (p : ManaPool) : Nat := p.countRestricted .colorless .cantNonartifact

/-- Blue mana that cannot be spent to cast a nonartifact spell (Hydraulic Helper). -/
def cantNonartifactBlue (p : ManaPool) : Nat := p.countRestricted (.colored .blue) .cantNonartifact

/-- Entries in `p` carrying a spending restriction (CR 106.6). -/
def restrictedEntries (p : ManaPool) : Array (ManaType × ManaSpendRestriction) :=
  p.units.filterMap fun u => u.restriction.map (u.mana, ·)

/-- Mana of this type with no spending restriction (CR 106.6). -/
def unrestricted (p : ManaPool) (t : ManaType) : Nat :=
  p.countWhere fun u => u.mana == t && u.restriction.isNone

/-- Amount of this type that may be spent in `spend` context (CR 106.6). -/
def usable (p : ManaPool) (t : ManaType) (spend : ManaSpend := {}) : Nat :=
  p.countWhere fun u =>
    u.mana == t &&
      match u.restriction with
      | none => true
      | some r => r.allows spend

/-- Add one `ManaUnit` to `p` (CR 106.4 / 106.6). -/
def addUnit (p : ManaPool) (u : ManaUnit) : ManaPool :=
  { units := p.units.push u }

/-- Add `units` to `p` in order (CR 106.4 / 106.6). -/
def addUnits (p : ManaPool) (units : Array ManaUnit) : ManaPool :=
  units.foldl addUnit p

/-- Remove one `ManaUnit` from `p` (CR 106.4 / 106.6). Matches `source` when
present; falls back to matching `mana`, `restriction`, and `riders` when
`u.source` is `none`. -/
def removeUnit (p : ManaPool) (u : ManaUnit) : ManaPool :=
  match eraseFirst? p.units (· == u) with
  | some (us, _) => { units := us }
  | none =>
    if u.source.isSome then
      match eraseFirst? p.units (fun u' =>
          u'.mana == u.mana && u'.source == u.source && u'.restriction == u.restriction &&
            u'.riders == u.riders) with
      | some (us, _) => { units := us }
      | none => p
    else
      match eraseFirst? p.units (fun u' =>
          u'.mana == u.mana && u'.restriction == u.restriction && u'.riders == u.riders) with
      | some (us, _) => { units := us }
      | none => p

/-- Remove `units` from `p` in order (CR 106.4 / 106.6). -/
def removeUnits (p : ManaPool) (units : Array ManaUnit) : ManaPool :=
  units.foldl removeUnit p

/-- Add `n` units of mana of type `t` with optional `restriction`, `source`,
Treasure provenance, and `riders` (CR 106.4 / 106.6). -/
def add (p : ManaPool) (t : ManaType) (n : Nat := 1)
    (restriction : Option ManaSpendRestriction := none)
    (source : Option ObjectId := none) (fromTreasure : Bool := false)
    (riders : Array SpellRiderSpec := #[]) : ManaPool :=
  p.addUnits (Array.replicate n { mana := t, source, restriction, fromTreasure, riders })

/-- Try to spend one mana of the given type, returning the updated pool and the
`ManaUnit` spent. Narrow positive restrictions are spent before broad negative
restrictions and unrestricted mana (CR 106.6). -/
def spendOneUnit? (p : ManaPool) (t : ManaType) (spend : ManaSpend := {}) :
    Option (ManaPool × ManaUnit) :=
  let take (pred : ManaUnit → Bool) : Option (ManaPool × ManaUnit) :=
    (eraseFirst? p.units (fun u => u.mana == t && pred u)).map fun (us, u) => ({ units := us }, u)
  (take fun u => match u.restriction with | some r => r.isNarrow && r.allows spend | none => false)
    <|> (take fun u => match u.restriction with | some r => !r.isNarrow && r.allows spend | none => false)
    <|> (take fun u => u.restriction.isNone && spend.spell && !u.riders.isEmpty)
    <|> (take fun u => u.restriction.isNone && u.fromTreasure)
    <|> (take fun u => u.restriction.isNone && u.riders.isEmpty)
    <|> (take fun u => u.restriction.isNone)

/-- Try to spend one mana of the given type (CR 106.6). -/
def spendOne? (p : ManaPool) (t : ManaType) (spend : ManaSpend := {}) : Option ManaPool :=
  (p.spendOneUnit? t spend).map Prod.fst

/-- Spend one mana of any type, returning the updated pool and the `ManaUnit`
spent. Narrow restricted mana is spent first, then broad negative restrictions,
then unrestricted mana (preferring rider mana for spells and Treasure-provenance
mana); within each tier colorless precedes WUBRG (CR 106.6). -/
def spendAnyUnit? (p : ManaPool) (spend : ManaSpend := {}) :
    Option (ManaPool × ManaUnit) :=
  let colored : List ManaType :=
    [.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
  let order : List ManaType := [.colorless] ++ colored
  let takeFirst (pred : ManaUnit → Bool) : Option (ManaPool × ManaUnit) :=
    Id.run do
      for t in order do
        if let some (us, u) := eraseFirst? p.units (fun u => u.mana == t && pred u) then
          return some ({ units := us }, u)
      return none
  (takeFirst fun u => match u.restriction with | some r => r.isNarrow && r.allows spend | none => false)
    <|> (takeFirst fun u => match u.restriction with | some r => !r.isNarrow && r.allows spend | none => false)
    <|> (takeFirst fun u => u.restriction.isNone && spend.spell && !u.riders.isEmpty)
    <|> (takeFirst fun u => u.restriction.isNone && u.fromTreasure)
    <|> (takeFirst fun u => u.restriction.isNone && u.riders.isEmpty)
    <|> (takeFirst fun u => u.restriction.isNone)

/-- Spend one mana of any type under `spend` context (CR 106.6). -/
def spendAny? (p : ManaPool) (spend : ManaSpend := {}) : Option ManaPool :=
  (p.spendAnyUnit? spend).map Prod.fst

private structure ColorCounts where
  w : Nat := 0
  u : Nat := 0
  b : Nat := 0
  r : Nat := 0
  g : Nat := 0

private def ColorCounts.get (cc : ColorCounts) : Color → Nat
  | .white => cc.w
  | .blue => cc.u
  | .black => cc.b
  | .red => cc.r
  | .green => cc.g

private def ColorCounts.sub (cc : ColorCounts) (c : Color) (n : Nat) : ColorCounts :=
  match c with
  | .white => { cc with w := cc.w - n }
  | .blue => { cc with u := cc.u - n }
  | .black => { cc with b := cc.b - n }
  | .red => { cc with r := cc.r - n }
  | .green => { cc with g := cc.g - n }

private def usableColorCounts (p : ManaPool) (spend : ManaSpend) : ColorCounts × Nat :=
  let w := p.usable (.colored .white) spend
  let u := p.usable (.colored .blue) spend
  let b := p.usable (.colored .black) spend
  let r := p.usable (.colored .red) spend
  let g := p.usable (.colored .green) spend
  let c := p.usable .colorless spend
  ({ w, u, b, r, g }, w + u + b + r + g + c)

private def groupFlexibleSymbols (cost : ManaCost) :
    Array (Color × Nat) × Array (Color × Color × Nat) × Nat := Id.run do
  let mut twobrids : Array (Color × Nat) := #[]
  let mut hybrids : Array (Color × Color × Nat) := #[]
  let mut genericNeed : Nat := 0
  for s in cost.symbols do
    match s with
    | .twobrid c =>
      match twobrids.findIdx? (fun (c', _) => c' == c) with
      | some i =>
        let (_, k) := twobrids[i]!
        twobrids := twobrids.set! i (c, k + 1)
      | none => twobrids := twobrids.push (c, 1)
    | .hybrid a b =>
      if a != b then
        match hybrids.findIdx? (fun (a', b', _) => a' == a && b' == b) with
        | some i =>
          let (_, _, k) := hybrids[i]!
          hybrids := hybrids.set! i (a, b, k + 1)
        | none => hybrids := hybrids.push (a, b, 1)
    | .generic n => genericNeed := genericNeed + n
    | _ => pure ()
  return (twobrids, hybrids, genericNeed)

private def solveHybridsPay (hybrids : List (Color × Color × Nat))
    (cc : ColorCounts) : Option (List Nat) :=
  match hybrids with
  | [] => some []
  | (a, b, k) :: rest =>
    let availA := cc.get a
    let availB := cc.get b
    if availA + availB < k then none
    else
      let maxA := Nat.min k availA
      let minA := k - Nat.min k availB
      let rec tryA (ka : Nat) : Option (List Nat) :=
        let kb := k - ka
        let cc' := (cc.sub a ka).sub b kb
        match solveHybridsPay rest cc' with
        | some restA => some (ka :: restA)
        | none =>
          if ka > minA then tryA (ka - 1) else none
      tryA maxA

private def solveTwobridsPay (twobrids : List (Color × Nat))
    (hybrids : List (Color × Color × Nat)) (totalHybrids : Nat)
    (cc : ColorCounts) (totalRem : Nat) (genericNeed : Nat) :
    Option (List Nat × List Nat × Nat) :=
  match twobrids with
  | [] =>
    if totalRem < totalHybrids + genericNeed then none
    else
      (solveHybridsPay hybrids cc).map fun hybAs => ([], hybAs, genericNeed)
  | (c, k) :: rest =>
    let restMinUnits := rest.foldl (fun acc (_, rk) => acc + rk) 0
    if totalRem < k + restMinUnits + totalHybrids + genericNeed then none
    else
      let maxJ := Nat.min k (cc.get c)
      let minTotalNeeded := 2 * k + restMinUnits + totalHybrids + genericNeed
      let minJ := if totalRem ≥ minTotalNeeded then 0 else minTotalNeeded - totalRem
      if minJ > maxJ then none
      else
        let rec tryJ (j : Nat) : Option (List Nat × List Nat × Nat) :=
          let genericAdded := 2 * (k - j)
          match solveTwobridsPay rest hybrids totalHybrids (cc.sub c j) (totalRem - j)
              (genericNeed + genericAdded) with
          | some (restJs, hybAs, finalGen) => some (j :: restJs, hybAs, finalGen)
          | none =>
            if j > minJ then tryJ (j - 1) else none
        tryJ maxJ

private def solveHybridsCover (hybrids : List (Color × Color × Nat))
    (cc : ColorCounts) (paidSoFar : Nat) (remCap : Nat) (best : Nat) : Nat :=
  if paidSoFar + remCap ≤ best then best
  else
    match hybrids with
    | [] => Nat.max best paidSoFar
    | (a, b, k) :: rest =>
      let availA := cc.get a
      let availB := cc.get b
      let m := Nat.min k (availA + availB)
      let restCap := remCap - k
      if m == 0 then
        solveHybridsCover rest cc paidSoFar restCap best
      else
        let maxA := Nat.min m availA
        let minA := m - Nat.min m availB
        Id.run do
          let mut curBest := best
          for off in [0 : maxA - minA + 1] do
            if paidSoFar + remCap ≤ curBest then break
            let ka := maxA - off
            let kb := m - ka
            let cc' := (cc.sub a ka).sub b kb
            curBest := solveHybridsCover rest cc' (paidSoFar + m) restCap curBest
          return curBest

private def solveTwobridsCover (twobrids : List (Color × Nat))
    (hybrids : List (Color × Color × Nat)) (totalHybrids : Nat)
    (cc : ColorCounts) (totalRem : Nat) (paidSoFar : Nat) (genericNeed : Nat)
    (maxPossible : Nat) (best : Nat) : Nat :=
  if best ≥ maxPossible then best
  else
    match twobrids with
    | [] =>
      let maxH := solveHybridsCover hybrids cc 0 totalHybrids 0
      let extra := Nat.min totalRem (maxH + genericNeed)
      Nat.max best (paidSoFar + extra)
    | (c, k) :: rest =>
      let maxJ := Nat.min k (cc.get c)
      Id.run do
        let mut curBest := best
        for off in [0 : maxJ + 1] do
          if curBest ≥ maxPossible then break
          let j := maxJ - off
          let genericAdded := 2 * (k - j)
          curBest :=
            solveTwobridsCover rest hybrids totalHybrids (cc.sub c j) (totalRem - j)
              (paidSoFar + 2 * j) (genericNeed + genericAdded) maxPossible curBest
        return curBest

/-- Pay a mana cost, paying fixed colored/colorless symbols first, then
backtracking over hybrid/twobrid symbols, then paying generic mana (CR 107.4e / 202),
returning the updated pool and the `ManaUnit`s spent. -/
def payUnits? (p : ManaPool) (cost : ManaCost) (spend : ManaSpend := {}) :
    Option (ManaPool × Array ManaUnit) :=
  Id.run do
    let mut pool := p
    let mut units : Array ManaUnit := #[]
    -- Pass 1: fixed colored/colorless symbols (including degenerate `{c/c}` hybrids).
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOneUnit? (.colored c) spend with
        | some (p', u) => pool := p'; units := units.push u
        | none => return none
      | .colorless =>
        match pool.spendOneUnit? .colorless spend with
        | some (p', u) => pool := p'; units := units.push u
        | none => return none
      | .hybrid a b =>
        if a == b then
          match pool.spendOneUnit? (.colored a) spend with
          | some (p', u) => pool := p'; units := units.push u
          | none => return none
      | .twobrid _ | .generic _ | .x => pure () -- CR 107.3g: unpaid `{X}` is 0
    -- Pass 2: backtrack over `.twobrid` and `.hybrid` symbols before `.generic`.
    let (twobrids, hybrids, baseGeneric) := groupFlexibleSymbols cost
    let finalGeneric ←
      if twobrids.isEmpty && hybrids.isEmpty then
        pure baseGeneric
      else
        let (cc, totalRem) := usableColorCounts pool spend
        let totalHybrids := hybrids.foldl (fun acc (_, _, k) => acc + k) 0
        match solveTwobridsPay twobrids.toList hybrids.toList totalHybrids cc totalRem baseGeneric with
        | none => return none
        | some (twobridJs, hybridAs, genNeed) =>
          let mut tbRem := twobridJs.toArray
          let mut hybARem := hybridAs.toArray
          let mut hybBRem :=
            (List.zip hybrids.toList hybridAs).toArray.map fun ((_, _, k), ka) => k - ka
          for s in cost.symbols do
            match s with
            | .twobrid c =>
              if let some i := twobrids.findIdx? (fun (c', _) => c' == c) then
                if tbRem[i]! > 0 then
                  tbRem := tbRem.set! i (tbRem[i]! - 1)
                  match pool.spendOneUnit? (.colored c) spend with
                  | some (p', u) => pool := p'; units := units.push u
                  | none => return none
            | .hybrid a b =>
              if a != b then
                if let some i := hybrids.findIdx? (fun (a', b', _) => a' == a && b' == b) then
                  if hybARem[i]! > 0 then
                    hybARem := hybARem.set! i (hybARem[i]! - 1)
                    match pool.spendOneUnit? (.colored a) spend with
                    | some (p', u) => pool := p'; units := units.push u
                    | none => return none
                  else if hybBRem[i]! > 0 then
                    hybBRem := hybBRem.set! i (hybBRem[i]! - 1)
                    match pool.spendOneUnit? (.colored b) spend with
                    | some (p', u) => pool := p'; units := units.push u
                    | none => return none
                  else
                    return none
            | _ => pure ()
          pure genNeed
    -- Pass 3: generic mana (including twobrid `{2}` payments).
    for _ in [0:finalGeneric] do
      match pool.spendAnyUnit? spend with
      | some (p', u) => pool := p'; units := units.push u
      | none => return none
    return some (pool, units)

/-- Pay a mana cost, requiring colored/colorless symbols first, then hybrid/twobrid,
then generic (CR 107.4e / 202 / 106.6). -/
def pay? (p : ManaPool) (cost : ManaCost) (spend : ManaSpend := {}) : Option ManaPool :=
  (p.payUnits? cost spend).map Prod.fst

def canPay (p : ManaPool) (cost : ManaCost) (spend : ManaSpend := {}) : Bool :=
  (p.pay? cost spend).isSome

/-- How much of `cost` this pool can cover, in mana (CR 202.3). Fixed
colored/colorless symbols are covered first, then hybrid/twobrid symbols are
matched via backtracking before generic slots. -/
def coveredMana (p : ManaPool) (cost : ManaCost) (spend : ManaSpend := {}) : Nat :=
  Id.run do
    let mut pool := p
    let mut fixedPaid := 0
    -- Pass 1: cover fixed colored/colorless symbols first.
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOne? (.colored c) spend with
        | some p' =>
          pool := p'
          fixedPaid := fixedPaid + 1
        | none => pure ()
      | .colorless =>
        match pool.spendOne? .colorless spend with
        | some p' =>
          pool := p'
          fixedPaid := fixedPaid + 1
        | none => pure ()
      | .hybrid a b =>
        if a == b then
          match pool.spendOne? (.colored a) spend with
          | some p' =>
            pool := p'
            fixedPaid := fixedPaid + 1
          | none => pure ()
      | .twobrid _ | .generic _ | .x => pure ()
    -- Pass 2: backtrack over `.twobrid` and `.hybrid` symbols before `.generic`.
    let (twobrids, hybrids, baseGeneric) := groupFlexibleSymbols cost
    let (cc, totalRem) := usableColorCounts pool spend
    if twobrids.isEmpty && hybrids.isEmpty then
      return fixedPaid + Nat.min totalRem baseGeneric
    else
      let totalHybrids := hybrids.foldl (fun acc (_, _, k) => acc + k) 0
      return solveTwobridsCover twobrids.toList hybrids.toList totalHybrids
        cc totalRem fixedPaid baseGeneric cost.manaValue fixedPaid

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

private def isCompactPoolRestriction (r : ManaSpendRestriction) : Bool :=
  r == .elf || r == .instantOrSorcery || r == .hero || r == .villain ||
    r == .creatureSource || r == .cantNonartifact

def toNotation (p : ManaPool) : String :=
  if p.isEmpty then "{}"
  else
    let types : List (String × ManaType) :=
      [("W", .colored .white), ("U", .colored .blue), ("B", .colored .black),
       ("R", .colored .red), ("G", .colored .green), ("C", .colorless)]
    let otherRestricted :=
      p.units.toList.filterMap fun u =>
        match u.restriction with
        | some r => if isCompactPoolRestriction r then none else some s!"\{{u.mana.letter}} ({r.label})"
        | none => none
    let parts :=
      (types.map fun (letter, t) =>
        poolPart letter (p.unrestricted t) (p.getElf t) (p.getInst t)
          (p.getHero t) (p.getVillain t) (p.countRestricted t .cantNonartifact)
          (p.getCreature t)).flatten ++
      otherRestricted
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
  let p := ManaPool.empty.add (.colored .green) 2 (restriction := some .elf)
  let elfSpell := ManaSpend.forSpell (subtypes := #[.elf])
  p.total == 2 && p.elfGreen == 2 && p.unrestricted (.colored .green) == 0 &&
    (p.pay? (ManaCost.ofColor .green)).isNone &&
    (p.pay? (ManaCost.ofColor .green) elfSpell).isSome
#guard
  let p := ManaPool.empty.add (.colored .green) 1 |>.add (.colored .green) 1
    (restriction := some .elf)
  let elfSpell := ManaSpend.forSpell (subtypes := #[.elf])
  (p.pay? (ManaCost.ofColor .green)).isSome &&
    ((p.pay? (ManaCost.ofColor .green)).getD p).elfGreen == 1 &&
    (p.pay? (ManaCost.ofGeneric 2)).isNone &&
    (p.pay? (ManaCost.ofGeneric 2) elfSpell).isSome
#guard (ManaPool.empty.add (.colored .green) 1).coveredMana (ManaCost.ofColor .red) == 0
#guard (ManaPool.empty.add (.colored .green) 1).coveredMana (ManaCost.ofGenericAndColor 1 .red) == 1
#guard (ManaPool.empty.add (.colored .red) 1).coveredMana (ManaCost.ofColor .red) == 1
#guard
  let p := ManaPool.empty.add (.colored .green) 1 (restriction := some .elf)
  let elfSpell := ManaSpend.forSpell (subtypes := #[.elf])
  p.coveredMana (ManaCost.ofColor .green) == 0 &&
    p.coveredMana (ManaCost.ofColor .green) elfSpell == 1 &&
    p.usable (.colored .green) == 0 &&
    p.usable (.colored .green) elfSpell == 1
#guard (ManaCost.ofGenericAndColor 1 .green).coloredCount .green == 1
#guard (ManaCost.ofGenericAndColor 1 .green).coloredCount .red == 0
#guard (ManaCost.ofHybrid .black .red).coloredCount .black == 0
#guard (ManaCost.ofHybrid .black .red).symbolsIncludingColor .black == 1
#guard (ManaCost.ofHybrid .black .red).symbolsIncludingColor .red == 1
#guard (ManaCost.ofHybrid .black .red).symbolsIncludingColor .green == 0
#guard toString (ManaPool.empty.add (.colored .green) 2 (restriction := some .elf)) ==
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
  let p := ManaPool.empty.add (.colored .white) 1 (restriction := some .hero)
  let heroSpell := ManaSpend.forSpell (subtypes := #[.hero])
  p.heroWhite == 1 && (p.pay? (ManaCost.ofColor .white)).isNone &&
    (p.pay? (ManaCost.ofColor .white) heroSpell).isSome
#guard
  let p := ManaPool.empty.add .colorless 1 (restriction := some .cantNonartifact)
  let nonArtSpell := ManaSpend.forSpell (types := #[.creature])
  let artSpell := ManaSpend.forSpell (types := #[.artifact])
  (p.pay? (ManaCost.ofGeneric 1) nonArtSpell).isNone &&
    (p.pay? (ManaCost.ofGeneric 1) artSpell).isSome &&
    (p.pay? (ManaCost.ofGeneric 1)).isSome
#guard
  let p := ManaPool.empty.add (.colored .blue) 1 (restriction := some .cantNonartifact)
  let nonArtSpell := ManaSpend.forSpell (types := #[.instant])
  let artSpell := ManaSpend.forSpell (types := #[.artifact])
  (p.pay? (ManaCost.ofColor .blue) nonArtSpell).isNone &&
    (p.pay? (ManaCost.ofColor .blue) artSpell).isSome
#guard
  let p := ManaPool.empty.add (.colored .green) 2 (restriction := some .creatureSource)
  let creatureAb := ManaSpend.forAbility (sourceTypes := #[.creature])
  p.creatureGreen == 2 && (p.pay? (ManaCost.ofGeneric 2)).isNone &&
    (p.pay? (ManaCost.ofGeneric 2) creatureAb).isSome
#guard
  let cost : ManaCost := { symbols := #[.hybrid .black .green, .colored .black] }
  let p := ManaPool.empty.add (.colored .black) 1 |>.add (.colored .green) 1
  (p.payUnits? cost).isSome && p.coveredMana cost == 2
#guard
  let cost : ManaCost := { symbols := #[.hybrid .white .blue, .hybrid .white .black] }
  let p := ManaPool.empty.add (.colored .white) 1 |>.add (.colored .blue) 1
  (p.payUnits? cost).isSome && p.coveredMana cost == 2
#guard
  let cost : ManaCost := { symbols := #[.twobrid .white, .colored .white] }
  let p := ManaPool.empty.add (.colored .white) 1 |>.add .colorless 2
  (p.payUnits? cost).isSome && p.coveredMana cost == 3
#guard
  let cost : ManaCost := { symbols := #[.twobrid .white, .hybrid .white .blue] }
  let p := ManaPool.empty.add (.colored .white) 1 |>.add .colorless 2
  (p.payUnits? cost).isSome && p.coveredMana cost == 3

end ManaPool

end Mtg.Engine
