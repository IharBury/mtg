import Mtg.Engine.Color

/-!
# Mana (CR 106, 107.4, 202)

Mana is the primary resource in the game. There are six types of mana: the
five colors and colorless (CR 106.1b). Players spend mana to pay costs.
-/

namespace Mtg.Engine

/-- A type of mana that can exist in a mana pool (CR 106.1b). -/
inductive ManaType where
  | colored (color : Color)
  | colorless
deriving DecidableEq, Repr, Inhabited

namespace ManaType

def letter : ManaType → String
  | .colored c => c.letter
  | .colorless => "C"

instance : ToString ManaType where
  toString
    | .colored c => toString c
    | .colorless => "colorless"

end ManaType

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
  /-- The variable symbol `{X}` (CR 107.3). Treated as 0 off the stack (CR 107.3g). -/
  | x
deriving DecidableEq, Repr, Inhabited

namespace ManaSymbol

def toNotation : ManaSymbol → String
  | .generic n => s!"\{{n}}"
  | .colored c => s!"\{{c.letter}}"
  | .colorless => "{C}"
  | .hybrid a b => s!"\{{a.letter}/{b.letter}}"
  | .x => "{X}"

/-- Color contributed by this symbol to an object’s color (CR 202.2). -/
def colorContribution : ManaSymbol → ColorSet
  | .colored c => ColorSet.singleton c
  | .hybrid a b => ColorSet.singleton a |>.union (ColorSet.singleton b)
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
      | .x => acc)
    0

/-- Whether paying this cost requires spending mana (CR 601.2g). `{X}` is 0 until chosen. -/
def includesManaPayment (cost : ManaCost) : Bool :=
  cost.manaValue > 0

/-- How many mana symbols of color `c` appear in this cost. -/
def coloredCount (cost : ManaCost) (c : Color) : Nat :=
  cost.symbols.foldl
    (fun n s =>
      match s with
      | .colored d => if d == c then n + 1 else n
      | .generic _ | .colorless | .hybrid _ _ | .x => n)
    0

/-- Color of an object from the colored mana symbols in its mana cost (CR 202.2). -/
def colors (cost : ManaCost) : ColorSet :=
  cost.symbols.foldl (fun acc s => acc.union s.colorContribution) ColorSet.empty

/-- If `original` required mana and `result` has no symbols, the payable cost
is `{0}` rather than an empty (unpayable) cost (CR 107.4d / 118.7 / 202.1b). -/
def afterReduction (original result : ManaCost) : ManaCost :=
  if original.includesManaPayment && result.symbols.isEmpty then zero else result

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

/-- Unspent mana a player currently has (CR 106.4). Restricted mana (CR 106.10)
is a subset of the colored totals. -/
structure ManaPool where
  white : Nat := 0
  blue : Nat := 0
  black : Nat := 0
  red : Nat := 0
  green : Nat := 0
  colorless : Nat := 0
  /-- Colored mana that may be spent only to cast Elf spells and activate
  abilities of Elf sources (e.g. Woodland Weavemaster). -/
  elfWhite : Nat := 0
  elfBlue : Nat := 0
  elfBlack : Nat := 0
  elfRed : Nat := 0
  elfGreen : Nat := 0
  /-- Colored mana that may be spent only to cast an instant or sorcery
  (e.g. Pelargir Survivor). -/
  instWhite : Nat := 0
  instBlue : Nat := 0
  instBlack : Nat := 0
  instRed : Nat := 0
  instGreen : Nat := 0
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

/-- Restricted Elf-only amount of this type. Colorless cannot be so restricted. -/
def getElf (p : ManaPool) : ManaType → Nat
  | .colored .white => p.elfWhite
  | .colored .blue => p.elfBlue
  | .colored .black => p.elfBlack
  | .colored .red => p.elfRed
  | .colored .green => p.elfGreen
  | .colorless => 0

def setElf (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colored .white => { p with elfWhite := n }
  | .colored .blue => { p with elfBlue := n }
  | .colored .black => { p with elfBlack := n }
  | .colored .red => { p with elfRed := n }
  | .colored .green => { p with elfGreen := n }
  | .colorless => p

/-- Restricted instant-or-sorcery-only amount of this type. -/
def getInst (p : ManaPool) : ManaType → Nat
  | .colored .white => p.instWhite
  | .colored .blue => p.instBlue
  | .colored .black => p.instBlack
  | .colored .red => p.instRed
  | .colored .green => p.instGreen
  | .colorless => 0

def setInst (p : ManaPool) (t : ManaType) (n : Nat) : ManaPool :=
  match t with
  | .colored .white => { p with instWhite := n }
  | .colored .blue => { p with instBlue := n }
  | .colored .black => { p with instBlack := n }
  | .colored .red => { p with instRed := n }
  | .colored .green => { p with instGreen := n }
  | .colorless => p

/-- Mana of this type with no spending restriction. -/
def unrestricted (p : ManaPool) (t : ManaType) : Nat :=
  p.get t - p.getElf t - p.getInst t

def add (p : ManaPool) (t : ManaType) (n : Nat := 1) (elfRestricted : Bool := false)
    (instRestricted : Bool := false) : ManaPool :=
  let p := p.set t (p.get t + n)
  let p := if elfRestricted then p.setElf t (p.getElf t + n) else p
  if instRestricted then p.setInst t (p.getInst t + n) else p

def total (p : ManaPool) : Nat :=
  p.white + p.blue + p.black + p.red + p.green + p.colorless

/-- Try to spend one mana of the given type (CR 106.10). -/
def spendOne? (p : ManaPool) (t : ManaType) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) : Option ManaPool :=
  if p.get t == 0 then none
  else if allowElfRestricted && p.getElf t > 0 then
    some (p.set t (p.get t - 1) |>.setElf t (p.getElf t - 1))
  else if allowInstRestricted && p.getInst t > 0 then
    some (p.set t (p.get t - 1) |>.setInst t (p.getInst t - 1))
  else if p.unrestricted t > 0 then
    some (p.set t (p.get t - 1))
  else none

/-- Spend one mana of any type. Restricted Elf mana is spent first when allowed,
then instant/sorcery-restricted mana, then colorless, then WUBRG (CR 106.10). -/
def spendAny? (p : ManaPool) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) : Option ManaPool :=
  let colored : List ManaType :=
    [.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
  let order : List ManaType := [.colorless] ++ colored
  Id.run do
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
    for t in order do
      if let some p' := p.spendOne? t allowElfRestricted allowInstRestricted then
        return some p'
    return none

/-- Pay a mana cost, requiring colored/colorless symbols first, then generic (CR 202).
`allowElfRestricted` permits mana that may be spent only on Elf spells and
abilities (CR 106.10). `allowInstRestricted` permits mana that may be spent
only on instant or sorcery spells. -/
def pay? (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) : Option ManaPool :=
  Id.run do
    let mut pool := p
    -- Pay specific symbols first.
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOne? (.colored c) allowElfRestricted allowInstRestricted with
        | some p' => pool := p'
        | none => return none
      | .colorless =>
        match pool.spendOne? .colorless allowElfRestricted allowInstRestricted with
        | some p' => pool := p'
        | none => return none
      | .generic n =>
        for _ in [0:n] do
          match pool.spendAny? allowElfRestricted allowInstRestricted with
          | some p' => pool := p'
          | none => return none
      | .hybrid a b =>
        match pool.spendOne? (.colored a) allowElfRestricted allowInstRestricted with
        | some p' => pool := p'
        | none =>
          match pool.spendOne? (.colored b) allowElfRestricted allowInstRestricted with
          | some p' => pool := p'
          | none => return none
      | .x => pure () -- CR 107.3g: X is 0 off the stack; we treat unpaid X as 0
    return some pool

def canPay (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) : Bool :=
  (p.pay? cost allowElfRestricted allowInstRestricted).isSome

/-- One `{C}×n`, `{C}×n (Elf)`, or `{C}×n (instant/sorcery)` fragment. -/
def poolPart (letter : String) (free elf inst : Nat) : List String :=
  (if free > 0 then [s!"\{{letter}}×{free}"] else []) ++
  (if elf > 0 then [s!"\{{letter}}×{elf} (Elf)"] else []) ++
  (if inst > 0 then [s!"\{{letter}}×{inst} (instant/sorcery)"] else [])

def toNotation (p : ManaPool) : String :=
  if p.isEmpty then "{}"
  else
    let parts :=
      poolPart "W" (p.unrestricted (.colored .white)) p.elfWhite p.instWhite ++
      poolPart "U" (p.unrestricted (.colored .blue)) p.elfBlue p.instBlue ++
      poolPart "B" (p.unrestricted (.colored .black)) p.elfBlack p.instBlack ++
      poolPart "R" (p.unrestricted (.colored .red)) p.elfRed p.instRed ++
      poolPart "G" (p.unrestricted (.colored .green)) p.elfGreen p.instGreen ++
      poolPart "C" p.colorless 0 0
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
#guard (ManaCost.ofGenericAndColor 1 .green).coloredCount .green == 1
#guard (ManaCost.ofGenericAndColor 1 .green).coloredCount .red == 0
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

end ManaPool

end Mtg.Engine
