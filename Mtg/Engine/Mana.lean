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
  /-- The variable symbol `{X}` (CR 107.3). Treated as 0 off the stack (CR 107.3g). -/
  | x
deriving DecidableEq, Repr, Inhabited

namespace ManaSymbol

def toNotation : ManaSymbol → String
  | .generic n => s!"\{{n}}"
  | .colored c => s!"\{{c.letter}}"
  | .colorless => "{C}"
  | .x => "{X}"

/-- Color contributed by this symbol to an object’s color (CR 202.2). -/
def colorContribution : ManaSymbol → ColorSet
  | .colored c => ColorSet.singleton c
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

/-- Mana value is the total amount of mana in a mana cost (CR 202.3). `{X}` is 0. -/
def manaValue (cost : ManaCost) : Nat :=
  cost.symbols.foldl
    (fun acc s =>
      match s with
      | .generic n => acc + n
      | .colored _ => acc + 1
      | .colorless => acc + 1
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
      | .generic _ | .colorless | .x => n)
    0

/-- Color of an object from the colored mana symbols in its mana cost (CR 202.2). -/
def colors (cost : ManaCost) : ColorSet :=
  cost.symbols.foldl (fun acc s => acc.union s.colorContribution) ColorSet.empty

def toNotation (cost : ManaCost) : String :=
  if cost.symbols.isEmpty then "{0}"
  else String.join (cost.symbols.toList.map ManaSymbol.toNotation)

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

/-- Mana of this type with no spending restriction. -/
def unrestricted (p : ManaPool) (t : ManaType) : Nat :=
  p.get t - p.getElf t

def add (p : ManaPool) (t : ManaType) (n : Nat := 1) (elfRestricted : Bool := false) :
    ManaPool :=
  let p := p.set t (p.get t + n)
  if elfRestricted then p.setElf t (p.getElf t + n) else p

def total (p : ManaPool) : Nat :=
  p.white + p.blue + p.black + p.red + p.green + p.colorless

/-- Try to spend one mana of the given type (CR 106.10). -/
def spendOne? (p : ManaPool) (t : ManaType) (allowElfRestricted : Bool := false) :
    Option ManaPool :=
  if p.get t == 0 then none
  else if allowElfRestricted then
    if p.getElf t > 0 then
      some (p.set t (p.get t - 1) |>.setElf t (p.getElf t - 1))
    else
      some (p.set t (p.get t - 1))
  else if p.unrestricted t > 0 then
    some (p.set t (p.get t - 1))
  else none

/-- Spend one mana of any type. Restricted Elf mana is spent first when allowed,
then colorless, then WUBRG (CR 106.10). -/
def spendAny? (p : ManaPool) (allowElfRestricted : Bool := false) : Option ManaPool :=
  let colored : List ManaType :=
    [.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
  let order : List ManaType := [.colorless] ++ colored
  Id.run do
    if allowElfRestricted then
      for t in colored do
        if p.getElf t > 0 then
          if let some p' := p.spendOne? t true then
            return some p'
    for t in order do
      if let some p' := p.spendOne? t allowElfRestricted then
        return some p'
    return none

/-- Pay a mana cost, requiring colored/colorless symbols first, then generic (CR 202).
`allowElfRestricted` permits mana that may be spent only on Elf spells and
abilities (CR 106.10). -/
def pay? (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false) :
    Option ManaPool :=
  Id.run do
    let mut pool := p
    -- Pay specific symbols first.
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOne? (.colored c) allowElfRestricted with
        | some p' => pool := p'
        | none => return none
      | .colorless =>
        match pool.spendOne? .colorless allowElfRestricted with
        | some p' => pool := p'
        | none => return none
      | .generic n =>
        for _ in [0:n] do
          match pool.spendAny? allowElfRestricted with
          | some p' => pool := p'
          | none => return none
      | .x => pure () -- CR 107.3g: X is 0 off the stack; we treat unpaid X as 0
    return some pool

def canPay (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false) : Bool :=
  (p.pay? cost allowElfRestricted).isSome

/-- One `{C}×n` or `{C}×n (Elf)` fragment when `n > 0`. -/
def poolPart (letter : String) (free elf : Nat) : List String :=
  (if free > 0 then [s!"\{{letter}}×{free}"] else []) ++
  (if elf > 0 then [s!"\{{letter}}×{elf} (Elf)"] else [])

def toNotation (p : ManaPool) : String :=
  if p.isEmpty then "{}"
  else
    let parts :=
      poolPart "W" (p.unrestricted (.colored .white)) p.elfWhite ++
      poolPart "U" (p.unrestricted (.colored .blue)) p.elfBlue ++
      poolPart "B" (p.unrestricted (.colored .black)) p.elfBlack ++
      poolPart "R" (p.unrestricted (.colored .red)) p.elfRed ++
      poolPart "G" (p.unrestricted (.colored .green)) p.elfGreen ++
      poolPart "C" p.colorless 0
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

end ManaPool

end Mtg.Engine
