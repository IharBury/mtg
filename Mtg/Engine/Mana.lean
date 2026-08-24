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

/-- Unspent mana a player currently has (CR 106.4). -/
structure ManaPool where
  white : Nat := 0
  blue : Nat := 0
  black : Nat := 0
  red : Nat := 0
  green : Nat := 0
  colorless : Nat := 0
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

def add (p : ManaPool) (t : ManaType) (n : Nat := 1) : ManaPool :=
  p.set t (p.get t + n)

def total (p : ManaPool) : Nat :=
  p.white + p.blue + p.black + p.red + p.green + p.colorless

/-- Try to spend one mana of the given type. -/
def spendOne? (p : ManaPool) : ManaType → Option ManaPool
  | t =>
    let n := p.get t
    if n == 0 then none else some (p.set t (n - 1))

/-- Spend one mana of any type, preferring colorless then WUBRG order. -/
def spendAny? (p : ManaPool) : Option ManaPool :=
  let order : List ManaType :=
    [.colorless, .colored .white, .colored .blue, .colored .black,
     .colored .red, .colored .green]
  Id.run do
    for t in order do
      if let some p' := p.spendOne? t then
        return some p'
    return none

/-- Pay a mana cost, requiring colored/colorless symbols first, then generic (CR 202). -/
def pay? (p : ManaPool) (cost : ManaCost) : Option ManaPool :=
  Id.run do
    let mut pool := p
    -- Pay specific symbols first.
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOne? (.colored c) with
        | some p' => pool := p'
        | none => return none
      | .colorless =>
        match pool.spendOne? .colorless with
        | some p' => pool := p'
        | none => return none
      | .generic n =>
        for _ in [0:n] do
          match pool.spendAny? with
          | some p' => pool := p'
          | none => return none
      | .x => pure () -- CR 107.3g: X is 0 off the stack; we treat unpaid X as 0
    return some pool

def canPay (p : ManaPool) (cost : ManaCost) : Bool :=
  (p.pay? cost).isSome

def toNotation (p : ManaPool) : String :=
  if p.isEmpty then "{}"
  else
    let parts :=
      (if p.white > 0 then [s!"\{W}×{p.white}"] else []) ++
      (if p.blue > 0 then [s!"\{U}×{p.blue}"] else []) ++
      (if p.black > 0 then [s!"\{B}×{p.black}"] else []) ++
      (if p.red > 0 then [s!"\{R}×{p.red}"] else []) ++
      (if p.green > 0 then [s!"\{G}×{p.green}"] else []) ++
      (if p.colorless > 0 then [s!"\{C}×{p.colorless}"] else [])
    String.intercalate " " parts

instance : ToString ManaPool where
  toString := toNotation

theorem empty_isEmpty : ManaPool.empty.isEmpty = true := rfl

#guard (ManaPool.empty.add (.colored .red) 2 |>.add .colorless 1).total == 3
#guard ((ManaPool.empty.add (.colored .green) 1 |>.add .colorless 1).pay?
         (ManaCost.ofGenericAndColor 1 .green)).isSome
#guard ((ManaPool.empty.add (.colored .green) 1).pay?
         (ManaCost.ofGenericAndColor 1 .green)).isNone

end ManaPool

end Mtg.Engine
