/-!
# Colors (CR 105)

There are five colors in the Magic game: white, blue, black, red, and green.
Colorless is not a color. An object may be any combination of the five colors,
or none.
-/

namespace Mtg.Engine

/-- One of the five colors of Magic (CR 105.1). -/
inductive Color where
  | white
  | blue
  | black
  | red
  | green
deriving DecidableEq, Repr, Hashable, Inhabited

namespace Color

/-- Canonical WUBRG order (CR 105.1). -/
def all : List Color := [.white, .blue, .black, .red, .green]

/-- Single-letter mana-symbol abbreviation. -/
def letter : Color → String
  | .white => "W"
  | .blue => "U"
  | .black => "B"
  | .red => "R"
  | .green => "G"

/-- Full English name used when a player is asked to choose a color (CR 105.4). -/
def englishName : Color → String
  | .white => "white"
  | .blue => "blue"
  | .black => "black"
  | .red => "red"
  | .green => "green"

instance : ToString Color where
  toString c := c.englishName

end Color

/-- A (possibly empty) combination of the five colors (CR 105.2). -/
structure ColorSet where
  white : Bool := false
  blue : Bool := false
  black : Bool := false
  red : Bool := false
  green : Bool := false
deriving BEq, DecidableEq, Repr, Inhabited

namespace ColorSet

def empty : ColorSet := {}

def singleton : Color → ColorSet
  | .white => { white := true }
  | .blue => { blue := true }
  | .black => { black := true }
  | .red => { red := true }
  | .green => { green := true }

def contains (s : ColorSet) : Color → Bool
  | .white => s.white
  | .blue => s.blue
  | .black => s.black
  | .red => s.red
  | .green => s.green

def insert (s : ColorSet) : Color → ColorSet
  | .white => { s with white := true }
  | .blue => { s with blue := true }
  | .black => { s with black := true }
  | .red => { s with red := true }
  | .green => { s with green := true }

/-- Number of distinct colors in the set. -/
def count (s : ColorSet) : Nat :=
  (if s.white then 1 else 0) +
  (if s.blue then 1 else 0) +
  (if s.black then 1 else 0) +
  (if s.red then 1 else 0) +
  (if s.green then 1 else 0)

/-- An object with no color is colorless. Colorless is not a color (CR 105.2c). -/
def isColorless (s : ColorSet) : Bool := s.count == 0

/-- A monocolored object is exactly one of the five colors (CR 105.2a). -/
def isMonocolored (s : ColorSet) : Bool := s.count == 1

/-- A multicolored object is two or more of the five colors (CR 105.2b). -/
def isMulticolored (s : ColorSet) : Bool := s.count ≥ 2

/-- A color pair is exactly two of the five colors (CR 105.5). -/
def isColorPair (s : ColorSet) : Bool := s.count == 2

def toList (s : ColorSet) : List Color :=
  Color.all.filter s.contains

def ofList (cs : List Color) : ColorSet :=
  cs.foldl insert empty

def union (a b : ColorSet) : ColorSet :=
  { white := a.white || b.white
    blue := a.blue || b.blue
    black := a.black || b.black
    red := a.red || b.red
    green := a.green || b.green }

instance : ToString ColorSet where
  toString s :=
    if s.isColorless then "colorless"
    else String.join (s.toList.map Color.letter)

theorem empty_count : ColorSet.empty.count = 0 := rfl

theorem empty_isColorless : ColorSet.empty.isColorless = true := rfl

theorem singleton_monocolored (c : Color) :
    (ColorSet.singleton c).isMonocolored = true := by
  cases c <;> rfl

theorem all_five_colors : Color.all.length = 5 := rfl

/-- There are ten color pairs (CR 105.5). -/
def colorPairs : List ColorSet :=
  let rec pairs : List Color → List ColorSet
    | [] => []
    | c :: rest => rest.map (fun d => ofList [c, d]) ++ pairs rest
  pairs Color.all

#guard colorPairs.length == 10
#guard (ofList [.white, .blue]).isColorPair
#guard !(singleton .red).isColorPair
#guard (ofList [.white, .blue, .black]).isMulticolored

end ColorSet

end Mtg.Engine
