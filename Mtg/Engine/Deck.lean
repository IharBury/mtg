import Mtg.Engine.Card

/-!
# Deck construction (CR 100.2)

Constructed decks have a minimum size of 60. A constructed deck may contain
any number of basic land cards and no more than four of any other English
name.
-/

namespace Mtg.Engine

/-- How a deck is validated before a game begins. -/
inductive Format where
  /-- CR 100.2a: minimum 60, four-of except basic lands. -/
  | constructed
  /-- CR 100.2b: minimum 40, duplicates unrestricted. -/
  | limited
deriving DecidableEq, Repr, Inhabited

namespace Format

def minDeckSize : Format → Nat
  | .constructed => 60
  | .limited => 40

def englishName : Format → String
  | .constructed => "constructed"
  | .limited => "limited"

instance : ToString Format where
  toString := englishName

end Format

inductive DeckError where
  | tooSmall (got required : Nat)
  | tooManyCopies (cardName : String) (got : Nat)
deriving Repr

namespace DeckError

def message : DeckError → String
  | .tooSmall got required =>
    s!"Deck has {got} cards; minimum is {required}"
  | .tooManyCopies cardName got =>
    s!"Deck has {got} copies of {cardName}; constructed maximum is 4"

instance : ToString DeckError where
  toString := message

end DeckError

/-- Count copies of each English name. -/
def countNames (cards : Array CardDef) : List (String × Nat) :=
  Id.run do
    let mut acc : List (String × Nat) := []
    for c in cards do
      acc :=
        match acc.findIdx? (fun p => p.fst == c.name) with
        | none => acc ++ [(c.name, 1)]
        | some i =>
          acc.set i (c.name, acc[i]!.snd + 1)
    return acc

/-- Validate a deck against format construction rules (CR 100.2). -/
def validateDeck (fmt : Format) (cards : Array CardDef) : Except DeckError Unit := do
  let need := fmt.minDeckSize
  if cards.size < need then
    throw (.tooSmall cards.size need)
  if fmt == .constructed then
    for (name, n) in countNames cards do
      let sample := cards.find? (fun c => c.name == name)
      let basic :=
        match sample with
        | some c => isBasicLandCard c
        | none => false
      if !basic && n > 4 then
        throw (.tooManyCopies name n)
  return ()

def isLegalDeck (fmt : Format) (cards : Array CardDef) : Bool :=
  match validateDeck fmt cards with
  | .ok _ => true
  | .error _ => false

#guard Format.constructed.minDeckSize == 60
#guard Format.limited.minDeckSize == 40

end Mtg.Engine
