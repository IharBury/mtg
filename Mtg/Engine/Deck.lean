import Mtg.Engine.Card.CardDef

/-!
# Deck construction (CR 100.2)

Constructed decks have a minimum size of 60. A constructed deck may contain
any number of basic land cards and no more than four of any other English
name.
-/

namespace Mtg.Engine

/-- How a deck is validated before a game begins. -/
abbrev Format := EntersTappedRule

namespace Format

@[match_pattern] abbrev formatKind (isConstructed : Bool := false) : Format :=
  .entersTappedKind Option.none Option.none isConstructed false false false
/-- CR 100.2a: minimum 60, four-of except basic lands. -/
@[match_pattern] abbrev constructed : Format := .formatKind true
/-- CR 100.2b: minimum 40, duplicates unrestricted. -/
@[match_pattern] abbrev limited : Format := .formatKind false

def minDeckSize : Format → Nat
  | .constructed => 60
  | _ => 40

def englishName : Format → String
  | .constructed => "constructed"
  | _ => "limited"

instance : ToString Format where
  toString := englishName

end Format

namespace EntersTappedRule
export Format (formatKind constructed limited)
end EntersTappedRule

namespace CardStaticRule
export Format (formatKind constructed limited)
end CardStaticRule

abbrev DeckError := CardKeywordRule

namespace DeckError

@[match_pattern] abbrev tooSmall (got required : Nat) : DeckError :=
  .cardKeywordRuleKind (some got) Option.none Option.none Option.none (some required) false false false false false false
@[match_pattern] abbrev tooManyCopies (cardName : String) (got : Nat) : DeckError :=
  .cardKeywordRuleKind (some got) (some cardName) Option.none Option.none Option.none true false false false false false

def message : DeckError → String
  | .tooSmall got required =>
    s!"Deck has {got} cards; minimum is {required}"
  | .tooManyCopies cardName got =>
    s!"Deck has {got} copies of {cardName}; constructed maximum is 4"
  | _ => ""

instance : ToString DeckError where
  toString := message

end DeckError

namespace CardKeywordRule
export DeckError (tooSmall tooManyCopies)
end CardKeywordRule

namespace CardStaticRule
export DeckError (tooSmall tooManyCopies)
end CardStaticRule

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

/-- Validate a deck against format construction rules (CR 100.2). Basic
lands and cards saying a deck can have any number of them are not limited to
four (ruling 769). -/
def validateDeck (fmt : Format) (cards : Array CardDef) : Except DeckError Unit := do
  let need := fmt.minDeckSize
  if cards.size < need then
    throw (.tooSmall cards.size need)
  if fmt == .constructed then
    for (name, n) in countNames cards do
      let sample := cards.find? (fun c => c.name == name)
      let unlimited :=
        match sample with
        | some c => isBasicLandCard c || c.anyNumberInDeck
        | none => false
      if !unlimited && n > 4 then
        throw (.tooManyCopies name n)
  return ()

def isLegalDeck (fmt : Format) (cards : Array CardDef) : Bool :=
  match validateDeck fmt cards with
  | .ok _ => true
  | .error _ => false

#guard Format.constructed.minDeckSize == 60
#guard Format.limited.minDeckSize == 40

end Mtg.Engine
