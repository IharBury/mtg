import Mtg.Engine.Mana
import Mtg.Engine.Card.Keywords

/-!
# Shared Oracle-text helpers

English phrase builders (counts, joins, mana symbols, search clauses,
signed stats) reused across resolutions, abilities, and card summaries.
-/

namespace Mtg.Engine

/-- English word for a small count in Oracle text (`two`, `three`). Larger
counts print as digits, matching Oracle wording for the amounts we model. -/
def englishNumber (n : Nat) : String :=
  match n with
  | 2 => "two"
  | 3 => "three"
  | 4 => "four"
  | 5 => "five"
  | _ => toString n

#guard englishNumber 2 == "two"
#guard englishNumber 5 == "five"
#guard englishNumber 12 == "12"

/-- Oracle-style alternatives joined with `or`: `a`, `a or b`, `a, b, or c`. -/
def orJoin (xs : List String) : String :=
  match xs with
  | [a, b] => s!"{a} or {b}"
  | [] | [_] => String.intercalate "" xs
  | xs => s!"{String.intercalate ", " xs.dropLast}, or {xs.getLast!}"

#guard orJoin ["Elf"] == "Elf"
#guard orJoin ["Goblin", "Orc"] == "Goblin or Orc"
#guard orJoin ["Bear", "Spider", "Wolf"] == "Bear, Spider, or Wolf"
#guard Keywords.joinedAnd Keyword.trample == "trample"
#guard Keywords.joinedAnd (Keyword.trample.merge Keyword.haste) == "haste and trample"
#guard Keywords.joinedAnd
  ((Keyword.haste.merge Keyword.trample).merge Keyword.flying) ==
  "haste, flying, trample"

/-- English indefinite article for a noun (`an Elf`, `a Hero`). -/
def indefinite (noun : String) : String :=
  match noun.get? 0 with
  | none => "a"
  | some c =>
    match c.toLower with
    | 'a' | 'e' | 'i' | 'o' | 'u' => "an"
    | _ => "a"

#guard indefinite "Elf" == "an"
#guard indefinite "Hero" == "a"
#guard indefinite "Orc" == "an"
#guard indefinite "Bear" == "a"

/-- First character uppercased (ASCII), for ability sentences. -/
def capitalizeAscii (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- English for `n` cards (`a card` vs `2 cards`). -/
def cardPhrase (n : Nat) : String :=
  if n == 1 then "a card" else s!"{n} cards"

/-- English for putting `n` +1/+1 counters on a creature. -/
def plusOnePlusOneCountersPhrase (n : Nat) : String :=
  if n == 1 then "a +1/+1 counter" else s!"{n} +1/+1 counters"

/-- Oracle mana symbols for these types, e.g. `{G}{U}` or `{G} or {U}`. -/
def manaSymbolsText (types : Array ManaType) (sep : String := "") : String :=
  String.intercalate sep (types.toList.map (fun t => s!"\{{t.letter}}"))

#guard manaSymbolsText #[.colored .green, .colored .blue] == "{G}{U}"
#guard manaSymbolsText #[.colored .green, .colored .blue] " or " == "{G} or {U}"

/-- Oracle “search your library for `what`, reveal it, put it into your hand,
then shuffle” clause shared by spell, ability, chapter, and trigger wordings. -/
def searchLibraryToHandPhrase (what : String) : String :=
  s!"search your library for {what}, reveal it, put it into your hand, then shuffle"

/-- Oracle “search `whose` library for a basic land card, put it onto the
battlefield tapped, then shuffle” clause. -/
def searchBasicLandTappedPhrase (whose : String) : String :=
  s!"search {whose} library for a basic land card, put it onto the battlefield tapped, then shuffle"

/-- Oracle sentence for leaving the unpicked cards after a library dig. -/
def restOnBottomRandomPhrase : String :=
  "Put the rest on the bottom of your library in a random order"

/-- Oracle sentence granting play of a card exiled by the current effect. -/
def playThatCardUntilNextTurnPhrase : String :=
  "Until the end of your next turn, you may play that card"

#guard searchLibraryToHandPhrase "a basic land card" ==
  "search your library for a basic land card, reveal it, put it into your hand, then shuffle"
#guard searchBasicLandTappedPhrase "their" ==
  "search their library for a basic land card, put it onto the battlefield tapped, then shuffle"

/-- Signed power/toughness bonus for Oracle-style reminders (`+1` vs `-1`). -/
def signedStat (n : Int) : String :=
  if n < 0 then toString n else s!"+{n}"

end Mtg.Engine
