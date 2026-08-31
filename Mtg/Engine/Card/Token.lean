import Mtg.Engine.Card.Text

/-!
# Token kinds (CR 111)

Tokens the engine can create and their printed Oracle nouns.
-/

namespace Mtg.Engine

/-- A token the engine can create (CR 111). Oracle nouns are fixed so catalog
cards reconstruct printed “create a …” lines. -/
inductive TokenKind where
  | treasure
  | food
  | humanSoldier
  | wolf
  | dwarf
  | bear
  | elf
  | spirit
  | birdSoldier
  | wall
  | dragon
  /-- A Clue artifact token (CR 111 / 701.55). -/
  | clue
  /-- A 3/2 white Hero creature token with vigilance. -/
  | hero32vigilance
  /-- A 2/1 black Villain creature token with menace. -/
  | villain21menace
  /-- A 2/2 colorless Robot Villain artifact creature token. -/
  | robotVillain22
  /-- A 6/5 blue Leviathan creature token with hexproof. -/
  | leviathan65hexproof
  /-- A 1/1 white Soldier creature token. -/
  | soldier11white
  /-- A 1/1 green Squirrel creature token. -/
  | squirrel11green
  /-- A 0/4 colorless Wall creature token with defender. -/
  | wall04defender
  /-- A 3/3 colorless Robot Villain artifact creature token named Doombot. -/
  | doombot
  /-- A 1/1 green Insect creature token. -/
  | insect11green
  /-- A predefined Vibranium artifact token (MSH). -/
  | vibranium
  /-- A 1/1 green Minion creature token named Moloid. -/
  | moloid
deriving Repr, Inhabited, BEq

namespace TokenKind

def oracleNoun : TokenKind → String
  | .treasure => "Treasure token"
  | .food => "Food token"
  | .humanSoldier => "1/1 white Human Soldier creature token"
  | .wolf => "2/2 green Wolf creature token"
  | .dwarf => "2/2 red Dwarf creature token"
  | .bear => "2/2 green Bear creature token"
  | .elf => "1/1 green Elf creature token"
  | .spirit => "1/1 white Spirit creature token with flying"
  | .birdSoldier => "4/4 white Bird Soldier creature token with flying"
  | .wall => "3/1 colorless Wall artifact creature token with defender named Stone Boulder"
  | .dragon => "6/6 red Dragon creature token with flying"
  | .clue => "Clue token"
  | .hero32vigilance => "3/2 white Hero creature token with vigilance"
  | .villain21menace => "2/1 black Villain creature token with menace"
  | .robotVillain22 => "2/2 colorless Robot Villain artifact creature token"
  | .leviathan65hexproof => "6/5 blue Leviathan creature token with hexproof"
  | .soldier11white => "1/1 white Soldier creature token"
  | .squirrel11green => "1/1 green Squirrel creature token"
  | .wall04defender => "0/4 colorless Wall creature token with defender"
  | .doombot => "3/3 colorless Robot Villain artifact creature token named Doombot"
  | .insect11green => "1/1 green Insect creature token"
  | .vibranium => "Vibranium token"
  | .moloid =>
    "1/1 green Minion creature token named Moloid with \"Whenever this token attacks, you may mill a card.\""

/-- Plural Oracle noun: the singular form with `token` → `tokens`. -/
def pluralNoun (k : TokenKind) : String :=
  k.oracleNoun.replace "token" "tokens"

/-- Noun phrase for `n` created tokens (`a Treasure token`, `two 2/2 green
Wolf creature tokens`). `createPhrase` and “that player creates …” wordings
share it. -/
def createdTokensPhrase (k : TokenKind) (n : Nat) (tapped := false) : String :=
  let tappedS := if tapped then "tapped " else ""
  if n == 1 then
    s!"a {tappedS}{k.oracleNoun}"
  else
    s!"{englishNumber n} {tappedS}{k.pluralNoun}"

/-- Oracle “create …” clause for `n` tokens of this kind. -/
def createPhrase (k : TokenKind) (n : Nat) (tapped := false) : String :=
  s!"create {k.createdTokensPhrase n tapped}"

#guard TokenKind.pluralNoun .treasure == "Treasure tokens"
#guard TokenKind.pluralNoun .spirit == "1/1 white Spirit creature tokens with flying"
#guard TokenKind.pluralNoun .doombot ==
  "3/3 colorless Robot Villain artifact creature tokens named Doombot"
#guard TokenKind.createPhrase .wolf 2 == "create two 2/2 green Wolf creature tokens"
#guard TokenKind.createPhrase .elf 3 == "create three 1/1 green Elf creature tokens"

end TokenKind

end Mtg.Engine
