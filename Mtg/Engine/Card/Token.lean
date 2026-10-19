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
  /-- A 2/2 colorless Wizard Soldier creature token named Cadet (FRA). -/
  | cadet
  /-- A red and green Heartwood artifact token (FRA). -/
  | heartwood
  /-- A colorless Lotus artifact token (FRA). -/
  | lotus
  /-- A blue Jace planeswalker token (FRA). -/
  | jace
  /-- A 1/1 colorless Sculpture Treasure artifact creature token (FRA). -/
  | sculpture
  /-- A legendary 3/3 green Dog creature token named Mowu (FRA). -/
  | mowu
  /-- A 2/2 white Cat Soldier creature token named Ajani's Pridemate (FRA). -/
  | pridemate
  /-- A 4/4 green Beast creature token with trample (FRA). -/
  | beast44trample
  /-- A 5/5 red Dragon creature token with flying (FRA). -/
  | dragon55flying
  /-- A 3/3 green Forest Tentacle land creature token (FRA). -/
  | forestTentacle
  /-- A 1/1 colorless Thopter artifact creature token with flying (FRA). -/
  | thopter
  /-- A 3/3 blue Angel creature token with flying (FRA). -/
  | angel33blue
  /-- A 1/1 blue Illusion creature token (FRA). -/
  | illusion11blue
  /-- An 8/8 blue Leviathan creature token with hexproof (FRA). -/
  | leviathan88hexproof
  /-- A colorless Equipment artifact token named Axe. -/
  | axe
  /-- Zabu, a legendary 2/2 green Cat. -/
  | zabu
  /-- The Void, a legendary 5/5 black Horror Villain. -/
  | theVoid
  /-- Redwing, a legendary 1/1 blue Bird Scout. -/
  | redwing
  /-- A 1/1 red Alien creature token with haste. -/
  | alien
  /-- A colorless Equipment artifact token named Sturdy Shield. -/
  | sturdyShield
  /-- Galactus, a legendary 16/16 black Elder Alien with flying and trample. -/
  | galactus
  /-- A 1/1 blue Merfolk creature token. -/
  | merfolk
  /-- The Tiger God, a legendary 4/4 green Cat God creature token. -/
  | tigerGod
  /-- A 1/1 green and white Citizen creature token. -/
  | citizen
  /-- A 1/1 white Warrior creature token. -/
  | warrior
  /-- A 2/1 white Insect creature token with flying. -/
  | insect
  /-- A 1/1 colorless Myr artifact creature token. -/
  | myr
  /-- A 0/1 red Kobold creature token named Kobolds of Kher Keep. -/
  | kobold
  /-- A 1/1 colorless Phyrexian Mite artifact creature token with toxic 1 that can't block. -/
  | mite
  /-- An X/X blue Shark creature token with flying. -/
  | shark
  /-- A 1/1 colorless Food Golem artifact creature token named Gingerbrute with haste. -/
  | gingerbrute
  /-- A 4/4 white Angel creature token with flying. -/
  | angel
  /-- A 1/1 white Human creature token. -/
  | human
  /-- A 1/1 red Goblin creature token. -/
  | goblin
  /-- A colorless Map artifact token. -/
  | map
  /-- A 2/2 black Rogue creature token. -/
  | rogue
  /-- A colorless Incubator artifact token. -/
  | incubator
deriving Repr, Inhabited, BEq, DecidableEq

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
  | .cadet => "2/2 colorless Wizard Soldier creature token named Cadet"
  | .heartwood => "Heartwood token"
  | .lotus => "Lotus token"
  | .jace => "blue Jace planeswalker token"
  | .sculpture =>
    "1/1 colorless Sculpture Treasure artifact creature token with \"{T}, Sacrifice this token: Add one mana of any color.\""
  | .mowu => "legendary 3/3 green Dog creature token named Mowu"
  | .pridemate =>
    "2/2 white Cat Soldier creature token named Ajani's Pridemate with \"Whenever you gain life, put a +1/+1 counter on this token.\""
  | .beast44trample => "4/4 green Beast creature token with trample"
  | .dragon55flying => "5/5 red Dragon creature token with flying"
  | .forestTentacle => "3/3 green Forest Tentacle land creature token"
  | .thopter => "1/1 colorless Thopter artifact creature token with flying"
  | .angel33blue => "3/3 blue Angel creature token with flying"
  | .illusion11blue => "1/1 blue Illusion creature token"
  | .leviathan88hexproof => "8/8 blue Leviathan creature token with hexproof"
  | .axe => "colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}"
  | .zabu =>
    "Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\""
  | .theVoid =>
    "The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\""
  | .redwing =>
    "Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\""
  | .alien => "1/1 red Alien creature token with haste"
  | .sturdyShield => "colorless Equipment artifact token named Sturdy Shield"
  | .galactus => "Galactus, a legendary 16/16 black Elder Alien creature token with flying and trample"
  | .merfolk => "1/1 blue Merfolk creature token"
  | .tigerGod =>
    "The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .citizen => "1/1 green and white Citizen creature token"
  | .warrior => "1/1 white Warrior creature token"
  | .insect => "2/1 white Insect creature token with flying"
  | .myr => "1/1 colorless Myr artifact creature token"
  | .kobold => "0/1 red Kobold creature token named Kobolds of Kher Keep"
  | .mite =>
    "1/1 colorless Phyrexian Mite artifact creature token with toxic 1 and \"This token can't block.\""
  | .shark => "X/X blue Shark creature token with flying"
  | .gingerbrute => "1/1 colorless Food Golem artifact creature token named Gingerbrute with haste"
  | .angel => "4/4 white Angel creature token with flying"
  | .human => "1/1 white Human creature token"
  | .goblin => "1/1 red Goblin creature token"
  | .map => "Map token"
  | .rogue => "2/2 black Rogue creature token"
  | .incubator => "Incubator token"

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
