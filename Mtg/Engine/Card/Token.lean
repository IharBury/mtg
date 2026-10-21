import Mtg.Engine.Card.Text

/-!
# Token kinds (CR 111)

Tokens the engine can create and their printed Oracle nouns.
-/

namespace Mtg.Engine

/-- Non-creature artifact tokens (CR 111.10). -/
inductive ArtifactToken where
  /-- Standard predefined artifact token: Treasure (`!food && !clueOrMap`), Food (`food && !clueOrMap`), Clue (`!food && clueOrMap`), or Map (`food && clueOrMap`). -/
  | predefined (food : Bool := false) (clueOrMap : Bool := false)
  /-- Set-specific artifact token: Vibranium (`!heartwood && !lotusOrIncubator`), Heartwood (`heartwood && !lotusOrIncubator`), Lotus (`!heartwood && lotusOrIncubator`), or Incubator (`heartwood && lotusOrIncubator`). -/
  | setArtifact (heartwood : Bool := false) (lotusOrIncubator : Bool := false)
  /-- Colorless Equipment artifact token: Axe (`!sturdyShield`) or Sturdy Shield (`sturdyShield`). -/
  | equipment (sturdyShield : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Artifact creature tokens (CR 111). -/
inductive ArtifactCreatureToken where
  /-- 2/2 Robot Villain (`!doombot && !wallOrSculpture`), 3/3 Doombot (`doombot && !wallOrSculpture`), 3/1 Stone Boulder Wall (`!doombot && wallOrSculpture`), or 1/1 Sculpture Treasure (`doombot && wallOrSculpture`). -/
  | robotOrWall (doombot : Bool := false) (wallOrSculpture : Bool := false)
  /-- 1/1 flying Thopter (`!myr && !miteOrGingerbrute`), 1/1 Myr (`myr && !miteOrGingerbrute`), 1/1 Phyrexian Mite (`!myr && miteOrGingerbrute`), or 1/1 Gingerbrute (`myr && miteOrGingerbrute`). -/
  | constructToken (myr : Bool := false) (miteOrGingerbrute : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Legendary creature tokens (CR 111 / CR 205.4a). -/
inductive LegendaryToken where
  /-- 3/3 green Dog named Mowu (`!zabu`) or 2/2 green Cat named Zabu (`zabu`). -/
  | mowuOrZabu (zabu : Bool := false)
  /-- 5/5 black Horror Villain named The Void (`!redwing && !galactusOrTigerGod`), 1/1 blue Bird Scout named Redwing (`redwing && !galactusOrTigerGod`), 16/16 black Elder Alien named Galactus (`!redwing && galactusOrTigerGod`), or 4/4 green Cat God named The Tiger God (`redwing && galactusOrTigerGod`). -/
  | mshLegend (redwing : Bool := false) (galactusOrTigerGod : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Non-artifact, non-legendary creature tokens (CR 111). -/
inductive CreatureToken where
  /-- 1/1 white creature token: Human Soldier (`!soldierOnly && !humanOnly`), Soldier (`soldierOnly && !humanOnly`), Human (`!soldierOnly && humanOnly`), or Warrior (`soldierOnly && humanOnly`). -/
  | white11 (soldierOnly : Bool := false) (humanOnly : Bool := false)
  /-- Green creature token: 2/2 Wolf (`!bear && !elfOrSquirrel`), 2/2 Bear (`bear && !elfOrSquirrel`), 1/1 Elf (`!bear && elfOrSquirrel`), or 1/1 Squirrel (`bear && elfOrSquirrel`). -/
  | greenCreature (bear : Bool := false) (elfOrSquirrel : Bool := false)
  /-- White flying creature token: 1/1 Spirit (`!birdSoldier && !angelOrInsect`), 4/4 Bird Soldier (`birdSoldier && !angelOrInsect`), 4/4 Angel (`!birdSoldier && angelOrInsect`), or 2/1 Insect (`birdSoldier && angelOrInsect`). -/
  | flyingWhite (birdSoldier : Bool := false) (angelOrInsect : Bool := false)
  /-- Red flying Dragon creature token: 6/6 (`!fiveFive`) or 5/5 (`fiveFive`). -/
  | dragonKind (fiveFive : Bool := false)
  /-- Blue hexproof Leviathan creature token: 6/5 (`!eightEight`) or 8/8 (`eightEight`). -/
  | leviathanKind (eightEight : Bool := false)
  /-- Blue creature token: 3/3 flying Angel (`!illusion && !merfolkOrShark`), 1/1 Illusion (`illusion && !merfolkOrShark`), 1/1 Merfolk (`!illusion && merfolkOrShark`), or X/X flying Shark (`illusion && merfolkOrShark`). -/
  | blueCreature (illusion : Bool := false) (merfolkOrShark : Bool := false)
  /-- Red creature token: 2/2 Dwarf (`!goblin && !koboldOrAlien`), 1/1 Goblin (`goblin && !koboldOrAlien`), 0/1 Kobold (`!goblin && koboldOrAlien`), or 1/1 haste Alien (`goblin && koboldOrAlien`). -/
  | redCreature (goblin : Bool := false) (koboldOrAlien : Bool := false)
  /-- Keyword creature token: 3/2 vigilance Hero (`!villain && !wall04OrBeast`), 2/1 menace Villain (`villain && !wall04OrBeast`), 0/4 defender Wall (`!villain && wall04OrBeast`), or 4/4 trample Beast (`villain && wall04OrBeast`). -/
  | heroOrVillain (villain : Bool := false) (wall04OrBeast : Bool := false)
  /-- 1/1 green Insect (`!moloid && !cadetOrCitizen`), 1/1 green Minion named Moloid (`moloid && !cadetOrCitizen`), 2/2 colorless Wizard Soldier named Cadet (`!moloid && cadetOrCitizen`), or 1/1 green and white Citizen (`moloid && cadetOrCitizen`). -/
  | otherCreature (moloid : Bool := false) (cadetOrCitizen : Bool := false)
  /-- 2/2 white Cat Soldier named Ajani's Pridemate (`!forestTentacle`) or 3/3 green Forest Tentacle land creature (`forestTentacle`). -/
  | fraCreature (forestTentacle : Bool := false)
  /-- A 2/2 black Rogue creature token. -/
  | rogue
deriving Repr, Inhabited, BEq, DecidableEq

/-- A token the engine can create (CR 111). Oracle nouns are fixed so catalog
cards reconstruct printed “create a …” lines. -/
inductive TokenKind where
  /-- Non-creature artifact token (CR 111.10). -/
  | artifact (a : ArtifactToken)
  /-- Non-artifact, non-legendary creature token (CR 111). -/
  | creature (c : CreatureToken)
  /-- Artifact creature token (CR 111). -/
  | artifactCreature (a : ArtifactCreatureToken)
  /-- Legendary creature token (CR 111 / CR 205.4a). -/
  | legendary (l : LegendaryToken)
  /-- A blue Jace planeswalker token (FRA). -/
  | jace
deriving Repr, Inhabited, BEq, DecidableEq

namespace TokenKind

-- ArtifactToken aliases
@[match_pattern] abbrev treasure : TokenKind := .artifact (.predefined false false)
@[match_pattern] abbrev food : TokenKind := .artifact (.predefined true false)
@[match_pattern] abbrev clue : TokenKind := .artifact (.predefined false true)
@[match_pattern] abbrev map : TokenKind := .artifact (.predefined true true)
@[match_pattern] abbrev vibranium : TokenKind := .artifact (.setArtifact false false)
@[match_pattern] abbrev heartwood : TokenKind := .artifact (.setArtifact true false)
@[match_pattern] abbrev lotus : TokenKind := .artifact (.setArtifact false true)
@[match_pattern] abbrev incubator : TokenKind := .artifact (.setArtifact true true)
@[match_pattern] abbrev axe : TokenKind := .artifact (.equipment false)
@[match_pattern] abbrev sturdyShield : TokenKind := .artifact (.equipment true)

-- ArtifactCreatureToken aliases
@[match_pattern] abbrev robotVillain22 : TokenKind := .artifactCreature (.robotOrWall false false)
@[match_pattern] abbrev doombot : TokenKind := .artifactCreature (.robotOrWall true false)
@[match_pattern] abbrev wall : TokenKind := .artifactCreature (.robotOrWall false true)
@[match_pattern] abbrev sculpture : TokenKind := .artifactCreature (.robotOrWall true true)
@[match_pattern] abbrev thopter : TokenKind := .artifactCreature (.constructToken false false)
@[match_pattern] abbrev myr : TokenKind := .artifactCreature (.constructToken true false)
@[match_pattern] abbrev mite : TokenKind := .artifactCreature (.constructToken false true)
@[match_pattern] abbrev gingerbrute : TokenKind := .artifactCreature (.constructToken true true)

-- LegendaryToken aliases
@[match_pattern] abbrev mowu : TokenKind := .legendary (.mowuOrZabu false)
@[match_pattern] abbrev zabu : TokenKind := .legendary (.mowuOrZabu true)
@[match_pattern] abbrev theVoid : TokenKind := .legendary (.mshLegend false false)
@[match_pattern] abbrev redwing : TokenKind := .legendary (.mshLegend true false)
@[match_pattern] abbrev galactus : TokenKind := .legendary (.mshLegend false true)
@[match_pattern] abbrev tigerGod : TokenKind := .legendary (.mshLegend true true)

-- CreatureToken aliases
@[match_pattern] abbrev humanSoldier : TokenKind := .creature (.white11 false false)
@[match_pattern] abbrev soldier11white : TokenKind := .creature (.white11 true false)
@[match_pattern] abbrev human : TokenKind := .creature (.white11 false true)
@[match_pattern] abbrev warrior : TokenKind := .creature (.white11 true true)
@[match_pattern] abbrev wolf : TokenKind := .creature (.greenCreature false false)
@[match_pattern] abbrev bear : TokenKind := .creature (.greenCreature true false)
@[match_pattern] abbrev elf : TokenKind := .creature (.greenCreature false true)
@[match_pattern] abbrev squirrel11green : TokenKind := .creature (.greenCreature true true)
@[match_pattern] abbrev spirit : TokenKind := .creature (.flyingWhite false false)
@[match_pattern] abbrev birdSoldier : TokenKind := .creature (.flyingWhite true false)
@[match_pattern] abbrev angel : TokenKind := .creature (.flyingWhite false true)
@[match_pattern] abbrev insect : TokenKind := .creature (.flyingWhite true true)
@[match_pattern] abbrev dragon : TokenKind := .creature (.dragonKind false)
@[match_pattern] abbrev dragon55flying : TokenKind := .creature (.dragonKind true)
@[match_pattern] abbrev leviathan65hexproof : TokenKind := .creature (.leviathanKind false)
@[match_pattern] abbrev leviathan88hexproof : TokenKind := .creature (.leviathanKind true)
@[match_pattern] abbrev angel33blue : TokenKind := .creature (.blueCreature false false)
@[match_pattern] abbrev illusion11blue : TokenKind := .creature (.blueCreature true false)
@[match_pattern] abbrev merfolk : TokenKind := .creature (.blueCreature false true)
@[match_pattern] abbrev shark : TokenKind := .creature (.blueCreature true true)
@[match_pattern] abbrev dwarf : TokenKind := .creature (.redCreature false false)
@[match_pattern] abbrev goblin : TokenKind := .creature (.redCreature true false)
@[match_pattern] abbrev kobold : TokenKind := .creature (.redCreature false true)
@[match_pattern] abbrev alien : TokenKind := .creature (.redCreature true true)
@[match_pattern] abbrev hero32vigilance : TokenKind := .creature (.heroOrVillain false false)
@[match_pattern] abbrev villain21menace : TokenKind := .creature (.heroOrVillain true false)
@[match_pattern] abbrev wall04defender : TokenKind := .creature (.heroOrVillain false true)
@[match_pattern] abbrev beast44trample : TokenKind := .creature (.heroOrVillain true true)
@[match_pattern] abbrev insect11green : TokenKind := .creature (.otherCreature false false)
@[match_pattern] abbrev moloid : TokenKind := .creature (.otherCreature true false)
@[match_pattern] abbrev cadet : TokenKind := .creature (.otherCreature false true)
@[match_pattern] abbrev citizen : TokenKind := .creature (.otherCreature true true)
@[match_pattern] abbrev pridemate : TokenKind := .creature (.fraCreature false)
@[match_pattern] abbrev forestTentacle : TokenKind := .creature (.fraCreature true)
@[match_pattern] abbrev rogue : TokenKind := .creature .rogue

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
