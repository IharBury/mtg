import Mtg.Engine.Card.Text

/-!
# Token kinds (CR 111)

Tokens the engine can create and their printed Oracle nouns.
-/

namespace Mtg.Engine

/-- Non-creature artifact tokens (CR 111.10). -/
inductive ArtifactToken where
  /-- Parameterized non-creature artifact token: predefined/set artifact (`!equipment`: Treasure, Food, Clue, Map, Vibranium, Heartwood, Lotus, Incubator) or colorless Equipment (`equipment`: Axe when `!alt1`, Sturdy Shield when `alt1`). -/
  | artifactTokenKind (alt1 : Bool := false) (alt2 : Bool := false)
      (setArtifact : Bool := false) (equipment : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace ArtifactToken

@[match_pattern] abbrev predefinedOrSet (alt1 : Bool := false) (alt2 : Bool := false)
    (setArtifact : Bool := false) : ArtifactToken :=
  .artifactTokenKind alt1 alt2 setArtifact false
@[match_pattern] abbrev equipment (sturdyShield : Bool := false) : ArtifactToken :=
  .artifactTokenKind sturdyShield false false true

end ArtifactToken

/-- Artifact creature tokens (CR 111). -/
inductive ArtifactCreatureToken where
  /-- 2/2 Robot Villain (`!alt1 && !alt2 && !construct`), 3/3 Doombot (`alt1 && !alt2 && !construct`), 3/1 Stone Boulder Wall (`!alt1 && alt2 && !construct`), 1/1 Sculpture Treasure (`alt1 && alt2 && !construct`), 1/1 flying Thopter (`!alt1 && !alt2 && construct`), 1/1 Myr (`alt1 && !alt2 && construct`), 1/1 Phyrexian Mite (`!alt1 && alt2 && construct`), or 1/1 Gingerbrute (`alt1 && alt2 && construct`). -/
  | kind (alt1 : Bool := false) (alt2 : Bool := false) (construct : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Legendary creature tokens (CR 111 / CR 205.4a). -/
inductive LegendaryToken where
  /-- Parameterized legendary creature token: 3/3 Mowu or 2/2 Zabu (`!msh`) or MSH legendary token (`msh`: The Void, Redwing, Galactus, or The Tiger God). -/
  | legendaryTokenKind (alt1 : Bool := false) (alt2 : Bool := false) (msh : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace LegendaryToken

@[match_pattern] abbrev mowuOrZabu (zabu : Bool := false) : LegendaryToken :=
  .legendaryTokenKind zabu false false
@[match_pattern] abbrev mshLegend (redwing : Bool := false) (galactusOrTigerGod : Bool := false) : LegendaryToken :=
  .legendaryTokenKind redwing galactusOrTigerGod true

end LegendaryToken

/-- Non-artifact, non-legendary creature tokens (CR 111). -/
inductive CreatureToken where
  /-- Parameterized non-artifact, non-legendary creature token (CR 111). -/
  | creatureTokenKind (alt1 : Bool := false) (alt2 : Bool := false)
      (alt3 : Bool := false) (g1 : Bool := false) (g2 : Bool := false) (g3 : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CreatureToken

@[match_pattern] abbrev whiteOrGreen (alt1 : Bool := false) (alt2 : Bool := false)
    (green : Bool := false) : CreatureToken :=
  .creatureTokenKind alt1 alt2 green false false false
@[match_pattern] abbrev whiteFlyingOrBlue (alt1 : Bool := false) (alt2 : Bool := false)
    (blue : Bool := false) : CreatureToken :=
  .creatureTokenKind alt1 alt2 blue true false false
@[match_pattern] abbrev dragonOrLeviathan (alt : Bool := false)
    (leviathan : Bool := false) : CreatureToken :=
  .creatureTokenKind alt leviathan false false true false
@[match_pattern] abbrev redOrAlignment (alt1 : Bool := false) (alt2 : Bool := false)
    (alignment : Bool := false) : CreatureToken :=
  .creatureTokenKind alt1 alt2 alignment true true false
@[match_pattern] abbrev otherCreature (moloid : Bool := false)
    (cadetOrCitizen : Bool := false) : CreatureToken :=
  .creatureTokenKind moloid cadetOrCitizen false false false true
@[match_pattern] abbrev fraCreature (forestTentacle : Bool := false) : CreatureToken :=
  .creatureTokenKind forestTentacle false false true false true
@[match_pattern] abbrev rogue : CreatureToken :=
  .creatureTokenKind false false false false true true

end CreatureToken

/-- A token the engine can create (CR 111). Oracle nouns are fixed so catalog
cards reconstruct printed “create a …” lines. -/
inductive TokenKind where
  /-- Unified token kind (CR 111): non-creature artifact (`artifactOpt = some a`), creature (`creatureOpt = some c`), artifact creature (`artCreatureOpt = some a`), legendary (`legendaryOpt = some l`), or Jace planeswalker (all `none`). -/
  | tokenKind (artifactOpt : Option ArtifactToken := none)
      (creatureOpt : Option CreatureToken := none)
      (artCreatureOpt : Option ArtifactCreatureToken := none)
      (legendaryOpt : Option LegendaryToken := none)
deriving Repr, Inhabited, BEq, DecidableEq

namespace TokenKind

@[match_pattern] abbrev artifact (a : ArtifactToken) : TokenKind :=
  .tokenKind (some a) none none none
@[match_pattern] abbrev creature (c : CreatureToken) : TokenKind :=
  .tokenKind none (some c) none none
@[match_pattern] abbrev artifactCreature (a : ArtifactCreatureToken) : TokenKind :=
  .tokenKind none none (some a) none
@[match_pattern] abbrev legendary (l : LegendaryToken) : TokenKind :=
  .tokenKind none none none (some l)
@[match_pattern] abbrev jace : TokenKind :=
  .tokenKind none none none none

-- ArtifactToken aliases
@[match_pattern] abbrev treasure : TokenKind := .artifact (.predefinedOrSet false false false)
@[match_pattern] abbrev food : TokenKind := .artifact (.predefinedOrSet true false false)
@[match_pattern] abbrev clue : TokenKind := .artifact (.predefinedOrSet false true false)
@[match_pattern] abbrev map : TokenKind := .artifact (.predefinedOrSet true true false)
@[match_pattern] abbrev vibranium : TokenKind := .artifact (.predefinedOrSet false false true)
@[match_pattern] abbrev heartwood : TokenKind := .artifact (.predefinedOrSet true false true)
@[match_pattern] abbrev lotus : TokenKind := .artifact (.predefinedOrSet false true true)
@[match_pattern] abbrev incubator : TokenKind := .artifact (.predefinedOrSet true true true)
@[match_pattern] abbrev axe : TokenKind := .artifact (.equipment false)
@[match_pattern] abbrev sturdyShield : TokenKind := .artifact (.equipment true)

-- ArtifactCreatureToken aliases
@[match_pattern] abbrev robotVillain22 : TokenKind := .artifactCreature (.kind false false false)
@[match_pattern] abbrev doombot : TokenKind := .artifactCreature (.kind true false false)
@[match_pattern] abbrev wall : TokenKind := .artifactCreature (.kind false true false)
@[match_pattern] abbrev sculpture : TokenKind := .artifactCreature (.kind true true false)
@[match_pattern] abbrev thopter : TokenKind := .artifactCreature (.kind false false true)
@[match_pattern] abbrev myr : TokenKind := .artifactCreature (.kind true false true)
@[match_pattern] abbrev mite : TokenKind := .artifactCreature (.kind false true true)
@[match_pattern] abbrev gingerbrute : TokenKind := .artifactCreature (.kind true true true)

-- LegendaryToken aliases
@[match_pattern] abbrev mowu : TokenKind := .legendary (.mowuOrZabu false)
@[match_pattern] abbrev zabu : TokenKind := .legendary (.mowuOrZabu true)
@[match_pattern] abbrev theVoid : TokenKind := .legendary (.mshLegend false false)
@[match_pattern] abbrev redwing : TokenKind := .legendary (.mshLegend true false)
@[match_pattern] abbrev galactus : TokenKind := .legendary (.mshLegend false true)
@[match_pattern] abbrev tigerGod : TokenKind := .legendary (.mshLegend true true)

-- CreatureToken aliases
@[match_pattern] abbrev humanSoldier : TokenKind := .creature (.whiteOrGreen false false false)
@[match_pattern] abbrev soldier11white : TokenKind := .creature (.whiteOrGreen true false false)
@[match_pattern] abbrev human : TokenKind := .creature (.whiteOrGreen false true false)
@[match_pattern] abbrev warrior : TokenKind := .creature (.whiteOrGreen true true false)
@[match_pattern] abbrev wolf : TokenKind := .creature (.whiteOrGreen false false true)
@[match_pattern] abbrev bear : TokenKind := .creature (.whiteOrGreen true false true)
@[match_pattern] abbrev elf : TokenKind := .creature (.whiteOrGreen false true true)
@[match_pattern] abbrev squirrel11green : TokenKind := .creature (.whiteOrGreen true true true)
@[match_pattern] abbrev spirit : TokenKind := .creature (.whiteFlyingOrBlue false false false)
@[match_pattern] abbrev birdSoldier : TokenKind := .creature (.whiteFlyingOrBlue true false false)
@[match_pattern] abbrev angel : TokenKind := .creature (.whiteFlyingOrBlue false true false)
@[match_pattern] abbrev insect : TokenKind := .creature (.whiteFlyingOrBlue true true false)
@[match_pattern] abbrev dragon : TokenKind := .creature (.dragonOrLeviathan false false)
@[match_pattern] abbrev dragon55flying : TokenKind := .creature (.dragonOrLeviathan true false)
@[match_pattern] abbrev leviathan65hexproof : TokenKind := .creature (.dragonOrLeviathan false true)
@[match_pattern] abbrev leviathan88hexproof : TokenKind := .creature (.dragonOrLeviathan true true)
@[match_pattern] abbrev angel33blue : TokenKind := .creature (.whiteFlyingOrBlue false false true)
@[match_pattern] abbrev illusion11blue : TokenKind := .creature (.whiteFlyingOrBlue true false true)
@[match_pattern] abbrev merfolk : TokenKind := .creature (.whiteFlyingOrBlue false true true)
@[match_pattern] abbrev shark : TokenKind := .creature (.whiteFlyingOrBlue true true true)
@[match_pattern] abbrev dwarf : TokenKind := .creature (.redOrAlignment false false false)
@[match_pattern] abbrev goblin : TokenKind := .creature (.redOrAlignment true false false)
@[match_pattern] abbrev kobold : TokenKind := .creature (.redOrAlignment false true false)
@[match_pattern] abbrev alien : TokenKind := .creature (.redOrAlignment true true false)
@[match_pattern] abbrev hero32vigilance : TokenKind := .creature (.redOrAlignment false false true)
@[match_pattern] abbrev villain21menace : TokenKind := .creature (.redOrAlignment true false true)
@[match_pattern] abbrev wall04defender : TokenKind := .creature (.redOrAlignment false true true)
@[match_pattern] abbrev beast44trample : TokenKind := .creature (.redOrAlignment true true true)
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
  | _ => "Incubator token"

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
