/-!
# Reality Fracture Commander effects

Resolutions first printed in Reality Fracture Commander (FRC). Nested under
`FraResolution.frc` so `Resolution` stays under the C runtime constructor
limit. This module does not import `Effect`.
-/

namespace Mtg.Engine

/-- A token created by an FRC effect. Printed characteristics live in the
resolver so `TokenKind` stays closed. -/
inductive FrcToken where
  | citizen
  | warrior
  | insect
  | myr
  | kobold
  | mite
  | shark
  | gingerbrute
  | angel
  | human
  | goblin
  | map
  | treasure
  | rogue
  | incubator
deriving Repr, Inhabited, BEq

/-- One Reality Fracture Commander resolution. -/
inductive FrcEffect where
  /-- Draw `draw` cards, then put `put` cards from your hand on top of your
  library in any order. -/
  | drawPutOnTop (draw put : Nat)
  /-- Exile the targeted permanent. Its mana value was already checked. -/
  | exileTarget
  /-- Exile the targeted creature. Its controller may search for a basic land. -/
  | pathToExile
  /-- Exile the targeted creature. Its controller gains life equal to its power. -/
  | swords
  /-- Destroy the targeted nonland. Its controller creates a 1/1 white Human. -/
  | stroke
  /-- Create X 1/1 green and white Citizens. Creatures you control gain
  indestructible until end of turn. -/
  | grandCrescendo
  /-- Create X 1/1 white Soldiers. If X is 5 or more, destroy all other creatures. -/
  | martialCoup
  /-- Gain X life, create X Mites, and if X is 5 or more destroy all other creatures. -/
  | whiteSuns
  /-- Draw X, discard X, then a Spirit for each card type discarded. -/
  | occult
  /-- Exile all creatures, then incubate that many. -/
  | sunfall
  /-- Exile your creatures, then reveal that many creature cards onto the battlefield. -/
  | massPolymorph
  /-- Exile your creatures. At the next end step, reveal that many creatures. -/
  | syntheticDestiny
  /-- Search for a basic land of one of `kinds`. `untapAt` untaps it when you
  control at least that many lands; `0` leaves it tapped. -/
  | searchBasics (kinds : Array String) (untapAt : Nat)
  /-- Put the targeted creature on the bottom. Its controller reveals until a
  creature and puts that card onto the battlefield. -/
  | proteus
  /-- This land becomes a creature with the given power, toughness, and
  keywords until end of turn. -/
  | animate (power toughness : Nat) (flying firstStrike : Bool)
  /-- Create a Map token. -/
  | mapToken
  /-- Target opponent sacrifices a creature or planeswalker, discards, and
  loses 3. You draw and gain 3. -/
  | archon
  /-- Return the creature that died to the battlefield at the next end step. -/
  | avacyn
  /-- Reveal until X creatures, where X is the number of opponents. They enter
  goaded, then each opponent gains one. -/
  | dack
  /-- The targeted opponent reveals until a historic permanent. You put it
  onto the battlefield and lose life equal to its mana value. -/
  | jhoira
  /-- Draw, then the first time this resolves each turn reveal until a creature. -/
  | nissa
  /-- You may pay life equal to the life just gained. If you do, draw that many. -/
  | nivPay
  /-- Each opponent loses 1 life and you gain 1 life. -/
  | nivDrain
  /-- Destroy tapped creatures opponents control. Gain 1 life for each. -/
  | obEnter
  /-- If you gained life this turn, create a 4/4 white Angel with flying. -/
  | obAngel
  /-- Add {C}{C}. -/
  | omnathCc
  /-- Destroy all creatures with power 4 or greater. -/
  | elspethDestroy
  /-- You get an emblem: creatures you control get +2/+2 and have flying. -/
  | elspethEmblem
  /-- Draw two, then put a card from your hand on the bottom. -/
  | jacePlus
  /-- Exile another planeswalker or creature you control, then reveal until a
  creature or planeswalker. -/
  | jaceMinus
  /-- That opponent's creatures can't attack Jaces you control this combat. -/
  | jaceTax
  /-- You become the monarch. -/
  | monarch
  /-- Create a Gingerbrute token. -/
  | gingerbrute
  /-- Tap the creatures that dealt combat damage to you and put a stun counter
  on each. -/
  | tamiyoStun
  /-- Target opponent gains protection from everything, their life total can't
  change, and their nonland permanents phase out, until their next turn.
  Exile this spell. -/
  | teferi
  /-- Each player mills X, where X is the number of attacking Sphinxes. You
  may cast a card milled this way without paying its mana cost. -/
  | urSphinx
  /-- Copy the targeted instant or sorcery an opponent controls twice. -/
  | venserSpell
  /-- Create two token copies of the targeted permanent. They gain haste and
  are sacrificed at the next end step. -/
  | venserPerm
  /-- Create a 1/1 red Goblin with lifelink and haste until end of turn. -/
  | goblin
  /-- Create a 1/1 white Spirit with flying. -/
  | spirit
  /-- Put a story counter on this artifact. -/
  | story
  /-- You may exile the discarded card from its owner's graveyard. -/
  | currencyExile
  /-- Draw a card, then discard a card. -/
  | currencyLoot
  /-- Put a card exiled with this artifact into its owner's graveyard, then
  create a Treasure or a 2/2 black Rogue. -/
  | currencyReturn
  /-- You may have this artifact become a copy of a creature until end of turn
  with haste. -/
  | cursedCopy
  /-- Each opponent loses life equal to the life they lost this turn. -/
  | despair
  /-- You lose 1 life and amass Zombies 1. -/
  | dreadUpkeep
  /-- The attacking Zombie token gains lifelink until end of turn. -/
  | dreadLink
  /-- Create `n` 1/1 colorless Myr artifact creatures. -/
  | myr (n : Nat)
  /-- Draw a card for each artifact you control. -/
  | drawPerArtifact
  /-- Create an X/X blue Shark with flying, where X is the spell's mana value. -/
  | sharkCast
  /-- Create an X/X blue Shark with flying, where X is the cycling value. -/
  | sharkCycle
  /-- You lose 1 life and create a Phyrexian Mite with toxic 1 that can't block. -/
  | skrelv
  /-- Create two 2/1 white Insects with flying. -/
  | insects
  /-- Reveal the top five cards. An opponent splits them; one pile goes to
  your hand and the other to your graveyard. -/
  | factOrFiction
  /-- This creature gets +`n`/+0 until end of turn. -/
  | pump (n : Int)
  /-- Create a 0/1 red Kobold named Kobolds of Kher Keep. -/
  | kobold
  /-- Create X 1/1 white Warriors. -/
  | warriorsX
  /-- Create X 1/1 green and white Citizens. -/
  | citizensX
  /-- The source explores: a land goes to hand, otherwise a +1/+1 counter. -/
  | explore
  /-- Transform this Incubator into a 0/0 Phyrexian artifact creature. -/
  | transformIncubator
  /-- Turn this face-down creature face up. A special action, not a stack effect. -/
  | turnFaceUp
  /-- This token can't be blocked this turn except by creatures with haste. -/
  | gingerDash
deriving Repr, Inhabited, BEq

end Mtg.Engine
