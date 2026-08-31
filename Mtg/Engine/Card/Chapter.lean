import Mtg.Engine.Card.SpellResolution

/-!
# Saga chapter resolutions (CR 714.3)

How a printed Saga chapter resolves, including spell-shaped MSH chapters.
-/

namespace Mtg.Engine

/-- Spell-shaped MSH Saga chapter stored as unified Effect fields, so the
chapter bucket does not mention leftover spell constructors. -/
structure ChapterSpell where
  targeting : EffectTargeting := .of .none
  allowsZeroTargets : Bool := false
  phrase : String := ""
  resolution : SpellResolution := .extraLand
deriving Repr, Inhabited, BEq

/-- How a printed Saga chapter resolves (CR 714.3). Each supported catalog
Saga uses these constructors; `effect` on `SagaChapter` remains the Oracle
wording. -/
inductive ChapterResolution where
  /-- This Saga deals `n` damage to target creature an opponent controls. -/
  | dealDamageToOppCreature (n : Nat)
  /-- Destroy target artifact an opponent controls. -/
  | destroyOppArtifact
  /-- Add this mana (e.g. `{R}`). -/
  | addMana (mana : ManaType)
  /-- Search for a basic land, put it into your hand, then shuffle. -/
  | searchBasicLandToHand
  /-- This Saga gains landfall: create a 1/1 green Elf. -/
  | gainLandfallCreateElf
  /-- Elves you control get +P/+0 and vigilance until end of turn. -/
  | elvesGetVigilance (power : Int)
  /-- Target opponent reveals their hand; you choose a nonland; they discard it. -/
  | opponentDiscardsNonland
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Target opponent loses `n` life and you gain `n` life. -/
  | opponentLosesYouGain (n : Nat)
  /-- Target creature you control gains hexproof while this Saga remains. -/
  | grantHexproofWhileRemains
  /-- Prevent damage that would be dealt by up to one target creature while
  this Saga remains. -/
  | preventDamageWhileRemains
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Search for up to `max` basic Plains, exile them, shuffle, gain `life`. -/
  | searchBasicPlainsExileGainLife (max life : Nat)
  /-- Put a card exiled with this Saga into its owner's hand. -/
  | returnLinkedExileToHand
  /-- Whenever you attack this turn, a target creature you control gets
  +1/+1 per Plains you control. -/
  | grantAttackPumpPerPlainsThisTurn
  /-- Exile up to one target creature or land you control; return it at the
  beginning of the next end step. -/
  | blinkUntilEndStep
  /-- Create a Treasure. Then if you control four or more, sacrifice this
  Saga. If you do, create a 6/6 red Dragon with flying. -/
  | treasureThenDragonIfFour
  /-- Recruit. -/
  | recruit
  /-- Return target creature card with mana value `n` or less from your
  graveyard to the battlefield. -/
  | returnCreatureFromGyMvAtMost (n : Nat)
  /-- Put a +1/+1 counter on up to one target creature. -/
  | plusOneUpToOne
  /-- Gain control of up to two creatures with total mana value `n` or less
  for as long as this Saga remains. -/
  | gainControlOfUpToTwoCreaturesTotalMvAtMost (n : Nat)
  /-- This Saga deals `n` damage to each creature that is not this subtype
  and to each opponent. -/
  | dealDamageToEachNonSubtypeAndOpponents (n : Nat) (subtype : String)
  /-- This Saga deals X damage to target opponent, where X is the greatest
  mana value among artifacts you control. -/
  | dealXDamageToTargetOpponentGreatestArtifactMv
  /-- A spell-shaped MSH Saga chapter. -/
  | spell (s : ChapterSpell)
deriving Repr, Inhabited, BEq

end Mtg.Engine
