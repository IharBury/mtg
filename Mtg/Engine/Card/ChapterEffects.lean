import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.Trigger

/-!
# Saga-chapter effect constructors (CR 714.3)

Named `Effect.chapter*` constructors for printed Saga chapters.
-/

namespace Mtg.Engine

namespace Effect

/-- This Saga deals `n` damage to target creature an opponent controls. -/
def chapterDealDamageToOppCreature (n : Nat) : Effect :=
  { targeting := .of .oppCreature
    phrase := s!"this Saga deals {n} damage to target creature an opponent controls"
    resolution := .dealDamage (.fixed n) .target }

/-- Destroy target artifact an opponent controls. -/
def chapterDestroyOppArtifact : Effect :=
  { targeting := .of .oppArtifact
    phrase := "destroy target artifact an opponent controls"
    resolution := .destroy .target }

/-- Add this mana (e.g. `{R}`). -/
def chapterAddMana (mana : ManaType) : Effect :=
  { phrase := s!"add {mana}"
    resolution := .addMana #[mana] }

/-- Search for a basic land, put it into your hand, then shuffle. -/
def chapterSearchBasicLandToHand : Effect :=
  { phrase := searchLibraryToHandPhrase "a basic land card"
    resolution := .searchLibrary (.returnToHand .basicLand) }

/-- This Saga gains landfall: create a 1/1 green Elf. -/
def chapterGainLandfallCreateElf : Effect :=
  { phrase := "this Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\""
    resolution := .grant .landfallCreateElf .source }

/-- Elves you control get +P/+0 and vigilance until end of turn. -/
def chapterElvesGetVigilance (power : Int) : Effect :=
  { phrase := s!"Elves you control get {signedStat power}/+0 and gain vigilance until end of turn"
    resolution := .sequence [
      .pump (.fixed power) (.fixed 0) (.intersection [.creaturesYouControl, .youControl (.subtype "Elf")]),
      .grant (.keywords Keyword.vigilance) (.intersection [.creaturesYouControl, .youControl (.subtype "Elf")])] }

/-- Target opponent reveals their hand; you choose a nonland; they discard it. -/
def chapterOpponentDiscardsNonland : Effect :=
  { targeting := .of .opponent
    phrase := "target opponent reveals their hand. You choose a nonland card from it. That player discards that card"
    resolution := .discard .chosenNonland }

/-- Amass Goblins `n`. -/
def chapterAmassGoblins (n : Nat) : Effect :=
  { phrase := s!"amass Goblins {n}"
    resolution := .amass (.fixed n) }

/-- Target opponent loses `n` life and you gain `n` life. -/
def chapterOpponentLosesYouGain (n : Nat) : Effect :=
  { targeting := .of .opponent
    phrase := s!"target opponent loses {n} life and you gain {n} life"
    resolution := .sequence [.loseLife (.fixed n) (.target .opponent), .gainLife (.fixed n)] }

/-- Target creature you control gains hexproof while this Saga remains. -/
def chapterGrantHexproofWhileRemains : Effect :=
  { targeting := .of .creatureYouControl
    phrase := "target creature you control gains hexproof for as long as this Saga remains on the battlefield"
    resolution := .grant .hexproofWhileSource .target }

/-- Prevent damage that would be dealt by up to one target creature while
this Saga remains. -/
def chapterPreventDamageWhileRemains : Effect :=
  { targeting := .of .creature
    allowsZeroTargets := true
    phrase := "prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield"
    resolution := .grant .preventDamageWhileSource .target }

/-- Draw `n` cards. -/
def chapterDraw (n : Nat) : Effect :=
  { phrase := s!"draw {cardPhrase n}"
    resolution := .draw (.fixed n) }

/-- Search for up to `max` basic Plains, exile them, shuffle, gain `life`. -/
def chapterSearchBasicPlainsExileGainLife (max life : Nat) : Effect :=
  { phrase := s!"search your library for up to {max} basic Plains cards, exile them, then shuffle. You gain {life} life"
    resolution := .sequence [
      .searchLibrary (.exile (.basicUpTo "Plains" max) .forLater .linked),
      .gainLife (.fixed life)] }

/-- Put a card exiled with this Saga into its owner's hand. -/
def chapterReturnLinkedExileToHand : Effect :=
  { phrase := "put a card exiled with this Saga into its owner's hand"
    resolution := .returnToHand .linkedExile }

/-- Whenever you attack this turn, a target creature you control gets
+1/+1 per Plains you control. -/
def chapterGrantAttackPumpPerPlainsThisTurn : Effect :=
  { phrase := "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control"
    resolution := .queueReflexive (.pump .perPlains .perPlains .target) }

/-- Exile up to one target creature or land you control; return it at the
beginning of the next end step. -/
def chapterBlinkUntilEndStep : Effect :=
  { targeting := .of .creatureOrLandYouControl
    allowsZeroTargets := true
    phrase := "exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step"
    resolution := .exile .target .nextEndStep }

/-- Create a Treasure. Then if you control four or more, sacrifice this
Saga. If you do, create a 6/6 red Dragon with flying. -/
def chapterTreasureThenDragonIfFour : Effect :=
  { phrase := "create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying"
    resolution := .sequence [
      .createTokens .treasure (.fixed 1) false,
      .«if» ((.atLeast (.count (.youControl (.subtype "Treasure"))) (.fixed 4)))
        (.sacrifice (.sacrificedSource .isSacrificed) .noted),
      .«if» .sourceWasSacrificed (.createTokens .dragon (.fixed 1) false)] }

/-- Recruit. -/
def chapterRecruit : Effect :=
  { phrase := "recruit"
    resolution := .recruit }

/-- Return target creature card with mana value `n` or less from your
graveyard to the battlefield. -/
def chapterReturnCreatureFromGyMvAtMost (n : Nat) : Effect :=
  { targeting := .of (.creatureCardInYourGraveyardMvAtMost n)
    phrase := s!"return target creature card with mana value {n} or less from your graveyard to the battlefield"
    resolution := .put (.creatureMvAtMost n) }

/-- Put a +1/+1 counter on up to one target creature. -/
def chapterPlusOneUpToOne : Effect :=
  { targeting := .of .creature
    allowsZeroTargets := true
    phrase := "put a +1/+1 counter on up to one target creature"
    resolution := .putCounters (.ofKind .plusOnePlusOne) .permanent }

/-- Gain control of up to two creatures with total mana value `n` or less
for as long as this Saga remains. -/
def chapterGainControlOfUpToTwoCreaturesTotalMvAtMost (n : Nat) : Effect :=
  { targeting := .of (.upToTwoCreaturesTotalMvAtMost n)
    allowsZeroTargets := true
    phrase := s!"Gain control of up to two target creatures with total mana value {n} or less for as long as this Saga remains on the battlefield"
    resolution := .gainControl .whileSourceRemains }

/-- This Saga deals `n` damage to each creature that is not this subtype
and to each opponent. -/
def chapterDealDamageToEachNonSubtypeAndOpponents (n : Nat) (subtype : String) : Effect :=
  { phrase := s!"This Saga deals {n} damage to each non-{subtype} creature and each opponent"
    resolution := .dealDamage (.fixed n) (.eachNonSubtypeAndOpponents subtype) }

/-- This Saga deals X damage to target opponent, where X is the greatest
mana value among artifacts you control. -/
def chapterDealXDamageToTargetOpponentGreatestArtifactMv : Effect :=
  { targeting := .of .opponent
    phrase := "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control"
    resolution := .dealDamage .greatestArtifactMv (.player (.target .opponent)) }

end Effect

end Mtg.Engine
