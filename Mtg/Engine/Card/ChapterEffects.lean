import Mtg.Engine.Card.Effect

/-!
# Saga-chapter effect constructors

`Effect.ofChapter` plus the `Effect.chapter*` constructors that lift
`ChapterResolution` payloads onto unified effects.
-/

namespace Mtg.Engine

namespace Effect

/-- Build a Saga-chapter `Effect` that still stores the apply payload
so `asChapter?` and `Game.applyChapterEffect` can recover it. -/
def mkChapter (payload : ChapterResolution) (targeting : EffectTargeting := {})
    (allowsZeroTargets := false) (phrase : String) : Effect :=
  { targeting
    allowsZeroTargets
    resolution := Resolution.trigger (SharedTrigger.chapter 0 payload)
    phrase }

/-- Convert a printed Saga chapter to the unified `Effect`.
Always wraps the original `ChapterResolution` so `asChapter?` can recover it. -/
def ofChapter : ChapterResolution → Effect
  | e@(.dealDamageToOppCreature n) =>
    mkChapter e (.of .oppCreature)
      (phrase := s!"this Saga deals {n} damage to target creature an opponent controls")
  | e@(.destroyOppArtifact) =>
    mkChapter e (.of .oppArtifact)
      (phrase := "destroy target artifact an opponent controls")
  | e@(.addMana mana) =>
    mkChapter e (phrase := s!"add {mana}")
  | e@(.searchBasicLandToHand) =>
    mkChapter e (phrase := searchLibraryToHandPhrase "a basic land card")
  | e@(.gainLandfallCreateElf) =>
    mkChapter e
      (phrase := "this Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"")
  | e@(.elvesGetVigilance p) =>
    mkChapter e
      (phrase := s!"Elves you control get {signedStat p}/+0 and gain vigilance until end of turn")
  | e@(.opponentDiscardsNonland) =>
    mkChapter e (.of .opponent)
      (phrase := "target opponent reveals their hand. You choose a nonland card from it. That player discards that card")
  | e@(.amassGoblins n) =>
    mkChapter e (phrase := s!"amass Goblins {n}")
  | e@(.opponentLosesYouGain n) =>
    mkChapter e (.of .opponent)
      (phrase := s!"target opponent loses {n} life and you gain {n} life")
  | e@(.grantHexproofWhileRemains) =>
    mkChapter e (.of .creatureYouControl)
      (phrase := "target creature you control gains hexproof for as long as this Saga remains on the battlefield")
  | e@(.preventDamageWhileRemains) =>
    mkChapter e (.of .creature) (allowsZeroTargets := true)
      (phrase := "prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield")
  | e@(.draw n) =>
    mkChapter e (phrase := s!"draw {cardPhrase n}")
  | e@(.searchBasicPlainsExileGainLife max life) =>
    mkChapter e
      (phrase := s!"search your library for up to {max} basic Plains cards, exile them, then shuffle. You gain {life} life")
  | e@(.returnLinkedExileToHand) =>
    mkChapter e
      (phrase := "put a card exiled with this Saga into its owner's hand")
  | e@(.grantAttackPumpPerPlainsThisTurn) =>
    mkChapter e
      (phrase := "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control")
  | e@(.blinkUntilEndStep) =>
    mkChapter e (.of .creatureOrLandYouControl) (allowsZeroTargets := true)
      (phrase := "exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step")
  | e@(.treasureThenDragonIfFour) =>
    mkChapter e
      (phrase := "create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying")
  | e@(.recruit) =>
    mkChapter e (phrase := "recruit")
  | e@(.returnCreatureFromGyMvAtMost n) =>
    mkChapter e (.of (.creatureCardInYourGraveyardMvAtMost n))
      (phrase := s!"return target creature card with mana value {n} or less from your graveyard to the battlefield")
  | e@(.plusOneUpToOne) =>
    mkChapter e (.of .creature) (allowsZeroTargets := true)
      (phrase := "put a +1/+1 counter on up to one target creature")
  | e@(.gainControlOfUpToTwoCreaturesTotalMvAtMost n) =>
    mkChapter e (.of (.upToTwoCreaturesTotalMvAtMost n)) (allowsZeroTargets := true)
      (phrase :=
        s!"Gain control of up to two target creatures with total mana value {n} or less for as long as this Saga remains on the battlefield")
  | e@(.dealDamageToEachNonSubtypeAndOpponents n subtype) =>
    mkChapter e
      (phrase :=
        s!"This Saga deals {n} damage to each non-{subtype} creature and each opponent")
  | e@(.dealXDamageToTargetOpponentGreatestArtifactMv) =>
    mkChapter e (.of .opponent)
      (phrase :=
        "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control")
  | e@(.spell s) =>
    mkChapter e s.targeting (allowsZeroTargets := s.allowsZeroTargets) (phrase := s.phrase)

/-- Printed leftover chapter constructors as unified `Effect` values. -/

def chapterDealDamageToOppCreature (n : Nat) : Effect :=
  ofChapter (.dealDamageToOppCreature n)

def chapterDestroyOppArtifact : Effect :=
  ofChapter .destroyOppArtifact

def chapterAddMana (mana : ManaType) : Effect :=
  ofChapter (.addMana mana)

def chapterSearchBasicLandToHand : Effect :=
  ofChapter .searchBasicLandToHand

def chapterGainLandfallCreateElf : Effect :=
  ofChapter .gainLandfallCreateElf

def chapterElvesGetVigilance (power : Int) : Effect :=
  ofChapter (.elvesGetVigilance power)

def chapterOpponentDiscardsNonland : Effect :=
  ofChapter .opponentDiscardsNonland

def chapterAmassGoblins (n : Nat) : Effect :=
  ofChapter (.amassGoblins n)

def chapterOpponentLosesYouGain (n : Nat) : Effect :=
  ofChapter (.opponentLosesYouGain n)

def chapterGrantHexproofWhileRemains : Effect :=
  ofChapter .grantHexproofWhileRemains

def chapterPreventDamageWhileRemains : Effect :=
  ofChapter .preventDamageWhileRemains

def chapterDraw (n : Nat) : Effect :=
  ofChapter (.draw n)

def chapterSearchBasicPlainsExileGainLife (max life : Nat) : Effect :=
  ofChapter (.searchBasicPlainsExileGainLife max life)

def chapterReturnLinkedExileToHand : Effect :=
  ofChapter .returnLinkedExileToHand

def chapterGrantAttackPumpPerPlainsThisTurn : Effect :=
  ofChapter .grantAttackPumpPerPlainsThisTurn

def chapterBlinkUntilEndStep : Effect :=
  ofChapter .blinkUntilEndStep

def chapterTreasureThenDragonIfFour : Effect :=
  ofChapter .treasureThenDragonIfFour

def chapterRecruit : Effect :=
  ofChapter .recruit

def chapterReturnCreatureFromGyMvAtMost (n : Nat) : Effect :=
  ofChapter (.returnCreatureFromGyMvAtMost n)

def chapterPlusOneUpToOne : Effect :=
  ofChapter .plusOneUpToOne

def chapterGainControlOfUpToTwoCreaturesTotalMvAtMost (n : Nat) : Effect :=
  ofChapter (.gainControlOfUpToTwoCreaturesTotalMvAtMost n)

def chapterDealDamageToEachNonSubtypeAndOpponents (n : Nat) (subtype : String) : Effect :=
  ofChapter (.dealDamageToEachNonSubtypeAndOpponents n subtype)

def chapterDealXDamageToTargetOpponentGreatestArtifactMv : Effect :=
  ofChapter .dealXDamageToTargetOpponentGreatestArtifactMv

/-- Pack a unified spell `Effect` as a leftover Saga chapter. -/
def chapterSpell (e : Effect) : ChapterResolution :=
  .spell {
    targeting := e.targeting
    allowsZeroTargets := e.allowsZeroTargets
    phrase := e.phrase
    resolution := e.spellResolution }

instance : Coe ChapterResolution Effect where
  coe := ofChapter

end Effect

end Mtg.Engine
