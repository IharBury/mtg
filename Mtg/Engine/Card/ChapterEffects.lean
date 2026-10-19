import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.Trigger

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
    resolution := (TriggeredAbility.chapterTiming payload).resolution
    sharedTrigger := some (.chapter 0 payload)
    phrase }

/-- Convert a printed Saga chapter to the unified `Effect`.
Always wraps the original `ChapterResolution` so `asChapter?` can recover it. -/
def ofChapter : ChapterResolution → Effect
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
  ofChapter (.amass n)

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
