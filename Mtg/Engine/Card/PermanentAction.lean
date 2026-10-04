import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text

/-!
# Permanent actions (CR 608.2b)

What a spell, activated ability, or trigger does to a permanent. Shared so
`Game.applyPermanentAction` is one match, whether the permanent is an
announced target or the ability's source.
-/

namespace Mtg.Engine

/-- What a spell, activated ability, or trigger does to a permanent
(CR 608.2b). Shared so `Game.applyPermanentAction` is one match, whether the
permanent is an announced target or the ability's source. -/
inductive PermanentAction where
  /-- Until-end-of-turn +P/+T. -/
  | pump (power toughness : Int)
  /-- Until-end-of-turn +P/+T and trample. -/
  | pumpAndTrample (power toughness : Int)
  /-- Destroy the permanent (CR 701.7). -/
  | destroy
  /-- Put `n` +1/+1 counters on the permanent (CR 122.1). -/
  | plusOne (n : Nat)
  /-- A +1/+1 counter plus trample and hexproof until end of turn. -/
  | plusOnePlusOneTrampleHexproof
  /-- Deal `amount` damage. -/
  | dealDamage (amount : Nat)
  /-- Damage plus lose-indestructible and exile-if-dies this turn. -/
  | dealDamageLoseIndestructibleExile (amount : Nat)
  /-- Destroy, then creatures without flying can't block this turn. -/
  | destroyThenNonflyersCantBlock
  /-- The permanent can't be blocked this turn. -/
  | cantBeBlocked
  /-- Until-end-of-turn +P/+T and lifelink. -/
  | pumpAndLifelink (power toughness : Int)
  /-- Until-end-of-turn +P/+T. If the creature would die this turn, exile it instead. -/
  | pumpAndExileIfDies (power toughness : Int)
  /-- Grant these keywords until end of turn. -/
  | grantKeywords (k : Keywords)
  /-- Tap the permanent. -/
  | tap
  /-- Untap the permanent. -/
  | untap
  /-- Until end of turn, this becomes an artifact in addition to its other
  types and gains indestructible. -/
  | becomeArtifactIndestructible
  /-- Until-end-of-turn +P/+T and these keywords. -/
  | pumpAndGrant (power toughness : Int) (k : Keywords)
deriving Repr, Inhabited, BEq

namespace PermanentAction

/-- Oracle-style text for this action on `noun` (e.g. `target creature`).
`sentence` capitalizes the first letter for activated-ability lines. -/
def toNotation (action : PermanentAction) (noun : String) (sentence := false) : String :=
  let damage (n : Nat) : String := s!"deals {n} damage to {noun}"
  let raw :=
    match action with
    | .pump p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} until end of turn"
    | .pumpAndTrample p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
    | .destroy => s!"destroy {noun}"
    | .plusOne n => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
    | .plusOnePlusOneTrampleHexproof =>
      s!"put a +1/+1 counter on {noun}. It gains trample and hexproof until end of turn"
    | .dealDamage n => damage n
    | .dealDamageLoseIndestructibleExile n =>
      s!"{damage n}. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
    | .destroyThenNonflyersCantBlock =>
      s!"destroy {noun}. Creatures without flying can't block this turn"
    | .cantBeBlocked => s!"{noun} can't be blocked this turn"
    | .pumpAndLifelink p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} and gains lifelink until end of turn"
    | .pumpAndExileIfDies p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} until end of turn. If that creature would die this turn, exile it instead"
    | .grantKeywords k =>
      s!"{noun} gains {k.joinedAnd} until end of turn"
    | .tap => s!"tap {noun}"
    | .untap => s!"untap {noun}"
    | .becomeArtifactIndestructible =>
      s!"until end of turn, {noun} becomes an artifact in addition to its other types and gains indestructible"
    | .pumpAndGrant p t k =>
      s!"{noun} gets {signedStat p}/{signedStat t} and gains {k.joinedAnd} until end of turn"
  if sentence then capitalizeAscii raw else raw

end PermanentAction

end Mtg.Engine
