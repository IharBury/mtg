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
  /-- Deal `amount` damage. -/
  | dealDamage (amount : Nat)
  /-- Damage plus lose-indestructible and exile-if-dies this turn. -/
  | dealDamageLoseIndestructibleExile (amount : Nat)
  /-- The permanent can't be blocked this turn. -/
  | cantBeBlocked
  /-- Until-end-of-turn +P/+T. If the creature would die this turn, exile it instead. -/
  | pumpAndExileIfDies (power toughness : Int)
  /-- Grant these keywords until end of turn. -/
  | grantKeywords (k : Keywords)
  /-- Put an indestructible counter on the permanent. -/
  | indestructibleCounter
  /-- Put a double strike counter on the permanent. -/
  | doubleStrikeCounter
  /-- Put a burden counter on the permanent. -/
  | burdenCounter
  /-- Tap the permanent. -/
  | tap
  /-- Untap the permanent. -/
  | untap
  /-- Until end of turn, this becomes an artifact in addition to its other
  types and gains indestructible. -/
  | becomeArtifactIndestructible
  /-- The permanent becomes prepared (Reality Fracture). -/
  | becomePrepared
  /-- Until-end-of-turn layer-7b base power and toughness (CR 613.4b). -/
  | setBasePT (power toughness : Int)
  /-- Tap the permanent and put a stun counter on it (CR 122.1d). -/
  | tapAndStun
  /-- The owner puts this permanent on top of their library. -/
  | putOnTopOfLibrary
  /-- The owner puts this permanent on the bottom of their library. -/
  | putOnBottomOfLibrary
  /-- Exile the permanent. -/
  | exile
  /-- Until end of turn, add this permanent's power and toughness to itself,
  which doubles them. -/
  | doublePowerAndToughness
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
    | .dealDamage n => damage n
    | .dealDamageLoseIndestructibleExile n =>
      s!"{damage n}. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
    | .cantBeBlocked => s!"{noun} can't be blocked this turn"
    | .pumpAndExileIfDies p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} until end of turn. If that creature would die this turn, exile it instead"
    | .grantKeywords k =>
      s!"{noun} gains {k.joinedAnd} until end of turn"
    | .indestructibleCounter =>
      s!"put an indestructible counter on {noun}"
    | .doubleStrikeCounter =>
      s!"put a double strike counter on {noun}"
    | .burdenCounter =>
      s!"put a burden counter on {noun}"
    | .tap => s!"tap {noun}"
    | .untap => s!"untap {noun}"
    | .becomeArtifactIndestructible =>
      s!"until end of turn, {noun} becomes an artifact in addition to its other types and gains indestructible"
    | .becomePrepared => s!"{noun} becomes prepared"
    | .setBasePT p t =>
      s!"{noun} has base power and toughness {p}/{t} until end of turn"
    | .tapAndStun => s!"tap {noun} and put a stun counter on it"
    | .putOnTopOfLibrary =>
      s!"{noun}'s owner puts it on top of their library"
    | .putOnBottomOfLibrary =>
      s!"{noun}'s owner puts it on the bottom of their library"
    | .exile => s!"exile {noun}"
    | .doublePowerAndToughness =>
      s!"double {noun}'s power and toughness until end of turn"
  if sentence then capitalizeAscii raw else raw

end PermanentAction

end Mtg.Engine
