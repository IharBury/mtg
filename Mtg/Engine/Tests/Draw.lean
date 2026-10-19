import Mtg.Engine.Fixture

/-!
# `TriggerResolution.draw`

A fixed count, one card per tapped Human, one card per fat graveyard, the
discarded hand, mana spent to cast the triggering spell, and the opponent's
offer to have you draw.
-/

namespace Mtg.Engine.DrawTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opponent : PlayerId := ⟨1⟩

def pebble : CardDef := { name := "Pebble", types := #[.artifact] }

def handSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).hand.size

def pebbleOf (g : Game) : GameObject :=
  match g.battlefield.find? (·.name == "Pebble") with
  | some o => o
  | none => panic! "missing Pebble"

/-- A resolving ability whose cause recorded `spent` mana. -/
def withSpent (spent : Nat) : Game :=
  let g := addPermanent afterDraw pebble caster caster
  let src := pebbleOf g
  let (g, ab) := g.allocStackAbility src caster
  let g := g.setObject { ab with triggerCause := { status := some { manaSpentToCast := spent } } }
  { g with resolvingAbility := some ab.id }

def drawStep (g : Game) (r : TriggeredAbility.TriggerResolution) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) none
    (resolutionOverride := some r)

/- The controller draws the printed count. -/
#guard
  let before := handSize afterDraw caster
  let g := afterDraw.applyTriggeredAbility caster (.onEnterDraw 2) none
  handSize g caster == before + 2

/- Each Human tapped by the previous step is one card. Zero taps draw nothing. -/
#guard
  let before := handSize afterDraw caster
  let g := drawStep { afterDraw with thisWay := { afterDraw.thisWay with humansTappedThisWay := 2 } }
    (.draw .forEachTappedHuman)
  handSize g caster == before + 2 && g.humansTappedThisWay == 0

#guard
  let before := handSize afterDraw caster
  let g := drawStep { afterDraw with thisWay := { afterDraw.thisWay with humansTappedThisWay := 0 } }
    (.draw .forEachTappedHuman)
  handSize g caster == before && g.humansTappedThisWay == 0

/- One card for each graveyard with seven or more cards. -/
#guard
  let before := handSize afterDraw caster
  let g := (afterDraw.mill caster 7).applyTriggeredAbility caster
    .onDiesDrawPerFatGraveyard none
  handSize g caster == before + 1

#guard
  let before := handSize afterDraw caster
  let g := afterDraw.applyTriggeredAbility caster .onDiesDrawPerFatGraveyard none
  handSize g caster == before && logContains g "draws no cards"

/- The discarded-hand note is the draw count. A declined discard draws nothing. -/
#guard
  let before := handSize afterDraw caster
  let g := drawStep { afterDraw with thisWay := { afterDraw.thisWay with handDiscardedThisWay := some 3 } }
    (.draw .discardedHand)
  handSize g caster == before + 3

#guard
  let before := handSize afterDraw caster
  let g := drawStep afterDraw (.draw .discardedHand)
  handSize g caster == before

/- Mana spent to cast the triggering spell is the draw count. None skips
the rest of the sequence. -/
#guard
  let g0 := withSpent 4
  let before := handSize g0 caster
  let g := drawStep g0 (.draw .equalToManaSpent)
  handSize g caster == before + 4 && !g.skipTriggerSequenceRest

#guard
  let g := drawStep (withSpent 0) (.draw .equalToManaSpent)
  g.skipTriggerSequenceRest && logContains g "No mana was spent to cast that spell" &&
    handSize g caster == handSize (withSpent 0) caster

/- The targeted opponent is offered the draw. A missing offer does nothing. -/
#guard
  let g0 := addPermanent afterDraw pebble caster caster
  let sid := (pebbleOf g0).id
  let g := drawStep { g0 with thisWay := { g0.thisWay with palantirChoiceReady := some (caster, opponent, sid) } }
    (.draw (.fixed 1) (who := .opponentHasYou))
  match g.pending with
  | .fraChoice p (.palantirMayDraw c id) =>
    p == opponent && c == caster && id == sid && g.palantirChoiceReady.isNone
  | _ => false

#guard
  let g := drawStep afterDraw (.may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence []))
  g.pending == .none && handSize g caster == handSize afterDraw caster

/- You may draw X and discard two when mana was spent. -/
#guard
  let g := (withSpent 4).applyTriggeredAbility caster
    .onCastNoncreatureMayDrawXDiscard2 none
  match g.pending with
  | .fraChoice p (.mayDrawThenDiscard 4 2) => p == caster
  | _ => false

#guard
  let g := (withSpent 0).applyTriggeredAbility caster
    .onCastNoncreatureMayDrawXDiscard2 none
  g.pending == .none && logContains g "No mana was spent to cast that spell"

/- Tapping Humans is the choice that records the later draw count. -/
#guard
  let g := afterDraw.applyTriggeredAbility caster .onAttackTapHumansDraw none
  g.pending == .tapHumans caster && g.humansTappedThisWay == 0

end Mtg.Engine.DrawTests
