import Mtg.Engine.Fixture

/-!
# `TriggerResolution.discard`

The controller's cards, each opponent, the announced opponent, the
controller's hand, and a discard after mana was spent. Who discards,
what is discarded, and when are arguments.
-/

namespace Mtg.Engine.DiscardTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def pebble : CardDef := { name := "Pebble", types := #[.artifact] }

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (resolutionOverride := some r)

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
  let g := g.setObject { ab with fraCauseStatus := some { manaSpentToCast := spent } }
  { g with resolvingAbility := some ab.id }

def emptyHand (g : Game) (p : PlayerId) : Game :=
  g.modifyPlayer p (fun pl => { pl with hand := #[] })

/- The controller discards the printed count. One card leaves the hand.
An empty hand skips the choice. The discarded-land note is cleared. -/
#guard
  let marked := ((afterDraw.player caster).hand[0]?).getD ⟨0⟩
  let g0 := step { afterDraw with discardedCardThisWay := some (caster, marked) } .discard
  match g0.pending with
  | .chooseDiscardCard p _ =>
    p == caster && g0.discardedCardThisWay.isNone &&
      handSize g0 caster == handSize afterDraw caster
  | _ => false

#guard
  let g0 := step afterDraw .discard
  let id := (g0.player caster).hand.back!
  let g := mustApply g0 caster (.discard id)
  handSize g caster == handSize g0 caster - 1 &&
    (g.player caster).graveyard.size == (g0.player caster).graveyard.size + 1 &&
    g.pending == .none

#guard
  let g := step afterDraw (.discard 2)
  g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

#guard
  let g := step (emptyHand afterDraw caster) .discard
  g.pending == .none && logContains g "has no card to discard" &&
    handSize g caster == 0

/- Inside `mayThen`, one card is optional and declining skips the draw. -/
#guard
  let g := step afterDraw (.may (.discard 1) (.draw (.fixed 2)) .ifYouDo)
  match g.pending with
  | .mayDiscardDraw p n => p == caster && n == 2
  | _ => false

#guard
  let g := step (emptyHand afterDraw caster) (.may (.discard 1) (.draw (.fixed 2)) .ifYouDo)
  g.pending == .none && g.mayThenDrop == 0 &&
    logContains g "has no card to discard" &&
    handSize g caster == 0

/- Each opponent discards. An empty hand skips that opponent. -/
#guard
  let g := step afterDraw (.discard (who := .each))
  match g.pending with
  | .chooseDiscardCard p _ => p == opp && handSize g opp == handSize afterDraw opp
  | _ => false

#guard
  let g := step (emptyHand afterDraw opp) (.discard (who := .each))
  g.pending == .none && logContains g "has no card to discard" &&
    handSize g opp == 0

/- The announced opponent discards. No target, or an illegal one, discards
nothing. -/
#guard
  let g := step afterDraw (.discard 2 (who := .target)) (targets := #[Target.player opp])
  g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == opp
    | _ => false

#guard
  let g := step afterDraw (.discard 2 (who := .target))
  g.pending == afterDraw.pending && handSize g opp == handSize afterDraw opp &&
    !(logContains g "must discard")

#guard
  let g := step afterDraw (.discard (who := .target)) (targets := #[Target.player caster])
  logContains g "The target is no longer legal" &&
    handSize g caster == handSize afterDraw caster &&
    match g.pending with
    | .chooseDiscardCard _ _ => false
    | _ => true

/- The controller may discard their hand. The note starts empty and records
the source. Declining is the choice, not an immediate discard. -/
#guard
  let g0 := addPermanent afterDraw pebble caster caster
  let sid := (pebbleOf g0).id
  let g := step g0 (.discard (what := .hand)) (some sid)
  g.handDiscardedThisWay.isNone && g.notedSourceThisWay == some sid &&
    handSize g caster == handSize g0 caster &&
    match g.pending with
    | .fraChoice p (.mayDiscardHandBalin s) => p == caster && s == some sid
    | _ => false

#guard
  let g := step afterDraw (.may (.discard (what := .hand)) (.sequence []))
  handSize g caster == handSize afterDraw caster &&
    match g.pending with
    | .fraChoice p (.mayDiscardHandBalin none) => p == caster
    | _ => false

/- Discarding the hand to draw a fixed number is the `mayThen` choice. -/
#guard
  let g := step afterDraw (.may (.discard (what := .hand)) (.draw (.fixed 4)) .ifYouDo)
  match g.pending with
  | .fraChoice p (.mayDiscardHandDrawFixed n) => p == caster && n == 4
  | _ => false

/- Mana spent selects this discard. The step still asks for `n` cards, and
it leaves a discarded-land note from an earlier step alone. -/
#guard
  let marked := ((afterDraw.player caster).hand[0]?).getD ⟨0⟩
  let g := step { afterDraw with discardedCardThisWay := some (caster, marked) }
    (.discard 2 (when := .ifManaSpent))
  g.pendingDiscardsLeft == 2 && g.discardedCardThisWay == some (caster, marked) &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

/- You may draw X, then discard two, only when mana was spent. -/
#guard
  let g := step (withSpent 4)
    (.may (.sequence [.draw .equalToManaSpent, .discard 2 (when := .ifManaSpent)]) (.sequence []))
  match g.pending with
  | .fraChoice p (.mayDrawThenDiscard 4 2) => p == caster
  | _ => false

#guard
  let g := step (withSpent 0)
    (.may (.sequence [.draw .equalToManaSpent, .discard 2 (when := .ifManaSpent)]) (.sequence []))
  g.pending == .none && logContains g "No mana was spent to cast that spell"

/- A combination that is not printed discards nothing. -/
#guard
  let marked := ((afterDraw.player caster).hand[0]?).getD ⟨0⟩
  let g0 := { afterDraw with discardedCardThisWay := some (caster, marked) }
  let g := step g0 (.discard 2 (who := .each) (when := .ifManaSpent))
    (targets := #[Target.player opp])
  g.pending == g0.pending && handSize g caster == handSize g0 caster &&
    handSize g opp == handSize g0 opp &&
    g.discardedCardThisWay == some (caster, marked) &&
    !(logContains g "must discard") && !(logContains g "may discard")

#guard
  let g := step afterDraw (.discard (what := .hand) (when := .ifManaSpent))
  g.pending == afterDraw.pending && g.handDiscardedThisWay.isNone &&
    handSize g caster == handSize afterDraw caster

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.resolutionPhrase { resolution := .discard } == "discard a card"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard 2 } == "discard 2 cards"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard (who := .each) } ==
  "each opponent discards a card"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard 2 (who := .each) } ==
  "each opponent discards 2 cards"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .opponent, resolution := .discard 2 (who := .target) } ==
  "target opponent discards 2 cards"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard (what := .hand) } ==
  "discard your hand"
#guard TriggeredAbility.resolutionPhrase { resolution := .may (.discard (what := .hand)) (.sequence []) } ==
  "you may discard your hand"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard 2 (when := .ifManaSpent) } ==
  "discard 2 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .may (.discard 1) (.draw (.fixed 2)) .ifYouDo } ==
  "you may discard a card. If you do, draw 2 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .may (.discard (what := .hand)) (.draw (.fixed 4)) .ifYouDo } ==
  "you may discard your hand. If you do, draw 4 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .sequence [
        .draw .equalToManaSpent, .discard 2 (when := .ifManaSpent)] } ==
  "draw X cards, where X is the amount of mana spent to cast that spell, then discard two cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .discard (who := .each) (what := .hand) } == "discard cards"

end Mtg.Engine.DiscardTests
