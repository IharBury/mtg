import Mtg.Engine.Fixture

/-!
# `TriggerResolution.discard`

The controller's cards, each opponent, the announced opponent, and the
controller's hand. What is discarded is one `ObjectSelector`.
Discarding when mana was spent is `TriggerResolution.if`.
-/

namespace Mtg.Engine.DiscardTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

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
  let causeId : ObjectId := ⟨910⟩
  let g := g.record (GameEvent.spentMana g.turnNumber caster spent (forObject := some causeId))
  let g := g.record (GameEvent.cast g.turnNumber caster
    { id := some causeId, controller := some caster, owner := caster } (.hand caster))
  let g := g.changeObjects ab.id #[
    .fraCauseId (some causeId),
    .fraCauseStatus (some {})]
  g.change (.resolvingAbility (some ab.id))

/- The controller discards the printed count. One card leaves the hand.
An empty hand skips the choice. The discarded-land note is cleared. -/
#guard
  let marked := ((afterDraw.player caster).hand[0]?).getD ⟨0⟩
  let g0 := step (afterDraw.change (.discardedCardThisWay (some (caster, marked)))) .discard
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
  let g := step afterDraw (.discard (.cards 2))
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
  let g := step afterDraw (.may (.discard (.cards 1)) (.draw (.fixed 2)) .ifYouDo)
  match g.pending with
  | .mayDiscardDraw p n => p == caster && n == 2
  | _ => false

#guard
  let g := step (emptyHand afterDraw caster) (.may (.discard (.cards 1)) (.draw (.fixed 2)) .ifYouDo)
  g.pending == .none && g.mayThenDrop == 0 &&
    logContains g "has no card to discard" &&
    handSize g caster == 0

/- Each opponent discards. An empty hand skips that opponent. -/
#guard
  let g := step afterDraw (.discard (.cards 1 .eachOpponent))
  match g.pending with
  | .chooseDiscardCard p _ => p == opp && handSize g opp == handSize afterDraw opp
  | _ => false

#guard
  let g := step (emptyHand afterDraw opp) (.discard (.cards 1 .eachOpponent))
  g.pending == .none && logContains g "has no card to discard" &&
    handSize g opp == 0

/- The announced opponent discards. No target, or an illegal one, discards
nothing. -/
#guard
  let g := step afterDraw (.discard (.cards 2 (.target .opponent))) (targets := #[Target.player opp])
  g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == opp
    | _ => false

#guard
  let g := step afterDraw (.discard (.cards 2 (.target .opponent)))
  g.pending == afterDraw.pending && handSize g opp == handSize afterDraw opp &&
    !(logContains g "must discard")

#guard
  let g := step afterDraw (.discard (.cards 1 (.target .opponent))) (targets := #[Target.player caster])
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
  let g := step g0 (.discard .hand) (some sid)
  g.handDiscardedThisWay.isNone && g.notedSourceThisWay == some sid &&
    handSize g caster == handSize g0 caster &&
    match g.pending with
    | .fraChoice p (.mayDiscardHandBalin s) => p == caster && s == some sid
    | _ => false

#guard
  let g := step afterDraw (.may (.discard .hand) (.sequence []))
  handSize g caster == handSize afterDraw caster &&
    match g.pending with
    | .fraChoice p (.mayDiscardHandBalin none) => p == caster
    | _ => false

/- Discarding the hand to draw a fixed number is the `mayThen` choice. -/
#guard
  let g := step afterDraw (.may (.discard .hand) (.draw (.fixed 4)) .ifYouDo)
  match g.pending with
  | .fraChoice p (.mayDiscardHandDrawFixed n) => p == caster && n == 4
  | _ => false

/- Discarding when mana was spent is `if`. The step asks for `n` cards.
Spending none discards nothing and leaves an earlier note alone. -/
#guard
  let marked := ((afterDraw.player caster).hand[0]?).getD ⟨0⟩
  let g0 := (withSpent 3).change (.discardedCardThisWay (some (caster, marked)))
  let g := step g0 (.«if» .manaSpent (.discard (.cards 2)))
  g.pendingDiscardsLeft == 2 && g.discardedCardThisWay.isNone &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

#guard
  let marked := ((afterDraw.player caster).hand[0]?).getD ⟨0⟩
  let g0 := (withSpent 0).change (.discardedCardThisWay (some (caster, marked)))
  let g := step g0 (.«if» .manaSpent (.discard (.cards 2)))
  g.pending == g0.pending && handSize g caster == handSize g0 caster &&
    g.discardedCardThisWay == some (caster, marked) &&
    !(logContains g "must discard")

/- You may draw X, then discard two, only when mana was spent. -/
#guard
  let g := step (withSpent 4)
    (.may (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]) (.sequence []))
  match g.pending with
  | .fraChoice p (.mayDrawThenDiscard 4 2) => p == caster
  | _ => false

#guard
  let g := step (withSpent 0)
    (.may (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]) (.sequence []))
  g.pending == .none && logContains g "No mana was spent to cast that spell"

/- The same gate runs after drawing X. Spending none skips the discard. -/
#guard
  let g0 := withSpent 4
  let before := handSize g0 caster
  let g := step g0 (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))])
  handSize g caster == before + 4 && g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

#guard
  let g0 := withSpent 0
  let g := step g0 (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))])
  g.pending == .none && handSize g caster == handSize g0 caster &&
    logContains g "No mana was spent to cast that spell"

/- A combination that is not printed discards nothing. -/
#guard
  let marked := ((afterDraw.player caster).hand[0]?).getD ⟨0⟩
  let g0 := afterDraw.change (.discardedCardThisWay (some (caster, marked)))
  let g := step g0 (.discard .source)
    (targets := #[Target.player opp])
  g.pending == g0.pending && handSize g caster == handSize g0 caster &&
    handSize g opp == handSize g0 opp &&
    g.discardedCardThisWay == some (caster, marked) &&
    !(logContains g "must discard") && !(logContains g "may discard")

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.resolutionPhrase { resolution := .discard } == "discard a card"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard (.cards 2) } == "discard 2 cards"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard (.cards 1 .eachOpponent) } ==
  "each opponent discards a card"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard (.cards 2 .eachOpponent) } ==
  "each opponent discards 2 cards"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .opponent, resolution := .discard (.cards 2 (.target .opponent)) } ==
  "target opponent discards 2 cards"
#guard TriggeredAbility.resolutionPhrase { resolution := .discard .hand } ==
  "discard your hand"
#guard TriggeredAbility.resolutionPhrase { resolution := .may (.discard .hand) (.sequence []) } ==
  "you may discard your hand"
#guard TriggeredAbility.resolutionPhrase { resolution := .«if» .manaSpent (.discard (.cards 2)) } ==
  "discard 2 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .may (.discard (.cards 1)) (.draw (.fixed 2)) .ifYouDo } ==
  "you may discard a card. If you do, draw 2 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .may (.discard .hand) (.draw (.fixed 4)) .ifYouDo } ==
  "you may discard your hand. If you do, draw 4 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .sequence [
        .draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))] } ==
  "draw X cards, where X is the amount of mana spent to cast that spell, then discard two cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .discard .source } == "discard cards"

end Mtg.Engine.DiscardTests
