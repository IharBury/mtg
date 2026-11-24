import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture

/-!
# Unified discard instructions (`Instruction.discard*`)

The controller's cards, each opponent, the announced opponent, and the
controller's hand. Optional discard-to-draw and discard-after-mana-spent
execute through unified `Instruction.optional` and `Instruction.ifCond`.
-/

namespace Mtg.Engine.DiscardTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def pebble : CardDef := { name := "Pebble", types := #[.artifact] }

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .none) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targets := spec, body })
    sourceId targets

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
  let causeId : ObjectId := ⟨910⟩
  let g := g.record (GameEvent.manaSpent g.turnNumber caster (Array.replicate spent { mana := .colorless }) (forObject := some causeId))
  let g := g.record (GameEvent.spellCast g.turnNumber caster
    { id := some causeId, controller := some caster, owner := caster } (.hand caster))
  let abId : ObjectId := ⟨g.nextObjectId⟩
  let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId (g.snapshot src) caster
    (spec := { sourceId := some src.id, fraCauseId := some causeId, fraCauseStatus := some {} }))
  g.change (.resolvingAbility (some abId))

/- The controller discards the printed count. One card leaves the hand.
An empty hand skips the choice. -/
#guard
  let g0 := step afterDraw (Instruction.discardFixed 1)
  match g0.pending with
  | .chooseDiscardCard p _ =>
    p == caster && handSize g0 caster == handSize afterDraw caster
  | _ => false

#guard
  let g0 := step afterDraw (Instruction.discardFixed 1)
  let id := (g0.player caster).hand.back!
  let g := mustApply g0 caster (.discard id)
  handSize g caster == handSize g0 caster - 1 &&
    (g.player caster).graveyard.size == (g0.player caster).graveyard.size + 1 &&
    g.pending == .none

#guard
  let g := step afterDraw (Instruction.discardFixed 2)
  g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

#guard
  let g := step (emptyHand afterDraw caster) (Instruction.discardFixed 1)
  g.pending == .none && handSize g caster == 0

/- Optional discard to draw 2 cards; empty hand skips cleanly. -/
#guard
  let g := step afterDraw (Effect.triggerMayDiscardDraw 2).body
  match g.pending with
  | .mayDiscardDraw p n => p == caster && n == 2
  | .fraChoice p _ => p == caster
  | _ => false

#guard
  let g := step (emptyHand afterDraw caster) (Effect.triggerMayDiscardDraw 2).body
  g.pending == .none && handSize g caster == 0

/- Each opponent discards. An empty hand skips that opponent. -/
#guard
  let g := step afterDraw Effect.triggerEachOpponentDiscards.body
  match g.pending with
  | .chooseDiscardCard p _ => p == opp && handSize g opp == handSize afterDraw opp
  | _ => false

#guard
  let g := step (emptyHand afterDraw opp) Effect.triggerEachOpponentDiscards.body
  g.pending == .none && handSize g opp == 0

/- The announced opponent discards. No target, or an illegal one, discards nothing. -/
#guard
  let g := step afterDraw (Effect.triggerTargetOpponentDiscards 2).body none #[Target.player opp] .opponent
  g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == opp
    | _ => false

#guard
  let g := step afterDraw (Effect.triggerTargetOpponentDiscards 2).body none #[] .opponent
  g.pending == afterDraw.pending && handSize g opp == handSize afterDraw opp

#guard
  let g := step afterDraw (Effect.triggerTargetOpponentDiscards 1).body none #[Target.player caster] .opponent
  handSize g caster == handSize afterDraw caster &&
    match g.pending with
    | .chooseDiscardCard _ _ => false
    | _ => true

/- Optional discard hand to draw a fixed number offers a choice; accepting discards hand and draws 4. -/
#guard
  let g := step afterDraw (Effect.triggerMayDiscardHandDraw 4).body
  let accepted := mustApply g caster .accept
  let declined := mustApply g caster .decline
  handSize declined caster == handSize afterDraw caster &&
    handSize accepted caster == 4

/- Balin: optional discard hand, draw that many, damage if storied. -/
#guard
  let g0 := addPermanent afterDraw pebble caster caster
  let sid := (pebbleOf g0).id
  let g := step g0 Effect.triggerDiscardHandDrawDamageIfStory.body (some sid)
  handSize g caster == handSize g0 caster && g.pending != .none

/- Conditional discard when mana was spent to cast the causing spell. -/
def discardIfManaSpent : Instruction :=
  Instruction.ifThen (.cmp .gt (.manaSpent .triggerSubject) (.const 0)) (Instruction.discardFixed 2)

#guard
  let g0 := withSpent 3
  let g := step g0 discardIfManaSpent
  g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

#guard
  let g0 := withSpent 0
  let g := step g0 discardIfManaSpent
  g.pending == g0.pending && handSize g caster == handSize g0 caster

/- Draw X equal to mana spent, then if mana was spent, discard 2. -/
def drawXThenDiscardTwo : Instruction :=
  .seq #[
    Instruction.draw (.manaSpent .triggerSubject),
    discardIfManaSpent
  ]

#guard
  let g0 := withSpent 4
  let before := handSize g0 caster
  let g := step g0 drawXThenDiscardTwo
  handSize g caster == before + 4 && g.pendingDiscardsLeft == 2 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

#guard
  let g0 := withSpent 0
  let g := step g0 drawXThenDiscardTwo
  g.pending == .none && handSize g caster == handSize g0 caster

/- Printed phrases stay intact. -/
#guard TriggeredAbility.resolutionPhrase Effect.triggerEachOpponentDiscards ==
  "each opponent discards a card"
#guard TriggeredAbility.resolutionPhrase (Effect.triggerTargetOpponentDiscards 2) ==
  "target opponent discards 2 cards"
#guard TriggeredAbility.resolutionPhrase (Effect.triggerMayDiscardDraw 2) ==
  "you may discard a card. If you do, draw 2 cards"
#guard TriggeredAbility.resolutionPhrase (Effect.triggerMayDiscardHandDraw 4) ==
  "you may discard your hand. If you do, draw 4 cards"

/- CR 118.12a / 701.9b: Thirst for Knowledge's two-card discard shares a single
batch whether paid one card at a time after declining or chosen simultaneously. -/
#guard
  let g0 := insertObject (insertObject Mtg.Engine.Tests.afterDraw pebble caster (.hand caster)) pebble caster (.hand caster)
  let g1 := g0.applyEffect caster Effect.drawThreeDiscardUnlessArtifact #[]
  let pebbles := ((g1.player caster).hand.filter (fun id => (g1.object! id).name == pebble.name)).extract 0 2
  let gSim := mustApply g1 caster (.choosePermanents pebbles)
  let moves := (gSim.events.extract g0.events.size gSim.events.size).filter (fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ (.hand _) (.graveyard _) .discard ..)) => true
    | _ => false)
  gSim.pending == .none && gSim.discardBatch.isNone &&
    moves.size == 2 && moves[0]!.batch.isSome && moves[0]!.batch == moves[1]!.batch

end Mtg.Engine.DiscardTests
