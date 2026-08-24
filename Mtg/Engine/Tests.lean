import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Game

/-!
# Compile-time smoke tests for the engine.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

def demoConfig (seed : UInt64 := 20260807) : StartConfig := {
  seats := #[
    { name := "Chandra", deck := redDeck },
    { name := "Nissa", deck := greenDeck }
  ]
  format := .constructed
  seed := seed
  startingPlayer := some 0
}

def started : Game :=
  match Start.start (demoConfig 1) with
  | .ok g => g
  | .error e => panic! e

#guard isLegalDeck .constructed redDeck
#guard isLegalDeck .constructed greenDeck
#guard !isLegalDeck .constructed (copies 5 lightningBolt)

#guard started.players.size == 2
#guard (started.player ⟨0⟩).life == 20
#guard (started.player ⟨1⟩).life == 20
#guard (started.player ⟨0⟩).hand.size == 7
#guard (started.player ⟨1⟩).hand.size == 7
#guard (started.player ⟨0⟩).library.size == 53
#guard started.startingPlayer == ⟨0⟩
#guard started.isFirstTurn
#guard started.step == .upkeep

/-- First player skipped the draw step, so after advancing to the draw step
the active player's hand is still 7. -/
def afterDraw : Game :=
  match Game.pass started ⟨0⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨1⟩ with
    | .error e => panic! e
    | .ok g2 => g2

#guard afterDraw.step == .draw
#guard (afterDraw.player ⟨0⟩).hand.size == 7

def played : Game :=
  Agent.play started 80

#guard played.log.size > 10
#guard played.turnNumber ≥ 1

end Mtg.Engine.Tests
