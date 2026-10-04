import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Fixture
import Mtg.Engine.Game

/-!
# Shared fixtures, start-of-game setup, and idle-action helpers.

The reused opening games live in `Mtg.Engine.Fixture`, which is compiled once.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

#guard testRedDeck.size == 60
#guard testGreenDeck.size == 60
#guard isLegalDeck .constructed testRedDeck
#guard isLegalDeck .constructed testGreenDeck
#guard !isLegalDeck .constructed (copies 5 lightningBolt)

#guard drawnHands.pending == .declareMulligan ⟨0⟩
#guard drawnHands.actor == some ⟨0⟩
#guard drawnHands.openingHandsPending
#guard !drawnHands.hasPriority ⟨0⟩
#guard (drawnHands.player ⟨0⟩).hand.size == 7
#guard (drawnHands.player ⟨1⟩).hand.size == 7
#guard !(drawnHands.player ⟨0⟩).keptOpeningHand

#guard started.players.size == 2
#guard (started.player ⟨0⟩).life == 20
#guard (started.player ⟨1⟩).life == 20
#guard (started.player ⟨0⟩).hand.size == 7
#guard (started.player ⟨1⟩).hand.size == 7
#guard (started.player ⟨0⟩).library.size == 53
#guard started.startingPlayer == ⟨0⟩
#guard started.isFirstTurn
#guard started.step == .upkeep

#guard nissaStarts.startingPlayer == ⟨1⟩
#guard nissaStarts.activePlayer == ⟨1⟩
#guard nissaStarts.pending == .declareMulligan ⟨1⟩
#guard nissaStarts.actor == some ⟨1⟩
#guard nissaStarts.log.any (· == "Starting player: Nissa")

#guard norandomOpening.norandom
#guard (norandomOpening.player ⟨0⟩).hand.isEmpty
#guard (norandomOpening.player ⟨1⟩).hand.isEmpty
#guard
  match norandomOpening.pendingRandom? with
  | some (.shuffleLibrary p) => p == ⟨0⟩
  | _ => false

#guard
  match norandomOpening.apply ⟨0⟩ (.supplyOrder #[⟨99⟩]) with
  | .error msg =>
    msg == "Shuffle must list each library card once (bottom first), or omit the ids to keep the current order"
  | .ok _ => false

#guard
  match norandomAfterFirstShuffle.pendingRandom? with
  | some (.shuffleLibrary p) => p == ⟨1⟩
  | _ => false
#guard (norandomAfterFirstShuffle.player ⟨0⟩).hand.isEmpty

#guard norandomDrawnHands.pending == .declareMulligan ⟨0⟩
#guard (norandomDrawnHands.player ⟨0⟩).hand.size == 7
#guard (norandomDrawnHands.player ⟨1⟩).hand.size == 7
#guard (norandomDrawnHands.player ⟨0⟩).library.size == 53

/- Without `--norandom`, `Start.start` still shuffles from the seed. -/
#guard !drawnHands.norandom
#guard drawnHands.pendingRandom?.isNone

#guard
  match Start.start { testConfig 1 with norandom := true, startingPlayer := none } with
  | .ok g =>
    match g.pendingRandom? with
    | some (.chooseIndex n) => n == 2 && g.startingPlayer == ⟨0⟩
    | _ => false
  | .error _ => false

#guard
  match Start.start { testConfig 1 with norandom := true, startingPlayer := none } with
  | .ok g =>
    match g.apply ⟨0⟩ (.supplyIndex 1) with
    | .ok g' =>
      g'.startingPlayer == ⟨1⟩ &&
        (match g'.pendingRandom? with
         | some (.shuffleLibrary p) => p == ⟨0⟩
         | _ => false) &&
        g'.log.any (· == "Starting player: Nissa")
    | .error _ => false
  | .error _ => false

#guard nissaStarted.startingPlayer == ⟨1⟩
#guard nissaStarted.activePlayer == ⟨1⟩
#guard nissaStarted.skipsFirstDraw
#guard nissaStarted.log.any (· == "Nissa takes the first turn")

#guard nissaAfterDraw.step == .precombatMain
#guard (nissaAfterDraw.player ⟨1⟩).hand.size == 7
#guard nissaAfterDraw.hasPriority ⟨1⟩
#guard nissaAfterDraw.log.any (· == "Nissa skips their first draw step (CR 103.8a)")

#guard started.skipsFirstDraw
#guard afterDraw.step == .precombatMain
#guard (afterDraw.player ⟨0⟩).hand.size == 7
#guard (afterDraw.player ⟨0⟩).library.size == 53
#guard afterDraw.hasPriority ⟨0⟩
#guard afterDraw.asSorcery? ⟨0⟩
#guard afterDraw.canPlayLand ⟨0⟩
#guard !afterDraw.hasPriority ⟨1⟩
#guard afterDraw.actor == some ⟨0⟩
#guard afterDraw.log.any (· == "Chandra skips their first draw step (CR 103.8a)")
#guard (started.beginStep .draw).step == .precombatMain
#guard ((started.beginStep .draw).player ⟨0⟩).hand.size == 7

def played : Game :=
  Agent.play started 80

#guard played.log.size > 10
#guard played.turnNumber ≥ 1
#guard started.stack.isEmpty

#guard (drawnOnce.player ⟨0⟩).hand.size == 8
#guard (drawnOnce.player ⟨0⟩).library.size == 52
#guard (drawnOnce.player ⟨1⟩).hand.size == 7

-- Occupants are unchanged, but the land is now tapped (CR 110.5 / 605.3a).
#guard withMountain.battlefield.map (·.id) == tappedMountain.battlefield.map (·.id)
#guard tappedMountain.battlefield.any (·.status.tapped)
#guard !(withMountain.battlefield.any (·.status.tapped))
#guard (tappedMountain.player ⟨0⟩).manaPool != (withMountain.player ⟨0⟩).manaPool

#guard tappedMountain.battlefield.map (·.id) == afterUntapStep.battlefield.map (·.id)
#guard afterUntapStep.step == .untap
#guard !(afterUntapStep.battlefield.any (·.status.tapped))
#guard afterUntapStep.log.any (fun s => mentions s "untaps Mountain")

#guard (stolenMountain.permanentsOf ⟨1⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard !(stolenMountain.permanentsOf ⟨0⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard (lastPermanent stolenMountain).owner == ⟨0⟩
#guard (lastPermanent stolenMountain).controller == some ⟨1⟩

#guard withMountain.battlefield.map (·.id) == afterControlChange.battlefield.map (·.id)
#guard (lastPermanent afterControlChange).controller == some ⟨1⟩
#guard (lastPermanent afterControlChange).owner == ⟨0⟩

#guard (mixedControllers.permanentsOf ⟨0⟩)[0]!.name == "Forest"
#guard (mixedControllers.permanentsOf ⟨1⟩)[0]!.name == "Mountain"

#guard (lastPermanent uncontrolledPermanent).controller.isNone
#guard (lastPermanent uncontrolledPermanent).owner == ⟨0⟩

def withAttercop : Game := addPermanent started attercop ⟨0⟩ ⟨0⟩
def withWarg : Game := addPermanent started raveningWarg ⟨0⟩ ⟨0⟩
def withGollum : Game := addPermanent started gollumSilentSlinker ⟨0⟩ ⟨0⟩
def withCrusher : Game := addPermanent started ologHaiCrusher ⟨0⟩ ⟨0⟩

end Mtg.Engine.Tests
