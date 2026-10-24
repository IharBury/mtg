import Mtg.Engine.Catalog
import Mtg.Engine.Game

/-!
# Cached test games

These values are compiled into one plugin and initialized once per process.
`#guard` then reads the stored game instead of rebuilding decks and opening
hands for every check.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- 60-card constructed red fixture used only by engine tests. -/
@[irreducible, noinline] def testRedDeck : Array CardDef :=
  copies 32 mountain ++
    copies 4 lightningBolt ++
    copies 4 shock ++
    copies 4 ragingGoblin ++
    copies 4 grayOgre ++
    copies 4 hillGiant ++
    copies 4 canyonMinotaur ++
    copies 4 mountain

/-- 60-card constructed green fixture used only by engine tests. -/
@[irreducible, noinline] def testGreenDeck : Array CardDef :=
  copies 32 forest ++
    copies 4 llanowarElves ++
    copies 4 giantGrowth ++
    copies 4 grizzlyBears ++
    copies 4 giantSpider ++
    copies 4 crawWurm ++
    copies 4 centaurCourser ++
    copies 4 rumblingBaloth

def testConfig (seed : UInt64 := 20260807) : StartConfig := {
  seats := #[
    { name := "Chandra", deck := testRedDeck },
    { name := "Nissa", deck := testGreenDeck }
  ]
  format := .constructed
  seed := seed
  startingPlayer := some 0
}

@[irreducible, noinline] def drawnHands : Game :=
  match Start.start (testConfig 1) with
  | .ok g => g
  | .error e => panic! e

/-- Keep every remaining opening hand (CR 103.5) so tests can begin on turn 1. -/
def keepOpeningHands : Game → Nat → Game
  | _, 0 => panic! "keepOpeningHands fuel exhausted"
  | g, n + 1 =>
    match g.pending with
    | .declareMulligan p =>
      match g.apply p .keep with
      | .ok g' => keepOpeningHands g' n
      | .error e => panic! e
    | .putOnBottom _ _ => panic! "keepOpeningHands: unexpected putOnBottom"
    | _ => g

@[irreducible, noinline] def started : Game := keepOpeningHands drawnHands 8

/-- CR 103.1: the starting player is chosen before opening hands; that player
declares keep-or-mulligan first (CR 103.5). -/
@[irreducible, noinline] def nissaStarts : Game :=
  match Start.start { testConfig 1 with startingPlayer := some 1 } with
  | .ok g => g
  | .error e => panic! e

/-- `--norandom` pauses before opening shuffles so the host supplies the order. -/
@[irreducible, noinline] def norandomOpening : Game :=
  match Start.start { testConfig 1 with norandom := true } with
  | .ok g => g
  | .error e => panic! e

@[irreducible, noinline] def norandomAfterFirstShuffle : Game :=
  match norandomOpening.apply ⟨0⟩ (.supplyOrder #[]) with
  | .ok g => g
  | .error e => panic! e

@[irreducible, noinline] def norandomDrawnHands : Game :=
  match norandomAfterFirstShuffle.apply ⟨1⟩ (.supplyOrder #[]) with
  | .ok g => g
  | .error e => panic! e

@[irreducible, noinline] def nissaStarted : Game := keepOpeningHands nissaStarts 8

@[irreducible, noinline] def nissaAfterDraw : Game :=
  match Game.pass nissaStarted ⟨1⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨0⟩ with
    | .error e => panic! e
    | .ok g2 => g2

/-- First player skipped the draw step (CR 103.8a / 500.11), so after upkeep
the game proceeds to precombat main: no card is drawn and nobody received
priority during the skipped step. -/
@[irreducible, noinline] def afterDraw : Game :=
  match Game.pass started ⟨0⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨1⟩ with
    | .error e => panic! e
    | .ok g2 => g2

/-- `true` iff `needle` occurs in `haystack`. -/
def mentions (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- `true` iff some log line contains `needle`. -/
def logContains (g : Game) (needle : String) : Bool :=
  g.log.any (fun s => mentions s needle)

/-- First card of `p`'s hand; tests assume opening hands are non-empty. -/
def firstHandCard (g : Game) (p : PlayerId) : GameObject :=
  match (g.handObjects p)[0]? with
  | some o => o
  | none => panic! "expected a card in hand"

@[irreducible, noinline] def drawnOnce : Game := Game.draw started ⟨0⟩

/-- Put `card` into the game as a new object and optionally update its owner. -/
def insertObject (g : Game) (card : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (updateOwner : ObjectId → Player → Player := fun _ pl => pl) : Game :=
  let (g, obj) := g.allocObject card owner zone controller status
  g.modifyPlayer owner (updateOwner obj.id)

/-- Put `card` onto the battlefield with explicit owner and controller. -/
def addPermanent (g : Game) (card : CardDef) (owner controller : PlayerId) : Game :=
  let status : Status :=
    { summoningSick := false
      indestructibleCounters := if card.entersWithIndestructibleCounter then 1 else 0 }
  insertObject g card owner .battlefield (some controller) status

/-- Drop a basic land onto the battlefield without using the play-land action. -/
def addUntappedLand (g : Game) (card : CardDef) : Game :=
  addPermanent g card g.activePlayer g.activePlayer

@[irreducible, noinline] def withMountain : Game := addUntappedLand started mountain

@[irreducible, noinline] def tappedMountain : Game :=
  match (withMountain.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => panic! "expected a land on the battlefield"
  | some o =>
    match o.printed.manaAbilities[0]? with
    | none => panic! s!"{o.name} has no mana ability"
    | some m =>
      match withMountain.tapForMana ⟨0⟩ o.id m with
      | .ok g => g
      | .error e => panic! e

/-- Last permanent on the battlefield; tests assume one is present. -/
def lastPermanent (g : Game) : GameObject :=
  match g.battlefield.back? with
  | some o => o
  | none => panic! "expected a permanent on the battlefield"

/-- Untap is a turn-based action (CR 502.2): occupants stay put, but the land
is no longer tapped. -/
@[irreducible, noinline] def afterUntapStep : Game := tappedMountain.beginStep .untap

/-- A permanent Chandra owns and Nissa controls is among Nissa's permanents. -/
@[irreducible, noinline] def stolenMountain : Game := addPermanent started mountain ⟨0⟩ ⟨1⟩

/-- Changing control does not move the permanent off the battlefield. -/
@[irreducible, noinline] def afterControlChange : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := some ⟨1⟩ }

/-- Nissa's permanent entered first; Chandra still has a later Forest. -/
@[irreducible, noinline] def mixedControllers : Game := addPermanent stolenMountain forest ⟨0⟩ ⟨0⟩

@[irreducible, noinline] def uncontrolledPermanent : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := none }

@[irreducible, noinline] def withGoblin : Game := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
@[irreducible, noinline] def withElves : Game := addPermanent started llanowarElves ⟨0⟩ ⟨0⟩
@[irreducible, noinline] def withSpider : Game := addPermanent started giantSpider ⟨0⟩ ⟨0⟩

end Mtg.Engine.Tests
