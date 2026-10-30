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

/-- Put `card` into the game as a new object in `zone` (inserting into its zone list). -/
def insertObject (g : Game) (card : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {}) : Game :=
  (g.allocObject card owner zone controller status).1

/-- Tap or untap `id` through `PermanentEvent` in test fixtures. -/
def setTapped (g : Game) (id : ObjectId) (v : Bool) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let c := EventCause.gameRule .staticAbility
    if v then g.record (GameEvent.tapped g.turnNumber (g.snapshot o) (cause := c))
    else g.record (GameEvent.untapped g.turnNumber (g.snapshot o) false (cause := c))

/-- Set `id`'s marked damage through `DamageEvent` in test fixtures. -/
def setMarkedDamage (g : Game) (id : ObjectId) (amt : Nat) : Game :=
  let g := g.record (GameEvent.damageMarkedCleared g.turnNumber #[id]
    (cause := .turnBased .cleanupClear))
  if amt == 0 then g
  else g.record (GameEvent.damageMarked g.turnNumber id amt (cause := .gameRule .staticAbility))

/-- Turn `id` face down or face up through `PermanentEvent` in test fixtures. -/
def setFaceDown (g : Game) (id : ObjectId) (v : Bool) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let c := EventCause.gameRule .staticAbility
    if v then g.record (GameEvent.turnedFaceDown g.turnNumber (g.snapshot o) (cause := c))
    else g.record (GameEvent.turnedFaceUp g.turnNumber (g.snapshot o) (cause := c))

/-- Retain only `keep` (in bottom-to-top order) in `p`'s library via `ZoneEvent`. -/
def retainLibrary (g : Game) (p : PlayerId) (keep : Array ObjectId) : Game :=
  let g := ((g.player p).library.filter (!keep.contains ·)).foldl
    (fun acc id => acc.ceaseToExist id) g
  keep.foldl (fun acc id =>
    match acc.findObject? id with
    | some o =>
      let snap := acc.snapshot o
      acc.record (GameEvent.moved acc.turnNumber snap o.zone (.library p)
        (after := some { snap with zone := .library p })
        (libraryPosition := some .top)
        (cause := .gameRule .leavingZone))
    | none => acc) g

/-- Remove all cards from `p`'s library via `ZoneEvent.ceasedToExist`. -/
def emptyLibrary (g : Game) (p : PlayerId) : Game :=
  retainLibrary g p #[]

/-- Retain only `keep` in `p`'s hand via `ZoneEvent`. -/
def retainHand (g : Game) (p : PlayerId) (keep : Array ObjectId) : Game :=
  let g := ((g.player p).hand.filter (!keep.contains ·)).foldl
    (fun acc id => acc.ceaseToExist id) g
  keep.foldl (fun acc id =>
    match acc.findObject? id with
    | some o =>
      let snap := acc.snapshot o
      acc.record (GameEvent.moved acc.turnNumber snap o.zone (.hand p)
        (after := some { snap with zone := .hand p })
        (cause := .gameRule .leavingZone))
    | none => acc) g

/-- Remove all cards from `p`'s hand via `ZoneEvent.ceasedToExist`. -/
def emptyHand (g : Game) (p : PlayerId) : Game :=
  retainHand g p #[]

/-- Set `p`'s life total through `LifeEvent` in test fixtures. -/
def _root_.Mtg.Engine.Game.setLifeTotal (g : Game) (p : PlayerId) (life : Int) : Game :=
  let cur := (g.player p).life
  let c := EventCause.gameRule .staticAbility
  if life > cur then
    g.record (GameEvent.life g.turnNumber p (life - cur).toNat (gained := true) (cause := c))
  else if life < cur then
    g.record (GameEvent.life g.turnNumber p (cur - life).toNat (gained := false) (cause := c))
  else g

/-- Make `p` the monarch through `PlayerEvent.becameMonarch` in test fixtures. -/
def _root_.Mtg.Engine.Game.becomeMonarch (g : Game) (p : PlayerId) : Game :=
  let prev := (g.players.find? (·.isMonarch)).map (·.id)
  g.record (GameEvent.becameMonarch g.turnNumber p prev (cause := some (.gameRule .staticAbility)))

/-- Put `n` counters of `kind` on `p` through `PermanentEvent.counters` in test fixtures. -/
def _root_.Mtg.Engine.Game.addPlayerCounters (g : Game) (p : PlayerId) (kind : CounterKind) (n : Nat) : Game :=
  if n == 0 then g
  else
    g.record (GameEvent.rules g.turnNumber (.permanent (.counters (.player p) kind (.put n) none))
      (.gameRule .staticAbility))

/-- Put `card` onto the battlefield with explicit owner and controller. -/
def addPermanent (g : Game) (card : CardDef) (owner controller : PlayerId) : Game :=
  let status : Status :=
    { summoningSick := false
      counters := if card.entersWithIndestructibleCounter then #[(.indestructible, 1)] else #[] }
  insertObject g card owner .battlefield (some controller) status

/-- Put `card` onto the battlefield summoning-sick. -/
def addSickPermanent (g : Game) (card : CardDef) (owner controller : PlayerId) : Game :=
  let status : Status :=
    { summoningSick := true
      counters := if card.entersWithIndestructibleCounter then #[(.indestructible, 1)] else #[] }
  insertObject g card owner .battlefield (some controller) status

/-- Begin a new turn for `p` at `g.step` so `p`'s permanents lose summoning sickness (CR 302.6). -/
def readyControlledForTurn (g : Game) (p : PlayerId := g.activePlayer) : Game :=
  let st := g.step
  let g := g.record (GameEvent.turnBegan (g.turnNumber + 1) p false)
  g.record (GameEvent.stepBegan g.turnNumber st p)

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
  withMountain.changeControl o ⟨1⟩

/-- Nissa's permanent entered first; Chandra still has a later Forest. -/
@[irreducible, noinline] def mixedControllers : Game := addPermanent stolenMountain forest ⟨0⟩ ⟨0⟩

@[irreducible, noinline] def uncontrolledPermanent : Game :=
  insertObject (started.record (GameEvent.playerLost started.turnNumber ⟨0⟩ .conceded))
    mountain ⟨0⟩ .battlefield none { summoningSick := false }

@[irreducible, noinline] def withGoblin : Game := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
@[irreducible, noinline] def withElves : Game := addPermanent started llanowarElves ⟨0⟩ ⟨0⟩
@[irreducible, noinline] def withSpider : Game := addPermanent started giantSpider ⟨0⟩ ⟨0⟩

end Mtg.Engine.Tests
