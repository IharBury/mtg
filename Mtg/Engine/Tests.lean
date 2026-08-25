import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Game
import Mtg.Engine.Render

/-!
# Compile-time smoke tests for the engine.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Render

/-- 60-card constructed red fixture used only by engine tests. -/
def testRedDeck : Array CardDef :=
  copies 32 mountain ++
  copies 4 lightningBolt ++
  copies 4 shock ++
  copies 4 ragingGoblin ++
  copies 4 grayOgre ++
  copies 4 hillGiant ++
  copies 4 canyonMinotaur ++
  copies 4 mountain

/-- 60-card constructed green fixture used only by engine tests. -/
def testGreenDeck : Array CardDef :=
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

def drawnHands : Game :=
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

def started : Game := keepOpeningHands drawnHands 8

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

/-- First player skipped the draw step (CR 103.8a / 500.11), so after upkeep
the game proceeds to precombat main: no card is drawn and nobody received
priority during the skipped step. -/
def afterDraw : Game :=
  match Game.pass started ⟨0⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨1⟩ with
    | .error e => panic! e
    | .ok g2 => g2

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

#guard (changedZones started started).isEmpty
#guard (zoneObjectIds started (.hand ⟨0⟩)).size == 7
#guard (zoneObjectIds started (.library ⟨0⟩)).size == 53
#guard (zoneObjectIds started .stack).isEmpty
#guard zoneBlock started .stack == "zone stack (0): (empty)"
#guard zoneBlock started (.library ⟨0⟩) == "zone Chandra's library (53)"

/-- `true` iff `needle` occurs in `haystack`. -/
def mentions (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- First card of `p`'s hand; tests assume opening hands are non-empty. -/
def firstHandCard (g : Game) (p : PlayerId) : GameObject :=
  match (g.handObjects p)[0]? with
  | some o => o
  | none => panic! "expected a card in hand"

#guard canSeeZoneFaces none (.hand ⟨1⟩)
#guard canSeeZoneFaces (some ⟨0⟩) (.hand ⟨0⟩)
#guard !canSeeZoneFaces (some ⟨0⟩) (.hand ⟨1⟩)
#guard !canSeeZoneFaces none (.library ⟨0⟩)
#guard !canSeeZoneFaces (some ⟨0⟩) (.library ⟨0⟩)
#guard canSeeZoneFaces (some ⟨0⟩) .battlefield
#guard canSeeZoneFaces (some ⟨0⟩) (.graveyard ⟨1⟩)

#guard zoneBlock started (.library ⟨0⟩) (some ⟨0⟩) == "zone Chandra's library (53)"
#guard zoneBlock started (.hand ⟨1⟩) (some ⟨0⟩) == "zone Nissa's hand (7)"
#guard mentions (zoneBlock started (.hand ⟨0⟩) (some ⟨0⟩)) (firstHandCard started ⟨0⟩).name
#guard !mentions (zoneBlock started (.hand ⟨1⟩) (some ⟨0⟩)) (firstHandCard started ⟨1⟩).name
#guard mentions (zoneBlock started (.hand ⟨1⟩)) (firstHandCard started ⟨1⟩).name

#guard mentions (playerBlock started (started.player ⟨1⟩) (some ⟨0⟩)) "Hand (7):"
#guard mentions (playerBlock started (started.player ⟨1⟩) (some ⟨0⟩)) "(hidden)"
#guard !mentions (playerBlock started (started.player ⟨1⟩) (some ⟨0⟩))
  (firstHandCard started ⟨1⟩).name
#guard mentions (playerBlock started (started.player ⟨0⟩) (some ⟨0⟩))
  (firstHandCard started ⟨0⟩).name

#guard mentions (snapshot started (some ⟨0⟩)) "Chandra's view"
#guard !mentions (snapshot started) "view"
#guard mentions (snapshot started (some ⟨0⟩)) (firstHandCard started ⟨0⟩).name
#guard !mentions (snapshot started (some ⟨0⟩)) (firstHandCard started ⟨1⟩).name
#guard mentions (snapshot started) (firstHandCard started ⟨1⟩).name

#guard redactLogLine started ⟨0⟩ "Nissa draws Forest" == "Nissa draws a card"
#guard redactLogLine started ⟨0⟩ "Chandra draws Mountain" == "Chandra draws Mountain"
#guard redactLogLine started ⟨0⟩ "Nissa puts Forest on the bottom of their library" ==
  "Nissa puts a card on the bottom of their library"
#guard redactLogLine started ⟨0⟩ "Nissa puts Forest onto the battlefield tapped" ==
  "Nissa puts Forest onto the battlefield tapped"
#guard (newLog started 0 (some ⟨0⟩)).any (· == "Nissa draws a card")
#guard !(newLog started 0 (some ⟨0⟩)).any (fun s =>
  s.startsWith "Nissa draws " && s != "Nissa draws a card")
#guard (newLog started 0).any (fun s =>
  s.startsWith "Nissa draws " && s != "Nissa draws a card")

def drawnOnce : Game := Game.draw started ⟨0⟩

#guard (zoneObjectIds drawnOnce (.hand ⟨0⟩)).size == 8
#guard (zoneObjectIds drawnOnce (.library ⟨0⟩)).size == 52
#guard (changedZones started drawnOnce).contains (.hand ⟨0⟩)
#guard (changedZones started drawnOnce).contains (.library ⟨0⟩)
#guard !(changedZones started drawnOnce).contains .battlefield
#guard !(changedZones started drawnOnce).contains .stack
#guard zoneBlock drawnOnce (.hand ⟨1⟩) (some ⟨0⟩) == "zone Nissa's hand (7)"
#guard mentions (zoneBlock drawnOnce (.hand ⟨0⟩) (some ⟨0⟩)) (firstHandCard drawnOnce ⟨0⟩).name
#guard (zoneBlock drawnOnce (.hand ⟨0⟩) (some ⟨0⟩)).startsWith "zone Chandra's hand (8):"

/-- Put `card` onto the battlefield with explicit owner and controller. -/
def addPermanent (g : Game) (card : CardDef) (owner controller : PlayerId) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := owner
    controller := some controller
    zone := .battlefield
    status := { summoningSick := false }
    timestamp := ts
  }
  { g with objects := g.objects.push obj }

/-- Drop a basic land onto the battlefield without using the play-land action. -/
def addUntappedLand (g : Game) (card : CardDef) : Game :=
  addPermanent g card g.activePlayer g.activePlayer

def withMountain : Game := addUntappedLand started mountain

def tappedMountain : Game :=
  match (withMountain.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => panic! "expected a land on the battlefield"
  | some o =>
    match o.printed.manaAbilities[0]? with
    | none => panic! s!"{o.name} has no mana ability"
    | some m =>
      match withMountain.tapForMana ⟨0⟩ o.id m with
      | .ok g => g
      | .error e => panic! e

-- Occupants are unchanged, but the land is now tapped, so the battlefield
-- must reprint (the demo shows the land as tapped).
#guard (zoneObjectIds withMountain .battlefield) == (zoneObjectIds tappedMountain .battlefield)
#guard battlefieldView withMountain != battlefieldView tappedMountain
#guard (zoneBlock withMountain .battlefield) != (zoneBlock tappedMountain .battlefield)
#guard (changedZones withMountain tappedMountain).contains .battlefield
#guard (changedZones withMountain withMountain).isEmpty
#guard tappedMountain.battlefield.any (·.status.tapped)
#guard !(withMountain.battlefield.any (·.status.tapped))
#guard (tappedMountain.player ⟨0⟩).manaPool != (withMountain.player ⟨0⟩).manaPool
#guard (changedManaPools withMountain tappedMountain).size == 1
#guard (changedManaPools withMountain tappedMountain).any (fun pl =>
  pl.id == ⟨0⟩ && !pl.manaPool.isEmpty)
#guard manaLine (tappedMountain.player ⟨0⟩) == "Chandra — mana {R}×1"

/-- Battlefield rendering names owner and controller (CR 108.3, 110.2). -/
def lastPermanent (g : Game) : GameObject :=
  match g.battlefield.back? with
  | some o => o
  | none => panic! "expected a permanent on the battlefield"

def mountainLine (g : Game) : String :=
  objectLine g (lastPermanent g)

#guard mountainLine withMountain ==
  s!"{(lastPermanent withMountain).id} Mountain \{T}: Add \{R}. (owned by Chandra, controlled by Chandra)"
#guard mentions (mountainLine withMountain) "{T}: Add {R}"
-- Ungrouped lines still name owner and controller. Grouped battlefield
-- listings omit them when they match the controller heading.
#guard !mentions (zoneBlock withMountain .battlefield) "owned by"
#guard !mentions (zoneBlock withMountain .battlefield) "controlled by"
#guard !mentions (snapshot withMountain) "owned by"
#guard !mentions (snapshot withMountain) "controlled by"
#guard mentions (mountainLine tappedMountain) "(tapped)"
#guard mentions (mountainLine tappedMountain)
  "(owned by Chandra, controlled by Chandra)"

/-- Untap is a turn-based action (CR 502.2): occupants stay put, but the land
is no longer tapped, so the demo reprints the battlefield. -/
def afterUntapStep : Game := tappedMountain.beginStep .untap

#guard (zoneObjectIds tappedMountain .battlefield) == (zoneObjectIds afterUntapStep .battlefield)
#guard battlefieldView tappedMountain != battlefieldView afterUntapStep
#guard (zoneBlock tappedMountain .battlefield) != (zoneBlock afterUntapStep .battlefield)
#guard (changedZones tappedMountain afterUntapStep).contains .battlefield
#guard afterUntapStep.step == .untap
#guard !(afterUntapStep.battlefield.any (·.status.tapped))
#guard !mentions (mountainLine afterUntapStep) "(tapped)"
#guard afterUntapStep.log.any (fun s => mentions s "untaps Mountain")

/-- A permanent Chandra owns and Nissa controls is listed on Nissa's side. -/
def stolenMountain : Game := addPermanent started mountain ⟨0⟩ ⟨1⟩

#guard mountainLine stolenMountain ==
  s!"{(lastPermanent stolenMountain).id} Mountain \{T}: Add \{R}. (owned by Chandra, controlled by Nissa)"
#guard (stolenMountain.permanentsOf ⟨1⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard !(stolenMountain.permanentsOf ⟨0⟩).any (·.id == (lastPermanent stolenMountain).id)
-- Grouped under Nissa: owner differs, so it is printed; controller matches.
#guard mentions (playerBlock stolenMountain (stolenMountain.player ⟨1⟩))
  "(owned by Chandra)"
#guard !mentions (playerBlock stolenMountain (stolenMountain.player ⟨1⟩))
  "controlled by"
#guard mentions (playerBlock stolenMountain (stolenMountain.player ⟨0⟩)) "  (none)"
#guard mentions (zoneBlock stolenMountain .battlefield)
  "(owned by Chandra)"
#guard !mentions (zoneBlock stolenMountain .battlefield) "controlled by"
#guard mentions (snapshot stolenMountain)
  "(owned by Chandra)"
#guard !mentions (snapshot stolenMountain) "controlled by"

/-- Changing control without moving the permanent still reprints the battlefield. -/
def afterControlChange : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := some ⟨1⟩ }

#guard (zoneObjectIds withMountain .battlefield) == (zoneObjectIds afterControlChange .battlefield)
#guard battlefieldView withMountain != battlefieldView afterControlChange
#guard (changedZones withMountain afterControlChange).contains .battlefield
#guard mentions (objectLine afterControlChange (lastPermanent afterControlChange))
  "(owned by Chandra, controlled by Nissa)"
#guard mentions (objectLine afterControlChange (lastPermanent afterControlChange)
  (some (some ⟨1⟩))) "(owned by Chandra)"
#guard !mentions (objectLine afterControlChange (lastPermanent afterControlChange)
  (some (some ⟨1⟩))) "controlled by"

/- The shared battlefield listing is grouped by controller (CR 110.2). -/
#guard zoneBlock started .battlefield == "zone battlefield (0): (empty)"

#guard
  let m := lastPermanent withMountain
  zoneBlock withMountain .battlefield ==
    s!"zone battlefield (1):\n  Chandra:\n    {objectLine withMountain m (some (some ⟨0⟩))}"

#guard
  let m := lastPermanent stolenMountain
  zoneBlock stolenMountain .battlefield ==
    s!"zone battlefield (1):\n  Nissa:\n    {objectLine stolenMountain m (some (some ⟨1⟩))}"

/-- Nissa's permanent entered first; the listing still groups Chandra before Nissa. -/
def mixedControllers : Game := addPermanent stolenMountain forest ⟨0⟩ ⟨0⟩

#guard
  let forestP := (mixedControllers.permanentsOf ⟨0⟩)[0]!
  let mountainP := (mixedControllers.permanentsOf ⟨1⟩)[0]!
  forestP.name == "Forest" && mountainP.name == "Mountain" &&
    zoneBlock mixedControllers .battlefield ==
      s!"zone battlefield (2):\n  Chandra:\n    {objectLine mixedControllers forestP (some (some ⟨0⟩))}\n  Nissa:\n    {objectLine mixedControllers mountainP (some (some ⟨1⟩))}"

def uncontrolledPermanent : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := none }

#guard
  let m := lastPermanent uncontrolledPermanent
  zoneBlock uncontrolledPermanent .battlefield ==
    s!"zone battlefield (1):\n  (no controller):\n    {objectLine uncontrolledPermanent m (some none)}"

-- Owner still prints under the no-controller heading; "no controller" does not
-- repeat on the permanent line.
#guard mentions (zoneBlock uncontrolledPermanent .battlefield) "(owned by Chandra)"
#guard !mentions (objectLine uncontrolledPermanent (lastPermanent uncontrolledPermanent)
  (some none)) "no controller"
#guard !mentions (objectLine withMountain (lastPermanent withMountain) (some (some ⟨0⟩)))
  "owned by"
#guard !mentions (objectLine mixedControllers
  ((mixedControllers.permanentsOf ⟨0⟩)[0]!) (some (some ⟨0⟩))) "owned by"
#guard mentions (objectLine mixedControllers
  ((mixedControllers.permanentsOf ⟨1⟩)[0]!) (some (some ⟨1⟩))) "(owned by Chandra)"

/- Hands, battlefield, and other zones print keywords and abilities. -/
#guard mentions ragingGoblin.summary "haste"
#guard mentions giantSpider.summary "reach"
#guard mentions llanowarElves.summary "{T}: Add {G}"
#guard mentions lightningBolt.summary "deals 3 damage"
#guard mentions mountain.summary "{T}: Add {R}"
#guard mentions wayfarersBauble.summary "Search your library"
#guard mentions attercop.summary "reach"
#guard mentions attercop.summary "deathtouch"
#guard mentions attercop.summary "Landfall"
#guard mentions landrovalHorizonWitness.summary "flying"
#guard mentions landrovalHorizonWitness.summary "Whenever two or more creatures"
#guard mentions soldierOfTheGreyHost.summary "Flash"
#guard mentions soldierOfTheGreyHost.summary "flying"
#guard mentions roguesPassage.summary "{T}: Add {C}"
#guard mentions roguesPassage.summary "can't be blocked"

/- Structured abilities still print when Oracle text is absent. -/
#guard
  let c : CardDef := {
    name := "Silent Elves"
    types := #[.creature]
    power := some 1
    toughness := some 1
    tapAddMana := #[.colored .green]
  }
  mentions c.abilitiesText "{T}: Add {G}" &&
    mentions c.summary "{T}: Add {G}"

def withGoblin : Game := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
def withElves : Game := addPermanent started llanowarElves ⟨0⟩ ⟨0⟩
def withSpider : Game := addPermanent started giantSpider ⟨0⟩ ⟨0⟩
def withAttercop : Game := addPermanent started attercop ⟨0⟩ ⟨0⟩

#guard mentions (objectLine withGoblin (lastPermanent withGoblin)) "haste"
#guard mentions (playerBlock withGoblin (withGoblin.player ⟨0⟩)) "haste"
#guard mentions (objectLine withElves (lastPermanent withElves)) "{T}: Add {G}"
#guard mentions (objectLine withSpider (lastPermanent withSpider)) "reach"
#guard mentions (objectLine withAttercop (lastPermanent withAttercop)) "deathtouch"
#guard mentions (objectLine withAttercop (lastPermanent withAttercop)) "Landfall"
#guard mentions (zoneLine withAttercop .battlefield (lastPermanent withAttercop).id)
  "Landfall"

/-- Apply the idle action for whoever must act: empty combat declarations or pass. -/
def applyIdle (g : Game) : Game :=
  match g.pending, g.actor with
  | .declareAttackers, some p =>
    match g.apply p (.declareAttackers #[]) with
    | .ok g' => g'
    | .error e => panic! e
  | .declareBlockers, some p =>
    match g.apply p (.declareBlockers #[]) with
    | .ok g' => g'
    | .error e => panic! e
  | .declareMulligan _, some p =>
    match g.apply p .keep with
    | .ok g' => g'
    | .error e => panic! e
  | .putOnBottom _ n, some p =>
    match g.apply p (.putOnBottom ((g.player p).hand.extract 0 n)) with
    | .ok g' => g'
    | .error e => panic! e
  | _, some p =>
    match g.apply p .pass with
    | .ok g' => g'
    | .error e => panic! e
  | _, none => panic! s!"no actor at {g.step}"

/-- Advance by idle actions until `g` is in `st` with no pending choice. -/
def skipTo (g : Game) (st : Step) : Nat → Game
  | 0 => panic! s!"skipTo fuel exhausted at {g.step}"
  | n + 1 =>
    if g.over then panic! "game over while skipping"
    else if g.step == st && g.pending == .none then g
    else skipTo (applyIdle g) st n

def passBoth (g : Game) : Game :=
  applyIdle (applyIdle g)

def atEndStep : Game := skipTo started .end 80

/-- A 0/0 creature kept alive only by an until-end-of-turn pump. -/
def zeroZero : CardDef := {
  name := "Zero/Zero"
  types := #[.creature]
  power := some 0
  toughness := some 0
}

def addPumpedCreature (g : Game) (card : CardDef) (pumpP pumpT : Int) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := g.activePlayer
    controller := some g.activePlayer
    zone := .battlefield
    status := { pumpPower := pumpP, pumpToughness := pumpT, summoningSick := false }
    timestamp := ts
  }
  { g with objects := g.objects.push obj }

/-- CR 514.3: after both players pass in the end step, cleanup does not grant
priority, so the next player's upkeep begins immediately. -/
def afterSilentCleanup : Game := passBoth atEndStep

#guard atEndStep.step == .end
#guard atEndStep.turnNumber == 1
#guard atEndStep.activePlayer == ⟨0⟩
#guard afterSilentCleanup.turnNumber == 2
#guard afterSilentCleanup.step == .upkeep
#guard afterSilentCleanup.activePlayer == ⟨1⟩
#guard !afterSilentCleanup.cleanupGivesPriority
#guard !afterSilentCleanup.log.any (· == "Players receive priority during cleanup (CR 514.3a)")

/-- Opponent's untap (CR 502.2) does not untap Chandra's land. -/
def nissaTurn2 : Game := passBoth (skipTo tappedMountain .end 80)

#guard nissaTurn2.turnNumber == 2
#guard nissaTurn2.activePlayer == ⟨1⟩
#guard nissaTurn2.step == .upkeep
#guard nissaTurn2.battlefield.any (·.status.tapped)
#guard !nissaTurn2.skipsFirstDraw

/-- The second player does draw on their first turn and receives priority
during the draw step (CR 103.8a applies only to the starting player). -/
def nissaDraw : Game := passBoth nissaTurn2

#guard nissaDraw.step == .draw
#guard nissaDraw.playersReceivePriority
#guard nissaDraw.hasPriority ⟨1⟩
#guard nissaDraw.actor == some ⟨1⟩
#guard (nissaDraw.player ⟨1⟩).hand.size == 8
#guard (nissaDraw.player ⟨0⟩).hand.size == 7
#guard !nissaDraw.asSorcery? ⟨1⟩
#guard nissaDraw.log.any (fun s => mentions s "Nissa draws")

/-- The pass that ends Nissa's turn also runs Chandra's untap. Occupants are
unchanged, but the land is now untapped, so the demo reprints the battlefield. -/
def nissaEnd : Game := skipTo nissaTurn2 .end 80
def chandraTurn3 : Game := passBoth nissaEnd

#guard nissaEnd.turnNumber == 2
#guard nissaEnd.step == .end
#guard nissaEnd.battlefield.any (·.status.tapped)
#guard chandraTurn3.turnNumber == 3
#guard chandraTurn3.activePlayer == ⟨0⟩
#guard chandraTurn3.step == .upkeep
#guard !(chandraTurn3.battlefield.any (·.status.tapped))
#guard (zoneObjectIds nissaEnd .battlefield) == (zoneObjectIds chandraTurn3 .battlefield)
#guard battlefieldView nissaEnd != battlefieldView chandraTurn3
#guard (changedZones nissaEnd chandraTurn3).contains .battlefield
#guard mentions (zoneBlock nissaEnd .battlefield) "(tapped)"
#guard !mentions (zoneBlock chandraTurn3 .battlefield) "(tapped)"
#guard chandraTurn3.log.any (fun s => mentions s "untaps Mountain")

/-- CR 514.3a: ending a pump that was keeping a 0/0 alive causes a state-based
action, so the active player receives priority still in cleanup. -/
def cleanupWithSBA : Game :=
  passBoth (addPumpedCreature atEndStep zeroZero 1 1)

#guard cleanupWithSBA.step == .cleanup
#guard cleanupWithSBA.cleanupGivesPriority
#guard cleanupWithSBA.playersReceivePriority
#guard cleanupWithSBA.actor == some ⟨0⟩
#guard cleanupWithSBA.hasPriority ⟨0⟩
#guard (cleanupWithSBA.battlefield.filter (fun o => o.name == "Zero/Zero")).isEmpty
#guard cleanupWithSBA.log.any (· == "Players receive priority during cleanup (CR 514.3a)")

/-- After the 514.3a priority window, another cleanup begins; with no further
state-based actions it ends the turn (CR 514.3a last sentence). -/
def afterExceptionCleanup : Game := passBoth cleanupWithSBA

#guard afterExceptionCleanup.turnNumber == 2
#guard afterExceptionCleanup.step == .upkeep
#guard afterExceptionCleanup.activePlayer == ⟨1⟩
#guard !afterExceptionCleanup.cleanupGivesPriority

#guard (changedLifeTotals started started).isEmpty
#guard (changedLifeTotals started afterDraw).isEmpty
#guard lifeLine (started.player ⟨0⟩) == "Chandra — life 20"
#guard lifeLine (started.player ⟨1⟩) == "Nissa — life 20"

/-- Lightning Bolt to a player (CR 120.3a) changes that player's life total. -/
def afterBolt : Game :=
  started.applyEffect ⟨0⟩ (.dealDamage 3) #[Target.player ⟨1⟩]

#guard (started.player ⟨1⟩).life == 20
#guard (afterBolt.player ⟨1⟩).life == 17
#guard (afterBolt.player ⟨0⟩).life == 20
#guard (changedLifeTotals started afterBolt).size == 1
#guard (changedLifeTotals started afterBolt).any (fun pl => pl.id == ⟨1⟩ && pl.life == 17)
#guard lifeLine (afterBolt.player ⟨1⟩) == "Nissa — life 17"
#guard mentions (playerBlock afterBolt (afterBolt.player ⟨1⟩)) "life 17"
#guard afterBolt.log.any (fun s => mentions s "17 life")

/-- Unblocked combat damage (CR 510.1a / 120.3a) also changes life. -/
def attackingGoblin : Game :=
  let g := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
  let o := lastPermanent g
  g.setObject { o with status := { o.status with attacking := true } }

def afterCombatDamage : Game := attackingGoblin.combatDamage

#guard ragingGoblin.power == some 1
#guard (attackingGoblin.player ⟨1⟩).life == 20
#guard (afterCombatDamage.player ⟨1⟩).life == 19
#guard (changedLifeTotals attackingGoblin afterCombatDamage).size == 1
#guard (changedLifeTotals attackingGoblin afterCombatDamage).any (fun pl =>
  pl.id == ⟨1⟩ && pl.life == 19)
#guard lifeLine (afterCombatDamage.player ⟨1⟩) == "Nissa — life 19"
#guard afterCombatDamage.log.any (fun s => mentions s "19 life")
#guard (changedZones attackingGoblin afterCombatDamage).isEmpty

/-- Put `card` into `p`'s hand without drawing. -/
def addToHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := p
    zone := .hand p
    timestamp := ts
  }
  { g with objects := g.objects.push obj }.modifyPlayer p (fun pl =>
    { pl with hand := pl.hand.push id })

/-- Put `card` on top of `p`'s library (the back of the library array). -/
def addToLibraryTop (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id := id
    printed := card
    owner := p
    zone := .library p
    timestamp := ts
  }
  { g with objects := g.objects.push obj }.modifyPlayer p (fun pl =>
    { pl with library := pl.library.push id })

def mustApply (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! e

def handCardNamed (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match (g.handObjects p).find? (fun o => o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} in hand"

/-- CR 601.2g: a player may begin casting without mana in their pool, then
activate mana abilities, then pay. -/
def boltSetup : Game :=
  addToHand (addUntappedLand started mountain) lightningBolt ⟨0⟩

def boltInHand : GameObject :=
  handCardNamed boltSetup ⟨0⟩ "Lightning Bolt"

def boltMountain : GameObject :=
  lastPermanent boltSetup

#guard (boltSetup.player ⟨0⟩).manaPool.isEmpty
#guard !(boltSetup.player ⟨0⟩).manaPool.canPay lightningBolt.manaCost
#guard (boltSetup.availableMana ⟨0⟩).canPay lightningBolt.manaCost
#guard boltSetup.canCast ⟨0⟩ boltInHand
#guard boltSetup.hasPriority ⟨0⟩

/-- The agent proposes a spell instead of tapping first. -/
def agentBeginsCast : Bool :=
  match Agent.choose boltSetup ⟨0⟩ with
  | some (.cast _ _) => true
  | _ => false

#guard agentBeginsCast

def proposedBolt : Game :=
  mustApply boltSetup ⟨0⟩ (.cast boltInHand.id (some (Target.player ⟨1⟩)))

#guard proposedBolt.pending == .activateManaAbilities ⟨0⟩
#guard proposedBolt.proposedSpell.isSome
#guard !proposedBolt.stack.isEmpty
#guard !(proposedBolt.player ⟨0⟩).hand.contains boltInHand.id
#guard (proposedBolt.player ⟨0⟩).manaPool.isEmpty
#guard !proposedBolt.hasPriority ⟨0⟩
#guard proposedBolt.canActivateManaAbility ⟨0⟩
#guard !proposedBolt.canActivateManaAbility ⟨1⟩
#guard proposedBolt.actor == some ⟨0⟩
#guard proposedBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")
#guard proposedBolt.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard mentions (header proposedBolt) "activate mana abilities (CR 601.2g)"
#guard (changedZones boltSetup proposedBolt).contains (.hand ⟨0⟩)
#guard (changedZones boltSetup proposedBolt).contains .stack

/-- Opponent cannot activate mana abilities during the caster's 601.2g window. -/
def nissaTapDenied : Bool :=
  match proposedBolt.tapForMana ⟨1⟩ boltMountain.id (.colored .red) with
  | .error _ => true
  | .ok _ => false

#guard nissaTapDenied

def agentTapsInWindow : Bool :=
  match Agent.choose proposedBolt ⟨0⟩ with
  | some (.tapForMana id _) => id == boltMountain.id
  | _ => false

#guard agentTapsInWindow

def tappedForBolt : Game :=
  mustApply proposedBolt ⟨0⟩ (.tapForMana boltMountain.id (.colored .red))

#guard (tappedForBolt.player ⟨0⟩).manaPool.canPay lightningBolt.manaCost
#guard tappedForBolt.pending == .activateManaAbilities ⟨0⟩
#guard tappedForBolt.battlefield.any (·.status.tapped)

def agentPaysInWindow : Bool :=
  match Agent.choose tappedForBolt ⟨0⟩ with
  | some .pay => true
  | _ => false

#guard agentPaysInWindow

/-- Passing priority is not how the 601.2h payment is made. -/
def passDuringWindowDenied : Bool :=
  match proposedBolt.apply ⟨0⟩ .pass with
  | .error _ => true
  | .ok _ => false

#guard passDuringWindowDenied

def paidBolt : Game :=
  mustApply tappedForBolt ⟨0⟩ .pay

#guard paidBolt.pending == .none
#guard paidBolt.proposedSpell.isNone
#guard paidBolt.hasPriority ⟨0⟩
#guard (paidBolt.player ⟨0⟩).manaPool.isEmpty
#guard !paidBolt.stack.isEmpty
#guard paidBolt.log.any (fun s => mentions s "casts Lightning Bolt")
#guard !mentions (header paidBolt) "activate mana abilities"

/-- Paying without enough mana reverses the cast (CR 601.2 / 733.1). -/
def reversedBolt : Game :=
  mustApply proposedBolt ⟨0⟩ .pay

#guard reversedBolt.pending == .none
#guard reversedBolt.proposedSpell.isNone
#guard reversedBolt.stack.isEmpty
#guard reversedBolt.hasPriority ⟨0⟩
#guard (reversedBolt.handObjects ⟨0⟩).any (fun o => o.name == "Lightning Bolt")
#guard !(reversedBolt.battlefield.any (·.status.tapped))
#guard (reversedBolt.player ⟨0⟩).manaPool.isEmpty
#guard reversedBolt.log.any (fun s => mentions s "the casting is reversed")

/-- Mana abilities activated at 601.2g are reversed with the illegal cast. -/
def ogreSetup : Game :=
  addToHand (addUntappedLand (skipTo started .precombatMain 80) mountain) grayOgre ⟨0⟩

def proposedOgre : Game :=
  mustApply ogreSetup ⟨0⟩ (.cast (handCardNamed ogreSetup ⟨0⟩ "Gray Ogre").id none)

def tappedForOgre : Game :=
  mustApply proposedOgre ⟨0⟩ (.tapForMana (lastPermanent ogreSetup).id (.colored .red))

#guard tappedForOgre.pending == .activateManaAbilities ⟨0⟩
#guard (tappedForOgre.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .red)
#guard !(tappedForOgre.player ⟨0⟩).manaPool.canPay grayOgre.manaCost
#guard tappedForOgre.battlefield.any (·.status.tapped)

def reversedOgre : Game :=
  mustApply tappedForOgre ⟨0⟩ .pay

#guard reversedOgre.stack.isEmpty
#guard reversedOgre.hasPriority ⟨0⟩
#guard !(reversedOgre.battlefield.any (·.status.tapped))
#guard (reversedOgre.player ⟨0⟩).manaPool.isEmpty
#guard (reversedOgre.handObjects ⟨0⟩).any (fun o => o.name == "Gray Ogre")
#guard reversedOgre.log.any (fun s => mentions s "the casting is reversed")

/-- A resolved Lightning Bolt still changes life after the 601.2g window. -/
def resolvedBolt : Game :=
  mustApply (mustApply paidBolt ⟨0⟩ .pass) ⟨1⟩ .pass

#guard resolvedBolt.stack.isEmpty
#guard (resolvedBolt.player ⟨1⟩).life == 17
#guard resolvedBolt.log.any (fun s => mentions s "casts Lightning Bolt")

-- The heuristic still plays, and it activates mana abilities during 601.2g.
#guard played.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard played.log.any (fun s => mentions s "begins casting")

/-- Two ready creatures: declaring a subset of attackers leaves the rest
untapped and not attacking. -/
def twoReadyAttackers : Game :=
  addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

def readyToDeclareAttackers : Game :=
  passBoth (skipTo twoReadyAttackers .beginningOfCombat 80)

def namedPermanent (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (fun o => o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} on the battlefield"

#guard readyToDeclareAttackers.step == .declareAttackers
#guard readyToDeclareAttackers.pending == .declareAttackers
#guard (readyToDeclareAttackers.battlefield.filter (readyToDeclareAttackers.canAttack)).size == 2

def onlyBearsAttack : Game :=
  match readyToDeclareAttackers.apply ⟨0⟩
      (.declareAttackers #[(namedPermanent readyToDeclareAttackers "Grizzly Bears").id]) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.attacking
#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.tapped
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.attacking
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.tapped
#guard onlyBearsAttack.log.any (fun s => mentions s "attacks with Grizzly Bears")
#guard !onlyBearsAttack.log.any (fun s => mentions s "attacks with Gray Ogre")

/-- Declaring both creatures still works; the demo's bare `attack` uses this. -/
def bothAttack : Game :=
  let ids := readyToDeclareAttackers.battlefield.filter (readyToDeclareAttackers.canAttack) |>.map (·.id)
  match readyToDeclareAttackers.apply ⟨0⟩ (.declareAttackers ids) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent bothAttack "Grizzly Bears").status.attacking
#guard (namedPermanent bothAttack "Gray Ogre").status.attacking

/-- Chandra's Gray Ogre attacks; Nissa has Grizzly Bears to block. -/
def ogreVsBears : Game :=
  addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def ogreDeclaredAttacker : Game :=
  let g := passBoth (skipTo ogreVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])

def readyToDeclareBlockers : Game :=
  passBoth ogreDeclaredAttacker

#guard readyToDeclareBlockers.step == .declareBlockers
#guard readyToDeclareBlockers.pending == .declareBlockers
#guard readyToDeclareBlockers.actor == some ⟨1⟩
#guard (namedPermanent readyToDeclareBlockers "Gray Ogre").status.attacking
#guard (namedPermanent readyToDeclareBlockers "Grizzly Bears").status.blocking.isNone

def bearsBlockOgre : Game :=
  let g := readyToDeclareBlockers
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent bearsBlockOgre "Grizzly Bears").status.blocking ==
  some (namedPermanent bearsBlockOgre "Gray Ogre").id
#guard bearsBlockOgre.log.any (fun s => mentions s "Grizzly Bears blocks Gray Ogre")
#guard bearsBlockOgre.pending == .none

-- The demo names the attacker a blocker is assigned to (CR 509.1a).
#guard
  let g := bearsBlockOgre
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  objectLine g bears ==
    s!"{bears.id} Grizzly Bears {bears.power}/{bears.toughness} (owned by Nissa, controlled by Nissa) *blocking {ogre.id} Gray Ogre*" &&
  mentions (playerBlock g (g.player ⟨1⟩)) s!"*blocking {ogre.id} Gray Ogre*" &&
  mentions (zoneBlock g .battlefield) s!"*blocking {ogre.id} Gray Ogre*" &&
  mentions (objectLine g ogre) "*attacking*"
#guard !mentions
  (objectLine readyToDeclareBlockers (namedPermanent readyToDeclareBlockers "Grizzly Bears"))
  "*blocking"

/-- Blocking sends combat damage to the creature, not the defending player. -/
def afterBlockedDamage : Game := passBoth bearsBlockOgre

#guard (afterBlockedDamage.player ⟨1⟩).life == 20
#guard afterBlockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Grizzly Bears")
#guard afterBlockedDamage.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Gray Ogre")
#guard !afterBlockedDamage.log.any (fun s =>
  mentions s "deals 2 combat damage to Nissa")

def afterUnblockedDamage : Game :=
  passBoth (mustApply readyToDeclareBlockers ⟨1⟩ (.declareBlockers #[]))

#guard (afterUnblockedDamage.player ⟨1⟩).life == 18
#guard afterUnblockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")

#guard (changedManaPools started started).isEmpty
#guard (changedManaPools started afterDraw).isEmpty
#guard manaLine (started.player ⟨0⟩) == "Chandra — mana {}"
#guard manaLine (started.player ⟨1⟩) == "Nissa — mana {}"
#guard mentions (playerBlock tappedMountain (tappedMountain.player ⟨0⟩)) "mana {R}×1"

-- Paying a mana cost (CR 601.2h) spends the pool; the demo reprints the new
-- contents.
#guard (proposedBolt.player ⟨0⟩).manaPool.isEmpty
#guard (changedManaPools proposedBolt tappedForBolt).size == 1
#guard manaLine (tappedForBolt.player ⟨0⟩) == "Chandra — mana {R}×1"
#guard (changedManaPools tappedForBolt paidBolt).size == 1
#guard (changedManaPools tappedForBolt paidBolt).any (fun pl =>
  pl.id == ⟨0⟩ && pl.manaPool.isEmpty)
#guard manaLine (paidBolt.player ⟨0⟩) == "Chandra — mana {}"

/-- Unused mana is emptied as a turn-based action (CR 500.4). -/
def emptiedPool : Game := tappedMountain.emptyManaPools

#guard (emptiedPool.player ⟨0⟩).manaPool.isEmpty
#guard (changedManaPools tappedMountain emptiedPool).size == 1
#guard (changedManaPools tappedMountain emptiedPool).any (fun pl =>
  pl.id == ⟨0⟩ && pl.manaPool.isEmpty)
#guard manaLine (emptiedPool.player ⟨0⟩) == "Chandra — mana {}"
#guard emptiedPool.log.any (fun s => mentions s "empties mana pool")

/-- CR 103.5: the starting player declares first; the mulligan is taken only
after every remaining player has declared. -/
def afterChandraDeclaresMulligan : Game :=
  mustApply drawnHands ⟨0⟩ .takeMulligan

#guard afterChandraDeclaresMulligan.pending == .declareMulligan ⟨1⟩
#guard afterChandraDeclaresMulligan.actor == some ⟨1⟩
#guard (afterChandraDeclaresMulligan.player ⟨0⟩).hand == (drawnHands.player ⟨0⟩).hand
#guard (afterChandraDeclaresMulligan.player ⟨0⟩).mulligansTaken == 0
#guard afterChandraDeclaresMulligan.willMulligan == #[⟨0⟩]
#guard afterChandraDeclaresMulligan.log.any (fun s => mentions s "will take a mulligan")
#guard !afterChandraDeclaresMulligan.log.any (fun s => mentions s "takes a mulligan (")

/-- Nissa keeps; then Chandra's declared mulligan is taken (CR 103.5). -/
def afterChandraMulligan : Game :=
  mustApply afterChandraDeclaresMulligan ⟨1⟩ .keep

#guard afterChandraMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard afterChandraMulligan.actor == some ⟨0⟩
#guard (afterChandraMulligan.player ⟨0⟩).hand.size == 7
#guard (afterChandraMulligan.player ⟨0⟩).mulligansTaken == 1
#guard (afterChandraMulligan.player ⟨0⟩).library.size == 53
#guard (afterChandraMulligan.player ⟨1⟩).keptOpeningHand
#guard (afterChandraMulligan.player ⟨1⟩).hand == (drawnHands.player ⟨1⟩).hand
#guard afterChandraMulligan.log.any (fun s => mentions s "takes a mulligan")
#guard afterChandraMulligan.log.any (fun s => mentions s "at the same time")
#guard mentions (header afterChandraMulligan) "on the bottom"

def chandraBottomCard : GameObject :=
  match (afterChandraMulligan.handObjects ⟨0⟩)[0]? with
  | some o => o
  | none => panic! "expected a card to put on the bottom"

def afterChandraBottoms : Game :=
  mustApply afterChandraMulligan ⟨0⟩ (.putOnBottom #[chandraBottomCard.id])

#guard (afterChandraBottoms.player ⟨0⟩).hand.size == 6
#guard (afterChandraBottoms.player ⟨0⟩).library.size == 54
#guard afterChandraBottoms.pending == .declareMulligan ⟨0⟩
#guard (afterChandraBottoms.player ⟨1⟩).keptOpeningHand
#guard !(afterChandraBottoms.player ⟨0⟩).keptOpeningHand
#guard (afterChandraBottoms.object! (afterChandraBottoms.player ⟨0⟩).library[0]!).name ==
  chandraBottomCard.name
#guard afterChandraBottoms.log.any (fun s => mentions s "on the bottom of their library")
#guard (changedZones afterChandraMulligan afterChandraBottoms).contains (.hand ⟨0⟩)
#guard (changedZones afterChandraMulligan afterChandraBottoms).contains (.library ⟨0⟩)

def afterChandraKeepsSix : Game :=
  mustApply afterChandraBottoms ⟨0⟩ .keep

#guard afterChandraKeepsSix.pending == .none
#guard afterChandraKeepsSix.step == .upkeep
#guard afterChandraKeepsSix.isFirstTurn
#guard (afterChandraKeepsSix.player ⟨0⟩).hand.size == 6
#guard (afterChandraKeepsSix.player ⟨1⟩).hand.size == 7
#guard (afterChandraKeepsSix.player ⟨0⟩).keptOpeningHand
#guard afterChandraKeepsSix.log.any (fun s => mentions s "takes the first turn")

/-- Both players declare a mulligan before either hand is shuffled (CR 103.5). -/
def afterBothDeclareMulligan : Game :=
  mustApply afterChandraDeclaresMulligan ⟨1⟩ .takeMulligan

#guard afterBothDeclareMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard afterBothDeclareMulligan.actor == some ⟨0⟩
#guard (afterBothDeclareMulligan.player ⟨0⟩).mulligansTaken == 1
#guard (afterBothDeclareMulligan.player ⟨1⟩).mulligansTaken == 1
#guard (afterBothDeclareMulligan.player ⟨0⟩).hand.size == 7
#guard (afterBothDeclareMulligan.player ⟨1⟩).hand.size == 7
#guard (afterBothDeclareMulligan.player ⟨1⟩).hand != (drawnHands.player ⟨1⟩).hand
#guard afterBothDeclareMulligan.mulliganToBottom == #[⟨0⟩, ⟨1⟩]
#guard afterBothDeclareMulligan.log.any (fun s => mentions s "will take a mulligan")

def afterChandraBottomsBothMulligan : Game :=
  let id := (afterBothDeclareMulligan.player ⟨0⟩).hand[0]!
  mustApply afterBothDeclareMulligan ⟨0⟩ (.putOnBottom #[id])

#guard afterChandraBottomsBothMulligan.pending == .putOnBottom ⟨1⟩ 1
#guard afterChandraBottomsBothMulligan.actor == some ⟨1⟩
#guard (afterChandraBottomsBothMulligan.player ⟨0⟩).hand.size == 6
#guard (afterChandraBottomsBothMulligan.player ⟨1⟩).hand.size == 7

#guard started.pending == .none
#guard (started.player ⟨0⟩).keptOpeningHand
#guard (started.player ⟨1⟩).keptOpeningHand
#guard mentions (header drawnHands) "CR 103.5"

-- Lands cannot be played before opening hands are kept.
#guard
  match drawnHands.apply ⟨0⟩ (.playLand (drawnHands.player ⟨0⟩).hand[0]!) with
  | .error _ => true
  | .ok _ => false

-- Nissa cannot declare before Chandra in the first round.
#guard
  match drawnHands.apply ⟨1⟩ .takeMulligan with
  | .error msg => mentions msg "not your turn"
  | .ok _ => false

#guard
  match started.apply ⟨0⟩ .takeMulligan with
  | .error msg => mentions msg "Not time to take a mulligan"
  | .ok _ => false

#guard
  match afterChandraMulligan.apply ⟨0⟩ (.putOnBottom #[]) with
  | .error msg => mentions msg "exactly 1"
  | .ok _ => false

#guard
  match afterChandraMulligan.apply ⟨0⟩ (.putOnBottom #[⟨99999⟩]) with
  | .error msg => msg == "no such object"
  | .ok _ => false

/-- The seventh mulligan leaves a zero-card hand; further mulligans are illegal. -/
def seventhMulligan : Game :=
  let g := drawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 6 })
  let g := mustApply g ⟨0⟩ .takeMulligan
  mustApply g ⟨1⟩ .keep

#guard seventhMulligan.pending == .putOnBottom ⟨0⟩ 7

def afterZeroHand : Game :=
  mustApply seventhMulligan ⟨0⟩ (.putOnBottom (seventhMulligan.player ⟨0⟩).hand)

#guard (afterZeroHand.player ⟨0⟩).hand.size == 0
#guard (afterZeroHand.player ⟨0⟩).keptOpeningHand
#guard afterZeroHand.pending == .none
#guard afterZeroHand.step == .upkeep

#guard
  let g := drawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 7 })
  match g.apply ⟨0⟩ .takeMulligan with
  | .error msg => mentions msg "zero cards"
  | .ok _ => false

-- The heuristic keeps opening hands rather than mulliganing.
#guard
  match Agent.choose drawnHands ⟨0⟩ with
  | some .keep => true
  | _ => false

def agentKeepsHands : Game := Agent.play drawnHands 10

#guard (agentKeepsHands.player ⟨0⟩).keptOpeningHand
#guard (agentKeepsHands.player ⟨1⟩).keptOpeningHand
#guard !agentKeepsHands.openingHandsPending
#guard agentKeepsHands.log.any (fun s => mentions s "takes the first turn")

/-- Two untapped Mountains and a Wayfarer's Bauble; a land has already been
played this turn so the agent will activate rather than play another land. -/
def baubleReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := addPermanent g wayfarersBauble ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def baubleSource (g : Game) : GameObject :=
  namedPermanent g "Wayfarer's Bauble"

#guard wayfarersBauble.activatedAbilities.size == 1
#guard wayfarersBauble.manaAbilities.isEmpty
#guard baubleReady.hasPriority ⟨0⟩
#guard baubleReady.canActivate ⟨0⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!)
#guard !(baubleReady.canActivate ⟨1⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!))

-- The heuristic activates the bauble when {2} is available.
#guard
  match Agent.choose baubleReady ⟨0⟩ with
  | some (.activate id 0) => id == (baubleSource baubleReady).id
  | _ => false

def proposedBauble : Game :=
  mustApply baubleReady ⟨0⟩ (.activate (baubleSource baubleReady).id 0)

#guard proposedBauble.pending == .activateManaAbilities ⟨0⟩
#guard proposedBauble.proposedSpell.isSome
#guard
  match proposedBauble.proposedSpell with
  | some prop => prop.kind == .activatedAbility
  | none => false
#guard proposedBauble.stack.size == 1
#guard (namedPermanent proposedBauble "Wayfarer's Bauble").isOnBattlefield
#guard proposedBauble.log.any (fun s => mentions s "begins activating Wayfarer's Bauble")
#guard proposedBauble.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard (changedZones baubleReady proposedBauble).contains .stack
#guard mentions (stackBlock proposedBauble) "Search your library"
#guard mentions (zoneBlock proposedBauble .stack) "Search your library"

-- Opponent cannot activate Chandra's bauble.
#guard
  match baubleReady.activateAbility ⟨1⟩ (baubleSource baubleReady).id 0 with
  | .error _ => true
  | .ok _ => false

-- A land has no non-mana activated ability.
#guard
  match (baubleReady.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match baubleReady.activateAbility ⟨0⟩ land.id 0 with
    | .error msg => mentions msg "has no activated ability"
    | .ok _ => false

def tapNextMana (g : Game) (p : PlayerId) : Game :=
  match (g.manaSources p)[0]? with
  | none => panic! "expected a mana source"
  | some (src, types) =>
    match types[0]? with
    | none => panic! "expected a mana type"
    | some t => mustApply g p (.tapForMana src.id t)

/-- Paying without enough mana reverses the activation (CR 602.2 / 733.1). -/
def reversedBauble : Game :=
  mustApply proposedBauble ⟨0⟩ .pay

#guard reversedBauble.pending == .none
#guard reversedBauble.proposedSpell.isNone
#guard reversedBauble.stack.isEmpty
#guard reversedBauble.hasPriority ⟨0⟩
#guard (namedPermanent reversedBauble "Wayfarer's Bauble").isOnBattlefield
#guard reversedBauble.log.any (fun s => mentions s "the activation is reversed")

def tappedOnceForBauble : Game := tapNextMana proposedBauble ⟨0⟩
def tappedTwiceForBauble : Game := tapNextMana tappedOnceForBauble ⟨0⟩

#guard (tappedTwiceForBauble.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2)
#guard tappedTwiceForBauble.pending == .activateManaAbilities ⟨0⟩

def paidBauble : Game :=
  mustApply tappedTwiceForBauble ⟨0⟩ .pay

#guard paidBauble.pending == .none
#guard paidBauble.proposedSpell.isNone
#guard paidBauble.hasPriority ⟨0⟩
#guard paidBauble.stack.size == 1
#guard (paidBauble.player ⟨0⟩).manaPool.isEmpty
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  (paidBauble.object! id).name == "Wayfarer's Bauble")
#guard !(paidBauble.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard paidBauble.log.any (fun s => mentions s "sacrifices Wayfarer's Bauble")
#guard paidBauble.log.any (fun s => mentions s "activates Wayfarer's Bauble")
#guard (changedZones tappedTwiceForBauble paidBauble).contains .battlefield
#guard (changedZones tappedTwiceForBauble paidBauble).contains (.graveyard ⟨0⟩)
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  mentions (zoneLine paidBauble (.graveyard ⟨0⟩) id) "Search your library")

-- The agent pays once the pool covers {2}.
#guard
  match Agent.choose tappedTwiceForBauble ⟨0⟩ with
  | some .pay => true
  | _ => false

def resolvedBauble : Game := passBoth paidBauble

#guard resolvedBauble.stack.isEmpty
#guard (resolvedBauble.battlefield.filter (fun o => o.name == "Mountain")).size == 3
#guard (resolvedBauble.battlefield.filter (fun o =>
  o.name == "Mountain" && o.status.tapped)).size == 3
#guard resolvedBauble.log.any (fun s =>
  mentions s "puts Mountain onto the battlefield tapped")
#guard resolvedBauble.log.any (fun s => mentions s "shuffles their library")
#guard (changedZones paidBauble resolvedBauble).contains .battlefield
#guard (changedZones paidBauble resolvedBauble).contains (.library ⟨0⟩)

-- Lands put onto the battlefield this way are not a land drop (CR 305.3).
#guard (resolvedBauble.player ⟨0⟩).landsPlayedThisTurn == 1

/-- Snowslope Hunter plus fodder and a known library top, in the precombat main. -/
def hunterReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g mountain
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def hunterSource (g : Game) : GameObject :=
  namedPermanent g "Snowslope Hunter"

def hunterFodder (g : Game) : GameObject :=
  namedPermanent g "Raging Goblin"

def hunterAbility : ActivatedAbility :=
  snowslopeHunter.activatedAbilities[0]!

#guard snowslopeHunter.activatedAbilities.size == 1
#guard hunterAbility.cost.sacrificeAnotherCreatureOrArtifact
#guard hunterAbility.effect == .exileTopPlayUntilEndOfNextTurn
#guard hunterAbility.onlyDuringYourTurn
#guard hunterAbility.onceEachTurn
#guard !hunterAbility.onlyAsSorcery
#guard hunterReady.canActivate ⟨0⟩ (hunterSource hunterReady) hunterAbility
#guard !(hunterReady.canActivate ⟨1⟩ (hunterSource hunterReady) hunterAbility)
#guard (hunterReady.sacrificeCreatureOrArtifactChoices ⟨0⟩
  (hunterSource hunterReady).id).any (fun o => o.name == "Raging Goblin")

-- The heuristic begins activating the hunter when another creature is available.
#guard
  match Agent.choose hunterReady ⟨0⟩ with
  | some (.activate id 0) => id == (hunterSource hunterReady).id
  | _ => false

def proposedHunter : Game :=
  mustApply hunterReady ⟨0⟩ (.activate (hunterSource hunterReady).id 0)

#guard proposedHunter.pending == .activateManaAbilities ⟨0⟩
#guard proposedHunter.proposedSpell.isSome
#guard proposedHunter.stack.size == 1
#guard (namedPermanent proposedHunter "Raging Goblin").isOnBattlefield
#guard proposedHunter.log.any (fun s => mentions s "begins activating Snowslope Hunter")
#guard proposedHunter.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Sacrifice is not chosen at `activate`; it comes after `pay`.
#guard
  match proposedHunter.apply ⟨0⟩ (.sacrifice (hunterFodder proposedHunter).id) with
  | .error msg => mentions msg "Not time to sacrifice"
  | .ok _ => false

-- The heuristic pays the empty mana cost next.
#guard
  match Agent.choose proposedHunter ⟨0⟩ with
  | some .pay => true
  | _ => false

def paidHunter : Game :=
  mustApply proposedHunter ⟨0⟩ .pay

#guard
  match paidHunter.pending with
  | .sacrificePermanent p sid =>
    p == ⟨0⟩ && sid == (hunterSource paidHunter).id
  | _ => false
#guard paidHunter.proposedSpell.isSome
#guard (namedPermanent paidHunter "Raging Goblin").isOnBattlefield
#guard paidHunter.log.any (fun s =>
  mentions s "must sacrifice another creature or artifact")
#guard mentions (header paidHunter) "sacrifice a creature or artifact"

-- Cannot sacrifice the hunter itself, a land, or skip the choice.
#guard
  match paidHunter.apply ⟨0⟩ (.sacrifice (hunterSource paidHunter).id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

#guard
  match (paidHunter.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match paidHunter.apply ⟨0⟩ (.sacrifice land.id) with
    | .error msg => mentions msg "Can't sacrifice"
    | .ok _ => false

#guard
  match Agent.choose paidHunter ⟨0⟩ with
  | some (.sacrifice id) => id == (hunterFodder paidHunter).id
  | _ => false

def activatedHunter : Game :=
  mustApply paidHunter ⟨0⟩ (.sacrifice (hunterFodder paidHunter).id)

#guard activatedHunter.pending == .none
#guard activatedHunter.proposedSpell.isNone
#guard activatedHunter.hasPriority ⟨0⟩
#guard activatedHunter.stack.size == 1
#guard (namedPermanent activatedHunter "Snowslope Hunter").isOnBattlefield
#guard !(activatedHunter.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard (activatedHunter.player ⟨0⟩).graveyard.any (fun id =>
  (activatedHunter.object! id).name == "Raging Goblin")
#guard (namedPermanent activatedHunter "Snowslope Hunter").status.activationsThisTurn == 1
#guard activatedHunter.log.any (fun s => mentions s "sacrifices Raging Goblin")
#guard activatedHunter.log.any (fun s => mentions s "activates Snowslope Hunter")
#guard (changedZones hunterReady activatedHunter).contains .stack
#guard (changedZones hunterReady activatedHunter).contains .battlefield
#guard (changedZones hunterReady activatedHunter).contains (.graveyard ⟨0⟩)

/-- Finish activating Snowslope Hunter by paying, then sacrificing `sacName`. -/
def completeHunterActivation (g : Game) (sacName : String) : Game :=
  let g := mustApply g ⟨0⟩ (.activate (hunterSource g).id 0)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g sacName).id)

-- Only once each turn: a second fodder still cannot be spent this turn.
def hunterActivatedOnce : Game :=
  completeHunterActivation hunterReady "Raging Goblin"

#guard
  match hunterActivatedOnce.activateAbility ⟨0⟩ (hunterSource hunterActivatedOnce).id 0 with
  | .error msg => mentions msg "only once each turn"
  | .ok _ => false
#guard !(hunterActivatedOnce.canActivate ⟨0⟩ (hunterSource hunterActivatedOnce) hunterAbility)

def resolvedHunter : Game := passBoth activatedHunter

#guard resolvedHunter.stack.isEmpty
#guard resolvedHunter.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt")
#guard resolvedHunter.log.any (fun s =>
  mentions s "exiles Lightning Bolt and may play it until the end of their next turn")
#guard (changedZones activatedHunter resolvedHunter).contains .exile
#guard (changedZones activatedHunter resolvedHunter).contains (.library ⟨0⟩)
#guard mentions (snapshot resolvedHunter) "may be played by Chandra"
#guard mentions (zoneBlock resolvedHunter .exile) "may be played by Chandra"

def exiledBolt (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Lightning Bolt") with
  | some o => o
  | none => panic! "expected Lightning Bolt in exile"

#guard resolvedHunter.mayPlayFromExile ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.mayPlayFromExile ⟨1⟩ (exiledBolt resolvedHunter))
#guard resolvedHunter.canCast ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.canCast ⟨1⟩ (exiledBolt resolvedHunter))

-- Opponent cannot play the exiled card.
#guard
  match resolvedHunter.castSpell ⟨1⟩ (exiledBolt resolvedHunter).id
      (some (Target.player ⟨0⟩)) with
  | .error _ => true
  | .ok _ => false

-- Cast the exiled Lightning Bolt the same turn (CR 701.14).
def proposedExiledBolt : Game :=
  mustApply resolvedHunter ⟨0⟩
    (.cast (exiledBolt resolvedHunter).id (some (Target.player ⟨1⟩)))

#guard proposedExiledBolt.pending == .activateManaAbilities ⟨0⟩
#guard !(proposedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))
#guard proposedExiledBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")

def paidExiledBolt : Game :=
  mustApply (tapNextMana proposedExiledBolt ⟨0⟩) ⟨0⟩ .pay

def resolvedExiledBolt : Game := passBoth paidExiledBolt

#guard resolvedExiledBolt.stack.isEmpty
#guard (resolvedExiledBolt.player ⟨1⟩).life == 17
#guard resolvedExiledBolt.log.any (fun s => mentions s "is dealt 3 damage")
#guard !(resolvedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))

-- Playing an exiled land uses the land drop.
def hunterLandReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  addToLibraryTop g mountain ⟨0⟩

def resolvedHunterLand : Game :=
  passBoth (completeHunterActivation hunterLandReady "Raging Goblin")

def exiledMountain (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Mountain") with
  | some o => o
  | none => panic! "expected Mountain in exile"

#guard resolvedHunterLand.mayPlayFromExile ⟨0⟩ (exiledMountain resolvedHunterLand)
#guard resolvedHunterLand.canPlayLand ⟨0⟩

def playedExiledLand : Game :=
  mustApply resolvedHunterLand ⟨0⟩ (.playLand (exiledMountain resolvedHunterLand).id)

#guard (playedExiledLand.player ⟨0⟩).landsPlayedThisTurn == 1
#guard playedExiledLand.battlefield.any (fun o => o.name == "Mountain")
#guard playedExiledLand.log.any (fun s => mentions s "plays Mountain")
#guard !(playedExiledLand.objects.any (fun o => o.zone == .exile && o.name == "Mountain"))

-- Activate only during your turn: Chandra has priority on Nissa's turn.
def hunterOnNissaTurn : Game :=
  let g := skipTo hunterReady .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterOnNissaTurn.activePlayer == ⟨1⟩
#guard hunterOnNissaTurn.hasPriority ⟨0⟩
#guard
  match hunterOnNissaTurn.activateAbility ⟨0⟩ (hunterSource hunterOnNissaTurn).id 0 with
  | .error msg => mentions msg "only during your turn"
  | .ok _ => false

-- Instant-speed: the hunter can activate during the end step of your turn.
def hunterAtEndStep : Game := skipTo hunterReady .end 80

#guard hunterAtEndStep.step == .end
#guard hunterAtEndStep.canActivate ⟨0⟩ (hunterSource hunterAtEndStep) hunterAbility

-- Permission lasts through the next turn, then expires.
def hunterPermissionActive : Game :=
  let g := skipTo resolvedHunter .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterPermissionActive.activePlayer == ⟨1⟩
#guard hunterPermissionActive.mayPlayFromExile ⟨0⟩ (exiledBolt hunterPermissionActive)

def hunterOnNextTurn : Game :=
  let g := skipTo hunterPermissionActive .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterOnNextTurn.activePlayer == ⟨0⟩
#guard hunterOnNextTurn.mayPlayFromExile ⟨0⟩ (exiledBolt hunterOnNextTurn)
#guard hunterOnNextTurn.canActivate ⟨0⟩ (hunterSource hunterOnNextTurn) hunterAbility

def hunterActivatedNextTurn : Game :=
  completeHunterActivation hunterOnNextTurn "Gray Ogre"

#guard hunterActivatedNextTurn.log.any (fun s => mentions s "activates Snowslope Hunter")
#guard hunterActivatedNextTurn.log.any (fun s => mentions s "sacrifices Gray Ogre")

def hunterPermissionExpired : Game :=
  let g := skipTo hunterOnNextTurn .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterPermissionExpired.activePlayer == ⟨1⟩
#guard hunterPermissionExpired.hasPriority ⟨0⟩
#guard hunterPermissionExpired.log.any (fun s =>
  mentions s "can no longer be played from exile")
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o => !hunterPermissionExpired.mayPlayFromExile ⟨0⟩ o
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o =>
    match hunterPermissionExpired.castSpell ⟨0⟩ o.id (some (Target.player ⟨1⟩)) with
    | .error msg => mentions msg "may not play that card from exile"
    | .ok _ => false

-- Empty library: the ability still resolves.
def hunterEmptyLibrary : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })

def resolvedHunterEmpty : Game :=
  passBoth (completeHunterActivation hunterEmptyLibrary "Raging Goblin")

#guard resolvedHunterEmpty.stack.isEmpty
#guard resolvedHunterEmpty.log.any (fun s => mentions s "no cards in their library to exile")
#guard !(resolvedHunterEmpty.objects.any (fun o => o.zone == .exile))

end Mtg.Engine.Tests
