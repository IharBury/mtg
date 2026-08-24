import Mtg.Engine.Agent
import Mtg.Engine.Catalog
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

def started : Game :=
  match Start.start (testConfig 1) with
  | .ok g => g
  | .error e => panic! e

#guard testRedDeck.size == 60
#guard testGreenDeck.size == 60
#guard isLegalDeck .constructed testRedDeck
#guard isLegalDeck .constructed testGreenDeck
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

#guard (changedZones started started).isEmpty
#guard (zoneObjectIds started (.hand ⟨0⟩)).size == 7
#guard (zoneObjectIds started (.library ⟨0⟩)).size == 53
#guard (zoneObjectIds started .stack).isEmpty
#guard zoneBlock started .stack == "zone stack (0): (empty)"
#guard zoneBlock started (.library ⟨0⟩) == "zone Chandra's library (53)"

def drawnOnce : Game := Game.draw started ⟨0⟩

#guard (zoneObjectIds drawnOnce (.hand ⟨0⟩)).size == 8
#guard (zoneObjectIds drawnOnce (.library ⟨0⟩)).size == 52
#guard (changedZones started drawnOnce).contains (.hand ⟨0⟩)
#guard (changedZones started drawnOnce).contains (.library ⟨0⟩)
#guard !(changedZones started drawnOnce).contains .battlefield
#guard !(changedZones started drawnOnce).contains .stack

/-- `true` iff `needle` occurs in `haystack`. -/
def mentions (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

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

/-- Battlefield rendering names owner and controller (CR 108.3, 110.2). -/
def lastPermanent (g : Game) : GameObject :=
  match g.battlefield.back? with
  | some o => o
  | none => panic! "expected a permanent on the battlefield"

def mountainLine (g : Game) : String :=
  objectLine g (lastPermanent g)

#guard mountainLine withMountain ==
  s!"{(lastPermanent withMountain).id} Mountain (owned by Chandra, controlled by Chandra)"
#guard mentions (zoneBlock withMountain .battlefield)
  "(owned by Chandra, controlled by Chandra)"
#guard mentions (snapshot withMountain)
  "(owned by Chandra, controlled by Chandra)"
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
  s!"{(lastPermanent stolenMountain).id} Mountain (owned by Chandra, controlled by Nissa)"
#guard (stolenMountain.permanentsOf ⟨1⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard !(stolenMountain.permanentsOf ⟨0⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard mentions (playerBlock stolenMountain (stolenMountain.player ⟨1⟩))
  "(owned by Chandra, controlled by Nissa)"
#guard mentions (playerBlock stolenMountain (stolenMountain.player ⟨0⟩)) "  (none)"
#guard mentions (zoneBlock stolenMountain .battlefield)
  "(owned by Chandra, controlled by Nissa)"
#guard mentions (snapshot stolenMountain)
  "(owned by Chandra, controlled by Nissa)"

/-- Changing control without moving the permanent still reprints the battlefield. -/
def afterControlChange : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := some ⟨1⟩ }

#guard (zoneObjectIds withMountain .battlefield) == (zoneObjectIds afterControlChange .battlefield)
#guard battlefieldView withMountain != battlefieldView afterControlChange
#guard (changedZones withMountain afterControlChange).contains .battlefield
#guard mentions (objectLine afterControlChange (lastPermanent afterControlChange))
  "(owned by Chandra, controlled by Nissa)"

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

end Mtg.Engine.Tests
