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

#guard (changedManaPools started started).isEmpty
#guard (changedManaPools started afterDraw).isEmpty
#guard manaLine (started.player ⟨0⟩) == "Chandra — mana {}"
#guard manaLine (started.player ⟨1⟩) == "Nissa — mana {}"
#guard mentions (playerBlock tappedMountain (tappedMountain.player ⟨0⟩)) "mana {R}×1"

/-- Paying a mana cost (CR 601.2h) spends the pool; the demo reprints the new
contents. -/
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

end Mtg.Engine.Tests
