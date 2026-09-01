import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers

/-!
# Turn structure, cleanup, zone helpers, and basic combat or bolt smoke tests.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

def atEndStep : Game := skipTo started .end 80

/-- A 0/0 creature kept alive only by an until-end-of-turn pump. -/
def zeroZero : CardDef :=
  creature "Zero/Zero" ManaCost.empty #[] 0 0

def addPumpedCreature (g : Game) (card : CardDef) (pumpP pumpT : Int) : Game :=
  insertObject g card g.activePlayer .battlefield (some g.activePlayer)
    { pump := (pumpP, pumpT), summoningSick := false }

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
unchanged, but the land is now untapped (CR 502.2). -/
def nissaEnd : Game := skipTo nissaTurn2 .end 80
def chandraTurn3 : Game := passBoth nissaEnd

#guard nissaEnd.turnNumber == 2
#guard nissaEnd.step == .end
#guard nissaEnd.battlefield.any (·.status.tapped)
#guard chandraTurn3.turnNumber == 3
#guard chandraTurn3.activePlayer == ⟨0⟩
#guard chandraTurn3.step == .upkeep
#guard !(chandraTurn3.battlefield.any (·.status.tapped))
#guard nissaEnd.battlefield.map (·.id) == chandraTurn3.battlefield.map (·.id)
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

/-- Lightning Bolt to a player (CR 120.3a) changes that player's life total. -/
def afterBolt : Game :=
  started.applyEffect ⟨0⟩ (Effect.dealDamage 3) #[Target.player ⟨1⟩]

#guard (started.player ⟨1⟩).life == 20
#guard (afterBolt.player ⟨1⟩).life == 17
#guard (afterBolt.player ⟨0⟩).life == 20
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
#guard afterCombatDamage.log.any (fun s => mentions s "19 life")

/-- Put `card` into `p`'s hand without drawing. -/
def addToHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p) none {} (fun id pl => { pl with hand := pl.hand.push id })

/-- Put `card` into `p`'s graveyard. -/
def addToGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id pl =>
    { pl with graveyard := pl.graveyard.push id })

/-- Put `card` on top of `p`'s library (the back of the library array). -/
def addToLibraryTop (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p) none {} (fun id pl =>
    { pl with library := pl.library.push id })

/-- Propose a spell (CR 601.2a) and announce its target (CR 601.2c). -/
def proposeTargeted (g : Game) (p : PlayerId) (id : ObjectId) (t : Target) : Game :=
  mustApply (mustApply g p (.cast id)) p (.target t)

def handCardNamed (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match (g.handObjects p).find? (fun o => o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} in hand"

/-- CR 601.2: a player may begin casting without mana in their pool, then
announce a target (601.2c), activate mana abilities (601.2g), then pay. -/
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
  | some (.cast _) => true
  | _ => false

#guard agentBeginsCast

def proposedBolt : Game :=
  mustApply boltSetup ⟨0⟩ (.cast boltInHand.id)

#guard
  match proposedBolt.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedBolt.proposedSpell.isSome
#guard !proposedBolt.stack.isEmpty
#guard proposedBolt.stack.back!.targets.isEmpty
#guard !(proposedBolt.player ⟨0⟩).hand.contains boltInHand.id
#guard (proposedBolt.player ⟨0⟩).manaPool.isEmpty
#guard !proposedBolt.hasPriority ⟨0⟩
#guard !proposedBolt.canActivateManaAbility ⟨0⟩
#guard proposedBolt.actor == some ⟨0⟩
#guard proposedBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")
#guard proposedBolt.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- CR 601.2c comes before mana abilities and payment.
#guard
  match proposedBolt.apply ⟨0⟩ .pay with
  | .error msg => mentions msg "Choose a target first"
  | .ok _ => false
#guard
  match proposedBolt.apply ⟨0⟩ (.target (Target.permanent ⟨99999⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedBolt.apply ⟨1⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "may choose targets"
  | .ok _ => false

def agentChoosesTarget : Bool :=
  match Agent.choose proposedBolt ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

#guard agentChoosesTarget

def targetedBolt : Game :=
  mustApply proposedBolt ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard targetedBolt.pending == .activateManaAbilities ⟨0⟩
#guard targetedBolt.stack.back!.targets == #[Target.player ⟨1⟩]
#guard targetedBolt.canActivateManaAbility ⟨0⟩
#guard !targetedBolt.canActivateManaAbility ⟨1⟩
#guard targetedBolt.log.any (fun s => mentions s "chooses Nissa as a target (CR 601.2c)")
#guard targetedBolt.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

/-- Opponent cannot activate mana abilities during the caster's 601.2g window. -/
def nissaTapDenied : Bool :=
  match targetedBolt.tapForMana ⟨1⟩ boltMountain.id (.colored .red) with
  | .error _ => true
  | .ok _ => false

#guard nissaTapDenied

def agentTapsInWindow : Bool :=
  match Agent.choose targetedBolt ⟨0⟩ with
  | some (.tapForMana id _) => id == boltMountain.id
  | _ => false

#guard agentTapsInWindow

def tappedForBolt : Game :=
  mustApply targetedBolt ⟨0⟩ (.tapForMana boltMountain.id (.colored .red))

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
  match targetedBolt.apply ⟨0⟩ .pass with
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

/-- Paying without enough mana reverses the cast (CR 601.2 / 733.1). -/
def reversedBolt : Game :=
  mustApply targetedBolt ⟨0⟩ .pay

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
  mustApply ogreSetup ⟨0⟩ (.cast (handCardNamed ogreSetup ⟨0⟩ "Gray Ogre").id)

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

-- The heuristic still plays, and it announces targets then activates mana abilities.
#guard played.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard played.log.any (fun s => mentions s "must choose a target (CR 601.2c)")
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

def namedGraveyardCard (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.name == name && o.zone == .graveyard p) with
  | some o => o
  | none => panic! s!"expected {name} in the graveyard"

#guard readyToDeclareAttackers.step == .declareAttackers
#guard readyToDeclareAttackers.pending == .declareAttackers
#guard (readyToDeclareAttackers.battlefield.filter (readyToDeclareAttackers.canAttack)).size == 2

def onlyBearsAttack : Game :=
  match readyToDeclareAttackers.apply ⟨0⟩
      (.declareAttackers #[(namedPermanent readyToDeclareAttackers "Grizzly Bears").id]) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.attacking
#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.attackingWhom == some ⟨1⟩
#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.tapped
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.attacking
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.tapped
#guard onlyBearsAttack.log.any (fun s => mentions s "attacks Nissa with Grizzly Bears")
#guard !onlyBearsAttack.log.any (fun s => mentions s "with Gray Ogre")

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
#guard (namedPermanent readyToDeclareBlockers "Grizzly Bears").status.blocking.isEmpty

def bearsBlockOgre : Game :=
  let g := readyToDeclareBlockers
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent bearsBlockOgre "Grizzly Bears").status.blocking ==
  #[(namedPermanent bearsBlockOgre "Gray Ogre").id]
#guard (namedPermanent bearsBlockOgre "Gray Ogre").status.blocked
#guard bearsBlockOgre.log.any (fun s => mentions s "Grizzly Bears blocks Gray Ogre")
#guard bearsBlockOgre.pending == .none

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

/-- Unused mana is emptied as a turn-based action (CR 500.4). -/
def emptiedPool : Game := tappedMountain.emptyManaPools

#guard (emptiedPool.player ⟨0⟩).manaPool.isEmpty
#guard emptiedPool.log.any (fun s => mentions s "empties mana pool")

end Mtg.Engine.Tests
