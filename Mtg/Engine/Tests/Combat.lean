import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Activation
import Mtg.Engine.Tests.Auras

/-!
# Modal activation, combat damage assignment, and Warg Tactics.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Goblin Cratermaker plus an opposing 2/2 and a Mountain; a land drop is already
used so the agent will activate rather than play another land. -/
def cratermakerReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def cratermakerSource (g : Game) : GameObject :=
  namedPermanent g "Goblin Cratermaker"

def cratermakerAbility : ActivatedAbility :=
  goblinCratermaker.activatedAbilities[0]!

#guard cratermakerAbility.isModal
#guard cratermakerAbility.cost.sacrificeSource
#guard cratermakerAbility.effect == Effect.dealDamageToTargetCreature 2
#guard cratermakerAbility.otherModes ==
  #[Effect.destroyTargetColorlessNonland]
#guard cratermakerReady.canActivate ⟨0⟩ (cratermakerSource cratermakerReady) cratermakerAbility
#guard !(cratermakerReady.canActivate ⟨1⟩ (cratermakerSource cratermakerReady)
  cratermakerAbility)
#guard (namedPermanent cratermakerReady "Grizzly Bears").isColorlessNonland == false
#guard (cratermakerSource cratermakerReady).printed.colors.contains .red

-- The heuristic begins activating Cratermaker when {1} is available.
#guard
  match Agent.choose cratermakerReady ⟨0⟩ with
  | some (.activate id 0) => id == (cratermakerSource cratermakerReady).id
  | _ => false

def proposedCratermaker : Game :=
  mustApply cratermakerReady ⟨0⟩ (.activate (cratermakerSource cratermakerReady).id 0)

#guard
  match proposedCratermaker.pending with
  | .chooseMode ⟨0⟩ => true
  | _ => false
#guard proposedCratermaker.proposedSpell.isSome
#guard proposedCratermaker.stack.size == 1
#guard (proposedCratermaker.object! proposedCratermaker.stack.back!.objectId).abilityEffect.isNone
#guard (namedPermanent proposedCratermaker "Goblin Cratermaker").isOnBattlefield
#guard proposedCratermaker.log.any (fun s => mentions s "begins activating Goblin Cratermaker")
#guard proposedCratermaker.log.any (fun s => mentions s "must choose a mode (CR 601.2b)")

-- Opponent cannot choose Chandra's mode.
#guard
  match proposedCratermaker.apply ⟨1⟩ (.chooseMode 0) with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

-- Mode index out of range.
#guard
  match proposedCratermaker.apply ⟨0⟩ (.chooseMode 2) with
  | .error msg => mentions msg "No such mode"
  | .ok _ => false

-- Targeting is not chosen at `activate`; it comes after the mode.
#guard
  match proposedCratermaker.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent proposedCratermaker "Grizzly Bears").id)) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false

-- The heuristic picks the damage mode when the opponent has a creature.
#guard
  match Agent.choose proposedCratermaker ⟨0⟩ with
  | some (.chooseMode 0) => true
  | _ => false

def cratermakerModeChosen : Game :=
  mustApply proposedCratermaker ⟨0⟩ (.chooseMode 0)

#guard cratermakerModeChosen.pending == .chooseTargets ⟨0⟩
#guard (cratermakerModeChosen.object! cratermakerModeChosen.stack.back!.objectId).abilityEffect ==
  some (Effect.dealDamageToTargetCreature 2)
#guard cratermakerModeChosen.log.any (fun s =>
  mentions s "chooses a mode: This creature deals 2 damage")
#guard cratermakerModeChosen.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- A player is not a legal target for the damage mode.
#guard
  match cratermakerModeChosen.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets Nissa's creature.
#guard
  match Agent.choose cratermakerModeChosen ⟨0⟩ with
  | some (.target (Target.permanent id)) =>
    (cratermakerModeChosen.object! id).name == "Grizzly Bears"
  | _ => false

def cratermakerTargeted : Game :=
  mustApply cratermakerModeChosen ⟨0⟩
    (.target (Target.permanent (namedPermanent cratermakerModeChosen "Grizzly Bears").id))

#guard cratermakerTargeted.pending == .activateManaAbilities ⟨0⟩
#guard cratermakerTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent cratermakerTargeted "Grizzly Bears").id]
#guard cratermakerTargeted.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target (CR 601.2c)")
#guard cratermakerTargeted.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Paying without mana reverses the activation (CR 602.2 / 733.1).
def reversedCratermaker : Game :=
  mustApply cratermakerTargeted ⟨0⟩ .pay

#guard reversedCratermaker.pending == .none
#guard reversedCratermaker.stack.isEmpty
#guard (namedPermanent reversedCratermaker "Goblin Cratermaker").isOnBattlefield
#guard reversedCratermaker.log.any (fun s => mentions s "the activation is reversed")

def paidCratermaker : Game :=
  mustApply (tapNextMana cratermakerTargeted ⟨0⟩) ⟨0⟩ .pay

#guard paidCratermaker.pending == .none
#guard paidCratermaker.proposedSpell.isNone
#guard paidCratermaker.hasPriority ⟨0⟩
#guard paidCratermaker.stack.size == 1
#guard (paidCratermaker.player ⟨0⟩).graveyard.any (fun id =>
  (paidCratermaker.object! id).name == "Goblin Cratermaker")
#guard !(paidCratermaker.battlefield.any (fun o => o.name == "Goblin Cratermaker"))
#guard paidCratermaker.log.any (fun s => mentions s "sacrifices Goblin Cratermaker")
#guard paidCratermaker.log.any (fun s => mentions s "activates Goblin Cratermaker")

def resolvedCratermaker : Game := passBoth paidCratermaker

#guard resolvedCratermaker.stack.isEmpty
#guard resolvedCratermaker.log.any (fun s => mentions s "Grizzly Bears is dealt 2 damage")
#guard resolvedCratermaker.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")
#guard !(resolvedCratermaker.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedCratermaker.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .graveyard ⟨1⟩)

/-- 2 damage is not lethal to a 3-toughness creature. -/
def cratermakerVsGiant : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  addPermanent g hillGiant ⟨1⟩ ⟨1⟩

def resolvedCratermakerVsGiant : Game :=
  let g := mustApply cratermakerVsGiant ⟨0⟩
    (.activate (cratermakerSource cratermakerVsGiant).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Hill Giant").id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent resolvedCratermakerVsGiant "Hill Giant").status.damage == 2
#guard resolvedCratermakerVsGiant.battlefield.any (fun o => o.name == "Hill Giant")
#guard resolvedCratermakerVsGiant.log.any (fun s => mentions s "Hill Giant is dealt 2 damage")
#guard !resolvedCratermakerVsGiant.log.any (fun s => mentions s "Hill Giant dies")

/-- Targeting the Cratermaker itself: it is sacrificed as a cost, so the ability
does nothing on resolution. -/
def cratermakerSelfTarget : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩

def resolvedCratermakerSelf : Game :=
  let g := mustApply cratermakerSelfTarget ⟨0⟩
    (.activate (cratermakerSource cratermakerSelfTarget).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (cratermakerSource g).id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard resolvedCratermakerSelf.stack.isEmpty
#guard !(resolvedCratermakerSelf.battlefield.any (fun o => o.name == "Goblin Cratermaker"))
#guard resolvedCratermakerSelf.log.any (fun s => mentions s "The target is no longer in play")

/-- Destroy mode: Wayfarer's Bauble is a colorless nonland permanent. -/
def cratermakerDestroyReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  let g := addPermanent g wayfarersBauble ⟨1⟩ ⟨1⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

#guard (namedPermanent cratermakerDestroyReady "Wayfarer's Bauble").isColorlessNonland
#guard !(namedPermanent cratermakerDestroyReady "Goblin Cratermaker").isColorlessNonland

-- No opposing creature: the heuristic prefers the destroy mode.
#guard
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  match Agent.choose g ⟨0⟩ with
  | some (.chooseMode 1) => true
  | _ => false

-- A Mountain is a land, so it is not a legal destroy target.
#guard
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  match (g.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match g.apply ⟨0⟩ (.target (Target.permanent land.id)) with
    | .error msg => mentions msg "Illegal target"
    | .ok _ => false

-- A colored creature is not a legal destroy target.
#guard
  let g := addPermanent cratermakerDestroyReady grizzlyBears ⟨1⟩ ⟨1⟩
  let g := mustApply g ⟨0⟩ (.activate (cratermakerSource g).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def resolvedCratermakerDestroy : Game :=
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Wayfarer's Bauble").id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard resolvedCratermakerDestroy.stack.isEmpty
#guard resolvedCratermakerDestroy.log.any (fun s => mentions s "Wayfarer's Bauble is destroyed")
#guard !(resolvedCratermakerDestroy.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard resolvedCratermakerDestroy.objects.any (fun o =>
  o.name == "Wayfarer's Bauble" && o.zone == .graveyard ⟨1⟩)
#guard !(resolvedCratermakerDestroy.battlefield.any (fun o => o.name == "Goblin Cratermaker"))

-- Destroy mode cannot be chosen when there is no colorless nonland.
#guard
  match proposedCratermaker.apply ⟨0⟩ (.chooseMode 1) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Instant-speed: Cratermaker can activate during the end step.
def cratermakerAtEndStep : Game := skipTo cratermakerReady .end 80

#guard cratermakerAtEndStep.step == .end
#guard cratermakerAtEndStep.canActivate ⟨0⟩ (cratermakerSource cratermakerAtEndStep)
  cratermakerAbility

/-- Hill Giant (3/3) blocked by two Llanowar Elves (1/1): CR 510.1c lets the
attacker assign all 3 damage to one blocker. -/
def giantVsTwoElves : Game :=
  let g := addPermanent started hillGiant ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def giantBlockedByTwoElves : Game :=
  let g := passBoth (skipTo giantVsTwoElves .beginningOfCombat 80)
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let g := mustApply g ⟨0⟩ (.declareAttackers #[giant.id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(elves[0]!.id, giant.id), (elves[1]!.id, giant.id)])

def giantReadyToAssign : Game := passBoth giantBlockedByTwoElves

#guard giantReadyToAssign.step == .combatDamage
#guard giantReadyToAssign.pending == .assignCombatDamage ⟨0⟩ true
#guard giantReadyToAssign.actor == some ⟨0⟩
#guard giantReadyToAssign.needsCombatDamageChoice true
#guard !giantReadyToAssign.needsCombatDamageChoice false
#guard
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  g.combatDamageToAssign giant true == 3 &&
    (g.legalCombatDamageRecipients giant true).size == 2 &&
    !g.canAssignCombatDamageToDefendingPlayer giant true
#guard
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let g := g.setObject { giant with status := giant.status.grantUntilEot Keyword.trample }
  let giant := namedPermanent g "Hill Giant"
  g.hasTrample giant && g.canAssignCombatDamageToDefendingPlayer giant true &&
    g.combatDamageToAssign giant true == 3

def giantAllDamageOnFirst : Game :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  mustApply g ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 3), (elves[1]!.id, 0)]
  }])

#guard giantAllDamageOnFirst.log.any (fun s =>
  mentions s "Hill Giant deals 3 combat damage to Llanowar Elves")
#guard (giantAllDamageOnFirst.log.filter (fun s =>
  mentions s "Hill Giant deals" && mentions s "combat damage to Llanowar Elves")).size == 1
#guard (giantAllDamageOnFirst.player ⟨1⟩).life == 20
#guard (giantAllDamageOnFirst.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).size == 1
#guard giantAllDamageOnFirst.battlefield.any (fun o => o.name == "Hill Giant")
#guard (namedPermanent giantAllDamageOnFirst "Hill Giant").status.damage == 2

/-- The same total can be split 1 and 2; both Elves then take lethal damage. -/
def giantSplitDamage : Game :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  mustApply g ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 1), (elves[1]!.id, 2)]
  }])

#guard giantSplitDamage.log.any (fun s =>
  mentions s "Hill Giant deals 1 combat damage to Llanowar Elves")
#guard giantSplitDamage.log.any (fun s =>
  mentions s "Hill Giant deals 2 combat damage to Llanowar Elves")
#guard (giantSplitDamage.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).isEmpty
#guard giantSplitDamage.battlefield.any (fun o => o.name == "Hill Giant")

/-- Assigning less than power, or to a creature that is not blocking, is illegal. -/
def giantTooLittleDamage : Bool :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  match g.apply ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 2)]
  }]) with
  | .error msg => mentions msg "equal to its power"
  | .ok _ => false

#guard giantTooLittleDamage

def giantAssignsToItself : Bool :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  match g.apply ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(giant.id, 3)]
  }]) with
  | .error msg => mentions msg "creatures blocking it"
  | .ok _ => false

#guard giantAssignsToItself

/-- An empty assignment uses the default (all damage to the first blocker). -/
def giantDefaultAssign : Game :=
  mustApply giantReadyToAssign ⟨0⟩ (.assignCombatDamage #[])

#guard giantDefaultAssign.log.any (fun s =>
  mentions s "Hill Giant deals 3 combat damage to Llanowar Elves")
#guard (giantDefaultAssign.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).size == 1

/-- CR 510.1d: a blocker whose attacker has left combat assigns no damage. -/
def twoOgresOneBears : Game :=
  let g := addPermanent started grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def blockerWhoseAttackerLeft : Game :=
  let g := passBoth (skipTo twoOgresOneBears .beginningOfCombat 80)
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let bears := namedPermanent g "Grizzly Bears"
  let g := mustApply g ⟨0⟩ (.declareAttackers (ogres.map (·.id)))
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(bears.id, ogres[0]!.id)])
  let (g, _) := g.move ogres[0]!.id (.graveyard ⟨0⟩) none
  passBoth g

#guard blockerWhoseAttackerLeft.log.any (fun s =>
  mentions s "not blocking any creatures and assigns no combat damage")
#guard blockerWhoseAttackerLeft.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")
#guard (namedPermanent blockerWhoseAttackerLeft "Grizzly Bears").status.damage == 0
#guard (blockerWhoseAttackerLeft.player ⟨1⟩).life == 18

/-- CR 510.1d: a creature blocking two attackers divides its damage as chosen. -/
def bearsBlockingTwoOgresReady : Game :=
  let g := passBoth (skipTo twoOgresOneBears .beginningOfCombat 80)
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let g := mustApply g ⟨0⟩ (.declareAttackers (ogres.map (·.id)))
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with
    status := { bears.status with blocking := ogres.map (·.id) } }
  let g := Id.run do
    let mut g := g
    for o in ogres do
      let a := g.object! o.id
      g := g.setObject { a with status := { a.status with blocked := true } }
    return g
  passBoth g

#guard bearsBlockingTwoOgresReady.step == .combatDamage
#guard bearsBlockingTwoOgresReady.pending == .assignCombatDamage ⟨1⟩ false
#guard bearsBlockingTwoOgresReady.actor == some ⟨1⟩
#guard bearsBlockingTwoOgresReady.needsCombatDamageChoice false
#guard bearsBlockingTwoOgresReady.needsCombatDamageChoice true == false
#guard
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  g.combatDamageToAssign bears false == 2 &&
    (g.legalCombatDamageRecipients bears false).size == 2 &&
    !g.canAssignCombatDamageToDefendingPlayer bears false

def bearsAssignAllToFirstOgre : Game :=
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  mustApply g ⟨1⟩ (.assignCombatDamage #[{
    source := bears.id
    toCreatures := #[(ogres[0]!.id, 2), (ogres[1]!.id, 0)]
  }])

#guard bearsAssignAllToFirstOgre.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Gray Ogre")
#guard (bearsAssignAllToFirstOgre.log.filter (fun s =>
  mentions s "Grizzly Bears deals" && mentions s "combat damage to Gray Ogre")).size == 1
#guard (bearsAssignAllToFirstOgre.battlefield.filter (fun o =>
  o.name == "Gray Ogre")).size == 1
#guard !(bearsAssignAllToFirstOgre.battlefield.any (fun o => o.name == "Grizzly Bears"))

def bearsAssignsToItself : Bool :=
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  match g.apply ⟨1⟩ (.assignCombatDamage #[{
    source := bears.id
    toCreatures := #[(bears.id, 2)]
  }]) with
  | .error msg => mentions msg "creatures it's blocking"
  | .ok _ => false

#guard bearsAssignsToItself

/-- Propose a modal spell, choose a 0-based mode, then announce its target. -/
def proposeModal (g : Game) (p : PlayerId) (id : ObjectId) (mode : Nat) (t : Target) : Game :=
  mustApply (mustApply (mustApply g p (.cast id)) p (.chooseMode mode)) p (.target t)

def hexproofFlyer : CardDef :=
  creature "Hexproof Flyer" ManaCost.empty #[] 1 1
    (keywords := Keyword.flying.merge Keyword.hexproof)

/-- Warg Tactics in hand, Grizzly Bears you control, an opposing flyer, enough mana. -/
def wargSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterfliesCard ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard wargSetup.canCast ⟨0⟩ (handCardNamed wargSetup ⟨0⟩ "Warg Tactics")
#guard wargTactics.isModal
#guard wargTactics.requiresTarget
#guard (wargSetup.legalModes ⟨0⟩ (handCardNamed wargSetup ⟨0⟩ "Warg Tactics")).size == 2

-- Cannot cast with no legal mode (no flyer and no creature you control).
#guard
  let g := withGreenMana (addToHand afterDraw wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := withGreenMana (addToHand afterDraw wargTactics ⟨0⟩) ⟨0⟩ 2
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Warg Tactics").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Own creature alone enables only the +1/+1 mode; an opposing flyer alone enables destroy.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") &&
    g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[1]
#guard
  let g := addPermanent afterDraw velvetwingButterfliesCard ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") &&
    g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[0]

-- An opposing hexproof flyer cannot be chosen for destroy (CR 702.11b).
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[1]

-- Casting a modal spell asks for a mode before a target (CR 601.2b).
def proposedWarg : Game :=
  mustApply wargSetup ⟨0⟩ (.cast (handCardNamed wargSetup ⟨0⟩ "Warg Tactics").id)

#guard
  match proposedWarg.pending with
  | .chooseMode ⟨0⟩ => true
  | _ => false
#guard proposedWarg.proposedSpell.isSome
#guard !proposedWarg.stack.isEmpty
#guard proposedWarg.stack.back!.chosenMode.isNone
#guard proposedWarg.stack.back!.targets.isEmpty
#guard proposedWarg.actor == some ⟨0⟩
#guard proposedWarg.log.any (fun s => mentions s "begins casting Warg Tactics")
#guard proposedWarg.log.any (fun s => mentions s "must choose a mode (CR 601.2b")

#guard
  match proposedWarg.apply ⟨0⟩ .pay with
  | .error msg => mentions msg "Choose a mode first"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent proposedWarg "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨0⟩ (.chooseMode 2) with
  | .error msg => mentions msg "No such mode"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨1⟩ (.chooseMode 0) with
  | .error msg => mentions msg "may choose a mode"
  | .ok _ => false

-- The agent prefers destroying an opponent's flyer when that mode is legal.
#guard
  match Agent.choose proposedWarg ⟨0⟩ with
  | some (.chooseMode 0) => true
  | _ => false
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Warg Tactics").id)
  match Agent.choose g ⟨0⟩ with
  | some (.chooseMode 1) => true
  | _ => false

def wargModeDestroy : Game :=
  mustApply proposedWarg ⟨0⟩ (.chooseMode 0)

#guard wargModeDestroy.pending == .chooseTargets ⟨0⟩
#guard wargModeDestroy.stack.back!.chosenMode == some 0
#guard wargModeDestroy.log.any (fun s => mentions s "chooses mode 1")
#guard wargModeDestroy.log.any (fun s => mentions s "destroy target creature with flying")
#guard wargModeDestroy.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Mode 1 cannot target a creature without flying or a player.
#guard
  match wargModeDestroy.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent wargModeDestroy "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match wargModeDestroy.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

#guard
  match Agent.choose wargModeDestroy ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (wargModeDestroy.object! tid).name == "Velvetwing Butterflies"
  | _ => false

def targetedWargDestroy : Game :=
  mustApply wargModeDestroy ⟨0⟩
    (.target (Target.permanent (namedPermanent wargModeDestroy "Velvetwing Butterflies").id))

#guard targetedWargDestroy.pending == .activateManaAbilities ⟨0⟩
#guard targetedWargDestroy.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedWargDestroy "Velvetwing Butterflies").id]

def paidWargDestroy : Game :=
  mustApply targetedWargDestroy ⟨0⟩ .pay

#guard paidWargDestroy.hasPriority ⟨0⟩
#guard paidWargDestroy.stack.size == 1
#guard paidWargDestroy.log.any (fun s => mentions s "casts Warg Tactics")

def resolvedWargDestroy : Game := passBoth paidWargDestroy

#guard resolvedWargDestroy.stack.isEmpty
#guard !(resolvedWargDestroy.battlefield.any (fun o => o.name == "Velvetwing Butterflies"))
#guard resolvedWargDestroy.objects.any (fun o =>
  o.name == "Velvetwing Butterflies" && o.zone == .graveyard ⟨1⟩)
#guard resolvedWargDestroy.log.any (fun s => mentions s "Velvetwing Butterflies is destroyed")
#guard (resolvedWargDestroy.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedWargDestroy.object! id).name == "Warg Tactics")

-- If the flyer leaves before resolution, the spell does nothing (CR 608.2b).
def wargDestroyTargetGone : Game :=
  let id := (namedPermanent paidWargDestroy "Velvetwing Butterflies").id
  let (g, _) := paidWargDestroy.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard wargDestroyTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(wargDestroyTargetGone.battlefield.any (fun o => o.name == "Velvetwing Butterflies"))

def wargModePump : Game :=
  mustApply proposedWarg ⟨0⟩ (.chooseMode 1)

#guard wargModePump.pending == .chooseTargets ⟨0⟩
#guard wargModePump.stack.back!.chosenMode == some 1
#guard wargModePump.log.any (fun s => mentions s "chooses mode 2")

-- Mode 2 cannot target an opponent's creature.
#guard
  match wargModePump.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent wargModePump "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def paidWargPump : Game :=
  let g := mustApply wargModePump ⟨0⟩
    (.target (Target.permanent (namedPermanent wargModePump "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

def resolvedWargPump : Game := passBoth paidWargPump

#guard resolvedWargPump.stack.isEmpty
#guard (namedPermanent resolvedWargPump "Grizzly Bears").status.plusOnePlusOne == 1
#guard resolvedWargPump.power (namedPermanent resolvedWargPump "Grizzly Bears") == 3
#guard resolvedWargPump.toughness (namedPermanent resolvedWargPump "Grizzly Bears") == 3
#guard resolvedWargPump.hasTrample (namedPermanent resolvedWargPump "Grizzly Bears")
#guard resolvedWargPump.hasHexproof (namedPermanent resolvedWargPump "Grizzly Bears")
#guard (resolvedWargPump.effectiveKeywords
  (namedPermanent resolvedWargPump "Grizzly Bears")).hexproof
#guard resolvedWargPump.log.any (fun s =>
  mentions s "gets a +1/+1 counter and gains trample and hexproof")

/-- A 0/0 survives after receiving a +1/+1 counter. -/
def zeroWithCounter : Game :=
  let g := addPermanent started zeroZero ⟨0⟩ ⟨0⟩
  let id := (namedPermanent g "Zero/Zero").id
  g.applyEffect ⟨0⟩ (Effect.plusOnePlusOneTrampleHexproof) #[Target.permanent id]

#guard zeroWithCounter.power (namedPermanent zeroWithCounter "Zero/Zero") == 1
#guard zeroWithCounter.toughness (namedPermanent zeroWithCounter "Zero/Zero") == 1
#guard (zeroWithCounter.checkSBA).battlefield.any (fun o => o.name == "Zero/Zero")

/-- Hexproof wears off in cleanup; the counter does not. -/
def afterWargPumpCleanup : Game := passBoth (skipTo resolvedWargPump .end 80)

#guard (namedPermanent afterWargPumpCleanup "Grizzly Bears").status.plusOnePlusOne == 1
#guard afterWargPumpCleanup.power (namedPermanent afterWargPumpCleanup "Grizzly Bears") == 3
#guard !afterWargPumpCleanup.hasHexproof (namedPermanent afterWargPumpCleanup "Grizzly Bears")
#guard !afterWargPumpCleanup.hasTrample (namedPermanent afterWargPumpCleanup "Grizzly Bears")
#guard afterWargPumpCleanup.turnNumber == 2

/-- Granted trample assigns leftover combat damage. -/
def afterWargTrampleCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ (Effect.plusOnePlusOneTrampleHexproof)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Grizzly Bears").id)])
  passBoth g

#guard afterWargTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 1 combat damage to Llanowar Elves")
#guard afterWargTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears tramples for 2 to Nissa")
#guard (afterWargTrampleCombat.player ⟨1⟩).life == 18

/-- Nissa has Lightning Bolt while Chandra's pumped Grizzly Bears has hexproof. -/
def nissaBoltVsHexproof : Game :=
  let g := addPermanent resolvedWargPump mountain ⟨1⟩ ⟨1⟩
  let g := addToHand g lightningBolt ⟨1⟩
  mustApply g ⟨0⟩ .pass

#guard nissaBoltVsHexproof.hasPriority ⟨1⟩
#guard nissaBoltVsHexproof.canCast ⟨1⟩ (handCardNamed nissaBoltVsHexproof ⟨1⟩ "Lightning Bolt")

def proposedNissaBolt : Game :=
  mustApply nissaBoltVsHexproof ⟨1⟩
    (.cast (handCardNamed nissaBoltVsHexproof ⟨1⟩ "Lightning Bolt").id)

#guard
  match proposedNissaBolt.apply ⟨1⟩ (.target (Target.permanent
    (namedPermanent proposedNissaBolt "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def paidNissaBoltPlayer : Game :=
  let g := mustApply proposedNissaBolt ⟨1⟩ (.target (Target.player ⟨0⟩))
  let g := tapNextMana g ⟨1⟩
  mustApply g ⟨1⟩ .pay

def resolvedNissaBoltPlayer : Game := passBoth paidNissaBoltPlayer

#guard (resolvedNissaBoltPlayer.player ⟨0⟩).life == 17
#guard resolvedNissaBoltPlayer.battlefield.any (fun o => o.name == "Grizzly Bears")

-- After hexproof wears off, the same creature is a legal Lightning Bolt target.
#guard
  (afterWargPumpCleanup.legalTargets ⟨1⟩ (Effect.dealDamage 3)).contains
    (Target.permanent (namedPermanent afterWargPumpCleanup "Grizzly Bears").id)

/-- The agent casts Warg Tactics to destroy a flyer when that is the playable spell. -/
def agentWargDestroyOnly : Game :=
  let g := addPermanent afterDraw velvetwingButterfliesCard ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentWargDestroyOnly ⟨0⟩ with
  | some (.cast id) => (agentWargDestroyOnly.object! id).name == "Warg Tactics"
  | _ => false

/-- The agent casts Warg Tactics as a pump when no flyer is available. -/
def agentWargPumpOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentWargPumpOnly ⟨0⟩ with
  | some (.cast id) => (agentWargPumpOnly.object! id).name == "Warg Tactics"
  | _ => false

end Mtg.Engine.Tests
