import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Auras

/-!
# Equipment, attach choices, and Beorn's Hospitality.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Ragged Short Spear in hand, Grizzly Bears on the battlefield, enough mana. -/
def spearSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  withRedMana (addToHand g raggedShortSpear ⟨0⟩) ⟨0⟩ 2

#guard spearSetup.canCast ⟨0⟩ (handCardNamed spearSetup ⟨0⟩ "Ragged Short Spear")
#guard spearSetup.asSorcery? ⟨0⟩
#guard !raggedShortSpear.requiresTarget
#guard raggedShortSpear.isEquipment

/-- Equipment is cast without announcing a creature (CR 301.5b). -/
def proposedSpear : Game :=
  mustApply spearSetup ⟨0⟩ (.cast (handCardNamed spearSetup ⟨0⟩ "Ragged Short Spear").id)

#guard proposedSpear.pending == .activateManaAbilities ⟨0⟩
#guard proposedSpear.stack.back!.targets.isEmpty
#guard proposedSpear.log.any (fun s => mentions s "begins casting Ragged Short Spear")

def paidSpear : Game := mustApply proposedSpear ⟨0⟩ .pay

#guard paidSpear.stack.size == 1
#guard paidSpear.hasPriority ⟨0⟩

/-- The Equipment enters unattached; the discard trigger waits on the stack. -/
def spearEntered : Game := passBoth paidSpear

#guard (namedPermanent spearEntered "Ragged Short Spear").attachedTo.isNone
#guard spearEntered.power (namedPermanent spearEntered "Grizzly Bears") == 2
#guard spearEntered.stack.size == 1
#guard spearEntered.log.any (fun s => mentions s "enters the battlefield")
#guard spearEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def spearMayDiscard : Game := passBoth spearEntered

#guard
  match spearMayDiscard.pending with
  | .mayDiscardDraw ⟨0⟩ 2 => true
  | _ => false
#guard spearMayDiscard.actor == some ⟨0⟩
#guard !spearMayDiscard.hasPriority ⟨0⟩
#guard spearMayDiscard.log.any (fun s => mentions s "may discard a card")
#guard spearMayDiscard.stack.isEmpty

/-- Declining the optional discard draws nothing. -/
def spearDeclined : Game := mustApply spearMayDiscard ⟨0⟩ .decline

#guard spearDeclined.pending == .none
#guard spearDeclined.hasPriority ⟨0⟩
#guard spearDeclined.log.any (fun s => mentions s "declines to discard")
#guard (spearDeclined.player ⟨0⟩).hand.size == (spearMayDiscard.player ⟨0⟩).hand.size
#guard (spearDeclined.player ⟨0⟩).library.size == (spearMayDiscard.player ⟨0⟩).library.size

-- The opponent cannot discard or decline for Chandra.
#guard
  match spearMayDiscard.apply ⟨1⟩ .decline with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false
#guard
  match spearMayDiscard.apply ⟨1⟩
      (.discard (spearMayDiscard.player ⟨0⟩).hand.back!) with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

-- Discarding a card that is not in hand is illegal.
#guard
  match spearMayDiscard.apply ⟨0⟩
      (.discard (namedPermanent spearMayDiscard "Grizzly Bears").id) with
  | .error msg => mentions msg "not in your hand"
  | .ok _ => false

/-- Discard a known extra card, then draw the two known library tops. -/
def spearKnownLib : Game :=
  let g := addToHand spearEntered forest ⟨0⟩
  addToLibraryTop (addToLibraryTop g forest ⟨0⟩) llanowarElves ⟨0⟩

def spearKnownMayDiscard : Game := passBoth spearKnownLib

def spearDiscardedForest : Game :=
  mustApply spearKnownMayDiscard ⟨0⟩
    (.discard (handCardNamed spearKnownMayDiscard ⟨0⟩ "Forest").id)

#guard spearDiscardedForest.pending == .none
#guard spearDiscardedForest.hasPriority ⟨0⟩
#guard spearDiscardedForest.log.any (fun s => mentions s "discards Forest")
#guard spearDiscardedForest.log.any (fun s => mentions s "draws Llanowar Elves")
#guard spearDiscardedForest.log.any (fun s => mentions s "draws Forest")
#guard (spearDiscardedForest.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard (spearDiscardedForest.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard (spearDiscardedForest.player ⟨0⟩).graveyard.any (fun id =>
  (spearDiscardedForest.object! id).name == "Forest")
#guard (spearDiscardedForest.player ⟨0⟩).hand.size ==
  (spearKnownMayDiscard.player ⟨0⟩).hand.size + 1

-- The heuristic discards the last card in hand.
#guard
  match Agent.choose spearKnownMayDiscard ⟨0⟩ with
  | some (.discard id) => id == (spearKnownMayDiscard.player ⟨0⟩).hand.back!
  | _ => false

/-- An empty hand skips the optional discard; no draw. -/
def spearEmptyHand : Game :=
  let g := { spearEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[] })
  g.beginMayDiscardDraw ⟨0⟩ 2

#guard spearEmptyHand.pending == .none
#guard spearEmptyHand.log.any (fun s => mentions s "has no card to discard")

/-- Equip {3} with a creature you control and enough mana. -/
def spearReadyToEquip : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withRedMana g ⟨0⟩ 3

def spearEquipAbility : ActivatedAbility :=
  raggedShortSpear.activatedAbilities[0]!

#guard spearReadyToEquip.canActivate ⟨0⟩
  (namedPermanent spearReadyToEquip "Ragged Short Spear") spearEquipAbility
#guard !(spearReadyToEquip.canActivate ⟨1⟩
  (namedPermanent spearReadyToEquip "Ragged Short Spear") spearEquipAbility)
#guard spearEquipAbility.onlyAsSorcery
#guard spearEquipAbility.effect.requiresTarget

-- Cannot Equip with no creature you control.
#guard
  let g := addPermanent afterDraw raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility

-- Cannot Equip an opponent's creature: Equip needs a creature you control.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Ragged Short Spear").id 0)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Gray Ogre").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Equip is sorcery-speed only (CR 702.6a).
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.asSorcery? ⟨0⟩ &&
    !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility

-- The heuristic Equips when {3} is available and a creature is controlled.
#guard
  match Agent.choose spearReadyToEquip ⟨0⟩ with
  | some (.activate id 0) =>
    (spearReadyToEquip.object! id).name == "Ragged Short Spear"
  | _ => false

def proposedEquip : Game :=
  mustApply spearReadyToEquip ⟨0⟩
    (.activate (namedPermanent spearReadyToEquip "Ragged Short Spear").id 0)

#guard
  match proposedEquip.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedEquip.log.any (fun s => mentions s "begins activating Ragged Short Spear")
#guard proposedEquip.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- The heuristic targets Chandra's creature.
#guard
  match Agent.choose proposedEquip ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedEquip.object! tid).name == "Grizzly Bears"
  | _ => false

def targetedEquip : Game :=
  mustApply proposedEquip ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedEquip "Grizzly Bears").id))

#guard targetedEquip.pending == .activateManaAbilities ⟨0⟩
#guard targetedEquip.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedEquip "Grizzly Bears").id]

def paidEquip : Game := mustApply targetedEquip ⟨0⟩ .pay

#guard paidEquip.pending == .none
#guard paidEquip.hasPriority ⟨0⟩
#guard (namedPermanent paidEquip "Ragged Short Spear").attachedTo.isNone
#guard paidEquip.log.any (fun s => mentions s "activates Ragged Short Spear")

def spearEquipped : Game := passBoth paidEquip

#guard (namedPermanent spearEquipped "Ragged Short Spear").attachedTo ==
  some (namedPermanent spearEquipped "Grizzly Bears").id
#guard spearEquipped.power (namedPermanent spearEquipped "Grizzly Bears") == 4
#guard spearEquipped.toughness (namedPermanent spearEquipped "Grizzly Bears") == 2
#guard (namedPermanent spearEquipped "Grizzly Bears").power == 2
#guard spearEquipped.log.any (fun s => mentions s "attaches to Grizzly Bears")

-- The heuristic does not re-equip a creature that is already equipped.
#guard
  let g := withRedMana spearEquipped ⟨0⟩ 3
  match Agent.choose g ⟨0⟩ with
  | some (.activate id 0) => (g.object! id).name != "Ragged Short Spear"
  | some .pass => true
  | some (.cast _) => true
  | _ => true

/-- The +2/+0 is a continuous effect, so it does not wear off in cleanup. -/
def afterSpearCleanup : Game := passBoth (skipTo spearEquipped .end 80)

#guard afterSpearCleanup.power (namedPermanent afterSpearCleanup "Grizzly Bears") == 4
#guard (namedPermanent afterSpearCleanup "Grizzly Bears").status.pumpPower == 0

/-- If the target leaves before Equip resolves, the ability does nothing. -/
def equipTargetGone : Game :=
  let id := (namedPermanent paidEquip "Grizzly Bears").id
  let (g, _) := paidEquip.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (namedPermanent equipTargetGone "Ragged Short Spear").attachedTo.isNone
#guard equipTargetGone.log.any (fun s => mentions s "no longer in play")

/-- If the equipped creature leaves, the Equipment becomes unattached and stays
on the battlefield (CR 301.5c / 704.5n). -/
def afterEquippedHostLeaves : Game :=
  let id := (namedPermanent spearEquipped "Grizzly Bears").id
  let (g, _) := spearEquipped.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard afterEquippedHostLeaves.log.any (fun s => mentions s "becomes unattached")
#guard afterEquippedHostLeaves.battlefield.any (fun o => o.name == "Ragged Short Spear")
#guard (namedPermanent afterEquippedHostLeaves "Ragged Short Spear").attachedTo.isNone
#guard !(afterEquippedHostLeaves.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard !(afterEquippedHostLeaves.log.any (fun s =>
  mentions s "Ragged Short Spear is put into its owner's graveyard"))

/-- Combat uses the equipped power. -/
def afterEquippedCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g raggedShortSpear (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEquippedCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 4 combat damage to Nissa")
#guard (afterEquippedCombat.player ⟨1⟩).life == 16

/-- Move Equip from one creature to another. -/
def spearTwoCreatures : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  withRedMana g ⟨0⟩ 3

def spearMovedToOgre : Game :=
  let g := mustApply spearTwoCreatures ⟨0⟩
    (.activate (namedPermanent spearTwoCreatures "Ragged Short Spear").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := withRedMana g ⟨0⟩ 3
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Ragged Short Spear").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Gray Ogre").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard spearMovedToOgre.power (namedPermanent spearMovedToOgre "Grizzly Bears") == 2
#guard spearMovedToOgre.power (namedPermanent spearMovedToOgre "Gray Ogre") == 4
#guard (namedPermanent spearMovedToOgre "Ragged Short Spear").attachedTo ==
  some (namedPermanent spearMovedToOgre "Gray Ogre").id

/-- Illegally attached Equipment becomes unattached and stays (CR 704.5n). -/
def spearOnMountain : Game :=
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  addAttachedAura g raggedShortSpear (namedPermanent g "Mountain") ⟨0⟩ ⟨0⟩

def spearUnattachedFromLand : Game := spearOnMountain.checkSBA

#guard spearUnattachedFromLand.log.any (fun s => mentions s "704.5n")
#guard (namedPermanent spearUnattachedFromLand "Ragged Short Spear").attachedTo.isNone
#guard spearUnattachedFromLand.battlefield.any (fun o => o.name == "Ragged Short Spear")

/-- The agent casts Ragged Short Spear when that is the playable spell. -/
def agentSpearOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g raggedShortSpear ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentSpearOnly ⟨0⟩ with
  | some (.cast id) => (agentSpearOnly.object! id).name == "Ragged Short Spear"
  | _ => false

/- Crude Bent Blade: target opponent sacrifices a creature; Equip +2/+1. -/

/-- Crude Bent Blade in hand, Nissa has a Grizzly Bears, enough mana. -/
def bladeSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  withBlackMana (addToHand g crudeBentBladeCard ⟨0⟩) ⟨0⟩ 3

#guard bladeSetup.canCast ⟨0⟩ (handCardNamed bladeSetup ⟨0⟩ "Crude Bent Blade")
#guard bladeSetup.asSorcery? ⟨0⟩
#guard !crudeBentBladeCard.requiresTarget
#guard crudeBentBladeCard.isEquipment
#guard crudeBentBladeCard.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBladeCard.staticAbilities == #[.equippedCreatureGets 2 1]

/-- Equipment is cast without announcing a creature (CR 301.5b). -/
def proposedBlade : Game :=
  mustApply bladeSetup ⟨0⟩ (.cast (handCardNamed bladeSetup ⟨0⟩ "Crude Bent Blade").id)

#guard proposedBlade.pending == .activateManaAbilities ⟨0⟩
#guard proposedBlade.stack.back!.targets.isEmpty
#guard proposedBlade.log.any (fun s => mentions s "begins casting Crude Bent Blade")

def paidBlade : Game := mustApply proposedBlade ⟨0⟩ .pay

#guard paidBlade.stack.size == 1
#guard paidBlade.hasPriority ⟨0⟩

/-- The Equipment enters unattached; the edict trigger waits for a target. -/
def bladeEntered : Game := passBoth paidBlade

#guard (namedPermanent bladeEntered "Crude Bent Blade").attachedTo.isNone
#guard bladeEntered.power (namedPermanent bladeEntered "Grizzly Bears") == 2
#guard bladeEntered.stack.size == 1
#guard bladeEntered.log.any (fun s => mentions s "enters the battlefield")
#guard bladeEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard
  match bladeEntered.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard (bladeEntered.legalTriggerTargets ⟨0⟩ .onEnterTargetOpponentSacrificesCreature).contains
  (Target.player ⟨1⟩)
#guard !(bladeEntered.legalTriggerTargets ⟨0⟩ .onEnterTargetOpponentSacrificesCreature).contains
  (Target.player ⟨0⟩)
#guard (bladeEntered.object! bladeEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterTargetOpponentSacrificesCreature

-- Cannot target yourself or a creature; the trigger targets an opponent.
#guard
  match bladeEntered.apply ⟨0⟩ (.target (Target.player ⟨0⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match bladeEntered.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent bladeEntered "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match bladeEntered.apply ⟨0⟩ .decline with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- The heuristic targets the opposing player.
#guard
  match Agent.choose bladeEntered ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def bladeTargeted : Game :=
  mustApply bladeEntered ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard bladeTargeted.pending == .none
#guard bladeTargeted.stack.back!.targets == #[Target.player ⟨1⟩]
#guard bladeTargeted.log.any (fun s => mentions s "chooses Nissa")

/-- Resolving the trigger makes Nissa choose a creature to sacrifice. -/
def bladeMustSac : Game := passBoth bladeTargeted

#guard
  match bladeMustSac.pending with
  | .sacrificeCreature ⟨1⟩ => true
  | _ => false
#guard bladeMustSac.actor == some ⟨1⟩
#guard !bladeMustSac.hasPriority ⟨0⟩
#guard !bladeMustSac.hasPriority ⟨1⟩
#guard bladeMustSac.log.any (fun s => mentions s "must sacrifice a creature")
#guard bladeMustSac.stack.isEmpty
#guard (bladeMustSac.sacrificeCreatureChoices ⟨1⟩).any (fun o => o.name == "Grizzly Bears")
#guard (bladeMustSac.sacrificeCreatureChoices ⟨0⟩).isEmpty

-- Chandra cannot sacrifice for Nissa, and Nissa cannot sacrifice a land or skip.
#guard
  match bladeMustSac.apply ⟨0⟩
      (.sacrifice (namedPermanent bladeMustSac "Grizzly Bears").id) with
  | .error msg => mentions msg "Only Nissa"
  | .ok _ => false
#guard
  match bladeMustSac.apply ⟨1⟩ .pass with
  | .error msg => mentions msg "required choice"
  | .ok _ => false
#guard
  match bladeMustSac.apply ⟨1⟩ .decline with
  | .error msg => mentions msg "Not time to decline"
  | .ok _ => false
#guard
  let g := addPermanent bladeMustSac mountain ⟨1⟩ ⟨1⟩
  match g.apply ⟨1⟩ (.sacrifice (namedPermanent g "Mountain").id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

-- The heuristic sacrifices Nissa's creature.
#guard
  match Agent.choose bladeMustSac ⟨1⟩ with
  | some (.sacrifice id) => (bladeMustSac.object! id).name == "Grizzly Bears"
  | _ => false

def bladeSacrificed : Game :=
  mustApply bladeMustSac ⟨1⟩
    (.sacrifice (namedPermanent bladeMustSac "Grizzly Bears").id)

#guard bladeSacrificed.pending == .none
#guard bladeSacrificed.hasPriority ⟨0⟩
#guard bladeSacrificed.log.any (fun s => mentions s "sacrifices Grizzly Bears")
#guard !(bladeSacrificed.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard (bladeSacrificed.player ⟨1⟩).graveyard.any (fun id =>
  (bladeSacrificed.object! id).name == "Grizzly Bears")
#guard bladeSacrificed.battlefield.any (fun o => o.name == "Crude Bent Blade")

/-- Idle actions sacrifice the required creature so skipTo can proceed. -/
def bladeIdleSacrificed : Game := applyIdle bladeMustSac

#guard bladeIdleSacrificed.pending == .none
#guard bladeIdleSacrificed.log.any (fun s => mentions s "sacrifices Grizzly Bears")

/-- With no opposing creature, the trigger still targets and then does nothing. -/
def bladeNoCreatureSetup : Game :=
  withBlackMana (addToHand afterDraw crudeBentBladeCard ⟨0⟩) ⟨0⟩ 3

def bladeNoCreatureEntered : Game :=
  let g := mustApply bladeNoCreatureSetup ⟨0⟩
    (.cast (handCardNamed bladeNoCreatureSetup ⟨0⟩ "Crude Bent Blade").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard
  match bladeNoCreatureEntered.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard (bladeNoCreatureEntered.legalTriggerTargets ⟨0⟩
  .onEnterTargetOpponentSacrificesCreature).contains (Target.player ⟨1⟩)

def bladeNoCreatureResolved : Game :=
  let g := mustApply bladeNoCreatureEntered ⟨0⟩ (.target (Target.player ⟨1⟩))
  passBoth g

#guard bladeNoCreatureResolved.pending == .none
#guard bladeNoCreatureResolved.hasPriority ⟨0⟩
#guard bladeNoCreatureResolved.log.any (fun s => mentions s "has no creature to sacrifice")
#guard bladeNoCreatureResolved.battlefield.any (fun o => o.name == "Crude Bent Blade")

-- Direct resolution with no announced target logs that the target is gone.
#guard
  (bladeNoCreatureResolved.applyTriggeredAbility ⟨0⟩
    .onEnterTargetOpponentSacrificesCreature none).log.any
    (fun s => mentions s "The target is no longer legal")

/-- Sacrificing Goblin Fireleaper still queues its dies trigger. -/
def bladeFireleaperSetup : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  withBlackMana (addToHand g crudeBentBladeCard ⟨0⟩) ⟨0⟩ 3

def bladeSacrificesFireleaper : Game :=
  let g := mustApply bladeFireleaperSetup ⟨0⟩
    (.cast (handCardNamed bladeFireleaperSetup ⟨0⟩ "Crude Bent Blade").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  let g := passBoth g
  mustApply g ⟨1⟩ (.sacrifice (namedPermanent g "Goblin Fireleaper").id)

#guard bladeSacrificesFireleaper.log.any (fun s => mentions s "sacrifices Goblin Fireleaper")
#guard
  match bladeSacrificesFireleaper.pending with
  | .chooseTargets ⟨1⟩ => true
  | _ => false
#guard (bladeSacrificesFireleaper.object!
  bladeSacrificesFireleaper.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature

/-- Equip {2} with a creature you control and enough mana. -/
def bladeReadyToEquip : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g crudeBentBladeCard ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withBlackMana g ⟨0⟩ 2

def bladeEquipAbility : ActivatedAbility :=
  crudeBentBladeCard.activatedAbilities[0]!

#guard bladeReadyToEquip.canActivate ⟨0⟩
  (namedPermanent bladeReadyToEquip "Crude Bent Blade") bladeEquipAbility
#guard !(bladeReadyToEquip.canActivate ⟨1⟩
  (namedPermanent bladeReadyToEquip "Crude Bent Blade") bladeEquipAbility)
#guard bladeEquipAbility.onlyAsSorcery
#guard bladeEquipAbility.effect.requiresTarget
#guard bladeEquipAbility.cost.mana == ManaCost.ofGeneric 2

-- Cannot Equip with no creature you control.
#guard
  let g := addPermanent afterDraw crudeBentBladeCard ⟨0⟩ ⟨0⟩
  let g := withBlackMana g ⟨0⟩ 2
  !g.canActivate ⟨0⟩ (namedPermanent g "Crude Bent Blade") bladeEquipAbility

-- The heuristic Equips when {2} is available and a creature is controlled.
#guard
  match Agent.choose bladeReadyToEquip ⟨0⟩ with
  | some (.activate id 0) =>
    (bladeReadyToEquip.object! id).name == "Crude Bent Blade"
  | _ => false

def proposedBladeEquip : Game :=
  mustApply bladeReadyToEquip ⟨0⟩
    (.activate (namedPermanent bladeReadyToEquip "Crude Bent Blade").id 0)

#guard
  match proposedBladeEquip.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false

def targetedBladeEquip : Game :=
  mustApply proposedBladeEquip ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedBladeEquip "Grizzly Bears").id))

def paidBladeEquip : Game := mustApply targetedBladeEquip ⟨0⟩ .pay

def bladeEquipped : Game := passBoth paidBladeEquip

#guard (namedPermanent bladeEquipped "Crude Bent Blade").attachedTo ==
  some (namedPermanent bladeEquipped "Grizzly Bears").id
#guard bladeEquipped.power (namedPermanent bladeEquipped "Grizzly Bears") == 4
#guard bladeEquipped.toughness (namedPermanent bladeEquipped "Grizzly Bears") == 3
#guard (namedPermanent bladeEquipped "Grizzly Bears").power == 2
#guard (namedPermanent bladeEquipped "Grizzly Bears").toughness == 2
#guard bladeEquipped.log.any (fun s => mentions s "attaches to Grizzly Bears")

-- The heuristic does not re-equip a creature that is already equipped.
#guard
  let g := withBlackMana bladeEquipped ⟨0⟩ 2
  match Agent.choose g ⟨0⟩ with
  | some (.activate id 0) => (g.object! id).name != "Crude Bent Blade"
  | some .pass => true
  | some (.cast _) => true
  | _ => true

/-- Bofur (a Dwarf) and unattached Equipment; Vow to Erebor offers the attach. -/
def vowMayAttach : Game :=
  let g := addPermanent afterDraw bofurReliableGuardianCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  g.applyEffect ⟨0⟩ (Effect.untapPumpMaybeAttach 2 2)
    #[Target.permanent (namedPermanent g "Bofur, Reliable Guardian").id]

#guard
  match vowMayAttach.pending with
  | .mayAttachEquipment ⟨0⟩ id =>
    id == (namedPermanent vowMayAttach "Bofur, Reliable Guardian").id
  | _ => false
#guard vowMayAttach.actor == some ⟨0⟩
#guard !vowMayAttach.hasPriority ⟨0⟩
#guard vowMayAttach.log.any (fun s => mentions s "may attach an Equipment to Bofur")
#guard vowMayAttach.power (namedPermanent vowMayAttach "Bofur, Reliable Guardian") == 3
#guard (namedPermanent vowMayAttach "Ragged Short Spear").attachedTo.isNone

-- The heuristic attaches an Equipment it controls that is not already on the host.
#guard
  match Agent.choose vowMayAttach ⟨0⟩ with
  | some (.choosePermanents ids) =>
    ids == #[(namedPermanent vowMayAttach "Ragged Short Spear").id]
  | _ => false

def vowAttached : Game :=
  mustApply vowMayAttach ⟨0⟩
    (.choosePermanents #[(namedPermanent vowMayAttach "Ragged Short Spear").id])

#guard (namedPermanent vowAttached "Ragged Short Spear").attachedTo ==
  some (namedPermanent vowAttached "Bofur, Reliable Guardian").id
#guard vowAttached.power (namedPermanent vowAttached "Bofur, Reliable Guardian") == 5
#guard vowAttached.pending == .none
#guard vowAttached.hasPriority ⟨0⟩
#guard vowAttached.log.any (fun s => mentions s "attaches to Bofur")

#guard
  match vowMayAttach.apply ⟨1⟩
      (.choosePermanents #[(namedPermanent vowMayAttach "Ragged Short Spear").id]) with
  | .error msg => mentions msg "Only Chandra may attach Equipment"
  | .ok _ => false

#guard
  match vowMayAttach.apply ⟨0⟩
      (.choosePermanents #[(namedPermanent vowMayAttach "Bofur, Reliable Guardian").id]) with
  | .error msg => mentions msg "is not an Equipment you control"
  | .ok _ => false

def vowDeclined : Game := mustApply vowMayAttach ⟨0⟩ .decline

#guard vowDeclined.pending == .none
#guard (namedPermanent vowDeclined "Ragged Short Spear").attachedTo.isNone
#guard vowDeclined.log.any (fun s => mentions s "declines to attach Equipment")

/-- A non-Dwarf is pumped; the spell does not ask to attach Equipment. -/
def vowOnBears : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  g.applyEffect ⟨0⟩ (Effect.untapPumpMaybeAttach 2 2)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]

#guard vowOnBears.pending == .none
#guard vowOnBears.power (namedPermanent vowOnBears "Grizzly Bears") == 4
#guard (namedPermanent vowOnBears "Ragged Short Spear").attachedTo.isNone

/-- No Equipment: the player is still asked, and the heuristic declines. -/
def vowMayAttachNoGear : Game :=
  let g := addPermanent afterDraw bofurReliableGuardianCard ⟨0⟩ ⟨0⟩
  g.applyEffect ⟨0⟩ (Effect.untapPumpMaybeAttach 2 2)
    #[Target.permanent (namedPermanent g "Bofur, Reliable Guardian").id]

#guard
  match vowMayAttachNoGear.pending with
  | .mayAttachEquipment ⟨0⟩ _ => true
  | _ => false
#guard
  match Agent.choose vowMayAttachNoGear ⟨0⟩ with
  | some .decline => true
  | _ => false

def dunedainEquipHuman : ActivatedAbility :=
  dunedainBlade.activatedAbilities[0]!

def dunedainEquip : ActivatedAbility :=
  dunedainBlade.activatedAbilities[1]!

/-- Dúnedain Blade with a Human, a Bear, and {3} so either Equip can be paid. -/
def dunedainReady : Game :=
  let g := addPermanent afterDraw dunedainBlade ⟨0⟩ ⟨0⟩
  let g := addPermanent g esquireOfTheKing ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withWhiteMana g ⟨0⟩ 3

#guard dunedainBlade.activatedAbilities.size == 2
#guard dunedainReady.canActivate ⟨0⟩
  (namedPermanent dunedainReady "Dúnedain Blade") dunedainEquipHuman
#guard dunedainReady.canActivate ⟨0⟩
  (namedPermanent dunedainReady "Dúnedain Blade") dunedainEquip

/-- Equip Human cannot target a non-Human. -/
def dunedainHumanRejectsBear : Bool :=
  let g := mustApply dunedainReady ⟨0⟩
    (.activate (namedPermanent dunedainReady "Dúnedain Blade").id 0)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

#guard dunedainHumanRejectsBear

/-- Equip {3} can attach to a non-Human. -/
def dunedainEquippedBear : Game :=
  let g := mustApply dunedainReady ⟨0⟩
    (.activate (namedPermanent dunedainReady "Dúnedain Blade").id 1)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent dunedainEquippedBear "Dúnedain Blade").attachedTo ==
  some (namedPermanent dunedainEquippedBear "Grizzly Bears").id
#guard dunedainEquippedBear.power (namedPermanent dunedainEquippedBear "Grizzly Bears") == 4
#guard dunedainEquippedBear.toughness (namedPermanent dunedainEquippedBear "Grizzly Bears") == 3

/-- Equip Human attaches to a Human. -/
def dunedainEquippedHuman : Game :=
  let g := mustApply dunedainReady ⟨0⟩
    (.activate (namedPermanent dunedainReady "Dúnedain Blade").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Esquire of the King").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent dunedainEquippedHuman "Dúnedain Blade").attachedTo ==
  some (namedPermanent dunedainEquippedHuman "Esquire of the King").id

/-- Only a Bear and {3}: the heuristic activates Equip {3}, not Equip Human. -/
def dunedainBearOnly : Game :=
  let g := addPermanent afterDraw dunedainBlade ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withWhiteMana g ⟨0⟩ 3

#guard !(dunedainBearOnly.canActivate ⟨0⟩
  (namedPermanent dunedainBearOnly "Dúnedain Blade") dunedainEquipHuman)
#guard dunedainBearOnly.canActivate ⟨0⟩
  (namedPermanent dunedainBearOnly "Dúnedain Blade") dunedainEquip

def dunedainHumanNeedsTarget : Bool :=
  match dunedainBearOnly.activateAbility ⟨0⟩
      (namedPermanent dunedainBearOnly "Dúnedain Blade").id 0 with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

#guard dunedainHumanNeedsTarget

def dunedainAgentChoosesEquip : Bool :=
  match Agent.choose dunedainBearOnly ⟨0⟩ with
  | some (.activate id 1) =>
    (dunedainBearOnly.object! id).name == "Dúnedain Blade"
  | _ => false

#guard dunedainAgentChoosesEquip

/-- A Human and only {1}: the heuristic activates Equip Human. -/
def dunedainHumanCheap : Game :=
  let g := addPermanent afterDraw dunedainBlade ⟨0⟩ ⟨0⟩
  let g := addPermanent g esquireOfTheKing ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withWhiteMana g ⟨0⟩ 1

def dunedainAgentChoosesEquipHuman : Bool :=
  match Agent.choose dunedainHumanCheap ⟨0⟩ with
  | some (.activate id 0) =>
    (dunedainHumanCheap.object! id).name == "Dúnedain Blade"
  | _ => false

#guard dunedainAgentChoosesEquipHuman

/-- The +2/+1 is a continuous effect, so it does not wear off in cleanup. -/
def afterBladeCleanup : Game := passBoth (skipTo bladeEquipped .end 80)

#guard afterBladeCleanup.power (namedPermanent afterBladeCleanup "Grizzly Bears") == 4
#guard afterBladeCleanup.toughness (namedPermanent afterBladeCleanup "Grizzly Bears") == 3
#guard (namedPermanent afterBladeCleanup "Grizzly Bears").status.pumpPower == 0

/-- Combat uses the equipped power and toughness. -/
def afterEquippedBladeCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g crudeBentBladeCard (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEquippedBladeCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 4 combat damage to Nissa")
#guard (afterEquippedBladeCombat.player ⟨1⟩).life == 16

/-- The agent casts Crude Bent Blade when that is the playable spell. -/
def agentBladeOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withBlackMana (addToHand g crudeBentBladeCard ⟨0⟩) ⟨0⟩ 3

#guard
  match Agent.choose agentBladeOnly ⟨0⟩ with
  | some (.cast id) => (agentBladeOnly.object! id).name == "Crude Bent Blade"
  | _ => false

/- Beorn's Hospitality: landfall +1/+1 and lasting Bear animation. -/

def addForests (g : Game) (p : PlayerId) : Nat → Game
  | 0 => g
  | n + 1 => addPermanent (addForests g p n) forest p p

/-- Hospitality and Grizzly Bears in play; a Forest in hand. -/
def hospitalityLandfallSetup : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  addToHand g forest ⟨0⟩

#guard hospitalityLandfallSetup.canPlayLand ⟨0⟩
#guard beornsHospitality.triggeredAbilities == #[.onLandYouControlEntersPlusOnePlusOne]
#guard beornsHospitality.activatedAbilities[0]!.effect == Effect.becomeSubtypeWithLandsPT "Bear"

def hospitalityLandPlayed : Game :=
  mustApply hospitalityLandfallSetup ⟨0⟩
    (.playLand (handCardNamed hospitalityLandfallSetup ⟨0⟩ "Forest").id)

#guard hospitalityLandPlayed.pending == .chooseTargets ⟨0⟩
#guard hospitalityLandPlayed.stack.size == 1
#guard (hospitalityLandPlayed.object! hospitalityLandPlayed.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersPlusOnePlusOne
#guard hospitalityLandPlayed.stack.back!.targets.isEmpty
#guard hospitalityLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack")
#guard hospitalityLandPlayed.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !hospitalityLandPlayed.hasPriority ⟨0⟩
#guard hospitalityLandPlayed.actor == some ⟨0⟩

-- The landfall trigger cannot target an opponent's creature or a player.
#guard
  let g := addPermanent hospitalityLandPlayed velvetwingButterfliesCard ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match hospitalityLandPlayed.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets a creature you control.
#guard
  match Agent.choose hospitalityLandPlayed ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (hospitalityLandPlayed.object! tid).name == "Grizzly Bears"
  | _ => false

def hospitalityLandfallTargeted : Game :=
  mustApply hospitalityLandPlayed ⟨0⟩
    (.target (Target.permanent (namedPermanent hospitalityLandPlayed "Grizzly Bears").id))

#guard hospitalityLandfallTargeted.pending == .none
#guard hospitalityLandfallTargeted.hasPriority ⟨0⟩
#guard hospitalityLandfallTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent hospitalityLandfallTargeted "Grizzly Bears").id]
#guard hospitalityLandfallTargeted.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target")

def hospitalityLandfallResolved : Game := passBoth hospitalityLandfallTargeted

#guard hospitalityLandfallResolved.stack.isEmpty
#guard (namedPermanent hospitalityLandfallResolved "Grizzly Bears").status.plusOnePlusOne == 1
#guard hospitalityLandfallResolved.power
  (namedPermanent hospitalityLandfallResolved "Grizzly Bears") == 3
#guard hospitalityLandfallResolved.log.any (fun s => mentions s "gets a +1/+1 counter")

/-- No creature you control: the landfall trigger is removed (CR 603.3d). -/
def hospitalityNoTarget : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterfliesCard ⟨1⟩ ⟨1⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard hospitalityNoTarget.stack.isEmpty
#guard hospitalityNoTarget.hasPriority ⟨0⟩
#guard hospitalityNoTarget.log.any (fun s => mentions s "no legal target")

/-- An opponent's land does not trigger your landfall. -/
def nissaLandVsHospitality : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .end 80)
  let g := skipTo g .precombatMain 80
  let g := addToHand g forest ⟨1⟩
  mustApply g ⟨1⟩ (.playLand (handCardNamed g ⟨1⟩ "Forest").id)

#guard nissaLandVsHospitality.stack.isEmpty
#guard !(nissaLandVsHospitality.log.any (fun s => mentions s "landfall"))
#guard (namedPermanent nissaLandVsHospitality "Grizzly Bears").status.plusOnePlusOne == 0

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def hospitalityTargetGone : Game :=
  let id := (namedPermanent hospitalityLandfallTargeted "Grizzly Bears").id
  let (g, _) := hospitalityLandfallTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard hospitalityTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(hospitalityTargetGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- Animate Beorn's Hospitality with three lands in play. -/
def hospitalityAnimateSetup : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addForests g ⟨0⟩ 3
  g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with
      manaPool := pl.manaPool.add (.colored .green) 7
      landsPlayedThisTurn := 1 })

#guard hospitalityAnimateSetup.canActivate ⟨0⟩
  (namedPermanent hospitalityAnimateSetup "Beorn's Hospitality")
  (beornsHospitality.activatedAbilities[0]!)
#guard !(namedPermanent hospitalityAnimateSetup "Beorn's Hospitality").isCreature
#guard hospitalityAnimateSetup.landsYouControl ⟨0⟩ == 3

def proposedHospitalityAnimate : Game :=
  mustApply hospitalityAnimateSetup ⟨0⟩
    (.activate (namedPermanent hospitalityAnimateSetup "Beorn's Hospitality").id 0)

#guard proposedHospitalityAnimate.pending == .activateManaAbilities ⟨0⟩
#guard proposedHospitalityAnimate.log.any (fun s => mentions s "begins activating Beorn's Hospitality")

def paidHospitalityAnimate : Game :=
  mustApply proposedHospitalityAnimate ⟨0⟩ .pay

#guard paidHospitalityAnimate.hasPriority ⟨0⟩
#guard paidHospitalityAnimate.stack.size == 1
#guard paidHospitalityAnimate.log.any (fun s => mentions s "activates Beorn's Hospitality")

def animatedHospitality : Game := passBoth paidHospitalityAnimate

#guard animatedHospitality.stack.isEmpty
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").isCreature
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").hasSubtype "Bear"
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").printed.isEnchantment
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").types.any (· == .creature)
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").types.any (· == .enchantment)
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").status.additionalCreature
#guard animatedHospitality.power
  (namedPermanent animatedHospitality "Beorn's Hospitality") == 3
#guard animatedHospitality.toughness
  (namedPermanent animatedHospitality "Beorn's Hospitality") == 3
#guard animatedHospitality.log.any (fun s => mentions s "becomes a Bear creature")

/-- The animation does not wear off in cleanup. -/
def afterHospitalityCleanup : Game := passBoth (skipTo animatedHospitality .end 80)

#guard (namedPermanent afterHospitalityCleanup "Beorn's Hospitality").isCreature
#guard afterHospitalityCleanup.power
  (namedPermanent afterHospitalityCleanup "Beorn's Hospitality") == 3

/-- 0/0 animated Hospitality dies (CR 704.5f). -/
def hospitalityZeroLands : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := withGreenMana g ⟨0⟩ 7
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Beorn's Hospitality").id 0)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard !(hospitalityZeroLands.battlefield.any (fun o => o.name == "Beorn's Hospitality"))
#guard hospitalityZeroLands.log.any (fun s => mentions s "dies (toughness 0)")

/-- Pathmaker's printed setting ability uses lands you control. -/
def pathmakerWithLands : Game :=
  let g := addForests afterDraw ⟨0⟩ 2
  addPermanent g mirkwoodPathmaker ⟨0⟩ ⟨0⟩

#guard pathmakerWithLands.power (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.toughness
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2

/-- Landfall can target the animated Hospitality; P/T is lands plus counters. -/
def hospitalitySelfLandfall : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addForests g ⟨0⟩ 3
  let o := namedPermanent g "Beorn's Hospitality"
  let g := g.setObject { o with
    status := { o.status with
      additionalCreature := true
      additionalSubtypes := #["Bear"]
      grantedStaticAbilities := #[.powerToughnessEqualLandsYouControl] } }
  let g := addToHand g forest ⟨0⟩
  let g := mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Beorn's Hospitality").id))
  passBoth g

#guard (namedPermanent hospitalitySelfLandfall "Beorn's Hospitality").status.plusOnePlusOne == 1
#guard hospitalitySelfLandfall.power
  (namedPermanent hospitalitySelfLandfall "Beorn's Hospitality") ==
    Int.ofNat (hospitalitySelfLandfall.landsYouControl ⟨0⟩) + 1

/-- Summoning sickness: a Hospitality that entered this turn cannot attack
after it becomes a creature (CR 302.6). -/
def hospitalityEnteredThisTurn : Game :=
  let g := withGreenMana (addToHand afterDraw beornsHospitality ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Beorn's Hospitality").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := addForests g ⟨0⟩ 2
  let g := withGreenMana g ⟨0⟩ 7
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Beorn's Hospitality").id 0)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality").isCreature
#guard !(hospitalityEnteredThisTurn.canAttack
  (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality"))
#guard (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality").status.summoningSick

/- The agent begins activating Hospitality when {5}{G}{G} is available. -/
#guard
  match Agent.choose hospitalityAnimateSetup ⟨0⟩ with
  | some (.activate id 0) =>
    (hospitalityAnimateSetup.object! id).name == "Beorn's Hospitality"
  | _ => false

end Mtg.Engine.Tests
