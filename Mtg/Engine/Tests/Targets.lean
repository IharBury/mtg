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
import Mtg.Engine.Tests.Abilities

/-!
# Optional and sequential spell targets.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Meager Meal (Gollum adventure): up to one target creature, then target
player, in that card-text order (CR 601.2c / 115.1c). -/

#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetKind ==
  .upToOneCreatureThenPlayer
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetCount == 2
#guard
  match gollumSilentSlinkerCard.adventure with
  | some adv => adv.spellEffect == some (Effect.plusOneUpToOneAndPlayerGainsLife 2)
  | none => false

/-- Gollum in hand, a creature you control, an opposing creature, and {B}. -/
def meagerMealSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g gollumSilentSlinkerCard ⟨0⟩) ⟨0⟩ 1

#guard meagerMealSetup.canCastAdventure ⟨0⟩
  (handCardNamed meagerMealSetup ⟨0⟩ "Gollum, Silent Slinker")
#guard meagerMealSetup.asSorcery? ⟨0⟩

/-- No creatures: the first “target” word is optional, so Meager Meal is still
legal (the player target remains). -/
def meagerMealNoCreature : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand g gollumSilentSlinkerCard ⟨0⟩) ⟨0⟩ 1

#guard meagerMealNoCreature.canCastAdventure ⟨0⟩
  (handCardNamed meagerMealNoCreature ⟨0⟩ "Gollum, Silent Slinker")

def proposedMeagerMeal : Game :=
  mustApply meagerMealSetup ⟨0⟩
    (.castAdventure (handCardNamed meagerMealSetup ⟨0⟩ "Gollum, Silent Slinker").id)

#guard proposedMeagerMeal.pending == .chooseTargets ⟨0⟩
#guard (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId).name ==
  "Meager Meal"
#guard (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId).isAdventureSpell
#guard proposedMeagerMeal.stack.back!.targets.isEmpty
#guard proposedMeagerMeal.currentTargetSlot
  (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId) == 0
#guard proposedMeagerMeal.canSkipCurrentOptionalSlot
  (proposedMeagerMeal.object! proposedMeagerMeal.stack.back!.objectId)
#guard proposedMeagerMeal.log.any (fun s => mentions s "begins casting Meager Meal")
#guard proposedMeagerMeal.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- The first instance is the creature, not the player (card-text order).
#guard
  match proposedMeagerMeal.apply ⟨0⟩ (.target (Target.player ⟨0⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedMeagerMeal.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedMeagerMeal.announceTargetChoices ⟨0⟩
      #[(Target.permanent (namedPermanent proposedMeagerMeal "Grizzly Bears").id, none),
        (Target.player ⟨0⟩, none)] with
  | .error msg => mentions msg "separately"
  | .ok _ => false

-- Distinct instances of “target” are announced sequentially (CR 601.2c).
#guard
  match Agent.choose proposedMeagerMeal ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedMeagerMeal.object! tid).name == "Grizzly Bears"
  | _ => false

def meagerMealCreatureChosen : Game :=
  mustApply proposedMeagerMeal ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedMeagerMeal "Grizzly Bears").id))

#guard meagerMealCreatureChosen.pending == .chooseTargets ⟨0⟩
#guard meagerMealCreatureChosen.proposedSpell.isSome
#guard meagerMealCreatureChosen.stack.back!.targets ==
  #[Target.permanent (namedPermanent meagerMealCreatureChosen "Grizzly Bears").id]
#guard meagerMealCreatureChosen.currentTargetSlot
  (meagerMealCreatureChosen.object! meagerMealCreatureChosen.stack.back!.objectId) == 1
#guard !meagerMealCreatureChosen.canSkipCurrentOptionalSlot
  (meagerMealCreatureChosen.object! meagerMealCreatureChosen.stack.back!.objectId)
#guard meagerMealCreatureChosen.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target (CR 601.2c)")

-- After the creature, only a player is legal.
#guard
  match meagerMealCreatureChosen.apply ⟨0⟩
      (.target (Target.permanent
        (namedPermanent meagerMealCreatureChosen "Gray Ogre").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match meagerMealCreatureChosen.apply ⟨0⟩ .decline with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false
#guard
  match Agent.choose meagerMealCreatureChosen ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨0⟩
  | _ => false

def targetedMeagerMeal : Game :=
  mustApply meagerMealCreatureChosen ⟨0⟩ (.target (Target.player ⟨0⟩))

#guard targetedMeagerMeal.pending == .activateManaAbilities ⟨0⟩
#guard targetedMeagerMeal.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedMeagerMeal "Grizzly Bears").id,
    Target.player ⟨0⟩]

def paidMeagerMeal : Game := mustApply targetedMeagerMeal ⟨0⟩ .pay

#guard paidMeagerMeal.hasPriority ⟨0⟩
#guard paidMeagerMeal.log.any (fun s => mentions s "casts Meager Meal")

def resolvedMeagerMeal : Game := passBoth paidMeagerMeal

#guard resolvedMeagerMeal.stack.isEmpty
#guard (namedPermanent resolvedMeagerMeal "Grizzly Bears").status.plusOnePlusOne == 1
#guard (namedPermanent resolvedMeagerMeal "Gray Ogre").status.plusOnePlusOne == 0
#guard (resolvedMeagerMeal.player ⟨0⟩).life == 22
#guard (resolvedMeagerMeal.player ⟨1⟩).life == 20
#guard resolvedMeagerMeal.log.any (fun s =>
  mentions s "Grizzly Bears gets a +1/+1 counter")
#guard resolvedMeagerMeal.log.any (fun s => mentions s "Chandra gains 2 life")
#guard resolvedMeagerMeal.objects.any (fun o =>
  o.name == "Gollum, Silent Slinker" && o.zone == .exile)

/-- Decline the optional creature, then announce the player. -/
def meagerMealDeclinedCreature : Game :=
  mustApply proposedMeagerMeal ⟨0⟩ .decline

#guard meagerMealDeclinedCreature.pending == .chooseTargets ⟨0⟩
#guard meagerMealDeclinedCreature.stack.back!.targets.isEmpty
#guard meagerMealDeclinedCreature.stack.back!.skippedOptionalSlots == 1
#guard meagerMealDeclinedCreature.currentTargetSlot
  (meagerMealDeclinedCreature.object! meagerMealDeclinedCreature.stack.back!.objectId) == 1
#guard meagerMealDeclinedCreature.log.any (fun s =>
  mentions s "chooses no target (CR 603.3d / 601.2c)")
#guard
  match meagerMealDeclinedCreature.apply ⟨0⟩
      (.target (Target.permanent
        (namedPermanent meagerMealDeclinedCreature "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def targetedMeagerMealNoCreature : Game :=
  mustApply meagerMealDeclinedCreature ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard targetedMeagerMealNoCreature.pending == .activateManaAbilities ⟨0⟩
#guard targetedMeagerMealNoCreature.stack.back!.targets == #[Target.player ⟨1⟩]

def resolvedMeagerMealNoCreature : Game :=
  passBoth (mustApply targetedMeagerMealNoCreature ⟨0⟩ .pay)

#guard (namedPermanent resolvedMeagerMealNoCreature "Grizzly Bears").status.plusOnePlusOne == 0
#guard (resolvedMeagerMealNoCreature.player ⟨0⟩).life == 20
#guard (resolvedMeagerMealNoCreature.player ⟨1⟩).life == 22
#guard resolvedMeagerMealNoCreature.log.any (fun s => mentions s "Nissa gains 2 life")
#guard !resolvedMeagerMealNoCreature.log.any (fun s =>
  mentions s "gets a +1/+1 counter")

/-- With no creatures, the first slot is skipped automatically by the idle
path, then the player is announced. -/
def proposedMeagerMealNoCreature : Game :=
  mustApply meagerMealNoCreature ⟨0⟩
    (.castAdventure (handCardNamed meagerMealNoCreature ⟨0⟩ "Gollum, Silent Slinker").id)

#guard proposedMeagerMealNoCreature.pending == .chooseTargets ⟨0⟩
#guard proposedMeagerMealNoCreature.canSkipCurrentOptionalSlot
  (proposedMeagerMealNoCreature.object! proposedMeagerMealNoCreature.stack.back!.objectId)
#guard (proposedMeagerMealNoCreature.legalProposedTargets ⟨0⟩
  (proposedMeagerMealNoCreature.object! proposedMeagerMealNoCreature.stack.back!.objectId)).isEmpty
#guard
  match Agent.choose proposedMeagerMealNoCreature ⟨0⟩ with
  | some .decline => true
  | _ => false

def meagerMealNoCreatureAfterSkip : Game :=
  mustApply proposedMeagerMealNoCreature ⟨0⟩ .decline

#guard meagerMealNoCreatureAfterSkip.pending == .chooseTargets ⟨0⟩
#guard
  match Agent.choose meagerMealNoCreatureAfterSkip ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨0⟩
  | _ => false

-- A creature that leaves before resolution does not stop the life gain (CR 608.2b).
#guard
  let dest := namedPermanent paidMeagerMeal "Grizzly Bears"
  let (g, _) := paidMeagerMeal.move dest.id (.graveyard dest.owner) none
  let g := passBoth g
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (g.player ⟨0⟩).life == 22 &&
    g.log.any (fun s => mentions s "Chandra gains 2 life")

#guard (Keyword.firstStrike : Keywords).firstStrike
#guard (Keyword.islandwalk : Keywords).islandwalk
#guard largeBear.manaCost.manaValue == 5
#guard
  let p := ManaPool.empty.add (.colored .black) 2 |>.add .colorless 3
  (p.pay? largeBear.manaCost).isSome
#guard
  let p := ManaPool.empty.add (.colored .green) 2 |>.add .colorless 3
  (p.pay? largeBear.manaCost).isSome
#guard
  let p := ManaPool.empty.add (.colored .red) 2 |>.add .colorless 3
  (p.pay? largeBear.manaCost).isNone

end Mtg.Engine.Tests
