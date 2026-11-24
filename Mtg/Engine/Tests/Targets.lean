import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
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

#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetSpec ==
  .upToOneCreatureThenPlayer
#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).targetCount == 2
#guard
  match gollumSilentSlinker.adventure with
  | some adv => adv.spellEffect == some (Effect.plusOneUpToOneAndPlayerGainsLife 2)
  | none => false

/-- Gollum in hand, a creature you control, an opposing creature, and {B}. -/
def meagerMealSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g gollumSilentSlinker ⟨0⟩) ⟨0⟩ 1

#guard meagerMealSetup.canCastAdventure ⟨0⟩
  (handCardNamed meagerMealSetup ⟨0⟩ "Gollum, Silent Slinker")
#guard meagerMealSetup.asSorcery? ⟨0⟩

/-- No creatures: the first “target” word is optional, so Meager Meal is still
legal (the player target remains). -/
def meagerMealNoCreature : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand g gollumSilentSlinker ⟨0⟩) ⟨0⟩ 1

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
#guard meagerMealDeclinedCreature.stack.back!.skippedOptionalSlots == #[0]
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

#guard KeywordAbility.hasFirstStrike #[Keyword.firstStrike]
#guard KeywordAbility.hasIslandwalk #[Keyword.islandwalk]
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

-- Phase 11: `*/*` CR 604.3 / 613.4a CDA creature spells on the stack evaluate
-- their actual CDA power/toughness for `.creatureSpellPTAtMost`, and Layer 4
-- type-changing effects feed `TargetSpec` / `objectHasCardType`.
#guard
  let cdaCreatureSpell : CardDef := {
    name := "Lands Avatar"
    types := #[.creature]
    subtypes := #["Avatar"]
    staticAbilities := #[.powerToughnessEqualLandsYouControl]
  }
  let landCard : CardDef := { name := "Forest", types := #[.land], subtypes := #["Forest"] }
  let gTwoLands := addPermanent (addPermanent afterDraw landCard ⟨1⟩ ⟨1⟩) landCard ⟨1⟩ ⟨1⟩
  let (gTwoStack, spellTwo) := gTwoLands.allocObject cdaCreatureSpell ⟨1⟩ .stack (some ⟨1⟩)
  let gTwoStack := gTwoStack.change (.pushStack { objectId := spellTwo.id, controller := ⟨1⟩, targets := #[] })
  let gFourLands := addPermanent (addPermanent gTwoLands landCard ⟨1⟩ ⟨1⟩) landCard ⟨1⟩ ⟨1⟩
  let (gFourStack, spellFour) := gFourLands.allocObject cdaCreatureSpell ⟨1⟩ .stack (some ⟨1⟩)
  let gFourStack := gFourStack.change (.pushStack { objectId := spellFour.id, controller := ⟨1⟩, targets := #[] })
  let rockCard : CardDef := { name := "Target Rock", types := #[.artifact] }
  let gAnim0 := addPermanent afterDraw rockCard ⟨0⟩ ⟨0⟩
  let rockObj := namedPermanent gAnim0 "Target Rock"
  let gAnim := gAnim0.createEffect
    (.layered (.objects #[rockObj.id]) (.types .add #[.creature] #[.golem] #[]) .untilEndOfTurn)
  gTwoStack.snapshotPower spellTwo == 2 &&
    gTwoStack.snapshotToughness spellTwo == 2 &&
    (gTwoStack.legalTargetsForSpec ⟨0⟩ .creatureSpell none).contains (.card spellTwo.id) &&
    (gTwoStack.legalTargetsForSpec ⟨0⟩ (.creatureSpellPTAtMost 2) none).contains (.card spellTwo.id) &&
    gFourStack.snapshotPower spellFour == 4 &&
    gFourStack.snapshotToughness spellFour == 4 &&
    !(gFourStack.legalTargetsForSpec ⟨0⟩ (.creatureSpellPTAtMost 2) none).contains (.card spellFour.id) &&
    (gAnim.legalTargetsForSpec ⟨0⟩ (.creatureYouControlSubtype .golem) none).contains (.permanent rockObj.id)

-- Phase 25 Item 2:
-- 1. `.upToTwoCreaturesTotalMvAtMost n` simultaneous announcement enforces `totalMv ≤ n`
--    (rejecting two 2-MV bears against cap 3 while accepting a 2-MV + 1-MV pair).
-- 2. `.twoNonlandsSharingType` lookahead filters out slot-0 nonlands with no type-mate.
-- 3. `effectHasEnoughTargets` rejects mandatory `targetCount == 2` spells/modes when only
--    1 legal target exists while keeping `allowsZeroTargets` ("up to") spells castable.
#guard
  let p0 : PlayerId := ⟨0⟩
  let mvCapSpell : CardDef := {
    name := "Mv Cap Grab"
    types := #[.sorcery]
    spellAbility := some { effect := {
      targets := (.upToTwoCreaturesTotalMvAtMost 3)
      body := .noop
    } }
  }
  let oneDrop : CardDef := {
    name := "Tiny Cub"
    manaCost := { symbols := #[.colored .green] }
    types := #[.creature]
    power := some (.fixed 1)
    toughness := some (.fixed 1)
  }
  let gMv0 := readyMain (emptyHand afterDraw p0)
  let gMv1 := addPermanent (addPermanent (addPermanent gMv0 grizzlyBears p0 p0) grizzlyBears ⟨1⟩ ⟨1⟩) oneDrop p0 p0
  let bears := gMv1.battlefield.filter (·.name == "Grizzly Bears")
  let cub := namedPermanent gMv1 "Tiny Cub"
  let gMvHand := addToHand gMv1 mvCapSpell p0
  let gMvProp := mustApply gMvHand p0 (.cast (handCardNamed gMvHand p0 "Mv Cap Grab").id)
  let overCapRejected :=
    match gMvProp.announceTargetChoices p0
        #[(Target.permanent bears[0]!.id, none), (Target.permanent bears[1]!.id, none)] with
    | .error _ => true
    | .ok _ => false
  let withinCapAccepted :=
    (gMvProp.announceTargetChoices p0
      #[(Target.permanent bears[0]!.id, none), (Target.permanent cub.id, none)]).isOk
  let shareSpell : CardDef := {
    name := "Twin Polish"
    types := #[.sorcery]
    spellAbility := some { effect := { targets := .twoNonlandsSharingType } }
  }
  let rockA : CardDef := { name := "Polish Rock A", types := #[.artifact] }
  let rockB : CardDef := { name := "Polish Rock B", types := #[.artifact] }
  let loneEnch : CardDef := { name := "Lone Seal", types := #[.enchantment] }
  let gSh0 := readyMain (emptyHand afterDraw p0)
  let gSh1 := addPermanent (addPermanent (addPermanent gSh0 rockA p0 p0) rockB p0 p0) loneEnch p0 p0
  let rA := (namedPermanent gSh1 "Polish Rock A").id
  let rB := (namedPermanent gSh1 "Polish Rock B").id
  let enchId := (namedPermanent gSh1 "Lone Seal").id
  let gShHand := addToHand gSh1 shareSpell p0
  let gShProp := mustApply gShHand p0 (.cast (handCardNamed gShHand p0 "Twin Polish").id)
  let slot0Legal := gShProp.legalProposedTargets p0 (gShProp.object! gShProp.stack.back!.objectId)
  let lookaheadOk :=
    slot0Legal.contains (.permanent rA) &&
    slot0Legal.contains (.permanent rB) &&
    !slot0Legal.contains (.permanent enchId)
  let twoArtsSpell : CardDef := {
    name := "Dual Tinker"
    types := #[.sorcery]
    spellAbility := some { effect := { targets := .twoArtifactsYouControl } }
  }
  let gOneArt := addToHand (addPermanent (readyMain (emptyHand afterDraw p0)) rockA p0 p0) twoArtsSpell p0
  let oneArtCard := handCardNamed gOneArt p0 "Dual Tinker"
  let gTwoArt := addPermanent gOneArt rockB p0 p0
  let twoArtCard := handCardNamed gTwoArt p0 "Dual Tinker"
  let enoughTargetsOk :=
    !gOneArt.canCastFrontFace p0 oneArtCard &&
    gTwoArt.canCastFrontFace p0 twoArtCard &&
    gMvHand.canCastFrontFace p0 (handCardNamed gMvHand p0 "Mv Cap Grab")
  overCapRejected && withinCapAccepted && lookaheadOk && enoughTargetsOk

-- Phase 3 (Unified TargetSpec):
-- 1. All 5 `GroupTargetConstraint` variants in `satisfiesGroupConstraint` / `legalTargetsForSpec`:
--    - `shareCharacteristic .color` enforces CR 105.2c (two colorless objects never share a color);
--    - `shareCharacteristic .creatureType` / `.subtype`;
--    - `distinctControllers`;
--    - `distinctNames` (CR 201.2a: nameless face-down permanents have no name and never collide);
--    - `distinctCardTypes` (bipartite matching on multi-type Artifact Creature + Creature).
-- 2. CR 112.1 stack-ability vs spell separation (`TargetSpec.spell` vs `TargetDomain.stackAbility`).
-- 3. CR 108.2 / 111.6 graveyard token exclusion (`.isKind .card` rejects tokens in graveyard).
-- 4. CR 115.4 `anyTarget` vs `anyOtherTarget` (excludes `sourceId`).
-- 5. Layer-3 `HasTextChange TargetSpec` updates both legal targets and `ToOracle` rendering.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let redGoblin : CardDef :=
    creature "Red Goblin" { symbols := #[.colored .red] } #["Goblin"] 1 1
  let redElf : CardDef :=
    creature "Red Elf" { symbols := #[.colored .red] } #["Elf"] 1 1
  let colorlessRockA : CardDef := { name := "Colorless Rock A", types := #[.artifact] }
  let colorlessRockB : CardDef := { name := "Colorless Rock B", types := #[.artifact] }
  let artCreature : CardDef := {
    name := "Artifact Construct"
    types := #[.artifact, .creature]
    subtypes := #["Construct"]
    power := some (.fixed 2)
    toughness := some (.fixed 2)
  }
  let g0 := readyMain (emptyHand afterDraw p0)
  let g1 :=
    addPermanent (addPermanent (addPermanent (addPermanent (addPermanent (addPermanent g0
      redGoblin p0 p0) redElf p1 p1) colorlessRockA p0 p0) colorlessRockB p1 p1) artCreature p0 p0) grizzlyBears p0 p0
  let gobId := (namedPermanent g1 "Red Goblin").id
  let elfId := (namedPermanent g1 "Red Elf").id
  let rAId := (namedPermanent g1 "Colorless Rock A").id
  let rBId := (namedPermanent g1 "Colorless Rock B").id
  let acId := (namedPermanent g1 "Artifact Construct").id
  let bearId := (namedPermanent g1 "Grizzly Bears").id
  -- 1a. `shareCharacteristic .color` (CR 105.2c: colorless never shares a color)
  let shareColorOk :=
    g1.satisfiesGroupConstraint p0 none (.shareCharacteristic .color) #[.permanent gobId, .permanent elfId] &&
    !g1.satisfiesGroupConstraint p0 none (.shareCharacteristic .color) #[.permanent rAId, .permanent rBId] &&
    !g1.satisfiesGroupConstraint p0 none (.shareCharacteristic .color) #[.permanent gobId, .permanent rAId]
  -- 1b. `shareCharacteristic .creatureType` & `.subtype`
  let redGoblin2 : CardDef :=
    creature "Red Goblin 2" { symbols := #[.colored .red] } #["Goblin"] 1 1
  let gSub := addPermanent g1 redGoblin2 p0 p0
  let gob2Id := (namedPermanent gSub "Red Goblin 2").id
  let shareSubtypeOk :=
    gSub.satisfiesGroupConstraint p0 none (.shareCharacteristic .creatureType) #[.permanent gobId, .permanent gob2Id] &&
    !gSub.satisfiesGroupConstraint p0 none (.shareCharacteristic .creatureType) #[.permanent gobId, .permanent elfId] &&
    gSub.satisfiesGroupConstraint p0 none (.shareCharacteristic .subtype) #[.permanent gobId, .permanent gob2Id]
  -- 1c. `distinctControllers`
  let distinctCtrlOk :=
    g1.satisfiesGroupConstraint p0 none .distinctControllers #[.permanent gobId, .permanent elfId] &&
    !g1.satisfiesGroupConstraint p0 none .distinctControllers #[.permanent gobId, .permanent bearId]
  -- 1d. `distinctNames` (including CR 201.2a nameless face-down permanents)
  let gName := addPermanent g1 grizzlyBears p1 p1
  let allBears := gName.battlefield.filter (·.name == "Grizzly Bears")
  let gFd :=
    insertObject (insertObject g0 grizzlyBears p0 .battlefield (some p0) { faceDown := true })
      grizzlyBears p1 .battlefield (some p1) { faceDown := true }
  let fdBears := gFd.battlefield.filter (·.status.faceDown)
  let distinctNameOk :=
    gName.satisfiesGroupConstraint p0 none .distinctNames #[.permanent gobId, .permanent bearId] &&
    !gName.satisfiesGroupConstraint p0 none .distinctNames #[.permanent allBears[0]!.id, .permanent allBears[1]!.id] &&
    gFd.satisfiesGroupConstraint p0 none .distinctNames #[.permanent fdBears[0]!.id, .permanent fdBears[1]!.id]
  -- 1e. `distinctCardTypes` (bipartite matching: Artifact Creature + Creature -> Artifact/Creature)
  let distinctTypesOk :=
    g1.satisfiesGroupConstraint p0 none .distinctCardTypes #[.permanent acId, .permanent bearId] &&
    g1.satisfiesGroupConstraint p0 none .distinctCardTypes #[.permanent acId, .permanent rAId] &&
    !g1.satisfiesGroupConstraint p0 none .distinctCardTypes #[.permanent rAId, .permanent rBId] &&
    !g1.satisfiesGroupConstraint p0 none .distinctCardTypes #[.permanent gobId, .permanent bearId]
  -- 2. CR 112.1 stack ability vs spell
  let (gSt1, spellObj) := g1.allocObject lightningBolt p1 .stack (some p1)
  let gSt1 := gSt1.change (.pushStack { objectId := spellObj.id, controller := p1, targets := #[] })
  let (gSt2, abObj) := gSt1.putStackAbility (gSt1.object! gobId) p0 (abilityEffect := some (Effect.abilityDraw 1))
  let stackSpells := gSt2.legalTargetsForSpec p0 .spell none
  let stackAbs := gSt2.legalTargetsForSpec p0 (.stackAbilityFromSource .creature) none
  let stackSepOk :=
    stackSpells.contains (.card spellObj.id) &&
    !stackSpells.contains (.card abObj.id) &&
    stackAbs.contains (.card abObj.id) &&
    !stackAbs.contains (.card spellObj.id)
  -- 3. CR 108.2 / 111.6 graveyard token exclusion
  let tokDef : CardDef := { grizzlyBears with name := "Bear Token", isToken := true }
  let gGy := insertObject (insertObject g0 grizzlyBears p0 (.graveyard p0)) tokDef p0 (.graveyard p0)
  let gyCardId := (gGy.objects.find? (fun o => o.zone == .graveyard p0 && o.name == "Grizzly Bears")).get!.id
  let gyTokId := (gGy.objects.find? (fun o => o.zone == .graveyard p0 && o.name == "Bear Token")).get!.id
  let gyLegal := gGy.legalTargetsForSpec p0 .creatureCardInYourGraveyard none
  let gyTokenExcludedOk :=
    gyLegal.contains (.card gyCardId) && !gyLegal.contains (.card gyTokId)
  -- 4. CR 115.4 `anyTarget` vs `anyOtherTarget`
  let anyLegal := g1.legalTargetsForSpec p0 .anyTarget (some gobId)
  let anyOtherLegal := g1.legalTargetsForSpec p0 .anyOtherTarget (some gobId)
  let anyTargetOk :=
    anyLegal.contains (.permanent gobId) &&
    anyLegal.contains (.player p1) &&
    !anyOtherLegal.contains (.permanent gobId) &&
    anyOtherLegal.contains (.permanent bearId) &&
    anyOtherLegal.contains (.player p1)
  -- 5. Layer-3 `HasTextChange TargetSpec` updates both legal targets and `ToOracle`
  let elfSpec : TargetSpec := .creatureYouControlSubtype .elf
  let tcSpec : TargetSpec := HasTextChange.applyTextChanges #[.replaceCreatureType .elf .goblin] elfSpec
  let gL3 := addPermanent (addPermanent g0 redElf p0 p0) redGoblin p0 p0
  let l3ElfId := (namedPermanent gL3 "Red Elf").id
  let l3GobId := (namedPermanent gL3 "Red Goblin").id
  let l3Legal := gL3.legalTargetsForSpec p0 tcSpec none
  let layer3Ok :=
    tcSpec.noun == "target Goblin you control" &&
    l3Legal.contains (.permanent l3GobId) &&
    !l3Legal.contains (.permanent l3ElfId)
  shareColorOk && shareSubtypeOk && distinctCtrlOk && distinctNameOk &&
    distinctTypesOk && stackSepOk && gyTokenExcludedOk && anyTargetOk && layer3Ok

-- Phase 3 review regression: CR 115.5 stack abilities and copies cannot target themselves,
-- while still keeping `sourceId` for `"another"` permanent exclusions.
#guard
  let p0 : PlayerId := ⟨0⟩
  let echoDef : CardDef := {
    creature "Echo Test" { symbols := #[.generic 2] } #["Human"] 2 2 with
    activatedAbilities := #[
      { cost := CostSpec.empty, effect := Effect.copyControlledAbility .creature },
      { cost := CostSpec.empty, effect := Effect.mkAbility .anotherCreature (Instruction.tap (.target 0)) }
    ]
  }
  let otherCreature : CardDef :=
    creature "Bear Source" { symbols := #[.generic 2] } #["Bear"] 2 2
  let g0 := readyMain (emptyHand afterDraw p0)
  let g1 := addPermanent (addPermanent g0 echoDef p0 p0) otherCreature p0 p0
  let echoId := (namedPermanent g1 "Echo Test").id
  let bearId := (namedPermanent g1 "Bear Source").id
  let (g2, ab0) := g1.putStackAbility (g1.object! bearId) p0 (abilityEffect := some (Effect.abilityDraw 1))
  -- 1. Activating Echo's copy ability puts `ab1` on the stack with `sourceId = some echoId`.
  --    CR 115.5: `ab1` cannot be offered or accepted as a target of itself.
  let gAct :=
    match g2.activateAbility p0 echoId 0 with
    | .ok g' => g'
    | .error e => panic! e
  let ab1Id := gAct.proposedSpell.get!.spellId
  let ab1Obj := gAct.object! ab1Id
  let proposedLegal := gAct.legalProposedTargets p0 ab1Obj
  let selfExcludedAtAnnounce :=
    proposedLegal.contains (.card ab0.id) &&
    !proposedLegal.contains (.card ab1Id) &&
    !(gAct.announceTarget p0 (.card ab1Id)).isOk
  let gAnnounced :=
    match gAct.announceTarget p0 (.card ab0.id) with
    | .ok g' => g'
    | .error e => panic! e
  -- 2. Copying `ab1` on the stack (CR 707.10c) keeps `sourceId = some echoId`,
  --    yet the copy (`copyId`) cannot target itself via `validTargetArrayForEntry`
  --    or `answerResolutionChoice (.newTargetsForCopies #[copyId])`, while `ab0`/`ab1` are legal.
  let (gCopied, copyId?) := gAnnounced.copyStackAbilityWithId (gAnnounced.object! ab1Id) p0
  let copyId := copyId?.get!
  let copyObj := gCopied.object! copyId
  let copyEntry := (gCopied.stackEntry? copyId).get!
  let copySpec := gCopied.targetSpecOf copyObj
  let copySelfExcluded :=
    !gCopied.validTargetArrayForEntry copyEntry copyObj copySpec #[.card copyId] (allowUnchangedIllegal := true) &&
    gCopied.validTargetArrayForEntry copyEntry copyObj copySpec #[.card ab0.id] (allowUnchangedIllegal := true) &&
    gCopied.validTargetArrayForEntry copyEntry copyObj copySpec #[.card ab1Id] (allowUnchangedIllegal := true)
  let gPrompt := gCopied.beginResolutionChoice p0 (.newTargetsForCopies #[copyId]) "Choose new target"
  let copyRetargetChoiceOk :=
    !(gPrompt.answerResolutionChoice p0 (.objects #[copyId])).isOk &&
    (gPrompt.answerResolutionChoice p0 (.objects #[ab1Id])).isOk
  -- 3. `sourceId` is still preserved for `"another"` when activating ability 1 (`anotherCreature`).
  let gAnother :=
    match g2.activateAbility p0 echoId 1 with
    | .ok g' => g'
    | .error e => panic! e
  let abAnother := gAnother.object! gAnother.proposedSpell.get!.spellId
  let anotherLegal := gAnother.legalProposedTargets p0 abAnother
  let anotherPreserved :=
    anotherLegal.contains (.permanent bearId) &&
    !anotherLegal.contains (.permanent echoId)
  selfExcludedAtAnnounce && copySelfExcluded && copyRetargetChoiceOk && anotherPreserved

-- Phase 3 review regression: `"for each player, ... that player controls"` parses with
-- `PlayerFilter.thatPlayer` (never `.seat 0`) and expands into one concrete slot per player
-- (including the caster), checking each player's seat independently.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  match Parser.parseTargetSpec "for each player, up to one target creature that player controls",
        Parser.parseTargetSpec "for each player, target creature that player controls" with
  | some optSpec, some reqSpec =>
    let optEff : Effect := { targets := optSpec, body := Instruction.tap (.target 0) }
    let reqEff : Effect := { targets := reqSpec, body := Instruction.tap (.target 0) }
    let g0 := readyMain (emptyHand afterDraw p0)
    let gOnlyP0 := addPermanent g0 grizzlyBears p0 p0
    let gBoth := addPermanent gOnlyP0 grizzlyBears p1 p1
    let p0Bear := (gBoth.permanentsOf p0)[0]!.id
    let p1Bear := (gBoth.permanentsOf p1)[0]!.id
    let expOpt := gBoth.expandEachOpponentEffect p0 optEff
    let expReq := gBoth.expandEachOpponentEffect p0 reqEff
    let slotsOk :=
      expOpt.targetSpec.slots.size == 2 &&
      expReq.targetSpec.slots.size == 2 &&
      expOpt.targetSpec.slots.all (·.forEach?.isNone) &&
      gBoth.legalTargetsForSlot p0 expReq.targetSpec.slots[0]! none == #[.permanent p0Bear] &&
      gBoth.legalTargetsForSlot p0 expReq.targetSpec.slots[1]! none == #[.permanent p1Bear]
    -- Mandatory `"for each player"` requires a legal target for BOTH `p0` and `p1`.
    let enoughTargetsOk :=
      !gOnlyP0.effectHasEnoughTargets p0 reqEff none &&
      gBoth.effectHasEnoughTargets p0 reqEff none &&
      gOnlyP0.effectHasEnoughTargets p0 optEff none
    -- Casting a spell with `reqEff` prompts slot 0 (`p0`'s creature), then slot 1 (`p1`'s creature).
    let spellCard : CardDef := {
      name := "Each Player Tap", types := #[.sorcery], spellAbility := some { effect := reqEff }}
    let (gHand, spellObj) := gBoth.allocObject spellCard p0 (.hand p0)
    let gCast :=
      match gHand.castSpell p0 spellObj.id with
      | .ok g' => g'
      | .error e => panic! e
    let stackSpell := gCast.object! gCast.proposedSpell.get!.spellId
    let slot0Legal := gCast.legalProposedTargets p0 stackSpell
    let gAfterSlot0 :=
      match gCast.announceTarget p0 (.permanent p0Bear) with
      | .ok g' => g'
      | .error e => panic! e
    let slot1Legal := gAfterSlot0.legalProposedTargets p0 (gAfterSlot0.object! stackSpell.id)
    let announceFlowOk :=
      slot0Legal == #[.permanent p0Bear] &&
      slot1Legal == #[.permanent p1Bear] &&
      (gAfterSlot0.announceTarget p0 (.permanent p1Bear)).isOk
    slotsOk && enoughTargetsOk && announceFlowOk
  | _, _ => false

end Mtg.Engine.Tests
