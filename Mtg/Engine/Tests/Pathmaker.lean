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
import Mtg.Engine.Tests.Equipment
import Mtg.Engine.Tests.Elves

/-!
# Mana-payment heuristics and characteristic-defining P/T.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Forest is listed before the Mountain, so a greedy tap would waste it on `{R}`. -/
def forestFirstBolt : Game :=
  let g := addUntappedLand started forest
  let g := addToHand (addUntappedLand g mountain) lightningBolt ⟨0⟩
  proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Lightning Bolt").id (Target.player ⟨1⟩)

#guard
  let sources := forestFirstBolt.manaSources ⟨0⟩
  sources.size == 2 && sources[0]!.1.name == "Forest"

#guard
  match Agent.chooseManaPayment forestFirstBolt ⟨0⟩ with
  | some (.tapForMana id (.colored .red)) =>
    (forestFirstBolt.object! id).name == "Mountain"
  | _ => false

/-- Weavemaster's Elf-only mana cannot pay Giant Growth; the Forest can. -/
def weavemasterForestGrowth : Game :=
  let g := addUntappedLand weavemasterReady forest
  let g := addToHand g giantGrowth ⟨0⟩
  proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Woodland Weavemaster").id)

#guard
  match weavemasterForestGrowth.proposedSpell with
  | some prop =>
    let sources := weavemasterForestGrowth.manaSourcesForProposed ⟨0⟩ prop
    sources.size == 1 && sources[0]!.1.name == "Forest"
  | none => false

#guard
  match Agent.chooseManaPayment weavemasterForestGrowth ⟨0⟩ with
  | some (.tapForMana id (.colored .green)) =>
    (weavemasterForestGrowth.object! id).name == "Forest"
  | _ => false

/-- Delighted Halfling's colored mana is legendary-only; Giant Growth is not. -/
def delightedHalflingForestGrowth : Game :=
  let g := addPermanent afterDraw delightedHalfling ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g forest
  let g := addToHand g giantGrowth ⟨0⟩
  proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Delighted Halfling").id)

#guard
  match delightedHalflingForestGrowth.proposedSpell with
  | some prop =>
    let sources := delightedHalflingForestGrowth.manaSourcesForProposed ⟨0⟩ prop
    let half := sources.find? (fun (o, _) => o.name == "Delighted Halfling")
    let forestSrc := sources.find? (fun (o, _) => o.name == "Forest")
    half.any (fun (_, types) =>
      types.size == 1 && types.contains .colorless) &&
      forestSrc.any (fun (_, types) => types.contains (.colored .green))
  | none => false

#guard
  match Agent.chooseManaPayment delightedHalflingForestGrowth ⟨0⟩ with
  | some (.tapForMana id (.colored .green)) =>
    (delightedHalflingForestGrowth.object! id).name == "Forest"
  | _ => false

/-- With only legendary-restricted colored mana, do not tap Halfling for `{G}`. -/
def delightedHalflingGrowth : Game :=
  let g := addPermanent afterDraw delightedHalfling ⟨0⟩ ⟨0⟩
  let g := addToHand g giantGrowth ⟨0⟩
  proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Delighted Halfling").id)

#guard
  match Agent.chooseManaPayment delightedHalflingGrowth ⟨0⟩ with
  | some .pay =>
    !(namedPermanent delightedHalflingGrowth "Delighted Halfling").status.tapped
  | _ => false

/-- Halfling may tap for colored mana when the pending spell is legendary. -/
def delightedHalflingCeleborn : Game :=
  let g := addPermanent afterDraw delightedHalfling ⟨0⟩ ⟨0⟩
  let g := addToHand g celebornTheWise ⟨0⟩
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Celeborn the Wise").id)

#guard
  match delightedHalflingCeleborn.proposedSpell with
  | some prop =>
    delightedHalflingCeleborn.proposedAllowsLegendaryRestricted prop &&
      (delightedHalflingCeleborn.manaSourcesForProposed ⟨0⟩ prop).any (fun (o, types) =>
        o.name == "Delighted Halfling" && types.contains (.colored .green))
  | none => false

#guard
  match Agent.chooseManaPayment delightedHalflingCeleborn ⟨0⟩ with
  | some (.tapForMana id (.colored .green)) =>
    (delightedHalflingCeleborn.object! id).name == "Delighted Halfling"
  | _ => false

/-- Llanowar Elves is listed before the Forest; autopay should still tap the
land and leave the creature untapped. -/
def elvesFirstGrowth : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g forest
  let g := addToHand g giantGrowth ⟨0⟩
  proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Llanowar Elves").id)

#guard
  let sources := elvesFirstGrowth.manaSources ⟨0⟩
  sources.size == 2 && sources[0]!.1.name == "Llanowar Elves"

#guard
  match Agent.chooseManaPayment elvesFirstGrowth ⟨0⟩ with
  | some (.tapForMana id (.colored .green)) =>
    (elvesFirstGrowth.object! id).name == "Forest"
  | _ => false

/-- Mountain is listed before Rogue's Passage; `{2}` can use colorless, so
tap the Passage first and leave the Mountain. -/
def mountainThenPassageBauble : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g roguesPassage ⟨0⟩ ⟨0⟩
  let g := addPermanent g wayfarersBauble ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  mustApply g ⟨0⟩ (.activate (namedPermanent g "Wayfarer's Bauble").id 0)

#guard
  match mountainThenPassageBauble.proposedSpell with
  | some prop =>
    let sources := mountainThenPassageBauble.manaSourcesForProposed ⟨0⟩ prop
    sources.size == 2 && sources[0]!.1.name == "Mountain"
  | none => false

#guard
  match Agent.chooseManaPayment mountainThenPassageBauble ⟨0⟩ with
  | some (.tapForMana id .colorless) =>
    (mountainThenPassageBauble.object! id).name == "Rogue's Passage"
  | _ => false

/-- A source that lists green before colorless still taps for `{C}` when the
remaining cost is generic. -/
def greenThenColorlessLand : CardDef :=
  land "Silent Caves" "{T}: Add {C} or {G}."
    (tapAddOneOf := #[.colored .green, .colorless])

def silentCavesReady : Game :=
  addPermanent afterDraw greenThenColorlessLand ⟨0⟩ ⟨0⟩

#guard
  let src := namedPermanent silentCavesReady "Silent Caves"
  let types := silentCavesReady.manaAbilitiesOf src
  types[0]? == some (.colored .green) &&
    silentCavesReady.preferredManaType ⟨0⟩ src types (ManaCost.ofGeneric 1)
      false false == some .colorless &&
    silentCavesReady.preferredManaType ⟨0⟩ src types (ManaCost.ofColor .green)
      false false == some (.colored .green)

/-- Island `{U}` plus Mountain `{R}` pays `{1}{U}` (generic after colored). -/
def islandMountainApothecary : Game :=
  let g := addUntappedLand afterDraw island
  let g := addToHand (addUntappedLand g mountain) lakeshoreApothecaryCard ⟨0⟩
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Lakeshore Apothecary").id)

#guard
  match islandMountainApothecary.proposedSpell with
  | some prop =>
    let avail := islandMountainApothecary.availableMana ⟨0⟩
    toString avail == "{U}×1 {R}×1" && avail.canPay prop.cost &&
      prop.cost == ManaCost.ofGenericAndColor 1 .blue
  | none => false

#guard
  match Agent.chooseManaPayment islandMountainApothecary ⟨0⟩ with
  | some (.tapForMana id (.colored .blue)) =>
    (islandMountainApothecary.object! id).name == "Island"
  | _ => false

def islandTappedForApothecary : Game :=
  mustApply islandMountainApothecary ⟨0⟩
    (.tapForMana (namedPermanent islandMountainApothecary "Island").id (.colored .blue))

#guard
  match Agent.chooseManaPayment islandTappedForApothecary ⟨0⟩ with
  | some (.tapForMana id (.colored .red)) =>
    (islandTappedForApothecary.object! id).name == "Mountain"
  | _ => false

def bothTappedForApothecary : Game :=
  mustApply islandTappedForApothecary ⟨0⟩
    (.tapForMana (namedPermanent islandTappedForApothecary "Mountain").id (.colored .red))

#guard
  let pool := (bothTappedForApothecary.player ⟨0⟩).manaPool
  toString pool == "{U}×1 {R}×1" &&
    pool.canPay (ManaCost.ofGenericAndColor 1 .blue)

#guard
  match Agent.chooseManaPayment bothTappedForApothecary ⟨0⟩ with
  | some .pay => true
  | _ => false

/- Mirkwood Pathmaker: power and toughness equal lands you control in all
zones (CR 208.2a / 604.3). -/

#guard mirkwoodPathmaker.staticAbilities == #[.powerToughnessEqualLandsYouControl]
#guard mirkwoodPathmaker.power.isNone
#guard mirkwoodPathmaker.toughness.isNone
#guard mentions mirkwoodPathmaker.summary "*/*"

#guard pathmakerWithLands.power (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.toughness
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.basePower
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.snapshotPower
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.snapshotToughness
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard (namedPermanent pathmakerWithLands "Mirkwood Pathmaker").power == 0
#guard pathmakerWithLands.landsYouControl ⟨0⟩ == 2

/-- Opponent lands do not count. -/
def pathmakerOppLands : Game :=
  addPermanent (addForests pathmakerWithLands ⟨1⟩ 5) grayOgre ⟨1⟩ ⟨1⟩

#guard pathmakerOppLands.power (namedPermanent pathmakerOppLands "Mirkwood Pathmaker") == 2
#guard pathmakerOppLands.landsYouControl ⟨1⟩ == 5

/-- A stolen Pathmaker uses its controller's lands (CR 109.5). -/
def stolenPathmaker : Game :=
  let g := addForests afterDraw ⟨0⟩ 3
  let g := addForests g ⟨1⟩ 1
  addPermanent g mirkwoodPathmaker ⟨0⟩ ⟨1⟩

#guard stolenPathmaker.power (namedPermanent stolenPathmaker "Mirkwood Pathmaker") == 1
#guard (namedPermanent stolenPathmaker "Mirkwood Pathmaker").owner == ⟨0⟩
#guard (namedPermanent stolenPathmaker "Mirkwood Pathmaker").controller == some ⟨1⟩

/-- The CDA functions in hand, graveyard, and on the stack (CR 604.3). -/
def pathmakerInHand : Game :=
  addToHand (addForests afterDraw ⟨0⟩ 2) mirkwoodPathmaker ⟨0⟩

#guard pathmakerInHand.power (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker") == 2
#guard pathmakerInHand.toughness (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker") == 2
#guard (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker").controller.isNone
#guard (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker").you == ⟨0⟩

def pathmakerInGraveyard : Game :=
  addToGraveyard (addForests afterDraw ⟨0⟩ 3) mirkwoodPathmaker ⟨0⟩

#guard pathmakerInGraveyard.power
  (namedGraveyardCard pathmakerInGraveyard ⟨0⟩ "Mirkwood Pathmaker") == 3
#guard pathmakerInGraveyard.toughness
  (namedGraveyardCard pathmakerInGraveyard ⟨0⟩ "Mirkwood Pathmaker") == 3

/-- Mirkwood Pathmaker in hand with two Forests in play and enough mana. -/
def pathmakerSetup : Game :=
  withGreenMana (addToHand (addForests afterDraw ⟨0⟩ 2) mirkwoodPathmaker ⟨0⟩) ⟨0⟩ 3

#guard pathmakerSetup.canCast ⟨0⟩ (handCardNamed pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker")
#guard pathmakerSetup.asSorcery? ⟨0⟩
#guard mirkwoodPathmaker.hasSorcerySpeed
#guard pathmakerSetup.power (handCardNamed pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker") == 2

def proposedPathmaker : Game :=
  mustApply pathmakerSetup ⟨0⟩ (.cast (handCardNamed pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker").id)

#guard proposedPathmaker.pending == .activateManaAbilities ⟨0⟩
#guard proposedPathmaker.log.any (fun s => mentions s "begins casting Mirkwood Pathmaker")

def paidPathmaker : Game := mustApply proposedPathmaker ⟨0⟩ .pay

#guard paidPathmaker.stack.size == 1
#guard paidPathmaker.hasPriority ⟨0⟩
#guard paidPathmaker.power (paidPathmaker.object! paidPathmaker.stack.back!.objectId) == 2
#guard (paidPathmaker.object! paidPathmaker.stack.back!.objectId).controller == some ⟨0⟩
#guard paidPathmaker.log.any (fun s => mentions s "casts Mirkwood Pathmaker")

def pathmakerEntered : Game := passBoth paidPathmaker

#guard pathmakerEntered.stack.isEmpty
#guard pathmakerEntered.power (namedPermanent pathmakerEntered "Mirkwood Pathmaker") == 2
#guard pathmakerEntered.toughness (namedPermanent pathmakerEntered "Mirkwood Pathmaker") == 2
#guard (namedPermanent pathmakerEntered "Mirkwood Pathmaker").status.summoningSick
#guard !(pathmakerEntered.canAttack (namedPermanent pathmakerEntered "Mirkwood Pathmaker"))
#guard pathmakerEntered.log.any (fun s => mentions s "enters the battlefield")

/-- 0/0 Pathmaker dies (CR 704.5f). -/
def pathmakerZeroLands : Game :=
  (addPermanent afterDraw mirkwoodPathmaker ⟨0⟩ ⟨0⟩).checkSBA

#guard !(pathmakerZeroLands.battlefield.any (fun o => o.name == "Mirkwood Pathmaker"))
#guard pathmakerZeroLands.log.any (fun s => mentions s "dies (toughness 0)")

/-- Casting with no lands also dies on resolution. -/
def pathmakerEntersZero : Game :=
  let g := withGreenMana (addToHand afterDraw mirkwoodPathmaker ⟨0⟩) ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Pathmaker").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard !(pathmakerEntersZero.battlefield.any (fun o => o.name == "Mirkwood Pathmaker"))
#guard pathmakerEntersZero.log.any (fun s => mentions s "dies (toughness 0)")

/-- Playing a land updates P/T immediately (continuous effect). -/
def pathmakerGrowsWithLand : Game :=
  let g := addToHand pathmakerWithLands forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard pathmakerGrowsWithLand.power
  (namedPermanent pathmakerGrowsWithLand "Mirkwood Pathmaker") == 3
#guard pathmakerGrowsWithLand.toughness
  (namedPermanent pathmakerGrowsWithLand "Mirkwood Pathmaker") == 3
#guard pathmakerGrowsWithLand.landsYouControl ⟨0⟩ == 3

/-- Pumps, counters, lords, and Auras apply on top of the land-count base. -/
def pathmakerPumped : Game :=
  pathmakerWithLands.applyEffect ⟨0⟩ (Effect.pump 2 2)
    #[Target.permanent (namedPermanent pathmakerWithLands "Mirkwood Pathmaker").id]

#guard pathmakerPumped.power (namedPermanent pathmakerPumped "Mirkwood Pathmaker") == 4
#guard pathmakerPumped.basePower (namedPermanent pathmakerPumped "Mirkwood Pathmaker") == 2
#guard pathmakerPumped.toughness (namedPermanent pathmakerPumped "Mirkwood Pathmaker") == 4

def pathmakerWithCounter : Game :=
  let o := namedPermanent pathmakerWithLands "Mirkwood Pathmaker"
  pathmakerWithLands.setObject { o with
    status := { o.status with plusOnePlusOne := 1 } }

#guard pathmakerWithCounter.power
  (namedPermanent pathmakerWithCounter "Mirkwood Pathmaker") == 3
#guard pathmakerWithCounter.basePower
  (namedPermanent pathmakerWithCounter "Mirkwood Pathmaker") == 2

def pathmakerWithArchdruid : Game :=
  addPermanent pathmakerWithLands elvishArchdruid ⟨0⟩ ⟨0⟩

#guard pathmakerWithArchdruid.power
  (namedPermanent pathmakerWithArchdruid "Mirkwood Pathmaker") == 3
#guard pathmakerWithArchdruid.toughness
  (namedPermanent pathmakerWithArchdruid "Mirkwood Pathmaker") == 3
#guard pathmakerWithArchdruid.basePower
  (namedPermanent pathmakerWithArchdruid "Mirkwood Pathmaker") == 2

def pathmakerWithGift : Game :=
  let host := namedPermanent pathmakerWithLands "Mirkwood Pathmaker"
  addAttachedAura pathmakerWithLands giftOfStrands host ⟨0⟩ ⟨0⟩

#guard pathmakerWithGift.power (namedPermanent pathmakerWithGift "Mirkwood Pathmaker") == 5
#guard pathmakerWithGift.toughness
  (namedPermanent pathmakerWithGift "Mirkwood Pathmaker") == 5
#guard pathmakerWithGift.basePower (namedPermanent pathmakerWithGift "Mirkwood Pathmaker") == 2

/-- Combat uses the land-count power. -/
def afterPathmakerCombat : Game :=
  let g := passBoth (skipTo pathmakerWithLands .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Mirkwood Pathmaker").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterPathmakerCombat.log.any (fun s =>
  mentions s "Mirkwood Pathmaker deals 2 combat damage to Nissa")
#guard (afterPathmakerCombat.player ⟨1⟩).life == 18

/-- Returning Pathmaker from the graveyard gains life equal to its CDA power. -/
def elkReturnsPathmakerEntered : Game :=
  let g := addToGraveyard (addForests afterDraw ⟨0⟩ 2) mirkwoodPathmaker ⟨0⟩
  let g := withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

def elkReturnsPathmaker : Game :=
  let g := mustApply elkReturnsPathmakerEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkReturnsPathmakerEntered ⟨0⟩
      "Mirkwood Pathmaker").id))
  passBoth g

#guard (elkReturnsPathmaker.player ⟨0⟩).life == 22
#guard (elkReturnsPathmaker.handObjects ⟨0⟩).any (fun o => o.name == "Mirkwood Pathmaker")
#guard elkReturnsPathmaker.power
  (handCardNamed elkReturnsPathmaker ⟨0⟩ "Mirkwood Pathmaker") == 2
#guard elkReturnsPathmaker.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")

/-- The heuristic casts Pathmaker when it is the playable creature. -/
def agentPathmaker : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addForests g ⟨0⟩ 2
  withGreenMana (addToHand g mirkwoodPathmaker ⟨0⟩) ⟨0⟩ 3

#guard
  match Agent.choose agentPathmaker ⟨0⟩ with
  | some (.cast id) => (agentPathmaker.object! id).name == "Mirkwood Pathmaker"
  | _ => false

end Mtg.Engine.Tests
