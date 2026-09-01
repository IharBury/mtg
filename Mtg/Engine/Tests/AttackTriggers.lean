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

/-!
# Attack triggers that copy P/T, grant trample, or scry.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Galion, Elvenking's Butler: attack trigger sets another creature's base P/T. -/

def galionAndElves : Game :=
  addPermanent (addPermanent started galionElvenkingsButler ⟨0⟩ ⟨0⟩) llanowarElves ⟨0⟩ ⟨0⟩

#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard galionAndElves.power (namedPermanent galionAndElves "Galion, Elvenking's Butler") == 4
#guard galionAndElves.power (namedPermanent galionAndElves "Llanowar Elves") == 1

def galionAttackDeclared : Game :=
  let g := passBoth (skipTo galionAndElves .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])

#guard galionAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard galionAttackDeclared.stack.size == 1
#guard (galionAttackDeclared.object! galionAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some .onAttackSetOtherBasePT
#guard galionAttackDeclared.stack.back!.targets.isEmpty
#guard !galionAttackDeclared.stack.back!.targetsAnnounced
#guard galionAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard galionAttackDeclared.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !galionAttackDeclared.hasPriority ⟨0⟩
#guard galionAttackDeclared.actor == some ⟨0⟩

-- Cannot target Galion himself, an opponent's creature, or a player.
#guard
  match galionAttackDeclared.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent galionAttackDeclared
        "Galion, Elvenking's Butler").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent galionAttackDeclared grizzlyBears ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match galionAttackDeclared.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets the other creature you control.
#guard
  match Agent.choose galionAttackDeclared ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (galionAttackDeclared.object! tid).name == "Llanowar Elves"
  | _ => false

def galionTargeted : Game :=
  mustApply galionAttackDeclared ⟨0⟩
    (.target (Target.permanent (namedPermanent galionAttackDeclared "Llanowar Elves").id))

#guard galionTargeted.pending == .none
#guard galionTargeted.hasPriority ⟨0⟩
#guard galionTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent galionTargeted "Llanowar Elves").id]
#guard galionTargeted.stack.back!.targetsAnnounced
#guard galionTargeted.log.any (fun s => mentions s "chooses Llanowar Elves as a target")

def galionResolved : Game := passBoth galionTargeted

#guard galionResolved.stack.isEmpty
#guard galionResolved.basePower (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.baseToughness (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.power (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.toughness (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.log.any (fun s =>
  mentions s "base power and toughness become 4/4 until end of turn")

/-- Counters on the target apply after the new base (CR 613.3c–d). -/
def galionOnCounteredElves : Game :=
  let g := galionAndElves
  let elves := namedPermanent g "Llanowar Elves"
  let g := g.setObject { elves with
    status := { elves.status with plusOnePlusOne := 1 } }
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Llanowar Elves").id))
  passBoth g

#guard galionOnCounteredElves.basePower (namedPermanent galionOnCounteredElves "Llanowar Elves") == 4
#guard galionOnCounteredElves.power (namedPermanent galionOnCounteredElves "Llanowar Elves") == 5
#guard (namedPermanent galionOnCounteredElves "Llanowar Elves").status.plusOnePlusOne == 1

/-- Uses Galion's actual P/T at resolution, including pumps (CR 613.3b ruling). -/
def galionPumpedResolved : Game :=
  let g := galionAndElves
  let g := g.applyEffect ⟨0⟩ (Effect.pump 2 2)
    #[Target.permanent (namedPermanent g "Galion, Elvenking's Butler").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Llanowar Elves").id))
  passBoth g

#guard galionPumpedResolved.power
  (namedPermanent galionPumpedResolved "Galion, Elvenking's Butler") == 6
#guard galionPumpedResolved.power (namedPermanent galionPumpedResolved "Llanowar Elves") == 6
#guard galionPumpedResolved.log.any (fun s =>
  mentions s "base power and toughness become 6/6 until end of turn")

/-- Later changes to Galion do not update the other creature. -/
def galionPumpedAfterResolve : Game :=
  galionResolved.applyEffect ⟨0⟩ (Effect.pump 3 0)
    #[Target.permanent (namedPermanent galionResolved "Galion, Elvenking's Butler").id]

#guard galionPumpedAfterResolve.power
  (namedPermanent galionPumpedAfterResolve "Galion, Elvenking's Butler") == 7
#guard galionPumpedAfterResolve.power
  (namedPermanent galionPumpedAfterResolve "Llanowar Elves") == 4

/-- Overwrites a “P/T equal to lands you control” CDA (layer 7b over 7a). -/
def galionOnPathmaker : Game :=
  let g := addForests afterDraw ⟨0⟩ 2
  let g := addPermanent g galionElvenkingsButler ⟨0⟩ ⟨0⟩
  let g := addPermanent g mirkwoodPathmaker ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Mirkwood Pathmaker").id))
  passBoth g

#guard galionOnPathmaker.power (namedPermanent galionOnPathmaker "Mirkwood Pathmaker") == 4
#guard galionOnPathmaker.basePower (namedPermanent galionOnPathmaker "Mirkwood Pathmaker") == 4

/-- The set effect wears off in cleanup; Pathmaker returns to land-count P/T. -/
def afterGalionCleanup : Game := passBoth (skipTo galionResolved .end 80)

#guard afterGalionCleanup.power (namedPermanent afterGalionCleanup "Llanowar Elves") == 1
#guard afterGalionCleanup.basePower (namedPermanent afterGalionCleanup "Llanowar Elves") == 1
#guard (namedPermanent afterGalionCleanup "Llanowar Elves").status.setBasePower.isNone

def afterGalionPathmakerCleanup : Game := passBoth (skipTo galionOnPathmaker .end 80)

#guard afterGalionPathmakerCleanup.power
  (namedPermanent afterGalionPathmakerCleanup "Mirkwood Pathmaker") == 2

/-- “Up to one”: declining leaves the other creature unchanged. -/
def galionDeclined : Game :=
  let g := mustApply galionAttackDeclared ⟨0⟩ .decline
  passBoth g

#guard galionDeclined.stack.isEmpty
#guard galionDeclined.power (namedPermanent galionDeclined "Llanowar Elves") == 1
#guard galionDeclined.log.any (fun s => mentions s "chooses no target")
#guard galionDeclined.log.any (fun s => mentions s "No target was chosen")

/-- No other creature you control: the trigger still goes on the stack (CR 603.3d). -/
def galionAloneDeclared : Game :=
  let g := addPermanent started galionElvenkingsButler ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])

#guard galionAloneDeclared.pending == .chooseTargets ⟨0⟩
#guard galionAloneDeclared.stack.size == 1
#guard (galionAloneDeclared.legalProposedTargets ⟨0⟩
  (galionAloneDeclared.object! galionAloneDeclared.stack.back!.objectId)).isEmpty
#guard
  match Agent.choose galionAloneDeclared ⟨0⟩ with
  | some .decline => true
  | _ => false

def galionAloneResolved : Game :=
  let g := mustApply galionAloneDeclared ⟨0⟩ .decline
  passBoth g

#guard galionAloneResolved.stack.isEmpty
#guard galionAloneResolved.log.any (fun s => mentions s "chooses no target")

/-- Last known P/T if Galion leaves before resolution (CR 113.7a). -/
def galionSourceGone : Game :=
  let g := galionTargeted
  let id := (namedPermanent g "Galion, Elvenking's Butler").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard galionSourceGone.stack.isEmpty
#guard !(galionSourceGone.battlefield.any (fun o => o.name == "Galion, Elvenking's Butler"))
#guard galionSourceGone.power (namedPermanent galionSourceGone "Llanowar Elves") == 4
#guard galionSourceGone.log.any (fun s =>
  mentions s "base power and toughness become 4/4 until end of turn")

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def galionTargetGone : Game :=
  let id := (namedPermanent galionTargeted "Llanowar Elves").id
  let (g, _) := galionTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard galionTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(galionTargetGone.battlefield.any (fun o => o.name == "Llanowar Elves"))

/- Oliphaunt: attack trigger pumps another creature you control and grants trample. -/

def oliphauntAndOgre : Game :=
  addPermanent (addPermanent started oliphaunt ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphauntAndOgre.hasTrample (namedPermanent oliphauntAndOgre "Oliphaunt")
#guard !oliphauntAndOgre.hasTrample (namedPermanent oliphauntAndOgre "Gray Ogre")
#guard oliphauntAndOgre.power (namedPermanent oliphauntAndOgre "Gray Ogre") == 2

def oliphauntAttackDeclared : Game :=
  let g := passBoth (skipTo oliphauntAndOgre .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Oliphaunt").id])

#guard oliphauntAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard oliphauntAttackDeclared.stack.size == 1
#guard (oliphauntAttackDeclared.object! oliphauntAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some .onAttackOtherGets2AndTrample
#guard oliphauntAttackDeclared.stack.back!.targets.isEmpty
#guard !oliphauntAttackDeclared.stack.back!.targetsAnnounced
#guard oliphauntAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard oliphauntAttackDeclared.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !oliphauntAttackDeclared.hasPriority ⟨0⟩
#guard oliphauntAttackDeclared.actor == some ⟨0⟩

-- Cannot target Oliphaunt himself, an opponent's creature, or a player.
#guard
  match oliphauntAttackDeclared.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent oliphauntAttackDeclared "Oliphaunt").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent oliphauntAttackDeclared grizzlyBears ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match oliphauntAttackDeclared.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The trigger is not optional: decline is illegal when a target is required.
#guard
  match oliphauntAttackDeclared.apply ⟨0⟩ .decline with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- The heuristic targets the other creature you control.
#guard
  match Agent.choose oliphauntAttackDeclared ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (oliphauntAttackDeclared.object! tid).name == "Gray Ogre"
  | _ => false

def oliphauntTargeted : Game :=
  mustApply oliphauntAttackDeclared ⟨0⟩
    (.target (Target.permanent (namedPermanent oliphauntAttackDeclared "Gray Ogre").id))

#guard oliphauntTargeted.pending == .none
#guard oliphauntTargeted.hasPriority ⟨0⟩
#guard oliphauntTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent oliphauntTargeted "Gray Ogre").id]
#guard oliphauntTargeted.stack.back!.targetsAnnounced
#guard oliphauntTargeted.log.any (fun s => mentions s "chooses Gray Ogre as a target")

def oliphauntResolved : Game := passBoth oliphauntTargeted

#guard oliphauntResolved.stack.isEmpty
#guard oliphauntResolved.power (namedPermanent oliphauntResolved "Gray Ogre") == 4
#guard oliphauntResolved.toughness (namedPermanent oliphauntResolved "Gray Ogre") == 2
#guard oliphauntResolved.hasTrample (namedPermanent oliphauntResolved "Gray Ogre")
#guard (oliphauntResolved.effectiveKeywords
  (namedPermanent oliphauntResolved "Gray Ogre")).trample
#guard oliphauntResolved.log.any (fun s =>
  mentions s "gets +2/+0 and gains trample until end of turn")

-- Pump stacks with printed power; Oliphaunt itself is unchanged.
#guard oliphauntResolved.power (namedPermanent oliphauntResolved "Oliphaunt") == 6
#guard oliphauntResolved.hasTrample (namedPermanent oliphauntResolved "Oliphaunt")

/-- The pump and granted trample wear off in cleanup. -/
def afterOliphauntCleanup : Game := passBoth (skipTo oliphauntResolved .end 80)

#guard afterOliphauntCleanup.power (namedPermanent afterOliphauntCleanup "Gray Ogre") == 2
#guard !afterOliphauntCleanup.hasTrample (namedPermanent afterOliphauntCleanup "Gray Ogre")
#guard afterOliphauntCleanup.hasTrample (namedPermanent afterOliphauntCleanup "Oliphaunt")

/-- Granted trample assigns leftover combat damage (4/2 Ogre vs 1/1 Elves). -/
def oliphauntBothAttackDeclared : Game :=
  let g := passBoth (skipTo oliphauntAndOgre .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[
    (namedPermanent g "Oliphaunt").id,
    (namedPermanent g "Gray Ogre").id])

def oliphauntBothResolved : Game :=
  let g := mustApply oliphauntBothAttackDeclared ⟨0⟩
    (.target (Target.permanent (namedPermanent oliphauntBothAttackDeclared "Gray Ogre").id))
  passBoth g

#guard oliphauntBothResolved.power (namedPermanent oliphauntBothResolved "Gray Ogre") == 4
#guard oliphauntBothResolved.hasTrample (namedPermanent oliphauntBothResolved "Gray Ogre")
#guard (namedPermanent oliphauntBothResolved "Gray Ogre").status.attacking
#guard (namedPermanent oliphauntBothResolved "Oliphaunt").status.attacking

def afterOliphauntTrampleCombat : Game :=
  let g := addPermanent oliphauntBothResolved llanowarElves ⟨1⟩ ⟨1⟩
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard afterOliphauntTrampleCombat.log.any (fun s =>
  mentions s "Gray Ogre deals 1 combat damage to Llanowar Elves")
#guard afterOliphauntTrampleCombat.log.any (fun s =>
  mentions s "Gray Ogre tramples for 3 to Nissa")
#guard afterOliphauntTrampleCombat.log.any (fun s =>
  mentions s "Oliphaunt deals 6 combat damage to Nissa")
#guard (afterOliphauntTrampleCombat.player ⟨1⟩).life == 11

/-- Without the trigger, the same Ogre assigns all damage to the blocker. -/
def ogreOnlyVsElves : Game :=
  addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def afterOgreNoGrantedTrample : Game :=
  let g := passBoth (skipTo ogreOnlyVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard afterOgreNoGrantedTrample.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Llanowar Elves")
#guard !afterOgreNoGrantedTrample.log.any (fun s => mentions s "tramples")
#guard (afterOgreNoGrantedTrample.player ⟨1⟩).life == 20

/-- No other creature you control: the trigger is removed (CR 603.3d). -/
def oliphauntAloneDeclared : Game :=
  let g := addPermanent started oliphaunt ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Oliphaunt").id])

#guard oliphauntAloneDeclared.stack.isEmpty
#guard oliphauntAloneDeclared.pending == .none
#guard oliphauntAloneDeclared.hasPriority ⟨0⟩
#guard oliphauntAloneDeclared.log.any (fun s => mentions s "no legal target")

/-- The effect does not depend on Oliphaunt remaining in play. -/
def oliphauntSourceGone : Game :=
  let g := oliphauntTargeted
  let id := (namedPermanent g "Oliphaunt").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard oliphauntSourceGone.stack.isEmpty
#guard !(oliphauntSourceGone.battlefield.any (fun o => o.name == "Oliphaunt"))
#guard oliphauntSourceGone.power (namedPermanent oliphauntSourceGone "Gray Ogre") == 4
#guard oliphauntSourceGone.hasTrample (namedPermanent oliphauntSourceGone "Gray Ogre")
#guard oliphauntSourceGone.log.any (fun s =>
  mentions s "gets +2/+0 and gains trample until end of turn")

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def oliphauntTargetGone : Game :=
  let id := (namedPermanent oliphauntTargeted "Gray Ogre").id
  let (g, _) := oliphauntTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard oliphauntTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(oliphauntTargetGone.battlefield.any (fun o => o.name == "Gray Ogre"))

/- Lothlórien Lookout: attack trigger scries 1 (CR 508.2 / 701.20). -/

#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard lothlorienLookout.power == some 1
#guard lothlorienLookout.toughness == some 3

def lookoutOnBattlefield : Game :=
  addPermanent started lothlorienLookout ⟨0⟩ ⟨0⟩

#guard lookoutOnBattlefield.power (namedPermanent lookoutOnBattlefield "Lothlórien Lookout") == 1
#guard lookoutOnBattlefield.toughness (namedPermanent lookoutOnBattlefield "Lothlórien Lookout") == 3

def lookoutAttackDeclared : Game :=
  let g := passBoth (skipTo lookoutOnBattlefield .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Lothlórien Lookout").id])

#guard lookoutAttackDeclared.stack.size == 1
#guard (lookoutAttackDeclared.object! lookoutAttackDeclared.stack.back!.objectId).name ==
  "Lothlórien Lookout's ability"
#guard (lookoutAttackDeclared.object! lookoutAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackScry 1)
#guard (lookoutAttackDeclared.object! lookoutAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent lookoutAttackDeclared "Lothlórien Lookout").id
#guard lookoutAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard lookoutAttackDeclared.step == .declareAttackers
#guard lookoutAttackDeclared.hasPriority ⟨0⟩
#guard (namedPermanent lookoutAttackDeclared "Lothlórien Lookout").status.attacking

def lookoutScrying : Game := passBoth lookoutAttackDeclared

#guard
  match lookoutScrying.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard lookoutScrying.actor == some ⟨0⟩
#guard !lookoutScrying.hasPriority ⟨0⟩
#guard lookoutScrying.log.any (fun s => mentions s "scries 1")
#guard lookoutScrying.stack.isEmpty
#guard lookoutScrying.battlefield.any (fun o => o.name == "Lothlórien Lookout")

def lookoutScried : Game := keepScry lookoutScrying

#guard lookoutScried.pending == .none
#guard lookoutScried.hasPriority ⟨0⟩
#guard lookoutScried.battlefield.any (fun o => o.name == "Lothlórien Lookout")

-- The agent keeps scried cards on top.
#guard
  match Agent.choose lookoutScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == lookoutScrying.scryLookedIds ⟨0⟩ 1
  | _ => false

/-- Known library: Forest on top; scry 1 looks at that card. -/
def lookoutKnownLib : Game :=
  addToLibraryTop lookoutAttackDeclared forest ⟨0⟩

def lookoutKnownScrying : Game := passBoth lookoutKnownLib

#guard
  let looked := lookoutKnownScrying.scryLookedIds ⟨0⟩ 1
  looked.size == 1 &&
    (lookoutKnownScrying.object! looked[0]!).name == "Forest"

def lookoutForestToBottom : Game :=
  let looked := lookoutKnownScrying.scryLookedIds ⟨0⟩ 1
  mustApply lookoutKnownScrying ⟨0⟩ (.scry #[] looked)

#guard
  let lib := (lookoutForestToBottom.player ⟨0⟩).library
  lib.size == (lookoutKnownScrying.player ⟨0⟩).library.size &&
    (lookoutForestToBottom.object! lib[0]!).name == "Forest"
#guard lookoutForestToBottom.log.any (fun s =>
  mentions s "puts Forest on the bottom of their library")

/-- The trigger still scries if Lothlórien Lookout has left the battlefield (CR 113.7a). -/
def lookoutLeftBeforeTrigger : Game :=
  let id := (namedPermanent lookoutKnownLib "Lothlórien Lookout").id
  let (g, _) := lookoutKnownLib.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard
  match lookoutLeftBeforeTrigger.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard !(lookoutLeftBeforeTrigger.battlefield.any (fun o => o.name == "Lothlórien Lookout"))
#guard (lookoutLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (lookoutLeftBeforeTrigger.object! id).name == "Lothlórien Lookout")
#guard
  let looked := lookoutLeftBeforeTrigger.scryLookedIds ⟨0⟩ 1
  looked.size == 1 &&
    (lookoutLeftBeforeTrigger.object! looked[0]!).name == "Forest"

/-- Another creature attacking does not trigger Lothlórien Lookout. -/
def lookoutIdleWhileBearsAttack : Game :=
  let g := addPermanent lookoutOnBattlefield grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])

#guard lookoutIdleWhileBearsAttack.stack.isEmpty
#guard !lookoutIdleWhileBearsAttack.log.any (fun s => mentions s "attack trigger")
#guard (namedPermanent lookoutIdleWhileBearsAttack "Grizzly Bears").status.attacking
#guard !(namedPermanent lookoutIdleWhileBearsAttack "Lothlórien Lookout").status.attacking

/-- Entering the battlefield does not scry. -/
def lookoutSetup : Game :=
  withGreenMana (addToHand afterDraw lothlorienLookout ⟨0⟩) ⟨0⟩ 2

#guard lookoutSetup.canCast ⟨0⟩ (handCardNamed lookoutSetup ⟨0⟩ "Lothlórien Lookout")
#guard lookoutSetup.asSorcery? ⟨0⟩

def lookoutEntered : Game :=
  let g := mustApply lookoutSetup ⟨0⟩
    (.cast (handCardNamed lookoutSetup ⟨0⟩ "Lothlórien Lookout").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard lookoutEntered.stack.isEmpty
#guard lookoutEntered.pending == .none
#guard lookoutEntered.battlefield.any (fun o => o.name == "Lothlórien Lookout")
#guard !lookoutEntered.log.any (fun s => mentions s "scries")
#guard !lookoutEntered.log.any (fun s => mentions s "enters trigger")

end Mtg.Engine.Tests
