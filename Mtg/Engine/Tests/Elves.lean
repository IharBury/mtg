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
# Elf lords, scry pumps, and restricted-mana abilities.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Elvish Archdruid: other Elves get +1/+1, and `{T}: Add {G}` per Elf. -/

def archAndElves : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) llanowarElves ⟨0⟩ ⟨0⟩

def archAndBears : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) grizzlyBears ⟨0⟩ ⟨0⟩

def archAndOppElves : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def archAlone : Game := addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩

#guard archAndElves.power (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.toughness (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.snapshotPower (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.snapshotToughness (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.power (namedPermanent archAndElves "Elvish Archdruid") == 2
#guard archAndElves.toughness (namedPermanent archAndElves "Elvish Archdruid") == 2
#guard (namedPermanent archAndElves "Llanowar Elves").status.pumpPower == 0
#guard archAndBears.power (namedPermanent archAndBears "Grizzly Bears") == 2
#guard archAndOppElves.power (namedPermanent archAndOppElves "Llanowar Elves") == 1
#guard archAlone.power (namedPermanent archAlone "Elvish Archdruid") == 2
#guard archAndElves.countSubtype ⟨0⟩ "Elf" == 2
#guard archAndElves.countCreaturesControlledBy ⟨0⟩ == 2
#guard archAndOppElves.countCreaturesControlledBy ⟨0⟩ == 1
#guard (archAndElves.pickTeamworkCreatures ⟨0⟩ 2).size == 1
#guard (archAndElves.pickTeamworkCreatures ⟨0⟩ 3).size == 2
#guard (archAndElves.availableMana ⟨0⟩).green == 3
#guard (archAlone.availableMana ⟨0⟩).green == 1
#guard (archAndOppElves.availableMana ⟨0⟩).green == 1
#guard (archAndBears.availableMana ⟨0⟩).green == 1

/-- Two Archdruids pump each other (CR 604.2). -/
def twoArchdruids : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) elvishArchdruid ⟨0⟩ ⟨0⟩

#guard
  let elves := twoArchdruids.battlefield.filter (fun o => o.name == "Elvish Archdruid")
  elves.size == 2 &&
    elves.all (fun o => twoArchdruids.power o == 3 && twoArchdruids.toughness o == 3)
#guard (twoArchdruids.availableMana ⟨0⟩).green == 4

/-- The +1/+1 is a continuous effect, so it does not wear off in cleanup. -/
def afterArchCleanup : Game := passBoth (skipTo archAndElves .end 80)

#guard afterArchCleanup.power (namedPermanent afterArchCleanup "Llanowar Elves") == 2
#guard (namedPermanent afterArchCleanup "Llanowar Elves").status.pumpPower == 0

/-- A 0/0 Elf survives while Archdruid is in play, and dies when it leaves. -/
def zeroElf : CardDef :=
  creature "Zero Elf" ManaCost.empty #["Elf"] 0 0

def zeroElfWithArch : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) zeroElf ⟨0⟩ ⟨0⟩

#guard zeroElfWithArch.power (namedPermanent zeroElfWithArch "Zero Elf") == 1
#guard zeroElfWithArch.toughness (namedPermanent zeroElfWithArch "Zero Elf") == 1
#guard (zeroElfWithArch.checkSBA).battlefield.any (fun o => o.name == "Zero Elf")

def zeroElfArchLeaves : Game :=
  let id := (namedPermanent zeroElfWithArch "Elvish Archdruid").id
  let (g, _) := zeroElfWithArch.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard !(zeroElfArchLeaves.battlefield.any (fun o => o.name == "Zero Elf"))
#guard zeroElfArchLeaves.log.any (fun s => mentions s "dies (toughness 0)")

/-- Combat uses the lord's pumped power. -/
def afterArchdruidCombat : Game :=
  let g := passBoth (skipTo archAndElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Llanowar Elves").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterArchdruidCombat.log.any (fun s =>
  mentions s "Llanowar Elves deals 2 combat damage to Nissa")
#guard (afterArchdruidCombat.player ⟨1⟩).life == 18

/-- Tapping Archdruid alone adds {G} for itself. -/
def tappedArchAlone : Game :=
  mustApply archAlone ⟨0⟩
    (.tapForMana (namedPermanent archAlone "Elvish Archdruid").id (.colored .green))

#guard (tappedArchAlone.player ⟨0⟩).manaPool.green == 1
#guard (namedPermanent tappedArchAlone "Elvish Archdruid").status.tapped
#guard tappedArchAlone.log.any (fun s => mentions s "taps Elvish Archdruid for green")
#guard !(tappedArchAlone.log.any (fun s => mentions s "green ×"))

/-- Tapping Archdruid with another Elf adds {G}{G}. -/
def tappedArchAndElves : Game :=
  mustApply archAndElves ⟨0⟩
    (.tapForMana (namedPermanent archAndElves "Elvish Archdruid").id (.colored .green))

#guard (tappedArchAndElves.player ⟨0⟩).manaPool.green == 2
#guard (namedPermanent tappedArchAndElves "Elvish Archdruid").status.tapped
#guard !(namedPermanent tappedArchAndElves "Llanowar Elves").status.tapped
#guard tappedArchAndElves.log.any (fun s => mentions s "taps Elvish Archdruid for green ×2")
#guard (tappedArchAndElves.manaSources ⟨0⟩).size == 1
#guard (tappedArchAndElves.availableMana ⟨0⟩).green == 3

/-- Opponent Elves do not count toward the mana ability. -/
def tappedArchAndOppElves : Game :=
  mustApply archAndOppElves ⟨0⟩
    (.tapForMana (namedPermanent archAndOppElves "Elvish Archdruid").id (.colored .green))

#guard (tappedArchAndOppElves.player ⟨0⟩).manaPool.green == 1

-- Summoning sickness still stops the mana ability (CR 302.6).
#guard
  let o := namedPermanent archAlone "Elvish Archdruid"
  let g := archAlone.setObject { o with status := { o.status with summoningSick := true } }
  match g.tapForMana ⟨0⟩ o.id (.colored .green) with
  | .error msg => mentions msg "summoning sickness"
  | .ok _ => false

/-- Available mana from Archdruid plus Elves pays {2}{G}; the agent casts it. -/
def agentArchdruidMana : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g elvishArchdruid ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  addToHand g centaurCourser ⟨0⟩

#guard (agentArchdruidMana.availableMana ⟨0⟩).canPay centaurCourser.manaCost
#guard
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g elvishMystic ⟨0⟩ ⟨0⟩
  let g := addToHand g centaurCourser ⟨0⟩
  !((g.availableMana ⟨0⟩).canPay centaurCourser.manaCost)
#guard
  match Agent.choose agentArchdruidMana ⟨0⟩ with
  | some (.cast id) => (agentArchdruidMana.object! id).name == "Centaur Courser"
  | _ => false

/- Mirkwood Elk: trample and enters-or-attacks return an Elf from the graveyard
(CR 603.6a / 508.2 / 118.2). -/

#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]
#guard mirkwoodElk.keywords.trample
#guard mirkwoodElk.power == some 6
#guard mirkwoodElk.toughness == some 6

/-- Mirkwood Elk in hand, an Elf in the graveyard, and enough mana to cast it. -/
def elkSetup : Game :=
  let g := addToGraveyard afterDraw llanowarElves ⟨0⟩
  withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6

#guard elkSetup.canCast ⟨0⟩ (handCardNamed elkSetup ⟨0⟩ "Mirkwood Elk")
#guard elkSetup.asSorcery? ⟨0⟩
#guard mirkwoodElk.hasSorcerySpeed
#guard (namedGraveyardCard elkSetup ⟨0⟩ "Llanowar Elves").hasSubtype "Elf"
#guard (elkSetup.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).contains
  (Target.card (namedGraveyardCard elkSetup ⟨0⟩ "Llanowar Elves").id)

def proposedElk : Game :=
  mustApply elkSetup ⟨0⟩ (.cast (handCardNamed elkSetup ⟨0⟩ "Mirkwood Elk").id)

#guard proposedElk.pending == .activateManaAbilities ⟨0⟩
#guard proposedElk.log.any (fun s => mentions s "begins casting Mirkwood Elk")

def paidElk : Game := mustApply proposedElk ⟨0⟩ .pay

#guard paidElk.stack.size == 1
#guard paidElk.hasPriority ⟨0⟩
#guard paidElk.log.any (fun s => mentions s "casts Mirkwood Elk")

/-- The creature enters; the trigger waits for a graveyard Elf (CR 603.3d). -/
def elkEntered : Game := passBoth paidElk

#guard (namedPermanent elkEntered "Mirkwood Elk").printed.power == some 6
#guard elkEntered.power (namedPermanent elkEntered "Mirkwood Elk") == 6
#guard elkEntered.toughness (namedPermanent elkEntered "Mirkwood Elk") == 6
#guard (namedPermanent elkEntered "Mirkwood Elk").printed.keywords.trample
#guard elkEntered.stack.size == 1
#guard (elkEntered.object! elkEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterOrAttackReturnElfGainLife
#guard (elkEntered.object! elkEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent elkEntered "Mirkwood Elk").id
#guard elkEntered.stack.back!.targets.isEmpty
#guard elkEntered.pending == .chooseTargets ⟨0⟩
#guard elkEntered.actor == some ⟨0⟩
#guard !elkEntered.hasPriority ⟨0⟩
#guard elkEntered.log.any (fun s => mentions s "enters the battlefield")
#guard elkEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard elkEntered.log.any (fun s => mentions s "must choose a target (CR 603.3d")

-- The trigger cannot target a player, a battlefield creature, or a permanent id
-- of the graveyard card.
#guard
  match elkEntered.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match elkEntered.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent elkEntered "Mirkwood Elk").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match elkEntered.apply ⟨0⟩
      (.target (Target.permanent (namedGraveyardCard elkEntered ⟨0⟩ "Llanowar Elves").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic returns the Elf from the graveyard.
#guard
  match Agent.choose elkEntered ⟨0⟩ with
  | some (.target (Target.card tid)) =>
    (elkEntered.object! tid).name == "Llanowar Elves"
  | _ => false

def elkTargeted : Game :=
  mustApply elkEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkEntered ⟨0⟩ "Llanowar Elves").id))

#guard elkTargeted.pending == .none
#guard elkTargeted.hasPriority ⟨0⟩
#guard elkTargeted.stack.back!.targets ==
  #[Target.card (namedGraveyardCard elkTargeted ⟨0⟩ "Llanowar Elves").id]
#guard elkTargeted.log.any (fun s =>
  mentions s "chooses Llanowar Elves as a target (CR 601.2c)")

def elkResolved : Game := passBoth elkTargeted

#guard elkResolved.stack.isEmpty
#guard (elkResolved.player ⟨0⟩).life == 21
#guard (elkResolved.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard !(elkResolved.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨0⟩))
#guard elkResolved.log.any (fun s => mentions s "Llanowar Elves is returned to Chandra's hand")
#guard elkResolved.log.any (fun s => mentions s "Chandra gains 1 life (21 life)")
#guard elkResolved.battlefield.any (fun o => o.name == "Mirkwood Elk")

-- The trigger still returns the Elf if Mirkwood Elk has left (CR 113.7a).
def elkLeftBeforeTrigger : Game :=
  let id := (namedPermanent elkTargeted "Mirkwood Elk").id
  let (g, _) := elkTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (elkLeftBeforeTrigger.player ⟨0⟩).life == 21
#guard (elkLeftBeforeTrigger.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard !(elkLeftBeforeTrigger.battlefield.any (fun o => o.name == "Mirkwood Elk"))

-- If the targeted card leaves the graveyard, nothing happens (CR 608.2b).
def elkTargetLeft : Game :=
  let id := (namedGraveyardCard elkTargeted ⟨0⟩ "Llanowar Elves").id
  let (g, _) := elkTargeted.move id .exile none
  passBoth g

#guard (elkTargetLeft.player ⟨0⟩).life == 20
#guard !(elkTargetLeft.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard elkTargetLeft.log.any (fun s => mentions s "no longer in the graveyard")
#guard elkTargetLeft.objects.any (fun o => o.name == "Llanowar Elves" && o.zone == .exile)

/-- No Elf in the graveyard: the trigger is removed (CR 603.3d). -/
def elkNoTargetEntered : Game :=
  let g := withGreenMana (addToHand afterDraw mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard elkNoTargetEntered.stack.isEmpty
#guard elkNoTargetEntered.pending == .none
#guard elkNoTargetEntered.battlefield.any (fun o => o.name == "Mirkwood Elk")
#guard elkNoTargetEntered.log.any (fun s =>
  mentions s "enters trigger is removed from the stack (no legal target)")
#guard (elkNoTargetEntered.player ⟨0⟩).life == 20

-- A non-Elf in the graveyard is not a legal target.
#guard
  let g := addToGraveyard afterDraw grizzlyBears ⟨0⟩
  let g := withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  g.stack.isEmpty &&
    g.log.any (fun s => mentions s "no legal target") &&
    !(g.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).contains
      (Target.card (namedGraveyardCard (addToGraveyard afterDraw grizzlyBears ⟨0⟩)
        ⟨0⟩ "Grizzly Bears").id)

-- An Elf in an opponent's graveyard is not a legal target.
#guard
  let g := addToGraveyard afterDraw llanowarElves ⟨1⟩
  (g.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).isEmpty

/-- Two Elves: life equals the chosen card's power; the heuristic picks the last. -/
def elkTwoElvesEntered : Game :=
  let g := addToGraveyard afterDraw llanowarElves ⟨0⟩
  let g := addToGraveyard g galadhrimGuide ⟨0⟩
  let g := withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard elkTwoElvesEntered.pending == .chooseTargets ⟨0⟩
#guard (elkTwoElvesEntered.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).size == 2
#guard
  match Agent.choose elkTwoElvesEntered ⟨0⟩ with
  | some (.target (Target.card tid)) =>
    (elkTwoElvesEntered.object! tid).name == "Galadhrim Guide"
  | _ => false

def elkGuideResolved : Game :=
  let g := mustApply elkTwoElvesEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkTwoElvesEntered ⟨0⟩ "Galadhrim Guide").id))
  passBoth g

#guard (elkGuideResolved.player ⟨0⟩).life == 23
#guard (elkGuideResolved.handObjects ⟨0⟩).any (fun o => o.name == "Galadhrim Guide")
#guard (elkGuideResolved.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨0⟩))
#guard elkGuideResolved.log.any (fun s => mentions s "Chandra gains 3 life (23 life)")

def elkElvesResolved : Game :=
  let g := mustApply elkTwoElvesEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkTwoElvesEntered ⟨0⟩ "Llanowar Elves").id))
  passBoth g

#guard (elkElvesResolved.player ⟨0⟩).life == 21
#guard (elkElvesResolved.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard (elkElvesResolved.objects.any (fun o =>
  o.name == "Galadhrim Guide" && o.zone == .graveyard ⟨0⟩))

/-- Mirkwood Elk already in play so it can attack (no ETB from `addPermanent`). -/
def elkOnBattlefield : Game :=
  addToGraveyard (addPermanent started mirkwoodElk ⟨0⟩ ⟨0⟩) llanowarElves ⟨0⟩

def elkAttackDeclared : Game :=
  let g := passBoth (skipTo elkOnBattlefield .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Mirkwood Elk").id])

#guard elkAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard elkAttackDeclared.stack.size == 1
#guard (elkAttackDeclared.object! elkAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some .onEnterOrAttackReturnElfGainLife
#guard (elkAttackDeclared.object! elkAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent elkAttackDeclared "Mirkwood Elk").id
#guard elkAttackDeclared.stack.back!.targets.isEmpty
#guard elkAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard elkAttackDeclared.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !elkAttackDeclared.hasPriority ⟨0⟩
#guard elkAttackDeclared.actor == some ⟨0⟩
#guard (namedPermanent elkAttackDeclared "Mirkwood Elk").status.attacking

#guard
  match Agent.choose elkAttackDeclared ⟨0⟩ with
  | some (.target (Target.card tid)) =>
    (elkAttackDeclared.object! tid).name == "Llanowar Elves"
  | _ => false

def elkAttackResolved : Game :=
  let g := mustApply elkAttackDeclared ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkAttackDeclared ⟨0⟩ "Llanowar Elves").id))
  passBoth g

#guard elkAttackResolved.stack.isEmpty
#guard (elkAttackResolved.player ⟨0⟩).life == 21
#guard (elkAttackResolved.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard elkAttackResolved.log.any (fun s => mentions s "Chandra gains 1 life")
#guard (namedPermanent elkAttackResolved "Mirkwood Elk").status.attacking

/-- Attack with no Elf in the graveyard removes the trigger (CR 603.3d). -/
def elkAttackNoTarget : Game :=
  let g := addPermanent started mirkwoodElk ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Mirkwood Elk").id])

#guard elkAttackNoTarget.stack.isEmpty
#guard elkAttackNoTarget.pending == .none
#guard elkAttackNoTarget.hasPriority ⟨0⟩
#guard elkAttackNoTarget.log.any (fun s =>
  mentions s "attack trigger is removed from the stack (no legal target)")
#guard (namedPermanent elkAttackNoTarget "Mirkwood Elk").status.attacking

/-- Printed trample assigns leftover combat damage (6/6 vs 2/2 Bears). -/
def afterElkTrampleCombat : Game :=
  let g := addPermanent (addPermanent started mirkwoodElk ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Mirkwood Elk").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Mirkwood Elk").id)])
  passBoth g

#guard afterElkTrampleCombat.log.any (fun s =>
  mentions s "Mirkwood Elk deals 2 combat damage to Grizzly Bears")
#guard afterElkTrampleCombat.log.any (fun s =>
  mentions s "Mirkwood Elk tramples for 4 to Nissa")
#guard (afterElkTrampleCombat.player ⟨1⟩).life == 16
#guard !(afterElkTrampleCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))

-- The agent casts Mirkwood Elk when that is the playable spell.
def agentElkOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addToGraveyard g llanowarElves ⟨0⟩
  withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6

#guard
  match Agent.choose agentElkOnly ⟨0⟩ with
  | some (.cast id) => (agentElkOnly.object! id).name == "Mirkwood Elk"
  | _ => false

/- Celeborn the Wise: attack with Elves to scry 1; whenever you scry, +1/+1
per card looked at. -/

#guard celebornTheWise.triggeredAbilities ==
  #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt]
#guard celebornTheWise.subtypes.any (· == "Elf")

/-- Celeborn on the battlefield, ready to attack. -/
def celebornReady : Game :=
  addPermanent started celebornTheWise ⟨0⟩ ⟨0⟩

def celebornAttackDeclared : Game :=
  let g := passBoth (skipTo celebornReady .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Celeborn the Wise").id])

#guard celebornAttackDeclared.stack.size == 1
#guard (celebornAttackDeclared.object! celebornAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackWithElvesScry 1)
#guard (celebornAttackDeclared.object! celebornAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent celebornAttackDeclared "Celeborn the Wise").id
#guard celebornAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard celebornAttackDeclared.hasPriority ⟨0⟩
#guard celebornAttackDeclared.power (namedPermanent celebornAttackDeclared "Celeborn the Wise") == 3

/-- Resolving the attack trigger starts scry 1. -/
def celebornScrying : Game := passBoth celebornAttackDeclared

#guard
  match celebornScrying.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard celebornScrying.stack.isEmpty
#guard celebornScrying.log.any (fun s => mentions s "scries 1")
#guard !celebornScrying.hasPriority ⟨0⟩

/-- After the scry, the pump trigger uses the number of cards looked at. -/
def celebornScried : Game := keepScry celebornScrying

#guard celebornScried.pending == .none
#guard celebornScried.stack.size == 1
#guard (celebornScried.object! celebornScried.stack.back!.objectId).triggeredAbility ==
  some .onScryPumpSelfForEachLookedAt
#guard (celebornScried.object! celebornScried.stack.back!.objectId).lastKnownPower == some 1
#guard celebornScried.log.any (fun s => mentions s "scry trigger is put on the stack")
#guard celebornScried.hasPriority ⟨0⟩
#guard celebornScried.power (namedPermanent celebornScried "Celeborn the Wise") == 3

def celebornPumped : Game := passBoth celebornScried

#guard celebornPumped.stack.isEmpty
#guard celebornPumped.power (namedPermanent celebornPumped "Celeborn the Wise") == 4
#guard celebornPumped.toughness (namedPermanent celebornPumped "Celeborn the Wise") == 4
#guard (namedPermanent celebornPumped "Celeborn the Wise").status.pumpPower == 1
#guard (namedPermanent celebornPumped "Celeborn the Wise").status.pumpToughness == 1
#guard celebornPumped.log.any (fun s => mentions s "gets +1/+1 until end of turn")

/-- Two Elves attacking still put only one scry trigger on the stack. -/
def celebornTwoElvesDeclared : Game :=
  let g := addPermanent celebornReady llanowarElves ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[
    (namedPermanent g "Celeborn the Wise").id,
    (namedPermanent g "Llanowar Elves").id])

#guard celebornTwoElvesDeclared.stack.size == 1
#guard (celebornTwoElvesDeclared.object! celebornTwoElvesDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackWithElvesScry 1)

/-- An Elf attacking while Celeborn stays back still triggers. -/
def celebornElvesAttackAlone : Game :=
  let g := addPermanent celebornReady llanowarElves ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Llanowar Elves").id])

#guard celebornElvesAttackAlone.stack.size == 1
#guard (celebornElvesAttackAlone.object! celebornElvesAttackAlone.stack.back!.objectId).sourceId ==
  some (namedPermanent celebornElvesAttackAlone "Celeborn the Wise").id

/-- Attacking with only a non-Elf does not trigger. -/
def celebornBearsAttack : Game :=
  let g := addPermanent celebornReady grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])

#guard celebornBearsAttack.stack.isEmpty
#guard !celebornBearsAttack.log.any (fun s => mentions s "Celeborn the Wise's attack trigger")

/-- Gift of Strands scries 2; Celeborn gets +2/+2. -/
def celebornGiftEntered : Game :=
  addPermanent giftEntered celebornTheWise ⟨0⟩ ⟨0⟩

def celebornGiftScrying : Game := passBoth celebornGiftEntered

#guard
  match celebornGiftScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false

def celebornGiftScried : Game := keepScry celebornGiftScrying

#guard celebornGiftScried.stack.size == 1
#guard (celebornGiftScried.object! celebornGiftScried.stack.back!.objectId).triggeredAbility ==
  some .onScryPumpSelfForEachLookedAt
#guard (celebornGiftScried.object! celebornGiftScried.stack.back!.objectId).lastKnownPower == some 2

def celebornGiftPumped : Game := passBoth celebornGiftScried

#guard celebornGiftPumped.power (namedPermanent celebornGiftPumped "Celeborn the Wise") == 5
#guard celebornGiftPumped.toughness (namedPermanent celebornGiftPumped "Celeborn the Wise") == 5
#guard celebornGiftPumped.log.any (fun s => mentions s "gets +2/+2 until end of turn")

/-- Scry 2 with one card in the library looks at one card, so +1/+1. -/
def celebornScryOneOfTwo : Game :=
  let g := addPermanent giftEntered celebornTheWise ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with library := pl.library.extract (pl.library.size - 1) pl.library.size })
  keepScry (passBoth g)

#guard celebornScryOneOfTwo.stack.size == 1
#guard (celebornScryOneOfTwo.object! celebornScryOneOfTwo.stack.back!.objectId).lastKnownPower ==
  some 1

def celebornScryOneOfTwoPumped : Game := passBoth celebornScryOneOfTwo

#guard celebornScryOneOfTwoPumped.power
  (namedPermanent celebornScryOneOfTwoPumped "Celeborn the Wise") == 4

/-- An empty library still scries; Celeborn gets +0/+0. -/
def celebornEmptyScry : Game :=
  let g := addPermanent giftEntered celebornTheWise ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  passBoth g

#guard celebornEmptyScry.pending == .none
#guard celebornEmptyScry.stack.size == 1
#guard (celebornEmptyScry.object! celebornEmptyScry.stack.back!.objectId).triggeredAbility ==
  some .onScryPumpSelfForEachLookedAt
#guard (celebornEmptyScry.object! celebornEmptyScry.stack.back!.objectId).lastKnownPower == some 0
#guard celebornEmptyScry.log.any (fun s => mentions s "no cards to look at")

def celebornEmptyPumped : Game := passBoth celebornEmptyScry

#guard celebornEmptyPumped.power (namedPermanent celebornEmptyPumped "Celeborn the Wise") == 3
#guard celebornEmptyPumped.log.any (fun s => mentions s "gets +0/+0 until end of turn")

/-- If Celeborn leaves before the pump resolves, he is not pumped. -/
def celebornPumpSourceGone : Game :=
  let id := (namedPermanent celebornScried "Celeborn the Wise").id
  let (g, _) := celebornScried.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard celebornPumpSourceGone.stack.isEmpty
#guard !(celebornPumpSourceGone.battlefield.any (fun o => o.name == "Celeborn the Wise"))
#guard celebornPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")

/-- If Celeborn leaves before the attack trigger resolves, you still scry, but
he is not on the battlefield to trigger from that scry. -/
def celebornGoneBeforeScry : Game :=
  let id := (namedPermanent celebornAttackDeclared "Celeborn the Wise").id
  let (g, _) := celebornAttackDeclared.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard
  match celebornGoneBeforeScry.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard celebornGoneBeforeScry.waitingTriggers.isEmpty

def celebornGoneAfterScry : Game := keepScry celebornGoneBeforeScry

#guard celebornGoneAfterScry.stack.isEmpty
#guard celebornGoneAfterScry.pending == .none

/-- An opponent's scry does not pump your Celeborn. -/
def opponentScriesCeleborn : Game :=
  let g := addPermanent afterDraw celebornTheWise ⟨0⟩ ⟨0⟩
  keepScry (g.beginScry ⟨1⟩ 1)

#guard opponentScriesCeleborn.stack.isEmpty
#guard opponentScriesCeleborn.power (namedPermanent opponentScriesCeleborn "Celeborn the Wise") == 3
#guard (namedPermanent opponentScriesCeleborn "Celeborn the Wise").status.pumpPower == 0

/-- The +1/+1 wears off in cleanup. -/
def afterCelebornCleanup : Game := passBoth (skipTo celebornPumped .end 80)

#guard afterCelebornCleanup.power (namedPermanent afterCelebornCleanup "Celeborn the Wise") == 3
#guard (namedPermanent afterCelebornCleanup "Celeborn the Wise").status.pumpPower == 0
#guard (namedPermanent afterCelebornCleanup "Celeborn the Wise").status.pumpToughness == 0

/- Woodland Weavemaster: vigilance, another-Elf-enters +1/+1, and restricted
any-color mana equal to power. -/

#guard woodlandWeavemaster.keywords.vigilance
#guard woodlandWeavemaster.triggeredAbilities == #[.onAnotherElfYouControlEntersGets1]
#guard woodlandWeavemaster.tapAddAnyColorEqualToPower
#guard woodlandWeavemaster.manaAbilities.contains (.colored .green)
#guard woodlandWeavemaster.manaAbilities.contains (.colored .white)
#guard !woodlandWeavemaster.manaAbilities.contains .colorless

def weavemasterReady : Game :=
  addPermanent afterDraw woodlandWeavemaster ⟨0⟩ ⟨0⟩

#guard (weavemasterReady.effectiveKeywords
  (namedPermanent weavemasterReady "Woodland Weavemaster")).vigilance
#guard weavemasterReady.hasVigilance
  (namedPermanent weavemasterReady "Woodland Weavemaster")
#guard weavemasterReady.power (namedPermanent weavemasterReady "Woodland Weavemaster") == 1
#guard weavemasterReady.manaFromTap
  (namedPermanent weavemasterReady "Woodland Weavemaster") (.colored .green) == 1
#guard (weavemasterReady.availableMana ⟨0⟩).green == 1
#guard (weavemasterReady.availableMana ⟨0⟩).elfGreen == 1
#guard (weavemasterReady.availableMana ⟨0⟩).canPay (ManaCost.ofColor .green) true
#guard !(weavemasterReady.availableMana ⟨0⟩).canPay (ManaCost.ofColor .green)

/-- Casting another Elf you control pumps Weavemaster (CR 603.6a). -/
def weavemasterElfSetup : Game :=
  withGreenMana (addToHand weavemasterReady llanowarElves ⟨0⟩) ⟨0⟩

def proposedWeavemasterElf : Game :=
  mustApply weavemasterElfSetup ⟨0⟩
    (.cast (handCardNamed weavemasterElfSetup ⟨0⟩ "Llanowar Elves").id)

def paidWeavemasterElf : Game := mustApply proposedWeavemasterElf ⟨0⟩ .pay

def weavemasterElfEntered : Game := passBoth paidWeavemasterElf

#guard weavemasterElfEntered.stack.size == 1
#guard (weavemasterElfEntered.object! weavemasterElfEntered.stack.back!.objectId).triggeredAbility ==
  some .onAnotherElfYouControlEntersGets1
#guard (weavemasterElfEntered.object! weavemasterElfEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent weavemasterElfEntered "Woodland Weavemaster").id
#guard weavemasterElfEntered.log.any (fun s => mentions s "Llanowar Elves enters the battlefield")
#guard weavemasterElfEntered.log.any (fun s => mentions s "Elf-enters trigger is put on the stack")
#guard weavemasterElfEntered.power
  (namedPermanent weavemasterElfEntered "Woodland Weavemaster") == 1

def weavemasterElfPumped : Game := passBoth weavemasterElfEntered

#guard weavemasterElfPumped.stack.isEmpty
#guard weavemasterElfPumped.power
  (namedPermanent weavemasterElfPumped "Woodland Weavemaster") == 2
#guard weavemasterElfPumped.toughness
  (namedPermanent weavemasterElfPumped "Woodland Weavemaster") == 3
#guard weavemasterElfPumped.log.any (fun s =>
  mentions s "Woodland Weavemaster gets +1/+1 until end of turn")
#guard weavemasterElfPumped.manaFromTap
  (namedPermanent weavemasterElfPumped "Woodland Weavemaster") (.colored .green) == 2

/-- Weavemaster entering alone does not pump itself. -/
def weavemasterEntersAlone : Game :=
  let g := withGreenMana (addToHand afterDraw woodlandWeavemaster ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Woodland Weavemaster").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard weavemasterEntersAlone.battlefield.any (fun o => o.name == "Woodland Weavemaster")
#guard weavemasterEntersAlone.stack.isEmpty
#guard weavemasterEntersAlone.power
  (namedPermanent weavemasterEntersAlone "Woodland Weavemaster") == 1
#guard !weavemasterEntersAlone.log.any (fun s => mentions s "Elf-enters trigger")

/-- A non-Elf you control does not trigger the pump. -/
def weavemasterBearsEntered : Game :=
  let g := withGreenMana (addToHand weavemasterReady grizzlyBears ⟨0⟩) ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Grizzly Bears").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard weavemasterBearsEntered.stack.isEmpty
#guard weavemasterBearsEntered.power
  (namedPermanent weavemasterBearsEntered "Woodland Weavemaster") == 1

/-- An opponent's Elf does not trigger the pump. -/
def weavemasterOppElf : Game :=
  let g := addPermanent weavemasterReady llanowarElves ⟨1⟩ ⟨1⟩
  g.putAnotherElfYouControlEntersTriggers (namedPermanent g "Llanowar Elves")

#guard weavemasterOppElf.stack.isEmpty

/-- Two Weavemasters: the first triggers when the second enters. -/
def twoWeavemastersEntered : Game :=
  let g := addPermanent afterDraw woodlandWeavemaster ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g woodlandWeavemaster ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Woodland Weavemaster").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard twoWeavemastersEntered.stack.size == 1
#guard (twoWeavemastersEntered.object! twoWeavemastersEntered.stack.back!.objectId).triggeredAbility ==
  some .onAnotherElfYouControlEntersGets1

def twoWeavemastersPumped : Game := passBoth twoWeavemastersEntered

#guard
  let weavers := twoWeavemastersPumped.battlefield.filter
    (fun o => o.name == "Woodland Weavemaster")
  weavers.size == 2 &&
    (weavers.filter (fun o => twoWeavemastersPumped.power o == 2)).size == 1 &&
    (weavers.filter (fun o => twoWeavemastersPumped.power o == 1)).size == 1

/-- If Weavemaster leaves before the trigger resolves, it is not pumped. -/
def weavemasterPumpSourceGone : Game :=
  let id := (namedPermanent weavemasterElfEntered "Woodland Weavemaster").id
  let (g, _) := weavemasterElfEntered.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard weavemasterPumpSourceGone.stack.isEmpty
#guard !(weavemasterPumpSourceGone.battlefield.any (fun o => o.name == "Woodland Weavemaster"))
#guard weavemasterPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")

/-- The +1/+1 wears off in cleanup. -/
def afterWeavemasterCleanup : Game := passBoth (skipTo weavemasterElfPumped .end 80)

#guard afterWeavemasterCleanup.power
  (namedPermanent afterWeavemasterCleanup "Woodland Weavemaster") == 1
#guard (namedPermanent afterWeavemasterCleanup "Woodland Weavemaster").status.pumpPower == 0

/-- Tapping adds power of the chosen color as Elf-restricted mana. -/
def tappedWeavemasterGreen : Game :=
  mustApply weavemasterReady ⟨0⟩
    (.tapForMana (namedPermanent weavemasterReady "Woodland Weavemaster").id
      (.colored .green))

#guard (namedPermanent tappedWeavemasterGreen "Woodland Weavemaster").status.tapped
#guard (tappedWeavemasterGreen.player ⟨0⟩).manaPool.green == 1
#guard (tappedWeavemasterGreen.player ⟨0⟩).manaPool.elfGreen == 1
#guard (tappedWeavemasterGreen.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .green) true
#guard !(tappedWeavemasterGreen.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .green)
#guard !(tappedWeavemasterGreen.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .red) true
#guard tappedWeavemasterGreen.log.any (fun s =>
  mentions s "taps Woodland Weavemaster for green (Elf spells and abilities)")

def tappedWeavemasterWhite : Game :=
  mustApply weavemasterReady ⟨0⟩
    (.tapForMana (namedPermanent weavemasterReady "Woodland Weavemaster").id
      (.colored .white))

#guard (tappedWeavemasterWhite.player ⟨0⟩).manaPool.white == 1
#guard (tappedWeavemasterWhite.player ⟨0⟩).manaPool.elfWhite == 1

#guard
  match weavemasterReady.tapForMana ⟨0⟩
      (namedPermanent weavemasterReady "Woodland Weavemaster").id .colorless with
  | .error msg => mentions msg "cannot produce"
  | .ok _ => false

/-- Pumped power produces that much mana. -/
def tappedWeavemasterPumped : Game :=
  let g := weavemasterElfPumped.emptyManaPools
  mustApply g ⟨0⟩
    (.tapForMana (namedPermanent g "Woodland Weavemaster").id
      (.colored .green))

#guard (tappedWeavemasterPumped.player ⟨0⟩).manaPool.green == 2
#guard (tappedWeavemasterPumped.player ⟨0⟩).manaPool.elfGreen == 2
#guard tappedWeavemasterPumped.log.any (fun s =>
  mentions s "taps Woodland Weavemaster for green ×2 (Elf spells and abilities)")

/-- Restricted mana can pay for an Elf spell. -/
def weavemasterPaysElf : Game :=
  let g := addToHand tappedWeavemasterGreen llanowarElves ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Llanowar Elves").id)
  mustApply g ⟨0⟩ .pay

#guard weavemasterPaysElf.log.any (fun s => mentions s "casts Llanowar Elves")
#guard (weavemasterPaysElf.player ⟨0⟩).manaPool.isEmpty
#guard weavemasterPaysElf.stack.size == 1

/-- Restricted mana cannot pay for a non-Elf spell (CR 106.10). -/
def weavemasterPaysGrowth : Game :=
  let g := addToHand tappedWeavemasterGreen giantGrowth ⟨0⟩
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Woodland Weavemaster").id)
  mustApply g ⟨0⟩ .pay

#guard weavemasterPaysGrowth.log.any (fun s => mentions s "cannot pay")
#guard weavemasterPaysGrowth.log.any (fun s => mentions s "casting is reversed")
#guard weavemasterPaysGrowth.stack.isEmpty
#guard (weavemasterPaysGrowth.handObjects ⟨0⟩).any (fun o => o.name == "Giant Growth")
#guard (namedPermanent weavemasterPaysGrowth "Woodland Weavemaster").status.tapped
#guard (weavemasterPaysGrowth.player ⟨0⟩).manaPool.elfGreen == 1

/-- Summoning sickness still stops the mana ability (CR 302.6). -/
def weavemasterSick : Game :=
  let o := namedPermanent weavemasterReady "Woodland Weavemaster"
  weavemasterReady.setObject { o with status := { o.status with summoningSick := true } }

#guard
  match weavemasterSick.tapForMana ⟨0⟩
      (namedPermanent weavemasterSick "Woodland Weavemaster").id (.colored .green) with
  | .error msg => mentions msg "summoning sickness"
  | .ok _ => false

/-- Attacking with vigilance does not tap the creature (CR 702.20). -/
def weavemasterVsGoblin : Game :=
  addPermanent (addPermanent started woodlandWeavemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨1⟩ ⟨1⟩

def weavemasterAttackDeclared : Game :=
  let g := passBoth (skipTo weavemasterVsGoblin .beginningOfCombat 80)
  mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Woodland Weavemaster").id])

#guard (namedPermanent weavemasterAttackDeclared "Woodland Weavemaster").status.attacking
#guard !(namedPermanent weavemasterAttackDeclared "Woodland Weavemaster").status.tapped
#guard weavemasterAttackDeclared.log.any (fun s =>
  mentions s "attacks Nissa with Woodland Weavemaster")

/-- After attacking, Weavemaster can still block on the opponent's turn. -/
def nissaAttacksAfterVigilance : Game :=
  let g := passBoth (skipTo weavemasterAttackDeclared .beginningOfCombat 80)
  mustApply g ⟨1⟩ (.declareAttackers #[(namedPermanent g "Raging Goblin").id])

#guard !(namedPermanent nissaAttacksAfterVigilance "Woodland Weavemaster").status.tapped
#guard nissaAttacksAfterVigilance.canBlock
  (namedPermanent nissaAttacksAfterVigilance "Woodland Weavemaster")
  (namedPermanent nissaAttacksAfterVigilance "Raging Goblin")

def weavemasterBlocksAfterAttack : Game :=
  let g := passBoth nissaAttacksAfterVigilance
  mustApply g ⟨0⟩ (.declareBlockers #[(
    (namedPermanent g "Woodland Weavemaster").id,
    (namedPermanent g "Raging Goblin").id)])

#guard (namedPermanent weavemasterBlocksAfterAttack "Woodland Weavemaster").status.blocking.size == 1
#guard weavemasterBlocksAfterAttack.log.any (fun s =>
  mentions s "Woodland Weavemaster blocks Raging Goblin")

/-- The agent casts an Elf using Weavemaster's restricted mana. -/
def agentWeavemasterElf : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g woodlandWeavemaster ⟨0⟩ ⟨0⟩
  addToHand g llanowarElves ⟨0⟩

#guard
  match Agent.choose agentWeavemasterElf ⟨0⟩ with
  | some (.cast id) => (agentWeavemasterElf.object! id).name == "Llanowar Elves"
  | _ => false

def agentWeavemasterPaying : Game :=
  mustApply agentWeavemasterElf ⟨0⟩
    (.cast (handCardNamed agentWeavemasterElf ⟨0⟩ "Llanowar Elves").id)

#guard
  match Agent.choose agentWeavemasterPaying ⟨0⟩ with
  | some (.tapForMana id (.colored .green)) =>
    (agentWeavemasterPaying.object! id).name == "Woodland Weavemaster"
  | _ => false

/-- The agent will not try to cast a non-Elf with only restricted mana. -/
def agentWeavemasterGrowth : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g woodlandWeavemaster ⟨0⟩ ⟨0⟩
  addToHand g giantGrowth ⟨0⟩

#guard
  match Agent.choose agentWeavemasterGrowth ⟨0⟩ with
  | some (.cast id) => (agentWeavemasterGrowth.object! id).name != "Giant Growth"
  | _ => true

end Mtg.Engine.Tests
