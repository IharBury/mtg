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
import Mtg.Engine.Tests.Combat

/-!
# Fight spells, landfall pumps, and APNAP dies triggers.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Fire of Orthanc (CR 701.8 / 509.1b / 611.2a). -/

/-- Fire of Orthanc in hand, an opposing Forest, enough mana. -/
def fireOfOrthancSetup : Game :=
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4

#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.requiresTarget
#guard fireOfOrthanc.spellEffect == some (Effect.destroyArtifactOrLandNonflyersCantBlock)
#guard fireOfOrthancSetup.canCast ⟨0⟩ (handCardNamed fireOfOrthancSetup ⟨0⟩ "Fire of Orthanc")
#guard fireOfOrthancSetup.asSorcery? ⟨0⟩
#guard
  (fireOfOrthancSetup.legalTargets ⟨0⟩ (Effect.destroyArtifactOrLandNonflyersCantBlock)).contains
    (Target.permanent (namedPermanent fireOfOrthancSetup "Forest").id)

-- Cannot cast with no artifact or land.
#guard
  let g := withRedMana (addToHand afterDraw fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc")
#guard
  let g := withRedMana (addToHand afterDraw fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Fire of Orthanc").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- An opposing artifact is a legal target; a non-artifact creature is not.
#guard
  let g := addPermanent afterDraw wayfarersBauble ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  (g.legalTargets ⟨0⟩ (Effect.destroyArtifactOrLandNonflyersCantBlock)).contains
    (Target.permanent (namedPermanent g "Wayfarer's Bauble").id) &&
    !(g.legalTargets ⟨0⟩ (Effect.destroyArtifactOrLandNonflyersCantBlock)).contains
      (Target.permanent (namedPermanent g "Grizzly Bears").id)

-- Own lands are legal; hexproof on an opponent's land is not (CR 702.11b).
#guard
  let g := addPermanent afterDraw mountain ⟨0⟩ ⟨0⟩
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc") &&
    (g.legalTargets ⟨0⟩ (Effect.destroyArtifactOrLandNonflyersCantBlock)).contains
      (Target.permanent (namedPermanent g "Mountain").id)
#guard
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  let forest := namedPermanent g "Forest"
  let g := g.setObject { forest with
    status := { forest.status with untilEotKeywords := Keyword.hexproof } }
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc")

def proposedFireOfOrthanc : Game :=
  mustApply fireOfOrthancSetup ⟨0⟩
    (.cast (handCardNamed fireOfOrthancSetup ⟨0⟩ "Fire of Orthanc").id)

#guard proposedFireOfOrthanc.pending == .chooseTargets ⟨0⟩
#guard proposedFireOfOrthanc.log.any (fun s => mentions s "begins casting Fire of Orthanc")
#guard proposedFireOfOrthanc.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Cannot target a player or a creature that is not an artifact.
#guard
  match proposedFireOfOrthanc.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def targetedFireOfOrthanc : Game :=
  mustApply proposedFireOfOrthanc ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedFireOfOrthanc "Forest").id))

#guard targetedFireOfOrthanc.pending == .activateManaAbilities ⟨0⟩
#guard targetedFireOfOrthanc.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedFireOfOrthanc "Forest").id]

#guard
  match Agent.choose proposedFireOfOrthanc ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedFireOfOrthanc.object! tid).name == "Forest"
  | _ => false

-- Prefer an opposing land over your own (CR 601.2c heuristic).
#guard
  let g := addPermanent fireOfOrthancSetup mountain ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Fire of Orthanc").id)
  match Agent.choose g ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (g.object! tid).name == "Forest"
  | _ => false

def paidFireOfOrthanc : Game := mustApply targetedFireOfOrthanc ⟨0⟩ .pay

#guard paidFireOfOrthanc.hasPriority ⟨0⟩
#guard paidFireOfOrthanc.stack.size == 1
#guard paidFireOfOrthanc.log.any (fun s => mentions s "casts Fire of Orthanc")

def resolvedFireOfOrthanc : Game := passBoth paidFireOfOrthanc

#guard resolvedFireOfOrthanc.stack.isEmpty
#guard !(resolvedFireOfOrthanc.battlefield.any (fun o => o.name == "Forest"))
#guard resolvedFireOfOrthanc.objects.any (fun o =>
  o.name == "Forest" && o.zone == .graveyard ⟨1⟩)
#guard resolvedFireOfOrthanc.log.any (fun s => mentions s "Forest is destroyed")
#guard resolvedFireOfOrthanc.log.any (fun s =>
  mentions s "Creatures without flying can't block this turn")
#guard resolvedFireOfOrthanc.creaturesWithoutFlyingCantBlock
#guard (resolvedFireOfOrthanc.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedFireOfOrthanc.object! id).name == "Fire of Orthanc")

-- Destroying an artifact also sets the can't-block effect.
#guard
  let g := addPermanent afterDraw wayfarersBauble ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ (Effect.destroyArtifactOrLandNonflyersCantBlock)
    #[Target.permanent (namedPermanent g "Wayfarer's Bauble").id]
  !(g.battlefield.any (fun o => o.name == "Wayfarer's Bauble")) &&
    g.creaturesWithoutFlyingCantBlock &&
    g.log.any (fun s => mentions s "Wayfarer's Bauble is destroyed")

-- If the target leaves before resolution, neither effect happens (CR 608.2b).
def fireOfOrthancTargetGone : Game :=
  let id := (namedPermanent paidFireOfOrthanc "Forest").id
  let (g, _) := paidFireOfOrthanc.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard fireOfOrthancTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !fireOfOrthancTargetGone.creaturesWithoutFlyingCantBlock

/-- Chandra's Gray Ogre attacks after Fire of Orthanc; Nissa's Grizzly Bears
cannot block. -/
def fireOfOrthancReadyToBlock : Game :=
  let g := addPermanent started grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ (Effect.destroyArtifactOrLandNonflyersCantBlock)
    #[Target.permanent (namedPermanent g "Forest").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard fireOfOrthancReadyToBlock.pending == .declareBlockers
#guard fireOfOrthancReadyToBlock.creaturesWithoutFlyingCantBlock
#guard
  let g := fireOfOrthancReadyToBlock
  !g.canBlock (namedPermanent g "Grizzly Bears") (namedPermanent g "Gray Ogre")
#guard
  match fireOfOrthancReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent fireOfOrthancReadyToBlock "Grizzly Bears").id,
    (namedPermanent fireOfOrthancReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

/-- A flying creature can still block after Fire of Orthanc. -/
def fireOfOrthancFlyerReadyToBlock : Game :=
  let g := addPermanent started grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterfliesCard ⟨1⟩ ⟨1⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ (Effect.destroyArtifactOrLandNonflyersCantBlock)
    #[Target.permanent (namedPermanent g "Forest").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := fireOfOrthancFlyerReadyToBlock
  g.canBlock (namedPermanent g "Velvetwing Butterflies") (namedPermanent g "Gray Ogre")

def fireOfOrthancFlyerBlocks : Game :=
  let g := fireOfOrthancFlyerReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Velvetwing Butterflies").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent fireOfOrthancFlyerBlocks "Velvetwing Butterflies").status.blocking ==
  #[(namedPermanent fireOfOrthancFlyerBlocks "Gray Ogre").id]
#guard (namedPermanent fireOfOrthancFlyerBlocks "Gray Ogre").status.blocked

/-- The can't-block effect wears off in cleanup (CR 514.2). -/
def afterFireOfOrthancCleanup : Game :=
  passBoth (skipTo resolvedFireOfOrthanc .end 80)

#guard afterFireOfOrthancCleanup.turnNumber == 2
#guard !afterFireOfOrthancCleanup.creaturesWithoutFlyingCantBlock

/-- The agent casts Fire of Orthanc when that is the playable spell. -/
def agentFireOfOrthancOnly : Game :=
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4

#guard
  match Agent.choose agentFireOfOrthancOnly ⟨0⟩ with
  | some (.cast id) => (agentFireOfOrthancOnly.object! id).name == "Fire of Orthanc"
  | _ => false

/- Quarrel: target creature you control deals damage equal to its power to
target creature an opponent controls (CR 601.2c / 608.2b / 120.3a). -/

/-- Propose a two-target spell (CR 601.2a / 601.2c). -/
def proposeTwoTargeted (g : Game) (p : PlayerId) (id : ObjectId) (t1 t2 : Target) : Game :=
  mustApply (proposeTargeted g p id t1) p (.target t2)

/-- Quarrel in hand, Llanowar Elves you control, Grizzly Bears opposing. -/
def quarrelSetup : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

#guard quarrelCard.isInstant
#guard quarrelCard.requiresTarget
#guard Effect.creatureYouControlDealsPowerToOppCreature.targetCount == 2
#guard quarrelSetup.canCast ⟨0⟩ (handCardNamed quarrelSetup ⟨0⟩ "Quarrel")
#guard quarrelSetup.asSorcery? ⟨0⟩
#guard (quarrelSetup.legalTargets ⟨0⟩ (Effect.creatureYouControlDealsPowerToOppCreature)).size == 2

-- Cannot cast with no creature you control.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Quarrel")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Quarrel").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Cannot cast with no opposing creature.
#guard
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Quarrel")

-- Hexproof makes an opposing creature an illegal dest (CR 702.11b).
#guard
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Quarrel")

def proposedQuarrel : Game :=
  mustApply quarrelSetup ⟨0⟩ (.cast (handCardNamed quarrelSetup ⟨0⟩ "Quarrel").id)

#guard proposedQuarrel.pending == .chooseTargets ⟨0⟩
#guard proposedQuarrel.stack.back!.targets.isEmpty
#guard proposedQuarrel.log.any (fun s => mentions s "begins casting Quarrel")
#guard proposedQuarrel.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Distinct instances of the word “target” are announced sequentially (CR 601.2c).
#guard
  match proposedQuarrel.announceTargetChoices ⟨0⟩
      #[(Target.permanent (namedPermanent proposedQuarrel "Llanowar Elves").id, none),
        (Target.permanent (namedPermanent proposedQuarrel "Grizzly Bears").id, none)] with
  | .error msg => mentions msg "separately"
  | .ok _ => false

-- First target must be a creature you control, not a player or an opponent's creature.
#guard
  match proposedQuarrel.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedQuarrel.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent proposedQuarrel "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic's first target is the creature you control.
#guard
  match Agent.choose proposedQuarrel ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedQuarrel.object! tid).name == "Llanowar Elves"
  | _ => false

def quarrelSourceChosen : Game :=
  mustApply proposedQuarrel ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedQuarrel "Llanowar Elves").id))

#guard quarrelSourceChosen.pending == .chooseTargets ⟨0⟩
#guard quarrelSourceChosen.proposedSpell.isSome
#guard quarrelSourceChosen.stack.back!.targets ==
  #[Target.permanent (namedPermanent quarrelSourceChosen "Llanowar Elves").id]
#guard quarrelSourceChosen.log.any (fun s => mentions s "chooses Llanowar Elves as a target")

-- Second target must be an opposing creature.
#guard
  match quarrelSourceChosen.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match quarrelSourceChosen.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent quarrelSourceChosen "Llanowar Elves").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic's second target is the opposing creature.
#guard
  match Agent.choose quarrelSourceChosen ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (quarrelSourceChosen.object! tid).name == "Grizzly Bears"
  | _ => false

def targetedQuarrel : Game :=
  mustApply quarrelSourceChosen ⟨0⟩
    (.target (Target.permanent (namedPermanent quarrelSourceChosen "Grizzly Bears").id))

#guard targetedQuarrel.pending == .activateManaAbilities ⟨0⟩
#guard targetedQuarrel.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedQuarrel "Llanowar Elves").id,
    Target.permanent (namedPermanent targetedQuarrel "Grizzly Bears").id]

def paidQuarrel : Game := mustApply targetedQuarrel ⟨0⟩ .pay

#guard paidQuarrel.hasPriority ⟨0⟩
#guard paidQuarrel.log.any (fun s => mentions s "casts Quarrel")

def resolvedQuarrel : Game := passBoth paidQuarrel

#guard resolvedQuarrel.stack.isEmpty
#guard resolvedQuarrel.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent resolvedQuarrel "Grizzly Bears").status.damage == 1
#guard resolvedQuarrel.log.any (fun s => mentions s "Llanowar Elves deals 1 damage to Grizzly Bears")
#guard resolvedQuarrel.log.any (fun s => mentions s "goes to the graveyard")
#guard (resolvedQuarrel.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedQuarrel.object! id).name == "Quarrel")

/-- A 3-power source deals lethal damage to a 2/2. -/
def quarrelLethalSetup : Game :=
  let g := addPermanent afterDraw hillGiant ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

def resolvedQuarrelLethal : Game :=
  let g := proposeTwoTargeted quarrelLethalSetup ⟨0⟩
    (handCardNamed quarrelLethalSetup ⟨0⟩ "Quarrel").id
    (Target.permanent (namedPermanent quarrelLethalSetup "Hill Giant").id)
    (Target.permanent (namedPermanent quarrelLethalSetup "Grizzly Bears").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedQuarrelLethal.stack.isEmpty
#guard !(resolvedQuarrelLethal.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedQuarrelLethal.log.any (fun s => mentions s "Hill Giant deals 3 damage to Grizzly Bears")
#guard resolvedQuarrelLethal.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")

/-- Pumping the source after targeting uses the new power (CR 608.2g / 611.3a). -/
def quarrelPumpedSource : Game :=
  let g := addToHand paidQuarrel giantGrowth ⟨0⟩
  let g := withGreenMana g ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Llanowar Elves").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth (passBoth g)

#guard quarrelPumpedSource.power (namedPermanent quarrelPumpedSource "Llanowar Elves") == 4
#guard !(quarrelPumpedSource.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard quarrelPumpedSource.log.any (fun s =>
  mentions s "Llanowar Elves deals 4 damage to Grizzly Bears")

/-- If the dest leaves before resolution, no damage is dealt (CR 608.2b). -/
def quarrelDestGone : Game :=
  let dest := namedPermanent paidQuarrel "Grizzly Bears"
  let (g, _) := paidQuarrel.move dest.id (.graveyard dest.owner) none
  passBoth g

#guard quarrelDestGone.log.any (fun s => mentions s "The target is no longer in play")
#guard !quarrelDestGone.log.any (fun s => mentions s "deals")
#guard !(quarrelDestGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- If the source leaves before resolution, no damage is dealt (CR 608.2b). -/
def quarrelSourceGone : Game :=
  let src := namedPermanent paidQuarrel "Llanowar Elves"
  let (g, _) := paidQuarrel.move src.id (.graveyard src.owner) none
  passBoth g

#guard quarrelSourceGone.log.any (fun s => mentions s "The target is no longer in play")
#guard !quarrelSourceGone.log.any (fun s => mentions s "deals")
#guard quarrelSourceGone.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent quarrelSourceGone "Grizzly Bears").status.damage == 0

/-- Hexproof gained after targeting makes the dest illegal (CR 608.2b / 702.11b). -/
def quarrelDestHexproof : Game :=
  let dest := namedPermanent paidQuarrel "Grizzly Bears"
  let g := paidQuarrel.setObject { dest with
    status := { dest.status with untilEotKeywords := Keyword.hexproof } }
  passBoth g

#guard quarrelDestHexproof.log.any (fun s => mentions s "The target is no longer legal")
#guard !quarrelDestHexproof.log.any (fun s => mentions s "deals")
#guard (namedPermanent quarrelDestHexproof "Grizzly Bears").status.damage == 0

/-- The heuristic casts Quarrel when it is the playable spell. -/
def agentQuarrel : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentQuarrel ⟨0⟩ with
  | some (.cast id) => (agentQuarrel.object! id).name == "Quarrel"
  | _ => false

/- Attercop: reach, deathtouch, and landfall +1/+1 until end of turn. -/

#guard attercop.keywords.reach
#guard attercop.keywords.deathtouch
#guard attercop.triggeredAbilities == #[(.onLandYouControlEntersGets 1 1)]
#guard attercop.power == some 2
#guard attercop.toughness == some 1

/-- A flying attacker can be blocked by Attercop (reach) but not by a Gray Ogre. -/
def flyerVsAttercop : Game :=
  let g := addPermanent started smaugTheGreatCalamityCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g attercop ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let smaug := namedPermanent g "Smaug, the Great Calamity"
  g.setObject { smaug with status := { smaug.status with attacking := true } }

#guard flyerVsAttercop.canBlock
  (namedPermanent flyerVsAttercop "Attercop")
  (namedPermanent flyerVsAttercop "Smaug, the Great Calamity")
#guard !flyerVsAttercop.canBlock
  (namedPermanent flyerVsAttercop "Gray Ogre")
  (namedPermanent flyerVsAttercop "Smaug, the Great Calamity")

/-- Attercop in play; a Forest in hand. -/
def attercopLandfallSetup : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  addToHand g forest ⟨0⟩

#guard attercopLandfallSetup.canPlayLand ⟨0⟩
#guard attercopLandfallSetup.power (namedPermanent attercopLandfallSetup "Attercop") == 2
#guard attercopLandfallSetup.toughness (namedPermanent attercopLandfallSetup "Attercop") == 1

def attercopLandPlayed : Game :=
  mustApply attercopLandfallSetup ⟨0⟩
    (.playLand (handCardNamed attercopLandfallSetup ⟨0⟩ "Forest").id)

#guard attercopLandPlayed.pending == .none
#guard attercopLandPlayed.hasPriority ⟨0⟩
#guard attercopLandPlayed.stack.size == 1
#guard (attercopLandPlayed.object! attercopLandPlayed.stack.back!.objectId).triggeredAbility ==
  some (.onLandYouControlEntersGets 1 1)
#guard (attercopLandPlayed.object! attercopLandPlayed.stack.back!.objectId).sourceId ==
  some (namedPermanent attercopLandPlayed "Attercop").id
#guard attercopLandPlayed.stack.back!.targets.isEmpty
#guard attercopLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack")
#guard attercopLandPlayed.power (namedPermanent attercopLandPlayed "Attercop") == 2

def attercopLandfallResolved : Game := passBoth attercopLandPlayed

#guard attercopLandfallResolved.stack.isEmpty
#guard attercopLandfallResolved.hasPriority ⟨0⟩
#guard (namedPermanent attercopLandfallResolved "Attercop").status.pumpPower == 1
#guard (namedPermanent attercopLandfallResolved "Attercop").status.pumpToughness == 1
#guard attercopLandfallResolved.power
  (namedPermanent attercopLandfallResolved "Attercop") == 3
#guard attercopLandfallResolved.toughness
  (namedPermanent attercopLandfallResolved "Attercop") == 2
#guard attercopLandfallResolved.log.any (fun s =>
  mentions s "Attercop gets +1/+1 until end of turn")

-- Direct resolution of a landfall pump stacks with an existing pump.
#guard
  let id := (namedPermanent attercopLandfallResolved "Attercop").id
  let g := attercopLandfallResolved.applyTriggeredAbility ⟨0⟩
    (.onLandYouControlEntersGets 1 1) (some id)
  g.power (namedPermanent g "Attercop") == 4 &&
    g.toughness (namedPermanent g "Attercop") == 3

/-- An opponent's land does not trigger your landfall. -/
def nissaLandVsAttercop : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .end 80)
  let g := skipTo g .precombatMain 80
  let g := addToHand g forest ⟨1⟩
  mustApply g ⟨1⟩ (.playLand (handCardNamed g ⟨1⟩ "Forest").id)

#guard nissaLandVsAttercop.stack.isEmpty
#guard !(nissaLandVsAttercop.log.any (fun s => mentions s "landfall"))
#guard nissaLandVsAttercop.power (namedPermanent nissaLandVsAttercop "Attercop") == 2

/-- If Attercop leaves before the trigger resolves, it is not pumped. -/
def attercopSourceGone : Game :=
  let id := (namedPermanent attercopLandPlayed "Attercop").id
  let (g, _) := attercopLandPlayed.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard attercopSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard !(attercopSourceGone.battlefield.any (fun o => o.name == "Attercop"))

/-- The +1/+1 wears off in cleanup (CR 514.3). -/
def afterAttercopCleanup : Game := passBoth (skipTo attercopLandfallResolved .end 80)

#guard afterAttercopCleanup.power (namedPermanent afterAttercopCleanup "Attercop") == 2
#guard afterAttercopCleanup.toughness (namedPermanent afterAttercopCleanup "Attercop") == 1
#guard (namedPermanent afterAttercopCleanup "Attercop").status.pumpPower == 0
#guard (namedPermanent afterAttercopCleanup "Attercop").status.pumpToughness == 0

/-- Two Attercops both trigger from one land; the controller chooses order
(CR 603.3b). -/
def twoAttercopsLandPending : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g attercop ⟨0⟩ ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard twoAttercopsLandPending.pending == .chooseTriggerToStack ⟨0⟩
#guard twoAttercopsLandPending.waitingTriggers.size == 2
#guard twoAttercopsLandPending.stack.isEmpty
#guard twoAttercopsLandPending.actor == some ⟨0⟩
#guard twoAttercopsLandPending.log.any (fun s => mentions s "CR 603.3b")
#guard
  match Agent.choose twoAttercopsLandPending ⟨0⟩ with
  | some (.stackTriggers ids) =>
    ids == twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
  | _ => false

def twoAttercopsLandPlayed : Game := applyIdle twoAttercopsLandPending

#guard twoAttercopsLandPlayed.stack.size == 2
#guard (twoAttercopsLandPlayed.object! twoAttercopsLandPlayed.stack.back!.objectId).triggeredAbility ==
  some (.onLandYouControlEntersGets 1 1)
#guard (twoAttercopsLandPlayed.object!
  twoAttercopsLandPlayed.stack[0]!.objectId).triggeredAbility ==
  some (.onLandYouControlEntersGets 1 1)

def twoAttercopsPumped : Game := passBoth (passBoth twoAttercopsLandPlayed)

#guard twoAttercopsPumped.stack.isEmpty
#guard
  let spiders := twoAttercopsPumped.battlefield.filter (fun o => o.name == "Attercop")
  spiders.size == 2 && spiders.all (fun o => twoAttercopsPumped.power o == 3)

/- CR 603.3b: APNAP order and the controller's chosen order. -/

/-- The controller may put the newer Attercop's trigger first (bottom). -/
def twoAttercopsReversed : Game :=
  let ids := twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
  mustApply twoAttercopsLandPending ⟨0⟩ (.stackTriggers ids.reverse)

#guard twoAttercopsReversed.pending == .none
#guard twoAttercopsReversed.stack.size == 2
#guard twoAttercopsReversed.waitingTriggers.isEmpty
#guard twoAttercopsReversed.hasPriority ⟨0⟩
#guard
  let ids := twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
  (twoAttercopsReversed.object! twoAttercopsReversed.stack[0]!.objectId).sourceId ==
    some ids[1]! &&
    (twoAttercopsReversed.object! twoAttercopsReversed.stack.back!.objectId).sourceId ==
      some ids[0]!
#guard twoAttercopsReversed.log.any (fun s =>
  mentions s "chooses the order of triggered abilities")

-- An incomplete list is illegal.
#guard
  match twoAttercopsLandPending.apply ⟨0⟩
      (.stackTriggers (twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩).pop) with
  | .error msg => mentions msg "CR 603.3b"
  | .ok _ => false

-- Only the controller of those triggers may choose the order.
#guard
  match twoAttercopsLandPending.apply ⟨1⟩
      (.stackTriggers (twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩)) with
  | .error msg => mentions msg "CR 603.3b"
  | .ok _ => false

/-- Both Fireleapers in play with a creature each side can target. -/
def apnapDiesSetup : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g goblinFireleaper ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def fireleaperControlledBy (g : Game) (p : PlayerId) : ObjectId :=
  match (g.permanentsOf p).find? (fun o => o.name == "Goblin Fireleaper") with
  | some o => o.id
  | none => panic! "expected Goblin Fireleaper"

/-- Chandra (AP) and Nissa each have a dies trigger; AP puts first and
announces targets before NAP's trigger is stacked (CR 603.3b / 603.3d). -/
def apnapDiesTriggers : Game :=
  let chandraId := fireleaperControlledBy apnapDiesSetup ⟨0⟩
  let nissaId := fireleaperControlledBy apnapDiesSetup ⟨1⟩
  let (g, _) := apnapDiesSetup.move chandraId (.graveyard ⟨0⟩) none
  let (g, _) := g.move nissaId (.graveyard ⟨1⟩) none
  g.receivePriority ⟨0⟩

#guard apnapDiesTriggers.stack.size == 1
#guard apnapDiesTriggers.waitingTriggers.size == 1
#guard apnapDiesTriggers.waitingTriggers[0]!.controller == ⟨1⟩
#guard apnapDiesTriggers.pending == .chooseTargets ⟨0⟩
#guard apnapDiesTriggers.stack[0]!.controller == ⟨0⟩
#guard (apnapDiesTriggers.object! apnapDiesTriggers.stack[0]!.objectId).sourceId ==
  some (fireleaperControlledBy apnapDiesSetup ⟨0⟩)

def apnapDiesAfterApTargets : Game :=
  match (apnapDiesTriggers.permanentsOf ⟨1⟩).find? (fun o => o.name == "Grizzly Bears") with
  | none => panic! "expected Nissa's Grizzly Bears"
  | some bears =>
    mustApply apnapDiesTriggers ⟨0⟩ (.target (Target.permanent bears.id))

#guard apnapDiesAfterApTargets.stack.size == 2
#guard apnapDiesAfterApTargets.waitingTriggers.isEmpty
#guard apnapDiesAfterApTargets.pending == .chooseTargets ⟨1⟩
#guard apnapDiesAfterApTargets.stack[0]!.controller == ⟨0⟩
#guard apnapDiesAfterApTargets.stack.back!.controller == ⟨1⟩
#guard (apnapDiesAfterApTargets.object! apnapDiesAfterApTargets.stack.back!.objectId).sourceId ==
  some (fireleaperControlledBy apnapDiesSetup ⟨1⟩)

/-- Wood Elves putting a Forest onto the battlefield also triggers landfall. -/
def attercopWoodElvesResolved : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g woodElves ⟨0⟩) ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Wood Elves").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := addToLibraryTop (addToLibraryTop g forest ⟨0⟩) mountain ⟨0⟩
  passBoth g

#guard attercopWoodElvesResolved.battlefield.any (fun o => o.name == "Forest")
#guard attercopWoodElvesResolved.stack.size == 1
#guard (attercopWoodElvesResolved.object!
  attercopWoodElvesResolved.stack.back!.objectId).triggeredAbility ==
  some (.onLandYouControlEntersGets 1 1)
#guard attercopWoodElvesResolved.log.any (fun s => mentions s "landfall trigger is put on the stack")

def attercopWoodElvesPumped : Game := passBoth attercopWoodElvesResolved

#guard attercopWoodElvesPumped.stack.isEmpty
#guard attercopWoodElvesPumped.power
  (namedPermanent attercopWoodElvesPumped "Attercop") == 3
#guard attercopWoodElvesPumped.log.any (fun s =>
  mentions s "Attercop gets +1/+1 until end of turn")

/-- The heuristic plays a land when Attercop is in play. -/
def agentAttercopLand : Game :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[] })
  let g := addPermanent g attercop ⟨0⟩ ⟨0⟩
  addToHand g forest ⟨0⟩

#guard
  match Agent.choose agentAttercopLand ⟨0⟩ with
  | some (.playLand id) => (agentAttercopLand.object! id).name == "Forest"
  | _ => false

end Mtg.Engine.Tests
