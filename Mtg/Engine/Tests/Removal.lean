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
# Unblockable, exile-instead, Ferocious, and draw-and-lose-life.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Rogue's Passage: {T}: Add {C} and {4}, {T}: target creature can't be blocked. -/

def passageAbility : ActivatedAbility :=
  roguesPassage.activatedAbilities[0]!

/-- Passage, Gray Ogre, and opposing Bears; {4} in the pool; land drop used. -/
def passageReady : Game :=
  let g := addPermanent afterDraw roguesPassage ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 4

def passageSource (g : Game) : GameObject :=
  namedPermanent g "Rogue's Passage"

#guard passageAbility.effect == Effect.targetCantBeBlockedThisTurn
#guard passageAbility.cost.tap
#guard passageAbility.cost.mana == ManaCost.ofGeneric 4
#guard passageAbility.effect.requiresTarget
#guard !passageAbility.onlyAsSorcery
#guard passageReady.canActivate ⟨0⟩ (passageSource passageReady) passageAbility
#guard !(passageReady.canActivate ⟨1⟩ (passageSource passageReady) passageAbility)
#guard (passageReady.player ⟨0⟩).manaPool.canPay passageAbility.cost.mana
#guard roguesPassage.manaAbilities == #[.colorless]

-- Cannot activate with no creature in play.
#guard
  let g := addPermanent afterDraw roguesPassage ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 4
  !g.canActivate ⟨0⟩ (namedPermanent g "Rogue's Passage") passageAbility

-- Cannot activate while the land is tapped.
#guard
  let o := passageSource passageReady
  let g := passageReady.setObject { o with status := { o.status with tapped := true } }
  !g.canActivate ⟨0⟩ (namedPermanent g "Rogue's Passage") passageAbility

-- Instant-speed: Passage can activate during the end step.
#guard
  let g := skipTo passageReady .end 80
  g.step == .end && g.canActivate ⟨0⟩ (passageSource g) passageAbility

-- The {T}: Add {C} mana ability still works when the land is untapped.
#guard
  match passageReady.tapForMana ⟨0⟩ (passageSource passageReady).id .colorless with
  | .ok g =>
    (g.player ⟨0⟩).manaPool.get .colorless >= 1 &&
      (namedPermanent g "Rogue's Passage").status.tapped
  | .error _ => false

-- The heuristic does not dump {4} in the main phase.
#guard
  match Agent.choose passageReady ⟨0⟩ with
  | some (.activate id 0) => (passageReady.object! id).name != "Rogue's Passage"
  | _ => true

def proposedPassage : Game :=
  mustApply passageReady ⟨0⟩ (.activate (passageSource passageReady).id 0)

#guard
  match proposedPassage.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedPassage.proposedSpell.isSome
#guard proposedPassage.stack.size == 1
#guard (proposedPassage.object! proposedPassage.stack.back!.objectId).abilityEffect ==
  some (Effect.targetCantBeBlockedThisTurn)
#guard (namedPermanent proposedPassage "Rogue's Passage").isOnBattlefield
#guard !(namedPermanent proposedPassage "Rogue's Passage").status.tapped
#guard proposedPassage.log.any (fun s => mentions s "begins activating Rogue's Passage")
#guard proposedPassage.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Opponent cannot choose Chandra's target.
#guard
  match proposedPassage.apply ⟨1⟩
      (.target (Target.permanent (namedPermanent proposedPassage "Gray Ogre").id)) with
  | .error msg => mentions msg "may choose targets"
  | .ok _ => false

-- The heuristic targets Chandra's creature, not Nissa's.
#guard
  match Agent.choose proposedPassage ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedPassage.object! tid).name == "Gray Ogre"
  | _ => false

def targetedPassage : Game :=
  mustApply proposedPassage ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedPassage "Gray Ogre").id))

#guard targetedPassage.pending == .activateManaAbilities ⟨0⟩
#guard targetedPassage.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedPassage "Gray Ogre").id]
#guard targetedPassage.log.any (fun s => mentions s "chooses Gray Ogre as a target")

-- Cannot tap Passage for mana while its {T} is part of the activation cost.
#guard
  match targetedPassage.tapForMana ⟨0⟩ (passageSource targetedPassage).id .colorless with
  | .error msg => mentions msg "needed to pay"
  | .ok _ => false

-- Opponent cannot pay Chandra's activation.
#guard
  match targetedPassage.apply ⟨1⟩ .pay with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

def paidPassage : Game := mustApply targetedPassage ⟨0⟩ .pay

#guard paidPassage.hasPriority ⟨0⟩
#guard paidPassage.stack.size == 1
#guard (namedPermanent paidPassage "Rogue's Passage").status.tapped
#guard !(namedPermanent paidPassage "Gray Ogre").status.untilEotKeywords.cantBeBlocked
#guard paidPassage.log.any (fun s => mentions s "activates Rogue's Passage")

def passageResolved : Game := passBoth paidPassage

#guard passageResolved.stack.isEmpty
#guard (namedPermanent passageResolved "Gray Ogre").status.untilEotKeywords.cantBeBlocked
#guard passageResolved.hasCantBeBlocked (namedPermanent passageResolved "Gray Ogre")
#guard !passageResolved.hasCantBeBlocked (namedPermanent passageResolved "Grizzly Bears")
#guard passageResolved.log.any (fun s => mentions s "Gray Ogre can't be blocked this turn")

-- Targeting an opponent's creature is legal.
#guard
  let g := mustApply proposedPassage ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedPassage "Grizzly Bears").id))
  g.stack.back!.targets ==
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]

-- Hexproof makes an opposing creature an illegal target (CR 702.11b).
#guard
  let bears := namedPermanent proposedPassage "Grizzly Bears"
  let g := proposedPassage.setObject { bears with
    status := { bears.status with untilEotKeywords := Keyword.hexproof } }
  match g.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

/-- If the target leaves before the ability resolves, it does nothing. -/
def passageTargetGone : Game :=
  let id := (namedPermanent paidPassage "Gray Ogre").id
  let (g, _) := paidPassage.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard passageTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(passageTargetGone.battlefield.any (fun o => o.name == "Gray Ogre"))

/-- The can't-be-blocked grant wears off in cleanup. -/
def afterPassageCleanup : Game :=
  passBoth (skipTo passageResolved .end 80)

#guard !(namedPermanent afterPassageCleanup "Gray Ogre").status.untilEotKeywords.cantBeBlocked
#guard !afterPassageCleanup.hasCantBeBlocked
  (namedPermanent afterPassageCleanup "Gray Ogre")

/-- Gray Ogre attacks after becoming unblockable; Bears cannot block. -/
def passageOgreAttacking : Game :=
  let g := passBoth (skipTo passageResolved .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])

def passageReadyToBlock : Game := passBoth passageOgreAttacking

#guard passageReadyToBlock.pending == .declareBlockers
#guard !passageReadyToBlock.canBlock
  (namedPermanent passageReadyToBlock "Grizzly Bears")
  (namedPermanent passageReadyToBlock "Gray Ogre")
#guard
  match passageReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent passageReadyToBlock "Grizzly Bears").id,
    (namedPermanent passageReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

def passageUnblockedDamage : Game :=
  passBoth (mustApply passageReadyToBlock ⟨1⟩ (.declareBlockers #[]))

#guard (passageUnblockedDamage.player ⟨1⟩).life == 18
#guard passageUnblockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")
#guard !passageUnblockedDamage.log.any (fun s =>
  mentions s "Grizzly Bears blocks Gray Ogre")

/-- After attackers are declared, the heuristic activates Passage with {4} in the pool. -/
def passageAfterAttack : Game :=
  let g := passBoth (skipTo passageReady .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  withRedMana g ⟨0⟩ 4

#guard passageAfterAttack.hasPriority ⟨0⟩
#guard (namedPermanent passageAfterAttack "Gray Ogre").status.attacking
#guard
  match Agent.choose passageAfterAttack ⟨0⟩ with
  | some (.activate id 0) => id == (passageSource passageAfterAttack).id
  | _ => false

/-- Three Mountains plus Passage is not enough {4} once Passage must stay untapped. -/
def passageThreeMountainsAttacking : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g roguesPassage ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])

#guard
  (passageThreeMountainsAttacking.availableMana ⟨0⟩).canPay (ManaCost.ofGeneric 4)
#guard
  !(passageThreeMountainsAttacking.availableManaExcept ⟨0⟩
    (some (passageSource passageThreeMountainsAttacking).id)).canPay (ManaCost.ofGeneric 4)
#guard
  match Agent.choose passageThreeMountainsAttacking ⟨0⟩ with
  | some (.activate id 0) => (passageThreeMountainsAttacking.object! id).name != "Rogue's Passage"
  | _ => true

/-- Four Mountains plus Passage: the heuristic activates and taps Mountains, not Passage. -/
def passageFourMountainsAttacking : Game :=
  let g := addUntappedLand passageThreeMountainsAttacking mountain
  g

#guard
  (passageFourMountainsAttacking.availableManaExcept ⟨0⟩
    (some (passageSource passageFourMountainsAttacking).id)).canPay (ManaCost.ofGeneric 4)
#guard
  match Agent.choose passageFourMountainsAttacking ⟨0⟩ with
  | some (.activate id 0) => id == (passageSource passageFourMountainsAttacking).id
  | _ => false

def targetedPassageFromLands : Game :=
  let g := mustApply passageFourMountainsAttacking ⟨0⟩
    (.activate (passageSource passageFourMountainsAttacking).id 0)
  mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Gray Ogre").id))

#guard targetedPassageFromLands.pending == .activateManaAbilities ⟨0⟩
#guard
  match Agent.choose targetedPassageFromLands ⟨0⟩ with
  | some (.tapForMana id _) =>
    (targetedPassageFromLands.object! id).name != "Rogue's Passage"
  | _ => false

/- Smite the Deathless: 3 damage, lose indestructible until EOT, exile if it
would die this turn (CR 702.12 / 614.1 / 700.4). -/

def indestructibleBeast : CardDef :=
  creature "Indestructible Beast" ManaCost.empty #[] 2 2
    (keywords := Keyword.indestructible)

def indestructibleFlyer : CardDef :=
  creature "Indestructible Flyer" ManaCost.empty #[] 4 4
    (keywords := Keyword.flying.merge Keyword.indestructible)

def indestructibleZero : CardDef :=
  creature "Indestructible Zero" ManaCost.empty #[] 0 0
    (keywords := Keyword.indestructible)

def smiteOn (card : CardDef) : Game :=
  let g := addPermanent afterDraw card ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g smiteTheDeathless ⟨0⟩) ⟨0⟩ 2

def smiteSetup : Game := smiteOn grizzlyBears

#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (Effect.dealDamageLoseIndestructibleExile 3)
#guard smiteSetup.canCast ⟨0⟩ (handCardNamed smiteSetup ⟨0⟩ "Smite the Deathless")
#guard smiteSetup.asSorcery? ⟨0⟩
#guard (smiteSetup.legalTargets ⟨0⟩ (Effect.dealDamageLoseIndestructibleExile 3)).size == 1

-- Cannot cast with no creature on the battlefield.
#guard
  let g := withRedMana (addToHand afterDraw smiteTheDeathless ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Smite the Deathless")
#guard
  let g := withRedMana (addToHand afterDraw smiteTheDeathless ⟨0⟩) ⟨0⟩ 2
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

def proposedSmite : Game :=
  mustApply smiteSetup ⟨0⟩ (.cast (handCardNamed smiteSetup ⟨0⟩ "Smite the Deathless").id)

#guard
  match proposedSmite.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedSmite.log.any (fun s => mentions s "begins casting Smite the Deathless")
#guard proposedSmite.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Smite cannot target a player.
#guard
  match proposedSmite.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets an opposing creature.
#guard
  match Agent.choose proposedSmite ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedSmite.object! tid).name == "Grizzly Bears"
  | _ => false

def paidSmite : Game :=
  let g := mustApply proposedSmite ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedSmite "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

#guard paidSmite.hasPriority ⟨0⟩
#guard paidSmite.log.any (fun s => mentions s "casts Smite the Deathless")

def resolvedSmiteOnBears : Game := passBoth paidSmite

#guard resolvedSmiteOnBears.stack.isEmpty
#guard !(resolvedSmiteOnBears.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedSmiteOnBears.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard !(resolvedSmiteOnBears.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .graveyard ⟨1⟩))
#guard resolvedSmiteOnBears.log.any (fun s =>
  mentions s "is dealt 3 damage, loses indestructible until end of turn")
#guard resolvedSmiteOnBears.log.any (fun s => mentions s "dies from lethal damage")
#guard resolvedSmiteOnBears.log.any (fun s => mentions s "is exiled instead of dying")
#guard (resolvedSmiteOnBears.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedSmiteOnBears.object! id).name == "Smite the Deathless")

/-- 3 damage is not lethal to a 4-toughness creature; the replacement lasts. -/
def resolvedSmiteOnWurm : Game :=
  let g := smiteOn crawWurm
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Craw Wurm").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedSmiteOnWurm.battlefield.any (fun o => o.name == "Craw Wurm")
#guard (namedPermanent resolvedSmiteOnWurm "Craw Wurm").status.damage == 3
#guard (namedPermanent resolvedSmiteOnWurm "Craw Wurm").status.untilEotLosesIndestructible
#guard (namedPermanent resolvedSmiteOnWurm "Craw Wurm").status.untilEotExileIfDies
#guard !resolvedSmiteOnWurm.objects.any (fun o =>
  o.name == "Craw Wurm" && o.zone == .exile)

/-- Later this turn, 0 toughness is replaced by exile. -/
def smiteWurmThenZeroToughness : Game :=
  let o := namedPermanent resolvedSmiteOnWurm "Craw Wurm"
  let g := resolvedSmiteOnWurm.setObject { o with
    status := { o.status with pump := (o.status.pump.1, -4) } }
  g.receivePriority ⟨0⟩

#guard !(smiteWurmThenZeroToughness.battlefield.any (fun o => o.name == "Craw Wurm"))
#guard smiteWurmThenZeroToughness.objects.any (fun o =>
  o.name == "Craw Wurm" && o.zone == .exile)
#guard smiteWurmThenZeroToughness.log.any (fun s => mentions s "dies (toughness 0)")
#guard smiteWurmThenZeroToughness.log.any (fun s => mentions s "is exiled instead of dying")

/-- The until-EOT flags and marked damage wear off in cleanup. -/
def afterSmiteWurmCleanup : Game :=
  passBoth (skipTo resolvedSmiteOnWurm .end 80)

#guard (namedPermanent afterSmiteWurmCleanup "Craw Wurm").status.damage == 0
#guard !(namedPermanent afterSmiteWurmCleanup "Craw Wurm").status.untilEotLosesIndestructible
#guard !(namedPermanent afterSmiteWurmCleanup "Craw Wurm").status.untilEotExileIfDies

/-- Printed indestructible ignores lethal damage (CR 702.12b / 704.5g). -/
def indestructibleSurvivesDamage : Game :=
  let g := addPermanent afterDraw indestructibleBeast ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ (Effect.dealDamage 3)
    #[Target.permanent (namedPermanent g "Indestructible Beast").id]
  g.receivePriority ⟨0⟩

#guard indestructibleSurvivesDamage.battlefield.any (fun o =>
  o.name == "Indestructible Beast")
#guard (namedPermanent indestructibleSurvivesDamage "Indestructible Beast").status.damage == 3
#guard indestructibleSurvivesDamage.hasIndestructible
  (namedPermanent indestructibleSurvivesDamage "Indestructible Beast")
#guard !indestructibleSurvivesDamage.log.any (fun s => mentions s "dies from lethal damage")

/-- Indestructible does not save a creature with 0 toughness (CR 704.5f). -/
def indestructibleZeroDies : Game :=
  let g := addPermanent afterDraw indestructibleZero ⟨1⟩ ⟨1⟩
  g.receivePriority ⟨0⟩

#guard !(indestructibleZeroDies.battlefield.any (fun o => o.name == "Indestructible Zero"))
#guard indestructibleZeroDies.objects.any (fun o =>
  o.name == "Indestructible Zero" && o.zone == .graveyard ⟨1⟩)
#guard indestructibleZeroDies.log.any (fun s => mentions s "dies (toughness 0)")
#guard !indestructibleZeroDies.log.any (fun s => mentions s "exiled instead")

/-- Destroy does nothing to an indestructible creature (CR 701.7b / 702.12b). -/
def destroyIndestructibleFlyer : Game :=
  let g := addPermanent afterDraw indestructibleFlyer ⟨1⟩ ⟨1⟩
  g.applyEffect ⟨0⟩ (Effect.destroyCreatureWithFlying)
    #[Target.permanent (namedPermanent g "Indestructible Flyer").id]

#guard destroyIndestructibleFlyer.battlefield.any (fun o =>
  o.name == "Indestructible Flyer")
#guard destroyIndestructibleFlyer.log.any (fun s =>
  mentions s "is indestructible and isn't destroyed")
#guard !destroyIndestructibleFlyer.log.any (fun s =>
  mentions s "Indestructible Flyer is destroyed")

/-- Smite strips indestructible from a 2/2 and exiles it to lethal damage. -/
def resolvedSmiteOnIndestructibleBeast : Game :=
  let g := smiteOn indestructibleBeast
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Indestructible Beast").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard !(resolvedSmiteOnIndestructibleBeast.battlefield.any (fun o =>
  o.name == "Indestructible Beast"))
#guard resolvedSmiteOnIndestructibleBeast.objects.any (fun o =>
  o.name == "Indestructible Beast" && o.zone == .exile)
#guard resolvedSmiteOnIndestructibleBeast.log.any (fun s =>
  mentions s "is exiled instead of dying")

/-- After Smite, a 4/4 flyer can be destroyed and is exiled instead of dying. -/
def resolvedSmiteOnIndestructibleFlyer : Game :=
  let g := smiteOn indestructibleFlyer
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Indestructible Flyer").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedSmiteOnIndestructibleFlyer.battlefield.any (fun o =>
  o.name == "Indestructible Flyer")
#guard !resolvedSmiteOnIndestructibleFlyer.hasIndestructible
  (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer")
#guard (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer").status.damage
  == 3
#guard (resolvedSmiteOnIndestructibleFlyer.effectiveKeywords
  (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer")).flying
#guard !(resolvedSmiteOnIndestructibleFlyer.effectiveKeywords
  (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer")).indestructible

def smiteFlyerThenDestroy : Game :=
  resolvedSmiteOnIndestructibleFlyer.applyEffect ⟨0⟩ (Effect.destroyCreatureWithFlying)
    #[Target.permanent
      (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer").id]

#guard !(smiteFlyerThenDestroy.battlefield.any (fun o => o.name == "Indestructible Flyer"))
#guard smiteFlyerThenDestroy.objects.any (fun o =>
  o.name == "Indestructible Flyer" && o.zone == .exile)
#guard smiteFlyerThenDestroy.log.any (fun s => mentions s "is destroyed")
#guard smiteFlyerThenDestroy.log.any (fun s => mentions s "is exiled instead of dying")

/-- Exile-instead-of-dying means dies triggers do not go on the stack
(CR 700.4 / 614.6). -/
def smiteOnFireleaper : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  withRedMana (addToHand g smiteTheDeathless ⟨0⟩) ⟨0⟩ 2

def resolvedSmiteOnFireleaper : Game :=
  let g := mustApply smiteOnFireleaper ⟨0⟩
    (.cast (handCardNamed smiteOnFireleaper ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Goblin Fireleaper").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedSmiteOnFireleaper.objects.any (fun o =>
  o.name == "Goblin Fireleaper" && o.zone == .exile)
#guard resolvedSmiteOnFireleaper.stack.isEmpty
#guard !resolvedSmiteOnFireleaper.log.any (fun s => mentions s "dies trigger")
#guard resolvedSmiteOnFireleaper.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent resolvedSmiteOnFireleaper "Grizzly Bears").status.damage == 0

/-- How many Wolf tokens are on the battlefield. -/
def wolfCount (g : Game) : Nat :=
  g.battlefield.filter (fun o => o.name == "Wolf") |>.size

/-- How many waiting copies of `ab` are pending. -/
def countWaitingAbility (g : Game) (ab : TriggeredAbility) : Nat :=
  g.waitingTriggers.filter (fun wt => wt.ability == ab) |>.size

/-- Mark `name` with lethal damage so the next SBA check will try to make it die. -/
def withLethal (g : Game) (name : String) : Game :=
  let o := namedPermanent g name
  g.setObject { o with status := { o.status with damage := 20 } }

/-!
CR 614.6: if an event is replaced, it never happens. A modified event occurs
instead, which may in turn trigger abilities. Impossible instructions of that
modified event are ignored.
-/

/-- Head of the Hunt replaces an opposing death: the die event never happens,
so Great Fierce Bee does not trigger, and `creatureDiedThisTurn` stays false. -/
def headExilesPreyBeeSilent : Game :=
  let g := addPermanent afterDraw greatFierceBeeCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  (withLethal g "Grizzly Bears").checkSBA

#guard headExilesPreyBeeSilent.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard !(headExilesPreyBeeSilent.objects.any (fun o =>
  o.name == "Grizzly Bears" &&
    match o.zone with | .graveyard _ => true | _ => false))
#guard headExilesPreyBeeSilent.battlefield.any (fun o => o.name == "Great Fierce Bee")
#guard countWaitingAbility headExilesPreyBeeSilent
  (.onOneOrMoreOtherCreaturesDieScry 1) == 0
#guard !headExilesPreyBeeSilent.creatureDiedThisTurn
#guard wolfCount headExilesPreyBeeSilent == 1
#guard headExilesPreyBeeSilent.log.any (fun s => mentions s "CR 614.6")

/-- Bee itself dying does not see an opposing creature that was exiled instead
of dying. The Bee did die, so `creatureDiedThisTurn` is true. -/
def beeDiesWhileHeadExilesPrey : Game :=
  let g := addPermanent afterDraw greatFierceBeeCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withLethal g "Great Fierce Bee"
  (withLethal g "Grizzly Bears").checkSBA

#guard beeDiesWhileHeadExilesPrey.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard beeDiesWhileHeadExilesPrey.objects.any (fun o =>
  o.name == "Great Fierce Bee" &&
    match o.zone with | .graveyard _ => true | _ => false)
#guard countWaitingAbility beeDiesWhileHeadExilesPrey
  (.onOneOrMoreOtherCreaturesDieScry 1) == 0
#guard beeDiesWhileHeadExilesPrey.creatureDiedThisTurn
#guard wolfCount beeDiesWhileHeadExilesPrey == 1

/-- Simultaneous death of Head of the Hunt still replaces the opposing death
and creates exactly one Wolf from the snapshot source. -/
def headDiesWithPreyOneWolf : Game :=
  let g := addPermanent afterDraw headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withLethal g "Head of the Hunt"
  (withLethal g "Grizzly Bears").checkSBA

#guard headDiesWithPreyOneWolf.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard headDiesWithPreyOneWolf.objects.any (fun o =>
  o.name == "Head of the Hunt" &&
    match o.zone with | .graveyard _ => true | _ => false)
#guard wolfCount headDiesWithPreyOneWolf == 1

/-- The modified exile/leave event still triggers leaves-the-battlefield
abilities (CR 614.6). Fiend Hunter's return is a trigger, not an immediate
one-shot. -/
def hunterExiledInsteadLeaves : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileForLeaveTrigger (some hunter.id) (namedPermanent g "Grizzly Bears")
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.setObject { hunter with status :=
    { hunter.status with untilEotExileIfDies := true } }
  (g.move (namedPermanent g "Fiend Hunter").id (.graveyard ⟨0⟩) none).1

#guard hunterExiledInsteadLeaves.objects.any (fun o =>
  o.name == "Fiend Hunter" && o.zone == .exile)
#guard hunterExiledInsteadLeaves.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard countWaitingAbility hunterExiledInsteadLeaves .onLeaveReturnExiled == 1
#guard !hunterExiledInsteadLeaves.creatureDiedThisTurn

/-- CR 614.6: an impossible instruction of a modified event is ignored. An
Aura that cannot attach legally stays in exile. -/
def auraReturnImpossibleIgnored : Game :=
  let g := addPermanent afterDraw banishingLight ⟨0⟩ ⟨0⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let light := namedPermanent g "Banishing Light"
  let g := g.exileUntilSourceLeaves (some light.id)
    (namedPermanent g "Fog on the Barrow-Downs")
  (g.move (namedPermanent g "Banishing Light").id (.graveyard ⟨0⟩) none).1

#guard auraReturnImpossibleIgnored.objects.any (fun o =>
  o.name == "Fog on the Barrow-Downs" && o.zone == .exile)
#guard !auraReturnImpossibleIgnored.battlefield.any (fun o =>
  o.name == "Fog on the Barrow-Downs")
#guard auraReturnImpossibleIgnored.log.any (fun s => mentions s "CR 614.6")

/-- The heuristic casts Smite when it is the playable spell. -/
def agentSmite : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g smiteTheDeathless ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentSmite ⟨0⟩ with
  | some (.cast id) => (agentSmite.object! id).name == "Smite the Deathless"
  | _ => false

/- Ravening Warg: deathtouch (CR 702.2 / 704.5h) and Ferocious attack-gain-life. -/

#guard raveningWargCard.keywords.deathtouch
#guard raveningWargCard.triggeredAbilities == #[.onAttackFerociousGainLife 2]
#guard raveningWargCard.power == some 2
#guard raveningWargCard.toughness == some 2
#guard withWarg.hasDeathtouch (namedPermanent withWarg "Ravening Warg")
#guard (withWarg.effectiveKeywords (namedPermanent withWarg "Ravening Warg")).deathtouch
#guard withWarg.power (namedPermanent withWarg "Ravening Warg") == 2

/-- Alone, Ravening Warg is 2/2, so Ferocious does not trigger. -/
def wargAloneAttackDeclared : Game :=
  let g := passBoth (skipTo withWarg .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargAloneAttackDeclared.stack.isEmpty
#guard !wargAloneAttackDeclared.log.any (fun s => mentions s "attack trigger")
#guard (namedPermanent wargAloneAttackDeclared "Ravening Warg").status.attacking
#guard (wargAloneAttackDeclared.player ⟨0⟩).life == 20

/-- A 3-power creature you control is not enough for Ferocious. -/
def wargAndGiant : Game :=
  addPermanent withWarg hillGiant ⟨0⟩ ⟨0⟩

def wargAttackWithGiant : Game :=
  let g := passBoth (skipTo wargAndGiant .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargAttackWithGiant.stack.isEmpty
#guard !wargAttackWithGiant.log.any (fun s => mentions s "attack trigger")
#guard wargAndGiant.greatestPowerAmongCreatures ⟨0⟩ == 3

/-- An opponent's 4-power creature does not enable Ferocious. -/
def wargVsOppBaloth : Game :=
  addPermanent withWarg rumblingBaloth ⟨1⟩ ⟨1⟩

def wargAttackVsOppBaloth : Game :=
  let g := passBoth (skipTo wargVsOppBaloth .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargAttackVsOppBaloth.stack.isEmpty
#guard !wargAttackVsOppBaloth.log.any (fun s => mentions s "attack trigger")
#guard wargVsOppBaloth.greatestPowerAmongCreatures ⟨0⟩ == 2
#guard wargVsOppBaloth.greatestPowerAmongCreatures ⟨1⟩ == 4

/-- A 4-power creature you control makes Ferocious trigger. -/
def wargAndBaloth : Game :=
  addPermanent withWarg rumblingBaloth ⟨0⟩ ⟨0⟩

#guard wargAndBaloth.greatestPowerAmongCreatures ⟨0⟩ == 4
#guard wargAndBaloth.triggerConditionHolds ⟨0⟩ (.onAttackFerociousGainLife 2)
#guard !withWarg.triggerConditionHolds ⟨0⟩ (.onAttackFerociousGainLife 2)
#guard withWarg.triggerConditionHolds ⟨0⟩ (.onAttackScry 1)

def wargFerociousDeclared : Game :=
  let g := passBoth (skipTo wargAndBaloth .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargFerociousDeclared.stack.size == 1
#guard (wargFerociousDeclared.object! wargFerociousDeclared.stack.back!.objectId).name ==
  "Ravening Warg's ability"
#guard (wargFerociousDeclared.object! wargFerociousDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackFerociousGainLife 2)
#guard (wargFerociousDeclared.object! wargFerociousDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent wargFerociousDeclared "Ravening Warg").id
#guard wargFerociousDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard wargFerociousDeclared.hasPriority ⟨0⟩
#guard (namedPermanent wargFerociousDeclared "Ravening Warg").status.attacking
#guard !(namedPermanent wargFerociousDeclared "Rumbling Baloth").status.attacking

def wargFerociousResolved : Game := passBoth wargFerociousDeclared

#guard wargFerociousResolved.stack.isEmpty
#guard (wargFerociousResolved.player ⟨0⟩).life == 22
#guard wargFerociousResolved.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")
#guard wargFerociousResolved.battlefield.any (fun o => o.name == "Ravening Warg")

/-- The 4-power creature need not attack; another creature attacking without the
Warg does not trigger Ferocious. -/
def balothAttacksWhileWargIdle : Game :=
  let g := passBoth (skipTo wargAndBaloth .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Rumbling Baloth").id])

#guard balothAttacksWhileWargIdle.stack.isEmpty
#guard !balothAttacksWhileWargIdle.log.any (fun s => mentions s "attack trigger")
#guard (namedPermanent balothAttacksWhileWargIdle "Rumbling Baloth").status.attacking
#guard !(namedPermanent balothAttacksWhileWargIdle "Ravening Warg").status.attacking

/-- Ferocious is not rechecked on resolution (CR 603.4). -/
def wargFerociousBalothGone : Game :=
  let id := (namedPermanent wargFerociousDeclared "Rumbling Baloth").id
  let (g, _) := wargFerociousDeclared.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (wargFerociousBalothGone.player ⟨0⟩).life == 22
#guard !(wargFerociousBalothGone.battlefield.any (fun o => o.name == "Rumbling Baloth"))
#guard wargFerociousBalothGone.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")

/-- The trigger still gains life if Ravening Warg has left (CR 113.7a). -/
def wargFerociousSourceGone : Game :=
  let id := (namedPermanent wargFerociousDeclared "Ravening Warg").id
  let (g, _) := wargFerociousDeclared.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (wargFerociousSourceGone.player ⟨0⟩).life == 22
#guard !(wargFerociousSourceGone.battlefield.any (fun o => o.name == "Ravening Warg"))
#guard wargFerociousSourceGone.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")

/-- Ravening Warg itself at power 4 or greater also enables Ferocious. -/
def wargPumpedToFive : Game :=
  let o := namedPermanent withWarg "Ravening Warg"
  withWarg.setObject { o with status := { o.status with pump := (3, 3) } }

#guard wargPumpedToFive.power (namedPermanent wargPumpedToFive "Ravening Warg") == 5
#guard wargPumpedToFive.triggerConditionHolds ⟨0⟩ (.onAttackFerociousGainLife 2)

def wargPumpedAttackDeclared : Game :=
  let g := passBoth (skipTo wargPumpedToFive .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargPumpedAttackDeclared.stack.size == 1
#guard (wargPumpedAttackDeclared.object! wargPumpedAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackFerociousGainLife 2)

def wargPumpedAttackResolved : Game := passBoth wargPumpedAttackDeclared

#guard (wargPumpedAttackResolved.player ⟨0⟩).life == 22

/-- 2 deathtouch combat damage destroys a 3/3 (CR 704.5h); the Warg dies to 3. -/
def wargVsGiant : Game :=
  addPermanent withWarg hillGiant ⟨1⟩ ⟨1⟩

def wargVsGiantAfterDamage : Game :=
  let g := passBoth (skipTo wargVsGiant .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Hill Giant").id,
    (namedPermanent g "Ravening Warg").id)])
  passBoth g

#guard !(wargVsGiantAfterDamage.battlefield.any (fun o => o.name == "Hill Giant"))
#guard !(wargVsGiantAfterDamage.battlefield.any (fun o => o.name == "Ravening Warg"))
#guard wargVsGiantAfterDamage.objects.any (fun o =>
  o.name == "Hill Giant" && o.zone == .graveyard ⟨1⟩)
#guard wargVsGiantAfterDamage.objects.any (fun o =>
  o.name == "Ravening Warg" && o.zone == .graveyard ⟨0⟩)
#guard wargVsGiantAfterDamage.log.any (fun s =>
  mentions s "Ravening Warg deals 2 combat damage to Hill Giant")
#guard wargVsGiantAfterDamage.log.any (fun s => mentions s "Hill Giant dies from deathtouch")
#guard wargVsGiantAfterDamage.log.any (fun s =>
  mentions s "Ravening Warg dies from lethal damage")

/-- Without deathtouch, 2 damage does not kill a 3/3. -/
def ogreVsGiantAfterDamage : Game :=
  let g := addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) hillGiant ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Hill Giant").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard ogreVsGiantAfterDamage.battlefield.any (fun o => o.name == "Hill Giant")
#guard !(ogreVsGiantAfterDamage.battlefield.any (fun o => o.name == "Gray Ogre"))
#guard (namedPermanent ogreVsGiantAfterDamage "Hill Giant").status.damage == 2
#guard !ogreVsGiantAfterDamage.log.any (fun s => mentions s "dies from deathtouch")

/-- Indestructible ignores deathtouch (CR 702.12b / 704.5h); the flag clears. -/
def wargVsIndestructibleFlyer : Game :=
  addPermanent withWarg indestructibleFlyer ⟨1⟩ ⟨1⟩

def wargVsIndestructibleAfterDamage : Game :=
  let g := passBoth (skipTo wargVsIndestructibleFlyer .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Indestructible Flyer").id,
    (namedPermanent g "Ravening Warg").id)])
  passBoth g

#guard wargVsIndestructibleAfterDamage.battlefield.any (fun o =>
  o.name == "Indestructible Flyer")
#guard !(wargVsIndestructibleAfterDamage.battlefield.any (fun o =>
  o.name == "Ravening Warg"))
#guard (namedPermanent wargVsIndestructibleAfterDamage "Indestructible Flyer").status.damage == 2
#guard !(namedPermanent wargVsIndestructibleAfterDamage "Indestructible Flyer").status.dealtDeathtouch
#guard !wargVsIndestructibleAfterDamage.log.any (fun s =>
  mentions s "Indestructible Flyer dies from deathtouch")

/-- Deathtouch plus trample: 1 damage is lethal, so leftover tramples (CR 702.2c). -/
def deathtouchTrampler : CardDef :=
  creature "Deathtouch Trampler" ManaCost.empty #[] 2 2
    (keywords := Keyword.deathtouch.merge Keyword.trample)

def tramplerVsBalothAfterDamage : Game :=
  let g := addPermanent started deathtouchTrampler ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Deathtouch Trampler").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Rumbling Baloth").id,
    (namedPermanent g "Deathtouch Trampler").id)])
  passBoth g

#guard tramplerVsBalothAfterDamage.log.any (fun s =>
  mentions s "Deathtouch Trampler deals 1 combat damage to Rumbling Baloth")
#guard tramplerVsBalothAfterDamage.log.any (fun s =>
  mentions s "Deathtouch Trampler tramples for 1 to Nissa")
#guard (tramplerVsBalothAfterDamage.player ⟨1⟩).life == 19
#guard !(tramplerVsBalothAfterDamage.battlefield.any (fun o => o.name == "Rumbling Baloth"))
#guard tramplerVsBalothAfterDamage.log.any (fun s =>
  mentions s "Rumbling Baloth dies from deathtouch")

/-- Quarrel from Ravening Warg applies deathtouch to the damage it deals. -/
def quarrelWargVsGiant : Game :=
  let g := addPermanent afterDraw raveningWargCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

def resolvedQuarrelWarg : Game :=
  let g := mustApply quarrelWargVsGiant ⟨0⟩
    (.cast (handCardNamed quarrelWargVsGiant ⟨0⟩ "Quarrel").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Ravening Warg").id))
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Hill Giant").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedQuarrelWarg.battlefield.any (fun o => o.name == "Ravening Warg")
#guard !(resolvedQuarrelWarg.battlefield.any (fun o => o.name == "Hill Giant"))
#guard resolvedQuarrelWarg.log.any (fun s =>
  mentions s "Ravening Warg deals 2 damage to Hill Giant")
#guard resolvedQuarrelWarg.log.any (fun s => mentions s "Hill Giant dies from deathtouch")

/- Night's Whisper: you draw two cards and lose 2 life (CR 121 / 118.3a). -/

#guard nightsWhisper.isSorcery
#guard nightsWhisper.hasSorcerySpeed
#guard !nightsWhisper.hasInstantSpeed
#guard nightsWhisper.spellEffect == some (Effect.drawAndLoseLife 2 2)
#guard nightsWhisper.hasCastKind .draw
#guard !nightsWhisper.requiresTarget
#guard mentions nightsWhisper.summary "draw two cards"
#guard mentions nightsWhisper.summary "lose 2 life"

-- Direct resolution draws that many cards and loses that much life.
#guard
  let g := addToLibraryTop (addToLibraryTop afterDraw forest ⟨0⟩) swamp ⟨0⟩
  let beforeHand := (g.player ⟨0⟩).hand.size
  let g := g.applyEffect ⟨0⟩ (Effect.drawAndLoseLife 2 2) #[]
  (g.player ⟨0⟩).hand.size == beforeHand + 2 &&
    (g.player ⟨0⟩).life == 18 &&
    (g.handObjects ⟨0⟩).any (fun o => o.name == "Swamp") &&
    (g.handObjects ⟨0⟩).any (fun o => o.name == "Forest") &&
    g.log.any (fun s => mentions s "draws Swamp") &&
    g.log.any (fun s => mentions s "draws Forest") &&
    g.log.any (fun s => mentions s "loses 2 life (18 life)") &&
    !g.log.any (fun s => mentions s "is dealt 2 damage")

-- Losing 0 life does nothing (CR 118.9). Drawing 0 cards is a no-op.
#guard
  let g := afterDraw.applyEffect ⟨0⟩ (Effect.drawAndLoseLife 0 0) #[]
  (g.player ⟨0⟩).life == 20 &&
    (g.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size &&
    !g.log.any (fun s => mentions s "loses 0 life")

/-- Night's Whisper in hand with enough black mana. -/
def nightsWhisperSetup : Game :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withBlackMana (addToHand g nightsWhisper ⟨0⟩) ⟨0⟩ 2

#guard nightsWhisperSetup.canCast ⟨0⟩
  (handCardNamed nightsWhisperSetup ⟨0⟩ "Night's Whisper")
#guard nightsWhisperSetup.asSorcery? ⟨0⟩

-- Sorcery speed: illegal in the end step.
#guard
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  let g := withBlackMana (addToHand g nightsWhisper ⟨0⟩) ⟨0⟩ 2
  let g := skipTo g .end 80
  g.step == .end && !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Night's Whisper")

def proposedNightsWhisper : Game :=
  mustApply nightsWhisperSetup ⟨0⟩
    (.cast (handCardNamed nightsWhisperSetup ⟨0⟩ "Night's Whisper").id)

#guard proposedNightsWhisper.pending == .activateManaAbilities ⟨0⟩
#guard proposedNightsWhisper.log.any (fun s => mentions s "begins casting Night's Whisper")
#guard proposedNightsWhisper.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard !proposedNightsWhisper.log.any (fun s => mentions s "must choose a target")

def paidNightsWhisper : Game := mustApply proposedNightsWhisper ⟨0⟩ .pay

#guard paidNightsWhisper.hasPriority ⟨0⟩
#guard paidNightsWhisper.stack.size == 1
#guard (paidNightsWhisper.object! paidNightsWhisper.stack.back!.objectId).name ==
  "Night's Whisper"
#guard paidNightsWhisper.log.any (fun s => mentions s "casts Night's Whisper")

/-- Known library: Swamp then Forest are drawn on resolution (CR 121). -/
def nightsWhisperKnownLib : Game :=
  addToLibraryTop (addToLibraryTop paidNightsWhisper forest ⟨0⟩) swamp ⟨0⟩

def resolvedNightsWhisper : Game := passBoth nightsWhisperKnownLib

#guard resolvedNightsWhisper.stack.isEmpty
#guard resolvedNightsWhisper.hasPriority ⟨0⟩
#guard (resolvedNightsWhisper.player ⟨0⟩).hand.size ==
  (nightsWhisperKnownLib.player ⟨0⟩).hand.size + 2
#guard (resolvedNightsWhisper.handObjects ⟨0⟩).any (fun o => o.name == "Swamp")
#guard (resolvedNightsWhisper.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard (resolvedNightsWhisper.player ⟨0⟩).life == 18
#guard (resolvedNightsWhisper.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedNightsWhisper.object! id).name == "Night's Whisper")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "draws Swamp")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "draws Forest")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "loses 2 life (18 life)")
#guard !resolvedNightsWhisper.log.any (fun s => mentions s "is dealt 2 damage")

/-- Drawing from an empty library is a state-based loss (CR 704.5b / 121.4). -/
def nightsWhisperEmptyLib : Game :=
  let g := paidNightsWhisper.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  passBoth g

#guard nightsWhisperEmptyLib.over
#guard nightsWhisperEmptyLib.result == some (.won ⟨1⟩)
#guard (nightsWhisperEmptyLib.player ⟨0⟩).lost
#guard nightsWhisperEmptyLib.log.any (fun s => mentions s "tries to draw from an empty library")
#guard nightsWhisperEmptyLib.log.any (fun s => mentions s "loses the game (drew from empty library)")

/-- Losing the last 2 life ends the game (CR 704.5a). The spell is still legal. -/
def nightsWhisperPaysLastLife : Game :=
  let g := paidNightsWhisper.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  passBoth g

#guard (nightsWhisperPaysLastLife.player ⟨0⟩).life == 0
#guard nightsWhisperPaysLastLife.over
#guard nightsWhisperPaysLastLife.result == some (.won ⟨1⟩)
#guard nightsWhisperPaysLastLife.log.any (fun s => mentions s "loses 2 life (0 life)")
#guard nightsWhisperPaysLastLife.log.any (fun s => mentions s "loses the game (life total 0)")

/-- The agent casts Night's Whisper when that is the playable spell. -/
def agentNightsWhisperOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withBlackMana (addToHand g nightsWhisper ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentNightsWhisperOnly ⟨0⟩ with
  | some (.cast id) => (agentNightsWhisperOnly.object! id).name == "Night's Whisper"
  | _ => false

-- The heuristic will not lose the last 2 life.
#guard
  let g := agentNightsWhisperOnly.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  match Agent.choose g ⟨0⟩ with
  | some (.cast _) => false
  | _ => true

-- The heuristic will not draw into an empty library.
#guard
  let g := agentNightsWhisperOnly.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  match Agent.choose g ⟨0⟩ with
  | some (.cast _) => false
  | _ => true

-- The heuristic still casts at 3 life (survives at 1).
#guard
  let g := agentNightsWhisperOnly.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 3 })
  match Agent.choose g ⟨0⟩ with
  | some (.cast id) => (g.object! id).name == "Night's Whisper"
  | _ => false

-- The heuristic still attacks with Ravening Warg.
#guard
  let g := passBoth (skipTo wargAndBaloth .beginningOfCombat 80)
  match Agent.choose g ⟨0⟩ with
  | some (.declareAttackers ids _ _) =>
    ids.contains (namedPermanent g "Ravening Warg").id
  | _ => false

-- Nasty Little Rabbit: Ferocious beginning of combat puts a +1/+1 counter.

#guard nastyLittleRabbit.triggeredAbilities == #[.onYourBeginCombatFerociousPlusOne]
#guard nastyLittleRabbit.subtypes == #["Rabbit"]
#guard nastyLittleRabbit.power == some 1
#guard nastyLittleRabbit.toughness == some 2

def rabbitAndBaloth : Game :=
  addPermanent (addPermanent started nastyLittleRabbit ⟨0⟩ ⟨0⟩) rumblingBaloth ⟨0⟩ ⟨0⟩

#guard rabbitAndBaloth.triggerConditionHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne

-- Alone, Nasty Little Rabbit is 1/2, so Ferocious does not trigger.
#guard
  let g := skipTo (addPermanent started nastyLittleRabbit ⟨0⟩ ⟨0⟩) .beginningOfCombat 80
  g.stack.isEmpty &&
    (namedPermanent g "Nasty Little Rabbit").status.plusOnePlusOne == 0 &&
    !g.triggerConditionHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne

def rabbitBeginCombat : Game :=
  skipTo rabbitAndBaloth .beginningOfCombat 80

#guard rabbitBeginCombat.step == .beginningOfCombat
#guard rabbitBeginCombat.stack.size == 1
#guard (rabbitBeginCombat.object! rabbitBeginCombat.stack.back!.objectId).triggeredAbility ==
  some .onYourBeginCombatFerociousPlusOne
#guard rabbitBeginCombat.log.any (fun s => mentions s "begin-combat trigger")

def rabbitBeginCombatResolved : Game := passBoth rabbitBeginCombat

#guard rabbitBeginCombatResolved.stack.isEmpty
#guard (namedPermanent rabbitBeginCombatResolved "Nasty Little Rabbit").status.plusOnePlusOne == 1
#guard rabbitBeginCombatResolved.power
  (namedPermanent rabbitBeginCombatResolved "Nasty Little Rabbit") == 2
#guard rabbitBeginCombatResolved.toughness
  (namedPermanent rabbitBeginCombatResolved "Nasty Little Rabbit") == 3

end Mtg.Engine.Tests
