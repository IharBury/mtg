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
import Mtg.Engine.Tests.Adventures

/-!
# Cast triggers, additional costs, and activated keyword grants.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Inferno Titan: {R} pump and enters-or-attacks divided damage (CR 601.2d / 508.2). -/

def titanAbility : ActivatedAbility :=
  infernoTitan.activatedAbilities[0]!

#guard titanAbility.effect == Effect.sourceGets 1 0
#guard titanAbility.cost.mana == ManaCost.ofColor .red
#guard !titanAbility.effect.requiresTarget
#guard infernoTitan.triggeredAbilities == #[.onEnterOrAttackDealDividedDamage 3 3]

/-- Inferno Titan in hand with enough mana to cast it. -/
def titanSetup : Game :=
  withRedMana (addToHand afterDraw infernoTitan ⟨0⟩) ⟨0⟩ 6

#guard titanSetup.canCast ⟨0⟩ (handCardNamed titanSetup ⟨0⟩ "Inferno Titan")
#guard titanSetup.asSorcery? ⟨0⟩
#guard infernoTitan.hasSorcerySpeed

def proposedTitan : Game :=
  mustApply titanSetup ⟨0⟩ (.cast (handCardNamed titanSetup ⟨0⟩ "Inferno Titan").id)

#guard proposedTitan.pending == .activateManaAbilities ⟨0⟩
#guard proposedTitan.log.any (fun s => mentions s "begins casting Inferno Titan")

def paidTitan : Game := mustApply proposedTitan ⟨0⟩ .pay

#guard paidTitan.stack.size == 1
#guard paidTitan.hasPriority ⟨0⟩
#guard paidTitan.log.any (fun s => mentions s "casts Inferno Titan")

/-- The creature enters; the divided-damage trigger waits for a division (CR 601.2d). -/
def titanEntered : Game := passBoth paidTitan

#guard (namedPermanent titanEntered "Inferno Titan").printed.power == some 6
#guard titanEntered.power (namedPermanent titanEntered "Inferno Titan") == 6
#guard titanEntered.toughness (namedPermanent titanEntered "Inferno Titan") == 6
#guard titanEntered.stack.size == 1
#guard (titanEntered.object! titanEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterOrAttackDealDividedDamage 3 3)
#guard (titanEntered.object! titanEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent titanEntered "Inferno Titan").id
#guard titanEntered.stack.back!.targets.isEmpty
#guard titanEntered.stack.back!.dividedDamage.isEmpty
#guard titanEntered.pending == .chooseTargets ⟨0⟩
#guard titanEntered.actor == some ⟨0⟩
#guard !titanEntered.hasPriority ⟨0⟩
#guard titanEntered.log.any (fun s => mentions s "enters the battlefield")
#guard titanEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard titanEntered.log.any (fun s => mentions s "must divide 3 damage")
#guard titanEntered.announcingDividedDamage

-- The heuristic puts all 3 damage on the opponent.
#guard
  match Agent.choose titanEntered ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def titanTargetedOpponent : Game :=
  mustApply titanEntered ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard titanTargetedOpponent.pending == .none
#guard titanTargetedOpponent.hasPriority ⟨0⟩
#guard titanTargetedOpponent.stack.back!.targets == #[Target.player ⟨1⟩]
#guard titanTargetedOpponent.stack.back!.dividedDamage == #[3]
#guard titanTargetedOpponent.log.any (fun s =>
  mentions s "chooses Nissa to be dealt 3 damage (CR 601.2d)")

def titanResolvedOpponent : Game := passBoth titanTargetedOpponent

#guard titanResolvedOpponent.stack.isEmpty
#guard (titanResolvedOpponent.player ⟨1⟩).life == 17
#guard (titanResolvedOpponent.player ⟨0⟩).life == 20
#guard titanResolvedOpponent.log.any (fun s => mentions s "Nissa is dealt 3 damage")
#guard titanResolvedOpponent.battlefield.any (fun o => o.name == "Inferno Titan")

/-- Split 2 to the opponent and 1 to a creature. -/
def titanSplitAnnounced : Game :=
  let g := addPermanent titanEntered grizzlyBears ⟨1⟩ ⟨1⟩
  mustApply g ⟨0⟩
    (.divideDamage #[
      (Target.player ⟨1⟩, 2),
      (Target.permanent (namedPermanent g "Grizzly Bears").id, 1)])

#guard titanSplitAnnounced.stack.back!.dividedDamage == #[2, 1]

def titanSplitResolved : Game := passBoth titanSplitAnnounced

#guard (titanSplitResolved.player ⟨1⟩).life == 18
#guard (namedPermanent titanSplitResolved "Grizzly Bears").status.damage == 1

/-- Inferno Titan already in play so it can attack (no ETB from `addPermanent`). -/
def titanOnBattlefield : Game :=
  addPermanent started infernoTitan ⟨0⟩ ⟨0⟩

def titanAttackDeclared : Game :=
  let g := passBoth (skipTo titanOnBattlefield .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Inferno Titan").id])

#guard titanAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard titanAttackDeclared.stack.size == 1
#guard (titanAttackDeclared.object! titanAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onEnterOrAttackDealDividedDamage 3 3)
#guard (titanAttackDeclared.object! titanAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent titanAttackDeclared "Inferno Titan").id
#guard titanAttackDeclared.stack.back!.targets.isEmpty
#guard titanAttackDeclared.stack.back!.dividedDamage.isEmpty
#guard titanAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard titanAttackDeclared.log.any (fun s => mentions s "must divide 3 damage")
#guard titanAttackDeclared.announcingDividedDamage
#guard !titanAttackDeclared.hasPriority ⟨0⟩
#guard titanAttackDeclared.actor == some ⟨0⟩
#guard (namedPermanent titanAttackDeclared "Inferno Titan").status.attacking

-- The heuristic still dumps all 3 on the opponent on attack.
#guard
  match Agent.choose titanAttackDeclared ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def titanAttackResolved : Game :=
  let g := mustApply titanAttackDeclared ⟨0⟩ (.target (Target.player ⟨1⟩))
  passBoth g

#guard titanAttackResolved.stack.isEmpty
#guard (titanAttackResolved.player ⟨1⟩).life == 17
#guard titanAttackResolved.log.any (fun s => mentions s "Nissa is dealt 3 damage")
#guard (namedPermanent titanAttackResolved "Inferno Titan").status.attacking

/-- The trigger still deals damage if Inferno Titan has left (CR 113.7a). -/
def titanLeftBeforeAttackTrigger : Game :=
  let g := mustApply titanAttackDeclared ⟨0⟩ (.target (Target.player ⟨1⟩))
  let id := (namedPermanent g "Inferno Titan").id
  let (g, _) := g.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (titanLeftBeforeAttackTrigger.player ⟨1⟩).life == 17
#guard !(titanLeftBeforeAttackTrigger.battlefield.any (fun o => o.name == "Inferno Titan"))

/-- Inferno Titan in play with {R} in the pool; a land drop is already used. -/
def titanPumpReady : Game :=
  let g := addPermanent afterDraw infernoTitan ⟨0⟩ ⟨0⟩
  withRedMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 1

def titanSource (g : Game) : GameObject :=
  namedPermanent g "Inferno Titan"

#guard titanPumpReady.canActivate ⟨0⟩ (titanSource titanPumpReady) titanAbility
#guard !(titanPumpReady.canActivate ⟨1⟩ (titanSource titanPumpReady) titanAbility)
#guard (titanPumpReady.player ⟨0⟩).manaPool.canPay titanAbility.cost.mana
#guard titanPumpReady.power (titanSource titanPumpReady) == 6

-- The heuristic pumps Inferno Titan when {R} is available.
#guard
  match Agent.choose titanPumpReady ⟨0⟩ with
  | some (.activate id 0) => id == (titanSource titanPumpReady).id
  | _ => false

def proposedTitanPump : Game :=
  mustApply titanPumpReady ⟨0⟩ (.activate (titanSource titanPumpReady).id 0)

#guard proposedTitanPump.pending == .activateManaAbilities ⟨0⟩
#guard proposedTitanPump.proposedSpell.isSome
#guard proposedTitanPump.stack.size == 1
#guard (proposedTitanPump.object! proposedTitanPump.stack.back!.objectId).abilityEffect ==
  some (Effect.sourceGets 1 0)
#guard proposedTitanPump.log.any (fun s => mentions s "begins activating Inferno Titan")

def paidTitanPump : Game :=
  mustApply proposedTitanPump ⟨0⟩ .pay

#guard paidTitanPump.hasPriority ⟨0⟩
#guard paidTitanPump.stack.size == 1
#guard paidTitanPump.log.any (fun s => mentions s "activates Inferno Titan")
#guard (namedPermanent paidTitanPump "Inferno Titan").status.pumpPower == 0

def pumpedTitan : Game := passBoth paidTitanPump

#guard pumpedTitan.stack.isEmpty
#guard (namedPermanent pumpedTitan "Inferno Titan").status.pumpPower == 1
#guard pumpedTitan.power (namedPermanent pumpedTitan "Inferno Titan") == 7
#guard pumpedTitan.log.any (fun s => mentions s "Inferno Titan gets +1/+0 until end of turn")

/-- A second activation stacks. -/
def titanPumpedTwice : Game :=
  let g := withRedMana pumpedTitan ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.activate (titanSource g).id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard titanPumpedTwice.power (namedPermanent titanPumpedTwice "Inferno Titan") == 8
#guard (namedPermanent titanPumpedTwice "Inferno Titan").status.pumpPower == 2

/-- The +1/+0 wears off in cleanup. -/
def afterTitanCleanup : Game :=
  passBoth (skipTo pumpedTitan .end 80)

#guard afterTitanCleanup.power (namedPermanent afterTitanCleanup "Inferno Titan") == 6
#guard (namedPermanent afterTitanCleanup "Inferno Titan").status.pumpPower == 0

/-- If the source leaves before the pump resolves, the pump does not happen. -/
def titanPumpSourceGone : Game :=
  let id := (namedPermanent paidTitanPump "Inferno Titan").id
  let (g, _) := paidTitanPump.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard titanPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard titanPumpSourceGone.stack.isEmpty
#guard !(titanPumpSourceGone.battlefield.any (fun o => o.name == "Inferno Titan"))

-- Instant-speed: Inferno Titan can activate during the end step.
def titanAtEndStep : Game := skipTo titanPumpReady .end 80

#guard titanAtEndStep.step == .end
#guard titanAtEndStep.canActivate ⟨0⟩ (titanSource titanAtEndStep) titanAbility

/-- The agent casts Inferno Titan when that is the playable spell. -/
def agentTitanOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g infernoTitan ⟨0⟩) ⟨0⟩ 6

#guard
  match Agent.choose agentTitanOnly ⟨0⟩ with
  | some (.cast id) => (agentTitanOnly.object! id).name == "Inferno Titan"
  | _ => false

/- Guttersnipe: whenever you cast an instant or sorcery, 2 damage to each opponent. -/

#guard guttersnipe.triggeredAbilities == #[.onCastInstantOrSorceryDealDamageToEachOpponent 2]
#guard lightningBolt.isInstantOrSorcery
#guard !grayOgre.isInstantOrSorcery

/-- Guttersnipe in play with Lightning Bolt in hand and {R} in the pool. -/
def guttersnipeBoltSetup : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1

#guard guttersnipeBoltSetup.canCast ⟨0⟩
  (handCardNamed guttersnipeBoltSetup ⟨0⟩ "Lightning Bolt")
#guard (guttersnipeBoltSetup.player ⟨1⟩).life == 20

/-- Propose, announce Nissa, and pay. The trigger goes on the stack above the Bolt
(CR 601.2i / 603.3). -/
def paidGuttersnipeBolt : Game :=
  let g := mustApply guttersnipeBoltSetup ⟨0⟩
    (.cast (handCardNamed guttersnipeBoltSetup ⟨0⟩ "Lightning Bolt").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidGuttersnipeBolt.hasPriority ⟨0⟩
#guard paidGuttersnipeBolt.pending == .none
#guard paidGuttersnipeBolt.stack.size == 2
#guard (paidGuttersnipeBolt.object! paidGuttersnipeBolt.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidGuttersnipeBolt.object! paidGuttersnipeBolt.stack[0]!.objectId).name == "Lightning Bolt"
#guard paidGuttersnipeBolt.log.any (fun s => mentions s "casts Lightning Bolt")
#guard paidGuttersnipeBolt.log.any (fun s => mentions s "cast trigger is put on the stack")
#guard (paidGuttersnipeBolt.player ⟨1⟩).life == 20

/-- The trigger resolves first, then the Bolt. -/
def guttersnipeTriggerResolved : Game := passBoth paidGuttersnipeBolt

#guard guttersnipeTriggerResolved.stack.size == 1
#guard (guttersnipeTriggerResolved.object! guttersnipeTriggerResolved.stack.back!.objectId).name ==
  "Lightning Bolt"
#guard (guttersnipeTriggerResolved.player ⟨1⟩).life == 18
#guard guttersnipeTriggerResolved.log.any (fun s => mentions s "Nissa is dealt 2 damage")

def guttersnipeBoltResolved : Game := passBoth guttersnipeTriggerResolved

#guard guttersnipeBoltResolved.stack.isEmpty
#guard (guttersnipeBoltResolved.player ⟨1⟩).life == 15
#guard guttersnipeBoltResolved.log.any (fun s => mentions s "Nissa is dealt 3 damage")

-- Casting a creature does not trigger Guttersnipe.
def paidOgreWithGuttersnipe : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  let g := withRedMana (addToHand g grayOgre ⟨0⟩) ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Gray Ogre").id)
  mustApply g ⟨0⟩ .pay

#guard paidOgreWithGuttersnipe.stack.size == 1
#guard (paidOgreWithGuttersnipe.object! paidOgreWithGuttersnipe.stack.back!.objectId).name ==
  "Gray Ogre"
#guard !paidOgreWithGuttersnipe.log.any (fun s => mentions s "cast trigger")
#guard (paidOgreWithGuttersnipe.player ⟨1⟩).life == 20

-- An opponent's Guttersnipe does not trigger when you cast a spell.
def paidBoltOppGuttersnipe : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Lightning Bolt").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidBoltOppGuttersnipe.stack.size == 1
#guard (paidBoltOppGuttersnipe.object! paidBoltOppGuttersnipe.stack.back!.objectId).name ==
  "Lightning Bolt"
#guard !paidBoltOppGuttersnipe.log.any (fun s => mentions s "cast trigger")

-- Two Guttersnipes both trigger; the controller chooses stack order (CR 603.3b).
def paidBoltTwoGuttersnipesPending : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := addPermanent g guttersnipe ⟨0⟩ ⟨0⟩
  let g := withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Lightning Bolt").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidBoltTwoGuttersnipesPending.pending == .chooseTriggerToStack ⟨0⟩
#guard paidBoltTwoGuttersnipesPending.stack.size == 1
#guard paidBoltTwoGuttersnipesPending.waitingTriggers.size == 2
#guard paidBoltTwoGuttersnipesPending.log.any (fun s => mentions s "CR 603.3b")

def paidBoltTwoGuttersnipes : Game := applyIdle paidBoltTwoGuttersnipesPending

#guard paidBoltTwoGuttersnipes.stack.size == 3
#guard (paidBoltTwoGuttersnipes.object! paidBoltTwoGuttersnipes.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidBoltTwoGuttersnipes.object!
  paidBoltTwoGuttersnipes.stack[1]!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)

def twoGuttersnipesResolved : Game :=
  passBoth (passBoth (passBoth paidBoltTwoGuttersnipes))

#guard twoGuttersnipesResolved.stack.isEmpty
#guard (twoGuttersnipesResolved.player ⟨1⟩).life == 13

/-- The trigger still deals damage if Guttersnipe leaves before it resolves
(CR 113.7 / 608.2g). -/
def guttersnipeGoneResolved : Game :=
  let id := (namedPermanent paidGuttersnipeBolt "Guttersnipe").id
  let (g, _) := paidGuttersnipeBolt.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(guttersnipeGoneResolved.battlefield.any (fun o => o.name == "Guttersnipe"))
#guard (guttersnipeGoneResolved.player ⟨1⟩).life == 18
#guard guttersnipeGoneResolved.log.any (fun s => mentions s "Nissa is dealt 2 damage")

/-- Lethal Guttersnipe damage ends the game before the spell resolves. -/
def guttersnipeLethal : Game :=
  let g := paidGuttersnipeBolt.modifyPlayer ⟨1⟩ (fun pl => { pl with life := 2 })
  passBoth g

#guard guttersnipeLethal.over
#guard guttersnipeLethal.result == some (.won ⟨0⟩)
#guard (guttersnipeLethal.player ⟨1⟩).life == 0
#guard guttersnipeLethal.log.any (fun s => mentions s "Nissa loses the game")
#guard guttersnipeLethal.log.any (fun s => mentions s "Chandra wins the game")
#guard guttersnipeLethal.stack.size == 1

-- A sorcery Adventure is an instant-or-sorcery spell (CR 715.3b / 601.2i).
def paidSpewWithGuttersnipe : Game :=
  let g := addPermanent smaugSetup guttersnipe ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Smaug, the Great Calamity").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

#guard paidSpewWithGuttersnipe.stack.size == 2
#guard (paidSpewWithGuttersnipe.object! paidSpewWithGuttersnipe.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidSpewWithGuttersnipe.object! paidSpewWithGuttersnipe.stack[0]!.objectId).name ==
  "Spew Flame"
#guard paidSpewWithGuttersnipe.log.any (fun s => mentions s "casts Spew Flame")
#guard paidSpewWithGuttersnipe.log.any (fun s => mentions s "cast trigger is put on the stack")

def spewWithGuttersnipeResolved : Game :=
  passBoth (passBoth paidSpewWithGuttersnipe)

#guard (spewWithGuttersnipeResolved.player ⟨1⟩).life == 18
#guard !(spewWithGuttersnipeResolved.battlefield.any (fun o => o.name == "Grizzly Bears"))

-- The heuristic casts Bolt when that is the playable spell with Guttersnipe in play.
def agentGuttersnipeBoltOnly : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1

#guard
  match Agent.choose agentGuttersnipeBoltOnly ⟨0⟩ with
  | some (.cast id) => (agentGuttersnipeBoltOnly.object! id).name == "Lightning Bolt"
  | _ => false

/- Improvised Club: additional cost sacrifice an artifact or creature, then 4 damage. -/

def clubReady : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g mountain
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

def clubFodder (g : Game) : GameObject :=
  namedPermanent g "Raging Goblin"

def clubNoFodder : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

#guard clubReady.canCast ⟨0⟩ (handCardNamed clubReady ⟨0⟩ "Improvised Club")
#guard !(clubNoFodder.canCast ⟨0⟩ (handCardNamed clubNoFodder ⟨0⟩ "Improvised Club"))
#guard (clubReady.player ⟨0⟩).manaPool.canPay improvisedClub.manaCost
#guard clubReady.hasPriority ⟨0⟩

#guard
  match clubNoFodder.apply ⟨0⟩
      (.cast (handCardNamed clubNoFodder ⟨0⟩ "Improvised Club").id) with
  | .error msg => mentions msg "requires sacrificing an artifact or creature"
  | .ok _ => false

#guard
  match Agent.choose clubReady ⟨0⟩ with
  | some (.cast id) => (clubReady.object! id).name == "Improvised Club"
  | _ => false

#guard
  match Agent.choose clubNoFodder ⟨0⟩ with
  | some .pass => true
  | _ => false

def proposedClub : Game :=
  mustApply clubReady ⟨0⟩ (.cast (handCardNamed clubReady ⟨0⟩ "Improvised Club").id)

#guard
  match proposedClub.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedClub.proposedSpell.isSome
#guard proposedClub.stack.size == 1
#guard proposedClub.log.any (fun s => mentions s "begins casting Improvised Club")
#guard proposedClub.log.any (fun s => mentions s "must choose a target (CR 601.2c)")
#guard (namedPermanent proposedClub "Raging Goblin").isOnBattlefield

#guard
  match Agent.choose proposedClub ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def targetedClub : Game :=
  mustApply proposedClub ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard targetedClub.pending == .activateManaAbilities ⟨0⟩
#guard targetedClub.stack.back!.targets == #[Target.player ⟨1⟩]
#guard targetedClub.log.any (fun s => mentions s "chooses Nissa as a target (CR 601.2c)")
#guard targetedClub.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard
  match targetedClub.proposedSpell with
  | some prop => prop.needsSacrificeOther && prop.kind == .spell
  | none => false

#guard
  match Agent.choose targetedClub ⟨0⟩ with
  | some .pay => true
  | _ => false

def paidClub : Game :=
  mustApply targetedClub ⟨0⟩ .pay

#guard
  match paidClub.pending with
  | .sacrificePermanent p sid =>
    p == ⟨0⟩ && sid == paidClub.stack[0]!.objectId
  | _ => false
#guard paidClub.proposedSpell.isSome
#guard (namedPermanent paidClub "Raging Goblin").isOnBattlefield
#guard paidClub.log.any (fun s => mentions s "must sacrifice an artifact or creature")
#guard !(paidClub.log.any (fun s => mentions s "casts Improvised Club"))
#guard paidClub.stack.size == 1

#guard
  match paidClub.apply ⟨0⟩ (.sacrifice (namedPermanent paidClub "Raging Goblin").id) with
  | .ok _ => true
  | .error _ => false

-- Cannot sacrifice a land, an opponent's creature, or skip the choice.
#guard
  match (paidClub.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match paidClub.apply ⟨0⟩ (.sacrifice land.id) with
    | .error msg => mentions msg "Can't sacrifice"
    | .ok _ => false

#guard
  let g := addPermanent paidClub grizzlyBears ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.sacrifice (namedPermanent g "Grizzly Bears").id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

#guard
  match Agent.choose paidClub ⟨0⟩ with
  | some (.sacrifice id) => id == (clubFodder paidClub).id
  | _ => false

def castClub : Game :=
  mustApply paidClub ⟨0⟩ (.sacrifice (clubFodder paidClub).id)

#guard castClub.pending == .none
#guard castClub.proposedSpell.isNone
#guard castClub.hasPriority ⟨0⟩
#guard castClub.stack.size == 1
#guard (castClub.object! castClub.stack.back!.objectId).name == "Improvised Club"
#guard !(castClub.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard (castClub.player ⟨0⟩).graveyard.any (fun id =>
  (castClub.object! id).name == "Raging Goblin")
#guard castClub.log.any (fun s => mentions s "sacrifices Raging Goblin")
#guard castClub.log.any (fun s => mentions s "casts Improvised Club")
#guard (castClub.player ⟨1⟩).life == 20

def resolvedClub : Game := passBoth castClub

#guard resolvedClub.stack.isEmpty
#guard (resolvedClub.player ⟨1⟩).life == 16
#guard resolvedClub.log.any (fun s => mentions s "Nissa is dealt 4 damage")

-- An artifact is a legal additional-cost sacrifice.
def clubArtifactReady : Game :=
  let g := addPermanent afterDraw wayfarersBauble ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

#guard clubArtifactReady.canCast ⟨0⟩
  (handCardNamed clubArtifactReady ⟨0⟩ "Improvised Club")

def resolvedClubArtifact : Game :=
  let g := mustApply clubArtifactReady ⟨0⟩
    (.cast (handCardNamed clubArtifactReady ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Wayfarer's Bauble").id)
  passBoth g

#guard (resolvedClubArtifact.player ⟨1⟩).life == 16
#guard !(resolvedClubArtifact.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard resolvedClubArtifact.log.any (fun s => mentions s "sacrifices Wayfarer's Bauble")

-- Targeting the creature that is then sacrificed makes the target illegal.
def resolvedClubSacTarget : Game :=
  let g := mustApply clubReady ⟨0⟩
    (.cast (handCardNamed clubReady ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.permanent (clubFodder g).id))
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ (.sacrifice (clubFodder g).id)
  passBoth g

#guard resolvedClubSacTarget.log.any (fun s => mentions s "no longer in play")
#guard (resolvedClubSacTarget.player ⟨1⟩).life == 20
#guard !(resolvedClubSacTarget.battlefield.any (fun o => o.name == "Raging Goblin"))

-- Instant speed: legal in the end step.
def clubAtEnd : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  let g := addToHand g improvisedClub ⟨0⟩
  skipTo g .end 80

#guard clubAtEnd.step == .end
#guard clubAtEnd.canCast ⟨0⟩ (handCardNamed clubAtEnd ⟨0⟩ "Improvised Club")

-- Paying without enough mana reverses the cast; the fodder stays in play.
def reversedClub : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addToHand g improvisedClub ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard reversedClub.stack.isEmpty
#guard reversedClub.hasPriority ⟨0⟩
#guard (reversedClub.handObjects ⟨0⟩).any (fun o => o.name == "Improvised Club")
#guard reversedClub.battlefield.any (fun o => o.name == "Raging Goblin")
#guard reversedClub.log.any (fun s => mentions s "the casting is reversed")

-- Guttersnipe waits until the Club is actually cast, after the additional cost.
def clubGuttersnipeReady : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

def paidClubGuttersnipe : Game :=
  let g := mustApply clubGuttersnipeReady ⟨0⟩
    (.cast (handCardNamed clubGuttersnipeReady ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidClubGuttersnipe.stack.size == 1
#guard !(paidClubGuttersnipe.log.any (fun s => mentions s "cast trigger"))
#guard (namedPermanent paidClubGuttersnipe "Raging Goblin").isOnBattlefield

def castClubGuttersnipe : Game :=
  mustApply paidClubGuttersnipe ⟨0⟩
    (.sacrifice (namedPermanent paidClubGuttersnipe "Raging Goblin").id)

#guard castClubGuttersnipe.stack.size == 2
#guard (castClubGuttersnipe.object! castClubGuttersnipe.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (castClubGuttersnipe.object! castClubGuttersnipe.stack[0]!.objectId).name ==
  "Improvised Club"
#guard castClubGuttersnipe.log.any (fun s => mentions s "casts Improvised Club")
#guard castClubGuttersnipe.log.any (fun s => mentions s "cast trigger is put on the stack")

def resolvedClubGuttersnipe : Game :=
  passBoth (passBoth castClubGuttersnipe)

#guard resolvedClubGuttersnipe.stack.isEmpty
#guard (resolvedClubGuttersnipe.player ⟨1⟩).life == 14
#guard resolvedClubGuttersnipe.log.any (fun s => mentions s "Nissa is dealt 2 damage")
#guard resolvedClubGuttersnipe.log.any (fun s => mentions s "Nissa is dealt 4 damage")

-- Sacrificing Fireleaper to Club puts the dies trigger above the spell.
def clubSacrificesFireleaper : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  let g := withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Goblin Fireleaper").id)

#guard clubSacrificesFireleaper.pending == .chooseTargets ⟨0⟩
#guard clubSacrificesFireleaper.stack.size == 2
#guard (clubSacrificesFireleaper.object! clubSacrificesFireleaper.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature
#guard (clubSacrificesFireleaper.object! clubSacrificesFireleaper.stack[0]!.objectId).name ==
  "Improvised Club"
#guard clubSacrificesFireleaper.log.any (fun s => mentions s "sacrifices Goblin Fireleaper")
#guard clubSacrificesFireleaper.log.any (fun s => mentions s "dies trigger is put on the stack")
#guard clubSacrificesFireleaper.log.any (fun s => mentions s "casts Improvised Club")

/- Guardian of the Halls: trample and {5}{G}{G} for three +1/+1 counters. -/

def guardianAbility : ActivatedAbility :=
  guardianOfTheHalls.activatedAbilities[0]!

#guard guardianAbility.effect == Effect.putPlusOnePlusOneOnSource 3
#guard guardianAbility.cost.mana == ManaCost.ofGenericAndColors 5 [.green, .green]
#guard !guardianAbility.effect.requiresTarget
#guard guardianOfTheHalls.keywords.trample

/-- Guardian in play with {5}{G}{G} in the pool; a land drop is already used. -/
def guardianReady : Game :=
  let g := addPermanent afterDraw guardianOfTheHalls ⟨0⟩ ⟨0⟩
  withGreenMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 7

def guardianSource (g : Game) : GameObject :=
  namedPermanent g "Guardian of the Halls"

#guard guardianReady.canActivate ⟨0⟩ (guardianSource guardianReady) guardianAbility
#guard !(guardianReady.canActivate ⟨1⟩ (guardianSource guardianReady) guardianAbility)
#guard (guardianReady.player ⟨0⟩).manaPool.canPay guardianAbility.cost.mana
#guard guardianReady.power (guardianSource guardianReady) == 2
#guard guardianReady.toughness (guardianSource guardianReady) == 2
#guard guardianReady.hasTrample (guardianSource guardianReady)
#guard (guardianSource guardianReady).status.plusOnePlusOne == 0

-- Six green cannot pay {5}{G}{G}.
#guard
  let g := addPermanent afterDraw guardianOfTheHalls ⟨0⟩ ⟨0⟩
  let g := withGreenMana
    (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 6
  !(g.player ⟨0⟩).manaPool.canPay guardianAbility.cost.mana

-- The heuristic activates Guardian when {5}{G}{G} is available.
#guard
  match Agent.choose guardianReady ⟨0⟩ with
  | some (.activate id 0) => id == (guardianSource guardianReady).id
  | _ => false

def proposedGuardian : Game :=
  mustApply guardianReady ⟨0⟩ (.activate (guardianSource guardianReady).id 0)

#guard proposedGuardian.pending == .activateManaAbilities ⟨0⟩
#guard proposedGuardian.proposedSpell.isSome
#guard proposedGuardian.stack.size == 1
#guard (proposedGuardian.object! proposedGuardian.stack.back!.objectId).abilityEffect ==
  some (Effect.putPlusOnePlusOneOnSource 3)
#guard (namedPermanent proposedGuardian "Guardian of the Halls").isOnBattlefield
#guard proposedGuardian.log.any (fun s => mentions s "begins activating Guardian of the Halls")

-- Opponent cannot pay Chandra's activation.
#guard
  match proposedGuardian.apply ⟨1⟩ .pay with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

def paidGuardian : Game :=
  mustApply proposedGuardian ⟨0⟩ .pay

#guard paidGuardian.hasPriority ⟨0⟩
#guard paidGuardian.stack.size == 1
#guard paidGuardian.log.any (fun s => mentions s "activates Guardian of the Halls")
#guard (namedPermanent paidGuardian "Guardian of the Halls").status.plusOnePlusOne == 0

def guardianResolved : Game := passBoth paidGuardian

#guard guardianResolved.stack.isEmpty
#guard (namedPermanent guardianResolved "Guardian of the Halls").status.plusOnePlusOne == 3
#guard guardianResolved.power (namedPermanent guardianResolved "Guardian of the Halls") == 5
#guard guardianResolved.toughness (namedPermanent guardianResolved "Guardian of the Halls") == 5
#guard guardianResolved.hasTrample
  (namedPermanent guardianResolved "Guardian of the Halls")
#guard guardianResolved.log.any (fun s =>
  mentions s "Guardian of the Halls gets 3 +1/+1 counters")

/-- A second activation stacks. -/
def guardianResolvedTwice : Game :=
  let g := withGreenMana guardianResolved ⟨0⟩ 7
  let g := mustApply g ⟨0⟩ (.activate (guardianSource g).id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard guardianResolvedTwice.power
  (namedPermanent guardianResolvedTwice "Guardian of the Halls") == 8
#guard guardianResolvedTwice.toughness
  (namedPermanent guardianResolvedTwice "Guardian of the Halls") == 8
#guard (namedPermanent guardianResolvedTwice "Guardian of the Halls").status.plusOnePlusOne == 6

/-- Counters do not wear off in cleanup (CR 122.1 / 514.3). -/
def afterGuardianCleanup : Game :=
  passBoth (skipTo guardianResolved .end 80)

#guard afterGuardianCleanup.power
  (namedPermanent afterGuardianCleanup "Guardian of the Halls") == 5
#guard afterGuardianCleanup.toughness
  (namedPermanent afterGuardianCleanup "Guardian of the Halls") == 5
#guard (namedPermanent afterGuardianCleanup "Guardian of the Halls").status.plusOnePlusOne == 3

/-- If the source leaves before the ability resolves, the counters are not placed. -/
def guardianSourceGone : Game :=
  let id := (namedPermanent paidGuardian "Guardian of the Halls").id
  let (g, _) := paidGuardian.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard guardianSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard !(guardianSourceGone.battlefield.any (fun o => o.name == "Guardian of the Halls"))

-- Instant-speed: Guardian can activate during the end step.
def guardianAtEndStep : Game := skipTo guardianReady .end 80

#guard guardianAtEndStep.step == .end
#guard guardianAtEndStep.canActivate ⟨0⟩ (guardianSource guardianAtEndStep)
  guardianAbility

/-- Two damage is lethal to the 2/2, but not after three +1/+1 counters. -/
def guardianDiesFromTwoDamage : Game :=
  let o := namedPermanent guardianReady "Guardian of the Halls"
  let g := guardianReady.setObject { o with status := { o.status with damage := 2 } }
  g.receivePriority ⟨0⟩

#guard !(guardianDiesFromTwoDamage.battlefield.any (fun o =>
  o.name == "Guardian of the Halls"))
#guard guardianDiesFromTwoDamage.log.any (fun s =>
  mentions s "Guardian of the Halls dies from lethal damage")

def guardianSurvivesTwoDamage : Game :=
  let o := namedPermanent guardianResolved "Guardian of the Halls"
  let g := guardianResolved.setObject { o with status := { o.status with
    plusOnePlusOne := o.status.plusOnePlusOne, damage := 2 } }
  g.receivePriority ⟨0⟩

#guard guardianSurvivesTwoDamage.battlefield.any (fun o =>
  o.name == "Guardian of the Halls")
#guard (namedPermanent guardianSurvivesTwoDamage "Guardian of the Halls").status.damage == 2
#guard guardianSurvivesTwoDamage.power
  (namedPermanent guardianSurvivesTwoDamage "Guardian of the Halls") == 5

/-- Printed trample assigns leftover combat damage (5/5 vs 2/2 Bears). -/
def afterGuardianTrampleCombat : Game :=
  let g := addPermanent guardianResolved grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Guardian of the Halls").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Guardian of the Halls").id)])
  passBoth g

#guard afterGuardianTrampleCombat.log.any (fun s =>
  mentions s "Guardian of the Halls deals 2 combat damage to Grizzly Bears")
#guard afterGuardianTrampleCombat.log.any (fun s =>
  mentions s "Guardian of the Halls tramples for 3 to Nissa")
#guard afterGuardianTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears dies from lethal damage")
#guard (afterGuardianTrampleCombat.player ⟨1⟩).life == 17
#guard !(afterGuardianTrampleCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))

end Mtg.Engine.Tests
