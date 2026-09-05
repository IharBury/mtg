import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Activated abilities, exile play, granted trample, and becomes-blocked triggers.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Two untapped Mountains and a Wayfarer's Bauble; a land has already been
played this turn so the agent will activate rather than play another land. -/
def baubleReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := addPermanent g wayfarersBauble ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def baubleSource (g : Game) : GameObject :=
  namedPermanent g "Wayfarer's Bauble"

#guard wayfarersBauble.activatedAbilities.size == 1
#guard wayfarersBauble.manaAbilities.isEmpty
#guard baubleReady.hasPriority ⟨0⟩
#guard baubleReady.canActivate ⟨0⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!)
#guard !(baubleReady.canActivate ⟨1⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!))

-- The heuristic activates the bauble when {2} is available.
#guard
  match Agent.choose baubleReady ⟨0⟩ with
  | some (.activate id 0) => id == (baubleSource baubleReady).id
  | _ => false

def proposedBauble : Game :=
  mustApply baubleReady ⟨0⟩ (.activate (baubleSource baubleReady).id 0)

#guard proposedBauble.pending == .activateManaAbilities ⟨0⟩
#guard proposedBauble.proposedSpell.isSome
#guard
  match proposedBauble.proposedSpell with
  | some prop => prop.kind == .activatedAbility
  | none => false
#guard proposedBauble.stack.size == 1
#guard (proposedBauble.object! proposedBauble.stack.back!.objectId).sourceId ==
  some (baubleSource proposedBauble).id
#guard (namedPermanent proposedBauble "Wayfarer's Bauble").isOnBattlefield
#guard proposedBauble.log.any (fun s => mentions s "begins activating Wayfarer's Bauble")
#guard proposedBauble.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Opponent cannot activate Chandra's bauble.
#guard
  match baubleReady.activateAbility ⟨1⟩ (baubleSource baubleReady).id 0 with
  | .error _ => true
  | .ok _ => false

-- A land has no non-mana activated ability.
#guard
  match (baubleReady.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match baubleReady.activateAbility ⟨0⟩ land.id 0 with
    | .error msg => mentions msg "has no activated ability"
    | .ok _ => false

def tapNextMana (g : Game) (p : PlayerId) : Game :=
  match (g.manaSources p)[0]? with
  | none => panic! "expected a mana source"
  | some (src, types) =>
    match types[0]? with
    | none => panic! "expected a mana type"
    | some t => mustApply g p (.tapForMana src.id t)

/-- Paying without enough mana reverses the activation (CR 602.2 / 733.1). -/
def reversedBauble : Game :=
  mustApply proposedBauble ⟨0⟩ .pay

#guard reversedBauble.pending == .none
#guard reversedBauble.proposedSpell.isNone
#guard reversedBauble.stack.isEmpty
#guard reversedBauble.hasPriority ⟨0⟩
#guard (namedPermanent reversedBauble "Wayfarer's Bauble").isOnBattlefield
#guard reversedBauble.log.any (fun s => mentions s "the activation is reversed")

def tappedOnceForBauble : Game := tapNextMana proposedBauble ⟨0⟩
def tappedTwiceForBauble : Game := tapNextMana tappedOnceForBauble ⟨0⟩

#guard (tappedTwiceForBauble.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2)
#guard tappedTwiceForBauble.pending == .activateManaAbilities ⟨0⟩

def paidBauble : Game :=
  mustApply tappedTwiceForBauble ⟨0⟩ .pay

#guard paidBauble.pending == .none
#guard paidBauble.proposedSpell.isNone
#guard paidBauble.hasPriority ⟨0⟩
#guard paidBauble.stack.size == 1
#guard (paidBauble.player ⟨0⟩).manaPool.isEmpty
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  (paidBauble.object! id).name == "Wayfarer's Bauble")
#guard !(paidBauble.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard paidBauble.log.any (fun s => mentions s "sacrifices Wayfarer's Bauble")
#guard paidBauble.log.any (fun s => mentions s "activates Wayfarer's Bauble")

-- The agent pays once the pool covers {2}.
#guard
  match Agent.choose tappedTwiceForBauble ⟨0⟩ with
  | some .pay => true
  | _ => false

def resolvedBauble : Game := passBoth paidBauble

#guard resolvedBauble.stack.isEmpty
#guard (resolvedBauble.battlefield.filter (fun o => o.name == "Mountain")).size == 3
#guard (resolvedBauble.battlefield.filter (fun o =>
  o.name == "Mountain" && o.status.tapped)).size == 3
#guard resolvedBauble.log.any (fun s =>
  mentions s "puts Mountain onto the battlefield tapped")
#guard resolvedBauble.log.any (fun s => mentions s "shuffles their library")

-- Lands put onto the battlefield this way are not a land drop (CR 305.3).
#guard (resolvedBauble.player ⟨0⟩).landsPlayedThisTurn == 1

/-- Snowslope Hunter plus fodder and a known library top, in the precombat main. -/
def hunterReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunterCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g mountain
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def hunterSource (g : Game) : GameObject :=
  namedPermanent g "Snowslope Hunter"

def hunterFodder (g : Game) : GameObject :=
  namedPermanent g "Raging Goblin"

def hunterAbility : ActivatedAbility :=
  snowslopeHunterCard.activatedAbilities[0]!

#guard snowslopeHunterCard.activatedAbilities.size == 1
#guard hunterAbility.cost.sacrificeAnotherCreatureOrArtifact
#guard hunterAbility.effect == Effect.exileTopPlayUntilEndOfNextTurn
#guard hunterAbility.onlyDuringYourTurn
#guard hunterAbility.onceEachTurn
#guard !hunterAbility.onlyAsSorcery
#guard hunterReady.canActivate ⟨0⟩ (hunterSource hunterReady) hunterAbility
#guard !(hunterReady.canActivate ⟨1⟩ (hunterSource hunterReady) hunterAbility)
#guard (hunterReady.sacrificeCreatureOrArtifactChoices ⟨0⟩
  (hunterSource hunterReady).id).any (fun o => o.name == "Raging Goblin")

-- The heuristic begins activating the hunter when another creature is available.
#guard
  match Agent.choose hunterReady ⟨0⟩ with
  | some (.activate id 0) => id == (hunterSource hunterReady).id
  | _ => false

def proposedHunter : Game :=
  mustApply hunterReady ⟨0⟩ (.activate (hunterSource hunterReady).id 0)

#guard proposedHunter.pending == .activateManaAbilities ⟨0⟩
#guard proposedHunter.proposedSpell.isSome
#guard proposedHunter.stack.size == 1
#guard (namedPermanent proposedHunter "Raging Goblin").isOnBattlefield
#guard proposedHunter.log.any (fun s => mentions s "begins activating Snowslope Hunter")
#guard proposedHunter.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Sacrifice is not chosen at `activate`; it comes after `pay`.
#guard
  match proposedHunter.apply ⟨0⟩ (.sacrifice (hunterFodder proposedHunter).id) with
  | .error msg => mentions msg "Not time to sacrifice"
  | .ok _ => false

-- The heuristic pays the empty mana cost next.
#guard
  match Agent.choose proposedHunter ⟨0⟩ with
  | some .pay => true
  | _ => false

def paidHunter : Game :=
  mustApply proposedHunter ⟨0⟩ .pay

#guard
  match paidHunter.pending with
  | .sacrificePermanent p sid =>
    p == ⟨0⟩ && sid == (hunterSource paidHunter).id
  | _ => false
#guard paidHunter.proposedSpell.isSome
#guard (namedPermanent paidHunter "Raging Goblin").isOnBattlefield
#guard paidHunter.log.any (fun s =>
  mentions s "must sacrifice another creature or artifact")

-- Cannot sacrifice the hunter itself, a land, or skip the choice.
#guard
  match paidHunter.apply ⟨0⟩ (.sacrifice (hunterSource paidHunter).id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

#guard
  match (paidHunter.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match paidHunter.apply ⟨0⟩ (.sacrifice land.id) with
    | .error msg => mentions msg "Can't sacrifice"
    | .ok _ => false

#guard
  match Agent.choose paidHunter ⟨0⟩ with
  | some (.sacrifice id) => id == (hunterFodder paidHunter).id
  | _ => false

def activatedHunter : Game :=
  mustApply paidHunter ⟨0⟩ (.sacrifice (hunterFodder paidHunter).id)

#guard activatedHunter.pending == .none
#guard activatedHunter.proposedSpell.isNone
#guard activatedHunter.hasPriority ⟨0⟩
#guard activatedHunter.stack.size == 1
#guard (activatedHunter.object! activatedHunter.stack.back!.objectId).sourceId ==
  some (hunterSource activatedHunter).id
#guard (namedPermanent activatedHunter "Snowslope Hunter").isOnBattlefield
#guard !(activatedHunter.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard (activatedHunter.player ⟨0⟩).graveyard.any (fun id =>
  (activatedHunter.object! id).name == "Raging Goblin")
#guard (namedPermanent activatedHunter "Snowslope Hunter").status.activationsThisTurn == 1
#guard activatedHunter.log.any (fun s => mentions s "sacrifices Raging Goblin")
#guard activatedHunter.log.any (fun s => mentions s "activates Snowslope Hunter")

/-- Finish activating Snowslope Hunter by paying, then sacrificing `sacName`. -/
def completeHunterActivation (g : Game) (sacName : String) : Game :=
  let g := mustApply g ⟨0⟩ (.activate (hunterSource g).id 0)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g sacName).id)

-- Only once each turn: a second fodder still cannot be spent this turn.
def hunterActivatedOnce : Game :=
  completeHunterActivation hunterReady "Raging Goblin"

#guard
  match hunterActivatedOnce.activateAbility ⟨0⟩ (hunterSource hunterActivatedOnce).id 0 with
  | .error msg => mentions msg "only once each turn"
  | .ok _ => false
#guard !(hunterActivatedOnce.canActivate ⟨0⟩ (hunterSource hunterActivatedOnce) hunterAbility)

def resolvedHunter : Game := passBoth activatedHunter

#guard resolvedHunter.stack.isEmpty
#guard resolvedHunter.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt")
#guard resolvedHunter.log.any (fun s =>
  mentions s "exiles Lightning Bolt and may play it until the end of their next turn")

def exiledBolt (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Lightning Bolt") with
  | some o => o
  | none => panic! "expected Lightning Bolt in exile"

#guard resolvedHunter.mayPlayFromExile ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.mayPlayFromExile ⟨1⟩ (exiledBolt resolvedHunter))
#guard resolvedHunter.canCast ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.canCast ⟨1⟩ (exiledBolt resolvedHunter))

-- Opponent cannot play the exiled card.
#guard
  match resolvedHunter.castSpell ⟨1⟩ (exiledBolt resolvedHunter).id with
  | .error _ => true
  | .ok _ => false

-- Cast the exiled Lightning Bolt the same turn (CR 701.14).
def proposedExiledBolt : Game :=
  proposeTargeted resolvedHunter ⟨0⟩
    (exiledBolt resolvedHunter).id (Target.player ⟨1⟩)

#guard proposedExiledBolt.pending == .activateManaAbilities ⟨0⟩
#guard !(proposedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))
#guard proposedExiledBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")

def paidExiledBolt : Game :=
  mustApply (tapNextMana proposedExiledBolt ⟨0⟩) ⟨0⟩ .pay

def resolvedExiledBolt : Game := passBoth paidExiledBolt

#guard resolvedExiledBolt.stack.isEmpty
#guard (resolvedExiledBolt.player ⟨1⟩).life == 17
#guard resolvedExiledBolt.log.any (fun s => mentions s "is dealt 3 damage")
#guard !(resolvedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))

-- Playing an exiled land uses the land drop.
def hunterLandReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunterCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  addToLibraryTop g mountain ⟨0⟩

def resolvedHunterLand : Game :=
  passBoth (completeHunterActivation hunterLandReady "Raging Goblin")

def exiledMountain (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Mountain") with
  | some o => o
  | none => panic! "expected Mountain in exile"

#guard resolvedHunterLand.mayPlayFromExile ⟨0⟩ (exiledMountain resolvedHunterLand)
#guard resolvedHunterLand.canPlayLand ⟨0⟩

def playedExiledLand : Game :=
  mustApply resolvedHunterLand ⟨0⟩ (.playLand (exiledMountain resolvedHunterLand).id)

#guard (playedExiledLand.player ⟨0⟩).landsPlayedThisTurn == 1
#guard playedExiledLand.battlefield.any (fun o => o.name == "Mountain")
#guard playedExiledLand.log.any (fun s => mentions s "plays Mountain")
#guard !(playedExiledLand.objects.any (fun o => o.zone == .exile && o.name == "Mountain"))

-- Activate only during your turn: Chandra has priority on Nissa's turn.
def hunterOnNissaTurn : Game :=
  let g := skipTo hunterReady .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterOnNissaTurn.activePlayer == ⟨1⟩
#guard hunterOnNissaTurn.hasPriority ⟨0⟩
#guard
  match hunterOnNissaTurn.activateAbility ⟨0⟩ (hunterSource hunterOnNissaTurn).id 0 with
  | .error msg => mentions msg "only during your turn"
  | .ok _ => false

-- Instant-speed: the hunter can activate during the end step of your turn.
def hunterAtEndStep : Game := skipTo hunterReady .end 80

#guard hunterAtEndStep.step == .end
#guard hunterAtEndStep.canActivate ⟨0⟩ (hunterSource hunterAtEndStep) hunterAbility

-- Permission lasts through the next turn, then expires.
def hunterPermissionActive : Game :=
  let g := skipTo resolvedHunter .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterPermissionActive.activePlayer == ⟨1⟩
#guard hunterPermissionActive.mayPlayFromExile ⟨0⟩ (exiledBolt hunterPermissionActive)

def hunterOnNextTurn : Game :=
  let g := skipTo hunterPermissionActive .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterOnNextTurn.activePlayer == ⟨0⟩
#guard hunterOnNextTurn.mayPlayFromExile ⟨0⟩ (exiledBolt hunterOnNextTurn)
#guard hunterOnNextTurn.canActivate ⟨0⟩ (hunterSource hunterOnNextTurn) hunterAbility

def hunterActivatedNextTurn : Game :=
  completeHunterActivation hunterOnNextTurn "Gray Ogre"

#guard hunterActivatedNextTurn.log.any (fun s => mentions s "activates Snowslope Hunter")
#guard hunterActivatedNextTurn.log.any (fun s => mentions s "sacrifices Gray Ogre")

def hunterPermissionExpired : Game :=
  let g := skipTo hunterOnNextTurn .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterPermissionExpired.activePlayer == ⟨1⟩
#guard hunterPermissionExpired.hasPriority ⟨0⟩
#guard hunterPermissionExpired.log.any (fun s =>
  mentions s "can no longer be played from exile")
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o => !hunterPermissionExpired.mayPlayFromExile ⟨0⟩ o
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o =>
    match hunterPermissionExpired.castSpell ⟨0⟩ o.id with
    | .error msg => mentions msg "may not play that card from exile"
    | .ok _ => false

-- Empty library: the ability still resolves.
def hunterEmptyLibrary : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunterCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })

def resolvedHunterEmpty : Game :=
  passBoth (completeHunterActivation hunterEmptyLibrary "Raging Goblin")

#guard resolvedHunterEmpty.stack.isEmpty
#guard resolvedHunterEmpty.log.any (fun s => mentions s "no cards in their library to exile")
#guard !(resolvedHunterEmpty.objects.any (fun o => o.zone == .exile))

/-- Orcish Siegemaster grants trample to other Orcs and Goblins you control. -/
def siegeAndGoblin : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨0⟩ ⟨0⟩

def siegeAndOgre : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

def siegeAndOppGoblin : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨1⟩ ⟨1⟩

#guard siegeAndGoblin.hasTrample (namedPermanent siegeAndGoblin "Orcish Siegemaster")
#guard siegeAndGoblin.hasTrample (namedPermanent siegeAndGoblin "Raging Goblin")
#guard (siegeAndGoblin.effectiveKeywords (namedPermanent siegeAndGoblin "Raging Goblin")).trample
#guard (siegeAndGoblin.effectiveKeywords (namedPermanent siegeAndGoblin "Raging Goblin")).haste
#guard !withGoblin.hasTrample (lastPermanent withGoblin)
#guard !siegeAndOgre.hasTrample (namedPermanent siegeAndOgre "Gray Ogre")
#guard !siegeAndOppGoblin.hasTrample (namedPermanent siegeAndOppGoblin "Raging Goblin")

/-- Snowslope Hunter (a Goblin) trampling over Llanowar Elves. -/
def siegeHunterVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g snowslopeHunterCard ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def hunterGrantedTrampleAttack : Game :=
  let g := passBoth (skipTo siegeHunterVsElves .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Snowslope Hunter").id])

def hunterGrantedTrampleBlocked : Game :=
  let g := passBoth hunterGrantedTrampleAttack
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Snowslope Hunter").id)])

def afterGrantedTrample : Game := passBoth hunterGrantedTrampleBlocked

#guard afterGrantedTrample.log.any (fun s =>
  mentions s "Snowslope Hunter deals 1 combat damage to Llanowar Elves")
#guard afterGrantedTrample.log.any (fun s =>
  mentions s "Snowslope Hunter tramples for 1 to Nissa")
#guard (afterGrantedTrample.player ⟨1⟩).life == 19

/-- Without the Siegemaster, the same Goblin assigns all damage to the blocker. -/
def hunterOnlyVsElves : Game :=
  addPermanent (addPermanent started snowslopeHunterCard ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def afterHunterNoTrample : Game :=
  let g := passBoth (skipTo hunterOnlyVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Snowslope Hunter").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Snowslope Hunter").id)])
  passBoth g

#guard afterHunterNoTrample.log.any (fun s =>
  mentions s "Snowslope Hunter deals 2 combat damage to Llanowar Elves")
#guard !afterHunterNoTrample.log.any (fun s => mentions s "tramples")
#guard (afterHunterNoTrample.player ⟨1⟩).life == 20

/-- A non-Orc, non-Goblin does not receive the grant. -/
def siegeOgreVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def afterOgreNoTrample : Game :=
  let g := passBoth (skipTo siegeOgreVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard afterOgreNoTrample.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Llanowar Elves")
#guard !afterOgreNoTrample.log.any (fun s => mentions s "tramples")

/-- Attack trigger: +X/+0 where X is the greatest power among creatures you control. -/
def siegeGiantVsBears : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def siegeAttackDeclared : Game :=
  let g := passBoth (skipTo siegeGiantVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])

#guard siegeAttackDeclared.stack.size == 1
#guard (siegeAttackDeclared.object! siegeAttackDeclared.stack.back!.objectId).name ==
  "Orcish Siegemaster's ability"
#guard (siegeAttackDeclared.object! siegeAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent siegeAttackDeclared "Orcish Siegemaster").id
#guard siegeAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard (namedPermanent siegeAttackDeclared "Orcish Siegemaster").power == 0
#guard siegeAttackDeclared.step == .declareAttackers
#guard siegeAttackDeclared.hasPriority ⟨0⟩

def siegePumpResolved : Game := passBoth siegeAttackDeclared

#guard siegePumpResolved.stack.isEmpty
#guard (namedPermanent siegePumpResolved "Orcish Siegemaster").power == 3
#guard siegePumpResolved.log.any (fun s => mentions s "gets +3/+0 until end of turn")
#guard siegePumpResolved.step == .declareAttackers

def siegeReadyToBlock : Game := passBoth siegePumpResolved

#guard siegeReadyToBlock.pending == .declareBlockers

def siegeBlocked : Game :=
  let g := siegeReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Orcish Siegemaster").id)])

def afterSiegeCombat : Game := passBoth siegeBlocked

#guard afterSiegeCombat.log.any (fun s =>
  mentions s "Orcish Siegemaster deals 2 combat damage to Grizzly Bears")
#guard afterSiegeCombat.log.any (fun s =>
  mentions s "Orcish Siegemaster tramples for 1 to Nissa")
#guard (afterSiegeCombat.player ⟨1⟩).life == 19

/-- Alone, X is the Siegemaster's own power (0). -/
def siegeAloneResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegeAloneResolved "Orcish Siegemaster").power == 0
#guard siegeAloneResolved.log.any (fun s => mentions s "gets +0/+0 until end of turn")

/-- Opponent creatures do not count toward X. -/
def siegeVsWurmResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g crawWurm ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegeVsWurmResolved "Orcish Siegemaster").power == 0

/-- X uses current power, including until-end-of-turn pumps. -/
def siegePumpedGiantResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let g := g.applyEffect ⟨0⟩ (Effect.pump 2 0)
    #[Target.permanent (namedPermanent g "Hill Giant").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegePumpedGiantResolved "Hill Giant").power == 5
#guard (namedPermanent siegePumpedGiantResolved "Orcish Siegemaster").power == 5
#guard siegePumpedGiantResolved.log.any (fun s => mentions s "gets +5/+0 until end of turn")

/-- If the source leaves before the trigger resolves, the pump does not happen. -/
def siegeSourceGone : Game :=
  let g := siegeAttackDeclared
  let id := (namedPermanent g "Orcish Siegemaster").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard siegeSourceGone.stack.isEmpty
#guard !(siegeSourceGone.battlefield.any (fun o => o.name == "Orcish Siegemaster"))
#guard siegeSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard (namedPermanent siegeSourceGone "Hill Giant").status.pumpPower == 0

/-- The +X/+0 wears off in cleanup. -/
def afterSiegeCleanup : Game := passBoth (skipTo siegePumpResolved .end 80)

#guard (namedPermanent afterSiegeCleanup "Orcish Siegemaster").power == 0
#guard (namedPermanent afterSiegeCleanup "Orcish Siegemaster").status.pumpPower == 0

/-- Printed trample still assigns leftover damage (Beorn 5/5 vs Grizzly Bears 2/2). -/
def afterBeornTrample : Game :=
  let g := addPermanent (addPermanent started beornReluctantHost ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Beorn, Reluctant Host").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Beorn, Reluctant Host").id)])
  passBoth g

#guard afterBeornTrample.log.any (fun s =>
  mentions s "Beorn, Reluctant Host deals 2 combat damage to Grizzly Bears")
#guard afterBeornTrample.log.any (fun s =>
  mentions s "Beorn, Reluctant Host tramples for 3 to Nissa")
#guard (afterBeornTrample.player ⟨1⟩).life == 17

/-- Battle-Scarred Goblin vs Grizzly Bears: becomes-blocked trigger, then combat. -/
def goblinVsBears : Game :=
  addPermanent (addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def goblinDeclaredAttacker : Game :=
  let g := passBoth (skipTo goblinVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])

def goblinReadyToBlock : Game := passBoth goblinDeclaredAttacker

def goblinBlockedByBears : Game :=
  let g := goblinReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])

#guard goblinBlockedByBears.stack.size == 1
#guard (goblinBlockedByBears.object! goblinBlockedByBears.stack.back!.objectId).name ==
  "Battle-Scarred Goblin's ability"
#guard (goblinBlockedByBears.object! goblinBlockedByBears.stack.back!.objectId).sourceId ==
  some (namedPermanent goblinBlockedByBears "Battle-Scarred Goblin").id
#guard goblinBlockedByBears.log.any (fun s => mentions s "becomes-blocked trigger is put on the stack")
#guard (namedPermanent goblinBlockedByBears "Battle-Scarred Goblin").status.blocked
#guard goblinBlockedByBears.step == .declareBlockers
#guard goblinBlockedByBears.hasPriority ⟨0⟩
#guard (namedPermanent goblinBlockedByBears "Grizzly Bears").status.damage == 0

def goblinTriggerResolved : Game := passBoth goblinBlockedByBears

#guard goblinTriggerResolved.stack.isEmpty
#guard (namedPermanent goblinTriggerResolved "Grizzly Bears").status.damage == 1
#guard goblinTriggerResolved.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Grizzly Bears")
#guard goblinTriggerResolved.step == .declareBlockers
#guard goblinTriggerResolved.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (goblinTriggerResolved.player ⟨1⟩).life == 20

def afterGoblinBearsCombat : Game := passBoth goblinTriggerResolved

#guard afterGoblinBearsCombat.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 2 combat damage to Grizzly Bears")
#guard afterGoblinBearsCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Battle-Scarred Goblin")
#guard (afterGoblinBearsCombat.player ⟨1⟩).life == 20
#guard !(afterGoblinBearsCombat.battlefield.any (fun o => o.name == "Battle-Scarred Goblin"))
#guard !(afterGoblinBearsCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- A 1/1 blocker dies to the trigger; the Goblin stays blocked and assigns no
combat damage (CR 509.1h / 510.1c). -/
def goblinVsElves : Game :=
  addPermanent (addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def goblinBlockedByElves : Game :=
  let g := passBoth (skipTo goblinVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])

def goblinElvesAfterTrigger : Game := passBoth goblinBlockedByElves

#guard goblinElvesAfterTrigger.stack.isEmpty
#guard goblinElvesAfterTrigger.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")
#guard goblinElvesAfterTrigger.log.any (fun s => mentions s "Llanowar Elves dies from lethal damage")
#guard !(goblinElvesAfterTrigger.battlefield.any (fun o => o.name == "Llanowar Elves"))
#guard goblinElvesAfterTrigger.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨1⟩)
#guard (namedPermanent goblinElvesAfterTrigger "Battle-Scarred Goblin").status.blocked
#guard goblinElvesAfterTrigger.step == .declareBlockers
#guard (goblinElvesAfterTrigger.player ⟨1⟩).life == 20

def afterGoblinElvesCombat : Game := passBoth goblinElvesAfterTrigger

#guard afterGoblinElvesCombat.log.any (fun s =>
  mentions s "blocked with no remaining blockers and assigns no combat damage")
#guard !afterGoblinElvesCombat.log.any (fun s => mentions s "combat damage to Nissa")
#guard (afterGoblinElvesCombat.player ⟨1⟩).life == 20
#guard afterGoblinElvesCombat.battlefield.any (fun o => o.name == "Battle-Scarred Goblin")
#guard (namedPermanent afterGoblinElvesCombat "Battle-Scarred Goblin").status.damage == 0

/-- Unblocked: the trigger does not fire, and combat damage hits the player. -/
def afterGoblinUnblocked : Game :=
  passBoth (mustApply goblinReadyToBlock ⟨1⟩ (.declareBlockers #[]))

#guard afterGoblinUnblocked.stack.isEmpty
#guard !afterGoblinUnblocked.log.any (fun s => mentions s "becomes-blocked trigger")
#guard (afterGoblinUnblocked.player ⟨1⟩).life == 18
#guard afterGoblinUnblocked.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 2 combat damage to Nissa")

/-- CR 509.5c: two blockers still produce one trigger; each takes 1 damage. -/
def goblinVsTwoElves : Game :=
  let g := addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def goblinBlockedByTwoElves : Game :=
  let g := passBoth (skipTo goblinVsTwoElves .beginningOfCombat 80)
  let goblin := namedPermanent g "Battle-Scarred Goblin"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let g := mustApply g ⟨0⟩ (.declareAttackers #[goblin.id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(elves[0]!.id, goblin.id), (elves[1]!.id, goblin.id)])

#guard goblinBlockedByTwoElves.stack.size == 1
#guard (goblinBlockedByTwoElves.battlefield.filter (fun o =>
  !o.status.blocking.isEmpty)).size == 2

def goblinTwoElvesAfterTrigger : Game := passBoth goblinBlockedByTwoElves

#guard (goblinTwoElvesAfterTrigger.log.filter (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")).size == 2
#guard (goblinTwoElvesAfterTrigger.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).isEmpty
#guard (goblinTwoElvesAfterTrigger.objects.filter (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨1⟩)).size == 2

/-- Two Goblins, one blocked: only the blocked one triggers. -/
def twoGoblinsOneBlocked : Game :=
  let g := addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let goblins := g.battlefield.filter (fun o => o.name == "Battle-Scarred Goblin")
  let g := mustApply g ⟨0⟩ (.declareAttackers (goblins.map (·.id)))
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    goblins[0]!.id)])

#guard twoGoblinsOneBlocked.stack.size == 1
#guard (twoGoblinsOneBlocked.battlefield.filter (fun o =>
  o.name == "Battle-Scarred Goblin" && o.status.blocked)).size == 1
#guard (twoGoblinsOneBlocked.battlefield.filter (fun o =>
  o.name == "Battle-Scarred Goblin" && o.status.attacking && !o.status.blocked)).size == 1

/-- If the source leaves before the trigger resolves, blockers are unharmed. -/
def goblinSourceGone : Game :=
  let g := goblinBlockedByBears
  let id := (namedPermanent g "Battle-Scarred Goblin").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard goblinSourceGone.stack.isEmpty
#guard goblinSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard (namedPermanent goblinSourceGone "Grizzly Bears").status.damage == 0

/-- Granted trample plus a killed 1/1 blocker: leftover damage goes to the player
(CR 702.19d). -/
def siegeGoblinVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g battleScarredGoblin ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def afterSiegeGoblinElves : Game :=
  let g := passBoth (skipTo siegeGoblinVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])
  let g := passBoth g
  passBoth g

#guard afterSiegeGoblinElves.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")
#guard afterSiegeGoblinElves.log.any (fun s => mentions s "Llanowar Elves dies from lethal damage")
#guard afterSiegeGoblinElves.log.any (fun s =>
  mentions s "Battle-Scarred Goblin tramples for 2 to Nissa")
#guard (afterSiegeGoblinElves.player ⟨1⟩).life == 18
#guard afterSiegeGoblinElves.battlefield.any (fun o => o.name == "Battle-Scarred Goblin")

end Mtg.Engine.Tests
