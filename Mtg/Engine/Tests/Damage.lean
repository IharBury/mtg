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
# Divided damage, activated pumps, and dies triggers.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Gandalf, Spark Starter: reach and divided-damage enters trigger (CR 601.2d). -/

/-- A flying attacker can be blocked by Gandalf (reach) but not by a Gray Ogre. -/
def flyerVsGandalf : Game :=
  let g := addPermanent started smaugTheGreatCalamity ⟨0⟩ ⟨0⟩
  let g := addPermanent g gandalfSparkStarter ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let smaug := namedPermanent g "Smaug, the Great Calamity"
  g.setObject { smaug with status := { smaug.status with attacking := true } }

#guard flyerVsGandalf.canBlock
  (namedPermanent flyerVsGandalf "Gandalf, Spark Starter")
  (namedPermanent flyerVsGandalf "Smaug, the Great Calamity")
#guard !flyerVsGandalf.canBlock
  (namedPermanent flyerVsGandalf "Gray Ogre")
  (namedPermanent flyerVsGandalf "Smaug, the Great Calamity")

/-- Gandalf in hand with enough mana to cast him. -/
def gandalfSetup : Game :=
  withRedMana (addToHand afterDraw gandalfSparkStarter ⟨0⟩) ⟨0⟩ 6

#guard gandalfSetup.canCast ⟨0⟩ (handCardNamed gandalfSetup ⟨0⟩ "Gandalf, Spark Starter")
#guard gandalfSetup.asSorcery? ⟨0⟩
#guard gandalfSparkStarter.hasSorcerySpeed

def proposedGandalf : Game :=
  mustApply gandalfSetup ⟨0⟩ (.cast (handCardNamed gandalfSetup ⟨0⟩ "Gandalf, Spark Starter").id)

#guard proposedGandalf.pending == .activateManaAbilities ⟨0⟩
#guard proposedGandalf.log.any (fun s => mentions s "begins casting Gandalf, Spark Starter")

def paidGandalf : Game := mustApply proposedGandalf ⟨0⟩ .pay

#guard paidGandalf.stack.size == 1
#guard paidGandalf.hasPriority ⟨0⟩
#guard paidGandalf.log.any (fun s => mentions s "casts Gandalf, Spark Starter")

/-- The creature enters; the divided-damage trigger waits for a division (CR 601.2d). -/
def gandalfEntered : Game := passBoth paidGandalf

#guard (namedPermanent gandalfEntered "Gandalf, Spark Starter").printed.power == some 4
#guard gandalfEntered.power (namedPermanent gandalfEntered "Gandalf, Spark Starter") == 4
#guard gandalfEntered.toughness (namedPermanent gandalfEntered "Gandalf, Spark Starter") == 3
#guard (namedPermanent gandalfEntered "Gandalf, Spark Starter").printed.keywords.reach
#guard gandalfEntered.stack.size == 1
#guard (gandalfEntered.object! gandalfEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterDealDividedDamage 3 3)
#guard (gandalfEntered.object! gandalfEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent gandalfEntered "Gandalf, Spark Starter").id
#guard gandalfEntered.stack.back!.targets.isEmpty
#guard gandalfEntered.stack.back!.dividedDamage.isEmpty
#guard gandalfEntered.pending == .chooseTargets ⟨0⟩
#guard gandalfEntered.actor == some ⟨0⟩
#guard !gandalfEntered.hasPriority ⟨0⟩
#guard gandalfEntered.log.any (fun s => mentions s "enters the battlefield")
#guard gandalfEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard gandalfEntered.log.any (fun s => mentions s "must divide 3 damage")
#guard gandalfEntered.announcingDividedDamage

-- The heuristic puts all 3 damage on the opponent.
#guard
  match Agent.choose gandalfEntered ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

-- A player is a legal target; hexproof does not apply to players.
#guard (gandalfEntered.legalProposedTargets ⟨0⟩
  (gandalfEntered.object! gandalfEntered.stack.back!.objectId)).contains
  (Target.player ⟨1⟩)

-- `target` without an amount assigns all remaining damage (CR 601.2d).
def gandalfTargetedOpponent : Game :=
  mustApply gandalfEntered ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard gandalfTargetedOpponent.pending == .none
#guard gandalfTargetedOpponent.hasPriority ⟨0⟩
#guard gandalfTargetedOpponent.stack.back!.targets == #[Target.player ⟨1⟩]
#guard gandalfTargetedOpponent.stack.back!.dividedDamage == #[3]
#guard gandalfTargetedOpponent.log.any (fun s =>
  mentions s "chooses Nissa to be dealt 3 damage (CR 601.2d)")

def gandalfResolvedOpponent : Game := passBoth gandalfTargetedOpponent

#guard gandalfResolvedOpponent.stack.isEmpty
#guard (gandalfResolvedOpponent.player ⟨1⟩).life == 17
#guard (gandalfResolvedOpponent.player ⟨0⟩).life == 20
#guard gandalfResolvedOpponent.log.any (fun s => mentions s "Nissa is dealt 3 damage")
#guard gandalfResolvedOpponent.battlefield.any (fun o => o.name == "Gandalf, Spark Starter")

-- Zero damage to a target is illegal.
#guard
  match gandalfEntered.apply ⟨0⟩ (.divideDamage #[(Target.player ⟨1⟩, 0)]) with
  | .error msg => mentions msg "at least 1 damage"
  | .ok _ => false

-- More than the remaining damage is illegal.
#guard
  match gandalfEntered.apply ⟨0⟩ (.divideDamage #[(Target.player ⟨1⟩, 4)]) with
  | .error msg => mentions msg "remains to divide"
  | .ok _ => false

-- `divideDamage` is not used for ordinary targeted spells.
#guard
  match proposedBolt.apply ⟨0⟩ (.divideDamage #[(Target.player ⟨1⟩, 3)]) with
  | .error msg => mentions msg "does not divide damage"
  | .ok _ => false

/-- An opposing 2/2 is in play so damage can be split. -/
def gandalfSplitSetup : Game :=
  addPermanent gandalfEntered grizzlyBears ⟨1⟩ ⟨1⟩

-- Multiple targets of one instance of the word “target” are chosen together
-- (CR 601.2c); leftover damage after that announcement is illegal.
#guard
  match gandalfSplitSetup.apply ⟨0⟩
      (.divideDamage #[(Target.permanent (namedPermanent gandalfSplitSetup "Grizzly Bears").id, 2)]) with
  | .error msg => mentions msg "Must assign all remaining damage"
  | .ok _ => false

-- Duplicate targets of one instance are illegal (CR 115.3).
#guard
  match gandalfSplitSetup.apply ⟨0⟩
      (.divideDamage #[(Target.player ⟨1⟩, 2), (Target.player ⟨1⟩, 1)]) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Leaving leftover damage when more targets could still be chosen is illegal;
-- every target of this instance must be announced together.
#guard
  match gandalfSplitSetup.apply ⟨0⟩
      (.divideDamage #[(Target.player ⟨0⟩, 1), (Target.player ⟨1⟩, 1)]) with
  | .error msg => mentions msg "Must assign all remaining damage"
  | .ok _ => false

def gandalfSplitAnnounced : Game :=
  mustApply gandalfSplitSetup ⟨0⟩
    (.divideDamage #[
      (Target.player ⟨1⟩, 2),
      (Target.permanent (namedPermanent gandalfSplitSetup "Grizzly Bears").id, 1)])

#guard gandalfSplitAnnounced.pending == .none
#guard gandalfSplitAnnounced.hasPriority ⟨0⟩
#guard gandalfSplitAnnounced.stack.back!.targets.size == 2
#guard gandalfSplitAnnounced.stack.back!.dividedDamage == #[2, 1]
#guard gandalfSplitAnnounced.log.any (fun s =>
  mentions s "chooses Nissa to be dealt 2 damage")
#guard gandalfSplitAnnounced.log.any (fun s =>
  mentions s "chooses Grizzly Bears to be dealt 1 damage")

def gandalfSplitResolved : Game := passBoth gandalfSplitAnnounced

#guard gandalfSplitResolved.stack.isEmpty
#guard (gandalfSplitResolved.player ⟨1⟩).life == 18
#guard (namedPermanent gandalfSplitResolved "Grizzly Bears").status.damage == 1
#guard gandalfSplitResolved.log.any (fun s => mentions s "Nissa is dealt 2 damage")
#guard gandalfSplitResolved.log.any (fun s => mentions s "Grizzly Bears is dealt 1 damage")

/-- Three targets, 1 damage each. -/
def gandalfThreeAnnounced : Game :=
  let g := addPermanent gandalfEntered grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  mustApply g ⟨0⟩
    (.divideDamage #[
      (Target.player ⟨1⟩, 1),
      (Target.permanent (namedPermanent g "Grizzly Bears").id, 1),
      (Target.permanent (namedPermanent g "Gray Ogre").id, 1)])

#guard gandalfThreeAnnounced.stack.back!.dividedDamage == #[1, 1, 1]
#guard gandalfThreeAnnounced.pending == .none

def gandalfThreeResolved : Game := passBoth gandalfThreeAnnounced

#guard (gandalfThreeResolved.player ⟨1⟩).life == 19
#guard (namedPermanent gandalfThreeResolved "Grizzly Bears").status.damage == 1
#guard (namedPermanent gandalfThreeResolved "Gray Ogre").status.damage == 1

-- A fourth target of the same instance is illegal (CR 601.2d).
#guard
  let g := addPermanent gandalfEntered grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩
      (.divideDamage #[
        (Target.player ⟨1⟩, 1),
        (Target.permanent (namedPermanent g "Grizzly Bears").id, 1),
        (Target.permanent (namedPermanent g "Raging Goblin").id, 1),
        (Target.permanent (namedPermanent g "Gray Ogre").id, 1)]) with
  | .error msg => mentions msg "Cannot choose more than 3 targets"
  | .ok _ => false

-- After every target of that instance is announced, a further announcement
-- is not a targeting step.
#guard
  match gandalfThreeAnnounced.apply ⟨0⟩
      (.divideDamage #[(Target.permanent (namedPermanent gandalfThreeAnnounced "Gray Ogre").id, 1)]) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false

/-- If a targeted creature leaves before resolution, that portion is skipped. -/
def gandalfTargetGone : Game :=
  let id := (namedPermanent gandalfSplitAnnounced "Grizzly Bears").id
  let (g, _) := gandalfSplitAnnounced.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard (gandalfTargetGone.player ⟨1⟩).life == 18
#guard gandalfTargetGone.log.any (fun s => mentions s "Nissa is dealt 2 damage")
#guard gandalfTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(gandalfTargetGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- The trigger still deals damage if Gandalf has left (CR 113.7a). -/
def gandalfLeftBeforeTrigger : Game :=
  let id := (namedPermanent gandalfTargetedOpponent "Gandalf, Spark Starter").id
  let (g, _) := gandalfTargetedOpponent.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (gandalfLeftBeforeTrigger.player ⟨1⟩).life == 17
#guard !(gandalfLeftBeforeTrigger.battlefield.any (fun o =>
  o.name == "Gandalf, Spark Starter"))
#guard (gandalfLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (gandalfLeftBeforeTrigger.object! id).name == "Gandalf, Spark Starter")

-- Hexproof makes an opposing creature an illegal target (CR 702.11b).
#guard
  let g := addPermanent gandalfEntered velvetwingButterfliesCard ⟨1⟩ ⟨1⟩
  let o := namedPermanent g "Velvetwing Butterflies"
  let g := g.setObject { o with
    status := { o.status with untilEotKeywords := Keyword.hexproof } }
  match g.apply ⟨0⟩
      (.divideDamage #[(Target.permanent (namedPermanent g "Velvetwing Butterflies").id, 3)]) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

/-- The agent casts Gandalf when that is the playable spell. -/
def agentGandalfOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g gandalfSparkStarter ⟨0⟩) ⟨0⟩ 6

#guard
  match Agent.choose agentGandalfOnly ⟨0⟩ with
  | some (.cast id) => (agentGandalfOnly.object! id).name == "Gandalf, Spark Starter"
  | _ => false

/- Goblin Fireleaper: {1}{R} pump and a dies trigger. -/

def fireleaperAbility : ActivatedAbility :=
  goblinFireleaper.activatedAbilities[0]!

#guard fireleaperAbility.effect == Effect.sourceGets 1 0
#guard fireleaperAbility.cost.mana == ManaCost.ofGenericAndColor 1 .red
#guard !fireleaperAbility.effect.requiresTarget
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]

/-- Fireleaper in play with {1}{R} in the pool; a land drop is already used. -/
def fireleaperReady : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 2

def fireleaperSource (g : Game) : GameObject :=
  namedPermanent g "Goblin Fireleaper"

#guard fireleaperReady.canActivate ⟨0⟩ (fireleaperSource fireleaperReady) fireleaperAbility
#guard !(fireleaperReady.canActivate ⟨1⟩ (fireleaperSource fireleaperReady) fireleaperAbility)
#guard (fireleaperReady.player ⟨0⟩).manaPool.canPay fireleaperAbility.cost.mana
#guard fireleaperReady.power (fireleaperSource fireleaperReady) == 1

-- The heuristic pumps Fireleaper when {1}{R} is available.
#guard
  match Agent.choose fireleaperReady ⟨0⟩ with
  | some (.activate id 0) => id == (fireleaperSource fireleaperReady).id
  | _ => false

def proposedFireleaper : Game :=
  mustApply fireleaperReady ⟨0⟩ (.activate (fireleaperSource fireleaperReady).id 0)

#guard proposedFireleaper.pending == .activateManaAbilities ⟨0⟩
#guard proposedFireleaper.proposedSpell.isSome
#guard proposedFireleaper.stack.size == 1
#guard (proposedFireleaper.object! proposedFireleaper.stack.back!.objectId).abilityEffect ==
  some (Effect.sourceGets 1 0)
#guard (namedPermanent proposedFireleaper "Goblin Fireleaper").isOnBattlefield
#guard proposedFireleaper.log.any (fun s => mentions s "begins activating Goblin Fireleaper")

-- Opponent cannot pay Chandra's activation.
#guard
  match proposedFireleaper.apply ⟨1⟩ .pay with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

def paidFireleaper : Game :=
  mustApply proposedFireleaper ⟨0⟩ .pay

#guard paidFireleaper.hasPriority ⟨0⟩
#guard paidFireleaper.stack.size == 1
#guard paidFireleaper.log.any (fun s => mentions s "activates Goblin Fireleaper")
#guard (namedPermanent paidFireleaper "Goblin Fireleaper").status.pumpPower == 0

def pumpedFireleaper : Game := passBoth paidFireleaper

#guard pumpedFireleaper.stack.isEmpty
#guard (namedPermanent pumpedFireleaper "Goblin Fireleaper").status.pumpPower == 1
#guard pumpedFireleaper.power (namedPermanent pumpedFireleaper "Goblin Fireleaper") == 2
#guard pumpedFireleaper.log.any (fun s => mentions s "Goblin Fireleaper gets +1/+0 until end of turn")

/-- A second activation stacks. -/
def fireleaperPumpedTwice : Game :=
  let g := withRedMana pumpedFireleaper ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.activate (fireleaperSource g).id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard fireleaperPumpedTwice.power (namedPermanent fireleaperPumpedTwice "Goblin Fireleaper") == 3
#guard (namedPermanent fireleaperPumpedTwice "Goblin Fireleaper").status.pumpPower == 2

/-- The +1/+0 wears off in cleanup. -/
def afterFireleaperCleanup : Game :=
  passBoth (skipTo pumpedFireleaper .end 80)

#guard afterFireleaperCleanup.power
  (namedPermanent afterFireleaperCleanup "Goblin Fireleaper") == 1
#guard (namedPermanent afterFireleaperCleanup "Goblin Fireleaper").status.pumpPower == 0

/-- If the source leaves before the pump resolves, the pump does not happen;
the dies trigger waits until after that ability resolves (CR 603.3). -/
def fireleaperPumpSourceGone : Game :=
  let id := (namedPermanent paidFireleaper "Goblin Fireleaper").id
  let (g, _) := paidFireleaper.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard fireleaperPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard fireleaperPumpSourceGone.pending == .chooseTargets ⟨0⟩
#guard fireleaperPumpSourceGone.stack.size == 1
#guard (fireleaperPumpSourceGone.object! fireleaperPumpSourceGone.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature

-- Instant-speed: Fireleaper can activate during the end step.
def fireleaperAtEndStep : Game := skipTo fireleaperReady .end 80

#guard fireleaperAtEndStep.step == .end
#guard fireleaperAtEndStep.canActivate ⟨0⟩ (fireleaperSource fireleaperAtEndStep)
  fireleaperAbility

/- Desolation Prowler: Pay 2 life for +2/+2, only once each turn. -/

def prowlerAbility : ActivatedAbility :=
  desolationProwlerCard.activatedAbilities[0]!

#guard prowlerAbility.effect == Effect.sourceGets 2 2
#guard prowlerAbility.cost.payLife == 2
#guard prowlerAbility.cost.mana == ManaCost.empty
#guard !prowlerAbility.cost.tap
#guard prowlerAbility.onceEachTurn
#guard !prowlerAbility.effect.requiresTarget

/-- Prowler in play; a land drop is already used so the heuristic can activate. -/
def prowlerReady : Game :=
  let g := addPermanent afterDraw desolationProwlerCard ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def prowlerSource (g : Game) : GameObject :=
  namedPermanent g "Desolation Prowler"

#guard prowlerReady.canActivate ⟨0⟩ (prowlerSource prowlerReady) prowlerAbility
#guard !(prowlerReady.canActivate ⟨1⟩ (prowlerSource prowlerReady) prowlerAbility)
#guard prowlerReady.power (prowlerSource prowlerReady) == 2
#guard prowlerReady.toughness (prowlerSource prowlerReady) == 2
#guard (prowlerReady.player ⟨0⟩).life == 20

-- The heuristic pays 2 life to pump when it would not lose the game.
#guard
  match Agent.choose prowlerReady ⟨0⟩ with
  | some (.activate id 0) => id == (prowlerSource prowlerReady).id
  | _ => false

-- Life payment is part of activation, so the ability is on the stack immediately.
def activatedProwler : Game :=
  mustApply prowlerReady ⟨0⟩ (.activate (prowlerSource prowlerReady).id 0)

#guard activatedProwler.pending == .none
#guard activatedProwler.hasPriority ⟨0⟩
#guard activatedProwler.stack.size == 1
#guard (activatedProwler.object! activatedProwler.stack.back!.objectId).abilityEffect ==
  some (Effect.sourceGets 2 2)
#guard (activatedProwler.player ⟨0⟩).life == 18
#guard activatedProwler.log.any (fun s => mentions s "begins activating Desolation Prowler")
#guard activatedProwler.log.any (fun s => mentions s "pays 2 life (18 life)")
#guard activatedProwler.log.any (fun s => mentions s "activates Desolation Prowler")
#guard (namedPermanent activatedProwler "Desolation Prowler").status.activationsThisTurn == 1
#guard (namedPermanent activatedProwler "Desolation Prowler").status.pumpPower == 0

-- Payment of life is not damage (CR 118.3b).
#guard !(activatedProwler.log.any (fun s => mentions s "is dealt"))

def pumpedProwler : Game := passBoth activatedProwler

#guard pumpedProwler.stack.isEmpty
#guard (namedPermanent pumpedProwler "Desolation Prowler").status.pumpPower == 2
#guard (namedPermanent pumpedProwler "Desolation Prowler").status.pumpToughness == 2
#guard pumpedProwler.power (namedPermanent pumpedProwler "Desolation Prowler") == 4
#guard pumpedProwler.toughness (namedPermanent pumpedProwler "Desolation Prowler") == 4
#guard (pumpedProwler.player ⟨0⟩).life == 18
#guard pumpedProwler.log.any (fun s =>
  mentions s "Desolation Prowler gets +2/+2 until end of turn")

-- Only once each turn (CR 602.2b).
#guard !(pumpedProwler.canActivate ⟨0⟩ (prowlerSource pumpedProwler) prowlerAbility)
#guard
  match pumpedProwler.activateAbility ⟨0⟩ (prowlerSource pumpedProwler).id 0 with
  | .error msg => mentions msg "only once each turn"
  | .ok _ => false

/-- The +2/+2 wears off in cleanup, and the once-each-turn count resets. -/
def afterProwlerCleanup : Game :=
  passBoth (skipTo pumpedProwler .end 80)

#guard afterProwlerCleanup.power
  (namedPermanent afterProwlerCleanup "Desolation Prowler") == 2
#guard (namedPermanent afterProwlerCleanup "Desolation Prowler").status.pumpPower == 0
#guard (namedPermanent afterProwlerCleanup "Desolation Prowler").status.activationsThisTurn == 0

-- Instant-speed: Prowler can activate during the end step.
def prowlerAtEndStep : Game := skipTo prowlerReady .end 80

#guard prowlerAtEndStep.step == .end
#guard prowlerAtEndStep.canActivate ⟨0⟩ (prowlerSource prowlerAtEndStep) prowlerAbility

-- A player with 1 life cannot pay 2 life (CR 119.4).
#guard
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 1 })
  !g.canActivate ⟨0⟩ (prowlerSource g) prowlerAbility
#guard
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 1 })
  match g.activateAbility ⟨0⟩ (prowlerSource g).id 0 with
  | .error msg => mentions msg "cannot pay 2 life"
  | .ok _ => false

-- Paying 2 life from 2 life is legal, then CR 704.5a ends the game.
def prowlerPaysLastLife : Game :=
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  mustApply g ⟨0⟩ (.activate (prowlerSource g).id 0)

#guard (prowlerPaysLastLife.player ⟨0⟩).life == 0
#guard prowlerPaysLastLife.over
#guard prowlerPaysLastLife.result == some (.won ⟨1⟩)
#guard prowlerPaysLastLife.log.any (fun s => mentions s "pays 2 life (0 life)")
#guard prowlerPaysLastLife.log.any (fun s => mentions s "loses the game (life total 0)")
#guard prowlerPaysLastLife.power (namedPermanent prowlerPaysLastLife "Desolation Prowler") == 2

-- The heuristic will not pay the last 2 life.
#guard
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  match Agent.choose g ⟨0⟩ with
  | some (.activate _ 0) => false
  | _ => true

/-- Lethal damage puts the dies trigger on the stack (CR 700.4 / 603.3d). -/
def fireleaperDied : Game :=
  let o := namedPermanent fireleaperReady "Goblin Fireleaper"
  let g := fireleaperReady.setObject { o with status := { o.status with damage := 1 } }
  g.receivePriority ⟨0⟩

#guard fireleaperDied.pending == .chooseTargets ⟨0⟩
#guard fireleaperDied.stack.size == 1
#guard (fireleaperDied.object! fireleaperDied.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature
#guard (fireleaperDied.object! fireleaperDied.stack.back!.objectId).lastKnownPower == some 1
#guard fireleaperDied.stack.back!.targets.isEmpty
#guard fireleaperDied.log.any (fun s => mentions s "dies from lethal damage")
#guard fireleaperDied.log.any (fun s => mentions s "dies trigger is put on the stack")
#guard fireleaperDied.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !(fireleaperDied.battlefield.any (fun o => o.name == "Goblin Fireleaper"))
#guard !fireleaperDied.hasPriority ⟨0⟩
#guard fireleaperDied.actor == some ⟨0⟩

-- The dies trigger cannot target a player or a creature you control.
#guard
  match fireleaperDied.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent fireleaperDied ragingGoblin ⟨0⟩ ⟨0⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Raging Goblin").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Hexproof on an opponent's creature is not a legal target (CR 702.11b).
#guard
  let bears := namedPermanent fireleaperDied "Grizzly Bears"
  let g := fireleaperDied.setObject { bears with
    status := { bears.status with untilEotKeywords := Keyword.hexproof } }
  match g.apply ⟨0⟩ (.target (Target.permanent bears.id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets an opposing creature.
#guard
  match Agent.choose fireleaperDied ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (fireleaperDied.object! tid).name == "Grizzly Bears"
  | _ => false

def fireleaperDeathTargeted : Game :=
  mustApply fireleaperDied ⟨0⟩
    (.target (Target.permanent (namedPermanent fireleaperDied "Grizzly Bears").id))

#guard fireleaperDeathTargeted.pending == .none
#guard fireleaperDeathTargeted.hasPriority ⟨0⟩
#guard fireleaperDeathTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent fireleaperDeathTargeted "Grizzly Bears").id]
#guard fireleaperDeathTargeted.log.any (fun s => mentions s "chooses Grizzly Bears as a target")

def fireleaperDeathResolved : Game := passBoth fireleaperDeathTargeted

#guard fireleaperDeathResolved.stack.isEmpty
#guard fireleaperDeathResolved.log.any (fun s =>
  mentions s "Goblin Fireleaper deals 1 damage to Grizzly Bears")
#guard (namedPermanent fireleaperDeathResolved "Grizzly Bears").status.damage == 1
#guard fireleaperDeathResolved.battlefield.any (fun o => o.name == "Grizzly Bears")

/-- Pumped power is last known information when the Fireleaper dies (CR 113.7a). -/
def fireleaperPumpedThenDied : Game :=
  let o := namedPermanent pumpedFireleaper "Goblin Fireleaper"
  let g := pumpedFireleaper.setObject { o with status := { o.status with damage := 1 } }
  let g := g.receivePriority ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  passBoth g

#guard fireleaperPumpedThenDied.log.any (fun s =>
  mentions s "Goblin Fireleaper deals 2 damage to Grizzly Bears")
#guard !(fireleaperPumpedThenDied.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard fireleaperPumpedThenDied.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")

/-- No opposing creature: the dies trigger is removed (CR 603.3d). -/
def fireleaperDiedAlone : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Goblin Fireleaper"
  let g := g.setObject { o with status := { o.status with damage := 1 } }
  g.receivePriority ⟨0⟩

#guard fireleaperDiedAlone.stack.isEmpty
#guard fireleaperDiedAlone.hasPriority ⟨0⟩
#guard fireleaperDiedAlone.log.any (fun s => mentions s "no legal target")
#guard !(fireleaperDiedAlone.battlefield.any (fun o => o.name == "Goblin Fireleaper"))

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def fireleaperDeathTargetGone : Game :=
  let id := (namedPermanent fireleaperDeathTargeted "Grizzly Bears").id
  let (g, _) := fireleaperDeathTargeted.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard fireleaperDeathTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(fireleaperDeathTargetGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- Combat: 1/1 Fireleaper into 2/2 Bears. Fireleaper dies; the trigger then
kills the Bears. -/
def fireleaperVsBearsCombat : Game :=
  addPermanent (addPermanent started goblinFireleaper ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def fireleaperBlockedByBears : Game :=
  let g := passBoth (skipTo fireleaperVsBearsCombat .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Goblin Fireleaper").id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Goblin Fireleaper").id)])

#guard fireleaperBlockedByBears.stack.isEmpty
#guard fireleaperBlockedByBears.step == .declareBlockers

def fireleaperAfterCombatDamage : Game := passBoth fireleaperBlockedByBears

#guard fireleaperAfterCombatDamage.step == .combatDamage
#guard fireleaperAfterCombatDamage.pending == .chooseTargets ⟨0⟩
#guard !(fireleaperAfterCombatDamage.battlefield.any (fun o => o.name == "Goblin Fireleaper"))
#guard fireleaperAfterCombatDamage.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent fireleaperAfterCombatDamage "Grizzly Bears").status.damage == 1
#guard fireleaperAfterCombatDamage.log.any (fun s => mentions s "dies trigger is put on the stack")

def afterFireleaperBearsCombat : Game :=
  let g := mustApply fireleaperAfterCombatDamage ⟨0⟩
    (.target (Target.permanent (namedPermanent fireleaperAfterCombatDamage "Grizzly Bears").id))
  passBoth g

#guard afterFireleaperBearsCombat.log.any (fun s =>
  mentions s "Goblin Fireleaper deals 1 damage to Grizzly Bears")
#guard afterFireleaperBearsCombat.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")
#guard !(afterFireleaperBearsCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard !(afterFireleaperBearsCombat.battlefield.any (fun o => o.name == "Goblin Fireleaper"))

/-- Both 1/1s die in combat: no remaining opposing creature, trigger removed. -/
def fireleaperVsElvesCombat : Game :=
  addPermanent (addPermanent started goblinFireleaper ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def afterFireleaperElvesCombat : Game :=
  let g := passBoth (skipTo fireleaperVsElvesCombat .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Goblin Fireleaper").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Goblin Fireleaper").id)])
  passBoth g

#guard afterFireleaperElvesCombat.stack.isEmpty
#guard afterFireleaperElvesCombat.pending == .none
#guard afterFireleaperElvesCombat.log.any (fun s => mentions s "no legal target")
#guard !(afterFireleaperElvesCombat.battlefield.any (fun o => o.name == "Goblin Fireleaper"))
#guard !(afterFireleaperElvesCombat.battlefield.any (fun o => o.name == "Llanowar Elves"))

/-- Sacrificing Fireleaper to Snowslope Hunter puts the dies trigger above the
activated ability. -/
def hunterSacrificesFireleaper : Game :=
  let g := addPermanent afterDraw snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addUntappedLand g mountain
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Snowslope Hunter").id 0)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Goblin Fireleaper").id)

#guard hunterSacrificesFireleaper.pending == .chooseTargets ⟨0⟩
#guard hunterSacrificesFireleaper.stack.size == 2
#guard (hunterSacrificesFireleaper.object! hunterSacrificesFireleaper.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature
#guard hunterSacrificesFireleaper.log.any (fun s => mentions s "sacrifices Goblin Fireleaper")
#guard hunterSacrificesFireleaper.log.any (fun s => mentions s "dies trigger is put on the stack")

end Mtg.Engine.Tests
