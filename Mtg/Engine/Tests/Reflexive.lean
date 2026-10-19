import Mtg.Engine.Fixture

/-!
# `TriggerResolution.queueReflexive`

A modeled reflexive, divided damage, a milled spell, and this turn's
attack pump are the same constructor. Sacrificing the Plan and milling
an opponent are `if` notes the next step reads. Printed phrases stay
with the combination that produces them.
-/

namespace Mtg.Engine.ReflexiveTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def planCard : CardDef := {
  name := "The Plan"
  types := #[.enchantment]
}

def bolt : CardDef := {
  name := "Copied Bolt"
  types := #[.instant]
}

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId #[]
    (lastKnownPower := lastKnownPower) (resolutionOverride := some r)

def planOnBoard : Game :=
  addPermanent afterDraw planCard caster caster

def planId (g : Game) : ObjectId :=
  match g.battlefield.find? (·.name == "The Plan") with
  | some o => o.id
  | none => panic! "missing The Plan"

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id pl =>
    { pl with graveyard := pl.graveyard.push id })

def stackEffect (g : Game) : Option Effect :=
  match g.stack.back? with
  | some e => (g.findObject? e.objectId).bind (·.abilityEffect)
  | none => none

def sacrificed (follow : TriggeredAbility.TriggerResolution) :
    TriggeredAbility.TriggerResolution :=
  .sequence [
    .sacrifice .plan .forReflexive,
    .«if» .planWasSacrificed (.queueReflexive follow)]

/- The Plan's reflexive abilities, the milled copy, and the attack pump
use `queueReflexive`. -/
#guard TriggeredAbility.resolution .onFourthPlanReturnInstants ==
  sacrificed (.returnToHand (.graveyardInstants 2))
#guard TriggeredAbility.resolution .onSeventhPlanControlOpponent ==
  sacrificed (.gainControl .duringNextTurn)
#guard TriggeredAbility.resolution .onFifthPlanExileTopCast ==
  sacrificed (.exile (.opponentTop 5) (.mayCastUpTo 2))
#guard TriggeredAbility.resolution .onFourthPlanIndestructible ==
  sacrificed (.putCounters (.ofKind .indestructible) .permanent)
#guard TriggeredAbility.resolution .onFourthPlanDividedDamage ==
  .sequence [
    .sacrifice .plan .forReflexive,
    .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed 7) .target .divided))]
#guard TriggeredAbility.resolution .onCastSecondSpellMillThenCopy ==
  .sequence [
    .mill (.fixed 2) .eachOpponent (note := .opponentsMilled),
    .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))]
#guard (SharedTrigger.timing (.chapter 0 .grantAttackPumpPerPlainsThisTurn)).resolution ==
  .queueReflexive (.pump .perPlains .perPlains .target)

#guard TriggeredAbility.TriggerReflexiveKind.toNat .grantIndestructible == 0
#guard TriggeredAbility.TriggerReflexiveKind.toNat .trickArrows == 2
#guard TriggeredAbility.TriggerReflexiveKind.toNat .indestructibleCounter == 3
#guard TriggeredAbility.TriggerReflexiveKind.toNat .controlOpponent == 4
#guard TriggeredAbility.TriggerReflexiveKind.toNat .exileTopFive == 5
#guard TriggeredAbility.TriggerReflexiveKind.toNat .returnAttacking == 6
#guard TriggeredAbility.TriggerReflexiveKind.toNat .destroyOppNonland == 7
#guard TriggeredAbility.TriggerReflexiveKind.toNat .countersDamage == 8
#guard TriggeredAbility.TriggerReflexiveKind.toNat .hasteUnblockable == 9
#guard TriggeredAbility.TriggerReflexiveKind.toNat .returnInstants == 11
#guard TriggeredAbility.TriggerReflexiveKind.toNat .plusOne == 12

#guard TriggeredAbility.resolutionPhrase
    { resolution := .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2))) } ==
  "when you do, the reflexive ability triggers"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed 7) .target .divided)) } ==
  "when you do, it deals 7 damage divided as you choose among one or two targets"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying) } ==
  "exile and copy a card"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying)) } ==
  "when one or more cards are milled this way, exile and copy a card"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .queueReflexive (.pump .perPlains .perPlains .target) } ==
  "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control"
#guard TriggeredAbility.resolutionPhrase
    (TriggeredAbility.onFourthPlanDividedDamage).timing ==
  "sacrifice it. When you do, it deals 7 damage divided as you choose among one or two targets"
#guard TriggeredAbility.resolutionPhrase
    (TriggeredAbility.onCastSecondSpellMillThenCopy).timing ==
  "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"

/- Sacrificing the Plan queues the reflexive and consumes the note. -/
#guard
  let g0 := planOnBoard
  let sid := planId g0
  let g := step g0 (sacrificed (.returnToHand (.graveyardInstants 2))) (some sid)
  let queued :=
    match stackEffect g with
    | some eff =>
      match eff.resolution with
      | .mshReflexive 11 _ =>
        eff.phrase ==
          "Return up to two target instant and/or sorcery cards from your graveyard to your hand"
      | _ => false
    | none => false
  !g.planWasSacrificed && queued &&
    !(g.battlefield.any (·.id == sid)) &&
    logContains g "the Plan is completed" &&
    logContains g "reflexive ability is put on the stack"

/- A second check of that note queues nothing. -/
#guard
  let g0 := planOnBoard
  let sid := planId g0
  let g := step g0 (sacrificed (.returnToHand (.graveyardInstants 2))) (some sid)
  let again := step g (.«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2))))
    (some sid)
  g.stack.size == again.stack.size && !again.planWasSacrificed

/- A Plan that has already left queues nothing. -/
#guard
  let g0 := planOnBoard
  let sid := planId g0
  let (gGone, _) := g0.move sid (.graveyard caster) none
  let g := step gGone (sacrificed (.putCounters (.ofKind .indestructible) .permanent)) (some sid)
  g.stack.isEmpty && !g.planWasSacrificed &&
    logContains g "is no longer on the battlefield. The reflexive ability doesn't trigger."

/- The note alone, without a sacrifice, queues the modeled reflexive once. -/
#guard
  let g0 := { planOnBoard with thisWay := { planOnBoard.thisWay with planWasSacrificed := true } }
  let g := step g0 (.«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn)))
  !g.planWasSacrificed && g.hasModeledReflexiveOnStack

/- Divided damage uses the printed total and the divided-damage reflexive. -/
#guard
  let g0 := planOnBoard
  let sid := planId g0
  let g := step g0 (.sequence [
    .sacrifice .plan .forReflexive,
    .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed 7) .target .divided))]) (some sid)
  match stackEffect g with
  | some eff =>
    eff.dividedDamage == some (7, 2) &&
      (match eff.resolution with
       | .mshReflexive 10 _ => true
       | _ => false) &&
      eff.phrase == "It deals 7 damage divided as you choose among one or two targets" &&
      !g.planWasSacrificed
  | none => false

/- No note queues no divided damage. -/
#guard
  let g := step planOnBoard
    (.«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed 7) .target .divided)))
  g.stack.isEmpty && !g.planWasSacrificed

/- A milled instant of a low enough mana value is the reflexive's target. -/
#guard
  let g0 := putInGraveyard afterDraw bolt opp
  let g := step g0 (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying)) none (some 1)
  match stackEffect g with
  | some eff =>
    match eff.resolution with
    | .mayCast .milledSpell .causingSpell .withoutPaying _ =>
      logContains g "reflexive ability is put on the stack"
    | _ => false
  | none => false

/- No legal milled card removes the reflexive. -/
#guard
  let g := step afterDraw (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying)) none (some 1)
  g.stack.isEmpty &&
    logContains g "reflexive ability has no legal target and is removed"

/- A follow-up that is not a modeled reflexive is still put on the stack,
and resolving it applies that follow-up. -/
#guard
  let g0 := afterDraw
  let hand := (g0.player caster).hand.size
  let g := step g0 (.queueReflexive (.draw (.fixed 1)))
  let queued :=
    match g.stack.back?.bind (fun e => g.findObject? e.objectId) with
    | some o =>
      o.reflexiveResolution == some (.draw (.fixed 1)) && o.abilityEffect.isNone
    | none => false
  let resolved := passBoth g
  queued && g.stack.size == g0.stack.size + 1 &&
    logContains g "reflexive ability is put on the stack" &&
    (resolved.player caster).hand.size == hand + 1

/- Each resolution arms one attack pump for the rest of this turn. -/
#guard
  let g := step afterDraw (.queueReflexive (.pump .perPlains .perPlains .target))
  let again := step g (.queueReflexive (.pump .perPlains .perPlains .target))
  (g.player caster).attackPumpPerPlainsThisTurn == 1 &&
    logContains g "for each Plains they control" &&
    (again.player caster).attackPumpPerPlainsThisTurn == 2

end Mtg.Engine.ReflexiveTests
