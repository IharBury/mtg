import Mtg.Engine.Game.PowerToughness

/-!
# Combat damage assignment (CR 510.1)

Assigned-damage queries, lethal damage remaining (deathtouch-aware,
CR 702.2c), first-strike rounds (CR 508.4a), and which creatures still
need a combat-damage-assignment choice.
-/

namespace Mtg.Engine
namespace Game

/-- Combat damage already assigned to `id` in `asgns`. -/
def damageAssignedTo (asgns : Array CreatureCombatAssignment) (id : ObjectId) : Int :=
  asgns.foldl
    (fun acc a =>
      acc + a.toCreatures.foldl (fun n (tid, amt) => if tid == id then n + amt else n) 0)
    0

/-- Remaining lethal for trample (CR 702.19b): toughness minus marked damage
and damage already assigned this step. Any positive assignment from a
deathtouch source is lethal (CR 702.2c). `fromDeathtouch` is the source
currently assigning, so that source needs only 1 more if lethal remains. -/
def lethalRemaining (g : Game) (o : GameObject) (already : Array CreatureCombatAssignment)
    (fromDeathtouch := false) : Int :=
  let remaining := max (g.toughness o - o.status.damage - damageAssignedTo already o.id) 0
  let alreadyDeathtouch := already.any (fun a =>
    a.toCreatures.any (fun (tid, amt) => tid == o.id && amt > 0) &&
      match g.findObject? a.source with
      | some src => g.hasDeathtouch src
      | none => false)
  if remaining == 0 || alreadyDeathtouch then 0
  else if fromDeathtouch then 1
  else remaining

/-- True when any attacking or blocking creature has first strike (CR 702.7b). -/
def combatHasFirstStrike (g : Game) : Bool :=
  g.battlefield.any (fun o =>
    g.hasFirstStrike o && (o.status.attacking || !o.status.blocking.isEmpty))

/-- Creatures that assign combat damage in the current half of CR 510.1.
A first-strike combat damage step includes only first strikers; the regular
step includes only creatures without first strike (CR 702.7b). -/
def creaturesAssigningCombatDamage (g : Game) (forAttackers : Bool) : Array GameObject :=
  let all :=
    if forAttackers then
      g.battlefield.filter (·.status.attacking)
    else
      g.battlefield.filter (fun o => !o.status.blocking.isEmpty)
  if !g.combatHasFirstStrike && g.firstStrikeAssignedThisCombat.isEmpty then all
  else if !g.firstStrikeDamageDone then all.filter (g.hasFirstStrike)
  else
    all.filter (fun o =>
      if g.firstStrikeAssignedThisCombat.any (· == o.id) then
        g.hasDoubleStrike o
      else
        !g.hasFirstStrike o || g.hasDoubleStrike o)

/-- Legal creature recipients for `source`'s combat damage (CR 510.1c–d). -/
def legalCombatDamageRecipients (g : Game) (source : GameObject) (forAttackers : Bool) :
    Array GameObject :=
  if forAttackers then g.blockersOf source.id else g.creaturesBlockedBy source

/-- True when leftover combat damage may be assigned to the defending player
(unblocked, or trample; CR 510.1a / 702.19). -/
def canAssignCombatDamageToDefendingPlayer (g : Game) (source : GameObject)
    (forAttackers : Bool) : Bool :=
  forAttackers && (!source.status.blocked || g.hasTrample source)

/-- Combat damage `source` must assign this step (CR 510.1a), or `0` if it
assigns none because no recipients remain (CR 510.1c–d). -/
def combatDamageToAssign (g : Game) (source : GameObject) (forAttackers : Bool) : Int :=
  if (g.legalCombatDamageRecipients source forAttackers).isEmpty &&
      !g.canAssignCombatDamageToDefendingPlayer source forAttackers then
    0
  else
    let amt :=
      match g.assignCombatDamageEqualToughness with
      | some pid =>
        if source.controlledBy pid && g.toughness source > g.power source then
          g.toughness source
        else g.power source
      | none => g.power source
    max amt 0

/-- True when a creature this player controls has two or more creature
recipients, so the controller must divide combat damage (CR 510.1c–d). -/
def needsCombatDamageChoice (g : Game) (forAttackers : Bool) : Bool :=
  (g.creaturesAssigningCombatDamage forAttackers).any (fun o =>
    (g.legalCombatDamageRecipients o forAttackers).size ≥ 2 && max (g.power o) 0 > 0)

end Game
end Mtg.Engine
