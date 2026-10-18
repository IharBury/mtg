import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.fight`

The source fighting up to one other creature, and the creature that
received Equipment dealing damage equal to its power. Who fights and
how are arguments. Any other permanent the selector names fights that
way. A card or an unmade choice fights nothing.
-/

namespace Mtg.Engine.TriggerFightTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def alpha : CardDef := creature "Alpha" ManaCost.empty #[] 2 4
def beta : CardDef := creature "Beta" ManaCost.empty #[] 3 4

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (resolutionOverride := some r)

def pid (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def damageOf (g : Game) (name : String) : Int :=
  match g.objects.find? (·.name == name) with
  | some o => o.status.damage
  | none => panic! s!"missing {name}"

def board : Game :=
  addPermanent (addPermanent afterDraw alpha caster caster) beta opp opp

def sourceFight : TriggeredAbility.TriggerResolution := .fight .source .mutual
def hostDamage : TriggeredAbility.TriggerResolution := .fight .equipmentHost .reflexive

/- The source and the announced creature each deal damage equal to their
power. Choosing none fights nothing. -/
#guard
  let g0 := board
  let g := step g0 sourceFight (some (pid g0 "Alpha")) #[Target.permanent (pid g0 "Beta")]
  damageOf g "Alpha" == 3 && damageOf g "Beta" == 2 &&
    g.pending == g0.pending

#guard
  let g0 := board
  let g := step g0 .fight (some (pid g0 "Alpha")) #[Target.permanent (pid g0 "Beta")]
  damageOf g "Alpha" == 3 && damageOf g "Beta" == 2

#guard
  let g0 := board
  let g := step g0 sourceFight (some (pid g0 "Alpha"))
  damageOf g "Alpha" == 0 && damageOf g "Beta" == 0 &&
    g.pending == g0.pending && !(logContains g "no longer")

/- A missing source, a source that has left, and a target that has left
each fight nothing. -/
#guard
  let g0 := board
  let g := step g0 sourceFight none #[Target.permanent (pid g0 "Beta")]
  logContains g "The source is no longer in play" && damageOf g "Beta" == 0

#guard
  let g0 := board
  let (g1, alphaId) := g0.move (pid g0 "Alpha") (.graveyard caster) none
  let g := step g1 sourceFight (some alphaId) #[Target.permanent (pid g0 "Beta")]
  logContains g "The target is no longer legal" && damageOf g "Beta" == 0 &&
    damageOf g "Alpha" == 0

#guard
  let g0 := board
  let betaId := pid g0 "Beta"
  let (g1, _) := g0.move betaId (.graveyard opp) none
  let g := step g1 sourceFight (some (pid g0 "Alpha")) #[Target.permanent betaId]
  logContains g "The target is no longer legal" && damageOf g "Alpha" == 0

#guard
  let g0 := board
  let g := step g0 sourceFight (some (pid g0 "Alpha")) #[Target.permanent ⟨99999⟩]
  logContains g "The target is no longer legal" && damageOf g "Alpha" == 0 &&
    damageOf g "Beta" == 0

/- The creature that received Equipment queues a reflexive ability. The
target is chosen then, and only that creature is dealt damage. -/
#guard
  let g0 := board
  let alphaId := pid g0 "Alpha"
  let g := step { g0 with equipmentAttachedHost := some alphaId } hostDamage
  g.equipmentAttachedHost.isNone && damageOf g "Alpha" == 0 &&
    damageOf g "Beta" == 0 &&
    match g.pending with
    | .chooseTargets p => p == caster
    | _ => false

#guard
  let g0 := board
  let alphaId := pid g0 "Alpha"
  let g := step { g0 with equipmentAttachedHost := some alphaId } hostDamage
  match (g.object! g.stack.back!.objectId).abilityEffect with
  | some e =>
    e.resolution == .dealDamage (.power .source) .target && e.allowsZeroTargets &&
      e.phrase == "Alpha deals damage equal to its power to up to one target creature" &&
      (g.object! g.stack.back!.objectId).sourceId == some alphaId
  | none => false

#guard
  let g0 := board
  let alphaId := pid g0 "Alpha"
  let betaId := pid g0 "Beta"
  let g := step { g0 with equipmentAttachedHost := some alphaId } hostDamage
  let g := passBoth (mustApply g caster (.target (.permanent betaId)))
  damageOf g "Beta" == 2 && damageOf g "Alpha" == 0 &&
    logContains g "reflexive ability is put on the stack"

/- No attached creature, or one that has left, queues nothing. -/
#guard
  let g0 := board
  let g := step g0 hostDamage
  g.pending == g0.pending && g.stack.size == g0.stack.size &&
    damageOf g "Alpha" == 0 && damageOf g "Beta" == 0 &&
    !(logContains g "reflexive")

#guard
  let g0 := board
  let alphaId := pid g0 "Alpha"
  let (g1, _) := g0.move alphaId (.graveyard caster) none
  let g := step { g1 with equipmentAttachedHost := some alphaId } hostDamage
  g.equipmentAttachedHost.isNone && g.stack.size == g1.stack.size &&
    !(logContains g "reflexive")

#guard
  let g0 := board
  let g := step { g0 with equipmentAttachedHost := some ⟨99999⟩ } hostDamage
  g.equipmentAttachedHost.isNone && g.stack.size == g0.stack.size &&
    !(logContains g "reflexive")

/- The source dealing damage equal to its power hits the other creature
and does not queue a reflexive. The equipped creature fighting that
other creature deals damage both ways. The announced creature, with no
other creature chosen, has nothing to fight. -/
#guard
  let g0 := board
  let alphaId := pid g0 "Alpha"
  let marked := { g0 with equipmentAttachedHost := some alphaId }
  let g := step marked (.fight .source .reflexive) (some alphaId)
    #[Target.permanent (pid g0 "Beta")]
  g.equipmentAttachedHost == some alphaId && g.stack.size == marked.stack.size &&
    g.pending == marked.pending && damageOf g "Alpha" == 0 &&
    damageOf g "Beta" == 2 && !(logContains g "reflexive")

#guard
  let g0 := board
  let alphaId := pid g0 "Alpha"
  let marked := { g0 with equipmentAttachedHost := some alphaId }
  let g := step marked (.fight .equipmentHost .mutual) (some alphaId)
    #[Target.permanent (pid g0 "Beta")]
  g.equipmentAttachedHost == some alphaId && g.stack.size == marked.stack.size &&
    damageOf g "Alpha" == 3 && damageOf g "Beta" == 2 &&
    !(logContains g "reflexive")

#guard
  let g0 := board
  let g := step g0 (.fight .target .mutual) (some (pid g0 "Alpha"))
    #[Target.permanent (pid g0 "Beta")]
  damageOf g "Alpha" == 0 && damageOf g "Beta" == 0 &&
    logContains g "Beta has nothing to fight"

/- Printed phrases stay with the combination that produces them. -/
#guard (.fight : TriggeredAbility.TriggerResolution) == sourceFight
#guard TriggeredAbility.resolutionPhrase { resolution := .fight } ==
  "this fights up to one other target creature"
#guard TriggeredAbility.resolutionPhrase { resolution := sourceFight } ==
  "this fights up to one other target creature"
#guard TriggeredAbility.resolutionPhrase { resolution := hostDamage } ==
  "that creature deals damage equal to its power to up to one target creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .«if» .equipmentAttached hostDamage } ==
  "that creature deals damage equal to its power to up to one target creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .sequence [.attach .anyYouControl .target,
        .«if» .equipmentAttached hostDamage] } ==
  "attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .fight .source .reflexive } == "fight"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .fight .equipmentHost .mutual } == "fight"
#guard TriggeredAbility.resolution (.onEnter Effect.enterFightUpToOne) == .fight
#guard TriggeredAbility.resolution .onEnterAttachEquipmentThenFight ==
  .sequence [.attach .anyYouControl .target, .«if» .equipmentAttached hostDamage]

end Mtg.Engine.TriggerFightTests
