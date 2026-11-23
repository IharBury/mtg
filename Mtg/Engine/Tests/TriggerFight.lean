import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified fight and bite instructions (`DamageOp.fight`)

The source fighting up to one other target creature (`Effect.enterFightUpToOne`),
one-way power damage (`DamageOp.fight ... true`), and Thorin's attach-Equipment
reflexive trigger (`Effect.triggerAttachEquipmentThenFight`) all execute through
`Game/Interpreter.lean`.
-/

namespace Mtg.Engine.TriggerFightTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def alpha : CardDef := creature "Alpha" ManaCost.empty #[] 2 4
def beta : CardDef := creature "Beta" ManaCost.empty #[] 3 4
def blade : CardDef := {
  name := "Thorin's Blade"
  types := #[.artifact]
  subtypes := #["Equipment"]
}

def stepEffect (g : Game) (e : Effect)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters e) sourceId targets

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

def oneWayBite : Effect :=
  { targets := TargetSpec.creature.asUpTo 1
    body := .damage (.fight .this (.target 0) true) }

/- The source and the announced creature each deal damage equal to their
power. Choosing none fights nothing. -/
#guard
  let g0 := board
  let g := stepEffect g0 Effect.enterFightUpToOne (some (pid g0 "Alpha"))
    #[Target.permanent (pid g0 "Beta")]
  damageOf g "Alpha" == 3 && damageOf g "Beta" == 2 &&
    g.pending == g0.pending

#guard
  let g0 := board
  let g := stepEffect g0 Effect.enterFightUpToOne (some (pid g0 "Alpha"))
  damageOf g "Alpha" == 0 && damageOf g "Beta" == 0 &&
    g.pending == g0.pending && !(logContains g "no longer")

/- A missing source, a source that has left, and a target that has left
each fight nothing. -/
#guard
  let g0 := board
  let g := stepEffect g0 Effect.enterFightUpToOne none #[Target.permanent (pid g0 "Beta")]
  damageOf g "Beta" == 0

#guard
  let g0 := board
  let (g1, alphaId) := g0.move (pid g0 "Alpha") (.graveyard caster) none
  let g := stepEffect g1 Effect.enterFightUpToOne (some alphaId)
    #[Target.permanent (pid g0 "Beta")]
  damageOf g "Beta" == 0 && damageOf g "Alpha" == 0

#guard
  let g0 := board
  let betaId := pid g0 "Beta"
  let (g1, _) := g0.move betaId (.graveyard opp) none
  let g := stepEffect g1 Effect.enterFightUpToOne (some (pid g0 "Alpha"))
    #[Target.permanent betaId]
  logContains g "The target is no longer" && damageOf g "Alpha" == 0

#guard
  let g0 := board
  let g := stepEffect g0 Effect.enterFightUpToOne (some (pid g0 "Alpha"))
    #[Target.permanent ⟨99999⟩]
  logContains g "The target is no longer" && damageOf g "Alpha" == 0 &&
    damageOf g "Beta" == 0

/- One-way bite deals damage equal to source's power without dealing damage back. -/
#guard
  let g0 := board
  let g := stepEffect g0 oneWayBite (some (pid g0 "Alpha"))
    #[Target.permanent (pid g0 "Beta")]
  damageOf g "Alpha" == 0 && damageOf g "Beta" == 2

/- Thorin: attaching Equipment queues a reflexive trigger that deals the host's
power to up to one target creature. Declining to attach queues nothing. -/
#guard
  let g0 := addPermanent board blade caster caster
  let alphaId := pid g0 "Alpha"
  let betaId := pid g0 "Beta"
  let bladeId := pid g0 "Thorin's Blade"
  let offered := g0.applyTriggeredAbility caster .onEnterAttachEquipmentThenFight none
    #[Target.permanent alphaId]
  let attached := mustApply offered caster (.choosePermanents #[bladeId])
  let chosen := mustApply attached caster (.target (.permanent betaId))
  let resolved := passBoth chosen
  (match attached.pending with | .chooseTargets p => p == caster | _ => false) &&
    damageOf resolved "Beta" == 2 && damageOf resolved "Alpha" == 0 &&
    logContains resolved "reflexive ability is put on the stack"

#guard
  let g0 := addPermanent board blade caster caster
  let alphaId := pid g0 "Alpha"
  let offered := g0.applyTriggeredAbility caster .onEnterAttachEquipmentThenFight none
    #[Target.permanent alphaId]
  let declined := mustApply offered caster .decline
  declined.pending == .none && declined.stack.size == g0.stack.size &&
    damageOf declined "Alpha" == 0 && damageOf declined "Beta" == 0 &&
    !(logContains declined "reflexive")

/- Printed phrases and notations stay intact. -/
#guard TriggeredAbility.resolutionPhrase Effect.enterFightUpToOne ==
  "this fights up to one other target creature"
#guard (TriggeredAbility.onEnter Effect.enterFightUpToOne).effect.body ==
  Effect.enterFightUpToOne.body
#guard TriggeredAbility.onEnterAttachEquipmentThenFight.effect.body ==
  Effect.triggerAttachEquipmentThenFight.body
#guard TriggeredAbility.toNotation .onEnterAttachEquipmentThenFight ==
  "When this permanent enters, attach Equipment you control (chosen) to target creature you control. If you do, when you do, that permanent deals damage equal to its power to up to one target creature."

end Mtg.Engine.TriggerFightTests
