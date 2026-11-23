import Mtg.Engine.Fixture

/-!
# Unified surveil instructions (`Instruction.surveil` / `PlayerOp.surveil`)

Fixed counts and dynamic `ValueExpr` counts both execute through
`Game/Interpreter.lean`. Surveil 0 still logs.
-/

namespace Mtg.Engine.SurveilTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

def perOtherCreature : ValueExpr :=
  ValueExpr.count (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you]))

def stepBody (g : Game) (body : Instruction) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters { body }) none

/- Surveil 1 looks at one card. -/
#guard
  let g := stepBody afterDraw (Instruction.surveilFixed 1)
  match g.pending with
  | .surveil p n _ => p == caster && n == 1
  | _ => false

/- A count of other creatures is surveilled. Zero creatures still surveils 0. -/
#guard
  let g := stepBody afterDraw (Instruction.surveil perOtherCreature)
  g.pending == afterDraw.pending && logContains g "surveils 0"

#guard
  let bear : CardDef := {
    name := "Surveil Bear"
    types := #[.creature]
    power := some 2
    toughness := some 2
  }
  let g0 := addPermanent afterDraw bear caster caster
  let g := stepBody g0 (Instruction.surveil perOtherCreature)
  match g.pending with
  | .surveil p n _ => p == caster && n == 1
  | _ => false

#guard (TriggeredAbility.onEnterSurveil 2).effect.body == Instruction.surveilFixed 2
#guard TriggeredAbility.resolutionPhrase { body := Instruction.surveilFixed 2 } == "surveil 2"
#guard TriggeredAbility.toNotation (.onEnterSurveil 2) == "When this permanent enters, surveil 2."

end Mtg.Engine.SurveilTests
