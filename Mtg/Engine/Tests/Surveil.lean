import Mtg.Engine.Fixture

/-!
# `TriggerResolution.surveil`

How many cards is a `NumberSelector`. `.fixed` surveils that many.
Every other count is read the same way. Surveil 0 still logs.
-/

namespace Mtg.Engine.SurveilTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

def step (r : TriggeredAbility.TriggerResolution) : Game :=
  afterDraw.applyTriggeredAbility caster (.onEnterDraw 1) none
    (resolutionOverride := some r)

/- Surveil 1 looks at one card. -/
#guard
  let g := step (.surveil (.fixed 1))
  match g.pending with
  | .surveil p n _ => p == caster && n == 1
  | _ => false

/- A count of other creatures is surveilled. Zero creatures still surveils 0. -/
#guard
  let g := step (.surveil .perOtherCreature)
  g.pending == afterDraw.pending && logContains g "surveils 0"

#guard
  let bear : CardDef := {
    name := "Surveil Bear"
    types := #[.creature]
    power := some 2
    toughness := some 2
  }
  let g0 := addPermanent afterDraw bear caster caster
  let g := g0.applyTriggeredAbility caster (.onEnterDraw 1) none
    (resolutionOverride := some (.surveil .perOtherCreature))
  match g.pending with
  | .surveil p n _ => p == caster && n == 1
  | _ => false

#guard TriggeredAbility.resolution (.onEnterSurveil 2) == .surveil (.fixed 2)

#guard (SharedTrigger.timing (.surveil 1)).resolution == .surveil (.fixed 1)

#guard TriggeredAbility.resolutionPhrase
    { resolution := .surveil (.fixed 2) } == "surveil 2"

#guard TriggeredAbility.resolutionPhrase
    { resolution := .surveil .perOtherCreature } == "surveil"

end Mtg.Engine.SurveilTests
