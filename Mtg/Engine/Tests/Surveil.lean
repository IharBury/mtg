import Mtg.Engine.Fixture

/-!
# `TriggerResolution.surveil`

How many cards is a `NumberSelector`. `.fixed` surveils that many.
Any other selector surveils nothing.
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
  | .surveil p n => p == caster && n == 1
  | _ => false

/- Any other selector surveils nothing. -/
#guard
  let g := step (.surveil .perOtherCreature)
  g.pending == afterDraw.pending && g.log.size == afterDraw.log.size

#guard TriggeredAbility.resolution (.onEnterSurveil 2) == .surveil (.fixed 2)

#guard (SharedTrigger.timing (.surveil 1)).resolution == .surveil (.fixed 1)

#guard TriggeredAbility.resolutionPhrase
    { resolution := .surveil (.fixed 2) } == "surveil 2"

#guard TriggeredAbility.resolutionPhrase
    { resolution := .surveil .perOtherCreature } == "surveil"

end Mtg.Engine.SurveilTests
