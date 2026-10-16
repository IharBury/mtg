import Mtg.Engine.Fixture

/-!
# `TriggerResolution.connive`

Who connives is an `ObjectSelector`. The source, the announced target,
and the entering Villain are the printed recipients. Any other selector
connives nothing.
-/

namespace Mtg.Engine.ConniveTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

#guard
  let g := afterDraw.applyTriggeredAbility caster (.onEnterDraw 1) none
    (resolutionOverride := some (.connive .hand))
  g.pending == afterDraw.pending && g.log.size == afterDraw.log.size

#guard (SharedTrigger.timing (.connive (.target .creatureYouControl))).resolution ==
  .connive .target

#guard (SharedTrigger.timing (.connive (.target .creatureYouControl))).targeting.kind ==
  .creatureYouControl

#guard (SharedTrigger.timing .connive).resolution == .connive .source

#guard TriggeredAbility.resolutionPhrase { resolution := .connive .hand } == "connive"

end Mtg.Engine.ConniveTests
