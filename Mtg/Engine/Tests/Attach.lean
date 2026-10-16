import Mtg.Engine.Fixture

/-!
# `TriggerResolution.attach`

What is attached, and what it attaches to, are `ObjectSelector`s.
A pair this does not name attaches nothing.
-/

namespace Mtg.Engine.AttachTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

#guard
  let g := afterDraw.applyTriggeredAbility caster (.onEnterDraw 1) none
    (resolutionOverride := some (.attach .source .source))
  g.pending == afterDraw.pending && g.log.size == afterDraw.log.size

#guard (SharedTrigger.timing (.createThenAttach .dwarf)).resolution ==
  .sequence [.createTokens .dwarf (.fixed 1) false, .attach .source .createdToken]

end Mtg.Engine.AttachTests
