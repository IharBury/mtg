import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture

/-!
# Unified `PlayerInstr.connive`

Who connives is an `ObjectExpr`. The source, the announced target,
and the entering Villain are the printed recipients. A non-battlefield
selector connives nothing.
-/

namespace Mtg.Engine.ConniveTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

#guard
  let ab := TriggeredAbility.mkTrigger .thisEnters
    { body := .player (.connive (.inZones (.handOf .you) .anyObject)) }
  let g := afterDraw.applyTriggeredAbility caster ab none
  g.pending == afterDraw.pending

#guard Effect.triggerConniveTarget .creatureYouControl ==
  { targets := .creatureYouControl, body := .player (.connive (.target 0)) }

#guard (Effect.triggerConniveTarget .creatureYouControl).targets ==
  .creatureYouControl

#guard Effect.triggerConniveSource.body == .player (.connive .this)

#guard TriggeredAbility.toNotation .onEnterConnive ==
  "When this creature enters, it connives."

#guard TriggeredAbility.toNotation .onCombatTargetYouControlConnives ==
  "At the beginning of combat on your turn, target creature you control connives."

end Mtg.Engine.ConniveTests
