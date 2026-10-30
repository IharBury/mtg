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

/- Phase 11: Attaching and re-attaching Equipment records `PermanentEvent.attached`
with the full Layer 1–7 `attachment : EventObject` snapshot and `previous` host. -/
#guard
  let blade : CardDef := {
    name := "Attach Blade"
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  let bearA : CardDef := creature "Attach Bear A" ManaCost.empty #["Bear"] 2 2
  let bearB : CardDef := creature "Attach Bear B" ManaCost.empty #["Bear"] 2 2
  let g0 := addPermanent (addPermanent (addPermanent afterDraw blade caster caster) bearA caster caster) bearB caster caster
  let eqObj := (g0.battlefield.filter (·.name == "Attach Blade"))[0]!
  let hostA := (g0.battlefield.filter (·.name == "Attach Bear A"))[0]!
  let hostB := (g0.battlefield.filter (·.name == "Attach Bear B"))[0]!
  let g1 := g0.applyTriggeredAbility caster (.onEnterAttachThen (.setBasePT 2 2))
    (some eqObj.id) #[Target.permanent hostA.id]
    (resolutionOverride := some (.attach .source .target))
  let g2 := g1.applyTriggeredAbility caster (.onEnterAttachThen (.setBasePT 2 2))
    (some eqObj.id) #[Target.permanent hostB.id]
    (resolutionOverride := some (.attach .source .target))
  let attachedEvents := g2.events.filterMap fun e =>
    match e.change with
    | .rules (.permanent (.attached eo hid prev)) => some (eo, hid, prev)
    | _ => none
  attachedEvents.size == 2 &&
    attachedEvents[0]!.1.id == some eqObj.id &&
    attachedEvents[0]!.1.subtypes.contains .equipment &&
    attachedEvents[0]!.2.1 == hostA.id &&
    attachedEvents[0]!.2.2 == none &&
    attachedEvents[1]!.1.id == some eqObj.id &&
    attachedEvents[1]!.1.subtypes.contains .equipment &&
    attachedEvents[1]!.2.1 == hostB.id &&
    attachedEvents[1]!.2.2 == some hostA.id &&
    (g2.object! eqObj.id).attachedTo == some hostB.id

end Mtg.Engine.AttachTests
