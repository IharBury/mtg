import Mtg.Engine.Game.PowerToughness

/-!
# Object allocation

Fresh object ids and timestamps, materializing new `GameObject`s, and
putting spells and activated abilities on the stack (CR 405).
-/

namespace Mtg.Engine
namespace Game

/-- Materialize a new object identity and timestamp via `EngineChange.materializeObject`
without emitting `ZoneEvent.created` (CR 103.2 / 114 / 405 / 602.2a). -/
def allocObject (g : Game) (printed : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (sourceId : Option ObjectId := none)
    (attachedTo : Option ObjectId := none)
    (adventurerCard : Option CardDef := none) : Game × GameObject :=
  let id : ObjectId := ⟨g.nextObjectId⟩
  let ts : Nat := g.timestamp + 1
  let obj : GameObject := {
    id, printed, owner, controller, zone, status,
    timestamp := ts,
    abilityEffect, triggeredAbility, sourceId,
    attachedTo := if zone == .battlefield then attachedTo else none,
    adventurerCard,
    defaultController := if zone == .battlefield then controller else none
  }
  let g := g.change (.materializeObject obj)
  (g, g.object! id)

/-- Push a stack entry for an already-allocated object (CR 601.2a / 602.2a / 603.3). -/
def putStackEntry (g : Game) (controller : PlayerId) (objectId : ObjectId)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  g.changes #[
    .pushStack { objectId, controller, targets := #[], delayedTrigger, lastKnownPower, lastKnownToughness },
    .consecutivePasses 0]

/-- Allocate a stack object representing an activated or triggered ability of
`source` (CR 602.2a / 603.3). -/
def allocStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none) : Game × GameObject :=
  g.allocObject
    { name := s!"{source.name}'s ability", types := #[] }
    source.owner .stack (some controller)
    (abilityEffect := abilityEffect) (triggeredAbility := triggeredAbility)
    (sourceId := some source.id)

/-- Allocate a stack ability of `source` and push it onto the stack. -/
def putStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none) : Game × GameObject :=
  let (g, obj) := g.allocStackAbility source controller abilityEffect triggeredAbility
  (g.putStackEntry controller obj.id delayedTrigger lastKnownPower lastKnownToughness, obj)

end Game
end Mtg.Engine
