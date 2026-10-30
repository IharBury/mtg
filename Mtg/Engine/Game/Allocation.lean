import Mtg.Engine.Game.PowerToughness

/-!
# Object allocation

Fresh object ids and timestamps, materializing new `GameObject`s, and
putting spells and activated abilities on the stack (CR 405).
-/

namespace Mtg.Engine
namespace Game

def allocId (g : Game) : Game × ObjectId :=
  let id : ObjectId := ⟨g.nextObjectId⟩
  (g.change (.nextObjectId (g.nextObjectId + 1)), id)

def bumpTime (g : Game) : Game × Nat :=
  let ts := g.timestamp
  (g.change (.timestamp (ts + 1)), ts)

/-- Allocate a new object identity and timestamp, then put `obj` into the game
through `ZoneEvent.created` (CR 103.2 / 114 / 405 / 602.2a / 603.3). -/
def allocObject (g : Game) (printed : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (sourceId : Option ObjectId := none)
    (attachedTo : Option ObjectId := none)
    (adventurerCard : Option CardDef := none)
    (cause : EventCause := .gameRule .openingHandDraw) : Game × GameObject :=
  let id : ObjectId := ⟨g.nextObjectId⟩
  let obj : GameObject := {
    id, printed, owner, controller, zone, status,
    abilityEffect, triggeredAbility, sourceId,
    attachedTo, adventurerCard,
    defaultController := if zone == .battlefield then controller else none
  }
  let evTurn := if zone == .battlefield then 0 else g.turnNumber
  let createdEv :=
    GameEvent.created evTurn (controller.getD owner) obj.asEvent (cause := cause)
  let g :=
    if zone == .battlefield then
      let batchId : BatchId := (g.currentBatch.map Prod.fst).getD ⟨g.nextBatchId⟩
      (g.applySingleRulesEventInBatch batchId createdEv).1
    else
      g.record createdEv
  let ocs : Array ObjectChange := Id.run do
    let mut ocs : Array ObjectChange := #[]
    if abilityEffect.isSome then ocs := ocs.push (.abilityEffect abilityEffect)
    if triggeredAbility.isSome then ocs := ocs.push (.triggeredAbility triggeredAbility)
    if sourceId.isSome then ocs := ocs.push (.sourceId sourceId)
    if status.chosenOdd.isSome then ocs := ocs.push (.status (.chosenOdd status.chosenOdd))
    if status.chosenCreatureType.isSome then
      ocs := ocs.push (.status (.chosenCreatureType status.chosenCreatureType))
    if status.chosenColor.isSome then ocs := ocs.push (.status (.chosenColor status.chosenColor))
    if status.chosenName.isSome then ocs := ocs.push (.status (.chosenName status.chosenName))
    return ocs
  let g := if ocs.isEmpty then g else g.changeObjects id ocs
  let g := g.createPrintedStaticEffects (g.object! id)
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
  let cause : EventCause :=
    if triggeredAbility.isSome then .gameRule .triggeredAbility else .gameRule .abilityActivated
  g.allocObject
    { name := s!"{source.name}'s ability", types := #[] }
    source.owner .stack (some controller)
    (abilityEffect := abilityEffect) (triggeredAbility := triggeredAbility)
    (sourceId := some source.id) (cause := cause)

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
