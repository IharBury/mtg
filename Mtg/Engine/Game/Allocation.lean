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
    (adventurerCard : Option CardDef := none)
    (isCommander : Bool := false) : Game × GameObject :=
  let id : ObjectId := ⟨g.nextObjectId⟩
  let ts : Nat := g.timestamp + 1
  let obj : GameObject := {
    id, printed, owner, controller, zone, status,
    timestamp := ts,
    abilityEffect, triggeredAbility, sourceId,
    attachedTo := if zone == .battlefield then attachedTo else none,
    adventurerCard,
    isCommander,
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

/-- The copy of `srcId`'s prepare spell in exile, if any. -/
def preparedCopyOf? (g : Game) (srcId : ObjectId) : Option GameObject :=
  g.objects.find? (fun o =>
    o.zone == .exile && ((g.playPermission o).bind (·.prepareSource)) == some srcId)

/-- Create the exiled copy of `o`'s prepare spell and grant permission to cast
it while `o` remains prepared (ruling 742). -/
def createPreparedCopy (g : Game) (o : GameObject) (face : AdventureFace)
    (cause : Option EventCause := none) : Game :=
  let p := (g.controllerOf o).getD o.owner
  let copyId : ObjectId := ⟨g.nextObjectId⟩
  let copyTs := g.timestamp + 1
  let copyObj : GameObject := {
    id := copyId
    printed := face.toCardDef
    owner := p
    zone := .exile
    timestamp := copyTs
  }
  let resolvedCause := g.resolveOptionalCause cause (fallbackSrc := some o.id) (fallbackCtrl := some p)
  let g := g.record (GameEvent.created g.turnNumber p (g.snapshot copyObj) (cause := resolvedCause))
  g.createEffect (.playPermission copyId {
    player := p
    whileExiled := true
    prepareSource := some o.id }) (cause := some resolvedCause)

/-- Ensure the exiled copy of `o`'s prepare spell exists when `o` enters
already prepared (CR 614.1c, ruling 742). -/
def ensurePreparedCopy (g : Game) (o : GameObject) : Game :=
  if !o.status.prepared || (g.preparedCopyOf? o.id).isSome then g
  else
    match (g.baseCard o).prepareFace with
    | none => g
    | some face =>
      let g := g.createPreparedCopy o face (cause := some (.gameRule .staticAbility))
      g.logMsg s!"{o.name} becomes prepared. A copy of {face.name} is exiled"

end Game
end Mtg.Engine
