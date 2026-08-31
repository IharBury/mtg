import Mtg.Engine.Game.BasePT

/-!
# Object allocation

Fresh object ids and timestamps, materializing new `GameObject`s, and
putting spells and activated abilities on the stack (CR 405).
-/

namespace Mtg.Engine
namespace Game

def allocId (g : Game) : Game × ObjectId :=
  ({ g with nextObjectId := g.nextObjectId + 1 }, ⟨g.nextObjectId⟩)

def bumpTime (g : Game) : Game × Nat :=
  ({ g with timestamp := g.timestamp + 1 }, g.timestamp)

/-- Allocate a new object identity and timestamp, then put `obj` into the game. -/
def allocObject (g : Game) (printed : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (attachedTo : Option ObjectId := none) : Game × GameObject :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id, printed, owner, controller, zone, status, timestamp := ts,
    abilityEffect, triggeredAbility, sourceId, lastKnownPower, lastKnownToughness,
    attachedTo,
    defaultController := if zone == .battlefield then controller else none
  }
  ({ g with objects := g.objects.push obj }, obj)

/-- Push a stack entry for an already-allocated object (CR 601.2a / 602.2a / 603.3). -/
def putStackEntry (g : Game) (controller : PlayerId) (objectId : ObjectId) : Game :=
  { g with
    stack := g.stack.push { objectId, controller, targets := #[] }
    consecutivePasses := 0 }

/-- Allocate a stack object representing an activated or triggered ability of
`source` (CR 602.2a / 603.3). -/
def allocStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game × GameObject :=
  g.allocObject
    { name := s!"{source.name}'s ability", types := #[],
      oracleText := source.printed.oracleText }
    source.owner .stack (some controller)
    (abilityEffect := abilityEffect) (triggeredAbility := triggeredAbility)
    (sourceId := some source.id)
    (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)

/-- Allocate a stack ability of `source` and push it onto the stack. -/
def putStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option Effect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game × GameObject :=
  let (g, obj) := g.allocStackAbility source controller abilityEffect triggeredAbility
    lastKnownPower lastKnownToughness
  (g.putStackEntry controller obj.id, obj)

end Game
end Mtg.Engine
