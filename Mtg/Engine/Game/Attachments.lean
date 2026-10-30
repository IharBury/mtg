import Mtg.Engine.Game.Tokens

/-!
# Attach and unattach (CR 701.3)

Attaching a source to a host, a token ceasing to exist (CR 111.7),
zone-list bookkeeping, and unattaching from a leaving host.
-/

namespace Mtg.Engine
namespace Game

/-- Attach `src` to `host` (CR 301.5 / 303.4). -/
def attachSourceTo (g : Game) (src host : GameObject)
    (cause : Option EventCause := none) : Game :=
  let src := g.object! src.id
  let effCause := g.resolveOptionalCause cause (fallbackSrc := some src.id) (fallbackCtrl := g.controllerOf src)
  let g := g.record (GameEvent.attached g.turnNumber src.id host.id (cause := effCause))
  g.logMsg s!"{src.name} attaches to {host.name}"

/-- Remove an id from a zone list. -/
def stripId (ids : Array ObjectId) (id : ObjectId) : Array ObjectId :=
  ids.filter (fun x => x != id)

/-- An object ceases to exist (CR 608.2m / 111.8 / 704.5d / 704.5e).
The object is deleted and its id is removed from the zone it occupied, so a
graveyard, hand, library, or stack keeps nothing of it. -/
def ceaseToExist (g : Game) (id : ObjectId) (cause : Option EventCause := none) : Game :=
  let effCause :=
    g.resolveOptionalCause cause (fallbackSrc := some id)
      (defaultCause := some (.gameRule .leavingZone))
  match g.findObject? id with
  | some old =>
    let snap := g.snapshot old
    let g := g.record (GameEvent.ceasedToExist g.turnNumber snap (cause := effCause))
    let expCause := cause.orElse (fun _ => some (.gameRule .leavingZone))
    let g := g.expireEffectsOnLeavingObject old (cause := expCause)
    if old.zone == .battlefield then g.expireWhileSourceEffects id (cause := expCause) else g
  | none =>
    g.record (GameEvent.ceasedToExist g.turnNumber { id := some id } (cause := effCause))

/-- Move an object to a new zone, assigning a new object identity (CR 400.7).
Auras and Equipment attached to a permanent that leaves the battlefield
become unattached and remain on the battlefield (CR 701.3d). -/
def unattachFrom (g : Game) (hostId : ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.attachedTo == some hostId then
        g := g.record (GameEvent.unattached g.turnNumber o.asEvent hostId
          (cause := .gameRule .unattachOnHostLeave))
        g := g.logMsg s!"{o.name} becomes unattached"
    return g

end Game
end Mtg.Engine
