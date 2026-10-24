import Mtg.Engine.Game.Tokens

/-!
# Attach and unattach (CR 701.3)

Attaching a source to a host, a token ceasing to exist (CR 111.7),
zone-list bookkeeping, and unattaching from a leaving host.
-/

namespace Mtg.Engine
namespace Game

/-- Attach `src` to `host` (CR 301.5 / 303.4). -/
def attachSourceTo (g : Game) (src host : GameObject) : Game :=
  let (g, ts) := g.bumpTime
  let src := g.object! src.id
  let g := g.changeObject src.id (.timestamp ts)
  let g := g.record (GameEvent.attached g.turnNumber src.id host.id)
  g.logMsg s!"{src.name} attaches to {host.name}"

/-- Remove an id from a zone list. -/
def stripId (ids : Array ObjectId) (id : ObjectId) : Array ObjectId :=
  ids.filter (fun x => x != id)

/-- An object ceases to exist (CR 608.2m / 111.8 / 704.5d / 704.5e).
The object is deleted and its id is removed from the zone it occupied, so a
graveyard, hand, library, or stack keeps nothing of it. -/
def ceaseToExist (g : Game) (id : ObjectId) (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | some old =>
    let snap := g.snapshot old
    let g := g.record (GameEvent.ceasedToExist g.turnNumber snap cause)
    let g := g.expireEffectsOnLeavingObject old
    if old.zone == .battlefield then g.expireWhileSourceEffects id else g
  | none =>
    g.record (GameEvent.ceasedToExist g.turnNumber { id := some id } cause)

/-- Move an object to a new zone, assigning a new object identity (CR 400.7).
Auras and Equipment attached to a permanent that leaves the battlefield
become unattached and remain on the battlefield (CR 701.3d). -/
def unattachFrom (g : Game) (hostId : ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.attachedTo == some hostId then
        g := g.record (GameEvent.unattached g.turnNumber o.asEvent hostId
          (cause := some (.gameRule .unattachOnHostLeave)))
        g := g.logMsg s!"{o.name} becomes unattached"
    return g

end Game
end Mtg.Engine
