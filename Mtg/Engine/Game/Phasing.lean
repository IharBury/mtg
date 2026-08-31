import Mtg.Engine.Game.Designations

/-!
# Attachments in play and phasing (CR 702.26)

Attachment queries, removing a creature from combat (CR 506.4), and
phasing out and in, including phasing attachments with their host.
-/

namespace Mtg.Engine
namespace Game

/-- Permanents currently attached to `hostId`. -/
def attachmentsOfId (g : Game) (hostId : ObjectId) : Array GameObject :=
  g.battlefield.filter (fun o => o.attachedTo == some hostId)

/-- Attachments that should phase out or in with `host`. -/
def attachmentsOf (g : Game) (host : GameObject) : Array GameObject :=
  g.attachmentsOfId host.id

/-- Remove `o` from combat (CR 506.4). -/
def removeFromCombat (g : Game) (o : GameObject) : Game :=
  let g := g.setObject { o with status := { o.status with
    attacking := false
    attackingWhom := none
    blocking := #[] } }
  g.objects.foldl (fun acc x =>
    if x.status.blocking.any (· == o.id) then
      acc.setObject { x with status := { x.status with
        blocking := x.status.blocking.filter (· != o.id) } }
    else acc) g

/-- Phase `o` out, along with Auras and Equipment attached to it. Does not
trigger leaves-the-battlefield abilities. -/
def phaseOut (g : Game) (o : GameObject) : Game :=
  if o.status.phasedOut || o.zone != .battlefield then g
  else
    let g := g.removeFromCombat o
    let o := g.object! o.id
    let g := g.setObject { o with status := { o.status with
      phasedOut := true, phasedWith := none } }
    let g := g.logMsg s!"{o.name} phases out"
    (g.attachmentsOf o).foldl (fun acc att =>
      let att := acc.object! att.id
      let acc := acc.removeFromCombat att
      let att := acc.object! att.id
      acc.setObject { att with status := { att.status with
        phasedOut := true, phasedWith := some o.id } }
        |>.logMsg s!"{att.name} phases out attached to {o.name}") g

/-- Phase `o` in, along with anything that phased out attached to it.
Counters and “as this enters” choices are kept. Does not trigger enters. -/
def phaseIn (g : Game) (o : GameObject) : Game :=
  if !o.status.phasedOut then g
  else
    let g := g.setObject { o with status := { o.status with
      phasedOut := false, phasedWith := none, summoningSick := false } }
    let g := g.logMsg s!"{o.name} phases in"
    g.objects.foldl (fun acc att =>
      if att.status.phasedOut && att.status.phasedWith == some o.id then
        acc.setObject { att with status := { att.status with
          phasedOut := false, summoningSick := false } }
          |>.logMsg s!"{att.name} phases in still attached to {o.name}"
      else acc) g

/-- Phase in every phased-out permanent `p` controls (CR 502.1). -/
def phaseInControlled (g : Game) (p : PlayerId) : Game :=
  g.objects.foldl (fun acc o =>
    if o.zone == .battlefield && o.status.phasedOut && o.controlledBy p &&
        o.status.phasedWith.isNone then
      acc.phaseIn (acc.object! o.id)
    else acc) g

end Game
end Mtg.Engine
