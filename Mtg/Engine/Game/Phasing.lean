import Mtg.Engine.Game.Designations

/-!
# Attachments in play and phasing (CR 702.26)

Attachment queries, removing a creature from combat (CR 506.4), and
phasing out and in, including phasing attachments with their host.
-/

namespace Mtg.Engine
namespace Game

/-- Phase `o` out, along with Auras and Equipment attached to it. Does not
trigger leaves-the-battlefield abilities (CR 702.26b / 702.26d / 702.26g). -/
def phaseOut (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if o.status.phasedOut || o.zone != .battlefield then g
  else
    let batchCause :=
      g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o)
        (defaultCause := .turnBased .phaseInOut)
    g.withBatch (some batchCause) fun g =>
      let pre := g
      let stepCause (g : Game) : EventCause :=
        g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o)
          (defaultCause := .turnBased .phaseInOut)
      let g := g.removeFromCombat o (cause := some (stepCause g))
      let o := g.object! o.id
      let oName := g.name o
      let g := g.record (GameEvent.phasedOut g.turnNumber (g.snapshot o) false (cause := stepCause g))
      let g := g.logMsg s!"{oName} phases out"
      let g :=
        (g.attachmentsOf o).foldl (fun acc att =>
          let att := acc.object! att.id
          let acc := acc.removeFromCombat att (cause := some (stepCause acc))
          let att := acc.object! att.id
          let attName := acc.name att
          acc.record (GameEvent.phasedOut acc.turnNumber (acc.snapshot att) true (cause := stepCause acc))
            |>.logMsg s!"{attName} phases out attached to {oName}") g
      removeFromCombatOnControlChange pre g (cause := some (stepCause g))

/-- Phase `o` in, along with anything that phased out attached to it.
Counters and “as this enters” choices are kept. Does not trigger enters (CR 702.26c / 702.26g). -/
def phaseIn (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if !o.status.phasedOut then g
  else
    let resolvedCause :=
      g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o)
        (defaultCause := .turnBased .phaseInOut)
    g.withBatch (some resolvedCause) fun g =>
      let pre := g
      let g := g.record (GameEvent.phasedIn g.turnNumber (g.snapshot o) false (cause := resolvedCause))
      let oName := g.name (g.object! o.id)
      let g := g.logMsg s!"{oName} phases in"
      let g :=
        g.objects.foldl (fun acc att =>
          if att.status.phasedOut && att.status.phasedWith == some o.id then
            let acc := acc.record (GameEvent.phasedIn acc.turnNumber (acc.snapshot att) true (cause := resolvedCause))
            acc.logMsg s!"{acc.name (acc.object! att.id)} phases in still attached to {oName}"
          else acc) g
      removeFromCombatOnControlChange pre g (cause := some resolvedCause)

/-- Phase in every phased-out permanent `p` controls (CR 502.1 / 703.4a). -/
def phaseInControlled (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .phaseInOut)
  g.withBatch cause fun g =>
    g.objects.foldl (fun acc o =>
      if o.zone == .battlefield && o.status.phasedOut && acc.controlledBy o p &&
          o.status.phasedWith.isNone then
        acc.phaseIn (acc.object! o.id) (cause := cause)
      else acc) g

end Game
end Mtg.Engine
