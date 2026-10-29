import Mtg.Engine.Game.Designations

/-!
# Attachments in play and phasing (CR 702.26)

Attachment queries, removing a creature from combat (CR 506.4), and
phasing out and in, including phasing attachments with their host.
-/

namespace Mtg.Engine
namespace Game

/-- Remove `o` from combat (CR 506.4). -/
def removeFromCombat (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if o.status.attacking || !o.status.blocking.isEmpty || o.status.blocked ||
      g.objects.any (fun x => x.status.blocking.any (· == o.id)) then
    g.record (GameEvent.removedFromCombat g.turnNumber (g.snapshot o) (cause := cause))
  else g

/-- Phase `o` out, along with Auras and Equipment attached to it. Does not
trigger leaves-the-battlefield abilities (CR 702.26b / 702.26d / 702.26g). -/
def phaseOut (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if o.status.phasedOut || o.zone != .battlefield then g
  else
    let cause :=
      cause.orElse (fun _ =>
        g.currentResolvingContext?.map (fun (src, ctrl) =>
          .oneShotEffect (some ⟨g.nextEffectId⟩) src ctrl))
    g.withBatch cause fun g =>
      let g := g.removeFromCombat o (cause := cause)
      let o := g.object! o.id
      let oName := g.name o
      let g := g.expirePrintedStaticEffects o (cause := cause)
      let g := g.record (GameEvent.phasedOut g.turnNumber (g.snapshot o) false (cause := cause))
      let g := g.logMsg s!"{oName} phases out"
      (g.attachmentsOf o).foldl (fun acc att =>
        let att := acc.object! att.id
        let acc := acc.removeFromCombat att (cause := cause)
        let att := acc.object! att.id
        let attName := acc.name att
        let acc := acc.expirePrintedStaticEffects att (cause := cause)
        acc.record (GameEvent.phasedOut acc.turnNumber (acc.snapshot att) true (cause := cause))
          |>.logMsg s!"{attName} phases out attached to {oName}") g

/-- Phase `o` in, along with anything that phased out attached to it.
Counters and “as this enters” choices are kept. Does not trigger enters (CR 702.26c / 702.26g). -/
def phaseIn (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if !o.status.phasedOut then g
  else
    let g := g.record (GameEvent.phasedIn g.turnNumber (g.snapshot o) false (cause := cause))
    let g := g.createPrintedStaticEffects (g.object! o.id)
    let oName := g.name (g.object! o.id)
    let g := g.logMsg s!"{oName} phases in"
    g.objects.foldl (fun acc att =>
      if att.status.phasedOut && att.status.phasedWith == some o.id then
        let acc := acc.record (GameEvent.phasedIn acc.turnNumber (acc.snapshot att) true (cause := cause))
        let acc := acc.createPrintedStaticEffects (acc.object! att.id)
        acc.logMsg s!"{acc.name (acc.object! att.id)} phases in still attached to {oName}"
      else acc) g

/-- Phase in every phased-out permanent `p` controls (CR 502.1 / 703.4a). -/
def phaseInControlled (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .phaseInOut)
  g.objects.foldl (fun acc o =>
    if o.zone == .battlefield && o.status.phasedOut && acc.controlledBy o p &&
        o.status.phasedWith.isNone then
      acc.phaseIn (acc.object! o.id) (cause := cause)
    else acc) g

end Game
end Mtg.Engine
