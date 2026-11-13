import Mtg.Engine.Game.Designations

/-!
# Attachments in play and phasing (CR 702.26)

Attachment queries, removing a creature from combat (CR 506.4), and
phasing out and in, including phasing attachments with their host.
-/

namespace Mtg.Engine
namespace Game

/-- Collect phased-in permanents attached to `rootId` (and transitively attached
to those attachments) in breadth-first host-before-attachment order so indirect
phasing preserves each attachment's host (CR 702.26g). -/
private def indirectPhaseOutPairs (g : Game) (rootId : ObjectId) :
    Array (ObjectId × ObjectId) := Id.run do
  let mut res : Array (ObjectId × ObjectId) := #[]
  let mut queue : Array ObjectId := #[rootId]
  let mut seen : Array ObjectId := #[rootId]
  let mut qIdx := 0
  while qIdx < queue.size do
    let hostId := queue[qIdx]!
    qIdx := qIdx + 1
    for att in g.attachmentsOfId hostId do
      if att.isOnBattlefield && !seen.contains att.id then
        seen := seen.push att.id
        res := res.push (att.id, hostId)
        queue := queue.push att.id
  return res

/-- Attachment depth of `o` on `g`'s battlefield (`0` for unattached permanents,
`1 + depth(host)` for attached permanents, bounded by `g.objects.size`), so hosts
are processed before co-phasing attachments (CR 702.26g–h). -/
private def attachmentDepth (g : Game) (o : GameObject) : Nat :=
  let rec go (fuel : Nat) (cur : GameObject) : Nat :=
    match fuel, cur.attachedTo.bind g.findObject? with
    | 0, _ | _, none => 0
    | fuel + 1, some host =>
      if host.zone == .battlefield then 1 + go fuel host else 0
  go g.objects.size o

/-- Phase `o` out, along with Auras, Equipment, and Fortifications attached to it.
Does not trigger leaves-the-battlefield abilities (CR 702.26b / 702.26d / 702.26g). -/
def phaseOut (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  match g.findObject? o.id with
  | none => g
  | some live =>
    if !live.isOnBattlefield then g
    else
      let batchCause :=
        g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf live)
          (defaultCause := .turnBased .phaseInOut)
      (g.withBatchCore (some batchCause) fun g =>
        let pre := g
        let stepCause (g : Game) : EventCause :=
          g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf live)
            (defaultCause := .turnBased .phaseInOut)
        let pairs := g.indirectPhaseOutPairs live.id
        let g := g.removeFromCombat live (cause := some (stepCause g))
        let o := g.object! live.id
        let oName := g.name o
        let g := g.record (GameEvent.phasedOut g.turnNumber (g.snapshot o) false (cause := stepCause g))
        let g := g.logMsg s!"{oName} phases out"
        let g :=
          pairs.foldl (fun acc (attId, hostId) =>
            match acc.findObject? attId with
            | none => acc
            | some att =>
              if !att.isOnBattlefield then acc
              else
                let hostName := (acc.findObject? hostId).map acc.name |>.getD oName
                let acc := acc.removeFromCombat att (cause := some (stepCause acc))
                let att := acc.object! att.id
                let attName := acc.name att
                acc.record (GameEvent.phasedOut acc.turnNumber (acc.snapshot att) true (cause := stepCause acc))
                  |>.logMsg s!"{attName} phases out attached to {hostName}") g
        reconcileControlAfterTransitionFwd pre g (cause := some (stepCause g))).flushQueuedLinkedExileFwd

/-- Continue phasing out `remainingIds` sequentially inside the enclosing
simultaneous phase-out batch, pausing and chaining `.phaseOutPermanentsLoop` if
a CR 616.1 / 800.4c replacement or legend choice opens (CR 702.26g–h). -/
def phaseOutPermanentsLoop (g : Game) (remainingIds : Array ObjectId)
    (cause : Option EventCause := none) : Game := Id.run do
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    if let some o := g.findObject? id then
      if o.isOnBattlefield then
        g := g.phaseOut o (cause := cause)
        let paused :=
          match g.pending with
          | .chooseReplacement .. | .chooseLegend .. => true
          | _ => false
        if paused then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement (.phaseOutPermanentsLoop rem cause)
          return g
  return g

/-- Phase out all currently phased-in battlefield permanents in `targets`
simultaneously as one batch, snapshotting the target set up front and processing
hosts before co-phasing attachments so an attachment that would simultaneously
phase out directly and indirectly just phases out indirectly (CR 702.26g–h). -/
def phaseOutPermanents (g : Game) (targets : Array GameObject)
    (cause : Option EventCause := none) : Game :=
  let live := targets.filter (·.isOnBattlefield)
  if live.isEmpty then g
  else
    let withDepth := live.mapIdx (fun idx o => (g.attachmentDepth o, idx, o))
    let sorted := (withDepth.qsort (fun (d1, i1, _) (d2, i2, _) =>
      d1 < d2 || (d1 == d2 && i1 < i2))).map (fun (_, _, o) => o)
    let sortedIds := sorted.map (·.id)
    let batchCause :=
      g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf sorted[0]!)
        (defaultCause := .turnBased .phaseInOut)
    (g.withBatchCore (some batchCause) fun g =>
      g.phaseOutPermanentsLoop sortedIds (cause := cause)).flushQueuedLinkedExileFwd

/-- Phase `o` in, along with anything that phased out attached to it.
Counters and “as this enters” choices are kept. Does not trigger enters (CR 702.26c / 702.26d / 702.26g). -/
def phaseIn (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  match g.findObject? o.id with
  | none => g
  | some live =>
    if !live.status.phasedOut || live.zone != .battlefield then g
    else
      let resolvedCause :=
        g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf live)
          (defaultCause := .turnBased .phaseInOut)
      (g.withBatchCore (some resolvedCause) fun g =>
        let pre := g
        let g := g.record (GameEvent.phasedIn g.turnNumber (g.snapshot live) false (cause := resolvedCause))
        let oName := g.name (g.object! live.id)
        let g := g.logMsg s!"{oName} phases in"
        let g := Id.run do
          let mut acc := g
          let mut queue : Array ObjectId := #[live.id]
          let mut qIdx := 0
          while qIdx < queue.size do
            let hostId := queue[qIdx]!
            qIdx := qIdx + 1
            let hostName := (acc.findObject? hostId).map acc.name |>.getD oName
            for att in acc.objects do
              if att.zone == .battlefield && att.status.phasedOut &&
                  att.status.phasedWith == some hostId && att.attachedTo == some hostId then
                acc := acc.record (GameEvent.phasedIn acc.turnNumber (acc.snapshot att) true (cause := resolvedCause))
                acc := acc.logMsg s!"{acc.name (acc.object! att.id)} phases in still attached to {hostName}"
                queue := queue.push att.id
          return acc
        reconcileControlAfterTransitionFwd pre g (cause := some resolvedCause)).flushQueuedLinkedExileFwd

/-- Continue phasing in `remainingIds` sequentially inside the enclosing
simultaneous phase-in batch, pausing and chaining `.phaseInControlledLoop` if
a CR 616.1 / 800.4c replacement or legend choice opens (CR 502.1 / 703.4a). -/
def phaseInControlledLoop (g : Game) (remainingIds : Array ObjectId)
    (cause : Option EventCause := none) : Game := Id.run do
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    if let some o := g.findObject? id then
      if o.zone == .battlefield && o.status.phasedOut && o.status.phasedWith.isNone then
        g := g.phaseIn o (cause := cause)
        let paused :=
          match g.pending with
          | .chooseReplacement .. | .chooseLegend .. => true
          | _ => false
        if paused then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement (.phaseInControlledLoop rem cause)
          return g
  return g

/-- Phase in every phased-out permanent `p` controlled when it phased out
(CR 502.1 / 703.4a). -/
def phaseInControlled (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .phaseInOut)
  let phaseOutControllerOf (o : GameObject) : Option PlayerId :=
    match g.events.findSomeRev? (fun ev =>
      match ev.change with
      | .rules (.permanent (.phasedOut eo _)) =>
        if eo.id == some o.id then some eo.controller else none
      | _ => none) with
    | some ctrl? => ctrl?
    | none => g.controllerOf o
  let targetIds :=
    g.objects.filterMap fun o =>
      if o.zone == .battlefield && o.status.phasedOut && o.status.phasedWith.isNone &&
          phaseOutControllerOf o == some p then
        some o.id
      else none
  (g.withBatchCore cause fun g =>
    g.phaseInControlledLoop targetIds (cause := cause)).flushQueuedLinkedExileFwd

end Game
end Mtg.Engine
