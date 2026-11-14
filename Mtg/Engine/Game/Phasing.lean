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

/-- Whether departed player `dep`'s next turn would have begun in `g.events`
strictly after event index `sinceIdx`, folding turn-order, extra-turn, and
shared-turn state from `g.events` (CR 500.7 / 702.26m,n / 800.4 / 805.4). -/
private def departedNextTurnWouldHaveBegunSince (g : Game) (dep : PlayerId)
    (sinceIdx : Nat) : Bool := Id.run do
  let n := g.players.size
  if n == 0 then return false
  let hasLeaveEvent (p : PlayerId) : Bool :=
    g.events.any fun ev =>
      match ev.change with
      | .rules (.player (.lost q ..))
      | .rules (.player (.leftGame q)) => q == p
      | _ => false
  let mut alive : Array Bool := Array.ofFn (n := n) fun ⟨k, _⟩ =>
    let pk : PlayerId := ⟨k⟩
    g.stillInGame pk || hasLeaveEvent pk
  let initAp : PlayerId := Id.run do
    for i in [0 : min (sinceIdx + 1) g.events.size] do
      match g.events[i]!.change with
      | .engine (.startingPlayer v) => return v
      | .rules (.turn (.turnBegan p _)) => return p
      | .rules (.turn (.stepBegan _ ap)) => return ap
      | .rules (.turn (.turnEnded ap)) => return ap
      | _ => pure ()
    for ev in g.events do
      match ev.change with
      | .engine (.startingPlayer v) => return v
      | .rules (.turn (.stepBegan _ ap)) => return ap
      | .rules (.turn (.turnEnded ap)) => return ap
      | .rules (.turn (.turnBegan p _)) =>
        return if g.startingPlayer.idx < n then g.startingPlayer else p
      | _ => pure ()
    return if g.activePlayer.idx < n then g.activePlayer else ⟨0⟩
  let mut activePlayer : PlayerId := initAp
  let mut extraTurns : Array PlayerId := #[]
  let mut seats : Array PlayerId := #[initAp]
  let mut seatsExtra : Bool := false
  let isAlive (al : Array Bool) (q : PlayerId) : Bool :=
    q.idx < n && al[q.idx]!
  let isFinalSeat (ap : PlayerId) (al : Array Bool) (stSeats : Array PlayerId) : Bool := Id.run do
    for k in [1:n+1] do
      let q : PlayerId := ⟨(ap.idx + k) % n⟩
      if isAlive al q then
        return !(g.areTeammates ap q && !stSeats.contains q)
    return true
  for idx in [0:g.events.size] do
    match g.events[idx]!.change with
    | .engine (.addPlayer pl) =>
      if pl.id.idx < n then
        alive := alive.set! pl.id.idx (!pl.lost && !pl.leftTheGame)
    | .engine (.startingPlayer v) =>
      activePlayer := v
      seats := #[v]
      seatsExtra := false
    | .rules (.player (.lost q ..))
    | .rules (.player (.leftGame q)) =>
      if q.idx < n then
        alive := alive.set! q.idx false
    | .rules (.turn (.stepBegan _ ap))
    | .rules (.turn (.turnEnded ap)) =>
      activePlayer := ap
      if seats.isEmpty || (!seats.contains ap && !g.areTeammates seats[0]! ap) then
        seats := #[ap]
    | .rules (.turn (.extraTurnAdded player _)) =>
      let team := g.teamMembers player
      let inProgress :=
        if seatsExtra && !seats.isEmpty then
          Id.run do
            let mut seen := seats
            let mut cnt := 0
            let mut keepGoing := true
            for q in extraTurns do
              if keepGoing && g.areTeammates seats[0]! q && !seen.contains q then
                seen := seen.push q
                cnt := cnt + 1
              else
                keepGoing := false
            return cnt
        else 0
      extraTurns :=
        extraTurns.extract 0 inProgress ++ team ++
          extraTurns.extract inProgress extraTurns.size
    | .rules (.turn (.turnBegan player extra)) =>
      let sameShared :=
        extra == seatsExtra && !seats.isEmpty &&
          g.areTeammates seats[0]! player && !seats.contains player
      if idx > sinceIdx then
        let finalSeat := isFinalSeat activePlayer alive seats
        let midRegularShared := !seatsExtra && !finalSeat
        let skipped : Array PlayerId := Id.run do
          let mut depSkipped : Array PlayerId := #[]
          if !midRegularShared then
            let mut skipIdx := 0
            while skipIdx < extraTurns.size && !isAlive alive extraTurns[skipIdx]! do
              let d := extraTurns[skipIdx]!
              let extraSeatEnding :=
                seatsExtra && !sameShared &&
                  seats.any (fun s => s == d || g.areTeammates s d)
              if !(g.teamMembers d).any (isAlive alive) && !extraSeatEnding &&
                  !depSkipped.contains d then
                depSkipped := depSkipped.push d
              skipIdx := skipIdx + 1
            if (extraTurns.extract skipIdx extraTurns.size)[0]?.isSome then
              return depSkipped
          for k in [1:n+1] do
            let q : PlayerId := ⟨(activePlayer.idx + k) % n⟩
            if !isAlive alive q then
              let endingCurrentShared :=
                !sameShared && seats.any (fun s => s == q || g.areTeammates s q)
              if !(g.teamMembers q).any (isAlive alive) && !endingCurrentShared &&
                  !depSkipped.contains q then
                depSkipped := depSkipped.push q
            else
              return depSkipped
          return depSkipped
        let depSharedTurnBegan :=
          !sameShared && (player == dep || g.areTeammates player dep)
        if skipped.contains dep || depSharedTurnBegan then
          return true
      let dropLost (xs : Array PlayerId) : Array PlayerId :=
        (xs.toList.dropWhile (fun q => !isAlive alive q)).toArray
      let restExtra :=
        if extra then
          let trimmed := dropLost extraTurns
          if trimmed[0]? == some player then trimmed.extract 1 trimmed.size
          else trimmed
        else if sameShared then
          extraTurns
        else
          dropLost extraTurns
      extraTurns := restExtra
      activePlayer := player
      if sameShared then
        seats := seats.push player
      else
        seats := #[player]
        seatsExtra := extra
    | _ => pure ()
  return false

/-- Phase in every phased-out permanent `p` controlled when it phased out, plus
any phased-out permanent whose phase-out controller has left the game and whose
next turn would have begun since it phased out (CR 502.1 / 702.26m,n / 703.4a). -/
def phaseInControlled (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .phaseInOut)
  let phaseOutControllerOf (o : GameObject) : Option PlayerId × Nat := Id.run do
    for rev in [0:g.events.size] do
      let idx := g.events.size - 1 - rev
      match g.events[idx]!.change with
      | .rules (.permanent (.phasedOut eo _)) =>
        if eo.id == some o.id then return (eo.controller, idx)
      | _ => pure ()
    return (g.controllerOf o, 0)
  let targetIds :=
    g.objects.filterMap fun o =>
      if o.zone == .battlefield && o.status.phasedOut && o.status.phasedWith.isNone then
        let (ctrl?, sinceIdx) := phaseOutControllerOf o
        let shouldPhaseIn :=
          ctrl? == some p ||
            match ctrl? with
            | some dep => !g.stillInGame dep && departedNextTurnWouldHaveBegunSince g dep sinceIdx
            | none => false
        if shouldPhaseIn then some o.id else none
      else none
  (g.withBatchCore cause fun g =>
    g.phaseInControlledLoop targetIds (cause := cause)).flushQueuedLinkedExileFwd

end Game
end Mtg.Engine
