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

/-- Earliest event index in `g.events` belonging to the batch recorded at `idx`
(stepping backward across `.engine _` changes and any `.rules _` event carrying
the same `some bid` batch tag, CR 702.26b,g–h / 800.4c). -/
def phaseOutBatchStartIdx (g : Game) (idx : Nat) : Nat :=
  if idx ≥ g.events.size then g.events.size
  else
    match g.events[idx]!.batch with
    | none => idx
    | some bid => Id.run do
      let mut preBatchIdx := idx
      let mut j := idx
      while j > 0 do
        let evPrev := g.events[j - 1]!
        match evPrev.change with
        | .engine _ =>
          j := j - 1
        | .rules _ =>
          if evPrev.batch != some bid then
            break
          preBatchIdx := j - 1
          j := j - 1
      return preBatchIdx

/-- Phase `o` out, along with Auras, Equipment, and Fortifications attached to it.
Does not trigger leaves-the-battlefield abilities (CR 702.26b / 702.26d / 702.26g). -/
def phaseOut (g : Game) (o : GameObject) (cause : Option EventCause := none)
    (preSnaps : Array (ObjectId × EventObject) := #[])
    (reconcile : Bool := true) : Game :=
  match g.findObject? o.id with
  | none => g
  | some live =>
    if !live.isOnBattlefield then g
    else
      let preSnapOf? (oid : ObjectId) : Option EventObject :=
        preSnaps.findSome? (fun (sid, s) => if sid == oid then some s else none)
      let snapWithStatus (g0 : Game) (cur : GameObject) : EventObject :=
        match preSnapOf? cur.id with
        | some ps =>
          { ps with
            zone := cur.zone
            tapped := cur.status.tapped
            attacking := cur.status.attacking
            attackingTarget := cur.status.attackingTarget
            blocking := !cur.status.blocking.isEmpty
            blockingIds := cur.status.blocking
            phasedOut := cur.status.phasedOut
            faceDown := cur.status.faceDown
            transformed := cur.status.transformed
            attachedTo := cur.attachedTo
            counters := cur.status.toCounterBag }
        | none => g0.snapshot cur
      let fallbackCtrl :=
        (preSnapOf? live.id).bind (·.controller) |>.orElse (fun _ => g.controllerOf live)
      let batchCause :=
        g.resolveOptionalCause cause (fallbackCtrl := fallbackCtrl)
          (defaultCause := .turnBased .phaseInOut)
      let runBody (g : Game) : Game :=
        let pre := g
        let stepCause (g : Game) : EventCause :=
          g.resolveOptionalCause cause (fallbackCtrl := fallbackCtrl)
            (defaultCause := .turnBased .phaseInOut)
        let pairs := g.indirectPhaseOutPairs live.id
        let g := g.removeFromCombat live (cause := some (stepCause g))
        let o := g.object! live.id
        let oName := (preSnapOf? o.id).map (·.name) |>.getD (g.name o)
        let g := g.record (GameEvent.phasedOut g.turnNumber (snapWithStatus g o) false (cause := stepCause g))
        let g := g.logMsg s!"{oName} phases out"
        let g :=
          pairs.foldl (fun acc (attId, hostId) =>
            match acc.findObject? attId with
            | none => acc
            | some att =>
              if !att.isOnBattlefield then acc
              else
                let hostName :=
                  (preSnapOf? hostId).map (·.name) |>.getD
                    ((acc.findObject? hostId).map acc.name |>.getD oName)
                let acc := acc.removeFromCombat att (cause := some (stepCause acc))
                let att := acc.object! att.id
                let attName := (preSnapOf? att.id).map (·.name) |>.getD (acc.name att)
                acc.record (GameEvent.phasedOut acc.turnNumber (snapWithStatus acc att) true (cause := stepCause acc))
                  |>.logMsg s!"{attName} phases out attached to {hostName}") g
        if reconcile then
          reconcileControlAfterTransitionFwd pre g (cause := some (stepCause g))
        else g
      if reconcile then
        (g.withBatchCore (some batchCause) runBody).flushQueuedLinkedExileFwd
      else
        g.withBatchCore (some batchCause) runBody

/-- Continue phasing out `remainingIds` sequentially inside the enclosing
simultaneous phase-out batch, pausing and chaining `.phaseOutPermanentsLoop` if
a CR 616.1 / 800.4c replacement or legend choice opens (CR 702.26g–h). -/
def phaseOutPermanentsLoop (g : Game) (remainingIds : Array ObjectId)
    (cause : Option EventCause := none)
    (preSnaps : Array (ObjectId × EventObject) := #[]) : Game := Id.run do
  let entryEvLen := g.events.size
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    if let some o := g.findObject? id then
      if o.isOnBattlefield then
        g := g.phaseOut o (cause := cause) (preSnaps := preSnaps) (reconcile := false)
        let paused :=
          match g.pending with
          | .chooseReplacement .. | .chooseLegend .. => true
          | _ => false
        if paused then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement (.phaseOutPermanentsLoop rem cause preSnaps)
          return g
  let preBatchIdx? : Option Nat :=
    match g.currentBatch with
    | some (bid, _) =>
      Id.run do
        for rev in [0:g.events.size] do
          let idx := g.events.size - 1 - rev
          if g.events[idx]!.batch == some bid then
            return some (g.phaseOutBatchStartIdx idx)
        return none
    | none =>
      if entryEvLen < g.events.size then some entryEvLen else none
  if let some preBatchIdx := preBatchIdx? then
    let pre := g.mkHistoricalGameAt preBatchIdx
    let stepCause := g.resolveOptionalCause cause (defaultCause := .turnBased .phaseInOut)
    g := reconcileControlAfterTransitionFwd pre g (cause := some stepCause)
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
    let preSnaps : Array (ObjectId × EventObject) :=
      g.battlefield.map (fun obj => (obj.id, g.snapshot obj))
    let withDepth := live.mapIdx (fun idx o => (g.attachmentDepth o, idx, o))
    let sorted := (withDepth.qsort (fun (d1, i1, _) (d2, i2, _) =>
      d1 < d2 || (d1 == d2 && i1 < i2))).map (fun (_, _, o) => o)
    let sortedIds := sorted.map (·.id)
    let batchCause :=
      g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf sorted[0]!)
        (defaultCause := .turnBased .phaseInOut)
    (g.withBatchCore (some batchCause) fun g =>
      g.phaseOutPermanentsLoop sortedIds (cause := cause) (preSnaps := preSnaps)).flushQueuedLinkedExileFwd

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
strictly after event index `sinceIdx?` (`none` when phased out prior to `g.events[0]`),
folding turn-order, extra-turn, and shared-turn state from `g.events`
(CR 500.7 / 702.26m,n / 800.4 / 805.4). -/
private def departedNextTurnWouldHaveBegunSince (g : Game) (dep : PlayerId)
    (sinceIdx? : Option Nat) : Bool := Id.run do
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
  let (initAp, initSeats, initSeatsExtra) : PlayerId × Array PlayerId × Bool := Id.run do
    let mut aliveScan := alive
    for ev in g.events do
      match ev.change with
      | .engine (.addPlayer pl) =>
        if pl.id.idx < n then
          aliveScan := aliveScan.set! pl.id.idx (!pl.lost && !pl.leftTheGame)
      | .rules (.player (.lost q ..))
      | .rules (.player (.leftGame q)) =>
        if q.idx < n then
          aliveScan := aliveScan.set! q.idx false
      | .engine (.startingPlayer v) =>
        return (v, #[v], false)
      | .rules (.turn (.stepBegan _ ap))
      | .rules (.turn (.turnEnded ap)) =>
        let team := g.teamMembers ap
        let apPos := (team.findIdx? (· == ap)).getD 0
        let seats0 := team.extract 0 (apPos + 1)
        let initSeats := if seats0.isEmpty then #[ap] else seats0
        let isExtra := g.inferPreLogTurnIsExtra ap ev.turn
        return (ap, initSeats, isExtra)
      | .rules (.turn (.turnBegan p extra)) =>
        let mut prev? : Option PlayerId := none
        for k in [1 : n + 1] do
          let q : PlayerId := ⟨(p.idx + n - k) % n⟩
          if q.idx < n && aliveScan[q.idx]! then
            prev? := some q
            break
        let prev := prev?.getD (if g.startingPlayer.idx < n then g.startingPlayer else p)
        let team := g.teamMembers p
        let sameSharedPrev :=
          g.areTeammates prev p &&
            match team.findIdx? (· == prev), team.findIdx? (· == p) with
            | some ia, some ib => ia < ib
            | _, _ => false
        let prevPos := (team.findIdx? (· == prev)).getD 0
        let prevSeats :=
          if sameSharedPrev then
            let s0 := team.extract 0 (prevPos + 1)
            if s0.isEmpty then #[prev] else s0
          else #[prev]
        return (prev, prevSeats, if sameSharedPrev then extra else g.hasPreLogPowerUpsForbidden)
      | _ => pure ()
    let fallback := if g.activePlayer.idx < n then g.activePlayer else ⟨0⟩
    let fbTeam := g.teamMembers fallback
    let fbPos := (fbTeam.findIdx? (· == fallback)).getD 0
    let fbSeats0 := fbTeam.extract 0 (fbPos + 1)
    let fbSeats := if fbSeats0.isEmpty then #[fallback] else fbSeats0
    return (fallback, fbSeats, g.inferPreLogTurnIsExtra fallback g.turnNumber)
  let teamEndOf (q : PlayerId) : PlayerId :=
    (g.teamMembers q).back? |>.getD q
  let mut activePlayer : PlayerId := initAp
  let mut extraTurns : Array PlayerId := Id.run do
    if g.events.any (fun ev => match ev.change with | .engine (.startingPlayer _) => true | _ => false) then
      return #[]
    let mut qAcc := g.extraTurns
    for rev in [0:g.events.size] do
      let idx := g.events.size - 1 - rev
      match g.events[idx]!.change with
      | .rules (.turn (.turnBegan p true)) =>
        qAcc := #[p] ++ qAcc
      | .rules (.turn (.extraTurnAdded player _)) =>
        let (stSeats, stExtra) := g.currentSharedTurnState (some idx)
        let inProg := g.countInProgressSharedExtraSeats stSeats stExtra qAcc
        let team := g.teamMembers player
        let mut postIdx := inProg
        for m in team do
          if postIdx < qAcc.size && qAcc[postIdx]! == m then
            postIdx := postIdx + 1
        qAcc := qAcc.extract 0 inProg ++ qAcc.extract postIdx qAcc.size
      | _ => pure ()
    if initSeatsExtra then
      let team := g.teamMembers initAp
      let apPos := (team.findIdx? (· == initAp)).getD 0
      let remInProg :=
        (team.extract (apPos + 1) team.size).filter (fun m => m.idx < n && alive[m.idx]!)
      let missingPrefix := remInProg.filter (fun m => !qAcc.contains m)
      qAcc := missingPrefix ++ qAcc
    return qAcc
  let mut seats : Array PlayerId := initSeats
  let mut seatsExtra : Bool := initSeatsExtra
  let initRegSeat : PlayerId :=
    if !initSeatsExtra then initAp
    else if g.startingPlayer.idx < n then g.startingPlayer
    else initAp
  let mut lastRegEnd : PlayerId := teamEndOf initRegSeat
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
      lastRegEnd := teamEndOf v
    | .rules (.player (.lost q ..))
    | .rules (.player (.leftGame q)) =>
      if q.idx < n then
        alive := alive.set! q.idx false
    | .rules (.turn (.stepBegan _ ap))
    | .rules (.turn (.turnEnded ap)) =>
      activePlayer := ap
      if seats.isEmpty || (!seats.contains ap && !g.areTeammates seats[0]! ap) then
        seats := #[ap]
        seatsExtra := false
      else if g.areTeammates seats[0]! ap && !seats.contains ap then
        seats := seats.push ap
      if !seatsExtra then
        lastRegEnd := teamEndOf ap
    | .rules (.turn (.extraTurnAdded player _)) =>
      let team := g.teamMembers player
      let inProgress := g.countInProgressSharedExtraSeats seats seatsExtra extraTurns
      extraTurns :=
        extraTurns.extract 0 inProgress ++ team ++
          extraTurns.extract inProgress extraTurns.size
    | .rules (.turn (.turnBegan player extra)) =>
      let sameShared :=
        extra == seatsExtra && !seats.isEmpty &&
          g.areTeammates seats[0]! player && !seats.contains player
      if sinceIdx?.all (idx > ·) then
        let finalSeat := isFinalSeat activePlayer alive seats
        let midRegularShared := !seatsExtra && !finalSeat
        let inProgressExtraSeats := g.countInProgressSharedExtraSeats seats seatsExtra extraTurns
        let skipped : Array PlayerId := Id.run do
          let mut depSkipped : Array PlayerId := #[]
          if !midRegularShared then
            let mut skipIdx := 0
            while skipIdx < extraTurns.size && !isAlive alive extraTurns[skipIdx]! do
              let d := extraTurns[skipIdx]!
              let extraSeatEnding :=
                seatsExtra && !sameShared && skipIdx < inProgressExtraSeats
              if !(g.teamMembers d).any (isAlive alive) && !extraSeatEnding &&
                  !depSkipped.contains d then
                depSkipped := depSkipped.push d
              skipIdx := skipIdx + 1
            if (extraTurns.extract skipIdx extraTurns.size)[0]?.isSome then
              return depSkipped
          if !extra && !sameShared then
            let anchor : PlayerId := if seatsExtra then lastRegEnd else activePlayer
            for k in [1:n+1] do
              let q : PlayerId := ⟨(anchor.idx + k) % n⟩
              if !isAlive alive q then
                let endingCurrentRegularShared :=
                  !seatsExtra && !sameShared && seats.any (fun s => s == q || g.areTeammates s q)
                if !(g.teamMembers q).any (isAlive alive) && !endingCurrentRegularShared &&
                    !depSkipped.contains q then
                  depSkipped := depSkipped.push q
              else
                return depSkipped
          return depSkipped
        let depSharedTurnBegan :=
          !sameShared && (player == dep || g.areTeammates player dep)
        if skipped.any (fun q => q == dep || g.areTeammates q dep) || depSharedTurnBegan then
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
      if !extra then
        lastRegEnd := teamEndOf player
    | _ => pure ()
  return false

/-- Phase in every phased-out permanent `p` controlled when it phased out, plus
any phased-out permanent whose phase-out controller has left the game and whose
next turn would have begun since it phased out (CR 502.1 / 702.26m,n / 703.4a). -/
def phaseInControlled (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .phaseInOut)
  let fallbackCtrlOf (o : GameObject) : Option PlayerId :=
    (g.controllerOf o).orElse (fun _ =>
      some ((o.defaultController.orElse (fun _ => o.controller)).getD o.owner))
  let phaseOutControllerOf (o : GameObject) : Option PlayerId × Option Nat := Id.run do
    for rev in [0:g.events.size] do
      let idx := g.events.size - 1 - rev
      match g.events[idx]!.change with
      | .rules (.permanent (.phasedOut eo _)) =>
        if eo.id == some o.id then
          let preBatchIdx := g.phaseOutBatchStartIdx idx
          return (g.controllerOfAt o preBatchIdx <|> eo.controller <|> fallbackCtrlOf o, some idx)
      | .engine (.materializeObject obj _) =>
        if obj.id == o.id && obj.zone == .battlefield && obj.status.phasedOut &&
            !g.objectWasPhasedOutAt o idx then
          let matCtrl :=
            (g.controllerOfAt o (idx + 1)).orElse (fun _ =>
              some ((obj.defaultController.orElse (fun _ => obj.controller)).getD obj.owner))
          return (matCtrl, some idx)
      | .rules (.zone (.moved before after _ toZone ..)) =>
        if after.id == some o.id && toZone == .battlefield && after.phasedOut &&
            (before.id != some o.id || !g.objectWasPhasedOutAt o idx) then
          return (g.controllerOfAt o (idx + 1) <|> after.controller <|> fallbackCtrlOf o, some idx)
      | .rules (.zone (.created eo c)) =>
        if eo.id == some o.id && eo.zone == .battlefield && eo.phasedOut then
          return (g.controllerOfAt o (idx + 1) <|> eo.controller <|> some c, some idx)
      | _ => pure ()
    return (g.controllerOfAt o 0 <|> fallbackCtrlOf o, none)
  let targetIds :=
    g.objects.filterMap fun o =>
      if o.zone == .battlefield && o.status.phasedOut && o.status.phasedWith.isNone then
        let (ctrl?, sinceIdx?) := phaseOutControllerOf o
        let shouldPhaseIn :=
          ctrl? == some p ||
            match ctrl? with
            | some dep => !g.stillInGame dep && departedNextTurnWouldHaveBegunSince g dep sinceIdx?
            | none => false
        if shouldPhaseIn then some o.id else none
      else none
  (g.withBatchCore cause fun g =>
    g.phaseInControlledLoop targetIds (cause := cause)).flushQueuedLinkedExileFwd

end Game
end Mtg.Engine
