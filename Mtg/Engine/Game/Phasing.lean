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
(scanning forward for the earliest event carrying the same `some bid` batch tag,
even across unbatched replacement prompts inside a paused batch, CR 702.26b,g–h / 800.4c). -/
def phaseOutBatchStartIdx (g : Game) (idx : Nat) : Nat :=
  if idx ≥ g.events.size then g.events.size
  else
    match g.events[idx]!.batch with
    | none => idx
    | some bid => Id.run do
      for k in [0 : idx + 1] do
        if g.events[k]!.batch == some bid then
          return k
      return idx

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
def phaseIn (g : Game) (o : GameObject) (cause : Option EventCause := none)
    (reconcile : Bool := true) : Game :=
  match g.findObject? o.id with
  | none => g
  | some live =>
    if !live.status.phasedOut || live.zone != .battlefield then g
    else
      let resolvedCause :=
        g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf live)
          (defaultCause := .turnBased .phaseInOut)
      let runBody (g : Game) : Game :=
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
        if reconcile then
          reconcileControlAfterTransitionFwd pre g (cause := some resolvedCause)
        else g
      if reconcile then
        (g.withBatchCore (some resolvedCause) runBody).flushQueuedLinkedExileFwd
      else
        g.withBatchCore (some resolvedCause) runBody

/-- Continue phasing in `remainingIds` sequentially inside the enclosing
simultaneous phase-in batch, pausing and chaining `.phaseInControlledLoop` if
a CR 616.1 / 800.4c replacement or legend choice opens (CR 502.1 / 703.4a). -/
def phaseInControlledLoop (g : Game) (remainingIds : Array ObjectId)
    (cause : Option EventCause := none) (preSnap? : Option Game := none)
    (startEventIdx : Option Nat := none) : Game := Id.run do
  let entryEvLen := g.events.size
  let startIdx := startEventIdx.getD (preSnap?.map (·.events.size) |>.getD entryEvLen)
  let mut g := g
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    if let some o := g.findObject? id then
      if o.zone == .battlefield && o.status.phasedOut && o.status.phasedWith.isNone then
        g := g.phaseIn o (cause := cause) (reconcile := false)
        let paused :=
          match g.pending with
          | .chooseReplacement .. | .chooseLegend .. => true
          | _ => false
        if paused then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          g := g.chainPendingReplacement (.phaseInControlledLoop rem cause (some startIdx))
          return g
  let resolvedPre? : Option Game :=
    if startIdx ≥ g.events.size then none
    else
      match preSnap? with
      | some preSnap => some preSnap
      | none =>
        let preBatchIdx :=
          match g.currentBatch with
          | some (bid, _) =>
            Id.run do
              for k in [0 : g.events.size] do
                if g.events[k]!.batch == some bid then
                  return min k startIdx
              return startIdx
          | none => startIdx
        some (g.mkHistoricalGameAt preBatchIdx)
  if let some preSnap := resolvedPre? then
    let stepCause := g.resolveOptionalCause cause (defaultCause := .turnBased .phaseInOut)
    g := reconcileControlAfterTransitionFwd preSnap g (cause := some stepCause)
  return g

/-- Whether departed player `dep`'s next turn would have begun in `g.events`
strictly after event index `sinceIdx?` (`none` when phased out prior to `g.events[0]`),
folding turn-order, extra-turn, and shared-turn state from `g.events`
(CR 500.7 / 702.26m,n / 800.4 / 805.4). -/
private def departedNextTurnWouldHaveBegunSince (g : Game) (dep : PlayerId)
    (sinceIdx? : Option Nat) : Bool := Id.run do
  let n := g.players.size
  if n == 0 then return false
  let addedMidLog (p : PlayerId) : Bool :=
    g.events.any fun ev =>
      match ev.change with
      | .engine (.addPlayer pl) => pl.id == p
      | _ => false
  let hasLeaveEvent (p : PlayerId) : Bool :=
    g.events.any fun ev =>
      match ev.change with
      | .rules (.player (.lost q ..))
      | .rules (.player (.leftGame q)) => q == p
      | _ => false
  let hasStartingPlayer :=
    g.events.any fun ev =>
      match ev.change with
      | .engine (.startingPlayer _) => true
      | _ => false
  let mut alive : Array Bool := Array.ofFn (n := n) fun ⟨k, _⟩ =>
    let pk : PlayerId := ⟨k⟩
    !addedMidLog pk && (g.stillInGame pk || hasLeaveEvent pk)
  let sameTeam (a b : PlayerId) : Bool := a == b || g.areTeammates a b
  let preLogRegSeat : PlayerId := Id.run do
    let mut aliveScan := alive
    let mut seenTurnBegan := false
    let mut preStepReg? : Option PlayerId := none
    for idx in [0 : g.events.size] do
      let ev := g.events[idx]!
      match ev.change with
      | .engine (.addPlayer pl) =>
        if pl.id.idx < n then
          aliveScan := aliveScan.set! pl.id.idx (!pl.lost && !pl.leftTheGame)
      | .engine (.startingPlayer v) =>
        return v
      | .rules (.player (.lost q ..))
      | .rules (.player (.leftGame q)) =>
        if q.idx < n then
          aliveScan := aliveScan.set! q.idx false
      | .rules (.turn (.stepBegan _ ap))
      | .rules (.turn (.turnEnded ap)) =>
        if !seenTurnBegan && preStepReg?.isNone && !g.inferPreLogTurnIsExtra ap ev.turn then
          preStepReg? := some ap
      | .rules (.turn (.turnBegan q extra)) =>
        let wasFirstTb := !seenTurnBegan
        seenTurnBegan := true
        if !extra then
          if let some ap := preStepReg? then
            return ap
          let sameTurnAsStart := wasFirstTb && (idx == 0 || ev.turn == g.events[0]!.turn)
          let qTeam := g.teamMembers q
          let qPos := (qTeam.findIdx? (· == q)).getD 0
          let earlierAlive :=
            (qTeam.extract 0 qPos).filter fun m =>
              m.idx < n && (aliveScan[m.idx]! || (sameTurnAsStart && alive[m.idx]!))
          if !earlierAlive.isEmpty then
            return earlierAlive.back!
          if wasFirstTb && !hasStartingPlayer && g.startingPlayer.idx < n && ev.turn >= 2 then
            let startSeat := g.startingPlayer
            let startEnd := (g.teamMembers startSeat).back? |>.getD startSeat
            if !sameTeam q startSeat then
              let mut betweenTeams : Array PlayerId := #[]
              for k in [1 : n + 1] do
                let s : PlayerId := ⟨(startEnd.idx + k) % n⟩
                if sameTeam s q then break
                if !sameTeam s startSeat &&
                    (g.teamMembers s).any (fun m => m.idx < n && alive[m.idx]!) &&
                    !betweenTeams.any (sameTeam · s) then
                  betweenTeams := betweenTeams.push s
              if ev.turn <= betweenTeams.size + 3 then
                if betweenTeams.isEmpty then
                  return startSeat
                else if (!g.hasPreLogPowerUpsForbidden && ev.turn == betweenTeams.size + 2) ||
                    ev.turn == betweenTeams.size + 3 then
                  return betweenTeams.back!
          for k in [1 : n + 1] do
            let prev : PlayerId := ⟨(q.idx + n - k) % n⟩
            if prev.idx < n && aliveScan[prev.idx]! && !sameTeam prev q then
              return prev
          let lr := g.lastRegularTurnSeat
          return if lr.idx < n then lr else q
      | _ => pure ()
    if let some ap := preStepReg? then
      return ap
    let lr := g.lastRegularTurnSeat
    return if lr.idx < n then lr else (if g.activePlayer.idx < n then g.activePlayer else ⟨0⟩)
  let (initAp, initSeats, initSeatsExtra) : PlayerId × Array PlayerId × Bool := Id.run do
    let mut aliveScan := alive
    for idx in [0 : g.events.size] do
      let ev := g.events[idx]!
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
        let sameTurnAsStart := idx == 0 || ev.turn == g.events[0]!.turn
        let team := g.teamMembers p
        let pPos := (team.findIdx? (· == p)).getD 0
        let earlierAlive :=
          (team.extract 0 pPos).filter fun m =>
            m.idx < n && (aliveScan[m.idx]! || (sameTurnAsStart && alive[m.idx]!))
        if !earlierAlive.isEmpty then
          return (earlierAlive.back!, earlierAlive, extra)
        let t0 := if idx > 0 then g.events[0]!.turn else (if ev.turn > 0 then ev.turn - 1 else 0)
        let prevClearEotExtra : Bool :=
          if hasStartingPlayer || extra || t0 < 2 || g.startingPlayer.idx >= n then false
          else Id.run do
            let startSeat := g.startingPlayer
            let startEnd := (g.teamMembers startSeat).back? |>.getD startSeat
            if sameTeam p startSeat then
              let mut otherTeams : Array PlayerId := #[]
              for k in [1 : n + 1] do
                let s : PlayerId := ⟨(startEnd.idx + k) % n⟩
                if !sameTeam s startSeat &&
                    (g.teamMembers s).any (fun m => m.idx < n && alive[m.idx]!) &&
                    !otherTeams.any (sameTeam · s) then
                  otherTeams := otherTeams.push s
              return !otherTeams.isEmpty && t0 == otherTeams.size + 2
            else
              let mut betweenTeams : Array PlayerId := #[]
              for k in [1 : n + 1] do
                let s : PlayerId := ⟨(startEnd.idx + k) % n⟩
                if sameTeam s p then break
                if !sameTeam s startSeat &&
                    (g.teamMembers s).any (fun m => m.idx < n && alive[m.idx]!) &&
                    !betweenTeams.any (sameTeam · s) then
                  betweenTeams := betweenTeams.push s
              return t0 == betweenTeams.size + 2
        let prevIsExtra := g.hasPreLogPowerUpsForbidden || prevClearEotExtra
        if prevIsExtra then
          let nonPSeat? : Option PlayerId := Id.run do
            for k in [1 : n + 1] do
              let cand : PlayerId := ⟨(p.idx + n - k) % n⟩
              if cand.idx < n && !sameTeam cand p &&
                  (aliveScan[cand.idx]! || alive[cand.idx]!) then
                return some cand
            return none
          let chosenSeat := nonPSeat?.getD preLogRegSeat
          let fullTeam := g.teamMembers chosenSeat
          let prevTeamAlive := fullTeam.filter (fun m => m.idx < n && aliveScan[m.idx]!)
          let prevSeats := if prevTeamAlive.isEmpty then #[chosenSeat] else prevTeamAlive
          let prevAp := prevSeats.back? |>.getD chosenSeat
          return (prevAp, prevSeats, true)
        else
          let prevTeam := g.teamMembers preLogRegSeat
          let prevTeamAlive := prevTeam.filter (fun m => m.idx < n && aliveScan[m.idx]!)
          let prevSeats := if prevTeamAlive.isEmpty then #[preLogRegSeat] else prevTeamAlive
          let prevAp := prevSeats.back? |>.getD preLogRegSeat
          return (prevAp, prevSeats, false)
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
    if hasStartingPlayer then
      return #[]
    let initInProg : Array PlayerId := Id.run do
      if !initSeatsExtra then return #[]
      let team := g.teamMembers initAp
      let apPos := (team.findIdx? (· == initAp)).getD 0
      let rawRem := team.extract (apPos + 1) team.size
      if rawRem.isEmpty then return #[]
      let mut aliveAtTb := alive
      let mut firstTb? : Option (PlayerId × Bool) := none
      for ev in g.events do
        if firstTb?.isNone then
          match ev.change with
          | .engine (.addPlayer pl) =>
            if pl.id.idx < n then
              aliveAtTb := aliveAtTb.set! pl.id.idx (!pl.lost && !pl.leftTheGame)
          | .rules (.player (.lost q ..))
          | .rules (.player (.leftGame q)) =>
            if q.idx < n then
              aliveAtTb := aliveAtTb.set! q.idx false
          | .rules (.turn (.turnBegan p extra)) =>
            firstTb? := some (p, extra)
          | _ => pure ()
      match firstTb? with
      | none =>
        let addedCount (m : PlayerId) : Nat :=
          g.events.foldl (fun acc ev =>
            match ev.change with
            | .rules (.turn (.extraTurnAdded player _)) =>
              if (g.teamMembers player).contains m then acc + 1 else acc
            | _ => acc) 0
        return rawRem.filter fun m =>
          (g.extraTurns.filter (· == m)).size > addedCount m
      | some (p0, extra0) =>
        let p0Pos? := rawRem.findIdx? (· == p0)
        return rawRem.filter fun m =>
          let mPos := (rawRem.findIdx? (· == m)).getD 0
          if extra0 && sameTeam initAp p0 then
            match p0Pos? with
            | some p0Pos =>
              if mPos < p0Pos then !(m.idx < n && aliveAtTb[m.idx]!)
              else true
            | none => !(m.idx < n && aliveAtTb[m.idx]!)
          else
            !(m.idx < n && aliveAtTb[m.idx]!)
    let mut simSeats := initSeats
    let mut simExtra := initSeatsExtra
    let mut simAlive := alive
    let mut simQ : Array PlayerId := initInProg
    let mut preLogConsumed : Array PlayerId := #[]
    for ev in g.events do
      match ev.change with
      | .engine (.addPlayer pl) =>
        if pl.id.idx < n then
          simAlive := simAlive.set! pl.id.idx (!pl.lost && !pl.leftTheGame)
      | .rules (.player (.lost q ..))
      | .rules (.player (.leftGame q)) =>
        if q.idx < n then
          simAlive := simAlive.set! q.idx false
      | .rules (.turn (.stepBegan _ ap))
      | .rules (.turn (.turnEnded ap)) =>
        if simSeats.isEmpty || (!simSeats.contains ap && !g.areTeammates simSeats[0]! ap) then
          simSeats := #[ap]
          simExtra := false
        else if g.areTeammates simSeats[0]! ap && !simSeats.contains ap then
          simSeats := simSeats.push ap
      | .rules (.turn (.extraTurnAdded player _)) =>
        let inProg := g.countInProgressSharedExtraSeats simSeats simExtra simQ
        let pTeam := g.teamMembers player
        simQ := simQ.extract 0 inProg ++ pTeam ++ simQ.extract inProg simQ.size
      | .rules (.turn (.turnBegan p extra)) =>
        let sameShared :=
          extra == simExtra && !simSeats.isEmpty &&
            g.areTeammates simSeats[0]! p && !simSeats.contains p
        let trimmed := (simQ.toList.dropWhile (fun q => !(q.idx < n && simAlive[q.idx]!))).toArray
        if extra then
          if trimmed[0]? == some p then
            simQ := trimmed.extract 1 trimmed.size
          else
            let pTeam := g.teamMembers p
            let pPos := (pTeam.findIdx? (· == p)).getD 0
            preLogConsumed := preLogConsumed ++ pTeam.extract 0 (pPos + 1)
            simQ := pTeam.extract (pPos + 1) pTeam.size
        else if !sameShared then
          simQ := trimmed
        if sameShared then
          simSeats := simSeats.push p
        else
          simSeats := #[p]
          simExtra := extra
      | _ => pure ()
    let survivingPreLog :=
      if simQ.size < g.extraTurns.size then
        g.extraTurns.extract simQ.size g.extraTurns.size
      else #[]
    return initInProg ++ preLogConsumed ++ survivingPreLog
  let mut seats : Array PlayerId := initSeats
  let mut seatsExtra : Bool := initSeatsExtra
  let initRegSeat : PlayerId :=
    if !initSeatsExtra then initAp
    else preLogRegSeat
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
    g.phaseInControlledLoop targetIds (cause := cause) (preSnap? := some g)).flushQueuedLinkedExileFwd

end Game
end Mtg.Engine
