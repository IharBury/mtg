import Mtg.Engine.Game.Leaving

/-!
# State-based actions (CR 704)

APNAP order (CR 101.4), the legend rule and its choice prompt
(CR 704.5j), and the state-based-action sweep `checkSBA` (CR 704.5).
-/

namespace Mtg.Engine
namespace Game

/-- Alias of `apnapPlayers` (CR 101.4). -/
def apnapOrder (g : Game) : Array PlayerId :=
  g.apnapPlayers

/-- Legendary permanents `p` currently controls. -/
def legendaryPermanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (g.treatedAsLegendary)

/-- All legend-rule groups that need a choice (CR 704.5j / 201.2a): two or
more legendary permanents with the same name controlled by the same player,
taking players in APNAP order. When `onlyIds` is supplied, restricts candidate
permanents to those present at the start of the SBA pass (CR 704.3). -/
def legendRuleGroups (g : Game)
    (onlyIds : Option (Array ObjectId) := none) :
    Array (PlayerId × String × Array ObjectId) :=
  Id.run do
    let mut out : Array (PlayerId × String × Array ObjectId) := #[]
    for p in g.apnapPlayers.filter (fun p => !g.legendRuleOffThisTurn p) do
      let legs := (g.legendaryPermanentsOf p).filter (fun o =>
        match onlyIds with
        | some ids => ids.contains o.id
        | none => true)
      let mut seen : Array String := #[]
      for o in legs do
        let nm := g.name o
        if !seen.contains nm then
          seen := seen.push nm
          let group := legs.filter (fun x => g.name x == nm)
          if group.size ≥ 2 then
            out := out.push (p, nm, group.map (·.id))
    return out

/-- True while a player must choose which legendary permanent to keep. -/
def legendChoicePending? (g : Game) : Bool :=
  match g.pending with
  | .chooseLegend .. => true
  | _ => false

/-- True when `controller` controls a permanent saying planeswalkers they
control aren't put into graveyards for having 0 loyalty (Sanctum Lurker, CR 704.5i). -/
def planeswalkersSurviveZeroLoyalty (g : Game) (controller : Option PlayerId) : Bool :=
  match controller with
  | none => false
  | some p =>
    (g.permanentsOf p).any (fun o =>
      let env : EvalEnv := { controller := p, sourceId := some o.id }
      (g.staticAbilities o).any fun ab =>
        ab.anyRule fun cond? r =>
          match r with
          | .game (.planeswalkersSurviveZeroLoyalty _) =>
            cond?.all (EvalExpr.evalCondition g env)
          | _ => false)

/-- Default legend-rule choice: the copy that entered most recently. -/
def defaultLegendToKeep (g : Game) (ids : Array ObjectId) : ObjectId :=
  ids.foldl (fun best id =>
    match g.findObject? best, g.findObject? id with
    | some a, some b => if b.timestamp ≥ a.timestamp then id else best
    | _, some _ => id
    | _, none => best) (ids[0]!)

/-- Reconstruct the pre-batch board state when `o.id` already existed on the
battlefield at the start of an enclosing simultaneous batch (CR 608.2c / 701.8b). -/
private def preBatchDestroyCheck (g : Game) (o : GameObject) : Game × GameObject :=
  if g.currentBatch.isSome && !g.openBatchObjects.isEmpty then
    let preG : Game :=
      { g with
        objects := g.openBatchObjects
        players := g.openBatchPlayers
        activeEffects := g.openBatchEffects
        stack := g.openBatchStack }
    match preG.findObject? o.id with
    | some preO =>
      if preO.isOnBattlefield then (preG, preO) else (g, o)
    | none => (g, o)
  else (g, o)

/-- Destroy a permanent (CR 701.8). Indestructible permanents aren't destroyed
(CR 702.12b). A shield counter replaces destruction with removing a
shield counter via the CR 616.1 replacement loop (CR 122.1c / 614.6). If it
would die this turn under an exile replacement, `move` sends it to exile instead
of the graveyard (CR 614.1). -/
def destroyPermanent (g : Game) (o : GameObject)
    (cause : Option EventCause := none)
    (preBattlefield : Option (Array GameObject) := none)
    (reason : Option String := none)
    (deferPlayFromExileLogs : Bool := false) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.destroyPermanent o.id cause preBattlefield reason deferPlayFromExileLogs)
  else
  let (checkG, checkO) := g.preBatchDestroyCheck o
  if checkG.hasIndestructible checkO then
    g.logMsg s!"{g.name o} is indestructible and isn't destroyed"
  else
  let ctrl := g.controllerOf o
  let affected := ctrl.getD o.owner
  let mutSpecs : Array ReplacementSpec := Id.run do
    let mut s : Array ReplacementSpec := #[]
    if o.status.shield > 0 then
      s := s.push {
        id := { kind := .shieldCounterDestroy, object := some o.id }
        source := some o.id
        controller := ctrl
        affectedPlayer := affected
        kind := .shieldCounterDestroy o.id
      }
    for (_, eff) in g.activeEffects do
      match eff with
      | .replacement spec d =>
        if g.durationActive d then
          match spec.kind with
          | .shieldCounterDestroy tid =>
            if tid == o.id && o.status.shield > 0 then
              s := s.push { spec with affectedPlayer := affected }
          | _ => pure ()
      | _ => pure ()
    return s
  let candidates := mutSpecs.map (fun s => (ReplacementOrPrevention.replacement s).toCandidate)
  match g.selectNextReplacementStep candidates #[] with
  | .needChoice chooser choices _ =>
    g.promptChooseReplacement chooser choices
      (.destroyPermanent o.id cause preBattlefield reason deferPlayFromExileLogs)
  | .chosen chosen _ =>
    let g := g.consumeReplacementOrder #[chosen.id]
    let cause' := g.wrapReplacedCause chosen.id cause ctrl
    let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := ctrl)
    let oName := g.name o
    let g := g.recordRemoveCounters o.id .shield 1 (byPlayer := ctrl) (noActor := ctrl.isNone)
      (cause := some finalCause) (deferPlayFromExileLogs := deferPlayFromExileLogs)
    g.logMsg s!"A shield counter is removed from {oName} instead of destroying it"
  | .none =>
    g.moveToOwnerGraveyard o (reason.getD s!"{g.name o} is destroyed") (verb := some .destroy)
      (preBattlefield := preBattlefield) (cause := cause)
      (deferPlayFromExileLogs := deferPlayFromExileLogs)

/-- Execute the remaining permanent-removal and unattachment actions of a
single CR 704.3 state-based action pass inside the currently open batch using
conditions captured at the start of the pass (`.dyingCreatures` = dying creatures,
`.planeswalkersAndLegend` = 0-loyalty planeswalkers + legend rule + tokens/copies
outside valid zones, `.finalChapterSagas` = final-chapter Sagas,
`.illegalAttachments` = illegal Auras + illegal Equipment/creature attachments),
chaining `.finishSbaSweep` if a graveyard move pauses on
`Pending.chooseReplacement`. -/
def finishSbaSweep (g : Game) (moves : Array SbaGraveyardMove)
    (preBf : Array GameObject) (stage : SbaSweepStage)
    (pwMoves : Array SbaGraveyardMove := #[])
    (sagaMoves : Array SbaGraveyardMove := #[])
    (tokensOutsideBf : Array ObjectId := #[])
    (copiesOutside : Array ObjectId := #[])
    (illegalAuras : Array ObjectId := #[])
    (illegalEquips : Array (ObjectId × ObjectId) := #[])
    (illegalCreatureAtts : Array (ObjectId × ObjectId) := #[])
    (legendGroups : Array (PlayerId × String × Array ObjectId) := #[])
    (changedIn : Bool := false)
    (deferPlayFromExileLogs : Bool := false) :
    Game × (Bool × Bool) := Id.run do
  let mut g := g
  let mut changed := changedIn
  let isCounterStage := match stage with | .counterAnnihilation _ => true | _ => false
  if let .counterAnnihilation startIdx := stage then
    -- CR 704.5q: +1/+1 and -1/-1 counters on one permanent are removed in pairs.
    for i in [startIdx:preBf.size] do
      let o := preBf[i]!
      match g.findObject? o.id with
      | some curBefore =>
        if curBefore.isOnBattlefield then
          let k := Nat.min curBefore.status.plusOnePlusOne curBefore.status.minusOneMinusOne
          if k > 0 then
            let oName0 := g.name curBefore
            let cause := EventCause.stateBased .counterAnnihilation
            g := g.recordRemoveCountersMulti o.id #[(.plusOnePlusOne, k), (.minusOneMinusOne, k)]
              (noActor := true) (cause := some cause)
              (deferPlayFromExileLogs := deferPlayFromExileLogs)
            let oName :=
              match g.findObject? o.id with
              | some cur => if cur.isOnBattlefield then g.name cur else oName0
              | none => oName0
            g := g.logMsg s!"{k} +1/+1 and -1/-1 counter pair(s) are removed from {oName}"
            changed := true
            if g.sbaPaused then
              return (g.chainPendingReplacement (.finishSbaSweep moves preBf (.counterAnnihilation (i + 1))
                pwMoves sagaMoves tokensOutsideBf copiesOutside illegalAuras
                illegalEquips illegalCreatureAtts legendGroups deferPlayFromExileLogs), (true, true))
      | none => pure ()
  if isCounterStage || stage == .dyingCreatures then
    for i in [0:moves.size] do
      let m := moves[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          if m.verb == some .destroy then
            g := g.destroyPermanent o (cause := some (.stateBased m.sba))
              (preBattlefield := some preBf) (reason := some m.reason)
              (deferPlayFromExileLogs := deferPlayFromExileLogs)
          else
            g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
              (preBattlefield := some preBf)
              (cause := some (.stateBased m.sba))
              (deferPlayFromExileLogs := deferPlayFromExileLogs)
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := moves.extract (i + 1) moves.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .dyingCreatures
              pwMoves sagaMoves tokensOutsideBf copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts legendGroups deferPlayFromExileLogs), (true, true))
      | none => pure ()
    g := g.change .sbaChecked
  if isCounterStage || stage == .dyingCreatures || stage == .planeswalkersAndLegend then
    -- Planeswalkers with 0 loyalty captured at start of pass (CR 704.5i).
    let pwList : Array SbaGraveyardMove :=
      if stage == .planeswalkersAndLegend then moves else pwMoves
    for i in [0:pwList.size] do
      let m := pwList[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := pwList.extract (i + 1) pwList.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .planeswalkersAndLegend
              #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts legendGroups deferPlayFromExileLogs), (true, true))
      | none => pure ()
    -- Legend rule (CR 704.5j): groups captured at the start of the pass before
    -- `playerLost`, CR 704.5q counter annihilation, `dyingCreatures`, and `pwMoves`
    -- (CR 704.3 / 704.8 / 800.4a). Pause so a living controller chooses one to
    -- keep, chaining the rest of this SBA pass so `keepLegend` finishes the pass
    -- in the same batch before Pass 2 runs (CR 704.3 / 603.2c).
    for gi in [0:legendGroups.size] do
      let (p, name, rawIds) := legendGroups[gi]!
      if !(g.player p).leftTheGame then
        let ids := g.validLegendChoiceIds p name rawIds (requireStillInGame := false)
        if ids.size ≥ 2 then
          let restGroups := legendGroups.extract (gi + 1) legendGroups.size
          if g.stillInGame p then
            g := g.change (.pending (.chooseLegend p name ids))
            g := g.logMsg
              s!"{(g.player p).name} chooses which {name} to keep (legend rule, CR 704.5j)"
            g := g.chainPendingReplacement (.finishSbaSweep #[] preBf .planeswalkersAndLegend
              #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts restGroups deferPlayFromExileLogs)
            return (g, (true, true))
          else
            let keptId := g.defaultLegendToKeep ids
            let others := ids.filter (· != keptId)
            if let some kept := g.findObject? keptId then
              g := g.logMsg s!"{(g.player p).name} keeps {g.name kept} (legend rule, CR 704.5j)"
            for oi in [0:others.size] do
              let other := others[oi]!
              match g.findObject? other with
              | some o =>
                if (g.validLegendChoiceIds p name rawIds (requireStillInGame := false)).contains o.id then
                  g := g.moveToOwnerGraveyard o
                    s!"{g.name o} is put into its owner's graveyard (legend rule, CR 704.5j)"
                    (preBattlefield := some preBf)
                    (cause := some (.stateBased .legendRule))
                    (deferPlayFromExileLogs := deferPlayFromExileLogs)
                  changed := true
                  if let .chooseReplacement _ _ := g.pending then
                    let remOthers := others.extract (oi + 1) others.size
                    let tail := PendingReplacement.finishSbaSweep #[] preBf .planeswalkersAndLegend
                      #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
                      illegalEquips illegalCreatureAtts restGroups deferPlayFromExileLogs
                    let cont :=
                      if remOthers.isEmpty then tail
                      else .seq (.moveSimultaneousToGraveyard remOthers (some preBf)
                        (some (.stateBased .legendRule)) deferPlayFromExileLogs) tail
                    return (g.chainPendingReplacement cont, (true, true))
              | none => pure ()
  if isCounterStage || stage == .dyingCreatures || stage == .planeswalkersAndLegend ||
      stage == .tokensOutside then
    -- Tokens in zones other than the battlefield at start of pass cease to exist (CR 704.5d).
    for ti in [0:tokensOutsideBf.size] do
      let tid := tokensOutsideBf[ti]!
      match g.findObject? tid with
      | some o =>
        if o.printed.isToken && o.zone != .battlefield then
          let oName := g.name o
          g := g.ceaseToExist o.id (cause := some (.stateBased .tokenOutsideBattlefield))
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
          g := g.logMsg s!"{oName} ceases to exist (token left the battlefield)"
          changed := true
          if g.sbaPaused then
            let remToks := tokensOutsideBf.extract (ti + 1) tokensOutsideBf.size
            return (g.chainPendingReplacement (.finishSbaSweep #[] preBf .tokensOutside
              #[] sagaMoves remToks copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts #[] deferPlayFromExileLogs), (true, true))
      | none => pure ()
  if isCounterStage || stage == .dyingCreatures || stage == .planeswalkersAndLegend ||
      stage == .tokensOutside || stage == .copiesOutside then
    -- Non-token copies outside stack and battlefield at start of pass cease to exist (CR 704.5e;
    -- FRA ruling 736 exempts a prepared creature's associated spell copy in exile).
    for ci in [0:copiesOutside.size] do
      let cid := copiesOutside[ci]!
      match g.findObject? cid with
      | some o =>
        if o.isCopy && !o.printed.isToken && o.zone != .stack && o.zone != .battlefield &&
            !(o.zone == .exile &&
              (g.playPermissionEntriesOf o.id).any (fun (_, _, perm, _) => perm.prepareSource.isSome)) then
          let oName := g.name o
          g := g.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
          g := g.logMsg s!"{oName} ceases to exist (copy outside stack or battlefield, CR 704.5e)"
          changed := true
          if g.sbaPaused then
            let remCopies := copiesOutside.extract (ci + 1) copiesOutside.size
            return (g.chainPendingReplacement (.finishSbaSweep #[] preBf .copiesOutside
              #[] sagaMoves #[] remCopies illegalAuras
              illegalEquips illegalCreatureAtts #[] deferPlayFromExileLogs), (true, true))
      | none => pure ()
  if stage != .illegalAttachments then
    -- Saga with lore at or past its final chapter and no chapter on the
    -- stack captured at start of pass is sacrificed (CR 714.4 / 704.5s).
    let sagaList : Array SbaGraveyardMove :=
      if stage == .finalChapterSagas then moves else sagaMoves
    for i in [0:sagaList.size] do
      let m := sagaList[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := sagaList.extract (i + 1) sagaList.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .finalChapterSagas
              #[] #[] #[] #[] illegalAuras illegalEquips illegalCreatureAtts #[]
              deferPlayFromExileLogs), (true, true))
      | none => pure ()
  do
    -- Unattached or illegally attached Auras captured at start of pass (CR 704.5m).
    let auraList : Array SbaGraveyardMove :=
      if stage == .illegalAttachments then moves
      else
        illegalAuras.filterMap (fun aid =>
          match g.findObject? aid with
          | some o =>
            if o.isOnBattlefield then
              some {
                objectId := o.id
                reason := s!"{g.name o} is put into its owner's graveyard (CR 704.5m)"
                sba := .illegalAura
              }
            else none
          | none => none)
    for i in [0:auraList.size] do
      let m := auraList[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := auraList.extract (i + 1) auraList.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .illegalAttachments
              #[] #[] #[] #[] #[] illegalEquips illegalCreatureAtts #[]
              deferPlayFromExileLogs), (true, true))
      | none => pure ()
  -- Illegally attached Equipment captured at start of pass (CR 704.5n / 702.16d).
  for (eqId, hostId) in illegalEquips do
    match g.findObject? eqId with
    | some o =>
      if o.isOnBattlefield && o.attachedTo == some hostId then
        g := g.record (GameEvent.unattached g.turnNumber (g.snapshot o) hostId
          (cause := .stateBased .illegalEquipmentOrFortification))
        g := g.logMsg s!"{g.name o} becomes unattached (CR 704.5n)"
        changed := true
    | none => pure ()
  -- Creatures, battles, or non-Aura/non-Equipment permanents attached to an object (CR 704.5p).
  for (attId, hostId) in illegalCreatureAtts do
    match g.findObject? attId with
    | some o =>
      if o.isOnBattlefield && o.attachedTo == some hostId then
        g := g.record (GameEvent.unattached g.turnNumber (g.snapshot o) hostId
          (cause := .stateBased .illegalCreatureAttachment))
        g := g.logMsg s!"{g.name o} becomes unattached (CR 704.5p)"
        changed := true
    | none => pure ()
  match g.decideGameIfFinished with
  | some finished => return (finished, (true, true))
  | none => return (g, (changed, false))

/-- Validate `Pending.chooseLegend` against `validLegendChoiceIds` and
`preBatchLegendSnapshotValid`, narrowing stale candidate lists or clearing an
invalidated `< 2`-candidate prompt. Returns `(g, returnEarly, clearedInvalidLegend)`
(CR 704.3 / 704.5j / 704.8). -/
def normalizePendingLegendChoice (g : Game) : Game × Bool × Bool :=
  match g.pending with
  | .chooseLegend p name ids =>
    let still := g.validLegendChoiceIds p name ids
    if still.size ≥ 2 then
      let g :=
        if still != ids then
          g.change (.pending (.chooseLegend p name still))
        else g
      (g, true, false)
    else
      (g.change (.pending .none), false, true)
  | _ => (g, false, false)

/-- Perform applicable state-based actions (CR 704.3). The `Bool` is `true` if
any state-based action was performed (used by CR 514.3a). If a legend-rule
choice is required (CR 704.5j), the check pauses: that SBA is not finished,
so CR 704.3 does not yet repeat, put triggers on the stack, or grant
priority. `keepLegend` resumes the loop. -/
private def peelLeadingSbaOrLeave? :
    PendingReplacement → Option (PendingReplacement × Option PendingReplacement)
  | pr@(.checkSBA _) => some (pr, none)
  | pr@(.leavePlayersWhoLost ..) => some (pr, none)
  | .seq a b =>
    match peelLeadingSbaOrLeave? a with
    | some (lead, some rem) => some (lead, some (.seq rem b))
    | some (lead, none) => some (lead, some b)
    | none => none
  | _ => none

private def seqOptPending :
    Option PendingReplacement → Option PendingReplacement → Option PendingReplacement
  | some a, some b => some (.seq a b)
  | some a, none => some a
  | none, b? => b?

private def pushOuterSuffix (g : Game) (suf : PendingReplacement) : Game :=
  let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
  g.change (.pushOuterPendingReplacement suf)

/-- Pop `oCaller?` (when `popOuterCaller`) then `o0?` (when `po0`) and push a
single combined `O_0 >> rest? >> O_caller` entry onto `outerPendingReplacements`. -/
private def combineOuterContinuations (g : Game)
    (po0 : Bool) (rest? : Option PendingReplacement) (popOuterCaller : Bool) :
    Game × Bool :=
  if rest?.isNone && !popOuterCaller then (g, po0)
  else if rest?.isNone && !po0 then (g, popOuterCaller)
  else Id.run do
    let mut g := g
    let oCaller? : Option PendingReplacement :=
      if popOuterCaller then g.outerPendingReplacements.back? else none
    if oCaller?.isSome then
      g := g.change .popOuterPendingReplacement
    let o0? : Option PendingReplacement :=
      if po0 then g.outerPendingReplacements.back? else none
    if o0?.isSome then
      g := g.change .popOuterPendingReplacement
    match seqOptPending (seqOptPending o0? rest?) oCaller? with
    | some comb => return (pushOuterSuffix g comb, true)
    | none => return (g, false)

private def mergeLeaveArgs (g : Game)
    (s0 : Option Pending) (po0 : Bool) (d0 : Array PlayerId) (rw0 : Option Bool)
    (savedIn : Option Pending) (popOuterIn : Bool)
    (departedIn : Array PlayerId) (rewindProposalIn : Option Bool)
    (rest? : Option PendingReplacement := none) :
    Game × Option Pending × Bool × Array PlayerId × Option Bool := Id.run do
  let departed :=
    departedIn.foldl (fun acc pid => if acc.contains pid then acc else acc.push pid) d0
  let rw? := rw0 <|> rewindProposalIn
  match s0, savedIn with
  | some oldP, some newP =>
    if oldP != .none && newP != .none then
      let mut g := g
      let oCaller? : Option PendingReplacement :=
        if popOuterIn then g.outerPendingReplacements.back? else none
      if oCaller?.isSome then
        g := g.change .popOuterPendingReplacement
      let o0? : Option PendingReplacement :=
        if po0 then g.outerPendingReplacements.back? else none
      if o0?.isSome then
        g := g.change .popOuterPendingReplacement
      let restoreNew : PendingReplacement := .restorePending newP false (departed := departed)
      let tailAfterRest := g.chainRestoreAfterOpenBatch restoreNew oCaller?
      let outer :=
        match seqOptPending o0? rest? with
        | some pre => .seq pre tailAfterRest
        | none => tailAfterRest
      return (pushOuterSuffix g outer, some oldP, true, departed, rw?)
  | _, _ => pure ()
  let (g0, popOuter0) := combineOuterContinuations g po0 rest? popOuterIn
  let mut saved? := s0
  match s0, savedIn with
  | none, s => saved? := s
  | some .none, s => saved? := s.orElse (fun _ => some .none)
  | some _, _ => pure ()
  return (g0, saved?, popOuter0, departed, rw?)

private def splitFirstLeave? :
    PendingReplacement →
      Option (Option PendingReplacement × PendingReplacement × Option PendingReplacement)
  | pr@(.leavePlayersWhoLost ..) => some (none, pr, none)
  | .seq a b =>
    match splitFirstLeave? a with
    | some (before?, leaf, after?) =>
      some (before?, leaf, seqOptPending after? (some b))
    | none =>
      match splitFirstLeave? b with
      | some (before?, leaf, after?) =>
        some (seqOptPending (some a) before?, leaf, after?)
      | none => none
  | _ => none

private def splitFirstLeaveOrSba? :
    PendingReplacement →
      Option (Option PendingReplacement × PendingReplacement × Option PendingReplacement)
  | pr@(.leavePlayersWhoLost ..) => some (none, pr, none)
  | pr@(.checkSBA _) => some (none, pr, none)
  | .seq a b =>
    match splitFirstLeaveOrSba? a with
    | some (before?, leaf, after?) =>
      some (before?, leaf, seqOptPending after? (some b))
    | none =>
      match splitFirstLeaveOrSba? b with
      | some (before?, leaf, after?) =>
        some (seqOptPending (some a) before?, leaf, after?)
      | none => none
  | _ => none

private def mergeFromEventIdx (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

private def chainOrMergeLeave (g0 : Game)
    (saved? : Option Pending) (popOuter : Bool)
    (departed : Array PlayerId) (rewindProposal : Option Bool)
    (fromEventIdx? : Option Nat := none) : Game :=
  match g0.pendingReplacement with
  | none =>
    g0.chainPendingReplacement
      (.leavePlayersWhoLost saved? popOuter departed rewindProposal fromEventIdx?)
  | some pr =>
    match (splitFirstLeave? pr).orElse (fun _ => splitFirstLeaveOrSba? pr) with
    | some (before?, .leavePlayersWhoLost s0 po0 d0 rw0 fi0, after?) =>
      let foldTail :=
        after?.isSome &&
          (po0 || popOuter || s0.isSome || saved?.isSome || rw0.isSome || rewindProposal.isSome)
      let (g1, sm, pom, dm, rwm) :=
        mergeLeaveArgs g0 s0 po0 d0 rw0 saved? popOuter departed rewindProposal
          (rest? := if foldTail then after? else none)
      let newLeaf : PendingReplacement :=
        .leavePlayersWhoLost sm pom dm rwm (mergeFromEventIdx fi0 fromEventIdx?)
      let withBefore :=
        match before? with
        | some bef => .seq bef newLeaf
        | none => newLeaf
      let pr' :=
        if foldTail then withBefore
        else
          match after? with
          | some tail => .seq withBefore tail
          | none => withBefore
      g1.change (.pendingReplacement (some pr'))
    | some (before?, .checkSBA fi0, after?) =>
      let foldTail := after?.isSome && (popOuter || saved?.isSome || rewindProposal.isSome)
      let (g1, pom) :=
        if foldTail then combineOuterContinuations g0 false after? popOuter
        else (g0, popOuter)
      let newLeaf : PendingReplacement :=
        .leavePlayersWhoLost saved? pom departed rewindProposal (mergeFromEventIdx fi0 fromEventIdx?)
      let withBefore :=
        match before? with
        | some bef => .seq bef newLeaf
        | none => newLeaf
      let pr' :=
        if foldTail then withBefore
        else
          match after? with
          | some tail => .seq withBefore tail
          | none => withBefore
      g1.change (.pendingReplacement (some pr'))
    | _ =>
      g0.chainPendingReplacement
        (.leavePlayersWhoLost saved? popOuter departed rewindProposal fromEventIdx?)

private def chainOrMergeSba (g0 : Game) (fromEventIdx? : Option Nat := none) : Game :=
  match g0.pendingReplacement with
  | none => g0.chainPendingReplacement (.checkSBA fromEventIdx?)
  | some pr =>
    match (splitFirstLeave? pr).orElse (fun _ => splitFirstLeaveOrSba? pr) with
    | some (before?, .leavePlayersWhoLost s0 po0 d0 rw0 fi0, after?) =>
      let mfi := mergeFromEventIdx fi0 fromEventIdx?
      if mfi == fi0 then g0
      else
        let newLeaf : PendingReplacement := .leavePlayersWhoLost s0 po0 d0 rw0 mfi
        let withBefore :=
          match before? with
          | some bef => .seq bef newLeaf
          | none => newLeaf
        let pr' :=
          match after? with
          | some tail => .seq withBefore tail
          | none => withBefore
        g0.change (.pendingReplacement (some pr'))
    | some (before?, .checkSBA fi0, after?) =>
      let mfi := mergeFromEventIdx fi0 fromEventIdx?
      if mfi == fi0 then g0
      else
        let newLeaf : PendingReplacement := .checkSBA mfi
        let withBefore :=
          match before? with
          | some bef => .seq bef newLeaf
          | none => newLeaf
        let pr' :=
          match after? with
          | some tail => .seq withBefore tail
          | none => withBefore
        g0.change (.pendingReplacement (some pr'))
    | _ => g0.chainPendingReplacement (.checkSBA fromEventIdx?)

private def rewriteRepausedPostCloseBatch (g : Game) (curBid? : Option BatchId)
    (flushedFromPending : Bool)
    (savedIn : Option Pending) (popOuterAfterFlush : Bool)
    (departedIn : Array PlayerId) (rewindProposalIn : Option Bool)
    (deferRestore : Bool)
    (flushedPendingAfter? : Option PendingReplacement := none)
    (fromEventIdx? : Option Nat := none) :
    Game × Option Pending × Bool × Array PlayerId × Option Bool × Option Nat := Id.run do
  let mut g := g
  if flushedFromPending then
    match curBid?.bind (fun curBid => g.pendingReplacement.bind (splitAfterCloseBatchFor? curBid)) with
    | some (throughClose, curAfter0?) =>
      let curAfter? := seqOptPending curAfter0? flushedPendingAfter?
      if deferRestore then
        let g0 := g.change (.pendingReplacement (some throughClose))
        match curAfter?.bind peelLeadingSbaOrLeave? with
        | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, outerTail?) =>
          let (gm, sm, pom, dm, rwm) :=
            mergeLeaveArgs g0 s0 po0 d0 rw0 savedIn popOuterAfterFlush departedIn rewindProposalIn
              (rest? := outerTail?)
          return (gm, sm, pom, dm, rwm, mergeFromEventIdx fi0 fromEventIdx?)
        | some (.checkSBA fi0, outerTail?) =>
          let (gp, po1) := combineOuterContinuations g0 false outerTail? popOuterAfterFlush
          return (gp, savedIn, po1, departedIn, rewindProposalIn, mergeFromEventIdx fi0 fromEventIdx?)
        | _ =>
          let (gp, po1) := combineOuterContinuations g0 false curAfter? popOuterAfterFlush
          return (gp, savedIn, po1, departedIn, rewindProposalIn, fromEventIdx?)
      else
        let (g1, savedM, poM, depM, rwM, remTail?, mfi) :=
          match curAfter?.bind peelLeadingSbaOrLeave? with
          | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, outerTail?) =>
            let mfi := mergeFromEventIdx fi0 fromEventIdx?
            if outerTail?.isSome &&
                (po0 || popOuterAfterFlush || s0.isSome || savedIn.isSome || rw0.isSome || rewindProposalIn.isSome) then
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g s0 po0 d0 rw0 savedIn popOuterAfterFlush departedIn rewindProposalIn
                  (rest? := outerTail?)
              (gm, sm, pom, dm, rwm, none, mfi)
            else
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g s0 po0 d0 rw0 savedIn popOuterAfterFlush departedIn rewindProposalIn
              (gm, sm, pom, dm, rwm, outerTail?, mfi)
          | some (.checkSBA fi0, outerTail?) =>
            let mfi := mergeFromEventIdx fi0 fromEventIdx?
            if outerTail?.isSome && (popOuterAfterFlush || savedIn.isSome || rewindProposalIn.isSome) then
              let (gp, po1) := combineOuterContinuations g false outerTail? popOuterAfterFlush
              (gp, savedIn, po1, departedIn, rewindProposalIn, none, mfi)
            else
              (g, savedIn, popOuterAfterFlush, departedIn, rewindProposalIn, outerTail?, mfi)
          | _ =>
            if curAfter?.isSome && (popOuterAfterFlush || savedIn.isSome || rewindProposalIn.isSome) then
              let (gp, po1) := combineOuterContinuations g false curAfter? popOuterAfterFlush
              (gp, savedIn, po1, departedIn, rewindProposalIn, none, fromEventIdx?)
            else
              (g, savedIn, popOuterAfterFlush, departedIn, rewindProposalIn, curAfter?, fromEventIdx?)
        g := g1
        let newHead? : Option PendingReplacement :=
          if savedM.isSome || poM || !depM.isEmpty || rwM.isSome ||
              g.players.any (fun r => r.lost && !r.leftTheGame) then
            some (.leavePlayersWhoLost savedM poM depM rwM mfi)
          else
            some (.checkSBA mfi)
        let newAfter? := seqOptPending newHead? remTail?
        let newPr :=
          match newAfter? with
          | some after => .seq throughClose after
          | none => throughClose
        g := g.change (.pendingReplacement (some newPr))
        return (g, savedM, poM, depM, rwM, mfi)
    | none =>
      if deferRestore then
        match flushedPendingAfter?.bind peelLeadingSbaOrLeave? with
        | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, outerTail?) =>
          let (gm, sm, pom, dm, rwm) :=
            mergeLeaveArgs g s0 po0 d0 rw0 savedIn popOuterAfterFlush departedIn rewindProposalIn
              (rest? := outerTail?)
          return (gm, sm, pom, dm, rwm, mergeFromEventIdx fi0 fromEventIdx?)
        | some (.checkSBA fi0, outerTail?) =>
          let (gp, po1) := combineOuterContinuations g false outerTail? popOuterAfterFlush
          return (gp, savedIn, po1, departedIn, rewindProposalIn, mergeFromEventIdx fi0 fromEventIdx?)
        | _ =>
          let (gp, po1) := combineOuterContinuations g false flushedPendingAfter? popOuterAfterFlush
          return (gp, savedIn, po1, departedIn, rewindProposalIn, fromEventIdx?)
      else
        let (g1, savedM, poM, depM, rwM, remTail?, mfi) :=
          match flushedPendingAfter?.bind peelLeadingSbaOrLeave? with
          | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, outerTail?) =>
            let mfi := mergeFromEventIdx fi0 fromEventIdx?
            if outerTail?.isSome &&
                (po0 || popOuterAfterFlush || s0.isSome || savedIn.isSome || rw0.isSome || rewindProposalIn.isSome) then
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g s0 po0 d0 rw0 savedIn popOuterAfterFlush departedIn rewindProposalIn
                  (rest? := outerTail?)
              (gm, sm, pom, dm, rwm, none, mfi)
            else
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g s0 po0 d0 rw0 savedIn popOuterAfterFlush departedIn rewindProposalIn
              (gm, sm, pom, dm, rwm, outerTail?, mfi)
          | some (.checkSBA fi0, outerTail?) =>
            let mfi := mergeFromEventIdx fi0 fromEventIdx?
            if outerTail?.isSome && (popOuterAfterFlush || savedIn.isSome || rewindProposalIn.isSome) then
              let (gp, po1) := combineOuterContinuations g false outerTail? popOuterAfterFlush
              (gp, savedIn, po1, departedIn, rewindProposalIn, none, mfi)
            else
              (g, savedIn, popOuterAfterFlush, departedIn, rewindProposalIn, outerTail?, mfi)
          | _ =>
            if flushedPendingAfter?.isSome && (popOuterAfterFlush || savedIn.isSome || rewindProposalIn.isSome) then
              let (gp, po1) := combineOuterContinuations g false flushedPendingAfter? popOuterAfterFlush
              (gp, savedIn, po1, departedIn, rewindProposalIn, none, fromEventIdx?)
            else
              (g, savedIn, popOuterAfterFlush, departedIn, rewindProposalIn, flushedPendingAfter?, fromEventIdx?)
        g := g1
        let newHead? : Option PendingReplacement :=
          if savedM.isSome || poM || !depM.isEmpty || rwM.isSome ||
              g.players.any (fun r => r.lost && !r.leftTheGame) then
            some (.leavePlayersWhoLost savedM poM depM rwM mfi)
          else
            some (.checkSBA mfi)
        if let some suf := seqOptPending newHead? remTail? then
          g := g.chainPendingReplacement suf
        return (g, savedM, poM, depM, rwM, mfi)
  else
    let pushedAfter? : Option PendingReplacement :=
      if popOuterAfterFlush then g.outerPendingReplacements.back? else none
    if pushedAfter?.isSome then
      g := g.change .popOuterPendingReplacement
    if deferRestore then
      match pushedAfter?.bind peelLeadingSbaOrLeave? with
      | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, outerTail?) =>
        let (gm, sm, pom, dm, rwm) :=
          mergeLeaveArgs g s0 po0 d0 rw0 savedIn false departedIn rewindProposalIn
            (rest? := outerTail?)
        return (gm, sm, pom, dm, rwm, mergeFromEventIdx fi0 fromEventIdx?)
      | some (.checkSBA fi0, outerTail?) =>
        let (gp, po1) := combineOuterContinuations g false outerTail? false
        return (gp, savedIn, po1, departedIn, rewindProposalIn, mergeFromEventIdx fi0 fromEventIdx?)
      | _ =>
        let (gp, po1) := combineOuterContinuations g false pushedAfter? false
        return (gp, savedIn, po1, departedIn, rewindProposalIn, fromEventIdx?)
    else
      let (g1, savedM, poM, depM, rwM, remTail?, mfi) :=
        match pushedAfter?.bind peelLeadingSbaOrLeave? with
        | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, outerTail?) =>
          let mfi := mergeFromEventIdx fi0 fromEventIdx?
          if outerTail?.isSome &&
              (po0 || popOuterAfterFlush || s0.isSome || savedIn.isSome || rw0.isSome || rewindProposalIn.isSome) then
            let (gm, sm, pom, dm, rwm) :=
              mergeLeaveArgs g s0 po0 d0 rw0 savedIn false departedIn rewindProposalIn
                (rest? := outerTail?)
            (gm, sm, pom, dm, rwm, none, mfi)
          else
            let (gm, sm, pom, dm, rwm) :=
              mergeLeaveArgs g s0 po0 d0 rw0 savedIn false departedIn rewindProposalIn
            (gm, sm, pom, dm, rwm, outerTail?, mfi)
        | some (.checkSBA fi0, outerTail?) =>
          let mfi := mergeFromEventIdx fi0 fromEventIdx?
          if outerTail?.isSome && (popOuterAfterFlush || savedIn.isSome || rewindProposalIn.isSome) then
            let (gp, po1) := combineOuterContinuations g false outerTail? false
            (gp, savedIn, po1, departedIn, rewindProposalIn, none, mfi)
          else
            (g, savedIn, false, departedIn, rewindProposalIn, outerTail?, mfi)
        | _ =>
          if pushedAfter?.isSome && (popOuterAfterFlush || savedIn.isSome || rewindProposalIn.isSome) then
            let (gp, po1) := combineOuterContinuations g false pushedAfter? false
            (gp, savedIn, po1, departedIn, rewindProposalIn, none, fromEventIdx?)
          else
            (g, savedIn, false, departedIn, rewindProposalIn, pushedAfter?, fromEventIdx?)
      g := g1
      match curBid?.bind (fun curBid => g.pendingReplacement.bind (splitAfterCloseBatchFor? curBid)) with
      | some (throughClose, innerAfter?) =>
        let (g', poM, remTail?) :=
          if poM && innerAfter?.isSome then
            let o0? := g.outerPendingReplacements.back?
            let g0 := if o0?.isSome then g.change .popOuterPendingReplacement else g
            (g0, false, seqOptPending o0? remTail?)
          else
            (g, poM, remTail?)
        g := g'
        let newHead? : Option PendingReplacement :=
          if savedM.isSome || poM || !depM.isEmpty || rwM.isSome ||
              g.players.any (fun r => r.lost && !r.leftTheGame) then
            some (.leavePlayersWhoLost savedM poM depM rwM mfi)
          else
            some (.checkSBA mfi)
        let newAfter? := seqOptPending newHead? (seqOptPending innerAfter? remTail?)
        let newPr :=
          match newAfter? with
          | some after => .seq throughClose after
          | none => throughClose
        g := g.change (.pendingReplacement (some newPr))
        return (g, savedM, poM, depM, rwM, mfi)
      | none =>
        let newHead? : Option PendingReplacement :=
          if savedM.isSome || poM || !depM.isEmpty || rwM.isSome ||
              g.players.any (fun r => r.lost && !r.leftTheGame) then
            some (.leavePlayersWhoLost savedM poM depM rwM mfi)
          else
            some (.checkSBA mfi)
        if let some suf := seqOptPending newHead? remTail? then
          g := g.chainPendingReplacement suf
        return (g, savedM, poM, depM, rwM, mfi)

partial def checkSBACounted (g : Game)
    (savedIn : Option Pending := none) (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none)
    (deferRestore : Bool := false)
    (fromLeavesLoop : Bool := false)
    (deferPlayFromExileLogs : Bool := fromLeavesLoop)
    (fromEventIdx? : Option Nat := none) : Game × Bool :=
  let chainSbaPauseTail (g0 : Game) (saved? : Option Pending) (popOuter : Bool)
      (departed : Array PlayerId) (rewindProposal : Option Bool)
      (forceLeave : Bool := false) (fromIdx? : Option Nat := fromEventIdx?) : Game :=
    if deferRestore then g0
    else if forceLeave || saved?.isSome || popOuter || !departed.isEmpty ||
        rewindProposal.isSome || g0.players.any (fun r => r.lost && !r.leftTheGame) then
      chainOrMergeLeave g0 saved? popOuter departed rewindProposal (fromEventIdx? := fromIdx?)
    else
      chainOrMergeSba g0 (fromEventIdx? := fromIdx?)
  if g.over then (g, false)
  else
    -- Waiting for a legend-rule choice: do not apply further SBAs until
    -- the player keeps one copy (CR 704.5j). Narrow or drop a stale prompt
    -- before `g.sbaPaused` returns `(g, false)` or `withBatchReturn` opens a batch.
    let sbaFromIdx0 := fromEventIdx?.getD g.events.size
    let preSba0 :=
      match fromEventIdx? with
      | some idx => g.mkHistoricalGameAt idx
      | none => g
    let (g, returnEarly, clearedInvalidLegend) := g.normalizePendingLegendChoice
    if returnEarly || g.sbaPaused then (g, false)
    else
    let savedForFlush := if clearedInvalidLegend then none else savedIn
    let shouldFlush :=
      !(rewindProposalIn.isSome && g.isPreProposalCheckpointBatch) &&
        (clearedInvalidLegend ||
          (!g.sbaPaused && g.pending == .none && g.currentBatch.isSome &&
            g.openBatchAwaitedPausePrompt &&
            savedForFlush.all g.batchPausePromptGoneOrInvalid))
    let flushedBid? : Option BatchId :=
      if shouldFlush then g.currentBatch.map Prod.fst else none
    let flushedFromPending : Bool :=
      flushedBid?.any (fun bid => (g.pendingReplacement.bind (splitAfterCloseBatchFor? bid)).isSome)
    let flushedPendingAfter? : Option PendingReplacement :=
      flushedBid?.bind (fun bid => (g.pendingReplacement.bind (splitAfterCloseBatchFor? bid)).bind Prod.snd)
    let (g, popOuterIn) :=
      if shouldFlush then
        g.flushDismissedPausedBatch savedForFlush popOuterIn
          (hasDeferredRewind := rewindProposalIn.isSome)
          (chainAfterOnRepause := false)
      else (g, popOuterIn)
    if g.over then (g, true)
    else if flushedBid?.isSome && g.sbaPaused then
      let (g, _, _, _, _, _) :=
        rewriteRepausedPostCloseBatch g (g.currentBatch.map Prod.fst) flushedFromPending
          savedIn popOuterIn departedIn rewindProposalIn deferRestore
          (flushedPendingAfter? := flushedPendingAfter?)
          (fromEventIdx? := if deferPlayFromExileLogs then fromEventIdx? else some sbaFromIdx0)
      (g, true)
    else
    match g.pending with
    | .chooseReplacement .. | .chooseLegend .. =>
      (chainSbaPauseTail g savedIn popOuterIn departedIn rewindProposalIn
         (fromIdx? := if deferPlayFromExileLogs then fromEventIdx? else some sbaFromIdx0), true)
    | _ =>
    let (g, savedIn, popOuterIn, departedIn, rewindProposalIn, outerAfter?, peeledLeave, peeledSba, effFromIdx?) :
        Game × Option Pending × Bool × Array PlayerId × Option Bool ×
          Option PendingReplacement × Bool × Bool × Option Nat :=
      if shouldFlush && !deferRestore && g.currentBatch.isNone then
        match g.pendingReplacement with
        | some pr =>
          let g1 := g.change (.pendingReplacement none)
          match peelLeadingSbaOrLeave? pr with
          | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, rest?) =>
            let mfi := mergeFromEventIdx fi0 fromEventIdx?
            if rest?.isSome &&
                (po0 || popOuterIn || s0.isSome || savedIn.isSome || rw0.isSome || rewindProposalIn.isSome) then
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g1 s0 po0 d0 rw0 savedIn popOuterIn departedIn rewindProposalIn
                  (rest? := rest?)
              (gm, sm, pom, dm, rwm, none, true, false, mfi)
            else
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g1 s0 po0 d0 rw0 savedIn popOuterIn departedIn rewindProposalIn
              (gm, sm, pom, dm, rwm, rest?, true, false, mfi)
          | some (.checkSBA fi0, rest?) =>
            let mfi := mergeFromEventIdx fi0 fromEventIdx?
            if rest?.isSome && (popOuterIn || savedIn.isSome || rewindProposalIn.isSome) then
              let (g2, po1) := combineOuterContinuations g1 false rest? popOuterIn
              (g2, savedIn, po1, departedIn, rewindProposalIn, none, false, true, mfi)
            else
              (g1, savedIn, popOuterIn, departedIn, rewindProposalIn, rest?, false, true, mfi)
          | _ =>
            if popOuterIn || savedIn.isSome || rewindProposalIn.isSome then
              let (g2, po1) := combineOuterContinuations g1 false (some pr) popOuterIn
              (g2, savedIn, po1, departedIn, rewindProposalIn, none, false, false, fromEventIdx?)
            else
              (g1, savedIn, popOuterIn, departedIn, rewindProposalIn, some pr, false, false, fromEventIdx?)
        | none =>
          if popOuterIn then
            match g.outerPendingReplacements.back?.bind peelLeadingSbaOrLeave? with
            | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, rest?) =>
              let g1 := g.change .popOuterPendingReplacement
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g1 s0 po0 d0 rw0 savedIn false departedIn rewindProposalIn
                  (rest? := rest?)
              (gm, sm, pom, dm, rwm, none, true, false, mergeFromEventIdx fi0 fromEventIdx?)
            | some (.checkSBA fi0, rest?) =>
              let g1 := g.change .popOuterPendingReplacement
              let (g2, po1) := combineOuterContinuations g1 false rest? false
              (g2, savedIn, po1, departedIn, rewindProposalIn, none, false, true, mergeFromEventIdx fi0 fromEventIdx?)
            | _ =>
              (g, savedIn, popOuterIn, departedIn, rewindProposalIn, none, false, false, fromEventIdx?)
          else
            (g, savedIn, popOuterIn, departedIn, rewindProposalIn, none, false, false, fromEventIdx?)
      else
        (g, savedIn, popOuterIn, departedIn, rewindProposalIn, none, false, false, fromEventIdx?)
    let effSbaFromIdx :=
      match effFromIdx? with
      | some idx => min idx sbaFromIdx0
      | none => sbaFromIdx0
    let preSba :=
      if effSbaFromIdx < sbaFromIdx0 then g.mkHistoricalGameAt effSbaFromIdx
      else preSba0
    let pfeFromIdx? : Option Nat :=
      if deferPlayFromExileLogs then effFromIdx? else some effSbaFromIdx
    let (g, (changed, _paused)) := g.withBatchReturn none fun g => Id.run do
      let mut g := g
      let mut changed := false
      if let .chooseReplacement _ _ := g.pending then
        return (g, (changed, true))
      -- Capture all applicable CR 704.5 state-based actions simultaneously
      -- against the start-of-pass state BEFORE recording `GameEvent.playerLost`
      -- or applying CR 704.5q counter annihilation so a player losing in this
      -- pass does not alter battlefield control or continuous effects mid-pass
      -- (CR 704.3 / 800.4a), simultaneous 0-toughness death LKI retains its
      -- pre-annihilation counters, and Pass 1 does not sweep newly dead tokens
      -- or newly unattached Auras/Equipment until Pass 2 (CR 704.3 / 704.8).
      let preBf := g.battlefield
      let victims : Array SbaGraveyardMove :=
        preBf.filterMap (fun o =>
          if !g.isCreature o then none
          else
            let t := g.toughness o
            if t ≤ 0 then
              some {
                objectId := o.id
                reason := s!"{g.name o} dies (toughness {t})"
                verb := some .put
                sba := .zeroOrLessToughness
              }
            else if o.status.damage ≥ t && !g.hasIndestructible o then
              some {
                objectId := o.id
                reason := s!"{g.name o} dies from lethal damage"
                verb := some .destroy
                sba := .lethalDamage
              }
            else if g.deathtouchDealtSinceLastSba o.id && !g.hasIndestructible o then
              some {
                objectId := o.id
                reason := s!"{g.name o} dies from deathtouch"
                verb := some .destroy
                sba := .deathtouchDamage
              }
            else none)
      let pwMoves : Array SbaGraveyardMove :=
        preBf.filterMap (fun o =>
          if g.isPlaneswalker o && o.status.loyaltyCounters == 0 &&
              !g.planeswalkersSurviveZeroLoyalty (g.controllerOf o) then
            some {
              objectId := o.id
              reason := s!"{g.name o} is put into its owner's graveyard (0 loyalty, CR 704.5i)"
              sba := .zeroLoyalty
            }
          else none)
      let legendGroups : Array (PlayerId × String × Array ObjectId) :=
        g.legendRuleGroups (some (preBf.map (·.id)))
      let tokensOutsideBf : Array ObjectId :=
        g.objects.filterMap (fun o =>
          if o.printed.isToken && o.zone != .battlefield then some o.id else none)
      let copiesOutside : Array ObjectId :=
        g.objects.filterMap (fun o =>
          if o.isCopy && !o.printed.isToken && o.zone != .stack && o.zone != .battlefield &&
              !(o.zone == .exile &&
                (g.playPermissionEntriesOf o.id).any (fun (_, _, perm, _) => perm.prepareSource.isSome)) then
            some o.id
          else none)
      let sagaMoves : Array SbaGraveyardMove :=
        preBf.filterMap (fun o =>
          if g.hasSubtype o .saga then
            let finalCh := g.finalChapterNumber o
            match g.controllerOf o with
            | some ctrl =>
              if finalCh > 0 && o.status.lore ≥ finalCh &&
                  !g.sagaChapterPending o.id then
                some {
                  objectId := o.id
                  reason := s!"{g.name o} is sacrificed (CR 714.4)"
                  verb := some .sacrifice
                  actor := some ctrl
                  sba := .sagaFinalChapter
                }
              else none
            | none => none
          else none)
      let illegalAuras : Array ObjectId :=
        preBf.filterMap (fun o =>
          if !g.isAura o then none
          else
            let legal :=
              match o.attachedTo.bind g.findObject? with
              | some host => g.auraObjCanEnchant host o
              | none => false
            if !legal then some o.id else none)
      let illegalEquips : Array (ObjectId × ObjectId) :=
        preBf.filterMap (fun o =>
          if !g.isEquipment o then none
          else
            match o.attachedTo with
            | none => none
            | some hostId =>
              let legal :=
                match g.findObject? hostId with
                | some host =>
                  host.isOnBattlefield && g.isCreature host && !g.protectedFrom host o
                | none => false
              if !legal then some (o.id, hostId) else none)
      let illegalCreatureAtts : Array (ObjectId × ObjectId) :=
        preBf.filterMap (fun o =>
          match o.attachedTo with
          | none => none
          | some hostId =>
            if g.isCreature o || g.isBattle o || (!g.isAura o && !g.isEquipment o) then
              some (o.id, hostId)
            else none)
      -- Players losing (CR 704.5a–c / 704.6a–b / 810.8a,c,d / 810.11). They
      -- leave after this SBA pass if the game continues (CR 800.4 / 800.4a).
      let hasCantLose (g : Game) (pid : PlayerId) : Bool :=
        g.objects.any fun o =>
          (o.isOnBattlefield || o.zone == .command) &&
            let srcCtrl := (g.controllerOf o).getD o.owner
            g.stillInGame srcCtrl &&
              let env : EvalEnv := { controller := srcCtrl, sourceId := some o.id }
              (g.staticAbilities o).any fun ab =>
                ab.anyRule fun cond? r =>
                  match r with
                  | .player (.cantLoseGame who) =>
                    cond?.all (EvalExpr.evalCondition g env) &&
                      EvalExpr.matchesPlayerFilter g env who pid
                  | _ => false
      for pl in g.players do
        let curPl := g.player pl.id
        if g.stillInGame pl.id then
          let shielded :=
            hasCantLose g pl.id ||
              g.livingPlayers.any (fun mate =>
                g.areTeammates pl.id mate.id && hasCantLose g mate.id)
          if shielded then
            pure ()
          else
            let team := g.teamMembers pl.id
            let poisonThreshold :=
              if team.size ≤ 1 then 10 else 10 + 5 * (team.size - 1)
            let poisonLoss := g.teamPoison pl.id ≥ poisonThreshold
            let loss? : Option (LossReason × StateBasedAction) :=
              if curPl.life ≤ 0 then some (.lifeZeroOrLess, .lifeZeroOrLess)
              else if g.drewFromEmpty pl.id then some (.decked, .drewFromEmpty)
              else if poisonLoss then some (.poison, .tenPoison)
              else none
            match loss? with
            | none => pure ()
            | some (lossReason, sbaKind) =>
              g := g.record (GameEvent.playerLost g.turnNumber pl.id lossReason
                (cause := some (.stateBased sbaKind)))
              let detail :=
                match lossReason with
                | .lifeZeroOrLess => s!"life total {curPl.life}"
                | .decked => "drew from empty library"
                | .poison => "poison"
                | _ => "state-based action"
              g := g.logMsg s!"{curPl.name} loses the game ({detail})"
              for mate in g.players do
                if mate.id != pl.id && g.stillInGame mate.id && g.areTeammates pl.id mate.id then
                  g := g.record (GameEvent.playerLost g.turnNumber mate.id lossReason
                    (cause := some (.stateBased sbaKind)))
                  g := g.logMsg s!"{mate.name} loses the game (teammate lost; CR 810.8a)"
              changed := true
      match g.decideGameIfFinished with
      | some finished => return (finished, (true, true))
      | none => pure ()
      return g.finishSbaSweep victims preBf (.counterAnnihilation 0) pwMoves sagaMoves tokensOutsideBf
        copiesOutside illegalAuras illegalEquips illegalCreatureAtts legendGroups
        (changedIn := changed) (deferPlayFromExileLogs := true)
    let (g, didOut) :=
      match g.pending with
      | .chooseReplacement .. | .chooseLegend .. =>
        let g := chainSbaPauseTail g savedIn popOuterIn departedIn rewindProposalIn
          (forceLeave := peeledLeave) (fromIdx? := pfeFromIdx?)
        let g :=
          if !deferPlayFromExileLogs && deferRestore && !g.over then
            emitExpiredPlayFromExileLogs preSba g effSbaFromIdx
          else g
        (g, true)
      | _ =>
        let (g, chainedOwner) :=
          if !g.over && !deferRestore then
            if ((peeledLeave || peeledSba) &&
                  (savedIn.isSome || popOuterIn || !departedIn.isEmpty || rewindProposalIn.isSome ||
                    g.players.any (fun r => r.lost && !r.leftTheGame))) ||
                (!fromLeavesLoop &&
                  (savedIn.isSome || popOuterIn || !departedIn.isEmpty || rewindProposalIn.isSome ||
                    ((shouldFlush && g.currentBatch.isNone) &&
                      g.players.any (fun r => r.lost && !r.leftTheGame)))) then
              (chainOrMergeLeave g savedIn popOuterIn departedIn rewindProposalIn
                (fromEventIdx? := pfeFromIdx?), true)
            else if (peeledLeave || peeledSba) && changed then
              (chainOrMergeSba g (fromEventIdx? := pfeFromIdx?), true)
            else (g, false)
          else (g, false)
        let g :=
          if !deferPlayFromExileLogs && !chainedOwner && !g.over then
            emitExpiredPlayFromExileLogs preSba g effSbaFromIdx
          else g
        (g, changed || clearedInvalidLegend)
    let g :=
      match outerAfter? with
      | some outer => g.chainPendingReplacement outer
      | none => g
    (g, didOut)

/-- Internal core of `checkSBACountedWithLeavesCore` that also returns any merged
`fromEventIdx?` peeled from a dismissed paused batch when `deferRestore == true`. -/
partial def checkSBACountedWithLeavesCoreWithIdx (g : Game)
    (savedIn : Option Pending := none) (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none)
    (deferRestore : Bool := false)
    (outerAfterIn? : Option PendingReplacement := none)
    (deferPlayFromExileLogs : Bool := deferRestore)
    (fromEventIdx? : Option Nat := none) :
    Game × Bool × Option Pending × Bool × Array PlayerId × Option Bool × Option Nat :=
  let rec contHasSbaOrLeave : PendingReplacement → Bool
    | .checkSBA _ | .leavePlayersWhoLost .. => true
    | .seq a b => contHasSbaOrLeave a || contHasSbaOrLeave b
    | _ => false
  if g.over then (g, false, none, false, departedIn, none, fromEventIdx?)
  else
  let sbaFromIdx0 := fromEventIdx?.getD g.events.size
  let preSba0 :=
    match fromEventIdx? with
    | some idx => g.mkHistoricalGameAt idx
    | none => g
  let (g, popOuterIn, outerAfterIn?) :=
    if outerAfterIn?.isSome && (deferRestore || savedIn.isSome || popOuterIn || rewindProposalIn.isSome) then
      let (gf, pof) := combineOuterContinuations g popOuterIn outerAfterIn? false
      (gf, pof, none)
    else
      (g, popOuterIn, outerAfterIn?)
  let (g, _, clearedInvalidLegend) := g.normalizePendingLegendChoice
  let entryPaused := g.sbaPaused
  let savedForFlush := if clearedInvalidLegend then none else savedIn
  let shouldFlush :=
    !(rewindProposalIn.isSome && g.isPreProposalCheckpointBatch) &&
      (clearedInvalidLegend ||
        (!g.sbaPaused && g.pending == .none && g.currentBatch.isSome &&
          g.openBatchAwaitedPausePrompt &&
          savedForFlush.all g.batchPausePromptGoneOrInvalid))
  let flushedBid? : Option BatchId :=
    if shouldFlush then g.currentBatch.map Prod.fst else none
  let flushedFromPending : Bool :=
    flushedBid?.any (fun bid => (g.pendingReplacement.bind (splitAfterCloseBatchFor? bid)).isSome)
  let flushedPendingAfter? : Option PendingReplacement :=
    flushedBid?.bind (fun bid => (g.pendingReplacement.bind (splitAfterCloseBatchFor? bid)).bind Prod.snd)
  let (g, popOuterIn) :=
    if shouldFlush then
      g.flushDismissedPausedBatch savedForFlush popOuterIn
        (hasDeferredRewind := rewindProposalIn.isSome)
        (chainAfterOnRepause := false)
    else (g, popOuterIn)
  if g.over then (g, shouldFlush, none, false, departedIn, none, fromEventIdx?)
  else if flushedBid?.isSome && g.sbaPaused then
    let (g, savedM, poM, depM, rwM, mfi) :=
      rewriteRepausedPostCloseBatch g (g.currentBatch.map Prod.fst) flushedFromPending
        savedIn popOuterIn departedIn rewindProposalIn deferRestore
        (flushedPendingAfter? := flushedPendingAfter?)
        (fromEventIdx? := if deferPlayFromExileLogs then fromEventIdx? else some sbaFromIdx0)
    let (g, poM) :=
      match outerAfterIn? with
      | some oa =>
        if deferRestore || savedM.isSome || poM || !depM.isEmpty || rwM.isSome ||
            g.players.any (fun r => r.lost && !r.leftTheGame) then
          let (g1, po1) := combineOuterContinuations g poM (some oa) false
          let g2 :=
            if !deferRestore && po1 && !poM then
              chainOrMergeLeave g1 savedM po1 depM rwM (fromEventIdx? := mfi)
            else g1
          (g2, po1)
        else
          (g.chainPendingReplacement oa, poM)
      | none => (g, poM)
    (g, true, savedM, poM, depM, rwM, mfi)
  else
  let (g, savedIn, popOuterIn, departedIn, rewindProposalIn, outerAfter?, carriedFromIdx?) :
      Game × Option Pending × Bool × Array PlayerId × Option Bool × Option PendingReplacement × Option Nat :=
    if shouldFlush && !g.over && !g.sbaPaused && g.currentBatch.isNone then
      match g.pendingReplacement.bind peelLeadingSbaOrLeave? with
      | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, rest?) =>
        let g1 := g.change (.pendingReplacement none)
        let fullRest? := seqOptPending rest? outerAfterIn?
        if fullRest?.isSome &&
            (deferRestore || po0 || popOuterIn || s0.isSome || savedIn.isSome || rw0.isSome || rewindProposalIn.isSome) then
          let (gm, sm, pom, dm, rwm) :=
            mergeLeaveArgs g1 s0 po0 d0 rw0 savedIn popOuterIn departedIn rewindProposalIn
              (rest? := fullRest?)
          (gm, sm, pom, dm, rwm, none, fi0)
        else
          let (gm, sm, pom, dm, rwm) :=
            mergeLeaveArgs g1 s0 po0 d0 rw0 savedIn popOuterIn departedIn rewindProposalIn
          (gm, sm, pom, dm, rwm, fullRest?, fi0)
      | some (.checkSBA fi0, rest?) =>
        let g1 := g.change (.pendingReplacement none)
        let fullRest? := seqOptPending rest? outerAfterIn?
        if fullRest?.isSome && (deferRestore || popOuterIn || savedIn.isSome || rewindProposalIn.isSome) then
          let (g2, po1) := combineOuterContinuations g1 false fullRest? popOuterIn
          (g2, savedIn, po1, departedIn, rewindProposalIn, none, fi0)
        else
          (g1, savedIn, popOuterIn, departedIn, rewindProposalIn, fullRest?, fi0)
      | _ =>
        match g.pendingReplacement with
        | some pr =>
          let g1 := g.change (.pendingReplacement none)
          let fullPr := match outerAfterIn? with | some oa => .seq pr oa | none => pr
          if deferRestore || popOuterIn || savedIn.isSome || rewindProposalIn.isSome then
            let (g2, po1) := combineOuterContinuations g1 false (some fullPr) popOuterIn
            (g2, savedIn, po1, departedIn, rewindProposalIn, none, none)
          else
            (g1, savedIn, popOuterIn, departedIn, rewindProposalIn, some fullPr, none)
        | none =>
          if popOuterIn then
            match g.outerPendingReplacements.back?.bind peelLeadingSbaOrLeave? with
            | some (.leavePlayersWhoLost s0 po0 d0 rw0 fi0, rest?) =>
              let g1 := g.change .popOuterPendingReplacement
              let fullRest? := seqOptPending rest? outerAfterIn?
              let (gm, sm, pom, dm, rwm) :=
                mergeLeaveArgs g1 s0 po0 d0 rw0 savedIn false departedIn rewindProposalIn
                  (rest? := fullRest?)
              (gm, sm, pom, dm, rwm, none, fi0)
            | some (.checkSBA fi0, rest?) =>
              let g1 := g.change .popOuterPendingReplacement
              let fullRest? := seqOptPending rest? outerAfterIn?
              let (g2, po1) := combineOuterContinuations g1 false fullRest? false
              (g2, savedIn, po1, departedIn, rewindProposalIn, none, fi0)
            | _ =>
              if outerAfterIn?.isSome then
                let (g2, po1) := combineOuterContinuations g popOuterIn outerAfterIn? false
                (g2, savedIn, po1, departedIn, rewindProposalIn, none, none)
              else
                (g, savedIn, popOuterIn, departedIn, rewindProposalIn, none, none)
          else
            (g, savedIn, popOuterIn, departedIn, rewindProposalIn, outerAfterIn?, none)
    else
      if outerAfterIn?.isSome && (deferRestore || popOuterIn || savedIn.isSome || rewindProposalIn.isSome) then
        let (g2, po1) := combineOuterContinuations g popOuterIn outerAfterIn? false
        (g2, savedIn, po1, departedIn, rewindProposalIn, none, none)
      else
        (g, savedIn, popOuterIn, departedIn, rewindProposalIn, outerAfterIn?, none)
  let effFromIdx :=
    match carriedFromIdx? with
    | some idx => min idx sbaFromIdx0
    | none => sbaFromIdx0
  let preSba :=
    if effFromIdx < sbaFromIdx0 then g.mkHistoricalGameAt effFromIdx
    else preSba0
  let pfeIdxOpt : Option Nat := if deferPlayFromExileLogs then none else some effFromIdx
  let carriedOutIdx? : Option Nat := mergeFromEventIdx carriedFromIdx? fromEventIdx?
  let (reenterAfterRewind?, outerAfter?) :
      Option (Game × Bool × Option Pending × Bool × Array PlayerId × Option Bool × Option Nat) ×
        Option PendingReplacement :=
    match rewindProposalIn with
    | some hadPreBodyCont =>
      if !g.over && !g.sbaPaused && (g.currentBatch.isNone || g.isPreProposalCheckpointBatch) then
        let (gFolded, poFolded) :=
          if outerAfter?.isSome then combineOuterContinuations g popOuterIn outerAfter? false
          else (g, popOuterIn)
        let (g', s', po') := gFolded.applyDeferredProposalRewind savedIn poFolded departedIn hadPreBodyCont
        let (g'', didMore, savedOut, poOut, depOut, rwOut, fiOut) :=
          g'.checkSBACountedWithLeavesCoreWithIdx s' po' departedIn none (deferRestore := deferRestore)
            (fromEventIdx? := if deferPlayFromExileLogs then carriedOutIdx? else some effFromIdx)
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
        (some (g'', clearedInvalidLegend || didMore, savedOut, poOut, depOut, rwOut, fiOut), none)
      else (none, outerAfter?)
    | none => (none, outerAfter?)
  let (gOut, didOut, sOut, poOut, depOut, rwOut, outerAfter?, handledPfeLogs, outFromIdx?) :
      Game × Bool × Option Pending × Bool × Array PlayerId × Option Bool × Option PendingReplacement × Bool × Option Nat :=
    if let some (gR, dR, sR, pR, depR, rwR, fiR) := reenterAfterRewind? then
      let mergedFi := mergeFromEventIdx carriedOutIdx? fiR
      (gR, dR, sR, pR, depR, rwR, outerAfter?, !deferPlayFromExileLogs, mergedFi)
    else
      let wasPaused := g.sbaPaused
      let hasPendingLosers :=
        !g.over && !wasPaused && g.players.any (fun r => r.lost && !r.leftTheGame)
      let skipForOpenResolvingBatch :=
        g.currentBatch.isSome && !wasPaused && !g.openBatchAwaitedPausePrompt
      let (g, didSba) :=
        if hasPendingLosers || skipForOpenResolvingBatch then (g, false)
        else
          g.checkSBACounted savedIn popOuterIn departedIn rewindProposalIn
            (deferRestore := deferRestore) (fromLeavesLoop := true)
            (fromEventIdx? := pfeIdxOpt)
      let didAny := didSba || clearedInvalidLegend
      if g.over then (g, didAny, none, false, departedIn, none, none, true, carriedOutIdx?)
      else if wasPaused && (savedIn.isSome || popOuterIn || !departedIn.isEmpty || rewindProposalIn.isSome) then
        let (g, popOuterIn, outerAfter?) :=
          if outerAfter?.isSome then
            let (gf, pof) := combineOuterContinuations g popOuterIn outerAfter? false
            (gf, pof, none)
          else (g, popOuterIn, outerAfter?)
        let (g, handled) :=
          if deferRestore then (g, false)
          else (chainOrMergeLeave g savedIn popOuterIn departedIn rewindProposalIn
            (fromEventIdx? := pfeIdxOpt), true)
        (g, didAny, savedIn, popOuterIn, departedIn, rewindProposalIn, outerAfter?, handled, carriedOutIdx?)
      else if g.pending != .none then
        let (g, handled) :=
          if !entryPaused && wasPaused && !deferRestore &&
              !(savedIn.isSome || popOuterIn || !departedIn.isEmpty || rewindProposalIn.isSome) then
            (chainOrMergeSba g (fromEventIdx? := pfeIdxOpt), true)
          else if !wasPaused && !deferRestore && g.sbaPaused && g.pendingReplacement.any contHasSbaOrLeave then
            (chainOrMergeSba g (fromEventIdx? := pfeIdxOpt), true)
          else
            (g, false)
        (g, didAny, savedIn, popOuterIn, departedIn, rewindProposalIn, outerAfter?, handled, carriedOutIdx?)
      else
        let leftBefore := (g.players.filter (·.leftTheGame)).size
        let (g, saved?, popOuter, departed, rewindProposal) :=
          g.leavePlayersWhoLostCore savedIn popOuterIn departedIn rewindProposalIn
            (flushDismissed := false) (deferPlayFromExileLogs := true)
        let anyLeft := (g.players.filter (·.leftTheGame)).size > leftBefore
        if g.over then (g, didAny || anyLeft, none, false, departed, none, none, true, carriedOutIdx?)
        else
        let needFoldOuter :=
          outerAfter?.isSome &&
            (deferRestore || saved?.isSome || popOuter || rewindProposal.isSome ||
              (g.sbaPaused &&
                (g.players.any (fun r => r.lost && !r.leftTheGame) || !departed.isEmpty)))
        let (g, popOuter, outerAfter?) :=
          if needFoldOuter then
            let (gf, pof) := combineOuterContinuations g popOuter outerAfter? false
            (gf, pof, none)
          else
            (g, popOuter, outerAfter?)
        if g.sbaPaused then
          let (g, handled) :=
            if deferRestore then (g, false)
            else if g.players.any (fun r => r.lost && !r.leftTheGame) || saved?.isSome || popOuter ||
                !departed.isEmpty || rewindProposal.isSome then
              (chainOrMergeLeave g saved? popOuter departed rewindProposal
                (fromEventIdx? := pfeIdxOpt), true)
            else
              (chainOrMergeSba g (fromEventIdx? := pfeIdxOpt), true)
          (g, true, saved?, popOuter, departed, rewindProposal, outerAfter?, handled, carriedOutIdx?)
        else if g.pending != .none then
          (g, didAny || anyLeft, saved?, popOuter, departed, rewindProposal, outerAfter?, false, carriedOutIdx?)
        else if didSba || anyLeft || hasPendingLosers then
          let (g', didMore, saved'?, popOuter', departed', rewindProposal', fi') :=
            g.checkSBACountedWithLeavesCoreWithIdx saved? popOuter departed rewindProposal
              (deferRestore := deferRestore) (outerAfterIn? := outerAfter?)
              (fromEventIdx? := if deferPlayFromExileLogs then carriedOutIdx? else some effFromIdx)
              (deferPlayFromExileLogs := deferPlayFromExileLogs)
          let mergedFi := mergeFromEventIdx carriedOutIdx? fi'
          (g', didAny || anyLeft || didMore, saved'?, popOuter', departed', rewindProposal',
            none, !deferPlayFromExileLogs, mergedFi)
        else if deferRestore then
          (g, didAny, saved?, popOuter, departed, rewindProposal, outerAfter?, false, carriedOutIdx?)
        else
          let g :=
            if deferPlayFromExileLogs || g.over then g
            else emitExpiredPlayFromExileLogs preSba g effFromIdx
          (g.restoreSavedPostLeave saved? popOuter
             (departed := departed) (rewindProposal := rewindProposal),
           didAny, none, false, departed, none, outerAfter?, true, carriedOutIdx?)
  let gOut :=
    if handledPfeLogs || deferPlayFromExileLogs || gOut.over then gOut
    else emitExpiredPlayFromExileLogs preSba gOut effFromIdx
  let gOut :=
    if gOut.over then gOut
    else
      match outerAfter? with
      | some outer => gOut.chainPendingReplacement outer
      | none => gOut
  (gOut, didOut, sOut, poOut, depOut, rwOut, outFromIdx?)

/-- Core of `checkSBACountedWithLeaves`: repeats `checkSBACounted` and
`leavePlayersWhoLostCore` until neither performs an action or the game ends /
pauses on a pending choice, returning the updated `(g, didSba, saved?, popOuter,
departed, rewindProposal)` tuple. When `deferRestore` is `true`, suppresses
internal `.leavePlayersWhoLost` / `.checkSBA` chaining on pause and skips
`restoreSavedPostLeave` at fixpoint completion so callers such as
`finishConcedePriority` own post-SBA restoration (CR 104.5 / 704.3 / 800.4a). -/
def checkSBACountedWithLeavesCore (g : Game)
    (savedIn : Option Pending := none) (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none)
    (deferRestore : Bool := false)
    (outerAfterIn? : Option PendingReplacement := none)
    (deferPlayFromExileLogs : Bool := deferRestore)
    (fromEventIdx? : Option Nat := none) :
    Game × Bool × Option Pending × Bool × Array PlayerId × Option Bool :=
  let (gOut, didOut, sOut, poOut, depOut, rwOut, _) :=
    g.checkSBACountedWithLeavesCoreWithIdx savedIn popOuterIn departedIn rewindProposalIn
      (deferRestore := deferRestore) (outerAfterIn? := outerAfterIn?)
      (deferPlayFromExileLogs := deferPlayFromExileLogs) (fromEventIdx? := fromEventIdx?)
  (gOut, didOut, sOut, poOut, depOut, rwOut)

/-- Repeat `checkSBACounted` and `leavePlayersWhoLostCore` until neither performs
an action or the game ends / pauses on a pending choice, restoring any deferred
saved pending decision once at the end of the fixpoint (CR 704.3 / 800.4a). -/
def checkSBACountedWithLeaves (g : Game)
    (savedIn : Option Pending := none) (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none)
    (fromEventIdx? : Option Nat := none) : Game × Bool × Array PlayerId :=
  let (g, didSba, _, _, departed, _) :=
    g.checkSBACountedWithLeavesCore savedIn popOuterIn departedIn rewindProposalIn
      (deferRestore := false) (fromEventIdx? := fromEventIdx?)
  (g, didSba, departed)

def checkSBA (g : Game) : Game :=
  (g.checkSBACountedWithLeaves).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3 / 603.3b,
514.3a). All triggered abilities wait until a player would receive priority. -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingTriggers.isEmpty

end Game
end Mtg.Engine
