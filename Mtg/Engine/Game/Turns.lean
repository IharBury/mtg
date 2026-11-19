import Mtg.Engine.Game.Combat

/-!
# Turn structure (CR 500 / 514)

End-of-turn and cleanup clearing (CR 514.2), discarding to maximum hand
size, expiring play permissions and until-next-turn effects, starting
the next turn, `beginStep`, and step advancement.
-/

namespace Mtg.Engine
namespace Game

/-- Duration of a continuous effect (CR 611.2). -/
private def effectDuration : ContinuousEffect → EffectDuration
  | .layered _ _ d | .playerRule _ _ d | .gameRule _ d
  | .replacement _ d | .prevention _ d | .permission _ _ d => d

/-- Emit deferred `"{name} can no longer be played from exile"` logs once all
simultaneously expiring continuous effects in a transition starting at `pre`
have ended, checking `hadPlayable` on `pre` and post-expiry permissions /
`mayCastExiledBySource` on `g` (CR 611.2). -/
private def emitExpiredPlayFromExileLogs (pre g : Game) (fromEventIdx : Nat) : Game :=
  let prevSlice := g.events.extract pre.events.size fromEventIdx
  let alreadyLoggedBefore (oid : ObjectId) : Bool := Id.run do
    for j in [0:prevSlice.size] do
      match prevSlice[j]! with
      | .rules _ (.continuousEffect (.expired _ (some (.permission _ (.playFromExile oid' _) _)))) _ _ =>
        if oid' == oid then
          match prevSlice[j + 1]? with
          | some (.engine _ (.logMsg m) _) =>
            if m.endsWith " can no longer be played from exile" then
              return true
          | _ => pure ()
      | _ => pure ()
    return false
  let slice := g.events.extract fromEventIdx g.events.size
  let expiredOids : Array ObjectId :=
    slice.foldl (fun acc ev =>
      match ev with
      | .rules _ (.continuousEffect (.expired _ (some (.permission _ (.playFromExile oid perm) _)))) _ _ =>
        if perm.fromAdventure || perm.whileExiled || acc.contains oid || alreadyLoggedBefore oid then acc
        else acc.push oid
      | _ => acc) #[]
  expiredOids.foldl (fun acc oid =>
    let hadPlayable :=
      (pre.findObject? oid).any fun o =>
        o.zone == .exile &&
          (!(pre.activePlayPermissions o).isEmpty ||
            pre.livingPlayers.any (fun pl => pre.mayCastExiledBySource pl.id o))
    match acc.findObject? oid with
    | some o =>
      if o.zone == .exile && hadPlayable &&
          (acc.activePlayPermissions o).isEmpty &&
          !acc.livingPlayers.any (fun pl => acc.mayCastExiledBySource pl.id o) then
        acc.logMsg s!"{acc.name o} can no longer be played from exile"
      else acc
    | none => acc) g

/-- Expire a `.playFromExile oid perm` continuous effect `eid` as part of a
turn/step transition starting at `pre`, logging `"{name} can no longer be played
from exile"` at most once for `oid` when `oid` had a playable permission in
`pre` and now has none (CR 611.2). -/
private def expirePlayFromExileEffect (pre g : Game) (eid : EffectId) (_oid : ObjectId)
    (cause : Option EventCause) (reconcileControl : Bool := true)
    (deferLogs : Bool := false) : Game :=
  if deferLogs then
    g.expireEffectById eid (cause := cause) (reconcileControl := reconcileControl)
      (preState? := some pre)
  else
    let fromIdx := g.events.size
    let g := g.expireEffectById eid (cause := cause) (reconcileControl := reconcileControl)
      (preState? := some pre)
    emitExpiredPlayFromExileLogs pre g fromIdx

/-- Expire every active continuous effect whose duration satisfies `pred`,
handling `.control` via `endControlEffectById` and `.copy` log messages (CR 611.2a). -/
def expireEffectsByDuration (g : Game) (pred : EffectId → EffectDuration → Bool)
    (cause : Option EventCause) : Game :=
  let pre := g
  let fromIdx := pre.events.size
  let ctrlEids := g.activeEffects.filterMap fun (eid, e) =>
    match e with
    | .layered _ (.control _) d => if pred eid d then some eid else none
    | _ => none
  let expCopyEids := g.activeEffects.filterMap fun (eid, e) =>
    match e with
    | .layered _ (.copy _) d => if pred eid d then some eid else none
    | _ => none
  let copyCandLogs : Array (ObjectId × CardDef) :=
    let candIds : Array ObjectId :=
      g.activeEffects.foldl (fun idsAcc (eid, e) =>
        if !expCopyEids.contains eid then idsAcc
        else
          match e with
          | .layered (.objects ids) (.copy _) _ =>
            ids.foldl (fun a id =>
              if a.contains id then a
              else if (g.findObject? id).any (fun o => o.zone == .battlefield) then a.push id
              else a) idsAcc
          | _ => idsAcc) #[]
    candIds.filterMap fun oid =>
      match pre.findObject? oid with
      | none => none
      | some preObj =>
        match (pre.activeLayer1CopyChain preObj (ignoreDurationFor := expCopyEids)).back? with
        | some (topEid, topCard) =>
          if expCopyEids.contains topEid then some (oid, topCard) else none
        | none => none
  let endingEmbIds0 : Array ObjectId :=
    g.activeEffects.foldl (fun acc (eid, e) =>
      match e with
      | .gameRule (.fraEmblem id) d =>
        if pred eid d && !acc.contains id then acc.push id else acc
      | _ => acc) #[]
  let endingEmbIds := g.expandTransitiveCommandEmblems endingEmbIds0
  let hasEmblem := !endingEmbIds.isEmpty
  let skipIds :=
    g.coDepartingIds endingEmbIds (endingCtrlEids := ctrlEids) (includePhasedOut := true)
  let g :=
    if ctrlEids.isEmpty && expCopyEids.isEmpty && !hasEmblem then g
    else
      g.endControlEffectsSimultaneously ctrlEids (cause := cause)
        (preState? := some pre) (extraSkipIds := skipIds)
        (preExpire := fun g0 =>
          let g1 :=
            expCopyEids.foldl (fun acc eid =>
              acc.expireEffectById eid (cause := cause) (reconcileControl := false)
                (preState? := some pre) (skipLogIds := skipIds)) g0
          let g1 :=
            copyCandLogs.foldl (fun acc2 (id, topCard) =>
              match acc2.findObject? id with
              | some o =>
                if o.zone == .battlefield && !skipIds.contains id then
                  acc2.logMsg s!"{acc2.name o} is no longer a copy of {topCard.name}"
                else acc2
              | none => acc2) g1
          g1.ceaseEndingFraEmblemsWhere pred (cause := cause) (reconcileControl := false)
            (preState? := some pre) (skipLogIds := skipIds))
  let g :=
    g.activeEffects.foldl (fun acc (eid, e) =>
      if !pred eid (effectDuration e) then acc
      else
        match e with
        | .permission _ (.playFromExile oid perm) _ =>
          if perm.fromAdventure || perm.whileExiled then acc
          else expirePlayFromExileEffect pre acc eid oid cause (deferLogs := true)
        | _ =>
          acc.expireEffectById eid (cause := cause) (preState? := some pre)) g
  emitExpiredPlayFromExileLogs pre g fromIdx

/-- Expire effects lasting until the end of `st` (CR 500.5). -/
def expireAtStepEnd (g : Game) (st : Step) : Game :=
  g.expireEffectsByDuration (fun _ d => d == .untilEndOfStepOrPhase (.step st))
    (some (.turnBased .expireAtStepEnd))

/-- Expire effects lasting until the end of `ph` or (for `.combat`) until end of combat
(CR 500.5 / 500.5a / 511.2). -/
def expireAtPhaseEnd (g : Game) (ph : Phase) : Game :=
  g.expireEffectsByDuration
    (fun _ d =>
      d == .untilEndOfStepOrPhase (.phase ph) ||
        (ph == .combat && d == .untilEndOfCombat))
    (some (.turnBased .expireAtStepEnd))

/-- Expire effects lasting until `ph` begins (CR 500.4). -/
def expireAtPhaseBegin (g : Game) (ph : Phase) : Game :=
  g.expireEffectsByDuration (fun _ d => d == .untilStepOrPhase (.phase ph))
    (some (.turnBased .expireAtStepBegin))

/-- Expire effects lasting until `st` begins (CR 500.4). -/
def expireAtStepBegin (g : Game) (st : Step) : Game :=
  g.expireEffectsByDuration (fun _ d => d == .untilStepOrPhase (.step st))
    (some (.turnBased .expireAtStepBegin))

/-- Record `TurnEvent.stepEnded st` and expire effects ending with `st` (CR 500.5). -/
def recordStepEnded (g : Game) (st : Step) : Game :=
  g.withBatch none fun g =>
    (g.record (GameEvent.stepEnded g.turnNumber st
      (cause := some (.gameRule .stepAdvance)))).expireAtStepEnd st

/-- Record `TurnEvent.phaseEnded ph` and expire effects ending with `ph` (CR 500.5 / 511.2). -/
def recordPhaseEnded (g : Game) (ph : Phase) : Game :=
  g.withBatch none fun g =>
    (g.record (GameEvent.phaseEnded g.turnNumber ph
      (cause := some (.gameRule .stepAdvance)))).expireAtPhaseEnd ph

/-- Record `TurnEvent.phaseBegan ph` and expire effects lasting until `ph` begins (CR 500.4). -/
def recordPhaseBegan (g : Game) (ph : Phase) : Game :=
  let hasExpiry := g.activeEffects.any (fun (_, e) => effectDuration e == .untilStepOrPhase (.phase ph))
  let body (g : Game) : Game :=
    (g.record (GameEvent.phaseBegan g.turnNumber ph
      (cause := some (.gameRule .stepAdvance)))).expireAtPhaseBegin ph
  if hasExpiry then g.withBatch none body else body g

/-- Record `TurnEvent.stepBegan st` and expire effects lasting until `st` begins (CR 500.4). -/
def recordStepBegan (g : Game) (st : Step) : Game :=
  let hasExpiry := g.activeEffects.any (fun (_, e) => effectDuration e == .untilStepOrPhase (.step st))
  let body (g : Game) : Game :=
    (g.record (GameEvent.stepped g.turnNumber st g.activePlayer)).expireAtStepBegin st
  if hasExpiry then g.withBatch none body else body g

/-- Expire play-from-exile permissions as `endingPlayer`'s turn ends (CR 611.2 /
800.4i / 805.4 / 810.2). -/
def expirePlayPermissions (g : Game) (endingPlayer : PlayerId)
    (cause : Option EventCause := some (.turnBased .cleanupClear))
    (preState? : Option Game := none)
    (deferLogs : Bool := false) : Game :=
  let pre := preState?.getD g
  let fromIdx := g.events.size
  let departed := cause == some (.turnBased .expireAtStepBegin)
  let g :=
    g.activeEffects.foldl (fun g (eid, e) =>
      match e with
      | .permission p (.playFromExile oid perm) d =>
        if perm.fromAdventure || perm.whileExiled then g
        else
          let grantee := p.getD perm.player
          let expires :=
            match d with
            | .untilEndOfTurn =>
              (departed && grantee == endingPlayer) ||
                (!departed && g.isSharedTurnFinalSeat &&
                  (grantee == endingPlayer || g.areTeammates grantee endingPlayer))
            | .untilEndOfNextTurnOf q =>
              if departed then
                !(g.teamMembers endingPlayer).any g.stillInGame &&
                  (q == endingPlayer || g.areTeammates q endingPlayer)
              else
                (q == endingPlayer || g.areTeammates q endingPlayer) &&
                  g.isSharedTurnFinalSeat && g.hasTurnBegunSince eid q
            | _ => false
          if expires then expirePlayFromExileEffect pre g eid oid cause (deferLogs := true)
          else g
      | _ => g) g
  if deferLogs then g else emitExpiredPlayFromExileLogs pre g fromIdx

/-- Clear “once each turn” activation counts and `"this turn"` / `"until end of turn"`
player rules, permissions, and delayed triggers as a turn ends (CR 514.2 / 805.4 / 810.2). -/
def clearTurnActivations (g : Game) : Game :=
  if !g.isSharedTurnFinalSeat then g
  else
    let cause := some (EventCause.turnBased .cleanupClear)
    Id.run do
      let mut g := g
      g := g.expireAll .powerUpsForbiddenThisTurn (cause := cause)
      g := g.expireMatching (fun | .playerRule _ .pendingFreeRGCreature .untilEndOfTurn => true | _ => false) (cause := cause)
      -- Stingcaster Mage: flashback granted until end of turn ends.
      g := g.expireMatching (fun
        | .permission _ (.flashback _) .untilEndOfTurn => true
        | _ => false) (cause := cause)
      for pl in g.players do
        if !g.stillInGame pl.id then
          -- Keep last-known this-turn info until that turn would have begun
          -- (CR 800.4i).
          pure ()
        else do
          g := g.expireMatching (fun
            | .playerRule p (.additionalLands _) .untilEndOfTurn
            | .playerRule p .jaceLoyaltyAtInstantSpeed .untilEndOfTurn
            | .playerRule p .legendRuleOff .untilEndOfTurn
            | .playerRule p (.mountainExtraRed _) .untilEndOfTurn
            | .playerRule p (.cantAttackJaces _) .untilEndOfTurn
            | .playerRule p .cantCastSpells .untilEndOfTurn
            | .playerRule p .nextSpellCantBeCountered .untilEndOfTurn
            | .playerRule p (.typeSpellCostLess _ _) .untilEndOfTurn
            | .playerRule p (.supertypeSpellCostLess _ _) .untilEndOfTurn
            | .playerRule p .lifeLocked .untilEndOfTurn
            | .playerRule p (.controlsPlayer _ false) .untilEndOfTurn => p == pl.id
            | _ => false) (cause := cause)
      let expiredDt := g.delayedTriggers.filter (fun dt =>
        g.stillInGame dt.controller &&
        (match dt.kind with
         | .attackPumpPerPlains
         | .copyNextInstantSorceryThisTurn
         | .lokiCopyNextInstantSorceryThisTurn _ _ => true
         | _ => false))
      for dt in expiredDt do
        g := g.record (GameEvent.delayedTriggerExpired g.turnNumber dt (.turnBased .cleanupClear))
      return g

def clearEOT (g : Game) : Game :=
  if !g.isSharedTurnFinalSeat then g
  else
    g.withBatch none fun g =>
      let cause := some (EventCause.turnBased .cleanupClear)
      Id.run do
        let mut g := g
        g := g.expireAll .creaturesWithoutFlyingCantBlockUntilEot (cause := cause)
        g := g.expireAll .powerUpsForbiddenThisTurn (cause := cause)
        g := g.expireMatching (fun | .playerRule _ .assignCombatDamageEqualToughness .untilEndOfTurn => true | _ => false)
          (cause := cause)
        g := g.expireMatching (fun
          | .replacement _ .untilEndOfTurn | .prevention _ .untilEndOfTurn => true
          | _ => false) (cause := cause)
        -- Each control-changing effect ends or counts down on its own across all
        -- ObjectScopes, while all simultaneously ending control/copy effects share
        -- one pre-expiry controller snapshot (CR 514.2 / 613.7 / 800.4c).
        let ctrlEids := g.activeEffects.filterMap fun (eid, e) =>
          match e with
          | .layered _ (.control _) .untilEndOfTurn => some eid
          | .layered _ (.control _) (.untilEndOfNextTurnOf q) =>
            if (q == g.activePlayer || g.areTeammates q g.activePlayer) &&
                g.isSharedTurnFinalSeat && g.hasTurnBegunSince eid q then
              some eid
            else none
          | _ => none
        let endingEmbIds0 : Array ObjectId :=
          g.activeEffects.foldl (fun acc (eid, e) =>
            match e with
            | .gameRule (.fraEmblem id) .untilEndOfTurn =>
              if !acc.contains id then acc.push id else acc
            | .gameRule (.fraEmblem id) (.untilEndOfNextTurnOf q) =>
              if (q == g.activePlayer || g.areTeammates q g.activePlayer) &&
                  g.isSharedTurnFinalSeat && g.hasTurnBegunSince eid q &&
                  !acc.contains id then
                acc.push id
              else acc
            | _ => acc) #[]
        let endingEmbIds := g.expandTransitiveCommandEmblems endingEmbIds0
        let pre := g
        let fromIdx := pre.events.size
        let skipIds :=
          g.coDepartingIds endingEmbIds (endingCtrlEids := ctrlEids) (includePhasedOut := true)
        g := g.endControlEffectsSimultaneously ctrlEids (cause := cause)
          (extraSkipIds := skipIds)
          (preExpire := fun g0 =>
            let g0 := g0.restoreCopiesUntilEot (reconcileControl := false) (skipLogIds := skipIds)
            let g0 := g0.ceaseEndingFraEmblemsWhere
              (fun eid d =>
                match d with
                | .untilEndOfNextTurnOf q =>
                  (q == pre.activePlayer || pre.areTeammates q pre.activePlayer) &&
                    pre.isSharedTurnFinalSeat && pre.hasTurnBegunSince eid q
                | _ => false)
              (cause := cause) (reconcileControl := false) (preState? := some pre)
              (skipLogIds := skipIds)
            g0.ceaseEndingFraEmblemsWhere (fun _ d => d == .untilEndOfTurn)
              (cause := cause) (reconcileControl := false) (preState? := some pre)
              (skipLogIds := skipIds))
          (preState? := some pre)
        g := g.expirePlayPermissions g.activePlayer (cause := cause) (preState? := some pre)
          (deferLogs := true)
        for pl in g.players do
          if pl.id != g.activePlayer && g.stillInGame pl.id then
            g := g.activeEffects.foldl (fun g (eid, e) =>
              match e with
              | .permission p (.playFromExile oid perm) .untilEndOfTurn =>
                if perm.fromAdventure || perm.whileExiled || p.getD perm.player != pl.id then g
                else expirePlayFromExileEffect pre g eid oid cause (deferLogs := true)
              | _ => g) g
        g := g.clearTurnActivations
        for o in g.battlefield do
          -- Ending a control effect can exile the permanent (CR 800.4c).
          match g.findObject? o.id with
          | none => pure ()
          | some cur =>
            g := g.expireObjectUntilEotEffects cur
        g := g.activeEffects.foldl (fun acc (eid, e) =>
          match e with
          | .layered _ (.copy ..) _ | .layered _ (.control _) _
          | .permission _ (.playFromExile ..) _ => acc
          | _ =>
            match effectDuration e with
            | .untilEndOfNextTurnOf q =>
              if (q == acc.activePlayer || acc.areTeammates q acc.activePlayer) &&
                  acc.isSharedTurnFinalSeat && acc.hasTurnBegunSince eid q then
                acc.expireEffectById eid (cause := cause)
              else acc
            | _ => acc) g
        g := g.expireMatching (fun
          | .layered _ (.copy ..) _ | .layered _ (.control _) _ => false
          | .layered _ _ .untilEndOfTurn | .gameRule _ .untilEndOfTurn => true
          | _ => false) (cause := cause)
        g := emitExpiredPlayFromExileLogs pre g fromIdx
        -- CR 514.2 / 702.26d: remove marked damage from all permanents, including phased-out ones.
        let damagedIds :=
          (g.objects.filter (fun o => o.zone == .battlefield && o.status.damage != 0)).map (·.id)
        if !damagedIds.isEmpty then
          g := g.record (GameEvent.damageMarkedCleared g.turnNumber damagedIds
            (cause := .turnBased .cleanupClear))
        return g

/-- Discard `ids` during cleanup (CR 514.1), pausing and chaining
`.finishPostStep .discardCleanupIds` if a discard replacement opens
`Pending.chooseReplacement`. -/
def discardCleanupIds (g : Game) (p : PlayerId) (ids : Array ObjectId) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.finishPostStep (.discardCleanupIds p ids))
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    let pl := g.player p
    if pl.hand.contains id then
      let card := g.object! id
      let name := g.name card
      let owner := card.owner
      let (g', _) := g.move id (.graveyard owner) none (verb := some .discard) (actor := some p)
        (cause := some (.turnBased .cleanupDiscard))
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        g := g.chainPendingReplacement (.finishPostStep (.discardCleanupIds p rem (some (id, owner))))
        return g
      if (g.followMovedToZone? id (· == .graveyard owner)).isSome then
        g := g.logMsg s!"{pl.name} discards {name} (cleanup)"
  return g

/-- Discard down to maximum hand size (CR 514.1). This turn-based action does
not use the stack; the engine discards from the back of the hand array. -/
def discardToMaxHandSize (g : Game) : Game :=
  let pl := g.player g.activePlayer
  let extra :=
    match g.effectiveMaxHandSize g.activePlayer with
    | some maxHandSize => pl.hand.size - maxHandSize
    | none => 0
  if extra == 0 then g
  else
    let ids := (pl.hand.extract (pl.hand.size - extra) pl.hand.size).reverse
    g.withBatch (some (.turnBased .cleanupDiscard)) fun g =>
      g.discardCleanupIds g.activePlayer ids

/-- End goad designations placed by `p` (or `p`'s teammate when `includeTeammates`
is true, CR 805.4 / 810.2) as `p`'s next turn begins (CR 701.15a). -/
def expireGoadedFor (g : Game) (p : PlayerId) (includeTeammates : Bool := false) : Game :=
  g.battlefield.foldl (fun g o =>
    let matching := o.status.goadedUntilNextTurnOf.filter fun q =>
      q == p || (includeTeammates && g.areTeammates q p)
    matching.foldl (fun acc q =>
      acc.record (GameEvent.designation acc.turnNumber (acc.snapshot (acc.object! o.id)) (.goaded q) false
        (cause := .turnBased .expireAtStepBegin))) g) g

/-- End Reality Fracture effects that last until `p`'s next turn: Garruk,
Veiled Butcher's toughness and power reduction and the command-zone effects of Jace, Reality Sculptor
and Garruk, Curse Breaker (CR 611.2a / 805.4 / 810.2). -/
def expireFraUntilTurnEffects (g : Game) (p : PlayerId) (includeTeammates : Bool := false)
    (skipControl : Bool := false) (skipLogIds : Array ObjectId := #[])
    (preState? : Option Game := none)
    (deferLogs : Bool := false) : Game :=
  let pre := preState?.getD g
  let fromIdx := g.events.size
  let matchesTurnOf (q : PlayerId) : Bool :=
    q == p || (includeTeammates && g.areTeammates q p)
  let cause := some (EventCause.turnBased .expireAtStepBegin)
  let ctrlEids :=
    if skipControl then #[]
    else
      g.activeEffects.filterMap fun (eid, e) =>
        match e with
        | .layered _ (.control _) (.untilNextTurnOf q) =>
          if matchesTurnOf q then some eid else none
        | _ => none
  let endingEmbIds0 : Array ObjectId :=
    g.activeEffects.foldl (fun acc (_, e) =>
      match e with
      | .gameRule (.fraEmblem id) (.untilNextTurnOf q) =>
        if matchesTurnOf q && !acc.contains id then acc.push id else acc
      | _ => acc) #[]
  let endingEmbIds := g.expandTransitiveCommandEmblems endingEmbIds0
  let effSkipIds :=
    let base :=
      if skipControl then #[]
      else g.coDepartingIds endingEmbIds (endingCtrlEids := ctrlEids) (includePhasedOut := true)
    skipLogIds.foldl (fun acc id => if acc.contains id then acc else acc.push id) base
  let expireNonControl (g0 : Game) : Game :=
    let g0 :=
      g0.ceaseEndingFraEmblemsWhere
        (fun _ d => match d with | .untilNextTurnOf q => matchesTurnOf q | _ => false)
        (cause := cause) (reconcileControl := false) (preState? := some pre)
        (skipLogIds := effSkipIds)
    g0.activeEffects.foldl (fun acc (eid, e) =>
      match e with
      | .layered _ (.copy ..) _ | .layered _ (.control _) _
      | .playerRule _ .protectionFromEverything _
      | .playerRule _ .lifeCantChange _ => acc
      | .permission _ (.playFromExile oid perm) (.untilNextTurnOf q) =>
        if perm.fromAdventure || perm.whileExiled || !matchesTurnOf q then acc
        else expirePlayFromExileEffect pre acc eid oid cause (reconcileControl := false)
          (deferLogs := true)
      | e =>
        match effectDuration e with
        | .untilNextTurnOf q =>
          if matchesTurnOf q then
            acc.expireEffectById eid (cause := cause) (reconcileControl := false)
              (preState? := some pre)
          else acc
        | _ => acc) g0
  let g :=
    if skipControl then
      expireNonControl g
    else
      g.endControlEffectsSimultaneously ctrlEids (cause := cause)
        (extraSkipIds := effSkipIds)
        (preExpire := expireNonControl) (preState? := some pre)
  if deferLogs then g else emitExpiredPlayFromExileLogs pre g fromIdx

/-- Expire effects that last until `p`'s next turn (CR 800.4m) and clear
that player's last-turn information (CR 800.4i). -/
def expireUntilNextTurnEffects (g : Game) (p : PlayerId) : Game :=
  if g.over then g
  else
  g.withBatch none fun g =>
    let cause := some (EventCause.turnBased .expireAtStepBegin)
    let teamHasLiving := g.players.any (fun m => g.stillInGame m.id && g.areTeammates p m.id)
    let matchesDeparted (q : PlayerId) : Bool :=
      q == p || (!teamHasLiving && g.areTeammates q p)
    let targets : Array PlayerId :=
      if teamHasLiving then #[p] else g.teamMembers p
    let g :=
      if teamHasLiving then g
      else targets.foldl (fun acc t => acc.expireGoadedFor t) g
    let pre := g
    let fromIdx := pre.events.size
    let g :=
      if teamHasLiving then g
      else
        let ctrlEids := g.activeEffects.filterMap fun (eid, e) =>
          match e with
          | .layered _ (.control _) (.untilNextTurnOf q)
          | .layered _ (.control _) (.untilEndOfNextTurnOf q) =>
            if matchesDeparted q then some eid else none
          | _ => none
        let endingEmbIds0 : Array ObjectId :=
          g.activeEffects.foldl (fun acc (_, e) =>
            match e with
            | .gameRule (.fraEmblem id) (.untilNextTurnOf q)
            | .gameRule (.fraEmblem id) (.untilEndOfNextTurnOf q) =>
              if matchesDeparted q && !acc.contains id then acc.push id else acc
            | _ => acc) #[]
        let endingEmbIds := g.expandTransitiveCommandEmblems endingEmbIds0
        let skipIds :=
          g.coDepartingIds endingEmbIds (endingCtrlEids := ctrlEids) (includePhasedOut := true)
        let expireNonControl (g0 : Game) : Game :=
          let g0 := g0.restoreCopiesUntilNextTurn p (departed := true) (reconcileControl := false)
            (skipLogIds := skipIds)
          let g0 := g0.expireFraUntilTurnEffects p
            (includeTeammates := !teamHasLiving) (skipControl := true)
            (skipLogIds := skipIds) (preState? := some pre) (deferLogs := true)
          let g0 :=
            g0.ceaseEndingFraEmblemsWhere
              (fun _ d => match d with | .untilEndOfNextTurnOf q => matchesDeparted q | _ => false)
              (cause := cause) (reconcileControl := false) (preState? := some pre)
              (skipLogIds := skipIds)
          let g0 := g0.expireMatching (fun
            | .layered _ (.copy ..) _ | .layered _ (.control _) _
            | .permission _ (.playFromExile ..) _ => false
            | e =>
              match effectDuration e with
              | .untilEndOfNextTurnOf q => matchesDeparted q
              | _ => false) (cause := cause) (reconcileControl := false) (preState? := some pre)
          targets.foldl (fun acc t =>
            let acc :=
              if acc.hasActiveEffect (.protectionFromEverything t) then
                acc.expireMatching (· == .protectionFromEverything t) (cause := cause)
                  (reconcileControl := false) (preState? := some pre)
                  |>.logMsg
                    s!"{(acc.player t).name}'s protection from everything ends (CR 800.4m)"
              else acc
            acc.expireMatching (· == .lifeCantChange t) (cause := cause)
              (reconcileControl := false) (preState? := some pre)) g0
        g.endControlEffectsSimultaneously ctrlEids (cause := cause)
          (extraSkipIds := skipIds)
          (preExpire := expireNonControl) (preState? := some pre)
    let g := targets.foldl (fun acc t =>
      acc.expirePlayPermissions t (cause := cause) (preState? := some pre) (deferLogs := true)) g
    let g := g.expireMatching (fun
      | .playerRule q (.additionalLands _) .untilEndOfTurn
      | .playerRule q .jaceLoyaltyAtInstantSpeed .untilEndOfTurn
      | .playerRule q .legendRuleOff .untilEndOfTurn
      | .playerRule q (.mountainExtraRed _) .untilEndOfTurn
      | .playerRule q (.cantAttackJaces _) .untilEndOfTurn
      | .playerRule q .cantCastSpells .untilEndOfTurn
      | .playerRule q .nextSpellCantBeCountered .untilEndOfTurn
      | .playerRule q .lifeLocked .untilEndOfTurn
      | .playerRule q (.typeSpellCostLess _ _) .untilEndOfTurn
      | .playerRule q (.supertypeSpellCostLess _ _) .untilEndOfTurn => matchesDeparted q
      | .playerRule q (.controlsPlayer them false) .untilEndOfTurn =>
        matchesDeparted q || ((them == p || g.areTeammates them p) && !teamHasLiving)
      | .playerRule q (.controlsPlayer them true) _ =>
        matchesDeparted q || ((them == p || g.areTeammates them p) && !teamHasLiving)
      | _ => false) (cause := cause)
    let g := emitExpiredPlayFromExileLogs pre g fromIdx
    let expiredDt := g.delayedTriggers.filter (fun dt =>
      (match dt.kind with
       | .attackPumpPerPlains
       | .copyNextInstantSorceryThisTurn
       | .lokiCopyNextInstantSorceryThisTurn _ _ => true
       | _ => false) && matchesDeparted dt.controller)
    expiredDt.foldl (fun g dt =>
      g.record (GameEvent.delayedTriggerExpired g.turnNumber dt (.turnBased .expireAtStepBegin))) g

/-- Pending extra-turn causes reconstructed from `g.events`, aligned with `g.extraTurns`
(including CR 805.8 team extra turns). -/
private def pendingExtraTurnCauses (g : Game) : Array EventCause :=
  let dropLost (stk : Array (PlayerId × EventCause)) (lost : Array PlayerId) :
      Array (PlayerId × EventCause) :=
    (stk.toList.dropWhile (fun (p, _) => lost.contains p)).toArray
  let updateLost (lost : Array PlayerId) (p : PlayerId) (isLost : Bool) : Array PlayerId :=
    if isLost then (if lost.contains p then lost else lost.push p)
    else lost.filter (· != p)
  let (stk, _, _, _) := g.events.foldl
    (fun ((stk, lost, seats, seatsExtra) :
        Array (PlayerId × EventCause) × Array PlayerId × Array PlayerId × Bool) e =>
      match e.change with
      | .engine (.startingPlayer v) =>
        (stk, lost, #[v], false)
      | .rules (.player (.lost p _)) | .rules (.player (.leftGame p)) =>
        (stk, updateLost lost p true, seats, seatsExtra)
      | .engine (.addPlayer pl) =>
        (stk, updateLost lost pl.id (pl.lost || pl.leftTheGame), seats, seatsExtra)
      | .rules (.turn (.extraTurnAdded p _)) =>
        match e.cause? with
        | some c =>
          let team := (g.teamMembers p).map (fun q => (q, c))
          let inProgress :=
            g.countInProgressSharedExtraSeats seats seatsExtra (stk.map Prod.fst)
          let stk' := stk.extract 0 inProgress ++ team ++ stk.extract inProgress stk.size
          (stk', lost, seats, seatsExtra)
        | none => (stk, lost, seats, seatsExtra)
      | .rules (.turn (.turnBegan p extra)) =>
        let sameShared :=
          extra == seatsExtra && !seats.isEmpty &&
            g.areTeammates seats[0]! p && !seats.contains p
        let seats' := if sameShared then seats.push p else #[p]
        if extra then
          let trimmed := dropLost stk lost
          let next :=
            if (trimmed[0]?.map Prod.fst) == some p then trimmed.extract 1 trimmed.size
            else trimmed
          (next, lost, seats', true)
        else if sameShared then
          (stk, lost, seats', false)
        else
          (dropLost stk lost, lost, seats', false)
      | _ => (stk, lost, seats, seatsExtra))
    (#[], #[], #[⟨0⟩], false)
  stk.map Prod.snd

/-- Whether `st` is the first step of its phase (CR 500.1). -/
private def isPhaseStartStep : Step → Bool
  | .untap | .precombatMain | .beginningOfCombat | .postcombatMain | .end => true
  | _ => false

/-- Untap each remaining permanent in `ids` during the active player's untap step
(CR 502.3), pausing on `Pending.chooseReplacement` (`PendingReplacement.untapStepPermanents`)
when competing `.stunCounterUntap` replacement effects tie (CR 122.1d / 616.1). -/
def untapStepPermanents (g : Game) (ids : Array ObjectId) : Game :=
  let ap := g.activePlayer
  let apName := (g.player ap).name
  let baseCause := EventCause.turnBased .untapAll
  Id.run do
    let mut g := g
    let mut idx := 0
    while idx < ids.size do
      let oid := ids[idx]!
      idx := idx + 1
      match g.findObject? oid with
      | none => pure ()
      | some o =>
        -- CR 502.3: the active player untaps their permanents. Logging each
        -- previously tapped permanent makes the battlefield status change
        -- visible in the demo before the zone reprint.
        let skipUntap :=
          !o.isOnBattlefield || !g.controlledBy o ap ||
          ((g.staticAbilities o).any StaticAbility.doesntUntapUnlessEnduringStory? &&
            !g.hasEnduringStory ap) ||
          (g.staticAbilities o).any (· == .fra .doesntUntap) ||
          g.hostCantBecomeUntapped o ||
          g.hostSkipsUntapStep o
        if o.status.tapped && !skipUntap then
          let untap := GameEvent.untapped g.turnNumber (g.snapshot o) (cause := baseCause)
          -- CR 122.1d: a stun counter is removed instead of untapping via the CR 616.1 loop.
          let (stunned, applied, cause', choice?) := g.replaceUntap o (cause := some baseCause)
          match choice? with
          | some (chooser, choices) =>
            let rest := ids.extract (idx - 1) ids.size
            g := g.promptChooseReplacement chooser choices (.untapStepPermanents rest)
            idx := ids.size
          | none =>
            g := g.consumeReplacementOrder applied
            if stunned then
              let oName := g.name o
              g := g.logMsg s!"A stun counter is removed from {oName} instead of untapping it"
              g := g.recordRemoveCounters o.id .stun 1 (byPlayer := some ap)
                (cause := some (cause'.getD baseCause))
            else
              g := g.logMsg s!"{apName} untaps {g.name o}"
              if untap.watches .wouldUntap then
                g := g.record untap
    return g

private def expireFinishedNextTurnPlayerControl (g : Game) : Game :=
  let cause := some (EventCause.turnBased .expireAtStepBegin)
  let expiredCtrl := g.activeEffects.filter fun (eid, e) =>
    match e with
    | .playerRule _ (.controlsPlayer them true) _ => g.hasTurnAfterBegunSince eid them
    | _ => false
  if expiredCtrl.isEmpty then g
  else
    g.withBatch none fun g =>
      expiredCtrl.foldl (fun acc (eid, _) => acc.expireEffectById eid (cause := cause)) g

/-- Count of queued extra-turn seats belonging to the currently active shared extra turn
(CR 805.8). -/
private def sharedTurnInProgressExtraSeats (g : Game) (seats : Array PlayerId)
    (seatsExtra : Bool) : Nat :=
  g.countInProgressSharedExtraSeats seats seatsExtra g.extraTurns

mutual

/-- Resume `startNextTurn` across departed-player `expireUntilNextTurnEffects` pauses
(CR 800.4k / 800.4m), optionally entering `beginTurn` once `turnBegan` is recorded. -/
partial def continueStartNextTurn (g : Game) (nextP : PlayerId)
    (remainingDeparted : Array PlayerId) (runBeginTurn : Bool := false)
    (alreadyExpired : Array PlayerId := #[]) : Game := Id.run do
  if g.over then
    return g
  let mut g := g
  let mut alreadyExpired := alreadyExpired
  for i in [0:remainingDeparted.size] do
    let dep := remainingDeparted[i]!
    if !alreadyExpired.contains dep then
      if !(g.teamMembers dep).any g.stillInGame then
        for m in g.teamMembers dep do
          if !alreadyExpired.contains m then
            alreadyExpired := alreadyExpired.push m
      else
        alreadyExpired := alreadyExpired.push dep
      g := g.expireUntilNextTurnEffects dep
      if g.over then
        return g
      let paused :=
        match g.pending with
        | .chooseReplacement .. | .chooseLegend .. => true
        | _ => g.pendingReplacement.isSome
      if paused then
        let rem := remainingDeparted.extract (i + 1) remainingDeparted.size
        return g.chainPendingReplacement
          (.continueStartNextTurn nextP rem runBeginTurn alreadyExpired)
  let (seats, seatsExtra) := g.currentSharedTurnState
  let midRegularShared := !seatsExtra && !g.isSharedTurnFinalSeat
  let inProgressExtraSeats := sharedTurnInProgressExtraSeats g seats seatsExtra
  let pendingExtraCauses := pendingExtraTurnCauses g
  let lastReg := g.lastRegularTurnSeat
  let regEnd := (g.teamMembers lastReg).back? |>.getD lastReg
  let (targetP, targetExtra) : PlayerId × Bool := Id.run do
    if !midRegularShared then
      let mut sIdx := 0
      while sIdx < g.extraTurns.size && !g.stillInGame g.extraTurns[sIdx]! do
        sIdx := sIdx + 1
      if let some q := (g.extraTurns.extract sIdx g.extraTurns.size)[0]? then
        return (q, true)
    let n := g.players.size
    let fromExtra := !midRegularShared && g.extraTurns.contains nextP
    if fromExtra || !g.stillInGame nextP then
      let startIdx := if fromExtra then regEnd.idx + 1 else nextP.idx
      for k in [0:n] do
        let q : PlayerId := ⟨(startIdx + k) % n⟩
        if g.stillInGame q then
          return (q, false)
    return (nextP, false)
  let sameShared :=
    g.stillInGame targetP && targetExtra == seatsExtra && !seats.isEmpty &&
      g.areTeammates seats[0]! targetP && !seats.contains targetP
  let endingCurrentRegularShared (q : PlayerId) : Bool :=
    !seatsExtra && !sameShared && seats.any (fun s => s == q || g.areTeammates s q)
  let endingCurrentExtraShared (q : PlayerId) : Bool :=
    seatsExtra && !sameShared && seats.any (fun s => s == q || g.areTeammates s q)
  let mut skipIdx := 0
  let mut unexpiredExtra : Array PlayerId := #[]
  if !midRegularShared then
    while skipIdx < g.extraTurns.size && !g.stillInGame g.extraTurns[skipIdx]! do
      let d := g.extraTurns[skipIdx]!
      let extraSeatEnding :=
        seatsExtra && !sameShared && skipIdx < inProgressExtraSeats
      if !extraSeatEnding && !alreadyExpired.contains d && !unexpiredExtra.contains d then
        unexpiredExtra := unexpiredExtra.push d
      skipIdx := skipIdx + 1
  let nextExtra? :=
    if midRegularShared then none
    else (g.extraTurns.extract skipIdx g.extraTurns.size)[0]?
  if !sameShared && g.stillInGame targetP then
    for tm in g.teamMembers targetP do
      if !g.stillInGame tm &&
          !alreadyExpired.contains tm && !unexpiredExtra.contains tm then
        unexpiredExtra := unexpiredExtra.push tm
  if (!g.stillInGame nextP || !unexpiredExtra.isEmpty) && !g.over &&
      g.players.any (fun pl => g.stillInGame pl.id) then
    match nextExtra? with
    | some q =>
      if q != nextP || !unexpiredExtra.isEmpty then
        return g.continueStartNextTurn q unexpiredExtra runBeginTurn alreadyExpired
    | none =>
      let n := g.players.size
      let fromExtra := !midRegularShared && g.extraTurns.contains nextP
      let appendDepartedTeammates (base : Array PlayerId) (q : PlayerId) : Array PlayerId :=
        if !sameShared then
          (g.teamMembers q).foldl (fun acc tm =>
            if !g.stillInGame tm &&
                !alreadyExpired.contains tm && !acc.contains tm then
              acc.push tm
            else acc) base
        else base
      let (nextP', newlyDeparted) := Id.run do
        let mut newly := unexpiredExtra
        if fromExtra then
          if !endingCurrentExtraShared nextP && !alreadyExpired.contains nextP &&
              !newly.contains nextP then
            newly := newly.push nextP
          for k in [1:n+1] do
            let q : PlayerId := ⟨(regEnd.idx + k) % n⟩
            if !g.stillInGame q then
              if !endingCurrentRegularShared q && !alreadyExpired.contains q && !newly.contains q then
                newly := newly.push q
            else
              return (q, appendDepartedTeammates newly q)
          return (regEnd, newly)
        else
          for k in [0:n] do
            let q : PlayerId := ⟨(nextP.idx + k) % n⟩
            if !g.stillInGame q then
              if !endingCurrentRegularShared q && !alreadyExpired.contains q && !newly.contains q then
                newly := newly.push q
            else
              return (q, appendDepartedTeammates newly q)
          return (nextP, newly)
      if g.stillInGame nextP' && (nextP' != nextP || !newlyDeparted.isEmpty) then
        return g.continueStartNextTurn nextP' newlyDeparted runBeginTurn alreadyExpired
  let (gNext, didBeginTurn) : Game × Bool :=
    match nextExtra? with
    | some q =>
      let extraCause? := (pendingExtraCauses.extract skipIdx pendingExtraCauses.size)[0]?
      let sameShared :=
        seatsExtra && !seats.isEmpty && g.areTeammates seats[0]! q && !seats.contains q
      let nextTurnNum := if sameShared then g.turnNumber else g.turnNumber + 1
      let g := g.record (GameEvent.turnBegan nextTurnNum q (extra := true))
      let g := g.expireFinishedNextTurnPlayerControl
      let g := g.change (.cleanupGivesPriority false)
      let g :=
        if !g.powerUpsForbidden then
          let cause := extraCause? <|> some (.gameRule .continuousEffect)
          g.createEffect .powerUpsForbiddenThisTurn (cause := cause)
        else g
      (g.logMsg s!"It is now {(g.player q).name}'s extra turn {g.turnNumber}", true)
    | none =>
      if g.stillInGame nextP then
        let sameShared :=
          !seatsExtra && !seats.isEmpty &&
            g.areTeammates seats[0]! nextP && !seats.contains nextP
        let nextTurnNum := if sameShared then g.turnNumber else g.turnNumber + 1
        let g := g.record (GameEvent.turnBegan nextTurnNum nextP (extra := false))
        let g := g.expireFinishedNextTurnPlayerControl
        let g := g.change (.cleanupGivesPriority false)
        (g.logMsg s!"It is now {(g.player nextP).name}'s turn {g.turnNumber}", true)
      else (g, false)
  if runBeginTurn && didBeginTurn && !gNext.over && gNext.stillInGame gNext.activePlayer then
    gNext.beginTurn
  else gNext

partial def startNextTurnCore (g : Game) (runBeginTurn : Bool) : Game :=
  let ending := g.activePlayer
  let (seats, seatsExtra) := g.currentSharedTurnState
  let finalSeat := g.isSharedTurnFinalSeat
  let midRegularShared := !seatsExtra && !finalSeat
  let g :=
    if finalSeat then
      g.withBatch none fun g =>
        let cause := some (EventCause.turnBased .cleanupClear)
        let pre := g
        let fromIdx := pre.events.size
        let g := g.expirePlayPermissions ending (cause := cause) (preState? := some pre)
          (deferLogs := true)
        let g := g.players.foldl (fun g pl =>
          if pl.id != ending && g.stillInGame pl.id then
            g.activeEffects.foldl (fun g (eid, e) =>
              match e with
              | .permission p (.playFromExile oid perm) .untilEndOfTurn =>
                if perm.fromAdventure || perm.whileExiled || p.getD perm.player != pl.id then g
                else expirePlayFromExileEffect pre g eid oid cause (deferLogs := true)
              | _ => g) g
          else g) g
        let g := g.clearTurnActivations
        emitExpiredPlayFromExileLogs pre g fromIdx
    else g
  let g := g.record (GameEvent.turnEnded g.turnNumber ending)
  let lastReg := g.lastRegularTurnSeat
  let regEnd := (g.teamMembers lastReg).back? |>.getD lastReg
  let regAnchor := if seatsExtra then regEnd else ending
  let inProgressExtraSeats := sharedTurnInProgressExtraSeats g seats seatsExtra
  let (targetP, targetExtra) : PlayerId × Bool := Id.run do
    if !midRegularShared then
      let mut sIdx := 0
      while sIdx < g.extraTurns.size && !g.stillInGame g.extraTurns[sIdx]! do
        sIdx := sIdx + 1
      if let some q := (g.extraTurns.extract sIdx g.extraTurns.size)[0]? then
        return (q, true)
    let n := g.players.size
    for k in [1:n+1] do
      let q : PlayerId := ⟨(regAnchor.idx + k) % n⟩
      if g.stillInGame q then
        return (q, false)
    return (ending, false)
  let sameShared :=
    g.stillInGame targetP && targetExtra == seatsExtra && !seats.isEmpty &&
      g.areTeammates seats[0]! targetP && !seats.contains targetP
  let endingCurrentRegularShared (q : PlayerId) : Bool :=
    !seatsExtra && !sameShared && seats.any (fun s => s == q || g.areTeammates s q)
  let (nextP, departed0) := Id.run do
    let mut departed : Array PlayerId := #[]
    if !midRegularShared then
      let mut skipIdx := 0
      while skipIdx < g.extraTurns.size && !g.stillInGame g.extraTurns[skipIdx]! do
        let d := g.extraTurns[skipIdx]!
        let extraSeatEnding :=
          seatsExtra && !sameShared && skipIdx < inProgressExtraSeats
        if !extraSeatEnding && !departed.contains d then
          departed := departed.push d
        skipIdx := skipIdx + 1
      if let some q := (g.extraTurns.extract skipIdx g.extraTurns.size)[0]? then
        return (q, departed)
    let n := g.players.size
    for k in [1:n+1] do
      let q : PlayerId := ⟨(regAnchor.idx + k) % n⟩
      if !g.stillInGame q then
        if !endingCurrentRegularShared q && !departed.contains q then
          departed := departed.push q
      else
        return (q, departed)
    return (ending, departed)
  let departed :=
    if !sameShared && g.stillInGame nextP then
      (g.teamMembers nextP).foldl (fun acc tm =>
        if !g.stillInGame tm && !acc.contains tm then
          acc.push tm
        else acc) departed0
    else departed0
  g.continueStartNextTurn nextP departed runBeginTurn

/-- Advance to the next living player's turn after a cleanup step ends, and begin that turn. -/
partial def startNextTurnAndBegin (g : Game) : Game :=
  g.startNextTurnCore true

/-- Record `phaseEnded .ending` and advance to the next turn once `stepEnded .cleanup` finishes. -/
partial def endTurnAfterCleanupStepEnded (g : Game) : Game :=
  let g := g.recordPhaseEnded .ending
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep .startNextTurnAndBegin)
  else
    g.startNextTurnAndBegin

/-- Complete `.cleanup` once `checkSBACountedWithLeaves` has finished (CR 514.3 / 514.3a). -/
partial def finishPostSbaCleanup (g : Game) (sba : Bool) : Game :=
  if g.over then g
  else if sba || g.hasWaitingTriggers then
    let g := g.change (.cleanupGivesPriority true)
    let g := g.logMsg "Players receive priority during cleanup (CR 514.3a)"
    g.receivePriority g.activePlayer
  else
    -- The cleanup step ends (CR 500.3) and the turn ends.
    let g := g.emptyManaPools
    let g := g.recordStepEnded .cleanup
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep .endTurnAfterCleanupStepEnded)
    else
      g.endTurnAfterCleanupStepEnded

/-- Run cleanup SBAs after `clearEOT` completes (CR 514.3 / 514.3a / 704.3). -/
partial def finishCleanupAfterClearEot (g : Game) : Game :=
  let (g, sba, _) := g.checkSBACountedWithLeaves
  if g.over then g
  else
    match g.pending with
    | .chooseReplacement .. =>
      g.chainPendingReplacement (.finishPostStep (.postSbaCleanup sba))
    | .chooseLegend .. =>
      g.chainPendingReplacement (.finishPostStep (.postSbaCleanup true))
    | _ =>
      g.finishPostSbaCleanup sba

/-- Run `clearEOT` and cleanup SBAs once `discardToMaxHandSize` finishes (CR 514.2–514.3). -/
partial def finishCleanupStepAfterDiscard (g : Game) : Game :=
  let g := g.clearEOT
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement .finishCleanupAfterClearEot
  else
    g.finishCleanupAfterClearEot

/-- Untap the active player's permanents and record `stepEnded .untap` once
CR 502.1 phase-in (and any replacement or legend-rule pause it opened) finishes
(CR 502.3–502.4). -/
partial def runUntapStepAfterPhaseIn (g : Game) : Game :=
  if g.over then g
  else
    let ap := g.activePlayer
    let ids := (g.permanentsOf ap).map (·.id)
    let g := g.withBatch (some (.turnBased .untapAll)) fun g =>
      g.untapStepPermanents ids
    match g.pending with
    | .chooseReplacement .. | .chooseLegend .. =>
      g.chainPendingReplacement (.finishPostStep .recordUntapStepEnded)
    | _ =>
      -- No priority (CR 502.4). Immediately continue.
      g.recordStepEnded .untap

/-- Execute the body of `beginStep st` once `phaseBegan` and `stepBegan` have finished. -/
partial def beginStepBody (g : Game) (st : Step) : Game :=
  let g := g.logMsg s!"— Turn {g.turnNumber}, {g.player g.activePlayer |>.name}: {st} —"
  match st with
  | .untap =>
    let ap := g.activePlayer
    -- CR 502.1 / 805.4a–b / 810.2: phased-out permanents controlled by the active
    -- player (or their team on the shared turn's first seat) phase in before untapping.
    let g := if g.isSharedTurnFirstSeat then g.phaseInControlled ap (includeTeammates := true) else g
    match g.pending with
    | .chooseReplacement .. | .chooseLegend .. =>
      g.chainPendingReplacement (.finishPostStep .untapStepAfterPhaseIn)
    | _ =>
      if g.pendingReplacement.isSome then
        g.chainPendingReplacement (.finishPostStep .untapStepAfterPhaseIn)
      else
        g.runUntapStepAfterPhaseIn
  | .draw =>
    if g.skipsFirstDraw then
      -- CR 103.8a–b / 500.11 / 614.10 / 810.6: to skip a step is to proceed
      -- past it as though it didn't exist. Nothing happens during it — no
      -- turn-based draw, and no player receives priority.
      let crRef := if (g.teamMembers g.activePlayer).size > 1 then "CR 103.8b / 810.6" else "CR 103.8a"
      let g := g.logMsg s!"{g.player g.activePlayer |>.name} skips their first draw step ({crRef})"
      let g := g.recordPhaseEnded .beginning
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.beginStepCont .precombatMain)
      else
        g.beginStep .precombatMain
    else
      -- The turn-based draw happens before triggers (ruling 770).
      let g := g.draw g.activePlayer 1 (cause := some (.turnBased .drawStepDraw))
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.receivePriority g.activePlayer)
      else
        g.receivePriority g.activePlayer
  | .declareAttackers =>
    if !g.stillInGame g.activePlayer then
      g.receivePriority g.activePlayer
    else
      g.change (.pending .declareAttackers)
  | .declareBlockers =>
    let attackers := g.battlefield.filter (·.status.attacking)
    if attackers.isEmpty then
      -- CR 509.1 / 508.8: declare blockers step began because creatures attacked
      -- earlier this combat even though none remain attacking; skip blocker
      -- declaration and grant priority.
      (g.change (.blockersQueue #[])).receivePriority g.activePlayer
    else
      let ps := g.defendingPlayers
      let teamQueue := ps.foldl (fun (acc : Array PlayerId) pid =>
        if acc.any (fun q => q == pid || g.areTeammates q pid) then acc
        else acc.push pid) #[]
      if teamQueue.isEmpty then
        let opp := g.defendingPlayer
        if attackers.any (·.status.attackingTarget.isNone) &&
            (g.livingOpponents g.activePlayer).any (fun pl => pl.id == opp) then
          g.changes #[.pending .declareBlockers, .blockersQueue #[opp]]
        else
          -- CR 509.1 / 800.4: attackers remain (CR 506.4c), but every attacked
          -- player has left the game (or no living opponent remains); skip blocker
          -- declaration and grant priority.
          (g.change (.blockersQueue #[])).receivePriority g.activePlayer
      else
        g.changes #[.pending .declareBlockers, .blockersQueue teamQueue]
  | .combatDamage =>
      g.beginCombatDamageAssignment
  | .upkeep =>
    let ap := g.activePlayer
    g.receivePriority ap
  | .beginningOfCombat =>
    let ap := g.activePlayer
    g.receivePriority ap
  | .end =>
    g.receivePriority g.activePlayer
  | .cleanup =>
    -- CR 514.1–514.3.
    let g := g.discardToMaxHandSize
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep .cleanupStepAfterDiscard)
    else
      g.finishCleanupStepAfterDiscard
  | .precombatMain =>
    let ap := g.activePlayer
    let g := g.addLoreAfterDrawStep
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.receivePriority ap)
    else
      g.receivePriority ap
  | _ =>
    g.receivePriority g.activePlayer

/-- Record `stepBegan st` and enter `beginStepBody st` after `recordPhaseBegan` finishes. -/
partial def beginStepAfterPhaseBegan (g : Game) (st : Step) : Game :=
  let g := if st == .draw && g.skipsFirstDraw then g else g.recordStepBegan st
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.beginStepBody st))
  else
    g.beginStepBody st

/-- `partial` because a silent cleanup (CR 514.3) immediately begins the next
turn, and a skipped draw step (CR 103.8a / 500.11) immediately begins
precombat main; both re-enter `beginStep`. -/
partial def beginStep (g : Game) (st : Step) : Game :=
  if g.over then g
  else
    let g := Id.run do
      let mut g := g
      while g.proposalCheckpoint.isSome do
        g := g.change .clearProposalCheckpoint
      return g
    let g := g.changes #[
      .pending .none,
      .consecutivePasses 0,
      .cleanupGivesPriority false,
      .proposedSpell none ]
    let g :=
      if st == .draw && g.skipsFirstDraw then g
      else if isPhaseStartStep st then
        g.recordPhaseBegan st.phase
      else g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.beginStepAfterPhaseBegan st))
    else
      g.beginStepAfterPhaseBegan st

/-- Continue into `st` after step/phase-end replacement pauses resolve. -/
partial def beginStepCont (g : Game) (st : Step) : Game :=
  if g.step == .endOfCombat && st == .beginningOfCombat then
    g.clearCombat
      |>.logMsg "An additional combat phase begins"
      |>.beginStep .beginningOfCombat
  else if g.step == .endOfCombat && st != .endOfCombat then
    g.clearCombat |>.beginStep st
  else
    g.beginStep st

/-- Expire `.protectionFromEverything` and `.lifeCantChange` for `p`'s team at
the start of their shared turn (CR 500.4 / 611.2a / 805.4). -/
partial def expireTurnStartProtectionAndLife (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .expireAtStepBegin)
  let teamSeats := g.teamMembers p
  teamSeats.foldl (fun g q =>
    let hadLife := g.activeEffects.any (fun (_, s) => s == .lifeCantChange q)
    let hadProt := g.activeEffects.any (fun (_, s) => s == .protectionFromEverything q)
    if hadProt || hadLife then
      let g := if hadProt then g.expireAll (.protectionFromEverything q) (cause := cause) else g
      let g := if hadLife then g.expireAll (.lifeCantChange q) (cause := cause) else g
      g.logMsg
        (if hadProt && hadLife then s!"{(g.player q).name}'s protection and life lock end"
         else if hadProt then s!"{(g.player q).name}'s protection from everything ends"
         else s!"{(g.player q).name}'s life total can change again")
    else g) g

/-- Enter `.untap` and `.upkeep` after CR 500.4 turn-start expiry completes. -/
partial def beginTurnAfterStartExpiry (g : Game) : Game :=
  if g.over then g
  else
    let p := g.activePlayer
    let needDeferred :=
      g.isSharedTurnFirstSeat &&
        (g.teamMembers p).any (fun q =>
          g.activeEffects.any (fun (_, s) =>
            s == .lifeCantChange q || s == .protectionFromEverything q))
    let g :=
      if needDeferred then
        g.withBatch none (fun g => g.expireTurnStartProtectionAndLife p)
      else g
    if g.over then g
    else
      -- No player receives priority during untap (CR 502.4).
      let g := g.beginStep .untap
      match g.pending with
      | .chooseReplacement .. | .chooseLegend .. =>
        g.chainPendingReplacement (.beginStepCont .upkeep)
      | _ =>
        if g.pendingReplacement.isSome then
          g.chainPendingReplacement (.beginStepCont .upkeep)
        else
          g.beginStep .upkeep

partial def beginTurn (g : Game) : Game :=
  if g.over then g
  else
    let p := g.activePlayer
    let cause := some (EventCause.turnBased .expireAtStepBegin)
    -- CR 500.4 / 611.2a / 805.4 / 810.2: effects lasting until `p`'s team's next
    -- turn expire as the first living seat of that shared turn begins, before
    -- `TurnEvent.phaseBegan .beginning` / `TurnEvent.stepBegan .untap`.
    let g :=
      if !g.isSharedTurnFirstSeat then g
      else
        g.withBatch none fun g =>
          let expiredCtrl := g.activeEffects.filter fun (eid, e) =>
            match e with
            | .playerRule _ (.controlsPlayer them true) _ => g.hasTurnAfterBegunSince eid them
            | _ => false
          let g := expiredCtrl.foldl (fun acc (eid, _) => acc.expireEffectById eid (cause := cause)) g
          let g := g.expireGoadedFor p (includeTeammates := true)
          let ctrlEids := g.activeEffects.filterMap fun (eid, e) =>
            match e with
            | .layered _ (.control _) (.untilNextTurnOf q) =>
              if q == p || g.areTeammates q p then some eid else none
            | _ => none
          let endingEmbIds0 : Array ObjectId :=
            g.activeEffects.foldl (fun acc (_, e) =>
              match e with
              | .gameRule (.fraEmblem id) (.untilNextTurnOf q) =>
                if (q == p || g.areTeammates q p) && !acc.contains id then acc.push id else acc
              | _ => acc) #[]
          let endingEmbIds := g.expandTransitiveCommandEmblems endingEmbIds0
          let skipIds :=
            g.coDepartingIds endingEmbIds (endingCtrlEids := ctrlEids) (includePhasedOut := true)
          let preTurnExp := g
          let fromIdx := preTurnExp.events.size
          let g := g.endControlEffectsSimultaneously ctrlEids (cause := cause)
            (extraSkipIds := skipIds) (preState? := some preTurnExp)
            (preExpire := fun g0 =>
              let g0 := g0.restoreCopiesUntilNextTurn p (reconcileControl := false)
                (skipLogIds := skipIds)
              g0.expireFraUntilTurnEffects p (includeTeammates := true) (skipControl := true)
                (skipLogIds := skipIds) (preState? := some g0) (deferLogs := true))
          let g := emitExpiredPlayFromExileLogs preTurnExp g fromIdx
          let paused :=
            match g.pending with
            | .chooseReplacement .. | .chooseLegend .. => true
            | _ => g.pendingReplacement.isSome
          if paused || g.over then g
          else g.expireTurnStartProtectionAndLife p
    if g.over then g
    else
      match g.pending with
      | .chooseReplacement .. | .chooseLegend .. =>
        g.chainPendingReplacement .beginTurnAfterStartExpiry
      | _ =>
        if g.pendingReplacement.isSome then
          g.chainPendingReplacement .beginTurnAfterStartExpiry
        else
          g.beginTurnAfterStartExpiry

end

/-- Advance to the next living player's turn after a cleanup step ends.
A player who has left does not begin a turn (CR 800.4k); effects that last
until that turn expire when it would have begun (CR 800.4m). -/
def startNextTurn (g : Game) : Game :=
  g.startNextTurnCore false

/-- Advance after both players pass with an empty stack (CR 500.2). -/
def advanceStep (g : Game) : Game :=
  let g := g.emptyManaPools
  match g.step.next? with
  | some st =>
    -- CR 508.8: skip declare blockers and combat damage only if no creature was
    -- declared as an attacker or put onto the battlefield attacking this combat.
    let attackers := g.battlefield.filter (·.status.attacking)
    let hadAttackersThisCombat : Bool :=
      if g.step != .declareAttackers then true
      else
        let combatBoundIdx? :=
          (List.range g.events.size).reverse.find? fun idx =>
            let e := g.events[idx]!
            e.turn == g.turnNumber &&
              match e.change with
              | .rules (.turn (.phaseBegan .combat))
              | .rules (.turn (.phaseEnded .combat)) => true
              | _ => false
        let slice : Array GameEvent :=
          match combatBoundIdx? with
          | some boundIdx => g.events.extract (boundIdx + 1) g.events.size
          | none =>
            let stepStartIdx? :=
              (List.range g.events.size).reverse.find? fun idx =>
                let e : GameEvent := g.events[idx]!
                e.turn == g.turnNumber &&
                  match e.change with
                  | .rules (.turn (.stepBegan .declareAttackers _)) => true
                  | _ => false
            match stepStartIdx? with
            | some startIdx => g.events.extract (startIdx + 1) g.events.size
            | none => g.events.filter (·.turn == g.turnNumber)
        !attackers.isEmpty ||
          slice.any fun e =>
            match e.change with
            | .rules (.combat (.attackersDeclared _ decls)) => !decls.isEmpty
            | .rules (.combat (.becameAttacking ..)) => true
            | _ => false
    if g.step == .declareAttackers && !hadAttackersThisCombat then
      let g := g.recordStepEnded g.step
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.beginStepCont .endOfCombat)
      else
        g.beginStep .endOfCombat
    else if g.step == .combatDamage && g.pendingRegularCombatDamage then
      let g := g.recordStepEnded .combatDamage
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.beginStepCont .combatDamage)
      else
        g.beginStep .combatDamage
    else if g.step == .endOfCombat && g.additionalCombatPhases > 0 then
      let g := g.recordStepEnded .endOfCombat
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep .advanceAfterStepEnded)
      else
        let g := g.recordPhaseEnded .combat
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.beginStepCont .beginningOfCombat)
        else
          g.beginStepCont .beginningOfCombat
    else
      let g := g.recordStepEnded g.step
      if let .chooseReplacement .. := g.pending then
        if g.step.phase != st.phase then
          g.chainPendingReplacement (.finishPostStep .advanceAfterStepEnded)
        else
          g.chainPendingReplacement (.beginStepCont st)
      else
        let g :=
          if g.step.phase != st.phase then
            g.recordPhaseEnded g.step.phase
          else g
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.beginStepCont st)
        else
          g.beginStepCont st
  | none =>
    -- Leaving cleanup. If CR 514.3a granted priority this step, another
    -- cleanup step begins; otherwise the turn ends (CR 514.3 / 500.3).
    let g := g.recordStepEnded .cleanup
    if g.cleanupGivesPriority then
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.beginStepCont .cleanup)
      else
        g.beginStep .cleanup
    else
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep .endTurnAfterCleanupStepEnded)
      else
        g.endTurnAfterCleanupStepEnded

end Game
end Mtg.Engine
