import Mtg.Engine.Game.Combat

/-!
# Turn structure (CR 500 / 514)

End-of-turn and cleanup clearing (CR 514.3), discarding to maximum hand
size, expiring play permissions and until-next-turn effects, starting
the next turn, `beginStep`, and step advancement.
-/

namespace Mtg.Engine
namespace Game

/-- Duration of a continuous effect (CR 611.2). -/
private def effectDuration : ContinuousEffect → EffectDuration
  | .layered _ _ d | .playerRule _ _ d | .gameRule _ d
  | .replacement _ d | .prevention _ d | .permission _ _ d => d

/-- Expire every active continuous effect whose duration satisfies `pred`,
handling `.control` via `endControlEffectById` and `.copy` log messages (CR 611.2a). -/
def expireEffectsByDuration (g : Game) (pred : EffectId → EffectDuration → Bool)
    (cause : Option EventCause) : Game :=
  g.activeEffects.foldl (fun acc (eid, e) =>
    if !pred eid (effectDuration e) then acc
    else
      match e with
      | .layered _ (.control _) _ =>
        acc.endControlEffectById eid (cause := cause)
      | .layered (.objects #[id]) (.copy printed) _ =>
        let acc := acc.expireEffectById eid (cause := cause)
        match acc.findObject? id with
        | some o =>
          if o.zone == .battlefield then
            acc.logMsg s!"{(acc.baseCard o).name} is no longer a copy of {printed.name}"
          else acc
        | none => acc
      | _ =>
        acc.expireEffectById eid (cause := cause)) g

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

/-- Expire play-from-exile permissions as `endingPlayer`'s turn ends (CR 611.2). -/
def expirePlayPermissions (g : Game) (endingPlayer : PlayerId)
    (cause : Option EventCause := some (.turnBased .cleanupClear)) : Game :=
  g.activeEffects.foldl (fun g (eid, e) =>
    match e with
    | .permission p (.playFromExile oid perm) d =>
      if perm.fromAdventure || perm.whileExiled || p != some endingPlayer then g
      else
        let expires :=
          d == .untilEndOfTurn ||
          (d == .untilEndOfNextTurnOf endingPlayer &&
            (g.hasTurnBegunSince eid endingPlayer || cause == some (.turnBased .expireAtStepBegin)))
        if expires then
          let g := g.expireEffectById eid (cause := cause)
          match g.findObject? oid with
          | some o =>
            if o.zone == .exile then g.logMsg s!"{o.name} can no longer be played from exile"
            else g
          | none => g
        else g
    | _ => g) g

/-- Clear “once each turn” activation counts and `"this turn"` / `"until end of turn"`
player rules, permissions, and delayed triggers as a turn ends (CR 514.2). -/
def clearTurnActivations (g : Game) : Game :=
  let cause := some (EventCause.turnBased .cleanupClear)
  Id.run do
    let mut g := g
    g := g.expireAll .powerUpsForbiddenThisTurn (cause := cause)
    g := g.expireMatching (fun | .playerRule _ .pendingFreeRGCreature .untilEndOfTurn => true | _ => false) (cause := cause)
    -- Stingcaster Mage: flashback granted until end of turn ends.
    g := g.expireMatching (fun
      | .permission _ (.flashback _) .untilEndOfTurn
      | .permission _ (.freeCastFromGraveyard _) .untilEndOfTurn => true
      | _ => false) (cause := cause)
    for pl in g.players do
      if pl.lost then
        -- Keep last-known this-turn info until that turn would have begun
        -- (CR 800.4i).
        pure ()
      else do
        g := g.expireMatching (fun
          | .playerRule p (.additionalLands _) .untilEndOfTurn
          | .playerRule p .jaceLoyaltyAtInstantSpeed .untilEndOfTurn
          | .playerRule p (.mountainExtraRed _) .untilEndOfTurn
          | .playerRule p .cantAttackJaces .untilEndOfTurn
          | .playerRule p .cantCastSpells .untilEndOfTurn
          | .playerRule p .nextSpellCantBeCountered .untilEndOfTurn
          | .playerRule p .lifeLocked .untilEndOfTurn
          | .playerRule p (.typeSpellCostLess _ _) .untilEndOfTurn
          | .playerRule p (.supertypeSpellCostLess _ _) .untilEndOfTurn => p == pl.id
          | _ => false) (cause := cause)
    let expiredDt := g.delayedTriggers.filter (fun dt =>
      !(g.player dt.controller).lost &&
      (match dt.kind with
       | .attackPumpPerPlains
       | .copyNextInstantSorceryThisTurn
       | .lokiCopyNextInstantSorceryThisTurn _ _ => true
       | _ => false))
    for dt in expiredDt do
      g := g.record (GameEvent.delayedTriggerExpired g.turnNumber dt (.turnBased .cleanupClear))
    return g

def clearEOT (g : Game) : Game :=
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
      g := g.restoreCopiesUntilEot
      for pl in g.players do
        g := g.expireAll (.legendRuleOffThisTurn pl.id) (cause := cause)
      -- Each control-changing effect ends or counts down on its own across all
      -- ObjectScopes, so another control effect on the same permanent keeps
      -- applying (CR 514.2 / 613.7 / 800.4c).
      let effs := g.activeEffects
      for (eid, e) in effs do
        match e with
        | .layered _ (.control _) d =>
          if d == .untilEndOfTurn then
            g := g.endControlEffectById eid (cause := cause)
          else if d == .untilEndOfNextTurnOf g.activePlayer &&
              g.hasTurnBegunSince eid g.activePlayer then
            g := g.endControlEffectById eid (cause := cause)
        | _ => pure ()
      g := g.expirePlayPermissions g.activePlayer (cause := cause)
      for pl in g.players do
        if pl.id != g.activePlayer && !pl.lost then
          g := g.activeEffects.foldl (fun g (eid, e) =>
            match e with
            | .permission p (.playFromExile oid perm) .untilEndOfTurn =>
              if perm.fromAdventure || perm.whileExiled || p != some pl.id then g
              else
                let g := g.expireEffectById eid (cause := cause)
                match g.findObject? oid with
                | some o =>
                  if o.zone == .exile then g.logMsg s!"{o.name} can no longer be played from exile"
                  else g
                | none => g
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
          if effectDuration e == .untilEndOfNextTurnOf g.activePlayer &&
              acc.hasTurnBegunSince eid g.activePlayer then
            acc.expireEffectById eid (cause := cause)
          else acc) g
      g := g.expireMatching (fun
        | .layered _ (.copy ..) _ | .layered _ (.control _) _ => false
        | .layered _ _ .untilEndOfTurn | .gameRule _ .untilEndOfTurn => true
        | _ => false) (cause := cause)
      -- CR 514.2 / 702.26d: remove marked damage from all permanents, including phased-out ones.
      let damagedIds :=
        (g.objects.filter (fun o => o.zone == .battlefield && o.status.damage != 0)).map (·.id)
      if !damagedIds.isEmpty then
        g := g.record (GameEvent.damageMarkedCleared g.turnNumber damagedIds
          (cause := .turnBased .cleanupClear))
      return g

/-- Discard `ids` during cleanup (CR 514.1), pausing and chaining `.finishPostStep 38`
if a discard replacement opens `Pending.chooseReplacement`. -/
def discardCleanupIds (g : Game) (p : PlayerId) (ids : Array ObjectId) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.finishPostStep 38 p 0 (ids := ids))
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    let pl := g.player p
    if pl.hand.contains id then
      let name := (g.object! id).name
      let (g', _) := g.move id (.graveyard p) none (verb := some .discard) (actor := some p)
        (cause := some (.turnBased .cleanupDiscard))
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        g := g.chainPendingReplacement (.finishPostStep 38 p 1 (cardId := some id) (ids := rem))
        return g
      if !(g.player p).hand.contains id then
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

/-- End goad designations placed by `p` as `p`'s next turn begins (CR 701.15a). -/
def expireGoadedFor (g : Game) (p : PlayerId) : Game :=
  g.battlefield.foldl (fun g o =>
    if o.status.goadedUntilNextTurnOf.contains p then
      g.record (GameEvent.designation g.turnNumber (g.snapshot o) (.goaded p) false
        (cause := .turnBased .expireAtStepBegin))
    else g) g

/-- End Reality Fracture effects that last until `p`'s next turn: Garruk,
Veiled Butcher's toughness and power reduction and the command-zone effects of Jace, Reality Sculptor
and Garruk, Curse Breaker (CR 611.2a). -/
def expireFraUntilTurnEffects (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .expireAtStepBegin)
  let endingEmblems := g.objects.filter (fun o => o.zone == .command && g.fraEffectUntilTurnOf o == some p)
  let g :=
    g.activeEffects.foldl (fun acc (eid, e) =>
      match e with
      | .layered _ (.control _) (.untilNextTurnOf q) =>
        if q == p then acc.endControlEffectById eid (cause := cause) else acc
      | _ => acc) g
  let g := g.expireMatching (fun
    | .layered _ (.copy ..) _ | .layered _ (.control _) _
    | .playerRule _ .protectionFromEverything _
    | .playerRule _ .lifeCantChange _ => false
    | e => effectDuration e == .untilNextTurnOf p) (cause := cause)
  endingEmblems.foldl (fun g o =>
    if (g.findObject? o.id).any (·.zone == .command) then
      (g.ceaseToExist o.id (cause := cause)).logMsg s!"{o.name} ends"
    else g) g

/-- Expire effects that last until `p`'s next turn (CR 800.4m) and clear
that player's last-turn information (CR 800.4i). -/
def expireUntilNextTurnEffects (g : Game) (p : PlayerId) : Game :=
  g.withBatch none fun g =>
    let cause := some (EventCause.turnBased .expireAtStepBegin)
    let g := g.expireGoadedFor p
    let g := g.expireFraUntilTurnEffects p
    let g :=
      g.activeEffects.foldl (fun acc (eid, e) =>
        match e with
        | .layered _ (.control _) (.untilEndOfNextTurnOf q) =>
          if q == p then acc.endControlEffectById eid (cause := cause) else acc
        | _ => acc) g
    let g := g.expireMatching (fun
      | .layered _ (.copy ..) _ | .layered _ (.control _) _
      | .permission _ (.playFromExile ..) _ => false
      | e => effectDuration e == .untilEndOfNextTurnOf p) (cause := cause)
    let g :=
      if g.hasActiveEffect (.protectionFromEverything p) then
        g.expireAll (.protectionFromEverything p) (cause := cause)
          |>.logMsg
            s!"{(g.player p).name}'s protection from everything ends (CR 800.4m)"
      else g
    let g := g.expireAll (.lifeCantChange p) (cause := cause)
    let g := g.restoreCopiesUntilNextTurn p (departed := true)
    let g := g.expirePlayPermissions p (cause := cause)
    let g := g.expireMatching (fun
      | .playerRule q (.additionalLands _) .untilEndOfTurn
      | .playerRule q .jaceLoyaltyAtInstantSpeed .untilEndOfTurn
      | .playerRule q (.mountainExtraRed _) .untilEndOfTurn
      | .playerRule q .cantAttackJaces .untilEndOfTurn
      | .playerRule q .cantCastSpells .untilEndOfTurn
      | .playerRule q .nextSpellCantBeCountered .untilEndOfTurn
      | .playerRule q .lifeLocked .untilEndOfTurn
      | .playerRule q (.typeSpellCostLess _ _) .untilEndOfTurn
      | .playerRule q (.supertypeSpellCostLess _ _) .untilEndOfTurn => q == p
      | _ => false) (cause := cause)
    let expiredDt := g.delayedTriggers.filter (fun dt =>
      (match dt.kind with
       | .attackPumpPerPlains
       | .copyNextInstantSorceryThisTurn
       | .lokiCopyNextInstantSorceryThisTurn _ _ => true
       | _ => false) && dt.controller == p)
    expiredDt.foldl (fun g dt =>
      g.record (GameEvent.delayedTriggerExpired g.turnNumber dt (.turnBased .expireAtStepBegin))) g

/-- Pending extra-turn causes reconstructed from `g.events`, aligned with `g.extraTurns`. -/
private def pendingExtraTurnCauses (g : Game) : Array EventCause :=
  let dropLost (stk : Array (PlayerId × EventCause)) (lost : Array PlayerId) :
      Array (PlayerId × EventCause) :=
    (stk.toList.dropWhile (fun (p, _) => lost.contains p)).toArray
  let updateLost (lost : Array PlayerId) (p : PlayerId) (isLost : Bool) : Array PlayerId :=
    if isLost then (if lost.contains p then lost else lost.push p)
    else lost.filter (· != p)
  let (stk, _) := g.events.foldl
    (fun ((stk, lost) : Array (PlayerId × EventCause) × Array PlayerId) e =>
      match e.change with
      | .rules (.player (.lost p _)) | .rules (.player (.leftGame p)) =>
        (stk, updateLost lost p true)
      | .engine (.addPlayer pl) =>
        (stk, updateLost lost pl.id pl.lost)
      | .rules (.turn (.extraTurnAdded p _)) =>
        match e.cause? with
        | some c => (#[(p, c)] ++ stk, lost)
        | none => (stk, lost)
      | .rules (.turn (.turnBegan p true)) =>
        let trimmed := dropLost stk lost
        let next :=
          match trimmed.findIdx? (fun (q, _) => q == p) with
          | some idx => trimmed.extract (idx + 1) trimmed.size
          | none => trimmed.extract 1 trimmed.size
        (next, lost)
      | .rules (.turn (.turnBegan _ false)) =>
        (dropLost stk lost, lost)
      | _ => (stk, lost))
    (#[], #[])
  stk.map Prod.snd

/-- Whether `st` is the first step of its phase (CR 500.1). -/
private def isPhaseStartStep : Step → Bool
  | .untap | .precombatMain | .beginningOfCombat | .postcombatMain | .end => true
  | _ => false

private def stepToIdx (st : Step) : Nat :=
  (Step.all.findIdx? (· == st)).getD 0

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
              g := g.logMsg s!"A stun counter is removed from {g.name o} instead of untapping it"
              g := g.record (GameEvent.counters g.turnNumber (some ap) (g.snapshot o) .stun 1 true
                (cause := cause'.getD baseCause))
            else
              g := g.logMsg s!"{apName} untaps {g.name o}"
              if untap.watches .wouldUntap then
                g := g.record untap
    return g

mutual

/-- Resume `startNextTurn` across departed-player `expireUntilNextTurnEffects` pauses
(CR 800.4k / 800.4m), optionally entering `beginTurn` once `turnBegan` is recorded. -/
partial def continueStartNextTurn (g : Game) (nextP : PlayerId)
    (remainingDeparted : Array PlayerId) (runBeginTurn : Bool := false) : Game := Id.run do
  let mut g := g
  for i in [0:remainingDeparted.size] do
    let dep := remainingDeparted[i]!
    g := g.expireUntilNextTurnEffects dep
    if let .chooseReplacement .. := g.pending then
      let rem := remainingDeparted.extract (i + 1) remainingDeparted.size
      return g.chainPendingReplacement (.continueStartNextTurn nextP rem runBeginTurn)
  let pendingExtraCauses := pendingExtraTurnCauses g
  let mut skipIdx := 0
  while skipIdx < g.extraTurns.size && (g.player g.extraTurns[skipIdx]!).lost do
    skipIdx := skipIdx + 1
  let gNext :=
    match (g.extraTurns.extract skipIdx g.extraTurns.size)[0]? with
    | some q =>
      let extraCause? := (pendingExtraCauses.extract skipIdx pendingExtraCauses.size)[0]?
      let g := g.record (GameEvent.turnBegan (g.turnNumber + 1) q (extra := true))
      let g := g.change (.cleanupGivesPriority false)
      let g :=
        if !g.powerUpsForbidden then
          let cause := extraCause? <|> some (.gameRule .continuousEffect)
          g.createEffect .powerUpsForbiddenThisTurn (cause := cause)
        else g
      g.logMsg s!"It is now {(g.player q).name}'s extra turn {g.turnNumber}"
    | none =>
      if !(g.player nextP).lost then
        let g := g.record (GameEvent.turnBegan (g.turnNumber + 1) nextP (extra := false))
        let g := g.change (.cleanupGivesPriority false)
        g.logMsg s!"It is now {(g.player nextP).name}'s turn {g.turnNumber}"
      else g
  if runBeginTurn && !(gNext.player gNext.activePlayer).lost then
    gNext.beginTurn
  else gNext

partial def startNextTurnCore (g : Game) (runBeginTurn : Bool) : Game :=
  let ending := g.activePlayer
  let g := g.expirePlayPermissions ending (cause := some (.turnBased .cleanupClear))
    |>.clearTurnActivations
  let g := g.record (GameEvent.turnEnded g.turnNumber ending)
  let (nextP, departed) := Id.run do
    let mut departed : Array PlayerId := #[]
    let mut skipIdx := 0
    while skipIdx < g.extraTurns.size && (g.player g.extraTurns[skipIdx]!).lost do
      departed := departed.push g.extraTurns[skipIdx]!
      skipIdx := skipIdx + 1
    match (g.extraTurns.extract skipIdx g.extraTurns.size)[0]? with
    | some q => return (q, departed)
    | none =>
      let n := g.players.size
      for k in [1:n+1] do
        let q : PlayerId := ⟨(ending.idx + k) % n⟩
        if (g.player q).lost then
          departed := departed.push q
        else
          return (q, departed)
      return (ending, departed)
  g.continueStartNextTurn nextP departed runBeginTurn

/-- Advance to the next living player's turn after a cleanup step ends, and begin that turn. -/
partial def startNextTurnAndBegin (g : Game) : Game :=
  g.startNextTurnCore true

/-- Record `phaseEnded .ending` and advance to the next turn once `stepEnded .cleanup` finishes. -/
partial def endTurnAfterCleanupStepEnded (g : Game) : Game :=
  let g := g.recordPhaseEnded .ending
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep 94 g.activePlayer 1)
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
      g.chainPendingReplacement (.finishPostStep 94 g.activePlayer 0)
    else
      g.endTurnAfterCleanupStepEnded

/-- Run cleanup SBAs after `clearEOT` completes (CR 514.3 / 514.3a / 704.3). -/
partial def finishCleanupAfterClearEot (g : Game) : Game :=
  let (g, sba) := g.checkSBACountedWithLeaves
  if g.over then g
  else
    match g.pending with
    | .chooseReplacement .. =>
      g.chainPendingReplacement (.finishPostStep 39 g.activePlayer (if sba then 1 else 0))
    | .chooseLegend .. =>
      g.chainPendingReplacement (.finishPostStep 39 g.activePlayer 1)
    | _ =>
      g.finishPostSbaCleanup sba

/-- Run `clearEOT` and cleanup SBAs once `discardToMaxHandSize` finishes (CR 514.2–514.3). -/
partial def finishCleanupStepAfterDiscard (g : Game) : Game :=
  let g := g.clearEOT
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement .finishCleanupAfterClearEot
  else
    g.finishCleanupAfterClearEot

/-- Execute the body of `beginStep st` once `phaseBegan` and `stepBegan` have finished. -/
partial def beginStepBody (g : Game) (st : Step) : Game :=
  let g := g.logMsg s!"— Turn {g.turnNumber}, {g.player g.activePlayer |>.name}: {st} —"
  match st with
  | .untap =>
    Id.run do
      let mut g := g
      let ap := g.activePlayer
      -- CR 502.1: phased-out permanents phase in before the player untaps.
      g := g.phaseInControlled ap
      let ids := (g.permanentsOf ap).map (·.id)
      g := g.withBatch (some (.turnBased .untapAll)) fun g =>
        g.untapStepPermanents ids
      if let .chooseReplacement .. := g.pending then
        return g.chainPendingReplacement (.finishPostStep 95 ap 32)
      -- No priority (CR 502.4). Immediately continue.
      g := g.recordStepEnded .untap
      return g
  | .draw =>
    if g.skipsFirstDraw then
      -- CR 103.8a / 500.11 / 614.10: to skip a step is to proceed past it as
      -- though it didn't exist. Nothing happens during it — no turn-based
      -- draw, and no player receives priority.
      let g := g.logMsg s!"{g.player g.activePlayer |>.name} skips their first draw step (CR 103.8a)"
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
    if (g.player g.activePlayer).lost then
      g.receivePriority g.activePlayer
    else
      g.change (.pending .declareAttackers)
  | .declareBlockers =>
    let attackers := g.battlefield.filter (·.status.attacking)
    if attackers.isEmpty then
      g.logMsg "No attackers; skipping declare blockers and combat damage (CR 508.8)"
    else
      let ps := g.defendingPlayers
      if ps.isEmpty then
        let opp := g.opponent g.activePlayer
        if attackers.any (·.status.attackingTarget.isNone) &&
            (g.livingOpponents g.activePlayer).any (fun pl => pl.id == opp) then
          g.changes #[.pending .declareBlockers, .blockersQueue #[opp]]
        else
          -- CR 509.1 / 800.4: attackers remain (CR 506.4c), but every attacked
          -- player has left the game (or no living opponent remains); skip blocker
          -- declaration and grant priority.
          (g.change (.blockersQueue #[])).receivePriority g.activePlayer
      else
        g.changes #[.pending .declareBlockers, .blockersQueue ps]
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
      g.chainPendingReplacement (.finishPostStep 40 g.activePlayer)
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
    g.chainPendingReplacement (.finishPostStep 95 g.activePlayer (16 + stepToIdx st))
  else
    g.beginStepBody st

/-- `partial` because a silent cleanup (CR 514.3) immediately begins the next
turn, and a skipped draw step (CR 103.8a / 500.11) immediately begins
precombat main; both re-enter `beginStep`. -/
partial def beginStep (g : Game) (st : Step) : Game :=
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
    g.chainPendingReplacement (.finishPostStep 95 g.activePlayer (stepToIdx st))
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

/-- Enter `.untap` and `.upkeep` after CR 500.4 turn-start expiry completes. -/
partial def beginTurnAfterStartExpiry (g : Game) : Game :=
  -- No player receives priority during untap (CR 502.4).
  let g := g.beginStep .untap
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.beginStepCont .upkeep)
  else
    g.beginStep .upkeep

partial def beginTurn (g : Game) : Game :=
  let p := g.activePlayer
  let cause := some (EventCause.turnBased .expireAtStepBegin)
  -- CR 500.4 / 611.2a: effects lasting until `p`'s next turn expire as the turn
  -- begins, before `TurnEvent.phaseBegan .beginning` / `TurnEvent.stepBegan .untap`.
  let g := g.withBatch none fun g =>
    let g := g.expireGoadedFor p
    let g := g.expireFraUntilTurnEffects p
    let g := g.restoreCopiesUntilNextTurn p
    if g.protectionFromEverything p || g.lifeCantChange p then
      let hadLife := g.lifeCantChange p
      let hadProt := g.protectionFromEverything p
      let g := if hadProt then g.expireAll (.protectionFromEverything p) (cause := cause) else g
      let g := if hadLife then g.expireAll (.lifeCantChange p) (cause := cause) else g
      g.logMsg
        (if hadProt && hadLife then s!"{(g.player p).name}'s protection and life lock end"
         else if hadProt then s!"{(g.player p).name}'s protection from everything ends"
         else s!"{(g.player p).name}'s life total can change again")
    else g
  if let .chooseReplacement .. := g.pending then
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
    -- Skip declare blockers / combat damage when no attackers.
    let attackers := g.battlefield.filter (·.status.attacking)
    if g.step == .declareAttackers && attackers.isEmpty then
      let g := g.recordStepEnded g.step
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.beginStepCont .endOfCombat)
      else
        g.beginStep .endOfCombat
    else if g.step == .declareBlockers && attackers.isEmpty then
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
        g.chainPendingReplacement (.finishPostStep 94 g.activePlayer 2)
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
          g.chainPendingReplacement (.finishPostStep 94 g.activePlayer 2)
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
        g.chainPendingReplacement (.finishPostStep 94 g.activePlayer 0)
      else
        g.endTurnAfterCleanupStepEnded

end Game
end Mtg.Engine
