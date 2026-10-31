import Mtg.Engine.Game.Combat

/-!
# Turn structure (CR 500 / 514)

End-of-turn and cleanup clearing (CR 514.3), discarding to maximum hand
size, expiring play permissions and until-next-turn effects, starting
the next turn, `beginStep`, and step advancement.
-/

namespace Mtg.Engine
namespace Game

/-- Expire play-from-exile permissions as `endingPlayer`'s turn ends (CR 611.2). -/
def expirePlayPermissions (g : Game) (endingPlayer : PlayerId)
    (cause : Option EventCause := some (.turnBased .cleanupClear)) : Game :=
  g.activeEffects.foldl (fun g (eid, e) =>
    match e with
    | .permission p (.playFromExile oid perm) d =>
      if perm.fromAdventure || perm.whileExiled || p != endingPlayer then g
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

def clearEOT (g : Game) : Game :=
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
    for o in g.battlefield do
      -- Ending a control effect can exile the permanent (CR 800.4c).
      match g.findObject? o.id with
      | none => pure ()
      | some cur =>
        g := g.expireObjectUntilEotEffects cur
    g := g.expireMatching (fun
      | .layered _ (.copy ..) _ | .layered _ (.control _) _ => false
      | .layered _ _ .untilEndOfTurn | .gameRule _ .untilEndOfTurn => true
      | _ => false) (cause := cause)
    let damagedIds :=
      (g.battlefield.filter (fun o => o.status.damage != 0)).map (·.id)
    if !damagedIds.isEmpty then
      g := g.record (GameEvent.damageMarkedCleared g.turnNumber damagedIds
        (cause := .turnBased .cleanupClear))
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
    g.withBatch (some (.turnBased .cleanupDiscard)) fun g =>
      Id.run do
        let mut g := g
        for _ in [0:extra] do
          let pl := g.player g.activePlayer
          if let some last := pl.hand.back? then
            let card := g.object! last
            let (g', _) := g.move last (.graveyard pl.id) none
              (cause := some (.turnBased .cleanupDiscard))
            g := g'.logMsg s!"{pl.name} discards {card.name} (cleanup)"
        return g

/-- Clear “once each turn” activation counts as a turn ends. -/
def clearTurnActivations (g : Game) : Game :=
  let cause := some (EventCause.turnBased .cleanupClear)
  Id.run do
    let mut g := g
    g := g.expireAll .powerUpsForbiddenThisTurn (cause := cause)
    g := g.expireMatching (fun | .playerRule _ .pendingFreeRGCreature .untilEndOfTurn => true | _ => false) (cause := cause)
    g := g.expireMatching (fun | .playerRule _ (.pendingLokiCopy ..) _ => true | _ => false) (cause := cause)
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
          | .playerRule p .jaceLoyaltyAtInstantSpeed .untilEndOfTurn
          | .playerRule p (.copyNextInstantSorcery _) .untilEndOfTurn
          | .playerRule p (.mountainExtraRed _) .untilEndOfTurn
          | .playerRule p .cantAttackJaces .untilEndOfTurn
          | .playerRule p .cantCastSpells .untilEndOfTurn
          | .playerRule p .nextSpellCantBeCountered .untilEndOfTurn
          | .playerRule p .lifeLocked .untilEndOfTurn
          | .playerRule p (.typeSpellCostLess _ _) .untilEndOfTurn
          | .playerRule p (.supertypeSpellCostLess _ _) .untilEndOfTurn => p == pl.id
          | _ => false) (cause := cause)
    let expiredDt := g.delayedTriggers.filter (fun dt =>
      match dt.kind with
      | .attackPumpPerPlains => !(g.player dt.controller).lost
      | _ => false)
    for dt in expiredDt do
      g := g.record (GameEvent.delayedTriggerExpired g.turnNumber dt (.turnBased .cleanupClear))
    return g

/-- End goad designations placed by `p` as `p`'s next turn begins (CR 701.15a). -/
def expireGoadedFor (g : Game) (p : PlayerId) : Game :=
  g.battlefield.foldl (fun g o =>
    if o.status.goadedUntilNextTurnOf.contains p then
      g.record (GameEvent.designation g.turnNumber (g.snapshot o) (.goaded p) false
        (cause := .turnBased .expireAtStepBegin))
    else g) g

/-- End Reality Fracture effects that last until `p`'s next turn: Garruk,
Veiled Butcher's toughness and power reduction and the command-zone effects of Jace, Reality Sculptor
and Garruk, Curse Breaker (CR 611.2b). -/
def expireFraUntilTurnEffects (g : Game) (p : PlayerId) : Game :=
  let cause := some (EventCause.turnBased .expireAtStepBegin)
  let g :=
    g.activeEffects.foldl (fun acc (eid, e) =>
      match e with
      | .layered _ (.control _) (.untilNextTurnOf q) =>
        if q == p then acc.endControlEffectById eid (cause := cause) else acc
      | _ => acc) g
  let g := g.expireMatching (fun
    | .layered _ (.copy ..) _ | .layered _ (.control _) _ => false
    | .layered _ _ (.untilNextTurnOf q) => q == p
    | _ => false) (cause := cause)
  g.objects.foldl (fun g o =>
    if o.zone == .command && g.fraEffectUntilTurnOf o == some p then
      (g.ceaseToExist o.id (cause := cause)).logMsg s!"{o.name} ends"
    else g) g

/-- Expire effects that last until `p`'s next turn (CR 800.4m) and clear
that player's last-turn information (CR 800.4i). -/
def expireUntilNextTurnEffects (g : Game) (p : PlayerId) : Game :=
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
    | .layered _ (.copy ..) _ | .layered _ (.control _) _ => false
    | .layered _ _ (.untilEndOfNextTurnOf q) => q == p
    | _ => false) (cause := cause)
  let g :=
    if g.hasActiveEffect (.protectionFromEverything p) then
      g.expireAll (.protectionFromEverything p) (cause := cause)
        |>.logMsg
          s!"{(g.player p).name}'s protection from everything ends (CR 800.4m)"
    else g
  let g := g.expireAll (.lifeCantChange p) (cause := cause)
  let g := g.restoreCopiesUntilNextTurn p
  let g := g.expirePlayPermissions p (cause := cause)
  let g := g.expireAll (.cantCastSpellsThisTurn p) (cause := cause)
  let expiredDt := g.delayedTriggers.filter (fun dt =>
    dt.kind == .attackPumpPerPlains && dt.controller == p)
  expiredDt.foldl (fun g dt =>
    g.record (GameEvent.delayedTriggerExpired g.turnNumber dt (.turnBased .expireAtStepBegin))) g

/-- Advance to the next living player's turn after a cleanup step ends.
A player who has left does not begin a turn (CR 800.4k); effects that last
until that turn expire when it would have begun (CR 800.4m). -/
def startNextTurn (g : Game) : Game :=
  let ending := g.activePlayer
  let g := g.expirePlayPermissions ending (cause := some (.turnBased .cleanupClear))
    |>.clearTurnActivations
  let g := g.record (GameEvent.turnEnded g.turnNumber ending)
  Id.run do
    let mut g := g
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
        | .engine (.players pls) =>
          (stk, pls.foldl (fun acc pl => updateLost acc pl.id pl.lost) #[])
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
    let pendingExtraCauses := stk.map Prod.snd
    let mut skipIdx := 0
    while skipIdx < g.extraTurns.size && (g.player g.extraTurns[skipIdx]!).lost do
      g := g.expireUntilNextTurnEffects g.extraTurns[skipIdx]!
      skipIdx := skipIdx + 1
    match (g.extraTurns.extract skipIdx g.extraTurns.size)[0]? with
    | some q =>
      let extraCause? := (pendingExtraCauses.extract skipIdx pendingExtraCauses.size)[0]?
      g := g.record (GameEvent.turnBegan (g.turnNumber + 1) q (extra := true))
      g := g.change (.cleanupGivesPriority false)
      if !g.powerUpsForbidden then
        let cause := extraCause? <|> some (.gameRule .continuousEffect)
        g := g.createEffect .powerUpsForbiddenThisTurn (cause := cause)
      return g.logMsg s!"It is now {(g.player q).name}'s extra turn {g.turnNumber}"
    | none =>
      let n := g.players.size
      for k in [1:n+1] do
        let q : PlayerId := ⟨(ending.idx + k) % n⟩
        if (g.player q).lost then
          g := g.expireUntilNextTurnEffects q
        else
          g := g.record (GameEvent.turnBegan (g.turnNumber + 1) q (extra := false))
          g := g.change (.cleanupGivesPriority false)
          return g.logMsg s!"It is now {(g.player q).name}'s turn {g.turnNumber}"
      return g

/-- Whether `st` is the first step of its phase (CR 500.1). -/
private def isPhaseStartStep : Step → Bool
  | .untap | .precombatMain | .beginningOfCombat | .postcombatMain | .end => true
  | _ => false

/-- `partial` because a silent cleanup (CR 514.3) immediately begins the next
turn, and a skipped draw step (CR 103.8a / 500.11) immediately begins
precombat main; both re-enter `beginStep`. -/
partial def beginStep (g : Game) (st : Step) : Game :=
  let g := if g.proposalCheckpoint.isSome then g.change .clearProposalCheckpoint else g
  let g := g.changes #[
    .pending .none,
    .consecutivePasses 0,
    .cleanupGivesPriority false,
    .proposedSpell none ]
  let g :=
    if st == .draw && g.skipsFirstDraw then g
    else if isPhaseStartStep st then
      g.record (GameEvent.phaseBegan g.turnNumber st.phase
        (cause := some (.gameRule .stepAdvance)))
    else g
  let stepEvent := GameEvent.stepped g.turnNumber st g.activePlayer
  let g := if st == .draw && g.skipsFirstDraw then g else g.record stepEvent
  let g := g.logMsg s!"— Turn {g.turnNumber}, {g.player g.activePlayer |>.name}: {st} —"
  match st with
  | .untap =>
    Id.run do
      let mut g := g
      let ap := g.activePlayer
      let apName := (g.player ap).name
      g := g.expireGoadedFor ap
      g := g.expireFraUntilTurnEffects ap
      g := g.restoreCopiesUntilNextTurn ap
      -- CR 502.1: phased-out permanents phase in before the player untaps.
      g := g.phaseInControlled ap
      g := g.expireMatching (fun | .playerRule p (.additionalLands _) _ => p == ap | _ => false)
        (cause := some (.turnBased .expireAtStepBegin))
      g := g.withBatch (some (.turnBased .untapAll)) fun g =>
        Id.run do
          let mut g := g
          for o in g.permanentsOf ap do
            -- CR 502.3: the active player untaps their permanents. Logging each
            -- previously tapped permanent makes the battlefield status change
            -- visible in the demo before the zone reprint.
            let skipUntap :=
              ((g.staticAbilities o).any StaticAbility.doesntUntapUnlessEnduringStory? &&
                !g.hasEnduringStory ap) ||
              (g.staticAbilities o).any (· == .fra .doesntUntap) ||
              g.hostCantBecomeUntapped o ||
              g.hostSkipsUntapStep o
            let baseCause := EventCause.turnBased .untapAll
            let untap := GameEvent.untapped g.turnNumber (g.snapshot o) false (cause := baseCause)
            -- CR 122.1d: a stun counter is removed instead of untapping via the CR 616.1 loop.
            if o.status.tapped && !skipUntap then
              let (stunned, cause') := g.replaceUntap o (cause := some baseCause)
              if stunned then
                g := g.logMsg s!"A stun counter is removed from {g.name o} instead of untapping it"
                g := g.record (GameEvent.counters g.turnNumber (some ap) (g.snapshot o) .stun 1 true
                  (cause := cause'.getD baseCause))
              else
                g := g.logMsg s!"{apName} untaps {g.name o}"
                if untap.watches .wouldUntap then
                  g := g.record untap
          return g
      -- No priority (CR 502.4). Immediately continue.
      g := g.record (GameEvent.stepEnded g.turnNumber .untap
        (cause := some (.gameRule .stepAdvance)))
      return g
  | .draw =>
    if g.skipsFirstDraw then
      -- CR 103.8a / 500.11 / 614.10: to skip a step is to proceed past it as
      -- though it didn't exist. Nothing happens during it — no turn-based
      -- draw, and no player receives priority.
      let g := g.logMsg s!"{g.player g.activePlayer |>.name} skips their first draw step (CR 103.8a)"
      let g := g.record (GameEvent.phaseEnded g.turnNumber .beginning
        (cause := some (.gameRule .stepAdvance)))
      g.beginStep .precombatMain
    else
      -- The turn-based draw happens before triggers (ruling 770).
      let g := g.draw g.activePlayer 1 (cause := some (.turnBased .drawStepDraw))
      g.receivePriority g.activePlayer
  | .declareAttackers =>
    g.change (.pending .declareAttackers)
  | .declareBlockers =>
    if (g.battlefield.filter (·.status.attacking)).isEmpty then
      g.logMsg "No attackers; skipping declare blockers and combat damage (CR 508.8)"
    else
      let queue :=
        let ps := g.defendingPlayers
        if ps.isEmpty then #[g.opponent g.activePlayer] else ps
      g.changes #[.pending .declareBlockers, .blockersQueue queue]
  | .combatDamage =>
      g.beginCombatDamageAssignment
  | .upkeep =>
    let ap := g.activePlayer
    g.receivePriority ap
  | .beginningOfCombat =>
    let ap := g.activePlayer
    g.receivePriority ap
  | .end =>
    let ap := g.activePlayer
    let g :=
      Id.run do
        let mut g := g
        for o in g.permanentsOf ap do
          if (g.baseCard o).impending.isSome && g.loggedCastForImpending o.id && o.status.time > 0 then
            let impCause := EventCause.gameRule .impending
            g := (g.record (GameEvent.counters g.turnNumber (some ap) (g.snapshot o) .time 1 true
              (cause := impCause))).syncImpendingNotACreature o.id (cause := some impCause)
            g := g.logMsg s!"{g.name o} loses a time counter"
        return g
    g.receivePriority ap
  | .cleanup =>
    -- CR 514.1–514.3.
    let g := g.discardToMaxHandSize
    let g := g.clearEOT
    -- CR 514.3 / 514.3a / 704.3: normally no priority. If state-based actions
    -- would be performed or triggered abilities are waiting, perform them,
    -- put the triggers on the stack, and the active player receives priority.
    let (g, sba) := g.checkSBACounted
    if g.over then g
    else if sba || g.hasWaitingTriggers then
      let g := g.change (.cleanupGivesPriority true)
      let g := g.logMsg "Players receive priority during cleanup (CR 514.3a)"
      g.receivePriority g.activePlayer
    else
      -- The cleanup step ends (CR 500.3) and the turn ends.
      let g := g.emptyManaPools
      let g := g.record (GameEvent.stepEnded g.turnNumber .cleanup
        (cause := some (.gameRule .stepAdvance)))
      let g := g.record (GameEvent.phaseEnded g.turnNumber .ending
        (cause := some (.gameRule .stepAdvance)))
      (g.startNextTurn).beginStep .untap |>.beginStep .upkeep
  | .precombatMain =>
    let ap := g.activePlayer
    let g := g.addLoreAfterDrawStep
    g.receivePriority ap
  | _ =>
    g.receivePriority g.activePlayer

def beginTurn (g : Game) : Game :=
  let p := g.activePlayer
  let cause := some (EventCause.turnBased .expireAtStepBegin)
  let g := g.restoreCopiesUntilNextTurn p
  let g :=
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
  -- No player receives priority during untap (CR 502.4).
  (g.beginStep .untap).beginStep .upkeep

/-- Advance after both players pass with an empty stack (CR 500.2). -/
def advanceStep (g : Game) : Game :=
  let g := g.emptyManaPools
  match g.step.next? with
  | some st =>
    -- Skip declare blockers / combat damage when no attackers.
    let attackers := g.battlefield.filter (·.status.attacking)
    if g.step == .declareAttackers && attackers.isEmpty then
      let g := g.record (GameEvent.stepEnded g.turnNumber g.step
        (cause := some (.gameRule .stepAdvance)))
      g.beginStep .endOfCombat
    else if g.step == .declareBlockers && attackers.isEmpty then
      let g := g.record (GameEvent.stepEnded g.turnNumber g.step
        (cause := some (.gameRule .stepAdvance)))
      g.beginStep .endOfCombat
    else if g.step == .combatDamage && g.pendingRegularCombatDamage then
      let g := g.record (GameEvent.stepEnded g.turnNumber .combatDamage
        (cause := some (.gameRule .stepAdvance)))
      g.beginStep .combatDamage
    else if g.step == .endOfCombat && g.additionalCombatPhases > 0 then
      let g := g.record (GameEvent.stepEnded g.turnNumber .endOfCombat
        (cause := some (.gameRule .stepAdvance)))
      let g := g.record (GameEvent.phaseEnded g.turnNumber .combat
        (cause := some (.gameRule .stepAdvance)))
      let g := g.clearCombat
      g.logMsg "An additional combat phase begins"
        |>.beginStep .beginningOfCombat
    else
      let g := g.record (GameEvent.stepEnded g.turnNumber g.step
        (cause := some (.gameRule .stepAdvance)))
      let g :=
        if g.step.phase != st.phase then
          g.record (GameEvent.phaseEnded g.turnNumber g.step.phase
            (cause := some (.gameRule .stepAdvance)))
        else g
      let g := if g.step == .endOfCombat then g.clearCombat else g
      g.beginStep st
  | none =>
    -- Leaving cleanup. If CR 514.3a granted priority this step, another
    -- cleanup step begins; otherwise the turn ends (CR 514.3 / 500.3).
    let g := g.record (GameEvent.stepEnded g.turnNumber .cleanup
      (cause := some (.gameRule .stepAdvance)))
    if g.cleanupGivesPriority then
      g.beginStep .cleanup
    else
      let g := g.record (GameEvent.phaseEnded g.turnNumber .ending
        (cause := some (.gameRule .stepAdvance)))
      g.startNextTurn |>.beginTurn

end Game
end Mtg.Engine
