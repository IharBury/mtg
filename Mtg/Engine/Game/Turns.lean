import Mtg.Engine.Game.Combat

/-!
# Turn structure (CR 500 / 514)

End-of-turn and cleanup clearing (CR 514.3), discarding to maximum hand
size, expiring play permissions and until-next-turn effects, starting
the next turn, `beginStep`, and step advancement.
-/

namespace Mtg.Engine
namespace Game

def clearEOT (g : Game) : Game :=
  Id.run do
    let mut g := g
    g := g.expireAll .creaturesWithoutFlyingCantBlockUntilEot
    g := g.expireMatching (fun | .assignCombatDamageEqualToughnessUntilEot _ => true | _ => false)
    g := g.restoreCopiesUntilEot
    for pl in g.players do
      g := g.expireAll (.legendRuleOffThisTurn pl.id)
    -- Each control-changing effect ends or counts down on its own, so another
    -- control effect on the same permanent keeps applying (CR 514.2 / 613.7).
    let effs := g.activeEffects
    for (eid, e) in effs do
      match e with
      | .control oid c untilEot turnEndsLeft untilSourceLeaves =>
        if untilEot then
          g := g.endControlEffect oid eid
        else if turnEndsLeft > 0 && c == g.activePlayer then
          if turnEndsLeft - 1 == 0 then
            g := g.endControlEffect oid eid
          else
            g := g.change
              (.effectUpdated eid (.control oid c untilEot (turnEndsLeft - 1) untilSourceLeaves))
      | _ => pure ()
    for o in g.battlefield do
      -- Ending a control effect can exile the permanent (CR 800.4c).
      match g.findObject? o.id with
      | none => pure ()
      | some cur =>
        g := g.expireObjectUntilEotEffects cur
        match g.findObject? o.id with
        | some cur =>
          if cur.status.clearsAtCleanup then
            g := g.changeStatus o.id .clearedAtCleanup
        | none => pure ()
    return g

/-- Discard down to maximum hand size (CR 514.1). This turn-based action does
not use the stack; the engine discards from the back of the hand array. -/
def discardToMaxHandSize (g : Game) : Game :=
  let pl := g.player g.activePlayer
  let extra := pl.hand.size - g.effectiveMaxHandSize g.activePlayer
  if extra == 0 then g
  else
    Id.run do
      let mut g := g
      for _ in [0:extra] do
        let pl := g.player g.activePlayer
        if let some last := pl.hand.back? then
          let card := g.object! last
          let (g', _) := g.move last (.graveyard pl.id) none
          g := g'.logMsg s!"{pl.name} discards {card.name} (cleanup)"
      return g

/-- Clear “once each turn” activation counts as a turn ends. -/
def clearTurnActivations (g : Game) : Game :=
  Id.run do
    let mut g := g
    g := g.expireMatching (fun | .pendingFreeRGCreatureThisTurn _ => true | _ => false)
    g := g.expireMatching (fun | .pendingLokiCopy .. => true | _ => false)
    -- Stingcaster Mage: flashback granted until end of turn ends.
    g := g.expireMatching (fun
      | .flashbackUntilEot _ | .freeCastFromGraveyardUntilEot _ => true
      | _ => false)
    for pl in g.players do
      if pl.lost then
        -- Keep last-known this-turn info until that turn would have begun
        -- (CR 800.4i).
        pure ()
      else do
        g := g.expireMatching (fun
          | .attackPumpPerPlainsThisTurn p _ | .jaceLoyaltyAtInstantSpeedThisTurn p
          | .copyNextInstantSorceryThisTurn p _ | .mountainExtraRedThisTurn p _
          | .cantAttackJacesThisTurn p | .cantCastSpellsThisTurn p
          | .nextSpellCantBeCounteredThisTurn p | .lifeLocked p
          | .typeSpellCostLessThisTurn p _ _ | .supertypeSpellCostLessThisTurn p _ _ => p == pl.id
          | _ => false)
    for o in g.battlefield do
      if o.status.activationsThisTurn != 0 || o.status.firedOnceEachTurn ||
          o.status.optionalOnceUsed ||
          !o.status.allianceModesChosen.isEmpty ||
          o.status.declaredAsAttackerThisTurn || o.status.boastUsedThisTurn ||
          o.status.becameTappedThisTurn || o.status.gotPlusOneThisTurn ||
          o.status.loyaltyActivatedThisTurn ||
          !o.status.combatDamageToPlayers.isEmpty ||
          !o.status.modesChosenThisTurn.isEmpty then
        g := g.changeStatuses o.id #[
          .activationsThisTurn 0,
          .abilitiesActivatedThisTurn #[],
          .loyaltyActivatedThisTurn false,
          .firedOnceEachTurn false,
          .optionalOnceUsed false,
          .allianceModesChosen #[],
          .declaredAsAttackerThisTurn false,
          .boastUsedThisTurn false,
          .becameTappedThisTurn false,
          .gotPlusOneThisTurn false,
          .combatDamageToPlayers #[],
          .modesChosenThisTurn #[] ]
    return g

/-- Expire or decrement play-from-exile permissions as `endingPlayer`'s turn
ends. Each permission is its own continuous effect: it ends, or its remaining
turn count goes down, under its own `EffectId` (CR 611.2). -/
def expirePlayPermissions (g : Game) (endingPlayer : PlayerId) : Game :=
  g.activeEffects.foldl (fun g (eid, e) =>
    match e with
    | .playPermission oid perm =>
      if perm.fromAdventure || perm.whileExiled || perm.player != endingPlayer then g
      else if perm.turnEndsRemaining ≤ 1 then
        let g := g.expireEffectById eid
        match g.findObject? oid with
        | some o =>
          if o.zone == .exile then g.logMsg s!"{o.name} can no longer be played from exile"
          else g
        | none => g
      else
        g.change (.effectUpdated eid
          (.playPermission oid { perm with turnEndsRemaining := perm.turnEndsRemaining - 1 }))
    | _ => g) g

/-- End Reality Fracture effects that last until `p`'s next turn: Garruk,
Veiled Butcher's toughness and power reduction and the command-zone effects of Jace, Reality Sculptor
and Garruk, Curse Breaker (CR 611.2b). -/
def expireFraUntilTurnEffects (g : Game) (p : PlayerId) : Game :=
  let g := g.expireMatching (fun | .untilTurnOfPump _ q _ _ => q == p | _ => false)
  g.objects.foldl (fun g o =>
    if o.zone == .command && o.fraEffectUntilTurnOf == some p then
      (g.ceaseToExist o.id).logMsg s!"{o.name} ends"
    else g) g

/-- Expire effects that last until `p`'s next turn (CR 800.4m) and clear
that player's last-turn information (CR 800.4i). -/
def expireUntilNextTurnEffects (g : Game) (p : PlayerId) : Game :=
  let g := g.expireFraUntilTurnEffects p
  let g :=
    if g.hasActiveEffect (.protectionFromEverything p) then
      g.expireAll (.protectionFromEverything p)
        |>.logMsg
          s!"{(g.player p).name}'s protection from everything ends (CR 800.4m)"
    else g
  let g := g.expireAll (.lifeCantChange p)
  let g := g.restoreCopiesUntilNextTurn p
  let g := g.expirePlayPermissions p
  let g := g.expireAll (.cantCastSpellsThisTurn p)
  g.expireMatching (fun | .attackPumpPerPlainsThisTurn q _ => q == p | _ => false)

/-- Advance to the next living player's turn after a cleanup step ends.
A player who has left does not begin a turn (CR 800.4k); effects that last
until that turn expire when it would have begun (CR 800.4m). -/
def startNextTurn (g : Game) : Game :=
  let ending := g.activePlayer
  let g := g.expirePlayPermissions ending |>.clearTurnActivations
  Id.run do
    let mut g := g
    let extraN := g.extraTurns.size
    for _ in [0:extraN] do
      if !g.extraTurns.isEmpty && (g.player g.extraTurns[0]!).lost then
        let q := g.extraTurns[0]!
        g := g.expireUntilNextTurnEffects q
        g := g.change (.extraTurns (g.extraTurns.extract 1 g.extraTurns.size))
    match g.extraTurns[0]? with
    | some q =>
      g := g.changes #[
        .extraTurns (g.extraTurns.extract 1 g.extraTurns.size),
        .activePlayer q,
        .turnNumber (g.turnNumber + 1),
        .isFirstTurn false,
        .cleanupGivesPriority false ]
      if !g.powerUpsForbidden then
        g := g.createEffect .powerUpsForbiddenThisTurn
      return g.logMsg s!"It is now {(g.player q).name}'s extra turn {g.turnNumber}"
    | none =>
      let n := g.players.size
      for k in [1:n+1] do
        let q : PlayerId := ⟨(ending.idx + k) % n⟩
        if (g.player q).lost then
          g := g.expireUntilNextTurnEffects q
        else
          g := g.changes #[
            .activePlayer q,
            .turnNumber (g.turnNumber + 1),
            .isFirstTurn false,
            .cleanupGivesPriority false ]
          if g.powerUpsForbidden then
            g := g.expireAll .powerUpsForbiddenThisTurn
          return g.logMsg s!"It is now {(g.player q).name}'s turn {g.turnNumber}"
      return g

/-- `partial` because a silent cleanup (CR 514.3) immediately begins the next
turn, and a skipped draw step (CR 103.8a / 500.11) immediately begins
precombat main; both re-enter `beginStep`. -/
partial def beginStep (g : Game) (st : Step) : Game :=
  let g := g.changes #[
    .step st,
    .pending .none,
    .consecutivePasses 0,
    .cleanupGivesPriority false,
    .proposedSpell none ]
  let g := g.logMsg s!"— Turn {g.turnNumber}, {g.player g.activePlayer |>.name}: {st} —"
  let stepEvent := GameEvent.stepped g.turnNumber st g.activePlayer
  -- A skipped step does not happen (CR 614.10), so it is not recorded.
  let g := if st == .draw && g.skipsFirstDraw then g else g.record stepEvent
  match st with
  | .untap =>
    Id.run do
      let mut g := g
      let ap := g.activePlayer
      let apName := (g.player ap).name
      g := g.expireFraUntilTurnEffects ap
      -- CR 502.1: phased-out permanents phase in before the player untaps.
      g := g.phaseInControlled ap
      g := g.expireMatching (fun | .additionalLandsThisTurn p _ => p == ap | _ => false)
      for o in g.permanentsOf ap do
        -- CR 502.2: the active player untaps their permanents. Logging each
        -- previously tapped permanent makes the battlefield status change
        -- visible in the demo before the zone reprint.
        let skipUntap :=
          (o.staticAbilities.any StaticAbility.doesntUntapUnlessEnduringStory? &&
            !g.hasEnduringStory ap) ||
          o.staticAbilities.any (· == .fra .doesntUntap) ||
          g.hostCantBecomeUntapped o ||
          g.hostSkipsUntapStep o
        -- CR 122.1d: a stun counter is removed instead of untapping.
        let stunned := o.status.tapped && !skipUntap && o.status.stun > 0
        if o.status.tapped && !skipUntap && !stunned then do
          g := g.logMsg s!"{apName} untaps {o.name}"
          let untap := GameEvent.untapped g.turnNumber o.asEvent false
          if untap.watches .wouldUntap then
            g := g.record untap
        if stunned then do
          g := g.logMsg s!"A stun counter is removed from {o.name} instead of untapping it"
          g := g.record (GameEvent.untapped g.turnNumber o.asEvent true)
          g := g.record (GameEvent.counters g.turnNumber (some ap) o.asEvent .stun 1 true)
        let tapped := if skipUntap || stunned then o.status.tapped else false
        let stun := if stunned then o.status.stun - 1 else o.status.stun
        g := g.changeStatuses o.id #[
          .tapped tapped,
          .stun stun,
          .summoningSick false ]
      -- No priority (CR 502.4). Immediately continue.
      return g
  | .draw =>
    if g.skipsFirstDraw then
      -- CR 103.8a / 500.11 / 614.10: to skip a step is to proceed past it as
      -- though it didn't exist. Nothing happens during it — no turn-based
      -- draw, and no player receives priority.
      g.logMsg s!"{g.player g.activePlayer |>.name} skips their first draw step (CR 103.8a)"
        |>.beginStep .precombatMain
    else
      -- The turn-based draw happens before triggers (ruling 770).
      let g := g.draw g.activePlayer
      let g := (g.livingOpponents g.activePlayer).foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .eachOpponentDrawStep) g
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
    let g := Id.run do
      let mut g := g
      for pl in g.players do
        if pl.eaglesBirdsNextUpkeep > 0 then
          let n := pl.eaglesBirdsNextUpkeep
          g := g.changePlayer pl.id (.eaglesBirdsNextUpkeep 0)
          if g.stillInGame pl.id then
            g := g.createKindTokens pl.id .birdSoldier n
          g := g.logMsg
            s!"{pl.name}'s delayed triggered ability creates {n} Bird Soldier token(s)"
      return g
    let g :=
      if stepEvent.matchesTrigger ap ⟨0⟩ .yourUpkeep then
        g.putControlledTriggers ap .yourUpkeep
      else g
    let g :=
      g.livingPlayers.foldl (fun acc pl =>
        if stepEvent.matchesTrigger pl.id ⟨0⟩ .eachUpkeep then
          acc.putControlledTriggers pl.id .eachUpkeep
        else acc) g
    -- Abilities that trigger from a graveyard (Command the Stage).
    let g :=
      g.livingPlayers.foldl (fun g pl =>
        (g.player pl.id).graveyard.foldl (fun g id =>
          match g.findObject? id with
          | some card => g.putMatchingSourceTriggers pl.id card (.fra .eachUpkeepFromGraveyard)
          | none => g) g) g
    -- Auras with “at the beginning of the upkeep of enchanted creature's controller”.
    let g := g.battlefield.foldl (fun g aura =>
      match aura.attachedTo.bind g.findObject?, aura.controller with
      | some host, some c =>
        if host.controlledBy ap then g.putMatchingSourceTriggers c aura .enchantedControllerUpkeep
        else g
      | _, _ => g) g
    g.receivePriority ap
  | .beginningOfCombat =>
    let ap := g.activePlayer
    let g := g.livingPlayers.foldl (fun g pl =>
      if pl.id == ap then g
      else g.putFraEventTriggers pl.id .opponentBeginCombat) g
    let g :=
      if stepEvent.matchesTrigger ap ⟨0⟩ .yourBeginCombat then
        g.putControlledTriggers ap .yourBeginCombat
      else g
    let g := g.livingPlayers.foldl (fun g pl =>
      if stepEvent.matchesTrigger pl.id ⟨0⟩ .eachBeginCombat then
        g.putControlledTriggers pl.id .eachBeginCombat
      else g) g
    let g := (g.player ap).graveyard.foldl (fun g id =>
      match g.findObject? id with
      | some card => g.putMatchingSourceTriggers ap card (.fra .yourBeginCombatFromGraveyard)
      | none => g) g
    g.receivePriority ap
  | .end =>
    let ap := g.activePlayer
    let g :=
      Id.run do
        let mut g := g
        for o in g.permanentsOf ap do
          if o.printed.impending.isSome && g.loggedCastForImpending o.id && o.status.time > 0 then
            let left := o.status.time - 1
            g := g.changeStatus o.id (.time left)
            g := g.logMsg s!"{o.name} loses a time counter"
        let sacrifices := g.delayedEndStepSacrifices
        g := g.change (.delayedEndStepSacrifices #[])
        for id in sacrifices do
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield then
              g := g.sacrificeToGraveyard o s!"{o.name} is sacrificed"
          | none => pure ()
        let returns := g.delayedGraveReturns
        g := g.change (.delayedGraveReturns #[])
        for (id, who) in returns do
          match g.findObject? id with
          | some o =>
            if o.zone == .graveyard o.owner && !(g.player who).lost then
              let name := o.name
              let (g', newId) := g.putOntoBattlefield id who (summoningSick := !o.printed.keywords.haste)
              g := g'.logMsg s!"{name} returns to the battlefield"
              g := g.afterPermanentEnters (g.object! newId)
            else pure ()
          | none => pure ()
        g := g.applyDelayedSynthetic
        let ids := g.delayedEndStepReturns
        g := g.change (.delayedEndStepReturns #[])
        for id in ids do
          match g.findObject? id with
          | none => pure ()
          | some o =>
            if o.zone == .exile then
              let owner := o.owner
              if (g.player owner).lost then
                g := g.logMsg
                  s!"{o.name} remains in its current zone (CR 800.4b)"
              else
                let name := o.name
                let sick := !o.printed.keywords.haste
                let (g', newId) := g.putOntoBattlefield id owner (summoningSick := sick)
                g := g'.logMsg
                  s!"{name} returns to the battlefield (beginning of end step)"
                let back := g.object! newId
                g :=
                  if back.printed.isLand then g.afterLandEnters back
                  else g.afterPermanentEnters back
        let exiles := g.delayedEndStepExiles
        g := g.change (.delayedEndStepExiles #[])
        for id in exiles do
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield then
              let (g', _) := g.move id .exile none
              g := g'.logMsg s!"{o.name} is exiled (beginning of end step)"
          | none => pure ()
        return g
    let g :=
      g.livingPlayers.foldl (fun acc pl =>
        if stepEvent.matchesTrigger pl.id ⟨0⟩ .eachEndStep then
          acc.putControlledTriggers pl.id .eachEndStep
        else acc) g
    let g :=
      if stepEvent.matchesTrigger ap ⟨0⟩ .yourEndStep then
        g.putControlledTriggers ap .yourEndStep
      else g
    g.receivePriority ap
  | .cleanup =>
    -- Combatants leave combat; then CR 514.1–514.3.
    let g := g.clearCombat
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
      (g.startNextTurn).beginStep .untap |>.beginStep .upkeep
  | .precombatMain =>
    let ap := g.activePlayer
    let g := g.addLoreAfterDrawStep
    let g := g.putControlledTriggers ap .yourFirstMain
    g.receivePriority ap
  | _ =>
    g.receivePriority g.activePlayer

def beginTurn (g : Game) : Game :=
  let p := g.activePlayer
  let g := g.restoreCopiesUntilNextTurn p
  let g :=
    if (g.player p).protectionFromEverything || (g.player p).lifeCantChange then
      let hadLife := (g.player p).lifeCantChange
      let hadProt := (g.player p).protectionFromEverything
      let g := if hadProt then g.expireAll (.protectionFromEverything p) else g
      let g := if hadLife then g.expireAll (.lifeCantChange p) else g
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
      g.beginStep .endOfCombat
    else if g.step == .declareBlockers && attackers.isEmpty then
      g.beginStep .endOfCombat
    else if g.step == .combatDamage && g.pendingRegularCombatDamage then
      (g.change (.pendingRegularCombatDamage false)).beginCombatDamageAssignment
    else if g.step == .endOfCombat && g.additionalCombatPhases > 0 then
      let g := g.clearCombat
      let g := g.change (.additionalCombatPhases (g.additionalCombatPhases - 1))
      g.logMsg "An additional combat phase begins"
        |>.beginStep .beginningOfCombat
    else
      g.beginStep st
  | none =>
    -- Leaving cleanup. If CR 514.3a granted priority this step, another
    -- cleanup step begins; otherwise the turn ends (CR 514.3 / 500.3).
    if g.cleanupGivesPriority then
      g.beginStep .cleanup
    else
      g.startNextTurn |>.beginTurn

end Game
end Mtg.Engine
