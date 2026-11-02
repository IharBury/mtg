import Mtg.Engine.Game.Library

/-!
# Game end and leaving the game (CR 104 / 800.4)

Deciding a finished game, control-changing effects and their end
(CR 800.4a / 800.4c), objects and pending decisions of a player who
leaves a multiplayer game, and emptying mana pools (CR 500.5).
-/

namespace Mtg.Engine
namespace Game

/-- True while a CR 704.3 state-based action sweep is paused awaiting a
replacement or legend-rule choice. -/
def sbaPaused (g : Game) : Bool :=
  match g.pending with
  | .chooseReplacement .. | .chooseLegend .. => true
  | _ => false

/-- If 0 or 1 living players remain, set the game result (CR 104). -/
def decideGameIfFinished (g : Game) : Option Game :=
  let living := g.livingPlayers
  if living.size == 0 then
    some (g.record (GameEvent.gameEnded g.turnNumber .draw) |>.logMsg "The game is a draw")
  else if living.size == 1 then
    let w := living[0]!
    let blocked := (g.livingOpponents w.id).any (fun opp =>
      (g.permanentsOf opp.id).any (fun o =>
        (g.baseCard o).opponentsCantWin && g.retainsPrintedAbilities o))
    if blocked then none
    else some (g.record (GameEvent.gameEnded g.turnNumber (.won w.id)) |>.logMsg s!"{w.name} wins the game")
  else none

/-- True when this stack object is a card (CR 800.4a). Activated and
triggered abilities, and copies of spells, are not represented by cards. -/
def representedByCard (o : GameObject) : Bool :=
  o.abilityEffect.isNone && o.triggeredAbility.isNone && !o.isCopy

/-- Change `o`'s controller unless that player has left (CR 800.4b). -/
def changeControl (g : Game) (o : GameObject) (p : PlayerId)
    (untilEot : Bool := false) (turnEndsLeft : Nat := 0)
    (untilSourceLeaves : Option ObjectId := none)
    (cause : Option EventCause := none) : Game :=
  if (g.player p).lost then
    g.logMsg s!"{g.name o} does not change control (CR 800.4b)"
  else if g.controlledBy o p then
    if untilEot || turnEndsLeft > 0 || untilSourceLeaves.isSome then
      g.createEffect (.control o.id p untilEot turnEndsLeft untilSourceLeaves) (cause := cause)
    else g
  else
    let g :=
      match g.controllerOf o with
      | some oldCtrl =>
        if oldCtrl != p && (g.player oldCtrl).ringBearerId == some o.id then
          g.record (GameEvent.designation g.turnNumber (g.snapshot o) .ringBearer false
            (cause := cause.getD (.gameRule .staticAbility)))
        else g
      | none => g
    g.createEffect (.control o.id p untilEot turnEndsLeft untilSourceLeaves) (cause := cause)
      |>.logMsg s!"{(g.player p).name} gains control of {g.name o}"

/-- Exile each `(oid, logLine)` in `remaining` sequentially (CR 800.4a / 800.4c),
pausing and chaining `.endControlExileLoop` if a CR 616.1 replacement choice
opens and emitting `logLine` only once the permanent has left `.battlefield`. -/
def runEndControlExileLoop (g : Game) (remaining : Array (ObjectId × String))
    (cause : Option EventCause := none)
    (pendingLog : Option (ObjectId × String) := none) : Game :=
  if remaining.isEmpty && pendingLog.isNone then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.endControlExileLoop remaining cause pendingLog)
  else Id.run do
    let mut g := g
    if let some (fromId, logLine) := pendingLog then
      if !(g.findObject? fromId).any (·.isBattlefieldObject) then
        g := g.logMsg logLine
    for i in [0:remaining.size] do
      let (oid, logLine) := remaining[i]!
      if let some cur := g.findObject? oid then
        if cur.isBattlefieldObject then
          let (g', _) := g.move oid .exile none (cause := cause)
          g := g'
          if let .chooseReplacement .. := g.pending then
            let rem := remaining.extract (i + 1) remaining.size
            g := g.chainPendingReplacement (.endControlExileLoop rem cause (some (oid, logLine)))
            return g
          if !(g.findObject? oid).any (·.isBattlefieldObject) then
            g := g.logMsg logLine
    return g

/-- End the Layer 2 control-changing effect recorded under `eid` across every
battlefield permanent it applies to (singleton `.objects #[id]`, multi-target
`.objects ids`, `.creaturesControlledBy`, `.permanentsOfSubtype`, or
`.creaturesWithout`). Any other control-changing effects still applying to a
permanent keep applying, and Layer 2 timestamp/dependency order decides its
controller (CR 613.1b / 613.7 / 613.8). When none remain on an affected
permanent and the player who would control it has left the game, the permanent
is exiled (CR 800.4a / 800.4c). -/
def endControlEffectById (g : Game) (eid : EffectId)
    (cause : Option EventCause := none) : Game :=
  match g.activeEffect? eid with
  | none => g
  | some spec =>
    let explicitIds : Array ObjectId :=
      match spec with
      | .layered (.objects ids) (.control _) _ => ids
      | _ => #[]
    let candidates : Array (ObjectId × Option PlayerId × Bool) :=
      g.objects.filterMap fun o =>
        if !o.isBattlefieldObject then none
        else
          let applied := g.appliedControlEffectIds o
          if applied.contains eid || explicitIds.contains o.id then
            some (o.id, g.controllerOf o, g.controlChanged o || applied.contains eid)
          else none
    let g := g.expireEffectById eid (cause := cause)
    let (g, exileQueue) :=
      candidates.foldl (fun (acc, exiles) (oid, prevCtrl, hadControlChange) =>
        match acc.findObject? oid with
        | none => (acc, exiles)
        | some cur =>
          if !cur.isBattlefieldObject then (acc, exiles)
          else
            let othersRemain := !(acc.appliedControlEffectIds cur).isEmpty
            let curCtrl := acc.controllerOf cur
            let acc :=
              match prevCtrl with
              | some prev =>
                if curCtrl != prevCtrl && (acc.player prev).ringBearerId == some oid then
                  acc.record (GameEvent.designation acc.turnNumber (acc.snapshot cur) .ringBearer false
                    (cause := cause.getD (.gameRule .staticAbility)))
                else acc
              | none => acc
            if othersRemain then
              let acc :=
                if curCtrl != prevCtrl then
                  acc.logMsg s!"{acc.name cur} reverts to {(acc.player (curCtrl.getD cur.owner)).name}'s control"
                else acc
              (acc, exiles)
            else if !hadControlChange then (acc, exiles)
            else
              let dest := curCtrl.getD (cur.defaultController.getD cur.owner)
              if (acc.player dest).lost then
                (acc, exiles.push (oid, s!"{acc.name cur} is exiled (CR 800.4c)"))
              else if curCtrl != prevCtrl || prevCtrl != some dest then
                (acc.logMsg s!"{acc.name cur} reverts to {(acc.player dest).name}'s control", exiles)
              else (acc, exiles)) (g, #[])
    g.runEndControlExileLoop exileQueue (cause := some (.gameRule .playerLeftGame))

/-- End the control-changing effect recorded under `eid` (CR 613.1b / 800.4c). -/
def endControlEffect (g : Game) (_oid : ObjectId) (eid : EffectId)
    (cause : Option EventCause := none) : Game :=
  g.endControlEffectById eid (cause := cause)

/-- End every control-changing effect applying to `o`, each under its own
`EffectId` (CR 800.4a / 800.4c). -/
def endControlChangingEffect (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  let applied := g.appliedControlEffectIds o
  let ids := g.activeEffects.filterMap (fun (eid, e) =>
    match e with
    | .layered (.objects oids) (.control _) _ =>
      if oids.contains o.id || applied.contains eid then some eid else none
    | .layered _ (.control _) _ =>
      if applied.contains eid then some eid else none
    | _ => none)
  ids.foldl (fun acc eid => acc.endControlEffectById eid (cause := cause)) g

/-- Gain control of `o` until end of turn (CR 611.2a). -/
def giveControlUntilEot (g : Game) (o : GameObject) (p : PlayerId) : Game :=
  if (g.player p).lost then
    g.logMsg s!"{o.name} does not change control (CR 800.4b)"
  else
    g.changeControl o p (untilEot := true)

/-- Remove `o` from the game directly via `ceaseToExist` (without routing
through `move` to `.exile`), unattaching attachments, cleaning up prepared exile
copies, evaluating CR 603.10a leaves-the-battlefield look-back triggers for
remaining players, and returning CR 610.3 linked-exile cards (CR 800.4a).
Ante stays (CR 800.4n). -/
def objectLeavesTheGame (g : Game) (o : GameObject) (_leavingPlayer : PlayerId) : Game :=
  let cause := some (EventCause.gameRule .playerLeftGame)
  if o.zone == .ante then g
  else if o.zone == .battlefield then
    let sourceCtrlTargets : Array ObjectId :=
      let sourceCtrlIds := g.activeEffects.filterMap fun (eid, e) =>
        match e with
        | .layered _ (.control _) (.whileSourceOnBattlefield s)
        | .layered _ (.control _) (.untilSourceLeaves s)
        | .layered _ (.control _) (.whileSourceHasCounter s _) =>
          if s == o.id then some eid else none
        | _ => none
      if sourceCtrlIds.isEmpty then #[]
      else
        g.objects.filterMap fun pObj =>
          if pObj.isBattlefieldObject && pObj.id != o.id &&
              (g.appliedControlEffectIds pObj).any (fun eid => sourceCtrlIds.contains eid) then
            some pObj.id
          else none
    let g := g.withBatch cause fun g =>
      let g := g.unattachFrom o.id
      let g := g.removePreparedCopy o.id
      let g := g.ceaseToExist o.id (cause := cause)
      let exileQueue := sourceCtrlTargets.filterMap fun tid =>
        match g.findObject? tid with
        | none => none
        | some cur =>
          if !cur.isBattlefieldObject || !(g.appliedControlEffectIds cur).isEmpty then none
          else
            let destP := (g.controllerOf cur).getD (cur.defaultController.getD cur.owner)
            if (g.player destP).lost then some (tid, s!"{g.name cur} is exiled (CR 800.4c)") else none
      g.runEndControlExileLoop exileQueue (cause := cause)
    if !o.linkedExile.isEmpty && g.currentBatch.isNone then
      g.returnLinkedExileMoves o.linkedExile
    else g
  else
    g.ceaseToExist o.id (cause := cause)

private def findPausedCloseBatch? : PendingReplacement → Option (BatchId × Nat)
  | .closeBatch b s => some (b, s)
  | .seq a b => findPausedCloseBatch? a <|> findPausedCloseBatch? b
  | _ => none

private def afterRandomReferencesPlayer (p : PlayerId) : AfterRandom → Bool
  | .none => false
  | .draw q _ | .gainLife q _ | .revealRandomCreatureThenBottom q _
  | .putOnTop q _ | .beholdUntap q _ _ | .discardRandom q => q == p
  | .plusOne _ => false

private def filterLivingAttackTargets (g : Game) (controller : PlayerId)
    (opts : Array AttackTarget) : Array AttackTarget :=
  opts.filter fun
    | .player pid => g.isLivingOpponentOf controller pid
    | .planeswalker oid | .battle oid =>
      (g.findObject? oid).any (fun o =>
        o.isOnBattlefield && (g.livingOpponents controller).any (fun pl => g.controlledBy o pl.id))

private def sanitizeEnteringAttackItem (g : Game) : EnteringAttackItem → Option EnteringAttackItem
  | .token c kind tapped opts =>
    if !g.stillInGame c then none
    else some (.token c kind tapped (filterLivingAttackTargets g c opts))
  | .card cid c effCtrl tapped retArt extra mods logKind opts =>
    if !g.stillInGame c || (g.findObject? cid).isNone then none
    else some (.card cid c effCtrl tapped retArt extra mods logKind (filterLivingAttackTargets g c opts))

private partial def advanceSacDamagersAfterLeave (g : Game) (controller : PlayerId)
    (opponents : Array PlayerId) (chosen : Array (PlayerId × ObjectId)) : Game :=
  let living := opponents.filter g.stillInGame
  match living[0]? with
  | none =>
    let g := g.change (.pending .none)
    if chosen.isEmpty then g
    else
      let preBf := g.battlefield
      g.withBatch none fun g =>
        g.sacrificePermanentsLoop chosen (preBattlefield := some preBf)
  | some r =>
    let rest := living.extract 1 living.size
    let ids :=
      ((g.creaturesControlledBy r).filter (fun o =>
        (g.combatDamageToPlayers o.id).contains controller)).map (·.id)
    if ids.isEmpty then
      let g := g.logMsg s!"{(g.player r).name} controls no creature that dealt combat damage this turn"
      advanceSacDamagersAfterLeave g controller rest chosen
    else if ids.size == 1 then
      advanceSacDamagersAfterLeave g controller rest (chosen.push (r, ids[0]!))
    else
      (g.change (.pending (.fraChoice r (.sacrificeDamager ids rest controller chosen)))).logMsg
        s!"{(g.player r).name} chooses a creature that dealt combat damage to sacrifice"

/-- After `p` leaves, pending costs they would pay are not paid (CR 800.4f)
and other pending choices they would make are skipped or passed on
(CR 800.4g / 800.4h / 800.4j). Does not grant priority. -/
def redirectPendingAfterLeave (g : Game) (p : PlayerId) : Game :=
  match g.pending with
  | .none => g
  | .declareAttackers =>
    if g.activePlayer == p then
      g.change (.pending .none)
        |>.logMsg "no active player declares attackers (CR 800.4j)"
    else g
  | .declareBlockers =>
    let filtered := g.blockersQueue.filter (· != p)
    if g.currentBlockersPlayer == p then
      if filtered.isEmpty then
        let g := g.changes #[.pending .none, .blockersQueue #[]]
        let g := g.withBatch (some (.turnBased .declareBlockers)) fun g =>
          g.battlefield.foldl (fun acc o =>
            if o.status.attacking && !o.status.blocked then
              acc.record (GameEvent.remainedUnblocked acc.turnNumber (acc.snapshot o)
                (cause := some (.turnBased .declareBlockers)))
            else acc) g
        g.logMsg "no active player remains to declare blockers (CR 800.4j)"
      else
        g.changes #[.pending .declareBlockers, .blockersQueue filtered]
    else if filtered != g.blockersQueue then
      g.change (.blockersQueue filtered)
    else g
  | .payOrLetCounter q _ spellId =>
    if q == p then
      let g := g.change (.pending .none)
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      if g.unlessPaysInstead.isSome then
        g.change (.unlessPaysDue true)
      else
        let caster := g.unlessPaysController
        let g := g.clearUnlessPays
        match (g.findObject? spellId).filter (·.zone == .stack) with
        | none => g
        | some _ => g.counterStackSpell spellId (controller := some caster)
    else g
  | .payWard q spellId _ =>
    if q == p then
      let g := g.change (.pending .none)
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      match (g.findObject? spellId).filter (·.zone == .stack) with
      | none => g
      | some _ =>
        let wardCtrl := ((g.resolvingAbility.bind g.findObject?).bind (·.controller)).getD (g.opponent p)
        g.counterStackSpell spellId (controller := some wardCtrl)
    else g
  | .mayPayGeneric q _ =>
    if q == p then
      let g := g.changes #[.pending .none, .mayPayAlsoPlusOneOn none]
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else g
      g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
    else g
  | .chooseSacrificeCreature q chosen remaining =>
    let livingRem := remaining.filter g.stillInGame
    if q != p then
      if livingRem != remaining then
        g.change (.pending (.chooseSacrificeCreature q chosen livingRem))
      else g
    else
      match g.nextActorWithCreatures livingRem with
      | none =>
        let skipped := livingRem.filter (fun r => (g.creaturesControlledBy r).isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no creature to sacrifice")
        g.finishChosenSacrifices chosen
      | some (np, rest) =>
        let prefixIdx := livingRem.findIdx? (· == np) |>.getD 0
        let skipped := (livingRem.extract 0 prefixIdx).filter (fun r => (g.creaturesControlledBy r).isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no creature to sacrifice")
        (g.change (.pending (.chooseSacrificeCreature np chosen (rest.filter g.stillInGame)))).logMsg
          s!"{(g.player np).name} must sacrifice a creature"
  | .chooseDiscardCard q remaining =>
    let livingRem := remaining.filter g.stillInGame
    if q != p then
      if livingRem != remaining then
        g.change (.pending (.chooseDiscardCard q livingRem))
      else g
    else
      match g.nextActorWithHandCard livingRem with
      | none =>
        let skipped := livingRem.filter (fun r => (g.player r).hand.isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no card to discard")
        g.changes #[.pending .none, .pendingDiscardsLeft 0]
      | some (np, rest) =>
        let prefixIdx := livingRem.findIdx? (· == np) |>.getD 0
        let skipped := (livingRem.extract 0 prefixIdx).filter (fun r => (g.player r).hand.isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no card to discard")
        (g.changes #[
          .pendingDiscardsLeft 0,
          .pending (.chooseDiscardCard np (rest.filter g.stillInGame))]).logMsg
          s!"{(g.player np).name} must discard a card"
  | .chooseTriggerToStack q =>
    if q == p then g.change (.pending .none) else g
  | .chooseLegend q _ _ =>
    if q == p then g.change (.pending .none) else g
  | .chooseReplacement q _ =>
    if q == p then
      if g.proposedSpell.any (·.caster == p) then
        let closeInfo? :=
          (g.pendingReplacement.bind findPausedCloseBatch?).orElse (fun _ =>
            g.outerPendingReplacements.findSomeRev? findPausedCloseBatch?)
        let g := g.changes #[.pending .none, .pendingReplacement none, .proposedSpell none, .clearProposalCheckpoint]
        match closeInfo? with
        | some (batchId, startIdx) => g.finishOpenBatch batchId startIdx
        | none => if g.currentBatch.isSome then g.change .clearPausedBatch else g
      else
        -- CR 800.4h: keep `pendingReplacement` and any enclosing open batch intact so
        -- draining continuations transfers the replacement choice to the next living
        -- player (via `selectNextReplacementStep`) or finishes the event cleanly.
        g.change (.pending .none)
    else g
  | .assignCombatDamage q forAttackers =>
    let cleanAsgns := g.pendingBlockerAssignments.filter fun a =>
      (g.findObject? a.source).any (·.isOnBattlefield) &&
        a.toCreatures.all (fun (tid, _) => (g.findObject? tid).any (·.isOnBattlefield))
    let g :=
      if cleanAsgns != g.pendingBlockerAssignments then
        g.change (.pendingBlockerAssignments cleanAsgns)
      else g
    let already := cleanAsgns.map (·.source)
    let playerStillNeeds (r : PlayerId) : Bool :=
      (g.creaturesAssigningCombatDamage forAttackers).any fun o =>
        g.controlledBy o r && !already.contains o.id &&
          (g.legalCombatDamageRecipients o forAttackers).size ≥ 2 && g.combatDamageAmount o > 0
    if q == p then
      if forAttackers then
        g.changes #[.pending .none, .pendingBlockerAssignments #[]]
          |>.logMsg "no active player assigns combat damage (CR 800.4j)"
      else
        let nextP? := g.apnapPlayers.find? (fun r =>
          r != p && r != g.activePlayer && g.stillInGame r && playerStillNeeds r)
        match nextP? with
        | some nextP =>
          g.change (.pending (.assignCombatDamage nextP false))
            |>.logMsg s!"{(g.player nextP).name} assigns combat damage (CR 800.4h)"
        | none =>
          g.change (.pending .none)
    else if playerStillNeeds q then g
    else if forAttackers then
      g.change (.pending .none)
    else
      let nextP? := g.apnapPlayers.find? (fun r =>
        r != q && r != p && r != g.activePlayer && g.stillInGame r && playerStillNeeds r)
      match nextP? with
      | some nextP =>
        g.change (.pending (.assignCombatDamage nextP false))
          |>.logMsg s!"{(g.player nextP).name} assigns combat damage (CR 800.4h)"
      | none =>
        g.change (.pending .none)
  | .chooseMode q =>
    if q == p then
      let clearProp : Array EngineChange :=
        if g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      g.changes (#[.pending .none] ++ clearProp)
    else
      (g.change (.pending .none)).chainPendingReplacement (.finishPostStep 88 q)
  | .chooseTargets q =>
    if q == p then
      let clearProp : Array EngineChange :=
        if g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      g.changes (#[.pending .none] ++ clearProp)
    else
      (g.change (.pending .none)).chainPendingReplacement (.finishPostStep 89 q)
  | .activateManaAbilities q | .chooseX q
  | .chooseAdditionalCost q | .chooseKicker q | .chooseGift q
  | .chooseTeamwork q | .chooseTeamworkCreatures q _
  | .sacrificePermanent q _ | .discardForAdditionalCost q =>
    if q == p then
      let clearProp : Array EngineChange :=
        if g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      g.changes (#[.pending .none] ++ clearProp)
    else g
  | .fraChoice q choice =>
    let clearProp : Array EngineChange :=
      if q == p && g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
      else #[]
    match choice with
    | .mayWheel n rest =>
      let living := rest.filter g.stillInGame
      if q != p then
        if living != rest then g.change (.pending (.fraChoice q (.mayWheel n living))) else g
      else
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match living[0]? with
        | none => g.change (.pending .none)
        | some next =>
          (g.change (.pending (.fraChoice next (.mayWheel n (living.extract 1 living.size))))).logMsg
            s!"{(g.player next).name} may discard their hand and draw {n} cards"
    | .sacrificeCreatureEach controller rest chosen =>
      let living := rest.filter (fun r => g.stillInGame r && !(g.creaturesControlledBy r).isEmpty)
      if q != p then
        if living != rest then g.change (.pending (.fraChoice q (.sacrificeCreatureEach controller living chosen))) else g
      else
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match living[0]? with
        | some next =>
          (g.change (.pending (.fraChoice next (.sacrificeCreatureEach controller (living.extract 1 living.size) chosen)))).logMsg
            s!"{(g.player next).name} sacrifices a creature"
        | none =>
          let youSacrificed :=
            g.stillInGame controller &&
              chosen.any (fun id => (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o controller))
          let pairs := chosen.filterMap (fun id =>
            match g.findObject? id with
            | some o => if o.isOnBattlefield then some ((g.controllerOf o).getD o.owner, id) else none
            | none => none)
          let preBf := g.battlefield
          let g := g.change (.pending .none)
          g.withBatch none fun g =>
            g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)
              (createBeastFor := if youSacrificed then some controller else none)
    | .sacrificeNontokenEach rest chosen =>
      let hasNontoken (r : PlayerId) :=
        g.stillInGame r && (g.permanentsOf r).any (fun o => g.isCreature o && !o.printed.isToken)
      let living := rest.filter hasNontoken
      if q != p then
        if living != rest then g.change (.pending (.fraChoice q (.sacrificeNontokenEach living chosen))) else g
      else
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match living[0]? with
        | some next =>
          (g.change (.pending (.fraChoice next (.sacrificeNontokenEach (living.extract 1 living.size) chosen)))).logMsg
            s!"{(g.player next).name} sacrifices a nontoken creature"
        | none =>
          let pairs := chosen.filterMap (fun id =>
            match g.findObject? id with
            | some o => if o.isOnBattlefield then some ((g.controllerOf o).getD o.owner, id) else none
            | none => none)
          let preBf := g.battlefield
          let g := g.change (.pending .none)
          g.withBatch none fun g =>
            g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)
    | .sacrificeDamager ids rest controller chosen =>
      let living := rest.filter g.stillInGame
      if q != p then
        if living != rest then g.change (.pending (.fraChoice q (.sacrificeDamager ids living controller chosen))) else g
      else
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        advanceSacDamagersAfterLeave g controller living chosen
    | .discardTwo controller rest draws =>
      let living := rest.filter g.stillInGame
      if q != p then
        if living != rest then g.change (.pending (.fraChoice q (.discardTwo controller living draws))) else g
      else
        let g := g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
        match living[0]? with
        | some next =>
          if (g.player next).hand.size > 2 then
            (g.change (.pending (.fraChoice next (.discardTwo controller (living.extract 1 living.size) draws)))).logMsg
              s!"{(g.player next).name} discards two cards"
          else
            g.chainPendingReplacement
              (.finishPostStep 10 controller (n := draws) (modes := living.map (·.idx)))
        | none =>
          if g.stillInGame controller && draws > 0 then
            g.chainPendingReplacement (.finishPostStep 10 controller (n := draws) (modes := #[]))
          else g
    | .worldsPutCreatures eligible rest exiled chosen sourceId =>
      let living := rest.filter g.stillInGame
      if q != p then
        if living != rest then
          g.change (.pending (.fraChoice q (.worldsPutCreatures eligible living exiled chosen sourceId)))
        else g
      else
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let rec offerNext : List PlayerId → Game
          | [] =>
            (g.change (.pending .none)).chainPendingReplacement
              (.finishPostStep 67 g.activePlayer (sourceId := sourceId) (ids := exiled)
                (targets := chosen.map Target.card))
          | r :: more =>
            let elig := (g.player r).hand.filter (fun id => (g.findObject? id).any g.isCreature)
            if elig.isEmpty then offerNext more
            else
              (g.change (.pending (.fraChoice r (.worldsPutCreatures elig more.toArray exiled chosen sourceId)))).logMsg
                s!"{(g.player r).name} may put any number of creature cards from their hand onto the battlefield"
        offerNext living.toList
    | .chooseEnteringAttackTarget remaining chosen cause =>
      let chosenClean := chosen.filterMap fun (item, tgt?) =>
        match sanitizeEnteringAttackItem g item with
        | none => none
        | some item' =>
          let validTgt? := tgt?.filter (fun t => (filterLivingAttackTargets g item'.controller #[t]).size == 1)
          some (item', validTgt?.orElse (fun _ => item'.options[0]?))
      if q != p then
        let remClean := remaining.filterMap (sanitizeEnteringAttackItem g)
        if remClean.isEmpty then
          (g.change (.pending .none)).chainPendingReplacement
            (.commitEnteringAttackItems chosenClean cause true)
        else if remClean != remaining || chosenClean != chosen then
          let nextCtrl := remClean[0]!.controller
          g.change (.pending (.fraChoice nextCtrl (.chooseEnteringAttackTarget remClean chosenClean cause)))
        else g
      else
        let remTail := (remaining.extract 1 remaining.size).filterMap (sanitizeEnteringAttackItem g)
        let (restAfter, chosen') := advanceFixedEnteringAttackItems remTail chosenClean
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match restAfter[0]? with
        | some nextItem =>
          let nextCtrl := nextItem.controller
          let nextNm := g.enteringAttackItemName nextItem
          (g.change (.pending (.fraChoice nextCtrl (.chooseEnteringAttackTarget restAfter chosen' cause)))).logMsg
            s!"{(g.player nextCtrl).name} chooses what {nextNm} enters attacking"
        | none =>
          (g.change (.pending .none)).chainPendingReplacement
            (.commitEnteringAttackItems chosen' cause true)
    | .discardFromRevealedHand victim _ | .exileFromRevealedHand victim _ =>
      if p == victim || q == p then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else g
    | .extrapolatePick revealer ids =>
      if p == revealer then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match (g.livingOpponents revealer)[0]? with
        | some opp =>
          (g.change (.pending (.fraChoice opp.id (.extrapolatePick revealer ids)))).logMsg
            s!"{opp.name} chooses one of them (CR 800.4h)"
        | none =>
          let g := g.change (.pending .none)
          match ids.find? (fun id => (g.findObject? id).isSome) with
          | some id =>
            let name := (g.object! id).name
            let (g, _) := g.move id (.hand revealer) none
            g.logMsg s!"{(g.player revealer).name} puts {name} into their hand"
          | none => g
      else g
    | .riddlesChoosePile controller faceUp faceDown =>
      if p == controller then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match (g.livingOpponents controller)[0]? with
        | some opp =>
          (g.change (.pending (.fraChoice opp.id (.riddlesChoosePile controller faceUp faceDown)))).logMsg
            s!"{opp.name} chooses a pile (CR 800.4h)"
        | none =>
          let g := g.change (.pending .none)
          let g := g.withBatch none fun g =>
            faceUp.foldl (fun acc id =>
              if (acc.findObject? id).isSome then (acc.move id (.hand controller) none).1 else acc) g
          g.withBatch none fun g =>
            faceDown.foldl (fun acc id =>
              if (acc.findObject? id).isSome then (acc.move id (.graveyard controller) none).1 else acc) g
      else g
    | .palantirMayDraw controller sourceId =>
      if p == controller then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else if q == p then
        let g := g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
        if g.stillInGame controller then
          g.chainPendingReplacement (.finishPostStep 78 controller (sourceId := some sourceId))
        else g
      else g
    | .tricksterLibrary caster _id connive =>
      if p == caster then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else if q == p then
        let g := g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
        if g.stillInGame caster && connive.isSome then
          g.chainPendingReplacement (.connive caster connive)
        else g
      else g
    | .mayCastGrima cardId others victim =>
      if p == victim then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else if q == p then
        let g := g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
        if g.stillInGame victim then
          let live := (others.push cardId).filter (fun id => (g.findObject? id).any (·.zone == .exile))
          if live.isEmpty then g
          else
            let cause := g.lastMoveCauseOf? cardId
            g.requestOrderInto live (.library victim)
              s!"{(g.player victim).name} puts the exiled cards on the bottom of their library in a random order"
              (cause := cause)
        else g
      else g
    | .mayBeginOnBattlefield cards =>
      let liveCards := cards.filter (fun id =>
        (g.findObject? id).any (fun o => g.stillInGame o.owner && o.zone == .hand o.owner))
      if liveCards.isEmpty then
        g.changes (#[.pending .none, .chooseModesRest none] ++ (if q == p then clearProp else #[]))
      else
        let firstObj := g.object! liveCards[0]!
        let nextOwner := firstObj.owner
        if q == p then
          (g.changes (#[.chooseModesRest none,
            .pending (.fraChoice nextOwner (.mayBeginOnBattlefield liveCards))] ++ clearProp)).logMsg
            s!"{(g.player nextOwner).name} may begin the game with {firstObj.name} on the battlefield"
        else if liveCards != cards then
          g.change (.pending (.fraChoice nextOwner (.mayBeginOnBattlefield liveCards)))
        else g
    | .triggerModes objId remaining chosen =>
      if q == p then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else
        (g.change (.pending .none)).chainPendingReplacement
          (.finishPostStep 90 q (n := remaining) (sourceId := some objId) (modes := chosen))
    | .blackGatePlayer oid players =>
      let players' := players.filter g.stillInGame
      if q == p then
        g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
      else if players'.isEmpty then
        g.changes #[.pending .none, .chooseModesRest none]
      else if players'.size == 1 then
        (g.changes #[.pending .none, .chooseModesRest none]).applyBlackGateUnblockable oid players'[0]!
      else if players' != players then
        g.change (.pending (.fraChoice q (.blackGatePlayer oid players')))
      else g
    | _ =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        if g.mayThenDrop > 0 then g.declineMayThenCore
        else g.change (.pending .none)
      else g
  | .mayDiscardDraw q _ | .maySacArtifactOrDiscard q _ =>
    if q == p then
      let clearProp : Array EngineChange :=
        if g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[.chooseModesRest none] ++ clearProp)
      let g :=
        if g.mayThenDrop > 0 then g.declineMayThenCore
        else g.change (.pending .none)
      g.logMsg s!"{(g.player p).name} declines (CR 800.4f)"
    else g
  | .sacrificeCreature q | .scry q .. | .surveil q ..
  | .mayAttachEquipment q _
  | .recruitDiscard q
  | .maySacrificeAnotherBolg q _ | .mayCastFromLooked q _ _ | .putOnBottom q _
  | .mayPutLandFromHand q
  | .mayHaveVillainConnive q _ _ | .declareMulligan q | .chooseProliferate q _ =>
    if q == p then
      let clearProp : Array EngineChange :=
        if g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
    else g
  | .mayCastExiledElseDamage q _ n sid =>
    if q == p then
      let g := (g.change (.pending .none)).logMsg s!"{(g.player p).name} declines (CR 800.4f)"
      if n > 0 then
        g.chainPendingReplacement
          (.finishPostStep 33 p (n := n) (sourceId := sid)
            (cause := some (g.resolvingOrRuleCause p sid)))
      else g
    else g
  | .chooseTriggerOr q =>
    if q == p then g.changes #[.pending .none, .triggerOr none] else g
  | .tapHumans q =>
    if q == p then
      g.changes #[
        .pending .none,
        .triggerSequenceRest none,
        .humansTappedThisWay 0]
    else g
  | .mayPutArtifactFromHand q _ =>
    if q == p then
      g.changes #[
        .pending .none,
        .triggerSequenceRest none,
        .putArtifactThisWay none]
    else g
  | .mayResolve q =>
    if q == p then (g.change (.pending .none)).clearMay else g
  | .chooseLibraryPlacement q _ =>
    if q == p then (g.change (.pending .none)).clearSpellOr else g
  | .resolveRandom req =>
    match req with
    | .shuffleLibrary q =>
      if q == p then
        let clearAfter : Array EngineChange :=
          if afterRandomReferencesPlayer p g.afterRandom then #[.afterRandom .none] else #[]
        g.changes (#[.pending .none] ++ clearAfter)
      else if afterRandomReferencesPlayer p g.afterRandom then
        g.change (.afterRandom .none)
      else g
    | .orderInto ids dest cause =>
      let destGone :=
        match dest with
        | .library q | .hand q | .graveyard q | .outside q => q == p || !g.stillInGame q
        | _ => false
      let liveIds := ids.filter (fun id => (g.findObject? id).isSome)
      if destGone || liveIds.isEmpty then
        g.change (.pending .none)
      else if liveIds.size == 1 then
        (g.change (.pending .none)).moveIdsInOrder liveIds dest (cause := cause)
      else if liveIds != ids then
        g.change (.pending (.resolveRandom (.orderInto liveIds dest cause)))
      else g
    | .chooseObject ids =>
      let liveIds := ids.filter (fun id => (g.findObject? id).isSome)
      if afterRandomReferencesPlayer p g.afterRandom || liveIds.isEmpty then
        g.changes #[.pending .none, .afterRandom .none]
      else if liveIds != ids then
        g.change (.pending (.resolveRandom (.chooseObject liveIds)))
      else g
    | .chooseIndex _ =>
      if g.pregameRandom == .none && (g.currentResolvingContext?.bind Prod.snd) == some p then
        g.changes #[.pending .none, .afterRandom .none]
      else g

/-- `p` loses and leaves the game (CR 800.4 / 800.4a). Owned objects leave
immediately (until-leaves one-shots return); control-changing effects that
gave them control end; their non-card stack objects cease; remaining objects
they control are exiled. This is not a state-based action. -/
def playerLeavesGame (g : Game) (p : PlayerId) : Game :=
  if (g.player p).leftTheGame then g
  else
    let cause := some (EventCause.gameRule .playerLeftGame)
    let wasMonarch := (g.player p).isMonarch
    let owned := g.objects.filter (fun o => o.owner == p && o.zone != .ante)
    let linkedExileIds := owned.foldl (fun acc o =>
      if o.zone == .battlefield then acc ++ o.linkedExile else acc) #[]
    let g := g.withBatchCore cause fun g =>
      let g := g.record (GameEvent.playerLeftGame g.turnNumber p (cause := cause))
      let g := g.logMsg s!"{(g.player p).name} leaves the game"
      let g :=
        if wasMonarch && !g.over && g.livingPlayers.size > 1 then
          let heir :=
            if g.stillInGame g.activePlayer && g.activePlayer != p then g.activePlayer
            else g.nextLiving p
          (g.record (GameEvent.becameMonarch g.turnNumber heir (some p) (cause := cause))).logMsg
            s!"{(g.player heir).name} becomes the monarch (CR 725.4)"
        else g
      let g :=
        owned.foldl (fun acc o =>
          match acc.findObject? o.id with
          | none => acc
          | some o => acc.objectLeavesTheGame o p) g
      let g :=
        g.activeEffects.foldl (fun acc (eid, e) =>
          match e with
          | .layered _ (.control c) _ =>
            if c == p then acc.endControlEffectById eid (cause := cause) else acc
          | .playerRule you (.controlsPlayer them _) _ =>
            if you == p || them == p then acc.expireEffectById eid (cause := cause) else acc
          | _ => acc) g
      let g :=
        g.objects.foldl (fun acc o =>
          if o.zone == .stack && acc.controlledBy o p && !representedByCard o then
            acc.ceaseToExist o.id (cause := cause)
          else acc) g
      let still := g.objects.filter (fun o =>
        g.controlledBy o p ||
          (o.isBattlefieldObject && (g.appliedControlEffectIds o).isEmpty &&
            ((o.defaultController.orElse (fun _ => o.controller)).getD o.owner) == p))
      let exileQueue := still.filterMap fun o =>
        (g.findObject? o.id).map (fun cur => (cur.id, s!"{g.name cur} is exiled (CR 800.4a)"))
      g.runEndControlExileLoop exileQueue (cause := cause)
    let g :=
      if g.mulliganToDeclare.contains p then
        g.change (.mulliganToDeclare (g.mulliganToDeclare.filter (· != p)))
      else g
    let g :=
      if g.willMulligan.contains p then
        g.change (.willMulligan (g.willMulligan.filter (· != p)))
      else g
    let g :=
      if g.mulliganToBottom.contains p then
        g.change (.mulliganToBottom (g.mulliganToBottom.filter (· != p)))
      else g
    let g :=
      if g.priority == p then g.change (.priority (g.nextLiving p)) else g
    let g :=
      if g.pendingPriority == some p then g.change (.pendingPriority (some (g.nextLiving p))) else g
    let wasCasterProposal := g.proposedSpell.any (fun prop => prop.caster == p)
    let g := g.redirectPendingAfterLeave p
    let g :=
      match g.postCastCleanup with
      | some (.grimaBottom victim cardId others) =>
        if p == victim then
          g.change (.postCastCleanup none)
        else if wasCasterProposal then
          let g := g.changes #[.proposedSpell none, .clearProposalCheckpoint, .postCastCleanup none]
          if g.stillInGame victim then
            let live := (others.push (g.followMoved cardId)).filter (fun id =>
              (g.findObject? id).any (fun (o : GameObject) => o.zone == Zone.exile))
            if live.isEmpty then g
            else
              let c := g.lastMoveCauseOf? cardId
              g.requestOrderInto live (.library victim)
                s!"{(g.player victim).name} puts the exiled cards on the bottom of their library in a random order"
                (cause := c)
          else g
        else g
      | _ => g
    let g :=
      if g.proposedSpell.any (fun (prop : ProposedSpell) => prop.caster == p) then
        g.changes #[.proposedSpell none, .clearProposalCheckpoint]
      else g
    let allLinked := linkedExileIds ++ g.queuedLinkedExile
    let g := if g.queuedLinkedExile.isEmpty then g else g.change .clearQueuedLinkedExile
    if allLinked.isEmpty then g
    else if g.sbaPaused || g.currentBatch.isSome then
      g.chainPendingReplacement (.finishLinkedExileMove allLinked)
    else if g.pending != .none then
      let saved := g.pending
      let outerCont? := g.pendingReplacement
      let g :=
        match outerCont? with
        | some outer => (g.change (.pendingReplacement none)).change (.pushOuterPendingReplacement outer)
        | none => g
      let g := (g.change (.pending .none)).returnLinkedExileMoves allLinked
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.restorePending saved)
      else
        let g :=
          if outerCont?.isSome then
            match g.outerPendingReplacements.back? with
            | some popped => g.changes #[.popOuterPendingReplacement, .pendingReplacement (some popped)]
            | none => g
          else g
        g.change (.pending saved)
    else
      let outerCont? := g.pendingReplacement
      let g :=
        match outerCont? with
        | some outer => (g.change (.pendingReplacement none)).change (.pushOuterPendingReplacement outer)
        | none => g
      let g := g.returnLinkedExileMoves allLinked
      if g.pending == .none && g.pendingReplacement.isNone && outerCont?.isSome then
        match g.outerPendingReplacements.back? with
        | some popped => g.changes #[.popOuterPendingReplacement, .pendingReplacement (some popped)]
        | none => g
      else g

/-- Perform CR 800.4a for every player who has lost but has not yet left.
Skipped when the game has already ended (two-player games, CR 104.2a). If a
departing player's post-departure `returnLinkedExileMoves` pauses on
`Pending.chooseReplacement`, chains `.leavePlayersWhoLost` for any remaining
losers (CR 104.5 / 800.4a). -/
def leavePlayersWhoLost (g : Game) : Game :=
  if g.over then g
  else if let .chooseReplacement .. := g.pending then
    if g.players.any (fun pl => pl.lost && !pl.leftTheGame) then
      g.chainPendingReplacement .leavePlayersWhoLost
    else g
  else Id.run do
    let mut g := g
    for pl in g.players do
      if g.over then
        return g
      if pl.lost && !(g.player pl.id).leftTheGame then
        g := g.playerLeavesGame pl.id
        if let .chooseReplacement .. := g.pending then
          if g.players.any (fun r => r.lost && !r.leftTheGame) then
            g := g.chainPendingReplacement .leavePlayersWhoLost
          return g
    return g

def emptyManaPools (g : Game) : Game :=
  Id.run do
    let mut g := g
    let cause := some (EventCause.turnBased .emptyManaPools)
    for pl in g.players do
      if !pl.manaPool.isEmpty then
        let colorless :=
          (g.permanentsOf pl.id).any (fun o =>
            (g.baseCard o).unspentManaBecomesColorless && g.retainsPrintedAbilities o)
        let units := pl.manaPool.toUnits
        if colorless then
          g := g.record (GameEvent.manaEmptied g.turnNumber pl.id units true (cause := cause))
          g := g.logMsg s!"{pl.name}'s unspent mana becomes colorless"
        else
          g := g.logMsg s!"{pl.name} empties mana pool ({pl.manaPool})"
          g := g.record (GameEvent.manaEmptied g.turnNumber pl.id units false (cause := cause))
    return g

end Game
end Mtg.Engine
