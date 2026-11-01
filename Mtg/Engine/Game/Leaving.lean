import Mtg.Engine.Game.Movement

/-!
# Game end and leaving the game (CR 104 / 800.4)

Deciding a finished game, control-changing effects and their end
(CR 800.4a / 800.4c), objects and pending decisions of a player who
leaves a multiplayer game, and emptying mana pools (CR 500.5).
-/

namespace Mtg.Engine
namespace Game

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
      g.battlefield.filterMap fun o =>
        let applied := g.appliedControlEffectIds o
        if applied.contains eid || explicitIds.contains o.id then
          some (o.id, g.controllerOf o, g.controlChanged o || applied.contains eid)
        else none
    let g := g.expireEffectById eid (cause := cause)
    candidates.foldl (fun acc (oid, prevCtrl, hadControlChange) =>
      match acc.findObject? oid with
      | none => acc
      | some cur =>
        if !cur.isOnBattlefield then acc
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
            if curCtrl != prevCtrl then
              acc.logMsg s!"{acc.name cur} reverts to {(acc.player (curCtrl.getD cur.owner)).name}'s control"
            else acc
          else if !hadControlChange then acc
          else
            let dest := curCtrl.getD (cur.defaultController.getD cur.owner)
            if (acc.player dest).lost then
              let name := acc.name cur
              let (acc, _) := acc.move oid .exile none (cause := some (.gameRule .playerLeftGame))
              acc.logMsg s!"{name} is exiled (CR 800.4c)"
            else if curCtrl != prevCtrl || prevCtrl != some dest then
              acc.logMsg s!"{acc.name cur} reverts to {(acc.player dest).name}'s control"
            else acc) g

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
        | .layered _ (.control _) (.untilSourceLeaves s) =>
          if s == o.id then some eid else none
        | _ => none
      if sourceCtrlIds.isEmpty then #[]
      else
        g.battlefield.filterMap fun pObj =>
          if pObj.id != o.id &&
              (g.appliedControlEffectIds pObj).any (fun eid => sourceCtrlIds.contains eid) then
            some pObj.id
          else none
    let g := g.withBatch cause fun g =>
      let g := g.unattachFrom o.id
      let g := g.removePreparedCopy o.id
      let g := g.ceaseToExist o.id (cause := cause)
      sourceCtrlTargets.foldl (fun acc tid =>
        match acc.findObject? tid with
        | none => acc
        | some cur =>
          if !cur.isOnBattlefield || !(acc.appliedControlEffectIds cur).isEmpty then acc
          else
            let destP := (acc.controllerOf cur).getD (cur.defaultController.getD cur.owner)
            if (acc.player destP).lost then
              let name := acc.name cur
              let (acc, _) := acc.move tid .exile none (cause := cause)
              acc.logMsg s!"{name} is exiled (CR 800.4c)"
            else acc) g
    if !o.linkedExile.isEmpty then
      g.returnLinkedExileMoves o.linkedExile
    else g
  else
    g.ceaseToExist o.id (cause := cause)

private def findPausedCloseBatch? : PendingReplacement → Option (BatchId × Nat)
  | .closeBatch b s => some (b, s)
  | .seq a b => findPausedCloseBatch? a <|> findPausedCloseBatch? b
  | _ => none

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
      g.change (.pending .none)
        |>.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
    else g
  | .chooseSacrificeCreature q chosen remaining =>
    if q != p then g
    else
      match remaining.find? (fun r => g.stillInGame r) with
      | none => g.change (.pending .none)
      | some np =>
        g.change (.pending (.chooseSacrificeCreature np chosen
          (remaining.filter (fun r => r != np && g.stillInGame r))))
  | .chooseDiscardCard q remaining =>
    if q != p then g
    else
      match remaining.find? (fun r => g.stillInGame r) with
      | none => g.changes #[.pending .none, .pendingDiscardsLeft 0]
      | some np =>
        g.changes #[
          .pendingDiscardsLeft 0,
          .pending (.chooseDiscardCard np
            (remaining.filter (fun r => r != np && g.stillInGame r)))]
  | .chooseTriggerToStack q =>
    if q == p then g.change (.pending .none) else g
  | .chooseLegend q _ _ =>
    if q == p then g.change (.pending .none) else g
  | .chooseReplacement q _ =>
    if q == p then
      let closeInfo? := g.pendingReplacement.bind findPausedCloseBatch?
      let clearProp : Array EngineChange :=
        if g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[.pending .none, .pendingReplacement none] ++ clearProp)
      match closeInfo? with
      | some (batchId, startIdx) => g.finishOpenBatch batchId startIdx
      | none => if g.currentBatch.isSome then g.change .clearPausedBatch else g
    else g
  | .assignCombatDamage q forAttackers =>
    if q == p then
      if forAttackers then
        g.changes #[.pending .none, .pendingBlockerAssignments #[]]
          |>.logMsg "no active player assigns combat damage (CR 800.4j)"
      else
        let already := g.pendingBlockerAssignments.map (·.source)
        let nextP? := g.apnapPlayers.find? (fun r =>
          r != p && r != g.activePlayer && g.stillInGame r &&
            g.battlefield.any (fun o =>
              g.isCreature o && g.controlledBy o r && !already.contains o.id &&
                o.status.blocking.size ≥ 2 && (g.power o) > 0))
        match nextP? with
        | some nextP =>
          g.change (.pending (.assignCombatDamage nextP false))
            |>.logMsg s!"{(g.player nextP).name} assigns combat damage (CR 800.4h)"
        | none =>
          g.change (.pending .none)
    else g
  | .activateManaAbilities q | .chooseMode q | .chooseX q | .chooseTargets q
  | .chooseAdditionalCost q | .chooseKicker q | .chooseGift q
  | .chooseTeamwork q | .chooseTeamworkCreatures q _
  | .sacrificePermanent q _ | .discardForAdditionalCost q =>
    if q == p then g.changes #[.pending .none, .proposedSpell none, .clearProposalCheckpoint] else g
  | .sacrificeCreature q | .scry q .. | .surveil q ..
  | .mayDiscardDraw q _ | .mayAttachEquipment q _
  | .recruitDiscard q | .chooseRingBearer q
  | .maySacrificeAnotherBolg q _ | .mayCastFromLooked q _ _ | .putOnBottom q _
  | .mayPutLandFromHand q
  | .maySacArtifactOrDiscard q _
  | .mayHaveVillainConnive q _ _ | .declareMulligan q | .chooseProliferate q _
  | .fraChoice q _ =>
    if q == p then
      let clearProp : Array EngineChange :=
        if g.proposedSpell.any (·.caster == p) then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      g.changes (#[.pending .none, .chooseModesRest none] ++ clearProp)
    else g
  | .mayCastExiledElseDamage q .. =>
    if q == p then g.change (.pending .none) else g
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
  | .resolveRandom _ => g

/-- `p` loses and leaves the game (CR 800.4 / 800.4a). Owned objects leave
immediately (until-leaves one-shots return); control-changing effects that
gave them control end; their non-card stack objects cease; remaining objects
they control are exiled. This is not a state-based action. -/
def playerLeavesGame (g : Game) (p : PlayerId) : Game :=
  if (g.player p).leftTheGame then g
  else
    let cause := some (EventCause.gameRule .playerLeftGame)
    let g := g.record (GameEvent.playerLeftGame g.turnNumber p (cause := cause))
    let g := g.logMsg s!"{(g.player p).name} leaves the game"
    let owned := g.objects.filter (fun o => o.owner == p && o.zone != .ante)
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
        (o.zone == .battlefield && (g.appliedControlEffectIds o).isEmpty &&
          ((o.defaultController.orElse (fun _ => o.controller)).getD o.owner) == p))
    let g :=
      still.foldl (fun acc o =>
        match acc.findObject? o.id with
        | none => acc
        | some o =>
          let name := acc.name o
          let (acc, _) := acc.move o.id .exile none (cause := cause)
          acc.logMsg s!"{name} is exiled (CR 800.4a)") g
    let g :=
      match g.proposedSpell with
      | some prop =>
        if prop.caster == p then g.changes #[.proposedSpell none, .clearProposalCheckpoint] else g
      | none => g
    let g :=
      if g.priority == p then g.change (.priority (g.nextLiving p)) else g
    let g :=
      if g.pendingPriority == some p then g.change (.pendingPriority (some (g.nextLiving p))) else g
    g.redirectPendingAfterLeave p

/-- Perform CR 800.4a for every player who has lost but has not yet left.
Skipped when the game has already ended (two-player games, CR 104.2a). -/
def leavePlayersWhoLost (g : Game) : Game :=
  if g.over then g
  else
    g.players.foldl (fun acc pl =>
      if pl.lost && !pl.leftTheGame then acc.playerLeavesGame pl.id else acc) g

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
