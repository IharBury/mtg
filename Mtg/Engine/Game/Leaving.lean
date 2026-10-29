import Mtg.Engine.Game.Movement

/-!
# Game end and leaving the game (CR 104 / 800.4)

Deciding a finished game, control-changing effects and their end
(CR 800.4a / 800.4c), objects and pending decisions of a player who
leaves a multiplayer game, and emptying mana pools (CR 500.4).
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
    g.createEffect (.control o.id p untilEot turnEndsLeft untilSourceLeaves) (cause := cause)
      |>.logMsg s!"{(g.player p).name} gains control of {g.name o}"

/-- End the control-changing effect recorded under `eid` on `oid`. Any other
control-changing effects on that permanent keep applying, and the most recent
of them decides its controller (CR 613.1b / 613.7). When none remain and the
default controller has left the game, the permanent is exiled (CR 800.4a /
800.4c). -/
def endControlEffect (g : Game) (oid : ObjectId) (eid : EffectId)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? oid with
  | none => g.expireEffectById eid (cause := cause)
  | some o =>
    let prevCtrl := g.controllerOf o
    let hadControlChange := g.controlChanged o
    let g := g.expireEffectById eid (cause := cause)
    let othersRemain := g.activeEffects.any (fun (_, e) =>
      match e with
      | .layered (.objects #[id]) (.control _) _ => id == oid
      | _ => false)
    match g.findObject? oid with
    | none => g
    | some cur =>
      let curCtrl := g.controllerOf cur
      if othersRemain then
        if curCtrl != prevCtrl then
          g.logMsg s!"{g.name cur} reverts to {(g.player (curCtrl.getD cur.owner)).name}'s control"
        else g
      else if !hadControlChange then g
      else
        let dest := cur.defaultController.getD cur.owner
        if (g.player dest).lost then
          let name := g.name cur
          let (g, _) := g.move oid .exile none (cause := some (.gameRule .playerLeftGame))
          g.logMsg s!"{name} is exiled (CR 800.4c)"
        else
          g.logMsg s!"{g.name cur} reverts to {(g.player dest).name}'s control"

/-- End every control-changing effect on `o`, each under its own `EffectId`
(CR 800.4a / 800.4c). -/
def endControlChangingEffect (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  let ids := g.activeEffects.filterMap (fun (eid, e) =>
    match e with
    | .layered (.objects #[id]) (.control _) _ => if id == o.id then some eid else none
    | _ => none)
  ids.foldl (fun acc eid => acc.endControlEffect o.id eid (cause := cause)) g

/-- Gain control of `o` until end of turn (CR 611.2a). -/
def giveControlUntilEot (g : Game) (o : GameObject) (p : PlayerId) : Game :=
  if (g.player p).lost then
    g.logMsg s!"{o.name} does not change control (CR 800.4b)"
  else
    g.changeControl o p (untilEot := true)

/-- Remove `o` from the game. Battlefield permanents use `move` so
until-leaves one-shots return (CR 610.3 / 800.4a). Ante stays (CR 800.4n). -/
def objectLeavesTheGame (g : Game) (o : GameObject) (leavingPlayer : PlayerId) : Game :=
  let cause := some (EventCause.gameRule .playerLeftGame)
  if o.zone == .ante then g
  else if o.zone == .battlefield then
    let (g, newId) := g.move o.id .exile none (cause := cause)
    let g := g.change (.removeWaitingTriggersOf leavingPlayer)
    g.ceaseToExist newId (cause := cause)
  else
    g.ceaseToExist o.id (cause := cause)

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
    if g.currentBlockersPlayer == p then
      let rest := g.blockersQueue.extract 1 g.blockersQueue.size
      if rest.isEmpty then
        g.changes #[.pending .none, .blockersQueue #[]]
          |>.logMsg "no active player remains to declare blockers (CR 800.4j)"
      else
        g.changes #[.pending .declareBlockers, .blockersQueue rest]
    else g
  | .payOrLetCounter q _ spellId =>
    if q == p then
      let g := g.change (.pending .none)
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      if g.unlessPaysInstead.isSome then
        g.change (.unlessPaysDue true)
      else
        match g.findObject? spellId with
        | none => g
        | some o =>
          let g := g.ceaseToExist o.id (cause := some (.gameRule .playerLeftGame))
          g.logMsg s!"{o.name} is countered"
    else g
  | .payWard q spellId _ =>
    if q == p then
      let g := g.change (.pending .none)
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      match g.findObject? spellId with
      | none => g
      | some o =>
        let g := g.ceaseToExist o.id (cause := some (.gameRule .playerLeftGame))
        g.logMsg s!"{o.name} is countered"
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
  | .chooseLegend q _ _ | .chooseReplacement q _ =>
    if q == p then g.change (.pending .none) else g
  | .assignCombatDamage q forAttackers =>
    if q == p then
      g.change (.pending (.assignCombatDamage (g.nextLiving p) forAttackers))
        |>.logMsg
          s!"{(g.player (g.nextLiving p)).name} assigns combat damage (CR 800.4h)"
    else g
  | .activateManaAbilities q | .chooseMode q | .chooseX q | .chooseTargets q
  | .chooseAdditionalCost q | .chooseKicker q | .chooseGift q
  | .chooseTeamwork q | .chooseTeamworkCreatures q _ =>
    if q == p then g.changes #[.pending .none, .proposedSpell none] else g
  | .sacrificePermanent q _ | .discardForAdditionalCost q
  | .sacrificeCreature q | .scry q .. | .surveil q ..
  | .mayDiscardDraw q _ | .mayAttachEquipment q _
  | .recruitDiscard q | .chooseRingBearer q
  | .maySacrificeAnotherBolg q _ | .mayCastFromLooked q _ _ | .putOnBottom q _
  | .mayPutLandFromHand q
  | .maySacArtifactOrDiscard q _
  | .mayHaveVillainConnive q _ _ | .declareMulligan q | .chooseProliferate q _
  | .fraChoice q _ =>
    if q == p then g.changes #[.pending .none, .chooseModesRest none] else g
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
        | .layered (.objects #[oid]) (.control c) _ =>
          if c == p then acc.endControlEffect oid eid (cause := cause) else acc
        | _ => acc) g
    let g :=
      g.objects.foldl (fun acc o =>
        if o.zone == .stack && acc.controlledBy o p && !representedByCard o then
          acc.ceaseToExist o.id (cause := cause)
        else acc) g
    let still := g.objects.filter (fun o => g.controlledBy o p)
    let g :=
      still.foldl (fun acc o =>
        match acc.findObject? o.id with
        | none => acc
        | some o =>
          let name := acc.name o
          let (acc, _) := acc.move o.id .exile none (cause := cause)
          acc.logMsg s!"{name} is exiled (CR 800.4a)") g
    let g := g.change (.removeWaitingTriggersOf p)
    let g :=
      match g.proposedSpell with
      | some prop =>
        if prop.caster == p then g.change (.proposedSpell none) else g
      | none => g
    let g :=
      if g.priority == p then g.change (.priority (g.nextLiving p)) else g
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
            o.printed.unspentManaBecomesColorless && g.retainsPrintedAbilities o)
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
