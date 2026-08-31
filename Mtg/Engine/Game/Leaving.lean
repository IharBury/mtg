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
    some ({ g with result := some .draw } |>.logMsg "The game is a draw")
  else if living.size == 1 then
    let w := living[0]!
    some ({ g with result := some (.won w.id) } |>.logMsg s!"{w.name} wins the game")
  else none

/-- True when this stack object is a card (CR 800.4a). Activated and
triggered abilities, and copies of spells, are not represented by cards. -/
def representedByCard (o : GameObject) : Bool :=
  o.abilityEffect.isNone && o.triggeredAbility.isNone && !o.isCopy

/-- Change `o`'s controller unless that player has left (CR 800.4b). -/
def changeControl (g : Game) (o : GameObject) (p : PlayerId) : Game :=
  if (g.player p).lost then
    g.logMsg s!"{o.name} does not change control (CR 800.4b)"
  else if o.controlledBy p then g
  else
    g.setObject { o with controller := some p, controlChanged := true }
      |>.logMsg s!"{(g.player p).name} gains control of {o.name}"

/-- End a control-changing effect on `o` (CR 800.4a / 800.4c). -/
def endControlChangingEffect (g : Game) (o : GameObject) : Game :=
  match g.findObject? o.id with
  | none => g
  | some o =>
    if !o.controlChanged then
      g.setObject { o with status := { o.status with controlUntilEot := false } }
    else
      let dest := o.defaultController.getD o.owner
      if (g.player dest).lost then
        let name := o.name
        let (g, _) := g.move o.id .exile none
        g.logMsg s!"{name} is exiled (CR 800.4c)"
      else
        let g := g.setObject { o with
          controller := some dest
          controlChanged := false
          status := { o.status with controlUntilEot := false } }
        g.logMsg s!"{o.name} reverts to {(g.player dest).name}'s control"

/-- Gain control of `o` until end of turn (CR 611.2a). -/
def giveControlUntilEot (g : Game) (o : GameObject) (p : PlayerId) : Game :=
  if (g.player p).lost then
    g.logMsg s!"{o.name} does not change control (CR 800.4b)"
  else
    let g := g.changeControl o p
    match g.findObject? o.id with
    | none => g
    | some o =>
      g.setObject { o with status := { o.status with controlUntilEot := true } }

/-- Remove `o` from the game. Battlefield permanents use `move` so
until-leaves one-shots return (CR 610.3 / 800.4a). Ante stays (CR 800.4n). -/
def objectLeavesTheGame (g : Game) (o : GameObject) (leavingPlayer : PlayerId) : Game :=
  if o.zone == .ante then g
  else if o.zone == .battlefield then
    let (g, newId) := g.move o.id .exile none
    let g := { g with
      waitingTriggers :=
        g.waitingTriggers.filter (fun wt => wt.controller != leavingPlayer) }
    g.ceaseToExist newId
  else
    g.removeFromZoneList o.id o.zone |>.ceaseToExist o.id

/-- After `p` leaves, pending costs they would pay are not paid (CR 800.4f)
and other pending choices they would make are skipped or passed on
(CR 800.4g / 800.4h / 800.4j). Does not grant priority. -/
def redirectPendingAfterLeave (g : Game) (p : PlayerId) : Game :=
  match g.pending with
  | .none => g
  | .declareAttackers =>
    if g.activePlayer == p then
      { g with pending := .none }
        |>.logMsg "no active player declares attackers (CR 800.4j)"
    else g
  | .declareBlockers =>
    if g.currentBlockersPlayer == p then
      let rest := g.blockersQueue.extract 1 g.blockersQueue.size
      if rest.isEmpty then
        { g with pending := .none, blockersQueue := #[] }
          |>.logMsg "no active player remains to declare blockers (CR 800.4j)"
      else
        { g with pending := .declareBlockers, blockersQueue := rest }
    else g
  | .payOrLetCounter q _ spellId | .payWard q spellId _ =>
    if q == p then
      let g := { g with pending := .none }
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      match g.findObject? spellId with
      | none => g
      | some o =>
        let g := g.removeFromZoneList o.id .stack |>.ceaseToExist o.id
        g.logMsg s!"{o.name} is countered"
    else g
  | .mayPayGeneric q _ =>
    if q == p then
      { g with pending := .none }
        |>.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
    else g
  | .chooseSacrificeCreature q chosen remaining =>
    if q != p then g
    else
      match remaining.find? (fun r => g.stillInGame r) with
      | none => { g with pending := .none }
      | some np =>
        { g with
          pending := .chooseSacrificeCreature np chosen
            (remaining.filter (fun r => r != np && g.stillInGame r)) }
  | .chooseDiscardCard q remaining =>
    if q != p then g
    else
      match remaining.find? (fun r => g.stillInGame r) with
      | none => { g with pending := .none, pendingDiscardsLeft := 0 }
      | some np =>
        { g with
          pendingDiscardsLeft := 0
          pending := .chooseDiscardCard np
            (remaining.filter (fun r => r != np && g.stillInGame r)) }
  | .chooseTriggerToStack q =>
    if q == p then { g with pending := .none } else g
  | .chooseLegend q _ _ =>
    if q == p then { g with pending := .none } else g
  | .assignCombatDamage q forAttackers =>
    if q == p then
      { g with pending := .assignCombatDamage (g.nextLiving p) forAttackers }
        |>.logMsg
          s!"{(g.player (g.nextLiving p)).name} assigns combat damage (CR 800.4h)"
    else g
  | .activateManaAbilities q | .chooseMode q | .chooseX q | .chooseTargets q
  | .chooseAdditionalCost q | .chooseKicker q | .chooseGift q
  | .chooseTeamwork q | .chooseTeamworkCreatures q _ =>
    if q == p then { g with pending := .none, proposedSpell := none } else g
  | .sacrificePermanent q _ | .sacrificeCreature q | .scry q _
  | .mayDiscardDraw q _ | .mayAttachEquipment q _ | .tapHumans q
  | .recruitDiscard q | .chooseRingBearer q | .chooseLibraryPlacement q _
  | .maySacrificeAnotherBolg q _ | .mayCastFromLooked q _ _ | .putOnBottom q _
  | .mayPutLandFromHand q | .chooseFoodOrTreasure q | .chooseTapOrUntap q _
  | .maySacArtifactOrDiscard q | .mayPutArtifactFromHand q _
  | .declareMulligan q =>
    if q == p then { g with pending := .none } else g
  | .resolveRandom _ => g

/-- `p` loses and leaves the game (CR 800.4 / 800.4a). Owned objects leave
immediately (until-leaves one-shots return); control-changing effects that
gave them control end; their non-card stack objects cease; remaining objects
they control are exiled. This is not a state-based action. -/
def playerLeavesGame (g : Game) (p : PlayerId) : Game :=
  if (g.player p).leftTheGame then g
  else
    let g := g.setPlayer { (g.player p) with lost := true, leftTheGame := true }
    let g := g.logMsg s!"{(g.player p).name} leaves the game"
    let owned := g.objects.filter (fun o => o.owner == p && o.zone != .ante)
    let g :=
      owned.foldl (fun acc o =>
        match acc.findObject? o.id with
        | none => acc
        | some o => acc.objectLeavesTheGame o p) g
    let g :=
      (g.battlefield.filter (fun o => o.controlChanged && o.controlledBy p)).foldl
        (fun acc o =>
          match acc.findObject? o.id with
          | none => acc
          | some o => acc.endControlChangingEffect o) g
    let g :=
      g.objects.foldl (fun acc o =>
        if o.zone == .stack && o.controlledBy p && !representedByCard o then
          acc.removeFromZoneList o.id .stack |>.ceaseToExist o.id
        else acc) g
    let still := g.objects.filter (fun o => o.controlledBy p)
    let g :=
      still.foldl (fun acc o =>
        match acc.findObject? o.id with
        | none => acc
        | some o =>
          let name := o.name
          let (acc, _) := acc.move o.id .exile none
          acc.logMsg s!"{name} is exiled (CR 800.4a)") g
    let g := { g with
      waitingTriggers := g.waitingTriggers.filter (fun wt => wt.controller != p) }
    let g :=
      match g.proposedSpell with
      | some prop =>
        if prop.caster == p then { g with proposedSpell := none } else g
      | none => g
    let g :=
      if g.priority == p then { g with priority := g.nextLiving p } else g
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
    for pl in g.players do
      if !pl.manaPool.isEmpty then
        g := g.logMsg s!"{pl.name} empties mana pool ({pl.manaPool})"
        g := g.setPlayer { pl with manaPool := ManaPool.empty }
    return g

end Game
end Mtg.Engine
