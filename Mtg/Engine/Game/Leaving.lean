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

/-- True when an opponent of `p` controls a permanent or command-zone object
whose static ability states opponents can't win the game (CR 104.2b). -/
def playerCantWin (g : Game) (p : PlayerId) : Bool :=
  (g.livingOpponents p).any (fun opp =>
    (g.permanentsOf opp.id).any (fun o =>
      (g.baseCard o).opponentsCantWin && g.retainsPrintedAbilities o) ||
    (g.objects.filter (fun o =>
      o.zone == .command && g.controlledBy o opp.id)).any (fun o =>
        (g.baseCard o).opponentsCantWin && g.retainsPrintedAbilities o))

/-- If 0 living players remain or a single surviving player/team has no living
opponents left, set the game result (CR 104.2a / 810.8a,b). -/
def decideGameIfFinished (g : Game) : Option Game :=
  if g.over then none
  else
    let living := g.livingPlayers
    if living.size == 0 then
      some (g.record (GameEvent.gameEnded g.turnNumber .draw) |>.logMsg "The game is a draw")
    else if (living.size == 1 || living.size < g.players.size) &&
        living.all (fun pl => (g.livingOpponents pl.id).isEmpty) then
      let w := living[0]!
      if living.any (fun pl => g.playerCantWin pl.id) then none
      else
        let msg := g.formatWinMessage (living.map (·.id))
        some (g.record (GameEvent.gameEnded g.turnNumber (.won w.id)) |>.logMsg msg)
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
  if !g.stillInGame p then
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
opens and emitting `logLine` only once the permanent has arrived in `.exile`
(CR 614.6). -/
def runEndControlExileLoop (g : Game) (remaining : Array (ObjectId × String))
    (cause : Option EventCause := none)
    (pendingLog : Option (ObjectId × String) := none) : Game :=
  if remaining.isEmpty && pendingLog.isNone then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.endControlExileLoop remaining cause pendingLog)
  else Id.run do
    let mut g := g
    if let some (fromId, logLine) := pendingLog then
      if (g.followMovedToZone? fromId (· == .exile)).isSome then
        g := g.logMsg logLine
    for i in [0:remaining.size] do
      let (oid, logLine) := remaining[i]!
      if let some cur := g.findObject? oid then
        if cur.isBattlefieldObject || cur.zone == .stack then
          let (g', _) := g.move oid .exile none (cause := cause)
          g := g'
          if let .chooseReplacement .. := g.pending then
            let rem := remaining.extract (i + 1) remaining.size
            g := g.chainPendingReplacement (.endControlExileLoop rem cause (some (oid, logLine)))
            return g
          if (g.followMovedToZone? oid (· == .exile)).isSome then
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
              if !acc.stillInGame dest then
                (acc, exiles.push (oid, s!"{acc.name cur} is exiled (CR 800.4c)"))
              else if curCtrl != prevCtrl || prevCtrl != some dest then
                (acc.logMsg s!"{acc.name cur} reverts to {(acc.player dest).name}'s control", exiles)
              else (acc, exiles)) (g, #[])
    g.runEndControlExileLoop exileQueue (cause := some (.gameRule .playerLeftGame))

/-- Record removing up to `n` counters of `kind` from `id` via
`PermanentEvent.counters` (CR 122.1). Clamps to the current counter count,
does nothing when `0` counters are removed, and expires `.whileSourceHasCounter`
effects immediately when `kind` reaches `0` (running `endControlEffectById` on
matching Layer 2 control effects before `expireMatching` so CR 800.4c applies). -/
def recordRemoveCounters (g : Game) (id : ObjectId) (kind : CounterKind) (n : Nat := 1)
    (byPlayer : Option PlayerId := none) (cause : Option EventCause := none)
    (noActor : Bool := false) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let actual := min n (o.status.counterCount kind)
    if actual == 0 then g
    else
      let actor :=
        if noActor then none
        else byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
      let finalCause := g.resolveOptionalCause cause (fallbackCtrl := actor)
      let g := g.record (GameEvent.counters g.turnNumber actor (g.snapshot o) kind actual (removed := true) (cause := finalCause))
      let g := if kind == .time then g.syncImpendingNotACreature id (cause := some finalCause) else g
      if (g.findObject? id).all (fun cur => cur.status.counterCount kind == 0) then
        let expCause := some (EventCause.gameRule .continuousEffect)
        let g := g.restoreCopiesWhere (fun _ _ _ d => d == .whileSourceHasCounter id kind) (cause := expCause)
        let ctrlEids := g.activeEffects.filterMap fun (eid, e) =>
          match e with
          | .layered _ (.control _) (.whileSourceHasCounter src k) =>
            if src == id && k == kind then some eid else none
          | _ => none
        let g := ctrlEids.foldl (fun acc eid => acc.endControlEffectById eid (cause := expCause)) g
        g.expireMatching (fun s =>
          match s.duration with
          | .whileSourceHasCounter src k => src == id && k == kind
          | _ => false) (cause := expCause)
      else g

/-- Remove all counters currently on `id`, emitting one `PermanentEvent.counters`
removal per non-zero counter kind in a single batch (CR 122.1). -/
def removeAllCountersFrom (g : Game) (id : ObjectId)
    (byPlayer : Option PlayerId := none) (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let bag := o.status.toCounterBag
    if bag.isEmpty then g
    else
      g.withBatchCore cause (fun g =>
        bag.foldl (fun acc (kind, cnt) =>
          acc.recordRemoveCounters id kind cnt (byPlayer := byPlayer) (cause := cause)) g)

/-- Put `n` +1/+1 counters on `o` (CR 122.1). When `entersWith` is true, the
counters have already been placed in `o`'s arrival `ZoneEvent.moved` via
`extraEntersWith` or `ZoneEvent.created` (CR 614.1c); `.youPutPlusOne`
triggers are evaluated from the recorded event batch in `matchTriggers`. -/
def addPlusOnePlusOneTo (g : Game) (o : GameObject) (n : Nat := 1)
    (entersWith := false) (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.addPlusOnePlusOneTo o.id n entersWith byPlayer cause)
  else if n == 0 then g
  else
  let putter0 := byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
  let propCause := g.resolveOptionalCause cause (fallbackCtrl := putter0)
  let proposed :=
    GameEvent.counters g.turnNumber putter0 (g.snapshot o) .plusOnePlusOne n (cause := propCause)
  let (n', applied, cause', choice?, _) :=
    if proposed.watches .wouldPutCounter then
      g.replaceCountersPutChoice o .plusOnePlusOne n (putter := byPlayer)
        (entersWith := entersWith) (cause := cause)
    else
      (g.countersYouPut o n (putter := byPlayer) (entersWith := entersWith), #[], cause, none, #[])
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addPlusOnePlusOneTo o.id n entersWith byPlayer cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    if n' == 0 then g
    else
      let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := putter0)
      let happened := GameEvent.counters g.turnNumber putter0 (g.snapshot (g.object! o.id)) .plusOnePlusOne n'
        (cause := finalCause)
      let g := if !entersWith then g.record happened else g
      let phrase :=
        if entersWith then s!"{g.name o} enters with {plusOnePlusOneCountersPhrase n'}"
        else s!"{g.name o} gets {plusOnePlusOneCountersPhrase n'}"
      g.logMsg phrase

def withSourceOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game)
    (missing := "The ability's source is no longer in play")
    (leftMsg : Option String := none) : Game :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then f g o
    else g.logMsg (leftMsg.getD s!"{g.name o} is no longer on the battlefield")
  | none =>
    g.logMsg missing

/-- Mister Hyde's chosen mode. Mode 0 puts a +1/+1 counter on the source.
Mode 1 removes a counter from the chosen creature, then draws. -/
def applyHydeMode (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (mode : Nat) (targets : Array Target) : Game :=
  if mode == 0 then
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.addPlusOnePlusOneTo o 1) "The source is no longer in play"
  else
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.isCreature o && g.controlledBy o controller && o.status.hasCounters then
          let kind? : Option CounterKind :=
            if o.status.plusOnePlusOne > 0 then some .plusOnePlusOne
            else if o.status.indestructibleCounters > 0 then some .indestructible
            else o.status.toCounterBag[0]?.map (·.1)
          match kind? with
          | some kind =>
            let nm := g.name o
            let before := o.status.counterCount kind
            let g := g.recordRemoveCounters o.id kind 1 (byPlayer := some controller)
              |>.logMsg s!"A counter is removed from {nm}"
            let removed : Bool :=
              match g.findObject? o.id with
              | some cur => decide (cur.status.counterCount kind < before)
              | none => true
            if removed then g.draw controller 1 else g
          | none => g
        else
          g.logMsg "You must remove a counter from a creature you control if you can"
      | none =>
        g.logMsg "You must remove a counter from a creature you control if you can"
    | _ =>
      if (g.permanentsOf controller).any (fun o =>
          g.isCreature o && o.status.hasCounters) then
        g.logMsg "You must remove a counter from a creature you control if you can"
      else g

/-- Creatures `p` may sacrifice to a “sacrifices a creature of their choice” effect. -/
def sacrificeCreatureChoices (g : Game) (p : PlayerId) : Array GameObject :=
  g.creaturesControlledBy p

/-- Whether `sac` is a legal creature for `p` to sacrifice to an edict. -/
def canSacrificeCreature (g : Game) (p : PlayerId) (sac : GameObject) : Bool :=
  (g.sacrificeCreatureChoices p).any (·.id == sac.id)

/-- Creatures `p` controls that are tied for least power. -/
def leastPowerCreatures (g : Game) (p : PlayerId) : Array GameObject :=
  let cs := g.sacrificeCreatureChoices p
  match cs[0]? with
  | none => #[]
  | some first =>
    let minP := cs.foldl (fun acc o => min acc (g.power o)) (g.power first)
    cs.filter (fun o => g.power o == minP)

/-- Sacrifice a least-power creature `p` controls. If several are tied and
`chosen` is none, the player still chooses (logged; no sacrifice yet). -/
def sacrificeLeastPowerCreature (g : Game) (p : PlayerId)
    (chosen : Option ObjectId := none) : Game :=
  if !g.stillInGame p then g
  else
    let tied := g.leastPowerCreatures p
    if tied.isEmpty then
      g.logMsg s!"{(g.player p).name} controls no creatures to sacrifice"
    else
      let pick :=
        match chosen with
        | some chosenId => tied.find? (fun (o : GameObject) => o.id == chosenId)
        | none => if tied.size == 1 then some tied[0]! else none
      match pick with
      | some o =>
        g.sacrificeToGraveyard o
          s!"{(g.player p).name} sacrifices {g.name o} (least power)"
      | none =>
        let ids : Array ObjectId := tied.map (fun (o : GameObject) => o.id)
        g.beginFraChoice p (.sacrificeLeastPower ids)
          s!"{(g.player p).name} chooses one of the creatures tied for least power to sacrifice"

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
  if !g.stillInGame p then
    g.logMsg s!"{g.name o} does not change control (CR 800.4b)"
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
            if !g.stillInGame destP then some (tid, s!"{g.name cur} is exiled (CR 800.4c)") else none
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

private def findPausedCloseBatchFor? (target : BatchId) : PendingReplacement → Option Nat
  | .closeBatch b s => if b == target then some s else none
  | .seq a b => findPausedCloseBatchFor? target a <|> findPausedCloseBatchFor? target b
  | _ => none

private def hasCloseBatchFor (g : Game) (target : BatchId) : Bool :=
  (g.pendingReplacement.bind (findPausedCloseBatchFor? target)).isSome ||
    (g.outerPendingReplacements.findSomeRev? (findPausedCloseBatchFor? target)).isSome

private def findEarliestBatchIdx (g : Game) (target : BatchId) : Nat := Id.run do
  for i in [0:g.events.size] do
    match g.events[i]! with
    | .engine _ (.pauseBatch bid ..) _ =>
      if bid == target then return i
    | e =>
      if e.batch == some target then return i
  return g.events.size

private def filterLivingAttackTargets (g : Game) (controller : PlayerId)
    (opts : Array AttackTarget) : Array AttackTarget :=
  opts.filter fun
    | .player pid => g.isLivingOpponentOf controller pid
    | .planeswalker oid | .battle oid =>
      (g.findObject? oid).any (fun o =>
        o.isOnBattlefield && (g.livingOpponents controller).any (fun pl => g.controlledBy o pl.id))

private def sanitizeEnteringAttackItem (g : Game) : EnteringAttackItem → Option EnteringAttackItem
  | .token c kind tapped opts tokenName =>
    if !g.stillInGame c then none
    else some (.token c kind tapped (filterLivingAttackTargets g c opts) tokenName)
  | .card cid c effCtrl tapped retArt extra mods logKind opts =>
    if !g.stillInGame c || (g.findObject? cid).isNone then none
    else some (.card cid c effCtrl tapped retArt extra mods logKind (filterLivingAttackTargets g c opts))

/-- Run `f` with the outer `g.pendingReplacement` stashed, re-chaining it after
whatever `f` leaves (including a fresh `Pending.chooseReplacement` continuation
from a graveyard / stack-leave replacement), so the outer continuation is not
clobbered when a player leaves the game (CR 616.1 / 800.4a,f–h). -/
private def withOuterContStashed (g : Game) (f : Game → Game) : Game :=
  let outerCont? := g.pendingReplacement
  let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
  let g := f g
  match outerCont? with
  | some outer => g.chainPendingReplacement outer
  | none => g

private partial def advanceSacDamagersAfterLeave (g : Game) (controller : PlayerId)
    (opponents : Array PlayerId) (chosen : Array (PlayerId × ObjectId)) : Game × Pending :=
  let living := opponents.filter g.stillInGame
  match living[0]? with
  | none =>
    let g := if g.pending != .none then g.change (.pending .none) else g
    if chosen.isEmpty then (g, .none)
    else
      let preBf := g.battlefield
      let g :=
        g.withOuterContStashed fun g =>
          g.withBatch none fun g =>
            g.sacrificePermanentsLoop chosen (preBattlefield := some preBf)
      (g, g.pending)
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
      (g.logMsg s!"{(g.player r).name} chooses a creature that dealt combat damage to sacrifice",
       .fraChoice r (.sacrificeDamager ids rest controller chosen))

/-- True when departing player `p` is the proposer of `g.proposedSpell` or owns
the card being proposed as a spell / turned face up (CR 601.2 / 800.4a). -/
def isProposalAbortedByLeave (g : Game) (p : PlayerId) : Bool :=
  g.proposedSpell.any fun prop =>
    prop.caster == p ||
      (g.findObject? prop.spellId).any (fun o =>
        o.owner == p && (prop.kind != .activatedAbility || g.controlledBy o p)) ||
      (prop.kind != .activatedAbility && prop.original.owner == p) ||
      prop.sourceId.any (fun sid =>
        (g.findObject? sid).any (fun src =>
          src.owner == p || (src.isOnBattlefield && g.controlledBy src p)))

private def isProposalPromptFor (caster : PlayerId) : Pending → Bool
  | .chooseMode q | .chooseTargets q | .activateManaAbilities q | .chooseX q
  | .chooseAdditionalCost q | .chooseKicker q | .chooseGift q
  | .chooseTeamwork q | .chooseTeamworkCreatures q _
  | .sacrificePermanent q _ | .discardForAdditionalCost q
  | .fraChoice q (.costPicks ..) | .fraChoice q (.crew ..)
  | .fraChoice q (.zemoBoastExile ..) => q == caster
  | _ => false

private def isProposalBoundaryStep (caster : PlayerId) : PendingReplacement → Bool
  | .endProposalAction
  | .finishProposedSpellCosts ..
  | .completeActivation ..
  | .finishBecomeCast ..
  | .finishBecomeActivated ..
  | .finishPostLoyaltyActivated ..
  | .finishTurnFaceUp ..
  | .payCostPickItems ..
  | .finishActivationExtraCosts ..
  | .finishActivateManaAbilityPicks ..
  | .finishActivateManaAbilityPostSac ..
  | .finishManaAbilityMountainTrigger .. => true
  | .finishPostStep (.resumeProposalCostAfterLeave q _)
  | .finishPostStep (.resumeChooseModeAfterLeave q)
  | .finishPostStep (.resumeChooseTargetsAfterLeave q) => q == caster
  | .restorePending rp .. => isProposalPromptFor caster rp
  | _ => false

private def hasProposalBoundaryStep (caster : PlayerId) : PendingReplacement → Bool
  | .seq a b => hasProposalBoundaryStep caster a || hasProposalBoundaryStep caster b
  | step => isProposalBoundaryStep caster step

private def stripAbortedProposalCont (caster : PlayerId) :
    PendingReplacement → Option PendingReplacement
  | .seq a b =>
    if hasProposalBoundaryStep caster b then
      stripAbortedProposalCont caster b
    else if hasProposalBoundaryStep caster a then
      match stripAbortedProposalCont caster a with
      | some a' => some (.seq a' b)
      | none => some b
    else
      some (.seq a b)
  | step =>
    if isProposalBoundaryStep caster step then none else some step

private def revertGoneStagedTargets (g : Game) (e? : Option StackEntry)
    (staged : Array Target) : Array Target :=
  match e? with
  | none => staged
  | some e =>
    let gone : Target → Bool
      | .player pid => !g.stillInGame pid
      | .permanent oid => !(g.findObject? oid).any (·.isOnBattlefield)
      | .card oid => (g.findObject? oid).isNone
    staged.mapIdx fun i st =>
      match e.targets[i]? with
      | some orig => if st != orig && gone st then orig else st
      | none => st

@[extern "mtg_game_amass"]
private opaque amass (g : Game) (controller : PlayerId) (subtype : CardSubtype) (n : Nat)
    (attach : Option ObjectId := none) (cause : Option EventCause := none) : Game := g

@[extern "mtg_game_finish_amass_on"]
private opaque finishAmassOn (g : Game) (controller : PlayerId) (armyId : ObjectId)
    (subtype : CardSubtype) (n : Nat) (attach : Option ObjectId := none)
    (stage : AmassStage := .putCounters) (cause : Option EventCause := none) : Game := g

@[extern "mtg_game_legal_targets_for_kind"]
private opaque legalTargetsForKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId := none) : Array Target := #[]

@[extern "mtg_game_finish_choose_cards"]
private opaque finishChooseCards (g : Game) (p : PlayerId) (chosen : Array ObjectId)
    (purpose : CardChoice) (cause : Option EventCause := none) : Game := g

@[extern "mtg_game_sequence_all_targets_illegal"]
private opaque sequenceAllTargetsIllegal (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none) : Bool := false

@[extern "mtg_game_grant_widow_cast"]
private opaque grantWidowCast (g : Game) (controller : PlayerId) (exiled : Option ObjectId)
    (cause : Option EventCause := none) : Game := g

@[extern "mtg_game_resume_trigger_sequence"]
private opaque resumeTriggerSequence (g : Game) : Game := g

@[extern "mtg_game_auto_resolve_choose_object"]
private opaque autoResolveSingleChooseObject (g : Game) (id : ObjectId) : Game := g

@[extern "mtg_game_run_post_cast_cleanup"]
private opaque runPostCastCleanup (g : Game) : Game := g

/-- After `p` leaves, pending costs they would pay are not paid (CR 800.4f)
and other pending choices they would make are skipped or passed on
(CR 800.4g / 800.4h / 800.4j). Returns `(g, nextPending)` without journaling
`.pending` for the redirected prompt so `playerLeavesGameCore` can restore it
after the departure batch, control-loss exiles, and linked-exile returns.
Does not grant priority. -/
def redirectPendingAfterLeave (g : Game) (p : PlayerId)
    (abortedProposal : Bool := false) (pending : Pending := g.pending) : Game × Pending :=
  let abortedProp := abortedProposal || g.isProposalAbortedByLeave p
  let rewindAbortedProp :=
    abortedProp && g.proposalCheckpoint.isSome &&
      g.proposedSpell.any (fun prop => prop.caster != p && g.stillInGame prop.caster)
  let clearProp : Array EngineChange :=
    if abortedProp && !rewindAbortedProp then #[.proposedSpell none, .clearProposalCheckpoint]
    else #[]
  let clearPending (g : Game) : Game :=
    if g.pending != .none then g.change (.pending .none) else g
  let clearPendingAnd (g : Game) (cs : Array EngineChange) : Game :=
    let all := (if g.pending != .none then #[EngineChange.pending .none] else #[]) ++ cs
    if all.isEmpty then g else g.changes all
  match pending with
  | .none => (g, .none)
  | .declareAttackers =>
    if g.activePlayer == p then
      ((clearPending g).logMsg "no active player declares attackers (CR 800.4j)", .none)
    else (g, pending)
  | .declareBlockers =>
    let livingMate? :=
      g.livingPlayers.find? (fun m => g.areTeammates p m.id && g.defendingPlayers.contains m.id)
        |>.map (·.id)
    let filtered :=
      match livingMate? with
      | some mid =>
        if g.blockersQueue.contains mid then g.blockersQueue.filter (· != p)
        else g.blockersQueue.map (fun q => if q == p then mid else q)
      | none => g.blockersQueue.filter (· != p)
    if g.currentBlockersPlayer == p then
      if filtered.isEmpty then
        let g := clearPendingAnd g #[.blockersQueue #[]]
        let g := g.withBatch (some (.turnBased .declareBlockers)) fun g =>
          g.battlefield.foldl (fun acc o =>
            if o.status.attacking && !o.status.blocked then
              acc.record (GameEvent.remainedUnblocked acc.turnNumber (acc.snapshot o)
                (cause := some (.turnBased .declareBlockers)))
            else acc) g
        (g.logMsg "no active player remains to declare blockers (CR 800.4j)", .none)
      else
        (g.change (.blockersQueue filtered), .declareBlockers)
    else if filtered != g.blockersQueue then
      (g.change (.blockersQueue filtered), pending)
    else (g, pending)
  | .payOrLetCounter q _ spellId? =>
    if q == p then
      let g := clearPending g
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      if g.unlessPaysInstead.isSome then
        (g.change (.unlessPaysDue true), .none)
      else
        let caster := g.unlessPaysController
        let g := g.clearUnlessPays
        match spellId?.bind g.findObject? |>.filter (·.zone == .stack) with
        | none => (g, .none)
        | some o =>
          if g.controlledBy o p then (g, .none)
          else
            let g :=
              g.withOuterContStashed fun g =>
                g.counterStackSpell o.id (controller := some caster)
            (g, g.pending)
    else
      match spellId? with
      | some sid =>
        if !(g.findObject? sid).any (·.zone == .stack) then
          ((clearPending g).clearUnlessPays, .none)
        else (g, pending)
      | none =>
        match g.unlessPaysInstead with
        | some eff =>
          if !g.stillInGame g.unlessPaysController ||
              (!g.unlessPaysTargets.isEmpty &&
               g.sequenceAllTargetsIllegal g.unlessPaysController eff g.unlessPaysTargets g.unlessPaysSource) then
            ((clearPending g).clearUnlessPays, .none)
          else (g, pending)
        | none => (g, pending)
  | .payWard q spellId cost =>
    if q == p then
      let g := clearPending g
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      match (g.findObject? spellId).filter (·.zone == .stack) with
      | none => (g, .none)
      | some o =>
        if g.controlledBy o p then (g, .none)
        else
          let wardCtrl := ((g.resolvingAbility.bind g.findObject?).bind (·.controller)).getD (g.opponent p)
          let g :=
            g.withOuterContStashed fun g =>
              g.counterStackSpell spellId (controller := some wardCtrl)
          (g, g.pending)
    else if !(g.findObject? spellId).any (·.zone == .stack) then
      (clearPending g, .none)
    else
      match cost with
      | .sacrificePermanents left paid chosen =>
        if paid > 0 && ((g.permanentsOf q).filter (fun o => !chosen.contains o.id)).size < left then
          let g := (clearPending g).logMsg s!"{(g.player q).name} cannot finish paying ward"
          let wardCtrl := ((g.resolvingAbility.bind g.findObject?).bind (·.controller)).getD (g.opponent q)
          let g :=
            g.withOuterContStashed fun g =>
              g.counterStackSpell spellId (controller := some wardCtrl)
          (g, g.pending)
        else (g, pending)
      | _ => (g, pending)
  | .mayPayGeneric q _ =>
    if q == p then
      let g := clearPending g
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else g
      (g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)", .none)
    else (g, pending)
  | .chooseSacrificeCreature q chosen remaining =>
    let livingRem := remaining.filter g.stillInGame
    if q != p && !(g.creaturesControlledBy q).isEmpty then
      if livingRem != remaining then
        (g, .chooseSacrificeCreature q chosen livingRem)
      else (g, pending)
    else
      let g :=
        if q != p then
          g.logMsg s!"{(g.player q).name} has no creature to sacrifice"
        else g
      match g.nextActorWithCreatures livingRem with
      | none =>
        let skipped := livingRem.filter (fun r => (g.creaturesControlledBy r).isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no creature to sacrifice")
        let g := clearPending g
        let g := g.withOuterContStashed fun g => g.finishChosenSacrifices chosen
        (g, g.pending)
      | some (np, rest) =>
        let prefixIdx := livingRem.findIdx? (· == np) |>.getD 0
        let skipped := (livingRem.extract 0 prefixIdx).filter (fun r => (g.creaturesControlledBy r).isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no creature to sacrifice")
        (g.logMsg s!"{(g.player np).name} must sacrifice a creature",
         .chooseSacrificeCreature np chosen (rest.filter g.stillInGame))
  | .chooseDiscardCard q remaining =>
    let livingRem := remaining.filter g.stillInGame
    if q != p then
      if livingRem != remaining then
        (g, .chooseDiscardCard q livingRem)
      else (g, pending)
    else
      match g.nextActorWithHandCard livingRem with
      | none =>
        let skipped := livingRem.filter (fun r => (g.player r).hand.isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no card to discard")
        let g :=
          if g.conniveSource.isSome then
            (g.change (.conniveSource none)).logMsg
              "No card is discarded; the conniving creature does not receive a +1/+1 counter"
          else g
        let g := clearPendingAnd g #[
          .thirstDiscardsLeft 0,
          .pendingDiscardsLeft 0, .discardCountPerPlayer 0]
        let g :=
          match g.discardBatch with
          | some (dbBid, dbStartIdx) =>
            let g := g.change (.discardBatch none)
            if g.currentBatch.map Prod.fst == some dbBid then
              g.finishOpenBatchAndLinkedExile dbBid dbStartIdx
            else g
          | none => g
        let g :=
          if g.plusOneAfterDiscards.isSome then
            g.withOuterContStashed fun g =>
              g.chainPendingReplacement (.finishPostStep .finishPlusOneAfterDiscards)
          else g
        (g, g.pending)
      | some (np, rest) =>
        let prefixIdx := livingRem.findIdx? (· == np) |>.getD 0
        let skipped := (livingRem.extract 0 prefixIdx).filter (fun r => (g.player r).hand.isEmpty)
        let g := g.logForPlayers skipped (fun r =>
          s!"{(g.player r).name} has no card to discard")
        let nextLeft := if g.discardCountPerPlayer > 1 then g.discardCountPerPlayer else 0
        ((g.change (.pendingDiscardsLeft nextLeft)).logMsg s!"{(g.player np).name} must discard a card",
         .chooseDiscardCard np (rest.filter g.stillInGame))
  | .chooseTriggerToStack q =>
    if q == p then (clearPending g, .none) else (g, pending)
  | .chooseLegend q name ids =>
    if q == p then (clearPending g, .none)
    else
      let liveIds := ids.filter fun id =>
        (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o q)
      if liveIds.size < 2 then (clearPending g, .none)
      else if liveIds != ids then (g, .chooseLegend q name liveIds)
      else (g, pending)
  | .chooseReplacement q _ =>
    if abortedProp then
      let caster? := g.proposedSpell.map (·.caster)
      let remCont? :=
        match caster?, g.pendingReplacement with
        | some c, some pr =>
          if hasProposalBoundaryStep c pr then stripAbortedProposalCont c pr else some pr
        | _, _ => none
      let closeInfo? :=
        (g.pendingReplacement.bind findPausedCloseBatch?).orElse (fun _ =>
          g.outerPendingReplacements.findSomeRev? findPausedCloseBatch?)
      let g := clearPendingAnd g (#[.pendingReplacement remCont?] ++ clearProp)
      let g :=
        match closeInfo? with
        | some (batchId, startIdx) =>
          if g.currentBatch.map Prod.fst == some batchId && !hasCloseBatchFor g batchId then
            g.finishOpenBatch batchId startIdx
          else g
        | none => if g.currentBatch.isSome then g.change .clearPausedBatch else g
      (g, .none)
    else if q == p then
      -- CR 800.4h: keep `pendingReplacement` and any enclosing open batch intact so
      -- draining continuations transfers the replacement choice to the next living
      -- player (via `selectNextReplacementStep`) or finishes the event cleanly.
      (clearPending g, .none)
    else (g, pending)
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
        (if forAttackers then g.isOnActiveTeam r && (g.controllerOf o).any g.isOnActiveTeam
         else g.controlledBy o r) &&
          !already.contains o.id &&
          (g.legalCombatDamageRecipients o forAttackers).size ≥ 2 && g.combatDamageAmount o > 0
    if q == p then
      if forAttackers then
        let nextAtk? := (g.teamMembers p).find? (fun r =>
          r != p && g.stillInGame r && playerStillNeeds r)
        match nextAtk? with
        | some nextAtk =>
          (g.logMsg s!"{(g.player nextAtk).name} assigns combat damage (CR 800.4h)",
           .assignCombatDamage nextAtk true)
        | none =>
          ((clearPendingAnd g #[.pendingBlockerAssignments #[]]).logMsg
            "no active player assigns combat damage (CR 800.4j)", .none)
      else
        let nextP? := g.apnapPlayers.find? (fun r =>
          r != p && !g.isOnActiveTeam r && g.stillInGame r && playerStillNeeds r)
        match nextP? with
        | some nextP =>
          (g.logMsg s!"{(g.player nextP).name} assigns combat damage (CR 800.4h)",
           .assignCombatDamage nextP false)
        | none =>
          (clearPending g, .none)
    else if playerStillNeeds q then (g, pending)
    else if forAttackers then
      (clearPending g, .none)
    else
      let nextP? := g.apnapPlayers.find? (fun r =>
        r != q && r != p && !g.isOnActiveTeam r && g.stillInGame r && playerStillNeeds r)
      match nextP? with
      | some nextP =>
        (g.logMsg s!"{(g.player nextP).name} assigns combat damage (CR 800.4h)",
         .assignCombatDamage nextP false)
      | none =>
        (clearPending g, .none)
  | .chooseMode q =>
    if q == p || abortedProp then
      (clearPendingAnd g (#[.chooseModesRest none] ++ clearProp), .none)
    else
      let g :=
        g.withOuterContStashed fun g =>
          (clearPending g).chainPendingReplacement (.finishPostStep (.resumeChooseModeAfterLeave q))
      (g, .none)
  | .chooseTargets q =>
    if q == p || abortedProp then
      (clearPendingAnd g clearProp, .none)
    else
      let g :=
        g.withOuterContStashed fun g =>
          (clearPending g).chainPendingReplacement (.finishPostStep (.resumeChooseTargetsAfterLeave q))
      (g, .none)
  | .activateManaAbilities q | .chooseX q
  | .chooseAdditionalCost q | .chooseKicker q | .chooseGift q
  | .chooseTeamwork q =>
    if q == p || abortedProp then
      (clearPendingAnd g clearProp, .none)
    else (g, pending)
  | .chooseTeamworkCreatures q _
  | .sacrificePermanent q _ | .discardForAdditionalCost q =>
    if q == p || abortedProp then
      (clearPendingAnd g clearProp, .none)
    else
      let g :=
        g.withOuterContStashed fun g =>
          (clearPending g).chainPendingReplacement (.finishPostStep (.resumeProposalCostAfterLeave q pending))
      (g, .none)
  | .fraChoice q choice =>
    match choice with
    | .costPicks .. | .crew .. | .zemoBoastExile .. =>
      if q == p || abortedProp then
        (clearPendingAnd g (#[.chooseModesRest none] ++ clearProp), .none)
      else
        let g :=
          g.withOuterContStashed fun g =>
            (clearPending g).chainPendingReplacement (.finishPostStep (.resumeProposalCostAfterLeave q pending))
        (g, .none)
    | .mayCastUpToFromExile ids left =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none, .pendingMayCastFromExile none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let liveIds := ids.filter fun id =>
          (g.findObject? id).any (fun o => o.zone == .exile && !g.isLand o)
        if liveIds.isEmpty || left == 0 then
          let g := g.changes #[.chooseModesRest none, .pendingMayCastFromExile none]
          let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
          (g, .none)
        else if liveIds != ids then
          (g, .fraChoice q (.mayCastUpToFromExile liveIds left))
        else (g, pending)
    | .mayWheel n rest accepted =>
      let living := rest.filter g.stillInGame
      let acceptedLiving := accepted.filter g.stillInGame
      if q != p then
        if living != rest || acceptedLiving != accepted then
          (g, .fraChoice q (.mayWheel n living acceptedLiving))
        else (g, pending)
      else
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match living[0]? with
        | none =>
          let g := clearPending g
          let g :=
            if acceptedLiving.isEmpty then g
            else
              g.withOuterContStashed fun g =>
                g.chainPendingReplacement (.finishPostStep (.wheelOfferNext n #[] acceptedLiving))
          (g, .none)
        | some next =>
          (g.logMsg s!"{(g.player next).name} may discard their hand and draw {n} cards",
           .fraChoice next (.mayWheel n (living.extract 1 living.size) acceptedLiving))
    | .sacrificeCreatureEach controller rest chosen =>
      let living := rest.filter (fun r => g.stillInGame r && !(g.creaturesControlledBy r).isEmpty)
      if q != p && !(g.creaturesControlledBy q).isEmpty then
        if living != rest then (g, .fraChoice q (.sacrificeCreatureEach controller living chosen)) else (g, pending)
      else
        let g := g.changes (#[.chooseModesRest none] ++ (if q == p then clearProp else #[]))
        match living[0]? with
        | some next =>
          (g.logMsg s!"{(g.player next).name} sacrifices a creature",
           .fraChoice next (.sacrificeCreatureEach controller (living.extract 1 living.size) chosen))
        | none =>
          let youSacrificed :=
            g.stillInGame controller &&
              chosen.any (fun id => (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o controller))
          let pairs := chosen.filterMap (fun id =>
            match g.findObject? id with
            | some o => if o.isOnBattlefield then some ((g.controllerOf o).getD o.owner, id) else none
            | none => none)
          let preBf := g.battlefield
          let g := clearPending g
          let g :=
            g.withOuterContStashed fun g =>
              g.withBatch none fun g =>
                g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)
                  (createBeastFor := if youSacrificed then some controller else none)
          (g, g.pending)
    | .sacrificeNontokenEach rest chosen =>
      let hasNontoken (r : PlayerId) :=
        g.stillInGame r && (g.permanentsOf r).any (fun o => g.isCreature o && !o.printed.isToken)
      let living := rest.filter hasNontoken
      if q != p && hasNontoken q then
        if living != rest then (g, .fraChoice q (.sacrificeNontokenEach living chosen)) else (g, pending)
      else
        let g := g.changes (#[.chooseModesRest none] ++ (if q == p then clearProp else #[]))
        match living[0]? with
        | some next =>
          (g.logMsg s!"{(g.player next).name} sacrifices a nontoken creature",
           .fraChoice next (.sacrificeNontokenEach (living.extract 1 living.size) chosen))
        | none =>
          let pairs := chosen.filterMap (fun id =>
            match g.findObject? id with
            | some o => if o.isOnBattlefield then some ((g.controllerOf o).getD o.owner, id) else none
            | none => none)
          let preBf := g.battlefield
          let g := clearPending g
          let g :=
            g.withOuterContStashed fun g =>
              g.withBatch none fun g =>
                g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)
          (g, g.pending)
    | .sacrificeDamager ids rest controller chosen =>
      let living := rest.filter g.stillInGame
      let liveIds := ids.filter (fun id =>
        (g.findObject? id).any (fun o => o.isOnBattlefield && g.isCreature o && g.controlledBy o q))
      if q != p && liveIds.size > 1 then
        if liveIds == ids && living == rest then (g, pending)
        else (g, .fraChoice q (.sacrificeDamager liveIds living controller chosen))
      else
        let g := clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[]))
        let g :=
          if q != p && liveIds.isEmpty then
            g.logMsg s!"{(g.player q).name} controls no creature that dealt combat damage this turn"
          else g
        let chosen' :=
          if q != p && liveIds.size == 1 then chosen.push (q, liveIds[0]!)
          else chosen
        advanceSacDamagersAfterLeave g controller living chosen'
    | .discardTwo controller rest draws chosen =>
      let living := rest.filter g.stillInGame
      let chosenLiving := chosen.filter (fun (r, _) => g.stillInGame r)
      if q != p then
        if living != rest || chosenLiving != chosen then
          (g, .fraChoice q (.discardTwo controller living draws chosenLiving))
        else (g, pending)
      else
        let g := clearPendingAnd g (#[.chooseModesRest none] ++ clearProp)
        match living[0]? with
        | some next =>
          if (g.player next).hand.size > 2 then
            (g.logMsg s!"{(g.player next).name} discards two cards",
             .fraChoice next (.discardTwo controller (living.extract 1 living.size) draws chosenLiving))
          else
            let g :=
              g.withOuterContStashed fun g =>
                g.chainPendingReplacement (.finishPostStep (.continueDiscardTwo controller living draws chosenLiving))
            (g, .none)
        | none =>
          let g :=
            if (g.stillInGame controller && draws > 0) || !chosenLiving.isEmpty then
              g.withOuterContStashed fun g =>
                g.chainPendingReplacement (.finishPostStep (.continueDiscardTwo controller #[] draws chosenLiving))
            else g
          (g, .none)
    | .worldsPutCreatures eligible rest exiled chosen sourceId =>
      let living := rest.filter g.stillInGame
      if q != p then
        if living != rest then
          (g, .fraChoice q (.worldsPutCreatures eligible living exiled chosen sourceId))
        else (g, pending)
      else
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let rec offerNext : List PlayerId → Game × Pending
          | [] =>
            let g :=
              g.withOuterContStashed fun g =>
                (clearPending g).chainPendingReplacement
                  (.finishPostStep (.worldsWithinWorlds exiled chosen sourceId))
            (g, .none)
          | r :: more =>
            let elig := (g.player r).hand.filter (fun id => (g.findObject? id).any g.isCreature)
            if elig.isEmpty then offerNext more
            else
              (g.logMsg s!"{(g.player r).name} may put any number of creature cards from their hand onto the battlefield",
               .fraChoice r (.worldsPutCreatures elig more.toArray exiled chosen sourceId))
        offerNext living.toList
    | .chooseEnteringAttackTarget remaining chosen cause =>
      let stagedClean := g.stagedAttackTokenBatches.filter (fun b => g.stillInGame b.controller)
      let g :=
        if stagedClean != g.stagedAttackTokenBatches then
          g.change (.stagedAttackTokenBatches stagedClean)
        else g
      let chosenClean := chosen.filterMap fun (item, tgt?) =>
        match sanitizeEnteringAttackItem g item with
        | none => none
        | some item' =>
          let validTgt? := tgt?.filter (fun t => (filterLivingAttackTargets g item'.controller #[t]).size == 1)
          some (item', validTgt?.orElse (fun _ => item'.options[0]?))
      if q != p then
        let remClean := remaining.filterMap (sanitizeEnteringAttackItem g)
        let (restAfter, chosen') := advanceFixedEnteringAttackItems remClean chosenClean
        if restAfter.isEmpty then
          let g :=
            g.withOuterContStashed fun g =>
              (clearPending g).chainPendingReplacement
                (.commitEnteringAttackItems chosen' cause true)
          (g, .none)
        else if restAfter != remaining || chosen' != chosen then
          let nextCtrl := restAfter[0]!.controller
          (g, .fraChoice nextCtrl (.chooseEnteringAttackTarget restAfter chosen' cause))
        else (g, pending)
      else
        let remTail := (remaining.extract 1 remaining.size).filterMap (sanitizeEnteringAttackItem g)
        let (restAfter, chosen') := advanceFixedEnteringAttackItems remTail chosenClean
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match restAfter[0]? with
        | some nextItem =>
          let nextCtrl := nextItem.controller
          let nextNm := g.enteringAttackItemName nextItem
          (g.logMsg s!"{(g.player nextCtrl).name} chooses what {nextNm} enters attacking",
           .fraChoice nextCtrl (.chooseEnteringAttackTarget restAfter chosen' cause))
        | none =>
          let g :=
            g.withOuterContStashed fun g =>
              (clearPending g).chainPendingReplacement
                (.commitEnteringAttackItems chosen' cause true)
          (g, .none)
    | .discardFromRevealedHand victim _ | .exileFromRevealedHand victim _ =>
      if p == victim || q == p then
        (clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[])), .none)
      else (g, pending)
    | .extrapolatePick revealer ids =>
      if p == revealer then
        (clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[])), .none)
      else if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match (g.livingOpponents revealer)[0]? with
        | some opp =>
          (g.logMsg s!"{opp.name} chooses one of them (CR 800.4h)",
           .fraChoice opp.id (.extrapolatePick revealer ids))
        | none =>
          let g := clearPending g
          match ids.find? (fun id => (g.findObject? id).isSome) with
          | some id =>
            let name := g.name (g.object! id)
            let g :=
              g.withOuterContStashed fun g =>
                let (g, _) := g.move id (.hand revealer) none
                if let .chooseReplacement .. := g.pending then
                  g.chainPendingReplacement (.finishPostStep (.logPutsIntoHand revealer id name))
                else if (g.followMovedToZone? id (· == .hand revealer)).isSome then
                  g.logMsg s!"{(g.player revealer).name} puts {name} into their hand"
                else g
            (g, g.pending)
          | none => (g, .none)
      else (g, pending)
    | .riddlesChoosePile controller faceUp faceDown =>
      if p == controller then
        (clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[])), .none)
      else if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        match (g.livingOpponents controller)[0]? with
        | some opp =>
          (g.logMsg s!"{opp.name} chooses a pile (CR 800.4h)",
           .fraChoice opp.id (.riddlesChoosePile controller faceUp faceDown))
        | none =>
          let outerCont? := g.pendingReplacement
          let g :=
            clearPendingAnd g (if outerCont?.isSome then #[.pendingReplacement none] else #[])
          let g := g.withBatch none fun g =>
            faceUp.foldl (fun acc id =>
              if (acc.findObject? id).isSome then (acc.move id (.hand controller) none).1 else acc) g
          let g := g.withBatch none fun g =>
            g.moveCardsToGraveyardLoop faceDown
          let g :=
            match outerCont? with
            | some outer => g.chainPendingReplacement outer
            | none => g
          (g, g.pending)
      else (g, pending)
    | .palantirMayDraw controller sourceId =>
      if p == controller then
        (clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[])), .none)
      else if q == p then
        let g := clearPendingAnd g (#[.chooseModesRest none] ++ clearProp)
        let g :=
          if g.stillInGame controller then
            g.withOuterContStashed fun g =>
              g.chainPendingReplacement (.finishPostStep (.millSourceInfluenceCount controller sourceId))
          else g
        (g, .none)
      else (g, pending)
    | .tricksterLibrary caster id connive sourceId =>
      if p == caster then
        (clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[])), .none)
      else if q == p || !(g.findObject? id).any (fun o => o.isOnBattlefield && g.isCreature o) then
        let g := clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[]))
        let g :=
          if q != p && g.stillInGame caster then
            g.logMsg "The target is no longer legal"
          else g
        let g :=
          if g.stillInGame caster && connive.isSome then
            g.withOuterContStashed fun g =>
              g.chainPendingReplacement (.finishPostStep (.conniveTricksterTarget caster connive sourceId))
          else g
        (g, .none)
      else (g, pending)
    | .mayCastGrima cardId others victim =>
      if p == victim then
        (clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[])), .none)
      else if q == p then
        let g := clearPendingAnd g (#[.chooseModesRest none] ++ clearProp)
        if g.stillInGame victim then
          let live := (others.push cardId).filter (fun id => (g.findObject? id).any (·.zone == .exile))
          if live.isEmpty then (g, .none)
          else
            let log := s!"{(g.player victim).name} puts the exiled cards on the bottom of their library in a random order"
            let (g, cause) : Game × Option EventCause :=
              match g.lastMoveCauseOf? cardId with
              | some c => (g, some c)
              | none =>
                match g.currentResolvingContext? with
                | some (src, ctrl) =>
                  let (g, c) := g.allocDelayedCause ctrl src
                  (g, some c)
                | none => (g, none)
            if g.pending == .none && live.size > 1 then
              (g.logMsg log, .resolveRandom (.orderInto live (.library victim) cause))
            else
              let g :=
                g.withOuterContStashed fun g =>
                  g.requestOrderInto live (.library victim) log (cause := cause)
              (g, g.pending)
        else (g, .none)
      else (g, pending)
    | .mayBeginOnBattlefield cards =>
      let liveCards := cards.filter (fun id =>
        (g.findObject? id).any (fun o => g.stillInGame o.owner && o.zone == .hand o.owner))
      if liveCards.isEmpty then
        (clearPendingAnd g (#[.chooseModesRest none] ++ (if q == p then clearProp else #[])), .none)
      else
        let firstObj := g.object! liveCards[0]!
        let nextOwner := firstObj.owner
        if q == p then
          let g := (g.changes (#[.chooseModesRest none] ++ clearProp)).logMsg
            s!"{(g.player nextOwner).name} may begin the game with {g.name firstObj} on the battlefield"
          (g, .fraChoice nextOwner (.mayBeginOnBattlefield liveCards))
        else if liveCards != cards then
          (g, .fraChoice nextOwner (.mayBeginOnBattlefield liveCards))
        else (g, pending)
    | .triggerModes objId remaining chosen =>
      if q == p then
        (clearPendingAnd g (#[.chooseModesRest none] ++ clearProp), .none)
      else
        let g :=
          g.withOuterContStashed fun g =>
            (clearPending g).chainPendingReplacement
              (.finishPostStep (.resumeTriggerModesAfterLeave q objId remaining chosen))
        (g, .none)
    | .upToTriggerModes objId remaining chosen =>
      if q == p then
        (clearPendingAnd g (#[.chooseModesRest none] ++ clearProp), .none)
      else
        let g :=
          g.withOuterContStashed fun g =>
            (clearPending g).chainPendingReplacement
              (.finishPostStep (.resumeUpToTriggerModesAfterLeave q objId remaining chosen))
        (g, .none)
    | .hawkeyeModes left chosen objId? =>
      if q == p then
        (clearPendingAnd g (#[.chooseModesRest none] ++ clearProp), .none)
      else
        match objId? with
        | none =>
          (clearPendingAnd g #[.chooseModesRest none], .none)
        | some objId =>
          let g :=
            g.withOuterContStashed fun g =>
              (clearPending g).chainPendingReplacement
                (.finishPostStep (.resumeHawkeyeModesAfterLeave q objId left chosen))
          (g, .none)
    | .stackHydeMode objId | .stackTriggerUnusedMode objId _ _ _ =>
      if q == p then
        (clearPendingAnd g (#[.chooseModesRest none] ++ clearProp), .none)
      else if !(g.findObject? objId).any (·.zone == .stack) then
        (clearPendingAnd g #[.chooseModesRest none], .none)
      else (g, pending)
    | .blackGatePlayer oid players =>
      let players' := players.filter g.stillInGame
      if q == p then
        (clearPendingAnd g (#[.chooseModesRest none] ++ clearProp), .none)
      else if !(g.findObject? oid).any (fun o => o.isOnBattlefield && g.isCreature o) then
        let g := (clearPendingAnd g #[.chooseModesRest none]).logMsg "The target is no longer legal"
        (g, .none)
      else if players'.isEmpty then
        (clearPendingAnd g #[.chooseModesRest none], .none)
      else if players'.size == 1 then
        ((clearPendingAnd g #[.chooseModesRest none]).applyBlackGateUnblockable oid players'[0]!, .none)
      else if players' != players then
        (g, .fraChoice q (.blackGatePlayer oid players'))
      else (g, pending)
    | .mayCastCards ids withoutPaying exileInstead =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let ids' := ids.filter (fun id => (g.findObject? id).isSome)
        if ids'.isEmpty then
          let g := g.change (.chooseModesRest none)
          let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
          (g, .none)
        else if ids' != ids then
          (g, .fraChoice q (.mayCastCards ids' withoutPaying exileInstead))
        else (g, pending)
    | .mayChangeSpellTarget spellId index staged =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? spellId).any (fun o => o.zone == .stack) then
        let g := g.change (.chooseModesRest none)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let staged' := g.revertGoneStagedTargets (g.stackEntry? spellId) staged
        if staged' != staged then
          (g, .fraChoice q (.mayChangeSpellTarget spellId index staged'))
        else (g, pending)
    | .newTargetsForCopies copies | .newTargetsForCopySlot copies _ _ =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let live := copies.filter (fun cid => (g.findObject? cid).any (fun o => o.zone == .stack))
        if live.isEmpty then
          let g := g.change (.chooseModesRest none)
          let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
          (g, .none)
        else if live[0]? != copies[0]? then
          (g, .fraChoice q (.newTargetsForCopies live))
        else
          match choice with
          | .newTargetsForCopySlot _ s st =>
            let st' := g.revertGoneStagedTargets (copies[0]?.bind g.stackEntry?) st
            if live != copies || st' != st then
              (g, .fraChoice q (.newTargetsForCopySlot live s st'))
            else (g, pending)
          | _ =>
            if live != copies then
              (g, .fraChoice q (.newTargetsForCopies live))
            else (g, pending)
    | .sacrificeLeastPower ids =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let liveTied := (g.leastPowerCreatures q).map (·.id)
        if liveTied.size ≤ 1 then
          let g := g.withOuterContStashed fun g =>
            (clearPending g).sacrificeLeastPowerCreature q
          (g, g.pending)
        else if liveTied != ids then
          (g, .fraChoice q (.sacrificeLeastPower liveTied))
        else (g, pending)
    | .hydeRemoveCounter ids =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let live := (g.permanentsOf q).filter (fun o => g.isCreature o && o.status.hasCounters) |>.map (·.id)
        if live.size ≤ 1 then
          let targets := if live.isEmpty then #[] else #[Target.permanent live[0]!]
          let g := g.withOuterContStashed fun g =>
            (clearPending g).applyHydeMode q none 1 targets
          (g, g.pending)
        else if live != ids then
          (g, .fraChoice q (.hydeRemoveCounter live))
        else (g, pending)
    | .chooseCards ids max purpose =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none, .stashedCause none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        match purpose with
        | .amassArmy subtype n attach =>
          let liveIds := ids.filter (fun id =>
            (g.findObject? id).any (fun o =>
              o.isOnBattlefield && g.controlledBy o q && g.hasSubtype o .army))
          if liveIds.isEmpty then
            let g := g.withOuterContStashed fun g =>
              let cause := g.stashedCause
              let g := (clearPending g).change (.stashedCause none)
              g.amass q subtype n attach (cause := cause)
            (g, g.pending)
          else if liveIds.size == 1 then
            let g := g.withOuterContStashed fun g =>
              let cause := g.stashedCause
              let g := (clearPending g).change (.stashedCause none)
              g.finishAmassOn q liveIds[0]! subtype n attach (cause := cause)
            (g, g.pending)
          else if liveIds != ids then
            (g, .fraChoice q (.chooseCards liveIds max purpose))
          else (g, pending)
        | .keepDestroyRest =>
          let liveIds := (g.battlefield.filter (g.isCreature ·)).map (·.id)
          if liveIds.size ≤ max then
            let g := g.withOuterContStashed fun g =>
              (clearPending g).finishChooseCards q liveIds .keepDestroyRest
            (g, g.pending)
          else if liveIds != ids then
            (g, .fraChoice q (.chooseCards liveIds max .keepDestroyRest))
          else (g, pending)
        | _ =>
          let liveIds := ids.filter (fun id => (g.findObject? id).isSome)
          if liveIds.isEmpty then
            let g := (g.change (.chooseModesRest none)).change (.stashedCause none)
            let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
            (g, .none)
          else if liveIds != ids then
            (g, .fraChoice q (.chooseCards liveIds max purpose))
          else (g, pending)
    | .attachAnyEquipment hostId eligible =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let liveEligible := eligible.filter (fun id =>
          (g.findObject? id).any (fun o => o.isOnBattlefield && g.isEquipment o))
        if !(g.findObject? hostId).any (fun o =>
            o.isOnBattlefield && g.isCreature o && g.controlledBy o q) ||
            liveEligible.isEmpty then
          let g := g.change (.chooseModesRest none)
          let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
          (g, .none)
        else if liveEligible != eligible then
          (g, .fraChoice q (.attachAnyEquipment hostId liveEligible))
        else (g, pending)
    | .maySacrificeAnotherCreatureForPower sid =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !((g.creaturesControlledBy q).any (·.id != sid)) then
        let g := (g.change (.chooseModesRest none)).logMsg "No other creature to sacrifice"
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .maySacrificeAnotherForDrawTreasure sid =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !((g.permanentsOf q).any (fun o =>
          o.id != sid && (g.isCreature o || g.isArtifact o))) then
        let g := (g.change (.chooseModesRest none)).logMsg "Nothing to sacrifice"
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .maySacrificeThese n ids =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let liveIds := ids.filter (fun id =>
          (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o q))
        if liveIds.size < n then
          let g := (g.change (.chooseModesRest none)).logMsg "Nothing to sacrifice"
          let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
          (g, .none)
        else if liveIds != ids then
          (g, .fraChoice q (.maySacrificeThese n liveIds))
        else (g, pending)
    | .sheHulkMayDamage _ target sourceId =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.legalTargetsForKind q .playerOrCreature sourceId).contains target then
        let g := (g.change (.chooseModesRest none)).logMsg "The target is no longer legal"
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .widowMayCounter sourceId exiled =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(sourceId.bind g.findObject?).any (·.isOnBattlefield) then
        let g := g.withOuterContStashed fun g =>
          (clearPending g).grantWidowCast q exiled
        (g, g.pending)
      else if exiled.any (fun id => (g.findObject? id).isNone) then
        (g, .fraChoice q (.widowMayCounter sourceId none))
      else (g, pending)
    | .topOrBottomDamage id _ _ =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? id).any (·.isOnBattlefield) then
        let g := g.change (.chooseModesRest none)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .chooseKeyword objectId _ | .mayBecomeBasePT objectId _ _ =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? objectId).any (·.isOnBattlefield) then
        let g := g.change (.chooseModesRest none)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .mayMovePlusOne sourceId =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? sourceId).any (fun o =>
          o.isOnBattlefield && o.status.plusOnePlusOne > 0) then
        let g := g.change (.chooseModesRest none)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .mayMoveAllCounters fromId toId =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? fromId).any (·.isOnBattlefield) ||
          !(g.findObject? toId).any (·.isOnBattlefield) then
        let g := g.change (.chooseModesRest none)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .mayTapSourceThen _ sourceId =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? sourceId).any (fun o =>
          o.isOnBattlefield && !o.status.tapped) then
        let g := g.change (.chooseModesRest none)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .nickFuryMayTransform id rest =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? id).any (fun o =>
          o.isOnBattlefield && (g.baseCard o).otherFace.isSome && !g.cantTransform o) then
        let g := g.withOuterContStashed fun g =>
          let cause := g.lastMoveCauseOf? id
          let g := g.change (.chooseModesRest none)
          let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
          g.putRestOnBottomRandom q rest (cause := cause)
        (g, g.pending)
      else (g, pending)
    | .orderLibraryBottom ids =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none, .stashedCause none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let liveIds := ids.filter (fun id => (g.findObject? id).any (·.zone == .library q))
        if liveIds.size ≤ 1 then
          let g := g.withOuterContStashed fun g =>
            let cause := g.stashedCause.orElse (fun _ => liveIds[0]?.bind g.lastMoveCauseOf?)
            let g := g.changes #[.chooseModesRest none, .stashedCause none]
            let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
            if !liveIds.isEmpty then
              g.moveIdsInOrder liveIds (.library q) (cause := cause)
                (log := s!"{(g.player q).name} puts the rest on the bottom of their library")
            else g
          (g, g.pending)
        else if liveIds != ids then
          (g, .fraChoice q (.orderLibraryBottom liveIds))
        else (g, pending)
    | .searchLibrary eligible count dest after kind
    | .maySearchLibrary eligible count dest after kind =>
      if q == p then
        let waitingPlusOne := g.plusOneAfterSearch
        let g := g.changes (#[
          .chooseModesRest none,
          .untapSearchedIfLands none,
          .plusOneAfterSearch none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        let g :=
          match waitingPlusOne with
          | some (cid, ctrl, srcId) =>
            if ctrl != p && g.stillInGame ctrl then
              g.withOuterContStashed fun g =>
                g.chainPendingReplacement (.finishPostStep (.applyPlusOneAfterSearch cid ctrl srcId))
            else g
          | none => g
        (g, .none)
      else
        let g :=
          if g.plusOneAfterSearch.any (fun (_, ctrl, _) => ctrl == p || !g.stillInGame ctrl) then
            g.change (.plusOneAfterSearch none)
          else g
        let liveEligible := eligible.filter (fun id => (g.findObject? id).isSome)
        (g,
          if liveEligible != eligible then
            .fraChoice q (match choice with
              | .searchLibrary .. => .searchLibrary liveEligible count dest after kind
              | _ => .maySearchLibrary liveEligible count dest after kind)
          else pending)
    | .castCopiesFree ids budget castsLeft =>
      if q == p then
        let alive := ids.filter (fun id => (g.findObject? id).any (·.zone == .exile))
        let g :=
          if alive.isEmpty then g
          else
            g.withBatch (some (.stateBased .copyOutsideStackOrBf)) fun g =>
              alive.foldl (fun g id =>
                g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))) g
        let g := g.changes (#[.chooseModesRest none, .pendingFreeCopies none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let alive := ids.filter (fun id => (g.findObject? id).any (·.zone == .exile))
        let castable := alive.filter (fun id =>
          (g.findObject? id).any (fun o => g.objectManaValue o ≤ budget))
        if castable.isEmpty || castsLeft == 0 then
          let g :=
            if alive.isEmpty then g
            else
              g.withBatch (some (.stateBased .copyOutsideStackOrBf)) fun g =>
                alive.foldl (fun g id =>
                  g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))) g
          let g := g.changes #[.chooseModesRest none, .pendingFreeCopies none]
          let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
          (g, .none)
        else if alive != ids then
          (g, .fraChoice q (.castCopiesFree alive budget castsLeft))
        else (g, pending)
    | .mayCastCopy copyId =>
      if q == p then
        let g : Game :=
          match g.findObject? copyId with
          | some (o : GameObject) =>
            if o.zone == Zone.exile && o.isCopy then
              let objName := g.name o
              (g.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
                s!"The copy of {objName} ceases to exist"
            else g
          | none => g
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else if !(g.findObject? copyId).any (·.zone == .exile) then
        let g := g.change (.chooseModesRest none)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
    | .mayCastCascade cardId others =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else
        let liveOthers := others.filter (fun id => (g.findObject? id).any (·.zone == .exile))
        if !(g.findObject? cardId).any (·.zone == .exile) then
          let g :=
            g.withOuterContStashed fun g =>
              let cause := g.lastMoveCauseOf? cardId
              let g := g.change (.chooseModesRest none)
              let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
              if liveOthers.isEmpty then g
              else
                g.requestOrderInto liveOthers (.library q)
                  s!"{(g.player q).name} puts the exiled cards on the bottom of their library in a random order"
                  (cause := cause)
          (g, g.pending)
        else if liveOthers != others then
          (g, .fraChoice q (.mayCastCascade cardId liveOthers))
        else (g, pending)
    | _ =>
      if q == p then
        let g := g.changes (#[.chooseModesRest none] ++ clearProp)
        let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
        (g, .none)
      else (g, pending)
  | .mayDiscardDraw q _ | .maySacArtifactOrDiscard q _ =>
    if q == p then
      let clearProp : Array EngineChange :=
        if abortedProp then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[.chooseModesRest none] ++ clearProp)
      let g :=
        if g.mayThenDrop > 0 then g.declineMayThenCore
        else clearPending g
      (g.logMsg s!"{(g.player p).name} declines (CR 800.4f)", .none)
    else (g, pending)
  | .scry q .. | .surveil q .. =>
    if q == p then
      let clearProp : Array EngineChange :=
        if abortedProp then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[
        .chooseModesRest none,
        .surveilReturnMvAtMost none,
        .surveilReturnNoncreatureNonland false] ++ clearProp)
      let g :=
        if g.mayThenDrop > 0 then g.declineMayThenCore
        else clearPending g
      let g :=
        g.withOuterContStashed fun g =>
          g.chainPendingReplacement .finishLibraryLook
      (g, .none)
    else (g, pending)
  | .sacrificeCreature q =>
    if q == p then
      let clearProp : Array EngineChange :=
        if abortedProp then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[.chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else if (g.sacrificeCreatureChoices q).isEmpty then
      let g := (g.change (.chooseModesRest none)).logMsg
        s!"{(g.player q).name} has no creature to sacrifice"
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else (g, pending)
  | .mayAttachEquipment q hostId sourceId =>
    if q == p then
      let clearProp : Array EngineChange :=
        if abortedProp then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[.chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else if !(g.findObject? hostId).any (fun o => o.isOnBattlefield && g.isCreature o) ||
        (sourceId.isSome && !(g.legalTargetsForKind q .permanent sourceId).contains (Target.permanent hostId)) ||
        !(g.permanentsOf q).any g.isEquipment then
      let g := g.change (.chooseModesRest none)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else (g, pending)
  | .maySacrificeAnotherBolg q bolgId =>
    if q == p then
      let clearProp : Array EngineChange :=
        if abortedProp then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[.chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else if !((g.creaturesControlledBy q).any (·.id != bolgId)) then
      let g := g.change (.chooseModesRest none)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else (g, pending)
  | .recruitDiscard q
  | .mayCastFromLooked q _ _ | .putOnBottom q _
  | .mayPutLandFromHand q
  | .mayHaveVillainConnive q _ _ | .declareMulligan q | .chooseProliferate q _ =>
    if q == p then
      let clearProp : Array EngineChange :=
        if abortedProp then #[.proposedSpell none, .clearProposalCheckpoint]
        else #[]
      let g := g.changes (#[.chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else (g, pending)
  | .mayCastExiledElseDamage q cardId n sid =>
    if q == p then
      let g := g.changes (#[.chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      let g := g.logMsg s!"{(g.player p).name} declines (CR 800.4f)"
      let g :=
        if n > 0 then
          g.withOuterContStashed fun g =>
            g.chainPendingReplacement
              (.finishPostStep (.dealDamageToEachOpponent p n sid (some (g.resolvingOrRuleCause p sid))))
        else g
      (g, .none)
    else if !(g.findObject? cardId).any (·.zone == .exile) then
      let g := g.change (.chooseModesRest none)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      let g :=
        if n > 0 then
          g.withOuterContStashed fun g =>
            g.chainPendingReplacement
              (.finishPostStep (.dealDamageToEachOpponent q n sid (some (g.resolvingOrRuleCause q sid))))
        else g
      (g, .none)
    else (g, pending)
  | .chooseTriggerOr q =>
    if q == p then
      let g := g.changes (#[.triggerOr none, .chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else (g, pending)
  | .tapHumans q =>
    if q == p then
      let g := g.changes (#[
        .triggerSequenceRest none,
        .humansTappedThisWay 0,
        .chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else (g, pending)
  | .mayPutArtifactFromHand q _ =>
    if q == p then
      let g := g.changes (#[
        .triggerSequenceRest none,
        .putArtifactThisWay none,
        .chooseModesRest none] ++ clearProp)
      let g := if g.mayThenDrop > 0 then g.declineMayThenCore else clearPending g
      (g, .none)
    else (g, pending)
  | .mayResolve q =>
    if q == p then
      match g.mayOnDecline with
      | some follow =>
        if g.mayContext.isSome then
          let g := g.withOuterContStashed fun g =>
            (((clearPendingAnd g #[.setTriggerSequenceRestFromMay [follow]]).clearMay).logMsg
              s!"{(g.player p).name} declines (CR 800.4f)").resumeTriggerSequence
          (g, g.pending)
        else ((clearPending g).clearMay, .none)
      | none => ((clearPending g).clearMay, .none)
    else
      match g.mayEffect with
      | some me =>
        if !g.mayTargets.isEmpty &&
            g.sequenceAllTargetsIllegal g.mayController me g.mayTargets g.maySource then
          (((clearPending g).clearMay).logMsg "The target is no longer legal", .none)
        else (g, pending)
      | none => (g, pending)
  | .chooseLibraryPlacement q id? =>
    if q == p then ((clearPending g).clearSpellOr, .none)
    else if (g.spellOrLibrary || id?.isSome) &&
        id?.any (fun id => !(g.findObject? id).any (·.isOnBattlefield)) then
      (((clearPending g).clearSpellOr).logMsg "The target is no longer legal", .none)
    else if !g.spellOrLibrary && !g.spellOr.isEmpty && !g.spellOrTargets.isEmpty &&
        g.sequenceAllTargetsIllegal g.spellOrController g.spellOr[0]! g.spellOrTargets g.spellOrSource then
      (((clearPending g).clearSpellOr).logMsg "The target is no longer legal", .none)
    else (g, pending)
  | .resolveRandom req =>
    match req with
    | .shuffleLibrary q =>
      if q == p then
        if g.pregameRandom != .none then
          (clearPending g, .none)
        else if g.afterRandom == .none ||
            g.afterRandom.player?.any (fun r => r == p || !g.stillInGame r) then
          (clearPendingAnd g (if g.afterRandom != .none then #[.afterRandom .none] else #[]), .none)
        else
          let after := g.afterRandom
          let g :=
            g.withOuterContStashed fun g =>
              (clearPendingAnd g #[.afterRandom .none]).chainPendingReplacement
                (.finishPostStep (.runAfterRandom after))
          (g, .none)
      else if g.afterRandom.player?.any (fun r => r == p || !g.stillInGame r) then
        (g.change (.afterRandom .none), pending)
      else (g, pending)
    | .orderInto ids dest cause =>
      let destGone :=
        match dest with
        | .library q | .hand q | .graveyard q | .outside q => q == p || !g.stillInGame q
        | _ => false
      let liveIds := ids.filter (fun id => (g.findObject? id).isSome)
      if destGone || liveIds.isEmpty then
        if g.afterRandom == .none ||
            g.afterRandom.player?.any (fun r => r == p || !g.stillInGame r) then
          (clearPendingAnd g (if g.afterRandom != .none then #[.afterRandom .none] else #[]), .none)
        else
          let after := g.afterRandom
          let g :=
            g.withOuterContStashed fun g =>
              (clearPendingAnd g #[.afterRandom .none]).chainPendingReplacement
                (.finishPostStep (.runAfterRandom after))
          (g, .none)
      else if liveIds.size == 1 then
        let g :=
          g.withOuterContStashed fun g =>
            let after := g.afterRandom
            let clearAfter : Array EngineChange :=
              if after != .none then #[.afterRandom .none] else #[]
            let g := (clearPendingAnd g clearAfter).moveIdsInOrder liveIds dest (cause := cause)
            if after != .none && !after.player?.any (fun r => r == p || !g.stillInGame r) then
              g.chainPendingReplacement (.finishPostStep (.runAfterRandom after))
            else g
        (g, g.pending)
      else if liveIds != ids then
        (g, .resolveRandom (.orderInto liveIds dest cause))
      else (g, pending)
    | .chooseObject ids =>
      let liveIds := ids.filter (fun id => (g.findObject? id).isSome)
      if g.afterRandom.player?.any (fun r => r == p || !g.stillInGame r) then
        (clearPendingAnd g #[.afterRandom .none, .stashedCause none], .none)
      else if liveIds.isEmpty then
        match g.afterRandom with
        | .revealRandomCreatureThenBottom ctrl revealed =>
          if ctrl != p && g.stillInGame ctrl then
            let g :=
              g.withOuterContStashed fun g =>
                let cause := g.stashedCause
                let g := clearPendingAnd g #[.afterRandom .none, .stashedCause none]
                g.putRestOnBottomRandom ctrl
                  (revealed.filter (fun id => (g.findObject? id).isSome))
                  (cause := cause)
            (g, g.pending)
          else
            (clearPendingAnd g #[.afterRandom .none, .stashedCause none], .none)
        | _ =>
          (clearPendingAnd g #[.afterRandom .none, .stashedCause none], .none)
      else if liveIds.size == 1 then
        let g :=
          g.withOuterContStashed fun g =>
            g.autoResolveSingleChooseObject liveIds[0]!
        (g, g.pending)
      else if liveIds != ids then
        (g, .resolveRandom (.chooseObject liveIds))
      else (g, pending)
    | .chooseIndex _ =>
      if g.pregameRandom == .none &&
          (g.afterRandom.player?.any (fun r => r == p || !g.stillInGame r) ||
            (g.currentResolvingContext?.bind Prod.snd) == some p) then
        (clearPendingAnd g #[.afterRandom .none], .none)
      else (g, pending)

/-- Re-pause a saved `currentBatch` snapshot once a departing player's leave /
linked-exile batch has closed, or finish `batchId` immediately when
`redirectPendingAfterLeave` ended the batch's awaiting prompt while the leave
batch owned `currentBatch` (CR 603.2c / 701.9b / 800.4a). -/
def restorePausedBatch (g : Game) (batchId : BatchId) (startIdx : Nat) (wasDiscard : Bool)
    (cause : Option EventCause) (objects : Array GameObject)
    (players : Array Player) (effects : Array (EffectId × ContinuousEffectSpec))
    (pending : Pending) (stack : Array StackEntry := #[]) : Game :=
  let g := g.change (.pauseBatch batchId cause objects players effects pending stack)
  if (wasDiscard && g.discardBatch.isNone) || (!wasDiscard && !hasCloseBatchFor g batchId) then
    g.finishOpenBatchAndLinkedExile batchId startIdx
  else g

/-- Whether a saved `Pending.chooseReplacement q choices` prompt remains valid in
`g`: `q` is still in the game and every choice's referenced subject, grantor,
and kind-specific object IDs still exist (and any `.asEntersAttachAura` host is
still on the battlefield) (CR 616.1 / 800.4a). -/
def replacementChoiceValid (g : Game) (q : PlayerId) (choices : Array ReplacementId)
    (allowLost : Bool := false) : Bool :=
  (if allowLost then !(g.player q).leftTheGame else g.stillInGame q) &&
    choices.all fun c =>
      c.object.all (fun oid => (g.findObject? oid).isSome) &&
        c.grantor.all (fun gid => (g.findObject? gid).isSome) &&
        match c.kind with
        | .entersUntappedBehold boId _ => (g.findObject? boId).isSome
        | .entersAsCopyCreatureUntilEot cid => (g.findObject? cid).isSome
        | .asEntersAttachAura hid => (g.findObject? hid).any (·.isOnBattlefield)
        | _ => true

@[extern "mtg_game_resume_pending_replacement"]
private opaque resumePendingReplacement (g : Game) (pr : PendingReplacement)
    (followedByFinishFra : Bool := false) : Game := g

/-- Roll back an active proposal aborted by a player's departure using
`reverseToProposalCheckpoint?`, the reversal log, and `runPostCastCleanup`
without granting priority or resuming continuations early (CR 601.2 / 602.2 /
733.1 / 800.4a). -/
def rewindAbortedProposalOnLeave (g : Game)
    (departed : Array PlayerId := #[])
    (pushedOuterCont? : Option PendingReplacement := none)
    (clearCkptPendingReplacement : Bool := false) :
    Game × Option PendingReplacement :=
  match g.proposedSpell with
  | none => (g, pushedOuterCont?)
  | some prop =>
    match g.reverseToProposalCheckpoint? with
    | .error _ => (g, pushedOuterCont?)
    | .ok g =>
      let g :=
        if clearCkptPendingReplacement && g.pendingReplacement.isSome then
          g.change (.pendingReplacement none)
        else g
      let name := (g.player prop.caster).name
      let reversed :=
        match prop.kind with
        | .spell => "the casting is reversed (CR 601.2 / 733.1)"
        | .activatedAbility => "the activation is reversed (CR 602.2 / 733.1)"
        | .turnFaceUp => "turning it face up is reversed (CR 116.2b / 702.37e / 733.1)"
      let g := g.logMsg s!"{name} cannot pay {prop.cost}; {reversed}"
      let g := if g.over then g else g.runPostCastCleanup
      let g :=
        if !departed.isEmpty then g.appendDepartedManyToContinuations departed else g
      let (g, pushedOuterCont?) :=
        if !g.sbaPaused then
          let combined :=
            match g.pendingReplacement, pushedOuterCont? with
            | some rCont, some outer => some (.seq rCont outer)
            | some rCont, none => some rCont
            | none, some outer => some outer
            | none, none => none
          let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
          (g, combined)
        else
          (g, pushedOuterCont?)
      (g, pushedOuterCont?)

/-- Chain an additional pending decision `extra?` behind `primary?`, prepending a
`.restorePending` continuation onto `pushedOuterCont?` when both are non-`.none`
so neither decision is dropped (CR 701.20a / 608.2 / 800.4a). -/
def chainSavedPending (primary? extra? : Option Pending)
    (pushedOuterCont? : Option PendingReplacement)
    (departed : Array PlayerId) :
    Option Pending × Option PendingReplacement :=
  match primary?, extra? with
  | some p1, some p2 =>
    if p1 == .none then (some p2, pushedOuterCont?)
    else if p2 == .none then (some p1, pushedOuterCont?)
    else
      let restoreExtra : PendingReplacement :=
        .restorePending p2 false (departed := departed)
      let combined :=
        match pushedOuterCont? with
        | some outer => some (.seq restoreExtra outer)
        | none => some restoreExtra
      (some p1, combined)
  | some p1, none => (some p1, pushedOuterCont?)
  | none, some p2 => (some p2, pushedOuterCont?)
  | none, none => (none, pushedOuterCont?)

/-- If `rewindAbortedProposalOnLeave` opened a non-replacement prompt (such as
`.resolveRandom (.orderInto …)` from `runPostCastCleanup`), capture it into
`saved?` and chain any prior saved prompt `oldP` at the front of
`pushedOuterCont?` so neither prompt is dropped (CR 701.20a / 608.2 / 800.4a). -/
def stashPostRewindPending (g : Game)
    (saved? : Option Pending)
    (pushedOuterCont? : Option PendingReplacement)
    (departed : Array PlayerId) :
    Game × Option Pending × Option PendingReplacement :=
  if !g.sbaPaused && g.pending != .none then
    let sp := g.pending
    let g := g.change (.pending .none)
    let (saved?, pushedOuterCont?) :=
      chainSavedPending (some sp) saved? pushedOuterCont? departed
    (g, saved?, pushedOuterCont?)
  else
    (g, saved?, pushedOuterCont?)

/-- Apply a deferred aborted-proposal rewind once a departure's replacement
pause finishes, preserving any outer continuation on `g.outerPendingReplacements`
and chaining any restored post-cast cleanup prompt with `saved?` (CR 733.1 / 800.4a). -/
def applyDeferredProposalRewind (g : Game)
    (saved? : Option Pending) (popOuter : Bool)
    (departed : Array PlayerId)
    (hadPreBodyCont : Bool) : Game × Option Pending × Bool :=
  let popped? : Option PendingReplacement :=
    if popOuter then g.outerPendingReplacements.back? else none
  let g := if popped?.isSome then g.change .popOuterPendingReplacement else g
  let (g, pushedOuterCont?) :=
    g.rewindAbortedProposalOnLeave departed popped? hadPreBodyCont
  let (g, saved?, pushedOuterCont?) :=
    g.stashPostRewindPending saved? pushedOuterCont? departed
  let g :=
    match pushedOuterCont? with
    | some outer =>
      let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
      g.change (.pushOuterPendingReplacement outer)
    | none => g
  (g, saved?, pushedOuterCont?.isSome)

/-- Restore a non-SBA pending decision saved across `playerLeavesGameCore`,
popping any pushed outer `pendingReplacement` when unpaused (CR 800.4a). -/
def restoreSavedPostLeave (g : Game) (saved? : Option Pending) (popOuter : Bool)
    (departed : Array PlayerId := #[]) (rewindProposal : Option Bool := none) : Game :=
  match saved? with
  | none =>
    if !popOuter && rewindProposal.isNone then g
    else if g.sbaPaused || g.pendingReplacement.isSome then
      g.chainPendingReplacement
        (.restorePending .none popOuter (departed := departed) (rewindProposal := rewindProposal))
    else
      g.resumePendingReplacement
        (.restorePending .none popOuter (departed := departed) (rewindProposal := rewindProposal))
  | some saved =>
    if g.sbaPaused || g.pendingReplacement.isSome then
      g.chainPendingReplacement
        (.restorePending saved popOuter (departed := departed) (rewindProposal := rewindProposal))
    else
      g.resumePendingReplacement
        (.restorePending saved popOuter (departed := departed) (rewindProposal := rewindProposal))

/-- Core implementation of `playerLeavesGame` (CR 800.4 / 800.4a). When
`deferRestore` is `true`, returns `(g, savedPreLeavePending?, popOuter, deferredRewind)`
instead of chaining `.restorePending` immediately so multi-player departure
loops (`leavePlayersWhoLost`, `concede`) can finish remaining departures and
post-departure SBAs before restoring `savedPreLeavePending?` / `popOuter`. -/
def playerLeavesGameCore (g : Game) (p : PlayerId)
    (deferRestore : Bool := false)
    (pendingIn : Option Pending := none)
    (departedIn : Array PlayerId := #[]) : Game × Option Pending × Bool × Option Bool :=
  if (g.player p).leftTheGame then (g, none, false, none)
  else
    let departed := if departedIn.contains p then departedIn else departedIn.push p
    let cause := some (EventCause.gameRule .playerLeftGame)
    let wasMonarch := (g.player p).isMonarch
    let owned := g.objects.filter (fun o =>
      o.owner == p && o.zone != .ante &&
        (o.zone != .stack || representedByCard o || g.controlledBy o p))
    let linkedExileIds := owned.foldl (fun acc o =>
      if o.zone == .battlefield then acc ++ o.linkedExile else acc) #[]
    let savedPausedBatch? :=
      match g.currentBatch with
      | some (origBid, origCause) =>
        let wasDiscard := g.discardBatch.map Prod.fst == some origBid
        let origStartIdx :=
          if wasDiscard then
            (g.discardBatch.map Prod.snd).getD 0
          else
            ((g.pendingReplacement.bind (findPausedCloseBatchFor? origBid)).orElse
              (fun _ => g.outerPendingReplacements.findSomeRev? (findPausedCloseBatchFor? origBid)))
              |>.getD (findEarliestBatchIdx g origBid)
        some (origBid, origStartIdx, wasDiscard, origCause, g.openBatchObjects,
          g.openBatchPlayers, g.openBatchEffects, g.openBatchPending, g.openBatchStack)
      | none => none
    let g := if savedPausedBatch?.isSome then g.change .clearPausedBatch else g
    let wasAbortedProposal := g.isProposalAbortedByLeave p
    let rewindAbortedProposal :=
      wasAbortedProposal && g.proposalCheckpoint.isSome &&
        g.proposedSpell.any (fun prop => prop.caster != p && g.stillInGame prop.caster)
    let (g, (savedPreLeavePending?, pushedOuterCont?, hadPreBodyCont)) := g.withBatchCoreReturn cause fun g =>
      let preBodyPending := pendingIn.getD g.pending
      let abortedCaster? := if wasAbortedProposal then g.proposedSpell.map (·.caster) else none
      let abortingReplacementProposal :=
        wasAbortedProposal &&
          ((match preBodyPending with | .chooseReplacement .. => true | _ => false) ||
            abortedCaster?.any (fun c => g.pendingReplacement.any (hasProposalBoundaryStep c)))
      let preBodyCont? :=
        match abortedCaster?, g.pendingReplacement with
        | some c, some pr =>
          if abortingReplacementProposal || hasProposalBoundaryStep c pr then
            stripAbortedProposalCont c pr
          else some pr
        | _, pr? => if abortingReplacementProposal then none else pr?
      let preBodyCont? := preBodyCont?.map (PendingReplacement.appendDepartedMany departed)
      let hadPreBodyCont := preBodyCont?.isSome
      let g :=
        match abortedCaster?, g.outerPendingReplacements.back? with
        | some c, some back =>
          if hasProposalBoundaryStep c back then
            let replaced := (stripAbortedProposalCont c back).getD (.restorePending .none false (departed := departed))
            g.changes #[.popOuterPendingReplacement, .pushOuterPendingReplacement replaced]
          else g
        | _, _ => g
      let g :=
        g.changes
          ((if g.pending != .none then #[EngineChange.pending .none] else #[]) ++
           (if g.pendingReplacement.isSome then #[EngineChange.pendingReplacement none] else #[]) ++
           (if abortingReplacementProposal && !rewindAbortedProposal then
              #[EngineChange.proposedSpell none, EngineChange.clearProposalCheckpoint]
            else #[]))
      let g := g.appendDepartedManyToContinuations departed
      let g := g.record (GameEvent.playerLeftGame g.turnNumber p (cause := cause))
      let g := g.logMsg s!"{(g.player p).name} leaves the game"
      let g :=
        if !(g.player p).manaPool.isEmpty then
          g.record (GameEvent.manaEmptied g.turnNumber p (g.player p).manaPool.toUnits false (cause := cause))
        else g
      let g :=
        if wasMonarch && !g.over && g.livingPlayers.size > 1 then
          let heir :=
            if g.stillInGame g.activePlayer && g.activePlayer != p then g.activePlayer
            else if !g.isSharedTurnFinalSeat then g.nextLiving g.activePlayer
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
            if you == p || them == p || (acc.areTeammates them p && !acc.stillInGame them) then
              acc.expireEffectById eid (cause := cause)
            else acc
          | _ => acc) g
      let bodyExilePending? := if g.pending != .none then some g.pending else none
      let bodyExileCont? := g.pendingReplacement
      let g :=
        g.changes
          ((if bodyExilePending?.isSome then #[EngineChange.pending .none] else #[]) ++
           (if bodyExileCont?.isSome then #[EngineChange.pendingReplacement none] else #[]))
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
      let runPostCastAndPropCleanup (g : Game) (curPending : Pending := g.pending) : Game × Pending :=
        let clearPropInCleanup : Array EngineChange :=
          if !rewindAbortedProposal then #[.proposedSpell none, .clearProposalCheckpoint]
          else #[]
        let orderBottomInCleanup (g : Game) (ids : Array ObjectId) (dest : Zone)
            (log : String) (cause : Option EventCause := none) : Game × Pending :=
          let (g, cause) : Game × Option EventCause :=
            match cause with
            | some c => (g, some c)
            | none =>
              if ids.isEmpty then (g, none)
              else
                match g.currentResolvingContext? with
                | some (src, ctrl) =>
                  let (g, c) := g.allocDelayedCause ctrl src
                  (g, some c)
                | none => (g, none)
          if let .chooseReplacement .. := g.pending then
            let g := g.withOuterContStashed fun g => g.requestOrderInto ids dest log (cause := cause)
            (g, curPending)
          else if curPending != .none then
            let g := g.withOuterContStashed fun g => g.moveIdsInOrder ids dest (cause := cause) (log := log)
            (g, curPending)
          else if ids.size > 1 then
            (g.logMsg log, .resolveRandom (.orderInto ids dest cause))
          else
            let g := g.withOuterContStashed fun g => g.requestOrderInto ids dest log (cause := cause)
            (g, g.pending)
        let prePostCastEvCount := g.events.size
        let (g, curPending) :=
          match g.postCastCleanup with
          | some (.grimaBottom victim cardId others) =>
            if p == victim then
              (g.change (.postCastCleanup none), curPending)
            else if wasAbortedProposal && !rewindAbortedProposal then
              let g := g.changes (clearPropInCleanup ++ #[EngineChange.postCastCleanup none])
              if g.stillInGame victim then
                let landed := g.followMoved cardId
                let uncast :=
                  if (g.findObject? cardId).any (fun (o : GameObject) => o.zone == Zone.exile) then #[cardId]
                  else if (g.findObject? landed).any (fun (o : GameObject) => o.zone == Zone.exile) then #[landed]
                  else #[]
                let live := (others ++ uncast).filter (fun id =>
                  (g.findObject? id).any (fun (o : GameObject) => o.zone == Zone.exile))
                if live.isEmpty then (g, curPending)
                else
                  let c := g.lastMoveCauseOf? cardId
                  orderBottomInCleanup g live (.library victim)
                    s!"{(g.player victim).name} puts the exiled cards on the bottom of their library in a random order"
                    (cause := c)
              else (g, curPending)
            else (g, curPending)
          | some (.cascadeBottom caster cardId others) =>
            if p == caster then
              (g.change (.postCastCleanup none), curPending)
            else if wasAbortedProposal && !rewindAbortedProposal then
              let g := g.changes (clearPropInCleanup ++ #[EngineChange.postCastCleanup none])
              if g.stillInGame caster then
                let landed := g.followMoved cardId
                let uncast :=
                  if (g.findObject? cardId).any (fun (o : GameObject) => o.zone == Zone.exile) then #[cardId]
                  else if (g.findObject? landed).any (fun (o : GameObject) => o.zone == Zone.exile) then #[landed]
                  else #[]
                let live := (others ++ uncast).filter (fun id =>
                  (g.findObject? id).any (fun (o : GameObject) => o.zone == Zone.exile))
                if live.isEmpty then (g, curPending)
                else
                  let c := g.lastMoveCauseOf? cardId
                  orderBottomInCleanup g live (.library caster)
                    s!"{(g.player caster).name} puts the exiled cards on the bottom of their library in a random order"
                    (cause := c)
              else (g, curPending)
            else (g, curPending)
          | some (.copyCeaseToExist copyId) =>
            let landed := g.followMoved copyId
            if (wasAbortedProposal && !rewindAbortedProposal) ||
                ((g.findObject? copyId).isNone && (g.findObject? landed).isNone) then
              let g := g.changes (#[EngineChange.postCastCleanup none] ++
                (if wasAbortedProposal then clearPropInCleanup else #[]))
              let copyCause := some (EventCause.stateBased .copyOutsideStackOrBf)
              let g :=
                match g.findObject? copyId with
                | some o =>
                  if o.isCopy then (g.ceaseToExist o.id (cause := copyCause)).logMsg s!"The copy of {g.name o} ceases to exist"
                  else g
                | none =>
                  match g.findObject? landed with
                  | some o =>
                    if o.isCopy then (g.ceaseToExist o.id (cause := copyCause)).logMsg s!"The copy of {g.name o} ceases to exist"
                    else g
                  | none => g
              (g, curPending)
            else (g, curPending)
          | some (.lookedBottom caster _cardId allLooked) =>
            if p == caster then
              (g.change (.postCastCleanup none), curPending)
            else if wasAbortedProposal && !rewindAbortedProposal then
              let g := g.changes (clearPropInCleanup ++ #[EngineChange.postCastCleanup none])
              if g.stillInGame caster then
                let unchosen := allLooked.filter (fun id =>
                  (g.findObject? id).any (fun (o : GameObject) => o.zone == Zone.library caster))
                if unchosen.isEmpty then (g, curPending)
                else
                  orderBottomInCleanup g unchosen (.library caster)
                    s!"{(g.player caster).name} puts the rest on the bottom of their library in a random order"
              else (g, curPending)
            else (g, curPending)
          | none => (g, curPending)
        let postCastTouchedPending :=
          (g.events.extract prePostCastEvCount g.events.size).any fun ev =>
            match ev with
            | .engine _ (.pending _) _ => true
            | _ => false
        let curPending := if curPending == .none && postCastTouchedPending then g.pending else curPending
        let g :=
          if (!rewindAbortedProposal && wasAbortedProposal &&
                (g.proposedSpell.isSome || g.proposalCheckpoint.isSome)) ||
              g.proposedSpell.any (fun (prop : ProposedSpell) => prop.caster == p) then
            g.changes #[.proposedSpell none, .clearProposalCheckpoint]
          else g
        let (g, curPending) :=
          match g.pendingMayCastFromExile with
          | some (q, ids, left) =>
            let alive := ids.filter (fun id =>
              (g.findObject? id).any (fun (o : GameObject) => o.zone == Zone.exile && !g.isLand o))
            if q == p || !g.stillInGame q || alive.isEmpty || left == 0 then
              (g.change (.pendingMayCastFromExile none), curPending)
            else if wasAbortedProposal && curPending == Pending.none then
              let nextP := Pending.fraChoice q (.mayCastUpToFromExile alive left)
              let g :=
                (g.change (.pendingMayCastFromExile none)).logMsg
                  s!"{(g.player q).name} may cast up to {left} more spells from among the exiled cards without paying their mana costs"
              (g, nextP)
            else if alive != ids then
              (g.change (.pendingMayCastFromExile (some (q, alive, left))), curPending)
            else (g, curPending)
          | none => (g, curPending)
        match g.pendingFreeCopies with
        | some (q, ids, budget, castsLeft) =>
          let alive := ids.filter (fun id =>
            (g.findObject? id).any (fun (o : GameObject) => o.zone == Zone.exile))
          if q == p || !g.stillInGame q then
            let g :=
              if alive.isEmpty then g
              else
                g.withBatch (some (.stateBased .copyOutsideStackOrBf)) fun g =>
                  alive.foldl (fun g id =>
                    g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))) g
            (g.change (.pendingFreeCopies none), curPending)
          else
            let castable := alive.filter (fun id =>
              (g.findObject? id).any (fun o => g.objectManaValue o ≤ budget))
            if castable.isEmpty || castsLeft == 0 then
              let g :=
                if alive.isEmpty then g
                else
                  g.withBatch (some (.stateBased .copyOutsideStackOrBf)) fun g =>
                    alive.foldl (fun g id =>
                      g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))) g
              (g.change (.pendingFreeCopies none), curPending)
            else if wasAbortedProposal && curPending == Pending.none then
              let nextP := Pending.fraChoice q (.castCopiesFree alive budget castsLeft)
              let g := g.change (.pendingFreeCopies none)
              (g, nextP)
            else if alive != ids then
              (g.change (.pendingFreeCopies (some (q, alive, budget, castsLeft))), curPending)
            else (g, curPending)
        | none => (g, curPending)
      match preBodyPending with
      | .chooseReplacement q choices =>
        if q != p && !abortingReplacementProposal then
          let choicesStillValidPre := g.replacementChoiceValid q choices (allowLost := true)
          let (g, postCleanupPending) :=
            runPostCastAndPropCleanup g (if choicesStillValidPre then preBodyPending else .none)
          let g :=
            if g.pending != .none then g.change (.pending .none) else g
          let combinedOuter? : Option PendingReplacement :=
            match g.pendingReplacement, preBodyCont? with
            | some rCont, some preCont => some (.seq rCont preCont)
            | some rCont, none => some rCont
            | none, some preCont => some preCont
            | none, none => none
          let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
          let g :=
            match combinedOuter? with
            | some outer => g.change (.pushOuterPendingReplacement outer)
            | none => g
          let g :=
            match bodyExilePending? with
            | some bp =>
              let g := g.change (.pending bp)
              match bodyExileCont? with
              | some bc => g.change (.pendingReplacement (some bc))
              | none => g
            | none => g
          let g := g.runEndControlExileLoop exileQueue (cause := cause)
          let choicesStillValid := g.replacementChoiceValid q choices (allowLost := true)
          let savedPreLeavePending? : Option Pending :=
            if choicesStillValid then some preBodyPending
            else if postCleanupPending != .none && postCleanupPending != preBodyPending then some postCleanupPending
            else none
          (g, (savedPreLeavePending?, combinedOuter?, hadPreBodyCont))
        else
          let (g, postCleanupPending) := runPostCastAndPropCleanup g .none
          let openedNewReplacement :=
            match postCleanupPending with
            | .chooseReplacement .. => true
            | _ => false
          if openedNewReplacement then
            let g :=
              match preBodyCont? with
              | some outer => g.change (.pushOuterPendingReplacement outer)
              | none => g
            let g :=
              match bodyExilePending? with
              | some bp =>
                let redirP := postCleanupPending
                let redirC? := g.pendingReplacement
                let g := g.changes #[.pending bp, .pendingReplacement bodyExileCont?]
                let g := g.chainPendingReplacement (.restorePending redirP false (departed := departed))
                match redirC? with
                | some rc => g.chainPendingReplacement rc
                | none => g
              | none => g
            let g := g.runEndControlExileLoop exileQueue (cause := cause)
            (g, (none, preBodyCont?, hadPreBodyCont))
          else
            let savedPreLeavePending? : Option Pending :=
              if postCleanupPending != .none then some postCleanupPending else none
            let g :=
              if g.pending != .none then g.change (.pending .none) else g
            let combinedOuter? : Option PendingReplacement :=
              match g.pendingReplacement, preBodyCont? with
              | some rCont, some preCont => some (.seq rCont preCont)
              | some rCont, none => some rCont
              | none, some preCont => some preCont
              | none, none => none
            let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
            let g :=
              match combinedOuter? with
              | some outer => g.change (.pushOuterPendingReplacement outer)
              | none => g
            let g :=
              match bodyExilePending? with
              | some bp =>
                let g := g.change (.pending bp)
                match bodyExileCont? with
                | some bc => g.change (.pendingReplacement (some bc))
                | none => g
              | none => g
            let g := g.runEndControlExileLoop exileQueue (cause := cause)
            (g, (savedPreLeavePending?, combinedOuter?, hadPreBodyCont))
      | _ =>
        let (g, redirPending) :=
          g.redirectPendingAfterLeave p (abortedProposal := wasAbortedProposal) (pending := preBodyPending)
        let (g, postRedirPending) := runPostCastAndPropCleanup g redirPending
        let openedNewReplacement :=
          match postRedirPending with
          | .chooseReplacement .. => true
          | _ => false
        if openedNewReplacement then
          let g :=
            match preBodyCont? with
            | some outer => g.change (.pushOuterPendingReplacement outer)
            | none => g
          let g :=
            match bodyExilePending? with
            | some bp =>
              let redirP := postRedirPending
              let redirC? := g.pendingReplacement
              let g := g.changes #[.pending bp, .pendingReplacement bodyExileCont?]
              let g := g.chainPendingReplacement (.restorePending redirP false (departed := departed))
              match redirC? with
              | some rc => g.chainPendingReplacement rc
              | none => g
            | none => g
          let g := g.runEndControlExileLoop exileQueue (cause := cause)
          (g, (none, preBodyCont?, hadPreBodyCont))
        else
          let savedPreLeavePending? : Option Pending :=
            if postRedirPending != .none then some postRedirPending else none
          let g :=
            if g.pending != .none then g.change (.pending .none) else g
          let combinedOuter? : Option PendingReplacement :=
            match g.pendingReplacement, preBodyCont? with
            | some rCont, some preCont => some (.seq rCont preCont)
            | some rCont, none => some rCont
            | none, some preCont => some preCont
            | none, none => none
          let g := if g.pendingReplacement.isSome then g.change (.pendingReplacement none) else g
          let g :=
            match combinedOuter? with
            | some outer => g.change (.pushOuterPendingReplacement outer)
            | none => g
          let g :=
            match bodyExilePending? with
            | some bp =>
              let g := g.change (.pending bp)
              match bodyExileCont? with
              | some bc => g.change (.pendingReplacement (some bc))
              | none => g
            | none => g
          let g := g.runEndControlExileLoop exileQueue (cause := cause)
          (g, (savedPreLeavePending?, combinedOuter?, hadPreBodyCont))
    let allLinked := linkedExileIds ++ g.queuedLinkedExile
    let g := if g.queuedLinkedExile.isEmpty then g else g.change .clearQueuedLinkedExile
    let g :=
      if allLinked.isEmpty then g
      else if g.sbaPaused || g.currentBatch.isSome then
        g.chainPendingReplacement (.finishLinkedExileMove allLinked)
      else
        g.returnLinkedExileMoves allLinked
    let shouldRewindProposal :=
      rewindAbortedProposal &&
        g.proposalCheckpoint.isSome &&
        g.proposedSpell.any (fun prop => g.stillInGame prop.caster)
    let depPaused := g.sbaPaused || g.currentBatch.isSome
    let g :=
      match if shouldRewindProposal then none else savedPausedBatch? with
      | some (origBid, origStartIdx, wasDiscard, origCause, origObjs, origPls, origEffs, origPend, origStk) =>
        if depPaused then
          g.chainPendingReplacement
            (.restorePausedBatch origBid origStartIdx wasDiscard origCause origObjs origPls origEffs origPend origStk)
        else
          g.restorePausedBatch origBid origStartIdx wasDiscard origCause origObjs origPls origEffs origPend origStk
      | none => g
    let (g, savedPreLeavePending?, pushedOuterCont?, deferredRewind) :=
      if shouldRewindProposal then
        if !depPaused then
          let (g, pushedOuterCont?) :=
            g.rewindAbortedProposalOnLeave departed pushedOuterCont? hadPreBodyCont
          let (g, savedPreLeavePending?, pushedOuterCont?) :=
            g.stashPostRewindPending savedPreLeavePending? pushedOuterCont? departed
          let g :=
            match pushedOuterCont? with
            | some outer =>
              let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
              g.change (.pushOuterPendingReplacement outer)
            | none => g
          (g, savedPreLeavePending?, pushedOuterCont?, none)
        else
          (g, savedPreLeavePending?, pushedOuterCont?, some hadPreBodyCont)
      else
        (g, savedPreLeavePending?, pushedOuterCont?, none)
    let popOuter := pushedOuterCont?.isSome
    if deferRestore then (g, savedPreLeavePending?, popOuter, deferredRewind)
    else
      (g.restoreSavedPostLeave savedPreLeavePending? popOuter
         (departed := departed) (rewindProposal := deferredRewind),
       none, false, none)

/-- `p` loses and leaves the game (CR 800.4 / 800.4a). Owned objects leave
immediately (until-leaves one-shots return); control-changing effects that
gave them control end; their non-card stack objects cease; remaining objects
they control are exiled. This is not a state-based action. -/
def playerLeavesGame (g : Game) (p : PlayerId) : Game :=
  (g.playerLeavesGameCore p false).1

/-- Core of `leavePlayersWhoLost`: returns `(g, saved?, popOuter, departed, rewindProposal)`
without immediately restoring `saved?` / `popOuter`, so `checkSBACounted` can
thread them across the post-departure SBA pass and only restore after all SBAs
finish (CR 104.5 / 800.4a). -/
def leavePlayersWhoLostCore (g : Game)
    (savedIn : Option Pending := none) (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none) :
    Game × Option Pending × Bool × Array PlayerId × Option Bool :=
  if g.over then (g, none, false, departedIn, none)
  else if let .chooseReplacement .. := g.pending then
    (g, savedIn, popOuterIn, departedIn, rewindProposalIn)
  else Id.run do
    let mut g := g
    let mut saved? := savedIn
    let mut popOuter := popOuterIn
    let mut departed := departedIn
    let mut rewindProposal := rewindProposalIn
    if let some hadPreBodyCont := rewindProposal then
      if !g.sbaPaused && g.currentBatch.isNone then
        let (g', s', po') := g.applyDeferredProposalRewind saved? popOuter departed hadPreBodyCont
        g := g'
        saved? := s'
        popOuter := po'
        rewindProposal := none
        if let .chooseReplacement .. := g.pending then
          return (g, saved?, popOuter, departed, none)
    for pl in g.players do
      if g.over then
        return (g, none, false, departed, none)
      if pl.lost && !(g.player pl.id).leftTheGame then
        if let some hadPreBodyCont := rewindProposal then
          if !g.sbaPaused && g.currentBatch.isNone then
            let (g', s', po') := g.applyDeferredProposalRewind saved? popOuter departed hadPreBodyCont
            g := g'
            saved? := s'
            popOuter := po'
            rewindProposal := none
            if let .chooseReplacement .. := g.pending then
              return (g, saved?, popOuter, departed, none)
        if popOuter then
          if let some popped := g.outerPendingReplacements.back? then
            g := (g.change .popOuterPendingReplacement).chainPendingReplacement popped
          popOuter := false
        let pendingIn := if g.pending == .none then saved? else none
        if pendingIn.isSome then
          saved? := none
        let (g', newlySaved?, po, rw) :=
          g.playerLeavesGameCore pl.id (deferRestore := true) (pendingIn := pendingIn)
            (departedIn := departed)
        g := g'
        departed := if departed.contains pl.id then departed else departed.push pl.id
        popOuter := popOuter || po
        match saved?, newlySaved? with
        | none, s => saved? := s
        | some .none, s => saved? := s.orElse (fun _ => some .none)
        | some oldP, some newP =>
          if newP != .none then
            let popped? : Option PendingReplacement :=
              if popOuter then g.outerPendingReplacements.back? else none
            if popped?.isSome then
              g := g.change .popOuterPendingReplacement
            let restoreOld : PendingReplacement := .restorePending oldP false (departed := departed)
            let outer :=
              match popped? with
              | some p => .seq restoreOld p
              | none => restoreOld
            if g.continuations.isEmpty then
              g := g.change (.pushContinuationFrame {})
            g := g.change (.pushOuterPendingReplacement outer)
            popOuter := true
            saved? := some newP
        | some _, none => pure ()
        rewindProposal :=
          match rewindProposal, rw with
          | some a, some b => some (a || b)
          | some a, none => some a
          | none, some b => some b
          | none, none => none
        if let .chooseReplacement .. := g.pending then
          return (g, saved?, popOuter, departed, rewindProposal)
    return (g, saved?, popOuter, departed, rewindProposal)

/-- Perform CR 800.4a for every player who has lost but has not yet left.
Skipped when the game has already ended (two-player games, CR 104.2a). If a
departing player's departure pauses on `Pending.chooseReplacement`, chains
`.leavePlayersWhoLost` for any remaining losers and deferred `savedPending`
(CR 104.5 / 800.4a). -/
def leavePlayersWhoLost (g : Game)
    (savedIn : Option Pending := none) (popOuterIn : Bool := false)
    (departedIn : Array PlayerId := #[])
    (rewindProposalIn : Option Bool := none) : Game :=
  let (g, saved?, popOuter, departed, rewindProposal) :=
    g.leavePlayersWhoLostCore savedIn popOuterIn departedIn rewindProposalIn
  if g.sbaPaused then
    if g.players.any (fun r => r.lost && !r.leftTheGame) || saved?.isSome || popOuter ||
        !departed.isEmpty || rewindProposal.isSome then
      g.chainPendingReplacement (.leavePlayersWhoLost saved? popOuter departed rewindProposal)
    else g
  else
    g.restoreSavedPostLeave saved? popOuter (departed := departed) (rewindProposal := rewindProposal)

def emptyManaPools (g : Game) : Game :=
  if !g.players.any (fun pl => g.stillInGame pl.id && !pl.manaPool.isEmpty) then g
  else
    let cause := some (EventCause.turnBased .emptyManaPools)
    g.withBatch cause fun g =>
      Id.run do
        let mut g := g
        for pl in g.players do
          if g.stillInGame pl.id && !pl.manaPool.isEmpty then
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
