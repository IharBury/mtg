import Mtg.Engine.Game.Triggers

/-!
# Cast and enters triggers (CR 601.2i / 603.6a)

Cast triggers, another-creature-enters triggers, counters added as a
permanent enters (CR 614.1c / 122.6), and everything that happens after a
permanent or land enters the battlefield.
-/

namespace Mtg.Engine
namespace Game

/-- Put “whenever you cast an instant or sorcery” triggers onto the stack
(CR 601.2i / 603.3). -/
def putCastTriggersOnStack (g : Game) (caster : PlayerId) (spell : GameObject) : Game :=
  let loggedOrigin? := Id.run do
    let mut idx := g.events.size
    while idx > 0 do
      idx := idx - 1
      match g.events[idx]!.change with
      | .rules (.cast (.proposed obj _ fz _)) =>
        if obj == spell.id then return some fz
      | .rules (.zone (.moved _ after fz .stack .cast ..)) =>
        if after.id == some spell.id then return some fz
      | _ => pure ()
    return none
  let fromZone :=
    match loggedOrigin? with
    | some fz => fz
    | none =>
      if g.castFromGraveyard spell.id then Zone.graveyard spell.owner
      else if g.castFromHand spell.id then Zone.hand spell.owner
      else Zone.exile
  let happened :=
    GameEvent.spellCast g.turnNumber caster
      { (g.snapshot spell) with manaValue := g.objectManaValue spell }
      fromZone
  let g := g.record happened
  match g.pendingFreeRGCreature with
  | some p =>
    if p == caster && g.isCreature spell &&
        ((g.colors spell).contains .red ||
          (g.colors spell).contains .green) then
      g.expireEffect (.pendingFreeRGCreatureThisTurn p) (cause := some (.gameRule .spellCast))
        |>.logMsg s!"World War Hulk's free-cast permission is used on {spell.name}"
    else g
  | none => g

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

/-- After a permanent enters, put its enters triggers and “another … enters”
triggers (CR 603.6a). -/
def afterPermanentEnters (g : Game) (o : GameObject) : Game :=
  let g := g.afterPermanentEntersInBatch o
  match g.findObject? o.id with
  | some cur =>
    if cur.isOnBattlefield && !g.enteringCausesNoTriggers cur && g.currentBatch.isNone then
      g.promptTriggerTargetsIfNeeded
    else g
  | none => g

/-- After a land enters, put its enters triggers, Elf-enters triggers, and landfall. -/
def afterLandEnters (g : Game) (land : GameObject) : Game :=
  g.afterPermanentEnters land

/-- Nick Fury power-up: put a Hero, Equipment, or Vehicle onto the battlefield.
A daybound front face enters back-face-up at night and cannot transform
(MSH 191). Otherwise it enters front-face-up; you may then transform a DFC
(MSH 192). Front-face enters abilities trigger in either case before the
optional transform. -/
def enterFromNickFury (g : Game) (controller : PlayerId) (id : ObjectId)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g.logMsg "No card to put onto the battlefield"
  | some o =>
    let nightBack := g.isNight && o.printed.daybound && o.printed.otherFace.isSome
    let (g, newId) := g.putOntoBattlefield id controller (nightBack := nightBack) (cause := cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.afterLastPermanentEnters (some id))
    else
      match g.findObject? newId with
      | some entered =>
        if !entered.isOnBattlefield then g
        else
          let g :=
            if nightBack then
              g.logMsg s!"{entered.name} enters back face up (night / daybound)"
            else g
          g.afterPermanentEnters (g.object! newId)
      | none => g

/-- Tom Bombadil is on the battlefield as a final chapter finishes resolving,
so his last ability triggers (ruling 74). -/
def finishSagaFinalChapter (g : Game) (controller : PlayerId)
    (snap : Option EventObject := none) (sourceId : Option ObjectId := none)
    (ability : Option TriggeredAbility := none) (alreadyResolved : Bool := false) : Game :=
  let g := g.logMsg "The final chapter ability is removed from the stack"
  let sagaSnap : EventObject :=
    match snap with
    | some s =>
      { s with subtypes := if s.subtypes.contains .saga then s.subtypes else s.subtypes.push .saga }
    | none =>
      { controller := some controller
        owner := controller
        zone := .stack
        subtypes := #[.saga] }
  let g :=
    if alreadyResolved then g
    else
      g.record (GameEvent.resolved g.turnNumber controller 0 sagaSnap
        (sourceId := sourceId) (ability := ability)
        (cause := some (.gameRule .abilityFinishedResolving)))
  match (g.permanentsOf controller).find? (fun o =>
    (g.baseCard o).hexproofIndestructibleIfLore.isSome) with
  | none => g
  | some tom => g.logMsg s!"{g.name tom}'s last ability triggers"

/-- Whether `host` is a legal Enchant-creature attachment (CR 303.4). -/
def isLegalAuraHost (g : Game) (host : GameObject) : Bool :=
  host.isOnBattlefield && g.isCreature host

/-- Resolve an Aura spell, attaching it (CR 303.4 / 608.3c) or putting it into
the graveyard when its target is illegal (CR 608.2b / 608.3b). -/
def resolveAuraSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let finishCause := some (EventCause.gameRule .permanentSpellResolved)
  let toGraveyard (g : Game) : Game :=
    if obj.isCopy then
      (g.ceaseToExist obj.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
        s!"{obj.name} ceases to exist (illegal Aura target, CR 704.5e)"
    else
      g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard (illegal Aura target)"
        (cause := finishCause)
  if entry.targets.isEmpty then
    -- CR 303.4f,g,i: untargeted Aura spell or copy attaches via `.asEntersAttachAura`.
    let (g, newId) := g.putOntoBattlefield obj.id entry.controller
      (verb := some .resolve) (actor := some entry.controller) (cause := finishCause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.afterLastPermanentEnters (some obj.id))
    else
      match g.findObject? newId with
      | some o =>
        if o.isOnBattlefield then
          let g :=
            match o.attachedTo.bind g.findObject? with
            | some host => g.logMsg s!"{g.name o} enters the battlefield attached to {g.name host}"
            | none => g.logMsg s!"{g.name o} enters the battlefield"
          g.afterPermanentEnters (g.object! newId)
        else g
      | none => g
  else
  match entry.targets[0]? with
  | some (Target.permanent hostId) =>
    match g.findObject? hostId with
    | some host =>
      let effCtrl := (g.controllerOf obj).getD entry.controller
      let auraAsPerm := { obj with controller := some effCtrl }
      let targetLegal :=
        entry.targets.isEmpty || g.canBeTargetedBy entry.controller host (some obj.id)
      if targetLegal && g.auraObjCanEnchant host auraAsPerm then
        let hostName := g.name host
        let (g, newId) := g.putOntoBattlefield obj.id entry.controller
          (attachedTo := some host.id) (verb := some .resolve) (actor := some entry.controller)
          (cause := finishCause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.afterLastPermanentEnters (some obj.id) (attachedToHost := some host.id))
        else
          match g.findObject? newId with
          | some o =>
            if o.isOnBattlefield then
              let g := g.logMsg s!"{g.name o} enters the battlefield attached to {hostName}"
              g.afterPermanentEnters (g.object! newId)
            else g
          | none => g
      else
        toGraveyard g
    | none => toGraveyard g
  | _ => toGraveyard g

/-- Resolve an Adventure: apply its effect, then exile the card and grant
permission to cast the permanent (CR 715.3d). A copy of an Adventure spell was
not cast as an Adventure and ceases to exist instead (CR 704.5e / 707.10). -/
def resolveAdventureSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  if obj.isCopy then
    (g.ceaseToExist obj.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
      s!"The copy of {obj.name} ceases to exist (CR 704.5e)"
  else
    let finishCause := some (EventCause.gameRule .adventureSpellResolved)
    let (g, _) := g.move obj.id .exile none
      (verb := some .resolve) (actor := some entry.controller) (cause := finishCause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep 99 entry.controller (cardId := some obj.id) (cause := finishCause))
    else
      match g.followMovedToZone? obj.id (· == .exile) with
      | some o =>
        let g := g.createEffect (.playPermission o.id {
            player := entry.controller
            fromAdventure := true })
          (cause := finishCause)
        g.logMsg
          s!"{o.name} is exiled. {(g.player entry.controller).name} may cast it for as long as it remains exiled (CR 715.3d)"
      | none => g

/-- Perform the final CR 608.2n / 608.2p / 608.3 stack-exit and `StackObjectEvent.resolved`
step for one finished `ResolutionFinish`. -/
def finishOneResolution (g : Game) (fin : ResolutionFinish) : Game :=
  match fin with
  | .ability objId snap controller sourceId sagaChapter =>
    let ab? := (g.findObject? objId).bind (·.triggeredAbility)
    let alreadyResolved := g.events.any fun e =>
      e.turn == g.turnNumber &&
        match e.change with
        | .rules (.stackObject (.resolved eo ..)) => eo.id == some objId
        | _ => false
    let g :=
      match g.findObject? objId with
      | some (cur : GameObject) =>
        if cur.zone == Zone.stack then
          g.ceaseToExist objId (cause := some (.gameRule .abilityFinishedResolving))
        else g
      | none =>
        if g.stack.any (·.objectId == objId) then
          g.change (.removeStackEntry objId)
        else g
    let finalSagaPlayer? :=
      match sagaChapter, sourceId.bind g.findObject? with
      | some n, some src =>
        match (g.baseCard src).saga, g.controllerOf src with
        | some s, some p => if n == s.finalChapterNumber then some p else none
        | _, _ => none
      | _, _ => none
    match finalSagaPlayer? with
    | some p =>
      g.finishSagaFinalChapter p (snap := some snap) (sourceId := sourceId)
        (ability := ab?) (alreadyResolved := alreadyResolved)
    | none =>
      if alreadyResolved then g
      else
        g.record (GameEvent.resolved g.turnNumber controller 0 snap
          (sourceId := sourceId) (ability := ab?)
          (cause := some (.gameRule .abilityFinishedResolving)))
  | .spell entry snap fromGy =>
    match g.findObject? entry.objectId with
    | none =>
      let g :=
        if g.stack.any (·.objectId == entry.objectId) then
          g.change (.removeStackEntry entry.objectId)
        else g
      g.record (GameEvent.resolved g.turnNumber entry.controller 0 snap
        (cause := some (.gameRule .instantOrSorceryFinishedResolving)))
    | some (obj : GameObject) =>
      if obj.zone != Zone.stack then
        let g :=
          if g.stack.any (·.objectId == entry.objectId) then
            g.change (.removeStackEntry entry.objectId)
          else g
        g.record (GameEvent.resolved g.turnNumber entry.controller 0 snap
          (cause := some (.gameRule .instantOrSorceryFinishedResolving)))
      else
        let finishCause : EventCause :=
          if obj.isAdventureSpell && !obj.isCopy then .gameRule .adventureSpellResolved
          else if g.isAura obj || (g.isPermanentCard obj && !g.isLand obj) then
            .gameRule .permanentSpellResolved
          else .gameRule .instantOrSorceryFinishedResolving
        let hasFlashback :=
          GameEvent.castWithFlashback g.events obj.id || g.flashbackUntilEot obj ||
            (fromGy && !g.freeCastFromGraveyard obj &&
              ((g.baseCard obj).flashback.isSome || g.hasFlashbackPermission obj))
        let g :=
          if obj.isAdventureSpell then
            g.resolveAdventureSpell entry obj
          else if g.isAura obj then
            g.resolveAuraSpell entry obj
          else if g.isPermanentCard obj && !g.isLand obj then
            let sneak := g.sneakPaid obj.id
            let sneakWhom := g.sneakAttackWhom? obj.id
            let sneakTarget :=
              if sneak then
                (g.sneakAttackTarget? obj.id).orElse (fun _ => sneakWhom.map AttackTarget.player)
              else none
            let (g, newId) := g.putOntoBattlefield obj.id entry.controller
              (tapped := sneak)
              (attacking := sneak)
              (attackingTarget := sneakTarget)
              (verb := some .resolve)
              (actor := some entry.controller)
              (cause := some finishCause)
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.afterLastPermanentEnters (some obj.id))
            else
              match g.findObject? newId with
              | some o =>
                if o.isOnBattlefield then
                  let g :=
                    match o.attachedTo.bind g.findObject? with
                    | some host => g.logMsg s!"{g.name o} enters the battlefield attached to {g.name host}"
                    | none => g.logMsg s!"{o.name} enters the battlefield"
                  g.afterPermanentEnters (g.object! newId)
                else g
              | none => g
          else if obj.isCopy then
            (g.ceaseToExist obj.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
              s!"The copy of {obj.name} ceases to exist (CR 704.5e)"
          else if hasFlashback then
            let (g, _) := g.move obj.id .exile none
              (verb := some .resolve) (actor := some entry.controller) (cause := some finishCause)
            g.logMsg s!"{obj.name} is exiled (flashback)"
          else
            g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard"
              (verb := some .resolve) (actor := some entry.controller) (cause := some finishCause)
        if g.pending == .none && g.afterRandom == .none then
          g.record (GameEvent.resolved g.turnNumber entry.controller 0 snap
            (cause := some finishCause))
        else
          g.change (.pendingResolvedEvent (some (snap, entry.controller, finishCause)))

/-- Drain completed `ContinuationFrame`s once all `Pending`, `afterRandom`, and
batch continuations have finished, running deferred CR 608.2n / 608.2p / 608.3
stack-exit actions and popping frames back to `#[]`. -/
partial def completeActiveResolutions (g : Game) : Game :=
  if !g.over && (g.pending != .none || g.afterRandom != .none || g.currentBatch.isSome ||
      g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
      g.triggerSequenceRest.isSome) then g
  else
    match g.continuations.back? with
    | none => if g.over then g else g.promptTriggerTargetsIfNeeded
    | some top =>
      if g.over then
        -- Game ended during resolution (CR 104.1): clean up any resolving stack
        -- entry and drain `g.continuations` without running further game actions.
        let g :=
          match top.resolutionFinish with
          | some (.ability objId ..) =>
            let g :=
              if g.stack.any (·.objectId == objId) then
                g.change (.removeStackEntry objId)
              else g
            match g.findObject? objId with
            | some (o : GameObject) =>
              if o.zone == Zone.stack then g.ceaseToExist objId (cause := some (.gameRule .abilityFinishedResolving))
              else g
            | none => g
          | some (.spell entry ..) =>
            if g.stack.any (·.objectId == entry.objectId) then
              g.change (.removeStackEntry entry.objectId)
            else g
          | none => g
        completeActiveResolutions (g.change .popContinuationFrame)
      else if let some (snap, ctrl, fc) := top.pendingResolvedEvent then
        let g := (g.change (.pendingResolvedEvent none)).record
          (GameEvent.resolved g.turnNumber ctrl 0 snap (cause := some fc))
        completeActiveResolutions (g.change .popContinuationFrame)
      else if let some fin := top.resolutionFinish then
        let g := g.changes #[
          .resolutionFinish none,
          .resolvingSpell none,
          .resolvingAbility none,
          .resolvingDivision #[]]
        let g := g.finishOneResolution fin
        if g.pending != .none || g.afterRandom != .none || g.currentBatch.isSome then g
        else completeActiveResolutions (g.change .popContinuationFrame)
      else
        completeActiveResolutions (g.change .popContinuationFrame)

/-- CR 704.3 / 603.3b: finish any completed active resolutions, check state-based
actions, then put waiting triggers on the stack in APNAP order (each player
choosing the order of their own). After that batch, check state-based actions
again. Repeat until idle, then `p` receives priority. `recheckSba` is false
while still placing the current batch (targets or the next player's triggers). -/
partial def receivePriority (g : Game) (p : PlayerId) (recheckSba := true) : Game :=
  let p := g.priorityInstead p
  let savePendingP (g : Game) : Game :=
    if g.pendingPriority == some p then g else g.change (.pendingPriority (some p))
  let hadEntryPending := g.pending != .none
  let g :=
    if g.pending == .none && g.afterRandom == .none then
      g.completeActiveResolutions
    else g
  if g.over then g
  else if g.legendChoicePending? then
    if hadEntryPending then g else savePendingP g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.receivePriority p)
  else if g.pending != .none then
    if hadEntryPending then g else savePendingP g
  else
    let g := if recheckSba then g.checkSBA else g
    if g.over then g
    -- CR 704.3 / 704.5j: a required legend-rule choice is part of performing
    -- the SBA. Do not put triggers on the stack or grant priority yet.
    else if g.legendChoicePending? then savePendingP g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.receivePriority p)
    else if g.pending != .none then savePendingP g
    else
      match g.nextTriggerStackingPlayer? with
      | none =>
        if g.waitingTriggers.isEmpty then
          if recheckSba then
            if g.pendingPriority.isSome then
              g.changes #[.priority p, .consecutivePasses 0, .pendingPriority none]
            else
              g.changes #[.priority p, .consecutivePasses 0]
          else
            -- Finished this CR 603.3b pass; check SBAs and any new triggers.
            receivePriority g p true
        else
          let g := g.putTriggerBatch g.currentTriggerBatch
          if g.over then g
          else if g.pending != .none then savePendingP g
          else receivePriority g p true
      | some q =>
        let mine := g.waitingTriggersOf q
        let allIdentical :=
          mine.size ≤ 1 ||
            mine.all (fun w =>
              w.source.id == mine[0]!.source.id &&
                w.ability == mine[0]!.ability &&
                w.event == mine[0]!.event &&
                w.causeId == mine[0]!.causeId &&
                w.causeIds == mine[0]!.causeIds &&
                w.causeController == mine[0]!.causeController &&
                w.lastKnownPower == mine[0]!.lastKnownPower &&
                w.lastKnownToughness == mine[0]!.lastKnownToughness &&
                w.delayedTrigger == mine[0]!.delayedTrigger &&
                w.abilityEffect == mine[0]!.abilityEffect &&
                w.reflexiveResolution == mine[0]!.reflexiveResolution)
        if allIdentical || mine.all (·.ordered) then
          let g := g.putTriggerBatch mine
          if g.over then g
          else if g.pending != .none then savePendingP g
          else receivePriority g p false
        else
          let g := savePendingP g
          (g.change (.pending (.chooseTriggerToStack q))).logMsg
            s!"{(g.player q).name} chooses the order of triggered abilities (CR 603.3b)"

/-- Emit the post-`recordPutCounters` log for `oid` from its counter delta
since `before` (`0 = stun`, `1 = loyalty`, `2 = doubleStrike`, `3 = charge`,
`4 = quest`, `5 = hone`, `6 = invasion`, `7 = trample`, `8 = loyalty cost`,
`9 = player puts stun`, `10 = minusOneMinusOne`, `11 = story`, `12 = received hone`,
`20..30 = keyword counter`). -/
def logPutCounterDelta (g : Game) (oid : ObjectId) (before : Nat) (kindTag : Nat)
    (byPlayer : Option PlayerId := none) (name : String := "") : Game :=
  match g.findObject? oid with
  | none => g
  | some o =>
    match kindTag with
    | 0 =>
      let k := o.status.stun - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "A stun counter is put" else s!"{k} stun counters are put"
        g.logMsg s!"{phrase} on {g.name o}"
    | 1 =>
      let k := o.status.counterCount .loyalty - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "A loyalty counter is put" else s!"{k} loyalty counters are put"
        g.logMsg s!"{phrase} on {g.name o}"
    | 2 =>
      let k := o.status.counterCount .doubleStrike - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "a double strike counter" else s!"{k} double strike counters"
        g.logMsg s!"{g.name o} gets {phrase}"
    | 3 =>
      let k := o.status.counterCount .charge - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "A charge counter is put" else s!"{k} charge counters are put"
        g.logMsg s!"{phrase} on {g.name o}"
    | 4 =>
      let k := o.status.quest - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "a quest counter" else s!"{k} quest counters"
        g.logMsg s!"{g.name o} gets {phrase} ({o.status.quest})"
    | 5 =>
      let k := o.status.hone - before
      if k == 0 then g
      else g.logMsg s!"{g.name o} gets {k} hone counter(s)"
    | 6 =>
      let k := o.status.counterCount .invasion - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "an invasion counter" else s!"{k} invasion counters"
        g.logMsg s!"{g.name o} gets {phrase}"
    | 7 =>
      let k := o.status.counterCount .trample - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "a trample counter" else s!"{k} trample counters"
        g.logMsg s!"{g.name o} gets {phrase}"
    | 8 =>
      let k := o.status.counterCount .loyalty - before
      if k == 0 then g
      else g.logMsg s!"{k} loyalty counter(s) are put on {g.name o}"
    | 9 =>
      let k := o.status.stun - before
      if k == 0 then g
      else
        let pName := (g.player (byPlayer.getD g.activePlayer)).name
        let phrase := if k == 1 then "a stun counter" else s!"{k} stun counters"
        g.logMsg s!"{pName} puts {phrase} on {g.name o}"
    | 10 =>
      let k := o.status.minusOneMinusOne - before
      if k == 0 then g
      else g.logMsg s!"{k} -1/-1 counter(s) are put on {g.name o}"
    | 11 =>
      let k := o.status.story - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "a story counter" else s!"{k} story counters"
        g.logMsg s!"{g.name o} gets {phrase}"
    | 12 =>
      let k := o.status.hone - before
      if k == 0 then g
      else
        let phrase := if k == 1 then "a hone counter" else s!"{k} hone counters"
        g.logMsg s!"{g.name o} received {phrase}"
    | tag =>
      let kwKind? : Option CounterKind :=
        match tag with
        | 20 => some .haste
        | 21 => some .flying
        | 22 => some .firstStrike
        | 23 => some .doubleStrike
        | 24 => some .deathtouch
        | 25 => some .indestructible
        | 26 => some .lifelink
        | 27 => some .menace
        | 28 => some .reach
        | 29 => some .trample
        | 30 => some .vigilance
        | _ => none
      match kwKind? with
      | some kind =>
        let k := o.status.counterCount kind - before
        if k == 0 then g
        else
          let phrase := if k == 1 then s!"a {name} counter" else s!"{k} {name} counters"
          g.logMsg s!"{g.name o} gets {phrase}"
      | none => g

/-- Run `recordPutCounters` on `oid` and emit `logPutCounterDelta` synchronously
or defer via `.finishPostStep 82` when `Pending.chooseReplacement` opened. -/
def putCountersDeferredLog (g : Game) (oid : ObjectId) (kind : CounterKind)
    (n : Nat) (byPlayer : Option PlayerId) (kindTag : Nat)
    (cause : Option EventCause := none) (name : String := "") : Game :=
  let before := ((g.findObject? oid).map (·.status.counterCount kind)).getD 0
  let g := g.recordPutCounters oid kind n (byPlayer := byPlayer) (cause := cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep 82 (byPlayer.getD g.activePlayer) (n := before)
        (cardId := some oid) (modes := #[kindTag]) (name := name))
  else
    g.logPutCounterDelta oid before kindTag (byPlayer := byPlayer) (name := name)

end Game
end Mtg.Engine
