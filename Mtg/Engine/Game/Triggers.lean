import Mtg.Engine.Game.Targeting

/-!
# Triggered abilities onto the stack (CR 603.3)

Putting triggered abilities on the stack, intervening-if conditions
(CR 603.4), extra trigger copies, Saga lore counters (CR 714.3),
battlefield folds and controlled-trigger helpers, `becomeTapped`
(CR 603.6d), activated- and mana-ability lookups, waiting-trigger
batches stacked in APNAP order (CR 603.3b), and `receivePriority`.
-/

namespace Mtg.Engine
namespace Game

/-- Modes of a modal triggered ability (“choose one —”) printed outside
Reality Fracture (CR 700.2). -/
def sharedTriggerModes (ab : TriggeredAbility) : Array Effect :=
  match ab.shared with
  | .tapOppOrUntapYours =>
    #[{ targeting := .of .oppCreature, resolution := .onPermanent .tap
        phrase := "Tap target creature an opponent controls" },
      { targeting := .of .creatureYouControl, resolution := .onPermanent .untap
        phrase := "Untap target creature you control" }]
  | .wolfPlusOneOrTreasure =>
    #[{ targeting := .of (.creatureYouControlAnySubtype #[.wolf])
        resolution := .onPermanent (.plusOne 1)
        phrase := "Put a +1/+1 counter on target Wolf you control" },
      { resolution := .createTokens .treasure 1
        phrase := "Create a Treasure token" }]
  | .enter .plusOnesOrReturnArtEnch =>
    #[{ targeting := .of .creature, allowsZeroTargets := true, maxTargets := 2,
        resolution := .plusOneOnEachTarget 1,
        phrase := "Put a +1/+1 counter on each of up to two target creatures" },
      { targeting := .of .artEnchCardInYourGraveyard,
        resolution := .returnFromGyToHand,
        phrase := "Return target artifact or enchantment card from your graveyard to your hand" }]
  | .watch .nontokenHeroModal =>
    #[{ resolution := .createTokens .soldier11white 1
        phrase := "Create a 1/1 white Soldier creature token" },
      { resolution := .creaturesYouControlPump 1 1
        phrase := "Creatures you control get +1/+1 until end of turn" }]
  | _ => #[]

/-- Modes of the triggered ability `obj` (from its source). -/
def triggerModesOf (g : Game) (obj : GameObject) : Array Effect :=
  let fra :=
    match obj.sourceId.bind g.findObject? with
    | some src => (g.baseCard src).fraTriggerModes
    | none => (g.baseCard obj).fraTriggerModes
  if !fra.isEmpty then fra
  else (obj.triggeredAbility.map sharedTriggerModes).getD #[]

/-- Whether `p` may choose this mode of a triggered ability (CR 700.2d). -/
def triggerModeChoosable (g : Game) (p : PlayerId) (obj : GameObject) (e : Effect) : Bool :=
  !e.requiresTarget || e.allowsZeroTargets ||
    !(g.legalTargetsForKind p e.targetKind obj.sourceId).isEmpty

/-- Ask for the modes of a modal triggered ability just put on the stack. -/
def beginTriggerModeChoice (g : Game) (p : PlayerId) (obj : GameObject) (count : Nat) : Game :=
  let modes := g.triggerModesOf obj
  if !modes.any (g.triggerModeChoosable p obj) then
    let g := g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
    g.logMsg s!"{obj.name} has no mode that can be chosen and is removed from the stack (CR 700.2d)"
  else
    let what := if count == 2 then "two modes" else "a mode"
    (g.change (.pending (.fraChoice p (.triggerModes obj.id count #[])))).logMsg
      s!"{(g.player p).name} chooses {what} for {obj.name} (CR 603.3c)"

/-- Put a triggered ability of `source` onto the stack (CR 603.3). A modal
ability's modes are chosen as it is put on the stack (CR 603.3c). -/
def putTriggeredAbilityOnStack (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) (cause : Option GameObject := none)
    (causeController : Option PlayerId := none)
    (eventCause : Option EventCause := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none) : Game :=
  if (g.player controller).lost then g
  else
    let (g, obj) := g.putStackAbility source controller
      (triggeredAbility := some ab)
      (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)
      (delayedTrigger := delayedTrigger)
    -- “For each opponent, up to one target … that player controls”: one
    -- optional instance per opponent (CR 601.2c).
    let abilityEffect :=
      match ab.effect.targetKind with
      | .filtered f =>
        if f.controller == .eachOpponent then
          let fs := (g.livingOpponents controller).map (fun pl =>
            { f with controller := .specific pl.id.idx })
          some { ab.effect with
            targeting := .of (.multi fs ((List.range fs.size).toArray)) }
        else none
      | _ => none
    let g := g.changeObjects obj.id #[
      .fraCauseId (cause.map (·.id)),
      .fraCauseController (causeController.orElse (fun _ => cause.bind g.controllerOf)),
      .fraCausePower (cause.bind (fun c =>
        if (g.findObject? c.id).any (·.isOnBattlefield) then some (g.power (g.object! c.id))
        else (g.lastKnownPowerOf? c.id).orElse (fun _ => some (g.power c)))),
      .fraCauseStatus (cause.map (·.status)),
      .abilityEffect abilityEffect]
    let obj := g.object! obj.id
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber obj.id source.asEvent controller
      (cause := eventCause))
    let g := g.logMsg s!"{g.name source}'s {event} is put on the stack"
    match ab.effect.resolution with
    | .chooseTriggerModes n => g.beginTriggerModeChoice controller obj n
    | _ => if (sharedTriggerModes ab).isEmpty then g else g.beginTriggerModeChoice controller obj 1

/-- True when this trigger would be put on the stack with no legal target (CR 603.3d). -/
def triggerHasNoLegalTarget (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : ObjectId) : Bool :=
  ab.requiresTarget && !ab.allowsZeroTargets &&
    (g.legalTriggerTargets controller ab (some sourceId)).isEmpty

/-- Put `ab` on the stack, or log that it is removed for lack of a target (CR 603.3d). -/
def putTriggerOrFizzle (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (causeController : Option PlayerId := none)
    (eventCause : Option EventCause := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none) : Game :=
  if g.triggerHasNoLegalTarget controller ab source.id then
    g.logMsg
      s!"{g.name source}'s {event} is removed from the stack (no legal target) (CR 603.3d)"
  else
    g.putTriggeredAbilityOnStack controller source ab event lastKnownPower lastKnownToughness
      (cause := cause) (causeController := causeController) (eventCause := eventCause)
      (delayedTrigger := delayedTrigger)

/-- Put `ab` on the stack for `event`, using that event's spec for the log label
and CR 603.3d check so a new event is not restated at every queue site. -/
def putQueuedTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (causeController : Option PlayerId := none)
    (eventCause : Option EventCause := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none) : Game :=
  if (g.player controller).lost then g
  else if !g.triggerConditionHolds controller ab cause (some source) then g
  else if event.checkTargets then
    g.putTriggerOrFizzle controller source ab event.label lastKnownPower lastKnownToughness
      (cause := cause) (causeController := causeController) (eventCause := eventCause)
      (delayedTrigger := delayedTrigger)
  else
    g.putTriggeredAbilityOnStack controller source ab event.label
      lastKnownPower lastKnownToughness (cause := cause) (causeController := causeController)
      (eventCause := eventCause) (delayedTrigger := delayedTrigger)

/-- Queue `ab` until a player would receive priority (CR 603.3 / 603.4). The
intervening condition is checked when the event occurs. -/
def queueTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (causeController : Option PlayerId := none)
    (eventCause : Option EventCause := none) : Game :=
  if (g.player controller).lost then g
  else if !g.triggerConditionHolds controller ab cause (some source) then g
  else if ab.onceEachTurn && g.loggedTriggeredThisTurn source.id ab then g
  else if ab.optionalOnceEachTurn && g.optionalOnceUsedThisTurn source.id then g
  else
    let attackEvent :=
      match event with
      | .attacking => true
      | .fra fe =>
        match fe with
        | .creatureYouControlAttacks | .creatureYouControlAttacksPlayerAlone
        | .zombieTokenAttacks | .sphinxesAttack => true
        | _ => false
      | _ => false
    let mardu :=
      if attackEvent && (g.permanentsOf controller).any (fun o =>
          (g.baseCard o).asEntersChooseMarduOrJeskai && g.retainsPrintedAbilities o &&
            o.status.windcragMardu) then 1 else 0
    let copies := g.extraTriggerCopies controller source + 1 + mardu
    let wt : WaitingTrigger := {
      controller, source, ability := ab, event, lastKnownPower, lastKnownToughness,
      causeId := cause.map (·.id), cause, causeController, checked := true, eventCause }
    let originBatch :=
      match g.currentBatch with
      | some (bid, _) => bid
      | none => ⟨g.nextBatchId⟩
    let trigEv :=
      GameEvent.triggered g.turnNumber (g.snapshot source) controller ab originBatch
    Id.run do
      let mut g := g
      for _ in [0:copies] do
        g := { g with events := g.events.push trigEv }
        g := g.enqueueWaitingTriggers #[wt]
      return g

/-- Put exactly one lore counter on `saga` and queue that chapter. -/
def addOneLoreRaw (g : Game) (saga : GameObject) : Game :=
  match g.controllerOf saga, (g.baseCard saga).saga with
  | some p, some _ =>
    match g.findObject? saga.id with
    | none => g
    | some saga =>
      if !saga.isOnBattlefield then g
      else
        let lore := saga.status.lore + 1
        let sagaName := g.name saga
        let g := g.record (GameEvent.counters g.turnNumber (some p) (g.snapshot saga) .lore 1
          (cause := some (.turnBased .sagaLoreOnMain)))
        g.logMsg s!"{sagaName} gets a lore counter ({lore})"
  | _, _ => g

/-- Add `n` lore counters one at a time, plus one per Doc Samson the
controller has (CR 714.3c / MSH 517). -/
def addLoreCounters (g : Game) (saga : GameObject) (n : Nat) : Game :=
  let n := g.countersYouPut saga n
  Id.run do
    let mut g := g
    for _ in [0:n] do
      match g.findObject? saga.id with
      | some o => g := g.addOneLoreRaw o
      | none => pure ()
    return g

/-- Put one lore counter on `saga` and queue the matching chapter abilities
(CR 714.2 / 714.3). Counters are added one at a time. -/
def addOneLoreCounter (g : Game) (saga : GameObject) : Game :=
  g.addLoreCounters saga 1

/-- As a Saga enters, put a lore counter on it (CR 714.3a). The lore counter(s)
are placed in `entersWith` during the zone change, so we log the lore
counter(s) on `o`. -/
def addLoreAsSagaEnters (g : Game) (o : GameObject) : Game :=
  match g.controllerOf o, (g.baseCard o).saga with
  | some _, some _ =>
    if o.status.faceDown || o.status.lore == 0 then g
    else
      let oName := g.name o
      Id.run do
        let mut g := g
        for i in [0:o.status.lore] do
          let lore := i + 1
          g := g.logMsg s!"{oName} gets a lore counter ({lore})"
        return g
  | _, _ => g

/-- After the draw step / as first main begins, add a lore counter to each
Saga the active player controls (CR 714.3b). -/
def addLoreAfterDrawStep (g : Game) : Game :=
  (g.permanentsOf g.activePlayer).foldl (fun acc o =>
    if (acc.baseCard o).saga.isSome then acc.addOneLoreCounter o else acc) g

/-- Queue each printed trigger of `source` that fires on `event` (CR 603.3). -/
def putMatchingSourceTriggers (g : Game) (controller : PlayerId) (source : GameObject)
    (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (keep : TriggeredAbility → Bool := fun _ => true) : Game :=
  Id.run do
    let mut g := g
    for ab in (g.matchingTriggers source event ++
        (g.prowessTriggers source).filter (·.firesOn event)).filter keep do
      let skipInfinity :=
        match ab.shared with
        | .step .harnessedFlicker => !source.status.harnessed
        | _ => false
      if !skipInfinity then
        g := g.queueTrigger controller source ab event lastKnownPower lastKnownToughness
          cause
    return g

/-- Apply `f` to each battlefield permanent matching `pred`. -/
def foldBattlefield (g : Game) (pred : GameObject → Bool)
    (f : Game → GameObject → Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if pred o then
        g := f g o
    return g

/-- Apply `f` to each battlefield permanent `p` controls, optionally skipping one id. -/
def foldControlledPermanents (g : Game) (p : PlayerId)
    (excludeId : Option ObjectId := none) (f : Game → GameObject → Game) : Game :=
  g.foldBattlefield (fun o => g.controlledBy o p && excludeId != some o.id) f

/-- Tap an untapped permanent and queue becomes-tapped triggers (CR 603.6d).
Entering the battlefield tapped is not becoming tapped; only a change from
untapped to tapped fires these abilities (Hawkeye's Bow, Trick Arrows,
Captain America, Living Legend). -/
def becomeTapped (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  let oName := g.name o
  if o.status.tapped then
    g.logMsg s!"{oName} is already tapped"
  else
    let during :=
      match g.controllerOf o with
      | some p => g.activePlayer == p
      | none => false
    let happened := GameEvent.tapped g.turnNumber (g.snapshot o) true during (cause := cause)
    (g.record happened).logMsg s!"{oName} becomes tapped"

/-- Apply `f` to each creature `p` controls, optionally skipping one id. -/
def forEachControlledCreature (g : Game) (p : PlayerId)
    (f : Game → GameObject → Game) (excludeId : Option ObjectId := none) : Game :=
  g.withBatch none fun g =>
    g.foldControlledPermanents p excludeId fun g o =>
      if g.isCreature o then f g o else g

/-- Put matching triggers of permanents `p` controls that fire on `event`.
`cause` is the object that made them trigger, when there is one. -/
def putControlledTriggers (g : Game) (p : PlayerId)
    (event : TriggerEvent) (excludeId : Option ObjectId := none)
    (cause : Option GameObject := none)
    (lastKnownPower : Option Int := none) : Game :=
  let g := g.foldControlledPermanents p excludeId fun g o =>
    g.putMatchingSourceTriggers p o event (lastKnownPower := lastKnownPower) (cause := cause)
  -- Emblems in the command zone trigger too (CR 114.4).
  (g.objects.filter (fun o => o.zone == .command && g.controlledBy o p)).foldl
    (fun g e => g.putMatchingSourceTriggers p e event
      (lastKnownPower := lastKnownPower) (cause := cause)) g

/-- Sacrifice `o` to its owner's graveyard (CR 701.21a). -/
def sacrificeToGraveyard (g : Game) (o : GameObject) (reason : String)
    (cause : Option EventCause := none) : Game :=
  let actor := (g.controllerOf o).getD o.owner
  g.moveToOwnerGraveyard o reason (verb := some .sacrifice) (actor := some actor)
    (cause := cause)

/-- Mana types Reality Fracture mana abilities of `o` produce, including the
`{T}: Add {C}{C}` Emrakul, the Exigent Doom grants a land. -/
def fraManaAbilities (g : Game) (o : GameObject) : Array ManaType :=
  let anyColor : Array ManaType :=
    #[.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
  let own := (g.staticAbilities o).foldl (fun acc ab =>
    match ab with
    | .fra .tapAddColorlessNotFromHand => acc.push .colorless
    | .fra .tapAddAnyColorPlaneswalkerOnly => acc ++ anyColor
    | .fra .tapSacrificeAddThreeOfOneColor => acc ++ anyColor
    | .fra .tapAddChosenColor =>
      match o.status.chosenColor with
      | some c => acc.push (.colored c)
      | none => acc
    | _ => acc) #[]
  if g.hasActiveColorlessGrant o && !own.contains .colorless then
    own.push .colorless
  else own

/-- The spending restriction on mana `o` adds when tapped for `mana`. -/
def fraManaUseOf (g : Game) (o : GameObject) (mana : ManaType) : Option FraManaUse :=
  if mana == .colorless && g.hasActiveColorlessGrant o then none
  else
    match (g.staticAbilities o).findSome? (fun ab =>
        match ab with
        | .fra s => s.manaUse?
        | _ => none) with
    | some u => some u
    | none => if g.hasSubtype o .treasure then some .fromTreasure else none

/-- If a stacked triggered ability still needs targets, prompt its controller
(CR 603.3d / 601.2c). -/
def promptTriggerTargetsIfNeeded (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some e =>
    if g.pending == .chooseTargets e.controller then g
    else if (match g.pending with | .fraChoice .. => true | _ => false) then g
    else
      let msg :=
        match (g.findObject? e.objectId).bind (fun o =>
            o.triggeredAbility.bind TriggeredAbility.dividedDamage?) with
        | some (n, maxTargets) =>
          s!"{(g.player e.controller).name} must divide {n} damage among one to {maxTargets} targets (CR 603.3d / 601.2d)"
        | none =>
          s!"{(g.player e.controller).name} must choose a target (CR 603.3d / 601.2c)"
      (g.change (.pending (.chooseTargets e.controller))).logMsg msg
  | none => g

/-- Triggers waiting to be put on the stack for `event`. -/
def waitingFor (g : Game) (event : TriggerEvent) : Array WaitingTrigger :=
  g.waitingTriggers.filter (·.event == event)

/-- CR 603.3b: part 1 is every waiting trigger whose condition is not another
ability triggering; part 2 is the remainder. -/
def waitingTriggersPart (g : Game) (part2 : Bool) : Array WaitingTrigger :=
  g.waitingTriggers.filter (fun wt => wt.event.isAnotherAbilityTriggering == part2)

/-- The current CR 603.3b batch: part 1 if any remain, otherwise part 2. -/
def currentTriggerBatch (g : Game) : Array WaitingTrigger :=
  let part1 := g.waitingTriggersPart false
  if !part1.isEmpty then part1 else g.waitingTriggersPart true

/-- This player's waiting triggers in the current CR 603.3b part. -/
def waitingTriggersOf (g : Game) (p : PlayerId) : Array WaitingTrigger :=
  g.currentTriggerBatch.filter (·.controller == p)

/-- Source ids of `p`'s current batch, oldest first (the default order). -/
def defaultTriggerSourceIds (g : Game) (p : PlayerId) : Array ObjectId :=
  (g.waitingTriggersOf p).map (·.source.id)

/-- Next player in APNAP order who has a waiting trigger in this part
(CR 603.3b / 101.4). -/
def nextTriggerStackingPlayer? (g : Game) : Option PlayerId :=
  let batch := g.currentTriggerBatch
  g.apnapPlayers.find? (fun p => batch.any (·.controller == p))

/-- Remove `wt` from the waiting list. -/
def removeWaitingTrigger (g : Game) (wt : WaitingTrigger) : Game :=
  match g.waitingTriggers.findIdx? (fun w =>
    w.controller == wt.controller && w.source.id == wt.source.id &&
      w.ability == wt.ability && w.event == wt.event &&
      w.causeId == wt.causeId && w.delayedTrigger == wt.delayedTrigger) with
  | none => g
  | some i => g.change (.waitingTriggers (g.waitingTriggers.eraseIdx! i))

/-- Last-known power, or the causing object's id for Baron Strucker's optional
connive (MSH 422). -/
def lastKnownPowerForTrigger (ab : TriggeredAbility) (lastKnownPower : Option Int)
    (causeId : Option ObjectId) : Option Int :=
  match ab.shared, causeId with
  | .watch .villainConniveOnce, some id => some (Int.ofNat id.raw)
  | .pumpIfFiveOtherForests, some id => some (Int.ofNat id.raw)
  | _, _ => lastKnownPower

/-- Put one waiting trigger on the stack. A trigger queued without
`queueTrigger` is checked here for “only once each turn” (CR 603.2h) and
gets its extra copies (Chief of the Wilds, Bifur). -/
def putWaitingTrigger (g : Game) (wt : WaitingTrigger) (event : TriggerEvent) : Game :=
  let put (g : Game) :=
    g.putQueuedTrigger wt.controller wt.source wt.ability event
      (lastKnownPowerForTrigger wt.ability wt.lastKnownPower wt.causeId)
      wt.lastKnownToughness (cause := wt.cause) (causeController := wt.causeController)
      (eventCause := wt.eventCause) (delayedTrigger := wt.delayedTrigger)
  if wt.checked then put g
  else
    if wt.ability.onceEachTurn && g.loggedTriggeredThisTurn wt.source.id wt.ability then g
    else if wt.ability.optionalOnceEachTurn && g.optionalOnceUsedThisTurn wt.source.id then g
    else if !g.triggerConditionHolds wt.controller wt.ability wt.cause (some wt.source) then g
    else
      let originBatch :=
        match g.currentBatch with
        | some (bid, _) => bid
        | none => ⟨g.nextBatchId⟩
      let trigEv :=
        GameEvent.triggered g.turnNumber (g.snapshot wt.source) wt.controller wt.ability originBatch
      let copies := g.extraTriggerCopies wt.controller wt.source + 1
      (List.range copies).foldl (fun g _ =>
        let g :=
          if g.loggedTriggeredThisTurn wt.source.id wt.ability then g
          else { g with events := g.events.push trigEv }
        put g) g

/-- Put these waiting triggers on the stack in the given order (CR 603.3 / 603.3d). -/
def putTriggerBatch (g : Game) (wts : Array WaitingTrigger) : Game :=
  if wts.isEmpty then g
  else
    Id.run do
      let mut g := g
      for wt in wts do
        g := g.removeWaitingTrigger wt
        g := g.putWaitingTrigger wt wt.event
      return g.promptTriggerTargetsIfNeeded

/-- Put queued triggers for `event` onto the stack (CR 603.3). The event spec
decides the log label and whether to remove abilities that require a target
and have none (CR 603.3d). -/
def flushWaitingTriggers (g : Game) (event : TriggerEvent) : Game :=
  let waiting := g.waitingFor event
  if waiting.isEmpty then g
  else
    Id.run do
      let mut g := g.change (.removeWaitingTriggersForEvent event)
      for wt in waiting do
        g := g.putWaitingTrigger wt event
      return g.promptTriggerTargetsIfNeeded

/-- CR 704.3 / 603.3b: check state-based actions, then put waiting triggers
on the stack in APNAP order (each player choosing the order of their own).
After that batch, check state-based actions again. Repeat until idle, then
`p` receives priority. `recheckSba` is false while still placing the current
batch (targets or the next player's triggers). -/
partial def receivePriority (g : Game) (p : PlayerId) (recheckSba := true) : Game :=
  let g :=
    if g.pending == .none && g.afterRandom == .none && g.continuations.size > 1 then
      g.change .popContinuationFrame
    else g
  let p := g.priorityInstead p
  let g := if recheckSba then g.checkSBA else g
  if g.over then g
  -- CR 704.3 / 704.5j: a required legend-rule choice is part of performing
  -- the SBA. Do not put triggers on the stack or grant priority yet.
  else if g.legendChoicePending? then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.receivePriority p)
  else if g.pending != .none then g
  else
    match g.nextTriggerStackingPlayer? with
    | none =>
      if g.waitingTriggers.isEmpty then
        if recheckSba then
          g.changes #[.priority p, .consecutivePasses 0]
        else
          -- Finished this CR 603.3b pass; check SBAs and any new triggers.
          receivePriority g p true
      else
        let g := g.putTriggerBatch g.currentTriggerBatch
        if g.over || g.pending != .none then g
        else receivePriority g p true
    | some q =>
      let mine := g.waitingTriggersOf q
      if (mine.filter (·.delayedTrigger.isNone)).size ≤ 1 then
        let g := g.putTriggerBatch mine
        if g.over || g.pending != .none then g
        else receivePriority g p false
      else
        (g.change (.pending (.chooseTriggerToStack q))).logMsg
          s!"{(g.player q).name} chooses the order of triggered abilities (CR 603.3b)"

/-- Start scrying `n` as a keyword action (CR 701.22).
Scry 0 is skipped and does not trigger “whenever you scry” (CR 701.22c). -/
def beginScry (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  let count := min n pl.library.size
  if n == 0 then
    g.logMsg s!"{pl.name} scries {n} (no cards to look at)"
  else if count == 0 then
    let happened :=
      GameEvent.looked g.turnNumber p 0 false n (cause := g.resolvingOneShotCause p)
    let g := g.record happened
    g.logMsg s!"{pl.name} scries {n} (no cards to look at)"
  else
    (g.changes #[.pending (.scry p count n), .surveilReturnMvAtMost none]).logMsg s!"{pl.name} scries {n}"

/-- Scry `scryN`, then draw `drawN`. An empty library draws immediately.
The draw waits on `pendingDrawAfterScry` while the scry choice is open. -/
def scryThenDraw (g : Game) (p : PlayerId) (scryN drawN : Nat) : Game :=
  let g := g.change (.pendingDrawAfterScry (some (p, drawN)))
  let g := g.beginScry p scryN
  if g.pendingDrawAfterScry.isSome &&
      (match g.pending with | .scry .. => false | _ => true) then
    let g := g.change (.pendingDrawAfterScry none)
    g.draw p drawN
  else g

end Game
end Mtg.Engine
