import Mtg.Engine.Game.Targeting

/-!
# Triggered abilities onto the stack (CR 603.3)

Putting triggered abilities on the stack, intervening-if conditions
(CR 603.4), extra trigger copies, Saga lore counters (CR 715.3a / 715.3c),
battlefield folds, `becomeTapped` (CR 603.2e), activated- and mana-ability
lookups, waiting-trigger batches stacked in APNAP order (CR 603.3b), and
`receivePriority`.
-/

namespace Mtg.Engine
namespace Game

/-- Modes of the triggered ability `obj` (from its source). -/
def triggerModesOf (g : Game) (obj : GameObject) : Array Effect :=
  let src? := obj.sourceId.bind g.damageSourceById?
  let tcs :=
    match src? with
    | some src => g.evalLayer3 src
    | none => g.evalLayer3 obj
  let raw :=
    match obj.abilityEffect.bind (·.modalSpec?) with
    | some ms => ms.modes
    | none =>
      match obj.triggeredAbility with
      | some ab => ab.modeEffects
      | none => #[]
  if tcs.isEmpty then raw else raw.map (TextChange.applyEffect tcs)

/-- Individual mode effects for Hawkeye's Trick Arrows reflexive trigger (CR 603.3c / 700.2b). -/
def hawkeyeModeEffects : Array Effect :=
  #[{ targets := .creature
      body := .installEffect (.applyContinuous .untilEndOfTurn (.target 0)
        (.applyRule (.combat (.cantBlock .self none)))) },
    { targets := .player
      body := Instruction.dealDamageFixed (.players (.target 0)) 2 },
    { body := .seq #[Instruction.discardFixed 1, Instruction.drawFixed 1] }]

/-- Modal body for once-per-turn unused-mode combat/draw triggers (e.g. The Vision). -/
def castingVisionModesBody : Instruction :=
  .chooseModes {
    unusedThisTurn := true
    modes := #[
      { body := Instruction.grantKeywords .this #[Keyword.doubleStrike] },
      { body := Instruction.grantKeywords .this #[Keyword.indestructible] },
      { body := Instruction.drawFixed 1 }
    ]
  }

/-- Modal body for +1/+1 counter vs. remove-counter-and-draw choice triggers (e.g. Mr. Hyde). -/
def stepHydeChooseBody : Instruction :=
  .chooseModes {
    modes := #[
      { body := Instruction.putPlusOne .this 1 },
      { body := .bind ⟨0⟩
          (.permanent (.modifyCounters (.remove none (.exact (.const 1)))
            (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .counterCount none .ge (.const 1)]))
            (choice? := some { chooser := .controller, count := .exact (.const 1) })))
          (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.drawFixed 1)) }
    ]
  }

/-- Hawkeye's Trick Arrows with the chosen modes, in printed order, with
target slots aligned across combined modes. -/
def hawkeyeArrowsEffect (modes : Array Nat) : Effect :=
  let sorted := modes.qsort (· < ·)
  let (spec, steps, _) := sorted.foldl (fun (accSpec, accSteps, nextSlot) m =>
    if m == 0 then
      let body := Instruction.installEffect
        (.applyContinuous .untilEndOfTurn (.target nextSlot) (.applyRule (.combat (.cantBlock .self none))))
      (accSpec.append TargetSpec.creature, accSteps.push body, nextSlot + 1)
    else if m == 1 then
      let body := Instruction.dealDamageFixed (.players (.target nextSlot)) 2
      (accSpec.append TargetSpec.player, accSteps.push body, nextSlot + 1)
    else
      let body := Instruction.seq #[Instruction.discardFixed 1, Instruction.drawFixed 1]
      (accSpec, accSteps.push body, nextSlot))
    (TargetSpec.none, #[], 0)
  let body :=
    if steps.isEmpty then .noop
    else if steps.size == 1 then steps[0]!
    else .seq steps
  { targets := spec, body }

/-- Whether `p` may choose this mode of a triggered ability (CR 603.3c / 700.2b / 115.5). -/
def triggerModeChoosable (g : Game) (p : PlayerId) (obj : GameObject) (e : Effect) : Bool :=
  let e := g.expandEachOpponentEffect p e (some obj.id)
  let spec := e.targets
  let stackSelf := if obj.zone == .stack then some obj.id else none
  let divOk :=
    e.dividedDamage?.all (fun (n, _) =>
      spec.allowsZero ||
        let legal := g.legalTargetsForSpec p spec obj.sourceId stackSelf
        !legal.isEmpty && e.targetCount ≤ n)
  divOk && (!e.requiresTarget || spec.allowsZero ||
    g.effectHasEnoughTargets p e obj.sourceId stackSelf)

/-- Ask for the modes of a modal triggered ability just put on the stack. -/
def beginTriggerModeChoice (g : Game) (p : PlayerId) (obj : GameObject) (count : Nat) : Game :=
  let modes := g.triggerModesOf obj
  let choosable := modes.filter (g.triggerModeChoosable p obj)
  if choosable.size < count then
    let objName := g.name obj
    let g := g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
    let detail :=
      if choosable.isEmpty then "has no mode that can be chosen"
      else s!"has fewer than {count} modes that can be chosen"
    g.logMsg s!"{objName} {detail} and is removed from the stack (CR 603.3c / 700.2b)"
  else
    let what := if count == 2 then "two modes" else "a mode"
    g.beginResolutionChoice p (.triggerModes obj.id count #[])
      s!"{(g.player p).name} chooses {what} for {g.name obj} (CR 603.3c)"

/-- Put a triggered ability of `source` onto the stack (CR 603.3). A modal
ability's modes are chosen as it is put on the stack (CR 603.3c). -/
def putTriggeredAbilityOnStack (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) (cause : Option GameObject := none)
    (causeId : Option ObjectId := none)
    (causeController : Option PlayerId := none)
    (causeIds : Array ObjectId := #[])
    (eventCause : Option EventCause := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none)
    (abilityEffectOverride : Option Effect := none)
    (isReflexive : Bool := false) : Game :=
  if !g.stillInGame controller then g
  else
    -- “For each opponent / player, ...”: expand `forEach?` into one slot per matching player (CR 601.2c).
    let abilityEffect :=
      abilityEffectOverride.orElse fun _ =>
        if ab.effect.targets.slots.any (·.forEach?.isSome) then
          some (g.expandEachOpponentEffect controller ab.effect)
        else none
    let srcIdOpt : Option ObjectId :=
      if source.id == noSourceSentinelId then none
      else some source.id
    let srcSnap : EventObject :=
      match srcIdOpt.bind g.findLiveSourceObject? with
      | some cur => g.snapshot cur
      | none =>
        match srcIdOpt.bind g.lastKnownBefore? with
        | some eo => eo
        | none =>
          if srcIdOpt.isNone then
            { (g.snapshot source) with
              id := none
              controller := source.controller.orElse (fun _ => some controller) }
          else g.snapshot source
    let newId : ObjectId := ⟨g.nextObjectId⟩
    let spec : StackTriggerSpec := {
      triggeredAbility := some ab
      abilityEffect := abilityEffect
      isReflexive := isReflexive || abilityEffectOverride.isSome
      sourceId := srcIdOpt
      abilityName := some s!"{if srcIdOpt.isSome then srcSnap.name else g.name source}'s ability"
      delayedTrigger := delayedTrigger
      lastKnownPower := lastKnownPower
      lastKnownToughness := lastKnownToughness
      triggerCauseId := (cause.map (·.id)).orElse (fun _ => causeId)
      triggerCauseIds := causeIds
      triggerCauseController := causeController.orElse (fun _ => cause.bind g.controllerOf)
      triggerCausePower := cause.bind (fun c =>
        if (g.findObject? c.id).any (·.isOnBattlefield) then some (g.power (g.object! c.id))
        else (g.lastKnownPowerOf? c.id).orElse (fun _ => some (g.power c)))
      triggerCauseStatus := cause.map (·.status)
    }
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber newId srcSnap controller
      (spec := spec) (cause := eventCause))
    let obj := g.object! newId
    let srcLabel := if srcIdOpt.isNone then source.name else srcSnap.name
    let g := g.logMsg s!"{srcLabel}'s {event} is put on the stack"
    let modal? := (obj.abilityEffect.bind (·.modalSpec?)).orElse (fun _ =>
      if abilityEffectOverride.isSome then none else ab.modalSpec?)
    match modal? with
    | none => g
    | some ms =>
      if ms.chooseAtResolution then g
      else if ms.maxModes == .eventAmount then
        -- Hawkeye's Trick Arrows reflexive modal trigger (up to paid-times modes).
        let paid := (lastKnownPower.map Int.toNat).getD 0
        let choosable := ms.modes.filter (g.triggerModeChoosable controller obj)
        let maxModes := Nat.min paid ms.modes.size
        if maxModes == 0 || choosable.isEmpty then
          let noop : Effect := { body := .noop }
          let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := #[]))
          let g := g.changes #[
            .object obj.id (.abilityEffect (some noop)),
            .stackEntry obj.id (.targetsAnnounced true)]
          g.logMsg s!"{(g.player controller).name} chooses 0 modes for {g.name obj} (CR 603.3c)"
        else
          g.beginResolutionChoice controller (.hawkeyeModes maxModes #[] (some obj.id))
            s!"{(g.player controller).name} chooses up to {maxModes} Trick Arrows modes (CR 603.3c)"
      else if ms.maxModes == .chosenX then
        let x := (source.chosenX.orElse (fun _ => g.chosenXOf? source.id)).getD 0
        let modes := g.triggerModesOf obj
        let choosable := modes.filter (g.triggerModeChoosable controller obj)
        let maxModes := Nat.min x modes.size
        if maxModes == 0 || choosable.isEmpty then
          let noop : Effect := { body := .noop }
          let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := #[]))
          let g := g.changes #[
            .object obj.id (.abilityEffect (some noop)),
            .stackEntry obj.id (.targetsAnnounced true)]
          g.logMsg s!"{(g.player controller).name} chooses 0 modes for {g.name obj} (CR 603.3c)"
        else
          g.beginResolutionChoice controller (.upToTriggerModes obj.id maxModes #[])
            s!"{(g.player controller).name} chooses up to {maxModes} mode(s) for {g.name obj} (CR 603.3c)"
      else if ms.unusedThisTurn || ms.unusedEver then
        let lifetime := ms.unusedEver
        let memory :=
          match srcIdOpt with
          | some sid => if lifetime then g.modesChosenEver sid else g.modesChosenThisTurn sid
          | none => #[]
        let available := (List.range ms.modes.size).toArray.filter (fun m =>
          !memory.contains m && (ms.modes[m]?.any (g.triggerModeChoosable controller obj)))
        if available.isEmpty then
          let objName := g.name obj
          let g := g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
          let msg :=
            if lifetime then
              if ms.modes.size == 3 then
                s!"all three modes have been chosen. {objName} is removed from the stack (CR 603.3c)"
              else
                s!"all modes have been chosen. {objName} is removed from the stack (CR 603.3c)"
            else if ab.effect.body == castingVisionModesBody then
              s!"{objName} has no unused mode and is removed from the stack (CR 603.3c)"
            else
              s!"all three modes have been chosen this turn. {objName} is removed from the stack (CR 603.3c)"
          g.logMsg msg
        else
          let prompt :=
            if lifetime then
              s!"{(g.player controller).name} chooses a mode that hasn't been chosen (CR 603.3c)"
            else if ab.effect.body == castingVisionModesBody then
              "Choose one that hasn't been chosen this turn (CR 603.3c)"
            else
              s!"{(g.player controller).name} chooses an Alliance mode that hasn't been chosen this turn (CR 603.3c)"
          g.beginResolutionChoice controller (.stackTriggerUnusedMode obj.id srcIdOpt available lifetime)
            prompt
      else if ab.effect.body == stepHydeChooseBody then
        g.beginResolutionChoice controller (.stackHydeMode obj.id)
          s!"{(g.player controller).name} chooses a mode for {g.name obj} — 0 put a +1/+1 counter, 1 remove a counter and draw (CR 603.3c)"
      else
        let n := (ms.minModes.evalConst?.getD 1).toNat
        g.beginTriggerModeChoice controller obj n

/-- True when this trigger would be put on the stack with no legal target (CR 603.3d). -/
def triggerHasNoLegalTarget (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : ObjectId) (abilityEffectOverride : Option Effect := none) : Bool :=
  let srcIdOpt :=
    if sourceId == noSourceSentinelId then none
    else some sourceId
  match abilityEffectOverride with
  | some eff =>
    eff.requiresTarget && !eff.allowsZeroTargets && !eff.effectiveTargetSpec.allowsZero &&
      !g.effectHasEnoughTargets controller eff srcIdOpt
  | none =>
    ab.requiresTarget && !ab.allowsZeroTargets && !ab.targetSpec.allowsZero &&
      (g.legalTargetsForSpec controller ab.targetSpec srcIdOpt).isEmpty

/-- Put `ab` on the stack, or log that it is removed for lack of a target (CR 603.3d). -/
def putTriggerOrFizzle (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (causeId : Option ObjectId := none)
    (causeController : Option PlayerId := none)
    (causeIds : Array ObjectId := #[])
    (eventCause : Option EventCause := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none)
    (abilityEffectOverride : Option Effect := none)
    (isReflexive : Bool := false) : Game :=
  if g.triggerHasNoLegalTarget controller ab source.id abilityEffectOverride then
    let isRefl := isReflexive || abilityEffectOverride.isSome
    let srcLabel :=
      if source.id == noSourceSentinelId then source.name
      else g.name source
    if isRefl then
      g.logMsg s!"{srcLabel}'s {event} has no legal target and is removed (CR 603.3d)"
    else
      g.logMsg
        s!"{srcLabel}'s {event} is removed from the stack (no legal target) (CR 603.3d)"
  else
    g.putTriggeredAbilityOnStack controller source ab event lastKnownPower lastKnownToughness
      (cause := cause) (causeId := causeId) (causeController := causeController) (causeIds := causeIds)
      (eventCause := eventCause)
      (delayedTrigger := delayedTrigger)
      (abilityEffectOverride := abilityEffectOverride)
      (isReflexive := isReflexive)

/-- Put `ab` on the stack for `pattern`, using that pattern's label and CR 603.3d check. -/
def putQueuedTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (pattern : TriggerPattern)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (causeId : Option ObjectId := none)
    (causeController : Option PlayerId := none)
    (causeIds : Array ObjectId := #[])
    (eventCause : Option EventCause := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none)
    (abilityEffectOverride : Option Effect := none)
    (isReflexive : Bool := false) : Game :=
  if !g.stillInGame controller then g
  else
    let label :=
      if isReflexive || abilityEffectOverride.isSome then "reflexive ability"
      else pattern.label
    if abilityEffectOverride.isSome || (ab.requiresTarget && !ab.allowsZeroTargets) then
      g.putTriggerOrFizzle controller source ab label lastKnownPower lastKnownToughness
        (cause := cause) (causeId := causeId) (causeController := causeController) (causeIds := causeIds)
        (eventCause := eventCause)
        (delayedTrigger := delayedTrigger)
        (abilityEffectOverride := abilityEffectOverride)
        (isReflexive := isReflexive)
    else
      g.putTriggeredAbilityOnStack controller source ab label
        lastKnownPower lastKnownToughness (cause := cause) (causeId := causeId)
        (causeController := causeController)
        (causeIds := causeIds)
        (eventCause := eventCause) (delayedTrigger := delayedTrigger)
        (abilityEffectOverride := abilityEffectOverride)
        (isReflexive := isReflexive)

/-- Add `n` lore counters via `replaceCountersPutChoice`, including Doc Samson's
+1 replacement (CR 614.1a / MSH 517), emitting a single `n'`-counter `.lore`
`PermanentEvent.counters` (CR 715.2b), pausing for CR 616.1 choice when
competing counter replacements tie, and preserving `EventCause.replaced`. -/
def addLoreCounters (g : Game) (saga : GameObject) (n : Nat)
    (cause : Option EventCause := some (.turnBased .sagaLoreOnMain)) : Game :=
  if let .chooseReplacement .. := g.pending then
    let baseCause := cause.getD (.turnBased .sagaLoreOnMain)
    g.chainPendingReplacement (.addLoreCounters saga.id n (some baseCause))
  else
  match g.controllerOf saga with
  | some p =>
    if !g.hasSubtype saga .saga then g
    else
    match g.findObject? saga.id with
    | none => g
    | some saga =>
      if !saga.isOnBattlefield || n == 0 then g
      else
        let baseCause := cause.getD (.turnBased .sagaLoreOnMain)
        let propCause := g.resolveOptionalCause (some baseCause) (fallbackCtrl := some p)
        let proposed := GameEvent.counters g.turnNumber (some p) (g.snapshot saga) .lore n (cause := propCause)
        let (n', applied, cause', choice?, _) :=
          if proposed.watches .wouldPutCounter then
            g.replaceCountersPutChoice saga .lore n (putter := some p) (cause := some baseCause)
          else (0, #[], some baseCause, none, #[])
        match choice? with
        | some (chooser, choices) =>
          g.promptChooseReplacement chooser choices (.addLoreCounters saga.id n (some baseCause))
        | none =>
          let g := g.consumeReplacementOrder applied
          let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := some p)
          if n' == 0 then g
          else
            match g.findObject? saga.id with
            | none => g
            | some o =>
              if !o.isOnBattlefield then g
              else
                let pre := g
                let wasZeroOnBf := o.isOnBattlefield && o.status.counterCount .lore == 0
                let hasWhileCounterCtrlOrCopy :=
                  wasZeroOnBf &&
                    g.activeEffects.any (fun (_, e) =>
                      match e with
                      | .layered _ (.control _) (.whileSourceHasCounter s k)
                      | .layered _ (.copy _) (.whileSourceHasCounter s k) =>
                        s == o.id && k == .lore
                      | _ => false)
                let g := g.record (GameEvent.counters g.turnNumber (some p) (g.snapshot o) .lore n'
                  (cause := finalCause))
                let g :=
                  if hasWhileCounterCtrlOrCopy then
                    reconcileControlAfterTransition pre g (cause := some finalCause)
                  else g
                let postObj? := g.findObject? o.id
                let sagaName := postObj?.map g.name |>.getD (g.name o)
                let lore := postObj?.map (·.status.lore) |>.getD (o.status.lore + n')
                if n' == 1 then
                  g.logMsg s!"{sagaName} gets a lore counter ({lore})"
                else
                  g.logMsg s!"{sagaName} gets {n'} lore counters ({lore})"
  | none => g

/-- Put one lore counter on `saga` and queue the matching chapter abilities
(CR 715.2). -/
def addOneLoreCounter (g : Game) (saga : GameObject) : Game :=
  g.addLoreCounters saga 1

/-- Add a lore counter to each Saga in `sagaIds` sequentially, pausing and
chaining `.addLoreAfterDrawStep rest` if a CR 616.1 replacement choice opens. -/
def addLoreAfterDrawStepIds (g : Game) (sagaIds : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    let mut idx := 0
    while idx < sagaIds.size do
      let sid := sagaIds[idx]!
      idx := idx + 1
      match g.findObject? sid with
      | some o =>
        if o.isOnBattlefield && g.hasSubtype o .saga && g.finalChapterNumber o > 0 then
          g := g.addOneLoreCounter o
          if let .chooseReplacement .. := g.pending then
            let rest := sagaIds.extract idx sagaIds.size
            if !rest.isEmpty then
              g := g.chainPendingReplacement (.addLoreAfterDrawStep rest)
            idx := sagaIds.size
      | none => pure ()
    return g

/-- After the draw step / as first main begins, add a lore counter to each
Saga the active player controls simultaneously in one batch (CR 613.1d,f / 703.4f / 715.3c). -/
def addLoreAfterDrawStep (g : Game) : Game :=
  let sagaIds := ((g.permanentsOf g.activePlayer).filter (fun o =>
    g.hasSubtype o .saga && g.finalChapterNumber o > 0)).map (·.id)
  if sagaIds.isEmpty then g
  else
    (g.withBatchCore (some (.turnBased .sagaLoreOnMain)) fun g =>
      g.addLoreAfterDrawStepIds sagaIds).flushQueuedLinkedExile

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

/-- Tap an untapped permanent and queue becomes-tapped triggers (CR 603.2e).
Entering the battlefield tapped is not becoming tapped; only a change from
untapped to tapped fires these abilities (Hawkeye's Bow, Trick Arrows,
Captain America, Living Legend). -/
def becomeTapped (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  let oName := g.name o
  if o.status.tapped then
    g.logMsg s!"{oName} is already tapped"
  else
    let during := (g.controllerOf o).any g.isOnActiveTeam
    let happened := GameEvent.tapped g.turnNumber (g.snapshot o) true during
      (cause := g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o))
    (g.record happened).logMsg s!"{oName} becomes tapped"

/-- Apply `f` to each creature `p` controls, optionally skipping one id. -/
def forEachControlledCreature (g : Game) (p : PlayerId)
    (f : Game → GameObject → Game) (excludeId : Option ObjectId := none) : Game :=
  g.withBatch none fun g =>
    g.foldControlledPermanents p excludeId fun g o =>
      if g.isCreature o then f g o else g

/-- If a stacked triggered ability still needs targets, prompt its controller
(CR 603.3d / 601.2c). -/
def promptTriggerTargetsIfNeeded (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some e =>
    if g.pending != .none then g
    else
      let msg :=
        match (g.findObject? e.objectId).bind (fun o =>
            o.abilityEffect.bind (·.dividedDamage?) <|>
              o.triggeredAbility.bind TriggeredAbility.dividedDamage?) with
        | some (n, maxTargets) =>
          s!"{(g.player e.controller).name} must divide {n} damage among one to {maxTargets} targets (CR 603.3d / 601.2d)"
        | none =>
          s!"{(g.player e.controller).name} must choose a target (CR 603.3d / 601.2c)"
      (g.change (.pending (.chooseTargets e.controller))).logMsg msg
  | none => g

/-- CR 603.3b: part 1 is every waiting trigger whose condition is not another
ability triggering; part 2 is the remainder. -/
def waitingTriggersPart (g : Game) (part2 : Bool) : Array WaitingTrigger :=
  g.waitingTriggers.filter (fun wt => wt.pattern.isAnotherAbilityTriggering == part2)

/-- The current CR 603.3b batch: part 1 if any remain, otherwise part 2. -/
def currentTriggerBatch (g : Game) : Array WaitingTrigger :=
  let part1 := g.waitingTriggersPart false
  if !part1.isEmpty then part1 else g.waitingTriggersPart true

/-- This player's waiting triggers in the current CR 603.3b part. -/
def waitingTriggersOf (g : Game) (p : PlayerId) : Array WaitingTrigger :=
  g.currentTriggerBatch.filter (·.controller == p)

/-- Candidate indices (`0 .. n - 1`) of `p`'s current batch, oldest first (the default order). -/
def defaultTriggerSourceIds (g : Game) (p : PlayerId) : Array Nat :=
  Array.range (g.waitingTriggersOf p).size

/-- Next player in APNAP order who has a waiting trigger in this part
(CR 603.3b / 101.4). -/
def nextTriggerStackingPlayer? (g : Game) : Option PlayerId :=
  let batch := g.currentTriggerBatch
  g.apnapPlayers.find? (fun p => batch.any (·.controller == p))

/-- Remove `wt` from the waiting list. -/
def removeWaitingTrigger (g : Game) (wt : WaitingTrigger) : Game :=
  match g.waitingTriggers.findIdx? (fun w =>
    w.controller == wt.controller && w.source.id == wt.source.id &&
      w.ability == wt.ability && w.pattern == wt.pattern &&
      w.causeId == wt.causeId && w.causeIds == wt.causeIds &&
      w.causeController == wt.causeController &&
      w.delayedTrigger == wt.delayedTrigger &&
      w.abilityEffect == wt.abilityEffect &&
      w.isReflexive == wt.isReflexive) with
  | none => g
  | some i => g.change (.waitingTriggers (g.waitingTriggers.eraseIdx! i))

/-- Put one waiting trigger on the stack. A trigger queued without
`checked := true` is checked here for “only once each turn” (CR 603.2h) and
gets its extra copies (Chief of the Wilds, Bifur). -/
def putWaitingTrigger (g : Game) (wt : WaitingTrigger) (pattern : TriggerPattern) : Game :=
  if !g.stillInGame wt.controller then g
  else
  let put (g : Game) :=
    g.putQueuedTrigger wt.controller wt.source wt.ability pattern
      wt.lastKnownPower wt.lastKnownToughness
      (cause := wt.cause) (causeId := wt.causeId) (causeController := wt.causeController)
      (causeIds := wt.causeIds)
      (eventCause := wt.eventCause) (delayedTrigger := wt.delayedTrigger)
      (abilityEffectOverride := wt.abilityEffect)
      (isReflexive := wt.isReflexive)
  if wt.checked then (put g).promptTriggerTargetsIfNeeded
  else
    if wt.ability.onceEachTurn && g.loggedTriggeredThisTurn wt.source.id wt.ability then g
    else if wt.ability.optionalOnceEachTurn && g.optionalOnceUsedThisTurn wt.source.id then g
    else if !g.triggerConditionHolds wt.controller wt.ability wt.cause (some wt.source) then g
    else
      let originBatch :=
        match g.currentBatch with
        | some (bid, _) => bid
        | none => ⟨g.nextBatchId⟩
      let srcSnap : EventObject :=
        if wt.source.id == noSourceSentinelId then
          { (g.snapshot wt.source) with
            id := none
            controller := wt.source.controller.orElse (fun _ => some wt.controller) }
        else
          match g.findLiveSourceObject? wt.source.id with
          | some cur => g.snapshot cur
          | none => (g.lastKnownBefore? wt.source.id).getD (g.snapshot wt.source)
      let copies := g.extraTriggerCopies wt.controller wt.source + 1
      Id.run do
        let mut g := g
        for _ in [0:copies] do
          g := g.recordTriggeredWithOrigin srcSnap wt.controller wt.ability originBatch
        for i in [0:copies] do
          g := (put g).promptTriggerTargetsIfNeeded
          if g.pending != .none then
            let remCount := copies - (i + 1)
            if remCount > 0 then
              let remCopy := { wt with pattern := pattern, checked := true, ordered := true }
              let rem := Array.replicate remCount remCopy
              g := g.change (.waitingTriggers (rem ++ g.waitingTriggers))
            return g
        return g

/-- Put these waiting triggers on the stack in the given order (CR 603.3 / 603.3d),
stopping early if a triggered ability pauses on mode or target selection
(CR 603.3c–d) and preserving `ordered := true` on any remaining triggers in the
ordered batch. -/
def putTriggerBatch (g : Game) (wts : Array WaitingTrigger) : Game :=
  if wts.isEmpty then g
  else
    Id.run do
      let mut g := g
      for i in [0:wts.size] do
        let wt := wts[i]!
        g := g.removeWaitingTrigger wt
        let beforeSize := g.waitingTriggers.size
        g := g.putWaitingTrigger wt wt.pattern
        if g.pending != .none then
          let rem := wts.extract (i + 1) wts.size
          if !rem.isEmpty then
            let prependedCount := g.waitingTriggers.size - beforeSize
            let prepended := g.waitingTriggers.extract 0 prependedCount
            g := g.change (.waitingTriggers (g.waitingTriggers.extract prependedCount g.waitingTriggers.size))
            for r in rem do
              g := g.removeWaitingTrigger r
            let orderedRem := rem.map ({ · with ordered := true })
            g := g.change (.waitingTriggers (prepended ++ orderedRem ++ g.waitingTriggers))
          return g
      return g.promptTriggerTargetsIfNeeded

/-- Start scrying `n` as a keyword action (CR 701.22).
Scry 0 is skipped and does not trigger “whenever you scry” (CR 701.22b). -/
def beginScry (g : Game) (p : PlayerId) (n : Nat) : Game :=
  g.withContinuationFrame fun g =>
    if !g.stillInGame p then g
    else
      let pl := g.player p
      let count := min n pl.library.size
      if n == 0 then
        g.logMsg s!"{pl.name} scries {n} (no cards to look at)"
      else if count == 0 then
        let happened :=
          GameEvent.looked g.turnNumber p 0 false n (cause := some (g.resolvingOrRuleCause p))
        let g := g.record happened
        g.logMsg s!"{pl.name} scries {n} (no cards to look at)"
      else
        (g.changes #[.pending (.scry p count n), .surveilReturnMvAtMost none]).logMsg s!"{pl.name} scries {n}"

/-- Scry `scryN`, then draw `drawN`. An empty library draws immediately.
The draw waits on `pendingDrawAfterScry` while the scry choice is open. -/
def scryThenDraw (g : Game) (p : PlayerId) (scryN drawN : Nat) : Game :=
  g.withContinuationFrame fun g =>
    let g := g.change (.pendingDrawAfterScry (some (p, drawN)))
    let g := g.beginScry p scryN
    if g.pendingDrawAfterScry.isSome &&
        (match g.pending with | .scry .. => false | _ => true) then
      let g := g.change (.pendingDrawAfterScry none)
      g.draw p drawN
    else g

end Game
end Mtg.Engine
