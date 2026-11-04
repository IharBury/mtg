import Mtg.Engine.Game.Targeting

/-!
# Triggered abilities onto the stack (CR 603.3)

Putting triggered abilities on the stack, intervening-if conditions
(CR 603.4), extra trigger copies, Saga lore counters (CR 714.3a / 714.3c),
battlefield folds, `becomeTapped` (CR 603.2e), activated- and mana-ability
lookups, waiting-trigger batches stacked in APNAP order (CR 603.3b), and
`receivePriority`.
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
  | .tapOrUntapNonland =>
    #[{ targeting := .of .nonland, resolution := .onPermanent .tap
        phrase := "Tap target nonland permanent" },
      { targeting := .of .nonland, resolution := .onPermanent .untap
        phrase := "Untap target nonland permanent" }]
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
  | .enter .chooseUpToXModes =>
    #[{ resolution := .sequence [.discard (.cards 1), .draw (.fixed 1)]
        phrase := "Discard a card, then draw a card" },
      { targeting := .of .opponent
        resolution := .targetPlayerLoseLife 2
        phrase := "Target opponent loses 2 life" },
      { targeting := .of (.filtered { noun := "target token", tokenOnly := true })
        resolution := .onPermanent .destroy
        phrase := "Destroy target token" },
      { resolution := .sacrifice .eachPlayersCreature
        phrase := "Each player sacrifices a creature of their choice" }]
  | _ => #[]

/-- Modes of the triggered ability `obj` (from its source). -/
def triggerModesOf (g : Game) (obj : GameObject) : Array Effect :=
  let fra :=
    match obj.sourceId.bind g.damageSourceById? with
    | some src => (g.baseCard src).fraTriggerModes
    | none => (g.baseCard obj).fraTriggerModes
  if !fra.isEmpty then fra
  else (obj.triggeredAbility.map sharedTriggerModes).getD #[]

/-- Individual mode effects for Hawkeye's Trick Arrows reflexive trigger (CR 603.3c / 700.2b). -/
def hawkeyeModeEffects : Array Effect :=
  #[{ targeting := .of .creature, resolution := .hawkeyeArrows [0]
      phrase := "Net — Target creature can't block this turn" },
    { targeting := .of .player, resolution := .hawkeyeArrows [1]
      phrase := "Explosive — Hawkeye deals 2 damage to target player" },
    { resolution := .hawkeyeArrows [2]
      phrase := "Boomerang — Discard a card, then draw a card" }]

/-- Whether `p` may choose this mode of a triggered ability (CR 603.3c / 700.2b). -/
def triggerModeChoosable (g : Game) (p : PlayerId) (obj : GameObject) (e : Effect) : Bool :=
  !e.requiresTarget || e.allowsZeroTargets ||
    !(g.legalTargetsForKind p e.targetKind obj.sourceId).isEmpty

/-- Ask for the modes of a modal triggered ability just put on the stack. -/
def beginTriggerModeChoice (g : Game) (p : PlayerId) (obj : GameObject) (count : Nat) : Game :=
  let modes := g.triggerModesOf obj
  let choosable := modes.filter (g.triggerModeChoosable p obj)
  if choosable.size < count then
    let g := g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
    let detail :=
      if choosable.isEmpty then "has no mode that can be chosen"
      else s!"has fewer than {count} modes that can be chosen"
    g.logMsg s!"{obj.name} {detail} and is removed from the stack (CR 603.3c / 700.2b)"
  else
    let what := if count == 2 then "two modes" else "a mode"
    (g.change (.pending (.fraChoice p (.triggerModes obj.id count #[])))).logMsg
      s!"{(g.player p).name} chooses {what} for {obj.name} (CR 603.3c)"

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
    (reflexiveResolution : Option TriggeredAbility.TriggerResolution := none) : Game :=
  if (g.player controller).lost || (g.player controller).leftTheGame then g
  else
    -- “For each opponent, up to one target … that player controls”: one
    -- optional instance per opponent (CR 601.2c).
    let abilityEffect :=
      abilityEffectOverride.orElse fun _ =>
        match ab.effect.targetKind with
        | .filtered f =>
          if f.controller == .eachOpponent then
            let fs := (g.livingOpponents controller).map (fun pl =>
              { f with controller := .specific pl.id.idx })
            some { ab.effect with
              targeting := .of (.multi fs ((List.range fs.size).toArray)) }
          else none
        | _ => none
    let srcIdOpt : Option ObjectId :=
      if source.id == noSourceSentinelId then none
      else some source.id
    let srcSnap : EventObject :=
      match srcIdOpt.bind g.findObject? with
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
      reflexiveResolution := reflexiveResolution
      sourceId := srcIdOpt
      abilityName := some s!"{source.name}'s ability"
      delayedTrigger := delayedTrigger
      lastKnownPower := lastKnownPower
      lastKnownToughness := lastKnownToughness
      fraCauseId := (cause.map (·.id)).orElse (fun _ => causeId)
      fraCauseIds := causeIds
      fraCauseController := causeController.orElse (fun _ => cause.bind g.controllerOf)
      fraCausePower := cause.bind (fun c =>
        if (g.findObject? c.id).any (·.isOnBattlefield) then some (g.power (g.object! c.id))
        else (g.lastKnownPowerOf? c.id).orElse (fun _ => some (g.power c)))
      fraCauseStatus := cause.map (·.status)
    }
    let g := g.record (GameEvent.triggerPutOnStack g.turnNumber newId srcSnap controller
      (spec := spec) (cause := eventCause))
    let obj := g.object! newId
    let srcLabel := if srcIdOpt.isNone then source.name else g.name source
    let g := g.logMsg s!"{srcLabel}'s {event} is put on the stack"
    match obj.abilityEffect.map Effect.resolution with
    | some (Resolution.mshReflexive .trickArrows paid) =>
      let choosable := hawkeyeModeEffects.filter (g.triggerModeChoosable controller obj)
      let maxModes := Nat.min paid 3
      if maxModes == 0 || choosable.isEmpty then
        let noop : Effect := { resolution := Resolution.hawkeyeArrows [], phrase := "" }
        let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := #[]))
        let g := g.changes #[
          .object obj.id (.abilityEffect (some noop)),
          .stackEntry obj.id (.targetsAnnounced true)]
        g.logMsg s!"{(g.player controller).name} chooses 0 modes for {obj.name} (CR 603.3c)"
      else
        (g.change (.pending (.fraChoice controller (.hawkeyeModes maxModes #[] (some obj.id))))).logMsg
          s!"{(g.player controller).name} chooses up to {maxModes} Trick Arrows modes (CR 603.3c)"
    | _ =>
    match ab.shared with
    | .enter .chooseUpToXModes =>
      let x := (source.chosenX.orElse (fun _ => g.chosenXOf? source.id)).getD 0
      let modes := sharedTriggerModes ab
      let choosable := modes.filter (g.triggerModeChoosable controller obj)
      let maxModes := Nat.min x modes.size
      if maxModes == 0 || choosable.isEmpty then
        let noop : Effect := { resolution := .sequence [], phrase := "" }
        let g := g.record (GameEvent.announced g.turnNumber obj.id (modes := #[]))
        let g := g.changes #[
          .object obj.id (.abilityEffect (some noop)),
          .stackEntry obj.id (.targetsAnnounced true)]
        g.logMsg s!"{(g.player controller).name} chooses 0 modes for {obj.name} (CR 603.3c)"
      else
        (g.change (.pending (.fraChoice controller (.upToTriggerModes obj.id maxModes #[])))).logMsg
          s!"{(g.player controller).name} chooses up to {maxModes} mode(s) for {obj.name} (CR 603.3c)"
    | _ =>
      match ab.effect.resolution with
      | .chooseTriggerModes n => g.beginTriggerModeChoice controller obj n
      | _ =>
        match ab.resolution with
        | .chooseModes modes how =>
          match how with
          | .plusOneOrRemoveCounter =>
            (g.change (.pending (.fraChoice controller (.stackHydeMode obj.id)))).logMsg
              s!"{(g.player controller).name} chooses a mode for {obj.name} — 0 put a +1/+1 counter, 1 remove a counter and draw (CR 603.3c)"
          | .vision | .oneUnused | .oneUnusedThisTurn =>
            let lifetime := how == .oneUnused
            let memory :=
              match srcIdOpt with
              | some sid => if lifetime then g.modesChosenEver sid else g.modesChosenThisTurn sid
              | none => #[]
            let available := (List.range modes.length).toArray.filter (fun m => !memory.contains m)
            if available.isEmpty then
              let g := g.ceaseToExist obj.id (cause := some (.gameRule .noLegalMode))
              let msg :=
                match how with
                | .oneUnusedThisTurn =>
                  s!"all three modes have been chosen this turn. {obj.name} is removed from the stack (CR 603.3c)"
                | .vision =>
                  s!"{obj.name} has no unused mode and is removed from the stack (CR 603.3c)"
                | _ =>
                  s!"all three modes have been chosen. {obj.name} is removed from the stack (CR 603.3c)"
              g.logMsg msg
            else
              let prompt :=
                match how with
                | .oneUnusedThisTurn =>
                  s!"{(g.player controller).name} chooses an Alliance mode that hasn't been chosen this turn (CR 603.3c)"
                | .vision =>
                  "Choose one that hasn't been chosen this turn (CR 603.3c)"
                | _ =>
                  s!"{(g.player controller).name} chooses a mode that hasn't been chosen (CR 603.3c)"
              (g.change (.pending (.fraChoice controller (.stackTriggerUnusedMode obj.id srcIdOpt available lifetime)))).logMsg
                prompt
          | _ =>
            if (sharedTriggerModes ab).isEmpty then g else g.beginTriggerModeChoice controller obj 1
        | _ =>
          if (sharedTriggerModes ab).isEmpty then g else g.beginTriggerModeChoice controller obj 1

/-- True when this trigger would be put on the stack with no legal target (CR 603.3d). -/
def triggerHasNoLegalTarget (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : ObjectId) (abilityEffectOverride : Option Effect := none) : Bool :=
  let srcIdOpt :=
    if sourceId == noSourceSentinelId then none
    else some sourceId
  -- A single-instance shape announcing several targets (`kind.spec.slots.isEmpty`) needs
  -- `targetCount` distinct legal targets (CR 115.3 / 603.3c–d); multi-slot shapes need a
  -- valid cross-slot assignment, checked in `legalTargetsForKind`.
  let lacking (kind : EffectTargetKind) (count : Nat) : Bool :=
    let legal := g.legalTargetsForKind controller kind srcIdOpt
    if kind.spec.slots.isEmpty then legal.size < max 1 count else legal.isEmpty
  match abilityEffectOverride with
  | some eff =>
    eff.requiresTarget && !eff.allowsZeroTargets && lacking eff.targetKind eff.targetCount
  | none =>
    ab.requiresTarget && !ab.allowsZeroTargets && lacking ab.targetKind ab.targeting.targetCount

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
    (reflexiveResolution : Option TriggeredAbility.TriggerResolution := none) : Game :=
  if g.triggerHasNoLegalTarget controller ab source.id abilityEffectOverride then
    let isRefl := abilityEffectOverride.isSome || reflexiveResolution.isSome
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
      (reflexiveResolution := reflexiveResolution)

/-- Put `ab` on the stack for `event`, using that event's spec for the log label
and CR 603.3d check so a new event is not restated at every queue site. -/
def putQueuedTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (causeId : Option ObjectId := none)
    (causeController : Option PlayerId := none)
    (causeIds : Array ObjectId := #[])
    (eventCause : Option EventCause := none)
    (delayedTrigger : Option (DelayedTriggerKind × EventCause) := none)
    (abilityEffectOverride : Option Effect := none)
    (reflexiveResolution : Option TriggeredAbility.TriggerResolution := none) : Game :=
  if (g.player controller).lost || (g.player controller).leftTheGame then g
  else
    let label :=
      if abilityEffectOverride.isSome || reflexiveResolution.isSome then "reflexive ability"
      else event.label
    if event.checkTargets || abilityEffectOverride.isSome ||
        (ab.requiresTarget && !ab.allowsZeroTargets) then
      g.putTriggerOrFizzle controller source ab label lastKnownPower lastKnownToughness
        (cause := cause) (causeId := causeId) (causeController := causeController) (causeIds := causeIds)
        (eventCause := eventCause)
        (delayedTrigger := delayedTrigger)
        (abilityEffectOverride := abilityEffectOverride)
        (reflexiveResolution := reflexiveResolution)
    else
      g.putTriggeredAbilityOnStack controller source ab label
        lastKnownPower lastKnownToughness (cause := cause) (causeId := causeId)
        (causeController := causeController)
        (causeIds := causeIds)
        (eventCause := eventCause) (delayedTrigger := delayedTrigger)
        (abilityEffectOverride := abilityEffectOverride)
        (reflexiveResolution := reflexiveResolution)

/-- Add `n` lore counters via `replaceCountersPutChoice`, including Doc Samson's
+1 replacement (CR 614.1a / MSH 517), emitting a single `n'`-counter `.lore`
`PermanentEvent.counters` (CR 714.2b), pausing for CR 616.1 choice when
competing counter replacements tie, and preserving `EventCause.replaced`. -/
def addLoreCounters (g : Game) (saga : GameObject) (n : Nat)
    (cause : Option EventCause := some (.turnBased .sagaLoreOnMain)) : Game :=
  if let .chooseReplacement .. := g.pending then
    let baseCause := cause.getD (.turnBased .sagaLoreOnMain)
    g.chainPendingReplacement (.addLoreCounters saga.id n (some baseCause))
  else
  match g.controllerOf saga, (g.baseCard saga).saga with
  | some p, some _ =>
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
                let lore := o.status.lore + n'
                let sagaName := g.name o
                let g := g.record (GameEvent.counters g.turnNumber (some p) (g.snapshot o) .lore n'
                  (cause := finalCause))
                if n' == 1 then
                  g.logMsg s!"{sagaName} gets a lore counter ({lore})"
                else
                  g.logMsg s!"{sagaName} gets {n'} lore counters ({lore})"
  | _, _ => g

/-- Put one lore counter on `saga` and queue the matching chapter abilities
(CR 714.2). -/
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
        if o.isOnBattlefield && (g.baseCard o).saga.isSome then
          g := g.addOneLoreCounter o
          if let .chooseReplacement .. := g.pending then
            let rest := sagaIds.extract idx sagaIds.size
            if !rest.isEmpty then
              g := g.chainPendingReplacement (.addLoreAfterDrawStep rest)
            idx := sagaIds.size
      | none => pure ()
    return g

/-- After the draw step / as first main begins, add a lore counter to each
Saga the active player controls simultaneously in one batch (CR 703.4f / 714.3c). -/
def addLoreAfterDrawStep (g : Game) : Game :=
  let sagaIds := ((g.permanentsOf g.activePlayer).filter (fun o => (g.baseCard o).saga.isSome)).map (·.id)
  if sagaIds.isEmpty then g
  else
    g.withBatchCore (some (.turnBased .sagaLoreOnMain)) fun g =>
      g.addLoreAfterDrawStepIds sagaIds

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
    let during :=
      match g.controllerOf o with
      | some p => g.activePlayer == p
      | none => false
    let happened := GameEvent.tapped g.turnNumber (g.snapshot o) true during
      (cause := g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o))
    (g.record happened).logMsg s!"{oName} becomes tapped"

/-- Apply `f` to each creature `p` controls, optionally skipping one id. -/
def forEachControlledCreature (g : Game) (p : PlayerId)
    (f : Game → GameObject → Game) (excludeId : Option ObjectId := none) : Game :=
  g.withBatch none fun g =>
    g.foldControlledPermanents p excludeId fun g o =>
      if g.isCreature o then f g o else g

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

/-- If a stacked triggered ability still needs targets, prompt its controller
(CR 603.3d / 601.2c). -/
def promptTriggerTargetsIfNeeded (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some e =>
    if g.pending != .none then g
    else
      let msg :=
        match (g.findObject? e.objectId).bind (fun o =>
            o.abilityEffect.bind (·.dividedDamage) <|>
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
  g.waitingTriggers.filter (fun wt => wt.event.isAnotherAbilityTriggering == part2)

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
      w.ability == wt.ability && w.event == wt.event &&
      w.causeId == wt.causeId && w.causeIds == wt.causeIds &&
      w.causeController == wt.causeController &&
      w.delayedTrigger == wt.delayedTrigger &&
      w.abilityEffect == wt.abilityEffect &&
      w.reflexiveResolution == wt.reflexiveResolution) with
  | none => g
  | some i => g.change (.waitingTriggers (g.waitingTriggers.eraseIdx! i))

/-- Put one waiting trigger on the stack. A trigger queued without
`checked := true` is checked here for “only once each turn” (CR 603.2h) and
gets its extra copies (Chief of the Wilds, Bifur). -/
def putWaitingTrigger (g : Game) (wt : WaitingTrigger) (event : TriggerEvent) : Game :=
  if (g.player wt.controller).lost || (g.player wt.controller).leftTheGame then g
  else
  let put (g : Game) :=
    g.putQueuedTrigger wt.controller wt.source wt.ability event
      wt.lastKnownPower wt.lastKnownToughness
      (cause := wt.cause) (causeId := wt.causeId) (causeController := wt.causeController)
      (causeIds := wt.causeIds)
      (eventCause := wt.eventCause) (delayedTrigger := wt.delayedTrigger)
      (abilityEffectOverride := wt.abilityEffect)
      (reflexiveResolution := wt.reflexiveResolution)
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
          match g.findObject? wt.source.id with
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
              let remCopy := { wt with event := event, checked := true, ordered := true }
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
        g := g.putWaitingTrigger wt wt.event
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
  let g := g.change (.pendingDrawAfterScry (some (p, drawN)))
  let g := g.beginScry p scryN
  if g.pendingDrawAfterScry.isSome &&
      (match g.pending with | .scry .. => false | _ => true) then
    let g := g.change (.pendingDrawAfterScry none)
    g.draw p drawN
  else g

end Game
end Mtg.Engine
