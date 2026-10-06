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
    #[{ targeting := .of (.creatureYouControlAnySubtype #["Wolf"])
        resolution := .onPermanent (.plusOne 1)
        phrase := "Put a +1/+1 counter on target Wolf you control" },
      { resolution := .createTokens .treasure 1
        phrase := "Create a Treasure token" }]
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
    | some src => src.printed.fraTriggerModes
    | none => obj.printed.fraTriggerModes
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
    let g := g.removeFromZoneList obj.id .stack |>.ceaseToExist obj.id
    g.logMsg s!"{obj.name} has no mode that can be chosen and is removed from the stack (CR 700.2d)"
  else
    let what := if count == 2 then "two modes" else "a mode"
    { g with pending := .fraChoice p (.triggerModes obj.id count #[]) }.logMsg
      s!"{(g.player p).name} chooses {what} for {obj.name} (CR 603.3c)"

/-- Put a triggered ability of `source` onto the stack (CR 603.3). A modal
ability's modes are chosen as it is put on the stack (CR 603.3c). -/
def putTriggeredAbilityOnStack (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) (cause : Option GameObject := none) : Game :=
  if (g.player controller).lost then g
  else
    let (g, obj) := g.putStackAbility source controller
      (triggeredAbility := some ab)
      (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)
    let obj := { obj with
      fraCauseId := cause.map (·.id)
      fraCauseController := cause.bind (·.controller)
      fraCausePower := cause.map (g.power ·)
      fraCauseStatus := cause.map (·.status)
      -- “For each opponent, up to one target … that player controls”: one
      -- optional instance per opponent (CR 601.2c).
      abilityEffect :=
        match ab.effect.targetKind with
        | .filtered f =>
          if f.controller == .eachOpponent then
            let fs := (g.livingOpponents controller).map (fun pl =>
              { f with controller := .specific pl.id.idx })
            some { ab.effect with
              targeting := .of (.multi fs ((List.range fs.size).toArray)) }
          else none
        | _ => none }
    let g := g.setObject obj
    let g := g.logMsg s!"{source.name}'s {event} is put on the stack"
    match ab.effect.resolution with
    | .fra (.chooseTriggerModes n) => g.beginTriggerModeChoice controller obj n
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
    (cause : Option GameObject := none) : Game :=
  if g.triggerHasNoLegalTarget controller ab source.id then
    g.logMsg
      s!"{source.name}'s {event} is removed from the stack (no legal target) (CR 603.3d)"
  else
    g.putTriggeredAbilityOnStack controller source ab event lastKnownPower lastKnownToughness
      (cause := cause)

/-- A Reality Fracture intervening “if” clause on the trigger's options. -/
def fraConditionHolds (g : Game) (controller : PlayerId) (cond : FraCondition)
    (source : Option GameObject) (causeStatus : Option Status := none) : Bool :=
  let pl := g.player controller
  match cond with
  | .none => true
  | .sourceNotToken => !(source.any (·.printed.isToken))
  | .twoCreaturesDiedThisTurn => g.creatureDeathsThisTurn ≥ 2
  | .opponentDealtNoncombatDamageLastTurn =>
    (g.livingOpponents controller).any (·.dealtNoncombatDamageLastTurn)
  | .drewThreeThisTurn => pl.cardsDrawnThisTurn ≥ 3
  | .castNoSpellThisTurn => pl.spellsCastThisTurn == 0
  | .activatedLoyaltyThisTurn => pl.activatedLoyaltyThisTurn
  | .sourceWasCast => source.any (·.wasCast)
  | .causeHadCounters => causeStatus.any (·.hasCounters)
  | .sourceHasCounters =>
    source.any (fun o => (g.findObject? o.id).any (·.status.hasCounters))

/-- Reality Fracture intervening “if” clauses, checked when the ability would
trigger and again as it resolves (rulings 743 / 889). -/
def fraInterveningHolds (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (source : Option GameObject) (cause : Option GameObject := none) : Bool :=
  match ab.shared with
  | .pumpIfFiveOtherForests =>
    ((g.permanentsOf controller).filter (fun o =>
      g.hasSubtype o "Forest" && some o.id != cause.map (·.id))).size ≥ 5
  | .destroyOppPermanentIfSixLands =>
    ((g.permanentsOf controller).filter (·.printed.isLand)).size ≥ 6
  | .prepareSourceIfNot =>
    match source.bind (fun o => g.findObject? o.id) with
    | some o => !o.status.prepared
    | none => true
  | .prepareSourceIfThreeDied => g.battlefieldCreaturesToGyThisTurn.size ≥ 3
  | .sacrificeSourceIfNoPlaneswalker =>
    !(g.permanentsOf controller).any (·.printed.isPlaneswalker)
  | .surveilReturnIfGainedLife => (g.player controller).lifeGainedThisTurn > 0
  | _ => true

/-- True when any intervening trigger condition holds (e.g. Ferocious). -/
def triggerConditionHolds (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (cause : Option GameObject := none) (source : Option GameObject := none) : Bool :=
  let powerOk :=
    match ab.youControlCreatureWithPower? with
    | none => true
    | some n => g.greatestPowerAmongCreatures controller ≥ n
  let otherOk :=
    match ab.anotherCreaturePowerAtMost? with
    | none => true
    | some n =>
      match cause with
      | some o => g.power o ≤ n
      | none => true
  let lifeOk :=
    match ab.timing.gainedLifeAtLeast with
    | none => true
    | some n => (g.player controller).lifeGainedThisTurn ≥ n
  let hulklingOk :=
    match ab.shared, cause, source with
    | .watch .hulklingCompare, some entered, some hulkling =>
      g.power entered > g.power hulkling || g.toughness entered > g.toughness hulkling
    | .watch .hulklingCompare, _, _ => false
    | _, _, _ => true
  -- “Whenever another [legendary] Wolf you control enters”.
  let causeOk :=
    match cause with
    | some o =>
      (ab.opts.thisOrAnotherSubtype.all (g.hasSubtype o ·)) &&
        (!ab.opts.anotherLegendary || o.isLegendary)
    | none => true
  -- Intervening “if” clauses checked as the ability triggers (CR 603.4);
  -- they are checked again on resolution.
  let interveningOk :=
    match ab.shared with
    | .beginCombatIfDrawnTwoPump => (g.player controller).cardsDrawnThisTurn ≥ 2
    | .thisAttack .equippedDrain =>
      source.any (fun s => g.battlefield.any (fun e => e.attachedTo == some s.id && e.printed.isEquipment))
    | .resource .drawIfAnotherHeroDamage =>
      (g.permanentsOf controller).any (fun o => g.hasSubtype o "Hero" && some o.id != source.map (·.id))
    | .step .drawToTen => (g.player controller).hand.size < 10
    | .protectionEverything => source.any (·.wasCast)
    | .death .deathtouchOppSac => cause.any (g.hasDeathtouch ·)
    | .resource .plusOneOnThisOnce => cause.any (fun c => some c.id != source.map (·.id))
    | .resource .plusOneOnHeroesCreateWall =>
      cause.any (fun c => some c.id != source.map (·.id) && c.controlledBy controller &&
        g.hasSubtype c "Hero")
    | .watch .sheHulkRedirectOnce => !g.sheHulkDamageUsedThisTurn
    | _ => true
  powerOk && otherOk && lifeOk && hulklingOk && causeOk && interveningOk &&
    g.fraInterveningHolds controller ab source cause &&
    g.fraConditionHolds controller ab.opts.fraCondition source (cause.map (·.status))

/-- Put `ab` on the stack for `event`, using that event's spec for the log label
and CR 603.3d check so a new event is not restated at every queue site. -/
def putQueuedTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  if (g.player controller).lost then g
  else if !g.triggerConditionHolds controller ab cause (some source) then g
  else if event.checkTargets then
    g.putTriggerOrFizzle controller source ab event.label lastKnownPower lastKnownToughness
      (cause := cause)
  else
    g.putTriggeredAbilityOnStack controller source ab event.label
      lastKnownPower lastKnownToughness (cause := cause)

/-- Append waiting-trigger snapshots. -/
def enqueueWaitingTriggers (g : Game) (wts : Array WaitingTrigger) : Game :=
  if wts.isEmpty then g else { g with waitingTriggers := g.waitingTriggers ++ wts }

/-- Extra times a trigger of `source` fires from Bifur / Chief / Wizard's Staff
statics. Each such ability adds one additional instance; they stack. -/
def extraTriggerCopies (g : Game) (controller : PlayerId) (source : GameObject) : Nat :=
  let story := (g.player controller).enduringStory
  (g.permanentsOf controller).foldl (fun acc o =>
    o.staticAbilities.foldl (fun acc ab =>
      match ab with
      | .extraTriggerIfEnduringStorySubtype subtype =>
        if story && g.hasSubtype source subtype then acc + 1 else acc
      | .extraTriggerAnotherYouControl subtypes includeBattles =>
        if o.id == source.id then acc
        else
          let matchSubtype := subtypes.any (fun s => g.hasSubtype source s)
          let matchBattle := includeBattles && source.printed.isBattle
          if matchSubtype || matchBattle then acc + 1 else acc
      | .equippedTriggersAgain =>
        if o.attachedTo == some source.id then acc + 1 else acc
      | _ => acc) acc) 0

/-- Queue `ab` until a player would receive priority (CR 603.3 / 603.4). The
intervening condition is checked when the event occurs. -/
def queueTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  if (g.player controller).lost then g
  else if !g.triggerConditionHolds controller ab cause (some source) then g
  else if ab.onceEachTurn &&
      ((g.findObject? source.id).map (·.status.firedOnceEachTurn)).getD source.status.firedOnceEachTurn then g
  else if ab.optionalOnceEachTurn &&
      ((g.findObject? source.id).map (·.status.optionalOnceUsed)).getD source.status.optionalOnceUsed then g
  else
    let g :=
      if ab.onceEachTurn then
        match g.findObject? source.id with
        | some o => g.setObject { o with status := { o.status with firedOnceEachTurn := true } }
        | none => g
      else g
    let copies := g.extraTriggerCopies controller source + 1
    let wt : WaitingTrigger := {
      controller, source, ability := ab, event, lastKnownPower, lastKnownToughness,
      causeId := cause.map (·.id), cause, checked := true }
    Id.run do
      let mut g := g
      for _ in [0:copies] do
        g := g.enqueueWaitingTriggers #[wt]
      return g

/-- Put one lore counter on `saga` and queue the matching chapter abilities
(CR 714.2 / 714.3). Counters are added one at a time. -/
def addOneLoreCounter (g : Game) (saga : GameObject) : Game :=
  match saga.controller, saga.printed.saga with
  | some p, some sdef =>
    match g.findObject? saga.id with
    | none => g
    | some saga =>
      if !saga.isOnBattlefield then g
      else
        let lore := saga.status.lore + 1
        let g := g.setObject { saga with status := { saga.status with lore } }
        let g := g.logMsg s!"{saga.name} gets a lore counter ({lore})"
        let saga := g.object! saga.id
        (sdef.chaptersForLore lore).foldl (fun g ch =>
          match ch.chapterEffect with
          | none => g
          | some ce =>
            g.queueTrigger p saga (TriggeredAbility.sagaChapter lore ce)
              .sagaChapter) g
  | _, _ => g

/-- Add `n` lore counters one at a time (CR 714.3c). -/
def addLoreCounters (g : Game) (saga : GameObject) (n : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      match g.findObject? saga.id with
      | some o => g := g.addOneLoreCounter o
      | none => pure ()
    return g

/-- As a Saga enters, put a lore counter on it (CR 714.2a). -/
def addLoreAsSagaEnters (g : Game) (o : GameObject) : Game :=
  if o.printed.saga.isSome then g.addOneLoreCounter o else g

/-- After the draw step / as first main begins, add a lore counter to each
Saga the active player controls (CR 714.2b). -/
def addLoreAfterDrawStep (g : Game) : Game :=
  (g.permanentsOf g.activePlayer).foldl (fun acc o =>
    if o.printed.saga.isSome then acc.addOneLoreCounter o else acc) g

/-- Triggered abilities an attached Equipment grants `o` (Hunter's Axe,
Medic's Kitesail). -/
def attachedGrantedTriggers (g : Game) (o : GameObject) : Array TriggeredAbility :=
  if !o.isOnBattlefield then #[]
  else
    g.battlefield.foldl (fun acc eq =>
      if eq.attachedTo != some o.id then acc
      else
        eq.staticAbilities.foldl (fun acc ab =>
          match ab with
          | .fra .equippedHuntersAxe =>
            acc.push (TriggeredAbility.fra .attack
              "Whenever this creature attacks, it gains your choice of trample or deathtouch until end of turn."
              (.fra (.chooseKeyword [0, 3])))
          | .fra .equippedMedicsKitesail =>
            acc.push (TriggeredAbility.fra .attack
              "Whenever this creature attacks, you gain 1 life." (.gainLife 1))
          | _ => acc) acc) #[]

/-- Prowess triggers of `o`, one for each instance (CR 702.108). -/
def prowessTriggers (g : Game) (o : GameObject) : Array TriggeredAbility :=
  if !o.isOnBattlefield then #[]
  else
    let printed := if g.retainsPrintedAbilities o then o.printed.prowessInstances else 0
    let granted :=
      (g.attachedGrantedKeywords o).prowess || o.grantedUntilEot.prowess ||
        (g.enduringStoryKeywords o).prowess || (g.leftoverGrantedKeywords o).prowess
    let n := printed + (if granted then 1 else 0)
    Array.replicate n (TriggeredAbility.fra .youCastNoncreature
      "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)"
      (.onSource (.pump 1 1)))

/-- Queue each printed trigger of `source` that fires on `event` (CR 603.3). -/
def putMatchingSourceTriggers (g : Game) (controller : PlayerId) (source : GameObject)
    (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (keep : TriggeredAbility → Bool := fun _ => true) : Game :=
  Id.run do
    let mut g := g
    for ab in (source.matchingTriggers event ++
        (g.attachedGrantedTriggers source ++ g.prowessTriggers source).filter (·.firesOn event)).filter keep do
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
  g.foldBattlefield (fun o => o.controlledBy p && excludeId != some o.id) f

/-- Tap an untapped permanent and queue becomes-tapped triggers (CR 603.6d).
Entering the battlefield tapped is not becoming tapped; only a change from
untapped to tapped fires these abilities (Hawkeye's Bow, Trick Arrows,
Captain America, Living Legend). -/
def becomeTapped (g : Game) (o : GameObject) : Game :=
  if o.status.tapped then
    g.logMsg s!"{o.name} is already tapped"
  else
    let first := !o.status.becameTappedThisTurn
    let g := g.setObject { o with status :=
      { o.status with tapped := true, becameTappedThisTurn := true } }
    let g := g.logMsg s!"{o.name} becomes tapped"
    let g := { g with lastBecameTapped := some o.id }
    match o.controller with
    | some p =>
      let g := g.putMatchingSourceTriggers p (g.object! o.id) .sourceBecomesTapped
      -- “Whenever one or more creatures you control become tapped” triggers once
      -- per batch of tapping.
      let g :=
        if o.isCreature then
          g.foldControlledPermanents p none fun g src =>
            if g.waitingTriggers.any (fun w =>
                w.source.id == src.id && w.event == .creaturesYouControlBecomeTapped) then g
            else g.putMatchingSourceTriggers p src .creaturesYouControlBecomeTapped
        else g
      let g :=
        (g.attachmentsOf (g.object! o.id)).foldl (fun (g : Game) (eq : GameObject) =>
          if eq.printed.isEquipment then
            g.putMatchingSourceTriggers p eq .equippedBecomesTapped
          else g) g
      if first && g.activePlayer == p then
        g.foldControlledPermanents p (excludeId := none) (fun g src =>
          g.putMatchingSourceTriggers p src .creatureYouControlTapped
            (cause := some (g.object! o.id)))
      else g
    | none => g

/-- Apply `f` to each creature `p` controls, optionally skipping one id. -/
def forEachControlledCreature (g : Game) (p : PlayerId)
    (f : Game → GameObject → Game) (excludeId : Option ObjectId := none) : Game :=
  g.foldControlledPermanents p excludeId fun g o =>
    if o.isCreature then f g o else g

/-- Queue `event` for each permanent `p` controls that doesn't already have a
waiting trigger for it, so a “one or more” trigger fires once per batch. -/
def putControlledTriggersOncePerBatch (g : Game) (p : PlayerId) (event : TriggerEvent) : Game :=
  g.foldControlledPermanents p none fun g src =>
    if g.waitingTriggers.any (fun w => w.source.id == src.id && w.event == event) then g
    else g.putMatchingSourceTriggers p src event

/-- `p` lost `n` life (from damage, payment, or loss; CR 119.3 / 120.3a):
trigger “whenever a player loses life”. The player and amount ride on the
trigger as last-known toughness (seat index) and power (The Master of
Lake-town). -/
def afterLifeLost (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if n == 0 then g
  else
    let g := { g with lastLifeLost := some (p, n) }
    g.livingPlayers.foldl (fun acc pl =>
      acc.foldControlledPermanents pl.id none fun acc o =>
        acc.putMatchingSourceTriggers pl.id o .playerLosesLife
          (lastKnownPower := some (Int.ofNat n)) (lastKnownToughness := some (Int.ofNat p.idx))) g

/-- Put matching triggers of permanents `p` controls that fire on `event`.
`cause` is the object that made them trigger, when there is one. -/
def putControlledTriggers (g : Game) (p : PlayerId)
    (event : TriggerEvent) (excludeId : Option ObjectId := none)
    (cause : Option GameObject := none)
    (lastKnownPower : Option Int := none) : Game :=
  let g := g.foldControlledPermanents p excludeId fun g o =>
    g.putMatchingSourceTriggers p o event (lastKnownPower := lastKnownPower) (cause := cause)
  -- Emblems in the command zone trigger too (CR 114.4).
  (g.objects.filter (fun o => o.zone == .command && o.controlledBy p)).foldl
    (fun g e => g.putMatchingSourceTriggers p e event
      (lastKnownPower := lastKnownPower) (cause := cause)) g

/-- Queue `p`'s triggered abilities whose Reality Fracture event satisfies
`pred`, with `cause` as the object that caused them. -/
def putFraEventTriggersWhere (g : Game) (p : PlayerId) (pred : FraEvent → Bool)
    (cause : Option GameObject := none) (excludeId : Option ObjectId := none) : Game :=
  let fire (g : Game) (o : GameObject) : Game :=
    (o.printed.triggeredAbilities ++ o.status.grantedTriggeredAbilities).foldl (fun g ab =>
      match ab.timing.events.find? (fun e =>
          match e with
          | .fra fe => pred fe
          | _ => false) with
      | some e => g.queueTrigger p o ab e (cause := cause)
      | none => g) g
  let g := g.foldControlledPermanents p excludeId fire
  -- Emblems and effects in the command zone trigger too (CR 114.4).
  (g.objects.filter (fun o => o.zone == .command && o.controlledBy p)).foldl fire g

/-- Queue `p`'s triggered abilities for the Reality Fracture event `e`. -/
def putFraEventTriggers (g : Game) (p : PlayerId) (e : FraEvent)
    (cause : Option GameObject := none) (excludeId : Option ObjectId := none) : Game :=
  g.putFraEventTriggersWhere p (· == e) cause excludeId

/-- Queue “whenever you sacrifice a token” if `o` was a token when sacrificed. -/
def queueYouSacrificeToken (g : Game) (o : GameObject) : Game :=
  if !o.printed.isToken then g
  else
    match o.controller with
    | some p => g.putControlledTriggers p .youSacrificeToken
    | none => g.putControlledTriggers o.owner .youSacrificeToken

/-- Sacrifice `o` to its owner's graveyard and fire token-sacrifice triggers. -/
def sacrificeToGraveyard (g : Game) (o : GameObject) (reason : String) : Game :=
  let g := g.moveToOwnerGraveyard o reason
  g.queueYouSacrificeToken o

/-- Cards of `subtype` in `p`'s graveyard (Thranduil-style copies). -/
def graveyardCardsOfSubtype (g : Game) (p : PlayerId) (subtype : String) :
    Array GameObject :=
  (g.player p).graveyard.filterMap (fun id =>
    match g.findObject? id with
    | some card =>
      if card.printed.hasSubtype subtype then some card else none
    | none => none)

/-- Collect `sel` from graveyard cards named by `copyActivatedFromGySubtype`. -/
def copiedFromGy {α : Type} (g : Game) (o : GameObject) (sel : CardDef → Array α) :
    Array α :=
  if !o.isOnBattlefield then #[]
  else
    match o.controller with
    | none => #[]
    | some p =>
      o.staticAbilities.foldl (fun acc sa =>
        match sa with
        | .copyActivatedFromGySubtype subtype =>
          (g.graveyardCardsOfSubtype p subtype).foldl
            (fun acc card => acc ++ sel card.printed) acc
        | _ => acc) #[]

/-- Printed activated abilities plus those copied from the graveyard. -/
def activatedAbilitiesOf (g : Game) (o : GameObject) : Array ActivatedAbility :=
  let own :=
    if !g.retainsPrintedAbilities o then #[]
    else
      o.printed.activatedAbilities ++ g.copiedFromGy o (·.activatedAbilities) ++
        (o.printed.crew.map ActivatedAbility.crewAbility).toArray ++
        (if o.printed.hasBoast then #[ActivatedAbility.zemoBoastAbility] else #[])
  -- Loyalty abilities granted to planeswalkers you control (Way of the
  -- Healer and similar). A planeswalker still activates only one loyalty
  -- ability per turn, however many it has (ruling 779).
  let granted :=
    if o.isOnBattlefield && o.printed.isPlaneswalker then
      match o.controller with
      | some p => (g.permanentsOf p).foldl (fun acc src =>
          acc ++ src.printed.planeswalkersYouControlHave) #[]
      | none => #[]
    else #[]
  own ++ granted

/-- True when `p` controls a basic land (CR 205.4c / 305.8). -/
def controlsBasicLand (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => isBasicLandCard o.printed)

/-- Hidden Lair's colored add ability: this land entered this turn, or you
control a basic land. -/
def canUseEnteredOrBasicAdd (g : Game) (o : GameObject) : Bool :=
  o.status.enteredThisTurn ||
    match o.controller with
    | some p => g.controlsBasicLand p
    | none => false

/-- Mana types other permanents currently grant `o` (`{T}: Add`). -/
def grantedManaAbilities (g : Game) (o : GameObject) : Array ManaType :=
  if !o.isOnBattlefield then #[]
  else
    match o.controller with
    | none => #[]
    | some p =>
      let fromLords :=
        (g.permanentsOf p).foldl (fun acc src =>
          if src.id == o.id then acc
          else
            src.staticAbilities.foldl (fun acc ab =>
              match ab with
              | .otherSubtypeHaveTapAddOneOf subtypes mana =>
                if subtypes.any (g.hasSubtype o) then
                  mana.foldl (fun acc t =>
                    if acc.contains t then acc else acc.push t) acc
                else acc
              | _ => acc) acc) #[]
      let anyColor : Array ManaType :=
        #[.colored .white, .colored .blue, .colored .black,
          .colored .red, .colored .green]
      if o.isCreature &&
          (g.permanentsOf p).any (fun src => src.printed.grantCreaturesTapAddAnyColor) then
        anyColor.foldl (fun acc t =>
          if acc.contains t then acc else acc.push t) fromLords
      else fromLords

/-- Mana types Reality Fracture mana abilities of `o` produce, including the
`{T}: Add {C}{C}` Emrakul, the Exigent Doom grants a land. -/
def fraManaAbilities (o : GameObject) : Array ManaType :=
  let anyColor : Array ManaType :=
    #[.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
  let own := o.staticAbilities.foldl (fun acc ab =>
    match ab with
    | .fra .tapAddColorlessNotFromHand => acc.push .colorless
    | .fra .tapAddAnyColorPlaneswalkerOnly => acc ++ anyColor
    | .fra .tapSacrificeAddThreeOfOneColor => acc ++ anyColor
    | .fra .tapAddChosenColor =>
      match o.status.chosenColor with
      | some c => acc.push (.colored c)
      | none => acc
    | _ => acc) #[]
  if o.isOnBattlefield && !o.status.colorlessGrantUntilCast.isEmpty && !own.contains .colorless then
    own.push .colorless
  else own

/-- The spending restriction on mana `o` adds when tapped for `mana`. -/
def fraManaUseOf (g : Game) (o : GameObject) (mana : ManaType) : Option FraManaUse :=
  if mana == .colorless && !o.status.colorlessGrantUntilCast.isEmpty then none
  else
    match o.staticAbilities.findSome? (fun ab =>
        match ab with
        | .fra s => s.manaUse?
        | _ => none) with
    | some u => some u
    | none => if g.hasSubtype o "Treasure" then some .fromTreasure else none

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
      { g with pending := .chooseTargets e.controller }.logMsg msg
  | none => g

/-- Triggers waiting to be put on the stack for `event`. -/
def waitingFor (g : Game) (event : TriggerEvent) : Array WaitingTrigger :=
  g.waitingTriggers.filter (·.event == event)

/-- One “whenever one or more other creatures die” trigger per source
(CR 603.2a / 603.3b). -/
def dedupWaitingTriggers (wts : Array WaitingTrigger) : Array WaitingTrigger :=
  wts.foldl (fun acc wt =>
    if wt.event == .oneOrMoreOtherCreaturesDie &&
        acc.any (fun w =>
          w.event == .oneOrMoreOtherCreaturesDie && w.source.id == wt.source.id) then
      acc
    else acc.push wt) #[]

/-- CR 603.3b: part 1 is every waiting trigger whose condition is not another
ability triggering; part 2 is the remainder. -/
def waitingTriggersPart (g : Game) (part2 : Bool) : Array WaitingTrigger :=
  g.waitingTriggers.filter (fun wt => wt.event.isAnotherAbilityTriggering == part2)
    |> dedupWaitingTriggers

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

/-- Remove `wt` from the waiting list. A “one or more other creatures die”
trigger consumes every queued copy from the same source. -/
def removeWaitingTrigger (g : Game) (wt : WaitingTrigger) : Game :=
  if wt.event == .oneOrMoreOtherCreaturesDie then
    { g with waitingTriggers :=
      g.waitingTriggers.filter (fun w =>
        !(w.event == .oneOrMoreOtherCreaturesDie && w.source.id == wt.source.id)) }
  else
    match g.waitingTriggers.findIdx? (fun w =>
      w.controller == wt.controller && w.source.id == wt.source.id &&
        w.ability == wt.ability && w.event == wt.event &&
        w.causeId == wt.causeId) with
    | none => g
    | some i => { g with waitingTriggers := g.waitingTriggers.eraseIdx! i }

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
      wt.lastKnownToughness (cause := wt.cause)
  if wt.checked then put g
  else
    let live := g.findObject? wt.source.id
    let status := (live.map (·.status)).getD wt.source.status
    if wt.ability.onceEachTurn && status.firedOnceEachTurn then g
    else if wt.ability.optionalOnceEachTurn && status.optionalOnceUsed then g
    else if !g.triggerConditionHolds wt.controller wt.ability wt.cause (some wt.source) then g
    else
      let g :=
        match live with
        | some o =>
          if wt.ability.onceEachTurn then
            g.setObject { o with status := { o.status with firedOnceEachTurn := true } }
          else g
        | none => g
      let copies := g.extraTriggerCopies wt.controller wt.source + 1
      (List.range copies).foldl (fun g _ => put g) g

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
  let waiting :=
    let raw := g.waitingFor event
    if event == .oneOrMoreOtherCreaturesDie then
      raw.foldl (fun acc wt =>
        if acc.any (fun w => w.source.id == wt.source.id) then acc else acc.push wt) #[]
    else raw
  if waiting.isEmpty then g
  else
    Id.run do
      let mut g := { g with waitingTriggers := g.waitingTriggers.filter (·.event != event) }
      for wt in waiting do
        g := g.putWaitingTrigger wt event
      return g.promptTriggerTargetsIfNeeded

/-- CR 704.3 / 603.3b: check state-based actions, then put waiting triggers
on the stack in APNAP order (each player choosing the order of their own).
After that batch, check state-based actions again. Repeat until idle, then
`p` receives priority. `recheckSba` is false while still placing the current
batch (targets or the next player's triggers). -/
partial def receivePriority (g : Game) (p : PlayerId) (recheckSba := true) : Game :=
  let p := g.priorityInstead p
  let g := if recheckSba then g.checkSBA else g
  if g.over then g
  -- CR 704.3 / 704.5j: a required legend-rule choice is part of performing
  -- the SBA. Do not put triggers on the stack or grant priority yet.
  else if g.legendChoicePending? then g
  else if g.pending != .none then g
  else
    match g.nextTriggerStackingPlayer? with
    | none =>
      if g.waitingTriggers.isEmpty then
        if recheckSba then
          { g with priority := p, consecutivePasses := 0 }
        else
          -- Finished this CR 603.3b pass; check SBAs and any new triggers.
          receivePriority g p true
      else
        let g := g.putTriggerBatch g.currentTriggerBatch
        if g.over || g.pending != .none then g
        else receivePriority g p true
    | some q =>
      let mine := g.waitingTriggersOf q
      if mine.size ≤ 1 then
        let g := g.putTriggerBatch mine
        if g.over || g.pending != .none then g
        else receivePriority g p false
      else
        { g with pending := .chooseTriggerToStack q }.logMsg
          s!"{(g.player q).name} chooses the order of triggered abilities (CR 603.3b)"

/-- Put enters-the-battlefield triggers of `o` onto the stack (CR 603.6a).
Abilities that require a target and have none are removed (CR 603.3d). -/
def putEnterTriggersOnStack (g : Game) (o : GameObject) : Game :=
  match o.controller with
  | none => g
  | some p =>
    Id.run do
      let mut g := g
      g := g.putMatchingSourceTriggers p o .entering
      return g.promptTriggerTargetsIfNeeded

/-- Put controlled triggers for `event` onto the stack, then prompt for targets
if a trigger requires them (CR 603.3d). -/
def putControlledTriggersWithPrompt (g : Game) (p : PlayerId) (event : TriggerEvent)
    (excludeId : Option ObjectId := none) : Game :=
  g.putControlledTriggers p event excludeId |>.promptTriggerTargetsIfNeeded

/-- Put “whenever a land you control enters” triggers onto the stack (CR 603.6a).
Abilities that require a target and have none are removed (CR 603.3d). -/
def putLandYouControlEntersTriggers (g : Game) (land : GameObject) : Game :=
  if !land.printed.isLand then g
  else
    match land.controller with
    | none => g
    | some landController =>
      -- “Return this card from your graveyard” works only from the graveyard
      -- (CR 113.6k); other landfall abilities only on the battlefield.
      let fromGraveyard (ab : TriggeredAbility) : Bool :=
        match ab.shared with
        | .payReturnFromGy => true
        | _ => false
      let g := (g.foldControlledPermanents landController none fun g o =>
        g.putMatchingSourceTriggers landController o .landYouControlEnters
          (cause := some land) (keep := (!fromGraveyard ·))).promptTriggerTargetsIfNeeded
      let g :=
        if g.hasSubtype land "Mountain" then
          g.putControlledTriggers landController .mountainYouControlEnters
        else g
      let g :=
        if g.hasSubtype land "Forest" then
          (g.foldControlledPermanents landController none fun g o =>
            g.putMatchingSourceTriggers landController o .forestYouControlEnters
              (cause := some land)).promptTriggerTargetsIfNeeded
        else g
      (g.player landController).graveyard.foldl (fun acc id =>
        match acc.findObject? id with
        | none => acc
        | some o =>
          acc.putMatchingSourceTriggers landController o .landYouControlEnters
            (keep := fromGraveyard)) g

end Game
end Mtg.Engine
