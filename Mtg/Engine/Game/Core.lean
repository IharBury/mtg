import Mtg.Engine.Game.Event
import Mtg.Engine.Game.Player

/-!
# Game state core

The `Game` structure itself and basic accessors: players, opponents, and
turn order, object lookup, battlefield queries, restoring expired copy
effects, and who controls, sees, or decides for whom
(CR 800.4 / MSH player control).
-/

namespace Mtg.Engine

structure Game where
  players : Array Player := #[]
  objects : Array GameObject := #[]
  stack : Array StackEntry := #[]
  activePlayer : PlayerId := ⟨0⟩
  priority : PlayerId := ⟨0⟩
  step : Step := .untap
  turnNumber : Nat := 1
  startingPlayer : PlayerId := ⟨0⟩
  isFirstTurn : Bool := true
  pending : Pending := .none
  nextObjectId : Nat := 0
  /-- Next unique effect identifier (CR 610 / 611), independent of `nextObjectId`. -/
  nextEffectId : Nat := 0
  /-- Next unique batch identifier for simultaneous rules events (CR 603.2c / 608.2c / 704.3). -/
  nextBatchId : Nat := 0
  /-- Active batch `(batchId, sharedCause?)` while recording simultaneous rules events. -/
  currentBatch : Option (BatchId × Option EventCause) := none
  /-- Pre-batch state captured when an outermost rules-event batch opens so it can
  close and evaluate CR 603.10 look-back triggers after `Pending.chooseReplacement` finishes. -/
  openBatchObjects : Array GameObject := #[]
  openBatchPlayers : Array Player := #[]
  openBatchEffects : Array (EffectId × ContinuousEffect) := #[]
  openBatchPending : Pending := .none
  /-- Active continuous effects paired with their unique `EffectId` (CR 611). -/
  activeEffects : Array (EffectId × ContinuousEffect) := #[]
  timestamp : Nat := 0
  /-- Continuation after a random result is applied. -/
  afterRandom : AfterRandom := .none
  result : Option GameResult := none
  log : Array String := #[]
  format : Format := .constructed
  /-- CR 903.12 Brawl option (free first mulligan, CR 103.5c / 903.12g). -/
  brawl : Bool := false
  consecutivePasses : Nat := 0
  /-- Set when CR 514.3a grants priority during the current cleanup step. -/
  cleanupGivesPriority : Bool := false
  /-- Until-end-of-turn continuous effect: creatures without flying can't
  block (e.g. Fire of Orthanc). Cleared in cleanup (CR 514.2 / 611.2a). -/
  creaturesWithoutFlyingCantBlock : Bool := false
  /-- Spell or ability proposed and waiting for mana abilities / payment
  (CR 601.2f–h / 602.2b). -/
  proposedSpell : Option ProposedSpell := none
  /-- Opening hands are kept and a “may begin on the battlefield” choice is
  still unfinished. The first turn starts when that choice ends. -/
  awaitingOpeningBegin : Bool := false
  /-- Players still to declare keep-or-mulligan in the current CR 103.5 round. -/
  mulliganToDeclare : Array PlayerId := #[]
  /-- Players who declared they will mulligan this round; taken together after
  every remaining player has declared (CR 103.5). -/
  willMulligan : Array PlayerId := #[]
  /-- Players who still must put cards on the bottom after simultaneous mulligans. -/
  mulliganToBottom : Array PlayerId := #[]
  /-- Combat damage assigned this step and not yet dealt (CR 510.1 / 510.2). -/
  assignedCombatDamage : Array CreatureCombatAssignment := #[]
  /-- Defending players who still must declare blockers, in APNAP order
  (CR 509.1 / 802). -/
  blockersQueue : Array PlayerId := #[]
  /-- Triggered abilities waiting to be put onto the stack the next time a
  player would receive priority (CR 603.3 / 603.3b). Distinguished by
  `WaitingTrigger.event`. -/
  waitingTriggers : Array WaitingTrigger := #[]
  /-- True after a first-strike combat damage step has been dealt this combat
  (CR 702.7b). Cleared when combat ends. -/
  firstStrikeDamageDone : Bool := false
  /-- After first-strike damage, a regular combat damage step is still pending
  (CR 702.7b). -/
  pendingRegularCombatDamage : Bool := false
  /-- Creatures that assigned first-strike combat damage this combat. They
  assign regular damage only if they have double strike (Okoye; MSH 173). -/
  firstStrikeAssignedThisCombat : Array ObjectId := #[]
  /-- It is night (CR 731 / 702.145). Used by Nick Fury / daybound (MSH 191). -/
  isNight : Bool := false
  /-- Draw these cards after the current scry finishes (e.g. Hithlain Knots). -/
  pendingDrawAfterScry : Option (PlayerId × Nat) := none
  /-- Card discarded while a later `.put .discardedLand (how := .tapped)`
  may put that land onto the battlefield tapped (Silvan Reveler). The
  player who discarded it, and the card. -/
  discardedCardThisWay : Option (PlayerId × ObjectId) := none
  /-- After Palantír of Orthanc finishes scrying, this opponent may have
  the controller draw. Stores controller, opponent, and the Palantír. -/
  palantirAfterScry : Option (PlayerId × PlayerId × ObjectId) := none
  /-- The spell whose effect is currently resolving (CR 608.2). -/
  resolvingSpell : Option ObjectId := none
  /-- The activated or triggered ability currently resolving. -/
  resolvingAbility : Option ObjectId := none
  /-- Tokens created by the most recent `createKindTokens` call, so a following
  sequence step can haste them or leave them out of a plus-one. -/
  recentTokenIds : Array ObjectId := #[]
  /-- Work left after the pending scry or surveil finishes (Eye of Jace):
  its controller, source, and what to do. -/
  fraAfterLook : Option (PlayerId × Option ObjectId × FraNext) := none
  /-- Copies a player may still cast without paying their mana costs as an
  ability resolves, with the mana value left (Uldaros Theorix). -/
  pendingFreeCopies : Option (PlayerId × Array ObjectId × Nat × Nat) := none
  /-- Spells exiled by a resolving ability that may still be cast without
  paying their mana costs, and how many casts remain (Doom Reigns Supreme). -/
  pendingMayCastFromExile : Option (PlayerId × Array ObjectId × Nat) := none
  /-- Paying the pending “you may pay” cost also puts a +1/+1 counter on this
  permanent (Proft, Consulting Detective). -/
  mayPayAlsoPlusOneOn : Option ObjectId := none
  /-- Humans chosen for the current “tap any number of Humans” step.
  `.draw (amount := .forEachTappedHuman)` draws this many cards. -/
  humansTappedThisWay : Nat := 0
  /-- Permanents destroyed by `.destroy .oppArtifactsEnchantments (note := .countDestroyed)`.
  `.gainLife .forEachDestroyedThisWay` gains this much life. -/
  permanentsDestroyedThisWay : Nat := 0
  /-- A hope counter was removed by the current `removeCounters .hope .source` step.
  `«if» .removedHope` draws a card when this is set. -/
  removedHopeThisWay : Bool := false
  /-- The permanent marked by the current `dealDamage` step when it notes
  `.markedPermanent`. `«if» (.dealtDamageToSubtype _)` destroys it when it
  has the subtype. -/
  permanentDealtDamageThisWay : Option ObjectId := none
  /-- A permanent was returned to its owner's hand by the current
  `returnToHand` step when it notes `.returnedPermanent`.
  `«if» .returnedPermanent` puts a +1/+1 counter on the source when this is set. -/
  returnedPermanentThisWay : Bool := false
  /-- Ordinal recorded by the current `noteResolveThisTurn` step.
  `«if» (.nthResolve _)` reads it and a finished sequence clears it. -/
  nthResolveThisWay : Option Nat := none
  /-- The current sequence step asked the rest of the sequence not to run
  (the source had already left, or no mana was spent). -/
  skipTriggerSequenceRest : Bool := false
  /-- Excess damage noted by `dealDamage` with `.excess` for the following
  amass step. -/
  excessDamageThisWay : Nat := 0
  /-- `.destroy .target (note := .forAmass)` chose a legal target. The controller,
  amount, and whether you controlled it feed the following amass and draw steps. -/
  destroyedForAmassThisWay : Bool := false
  amassControllerThisWay : Option PlayerId := none
  amassAmountThisWay : Nat := 0
  amassYouControlledThisWay : Bool := false
  /-- Cards milled by `.mill` when it notes `.milledCards`. -/
  milledIdsThisWay : Array ObjectId := #[]
  /-- Cards `revealLibrary` just showed. A following step reads them. -/
  revealedIdsThisWay : Array ObjectId := #[]
  /-- `.mill` noted `.opponentsMilled`: an opponent milled at least one card. -/
  opponentsMilledThisWay : Bool := false
  /-- Palantír finished putting an influence counter; the following step offers
  the opponent's draw choice. Controller, opponent, and the Palantír. -/
  palantirChoiceReady : Option (PlayerId × PlayerId × ObjectId) := none
  /-- `revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`
  stored the impulse. The following `.mayCast .impulse` offers the cast. -/
  grimaImpulseReady : Bool := false
  grimaImpulseVictim : Option PlayerId := none
  grimaImpulseFound : Option ObjectId := none
  grimaImpulseOthers : Array ObjectId := #[]
  /-- `sacrifice .you .plan .forReflexive` sacrificed the Plan. -/
  planWasSacrificed : Bool := false
  /-- `sacrifice .you .source .noted` sacrificed the source. -/
  sourceWasSacrificed : Bool := false
  /-- Lands exiled by `exile .landsYouControl .forLater .lands`.
  `.put .notedLands (how := .tapped)` returns them. -/
  exiledIdsThisWay : Array ObjectId := #[]
  /-- Creature exiled by `exile .target .untilSourceLeaves .copyAndHost`, copied by the next step.
  The object is the one from before it moved. -/
  notedCopyObject : Option GameObject := none
  notedHostId : Option ObjectId := none
  /-- Cards discarded by accepting `.discard .hand`. `none` means declined. -/
  handDiscardedThisWay : Option Nat := none
  /-- Source of the Balin ability, for the damage step after the discard. -/
  notedSourceThisWay : Option ObjectId := none
  /-- Creature that received Equipment from `attach .anyYouControl .target`. -/
  equipmentAttachedHost : Option ObjectId := none
  /-- A count captured before a later step could change it (invasion counters,
  cards discarded). -/
  notedCountThisWay : Nat := 0
  /-- Token created for the following attach or counter step. -/
  createdTokenThisWay : Option ObjectId := none
  /-- Artifact put from hand by `.put .artifactFromHand (note := .forAttach)`,
  and the creature `attach .putArtifact .notedHost` attaches it to when it
  is Equipment. -/
  putArtifactThisWay : Option (ObjectId × ObjectId) := none
  /-- Card exiled by `exile .graveyardCard .forLater .playCard`. -/
  playExiledThisWay : Option ObjectId := none
  /-- The following `surveil` returns a card with mana value at most the life
  gained this turn (ruling 750). -/
  armSurveilReturn : Bool := false
  /-- Later steps of a trigger `sequence`, waiting on the pending choice an
  earlier step opened. -/
  triggerSequenceRest : Option TriggerSequenceRest := none
  /-- Flattened steps of the `mayThen` conditional waiting in
  `triggerSequenceRest`. Declining the optional action drops this many. -/
  mayThenDrop : Nat := 0
  /-- After an optional `mayThen` action cannot be performed, the sequence
  fold skips this many following steps. -/
  mayThenSkip : Nat := 0
  /-- Conditional of the `mayThen` currently offered. The optional action
  reads it for its log and which choice to open. -/
  mayThenConditional : Option TriggeredAbility.TriggerResolution := none
  /-- Accepting `Pending.mayResolve` applies this trigger resolution.
  The ability context is `mayContext`. -/
  mayOnAccept : Option TriggeredAbility.TriggerResolution := none
  /-- Declining `Pending.mayResolve` applies this trigger resolution
  instead of `mayOnAccept`. -/
  mayOnDecline : Option TriggeredAbility.TriggerResolution := none
  /-- Ability context for `mayOnAccept` and `mayOnDecline`. -/
  mayContext : Option TriggerSequenceRest := none
  /-- Power of the creature sacrificed for
  `putCounters .plusOneSacrificedPower`. -/
  sacrificedPowerThisWay : Option Nat := none
  /-- An artifact-or-discard cost accepted a `mayThen`. The action handler
  resumes the conditional. -/
  mayThenResume : Bool := false
  /-- Alternatives for a pending `TriggerResolution.or`. `chooseMode` applies
  that index. -/
  triggerOr : Option TriggerOrRest := none
  /-- Context for a pending Alliance or Gollum mode choice. `chooseMode`
  applies that index of `modes`. -/
  chooseModesRest : Option ChooseModesRest := none
  /-- Declining `payOrLetCounter` resolves this effect instead of countering.
  The caster is `unlessPaysController`; `unlessPaysTargets` are the targets
  announced for that effect. -/
  unlessPaysInstead : Option Effect := none
  unlessPaysController : PlayerId := ⟨0⟩
  unlessPaysTargets : Array Target := #[]
  /-- The payer left without paying (CR 800.4f). `flushUnlessPays` resolves
  `unlessPaysInstead`. -/
  unlessPaysDue : Bool := false
  /-- Accepting `mayResolve` resolves this effect. The controller is
  `mayController`; `mayTargets` are the targets announced for that effect. -/
  mayEffect : Option Effect := none
  mayController : PlayerId := ⟨0⟩
  mayTargets : Array Target := #[]
  /-- Alternatives for a pending `SpellResolution.or`. `chooseTop` applies
  the first and `chooseBottom` the second. `chooseMode` applies that index.
  Library top and bottom are stored in that order when `spellOrLibrary`. -/
  spellOr : Array Effect := #[]
  spellOrController : PlayerId := ⟨0⟩
  spellOrTargets : Array Target := #[]
  /-- `chooseTop` and `chooseBottom` name the library side, not list order
  written by the card. The stashed effects are still top then bottom. -/
  spellOrLibrary : Bool := false
  /-- After the pending surveil, a card with mana value at most this put into
  the graveyard goes to its owner's hand (Enlightened Confidant). -/
  surveilReturnMvAtMost : Option Nat := none
  /-- A noncreature, nonland card put into the graveyard by the pending
  surveil goes to its owner's hand (Chandra, Chill of Compliance). -/
  surveilReturnNoncreatureNonland : Bool := false
  /-- Ordered `ReplacementId` preferences supplied by players via `chooseReplacement`
  (CR 616.1); consulted by the replacement/prevention loop when multiple
  candidates tie in the lowest applicable priority tier (CR 616.1a–e). -/
  replacementOrder : Array ReplacementId := #[]
  /-- Continuation for an event paused on `Pending.chooseReplacement` (CR 616.1). -/
  pendingReplacement : Option PendingReplacement := none
  /-- True while a spell is being cast from the top of a library
  (Elven Chorus cannot show the new top until that finishes). -/
  castingFromTop : Bool := false
  /-- Cards in exile that return at the beginning of the next end step
  (Roll-Roll-Roll-Roll and similar delayed blinks), with the cause of the
  delayed triggered ability (CR 603.7). -/
  delayedEndStepReturns : Array (ObjectId × EventCause) := #[]
  /-- Extra turns to take before the next player in turn order (Kang). -/
  extraTurns : Array PlayerId := #[]
  /-- Power-up abilities can't be activated during this extra turn (Kang). -/
  powerUpsForbidden : Bool := false
  /-- Permanents exiled at the beginning of the next end step (Vindictive
  Triumph), with the cause of the delayed triggered ability (CR 603.7). -/
  delayedEndStepExiles : Array (ObjectId × EventCause) := #[]
  /-- Source of the current connive action, if any (MSH / CR 701.47). -/
  conniveSource : Option ObjectId := none
  /-- Put a +1/+1 counter on this permanent after the current discard choices
  finish (Ninja of the Hand). -/
  plusOneAfterDiscards : Option ObjectId := none
  /-- Extra combat phases still to begin after the current combat (Hulk enrage). -/
  additionalCombatPhases : Nat := 0
  /-- Enrage triggers that will grant an additional combat when they resolve. -/
  enrageGrantsAdditionalCombat : Nat := 0
  /-- Damage assigned to each target of the resolving divided-damage ability
(CR 601.2d). -/
  resolvingDivision : Array Nat := #[]
  /-- Player-controlling effect: (you, the player you control). Last created
  wins (MSH 259). -/
  playerControl : Option (PlayerId × PlayerId) := none
  /-- If the controlled player skips their next turn, control applies to the
  next turn they actually take (MSH 221). -/
  controlOnNextTakenTurn : Bool := false
  /-- Loki delayed copy: (controller, Loki's id if still known, last-known
  power). Compared at cast time (MSH 109). -/
  pendingLokiCopy : Option (PlayerId × Option ObjectId × Int) := none
  /-- Until EOT, this player's creatures with toughness greater than power
  assign combat damage equal to toughness (The Kingpin of Crime; MSH 287). -/
  assignCombatDamageEqualToughness : Option PlayerId := none
  /-- World War Hulk chapter I: the next red or green creature spell this
  player casts this turn may be cast without paying its mana cost (MSH 343). -/
  pendingFreeRGCreature : Option PlayerId := none
  /-- After the current library search shuffles, put a +1/+1 counter on this
  creature if it is still a creature (Restorative Technique). -/
  plusOneAfterSearch : Option ObjectId := none
  /-- Remaining discards for Thirst for Knowledge (MSH 344). An artifact
  card finishes the requirement early. -/
  thirstDiscardsLeft : Nat := 0
  /-- Discarding a card of this type finishes `thirstDiscardsLeft` early. -/
  thirstDiscardType : CardType := .artifact
  /-- Remaining discards for a required multi-card discard such as “discard
  two cards”. Unlike `thirstDiscardsLeft`, an artifact does not end this
  early. -/
  pendingDiscardsLeft : Nat := 0
  /-- Ward payments still to announce after the current one (CR 702.21). -/
  wardQueue : Array WardObligation := #[]
  /-- Permanents sacrificed at the beginning of the next end step, with the
  cause of the delayed triggered ability (CR 603.7). -/
  delayedEndStepSacrifices : Array (ObjectId × EventCause) := #[]
  /-- Graveyard cards that return under a chosen player at the next end step,
  with the cause of the delayed triggered ability (CR 603.7). -/
  delayedGraveReturns : Array (ObjectId × PlayerId × EventCause) := #[]
  /-- At the next end step, reveal this many creature cards (Synthetic Destiny),
  with the cause of the delayed triggered ability (CR 603.7). -/
  delayedSynthetic : Array (PlayerId × Nat × EventCause) := #[]
  /-- Delayed Bird Soldier token batches `(player, count, cause)` queued for the
  beginning of the next upkeep (CR 603.7; The Eagles Are Coming!). -/
  eaglesBirdsCauses : Array (PlayerId × Nat × EventCause) := #[]
  /-- Exiling one-shot `EventCause` for each card in `linkedExile`, used when
  the card returns because the source leaves the battlefield (CR 610.3). -/
  linkedExileCauses : Array (ObjectId × EventCause) := #[]
  /-- After the current search, untap the land if its controller has this many lands. -/
  untapSearchedIfLands : Option Nat := none
  /-- Lands tapped for commander-identity mana that scries a matching creature. -/
  ancestryLandsTapped : Array ObjectId := #[]
  /-- Active resolving source object id and controller across pending resolution
  choices and delayed triggered abilities (CR 608 / 610.1). -/
  resolvingContext : Option (Option ObjectId × PlayerId) := none
  /-- State changes that happened this game, oldest first (CR 603.2 / 614.1).
  Conditions ask this log whether an action happened. Triggers and
  replacement effects match the same events. A replaced change is not
  recorded (CR 614.6). -/
  events : Array GameEvent := #[]
deriving Repr, Inhabited

/-- Pre-batch game state snapshot for CR 603.10 look-back trigger evaluation. -/
abbrev GameSnapshot := Game

namespace Status

/-- Apply one `CounterDelta` of `kind` directly to `s` (CR 122.1). -/
def applyCounterDelta (s : Status) (kind : CounterKind) (delta : CounterDelta) : Status :=
  let kw (f : KeywordCounters → KeywordCounters) : Status :=
    { s with keywordCounters := f s.keywordCounters }
  match delta with
  | .put n =>
    match kind with
    | .plusOnePlusOne =>
      { s with
        plusOnePlusOne := s.plusOnePlusOne + n
        gotPlusOneThisTurn := s.gotPlusOneThisTurn || n > 0 }
    | .minusOneMinusOne => { s with minusOneMinusOne := s.minusOneMinusOne + n }
    | .loyalty => { s with loyaltyCounters := s.loyaltyCounters + n }
    | .hope => { s with hope := s.hope + n }
    | .charge => { s with charge := s.charge + n }
    | .stun => { s with stun := s.stun + n }
    | .shield => { s with shield := s.shield + n }
    | .finality => { s with finality := s.finality + n }
    | .plan => { s with plan := s.plan + n }
    | .burden => { s with burden := s.burden + n }
    | .quest => { s with quest := s.quest + n }
    | .invasion => { s with invasion := s.invasion + n }
    | .influence => { s with influence := s.influence + n }
    | .trample => { s with trampleCounters := s.trampleCounters + n }
    | .indestructible => { s with indestructibleCounters := s.indestructibleCounters + n }
    | .lifelink => { s with lifelinkCounters := s.lifelinkCounters + n }
    | .hone => { s with hone := s.hone + n }
    | .shadow => { s with shadow := s.shadow + n }
    | .lore => { s with lore := s.lore + n }
    | .story => { s with story := s.story + n }
    | .time => { s with time := s.time + n }
    | .haste => kw fun k => { k with haste := k.haste + n }
    | .vigilance => kw fun k => { k with vigilance := k.vigilance + n }
    | .flying => kw fun k => { k with flying := k.flying + n }
    | .menace => kw fun k => { k with menace := k.menace + n }
    | .reach => kw fun k => { k with reach := k.reach + n }
    | .deathtouch => kw fun k => { k with deathtouch := k.deathtouch + n }
    | .firstStrike => kw fun k => { k with firstStrike := k.firstStrike + n }
    | .doubleStrike => kw fun k => { k with doubleStrike := k.doubleStrike + n }
    | .poison => { s with poison := s.poison + n }
  | .removed n =>
    match kind with
    | .plusOnePlusOne => { s with plusOnePlusOne := s.plusOnePlusOne - n }
    | .minusOneMinusOne => { s with minusOneMinusOne := s.minusOneMinusOne - n }
    | .loyalty => { s with loyaltyCounters := s.loyaltyCounters - n }
    | .hope => { s with hope := s.hope - n }
    | .charge => { s with charge := s.charge - n }
    | .stun => { s with stun := s.stun - n }
    | .shield => { s with shield := s.shield - n }
    | .finality => { s with finality := s.finality - n }
    | .plan => { s with plan := s.plan - n }
    | .burden => { s with burden := s.burden - n }
    | .quest => { s with quest := s.quest - n }
    | .invasion => { s with invasion := s.invasion - n }
    | .influence => { s with influence := s.influence - n }
    | .trample => { s with trampleCounters := s.trampleCounters - n }
    | .indestructible => { s with indestructibleCounters := s.indestructibleCounters - n }
    | .lifelink => { s with lifelinkCounters := s.lifelinkCounters - n }
    | .hone => { s with hone := s.hone - n }
    | .shadow => { s with shadow := s.shadow - n }
    | .lore => { s with lore := s.lore - n }
    | .story => { s with story := s.story - n }
    | .time => { s with time := s.time - n }
    | .haste => kw fun k => { k with haste := k.haste - n }
    | .vigilance => kw fun k => { k with vigilance := k.vigilance - n }
    | .flying => kw fun k => { k with flying := k.flying - n }
    | .menace => kw fun k => { k with menace := k.menace - n }
    | .reach => kw fun k => { k with reach := k.reach - n }
    | .deathtouch => kw fun k => { k with deathtouch := k.deathtouch - n }
    | .firstStrike => kw fun k => { k with firstStrike := k.firstStrike - n }
    | .doubleStrike => kw fun k => { k with doubleStrike := k.doubleStrike - n }
    | .poison => { s with poison := s.poison - n }

/-- Apply one `StatusChange` in isolation (CR 110.5). -/
def applyChange (s : Status) (c : StatusChange) : Status :=
  match c with
  | .set s' => s'
  | .reset => {}
  | .addDamage n deathtouch =>
    { s with
      damage := s.damage + n
      dealtDeathtouch := s.dealtDeathtouch || (deathtouch && n > 0) }
  | .addPump p t =>
    { s with pump := (s.pump.1 + p, s.pump.2 + t) }
  | .grantUntilEot k =>
    { s with untilEotKeywords := Keywords.merge s.untilEotKeywords k }
  | .clearedAtCleanup =>
    { s with
      pump := (0, 0)
      untilEotKeywords := Keywords.none
      untilEotLosesIndestructible := false
      untilEotExileIfDies := false
      setBasePT := none
      additionalArtifactUntilEot := false
      additionalCreatureUntilEot := false
      cantBeBlockedByPlayer := none
      cantBeBlockedExceptByHasteUntilEot := false
      cantBlockUntilEot := false
      dealtDamageThisTurn := false
      replacedCreatureTypesUntilEot := none
      pumpPerArtifactUntilEot := false
      ironFistTapGrants := 0
      losesAbilitiesUntilEot := false
      grantedTriggersUntilEot := #[]
      cardsInHandPowerUntilEot := false
      firstStrikeOnYourTurn := false
      combatDamageCreatesTreasure := false }
  | .clearCombat =>
    { s with
      attacking := false
      attackingTarget := none
      blocking := #[]
      blocked := false }
  | .addBlocking attackerId =>
    { s with
      blocking :=
        if s.blocking.contains attackerId then s.blocking else s.blocking.push attackerId }
  | .removeBlocking attackerId =>
    { s with blocking := s.blocking.filter (· != attackerId) }
  | .pushAbilitiesActivated idx =>
    { s with abilitiesActivatedThisTurn := s.abilitiesActivatedThisTurn.push idx }
  | .incActivationsThisTurn =>
    { s with activationsThisTurn := s.activationsThisTurn + 1 }
  | .pushGrantedStatic sa =>
    { s with grantedStaticAbilities := s.grantedStaticAbilities.push sa }
  | .pushGrantedTriggered ta =>
    { s with grantedTriggeredAbilities := s.grantedTriggeredAbilities.push ta }
  | .pushGrantedTriggerUntilEot ta =>
    { s with grantedTriggersUntilEot := s.grantedTriggersUntilEot.push ta }
  | .pushHexproofGrantedBy id =>
    { s with hexproofGrantedBy := s.hexproofGrantedBy.push id }
  | .removeHexproofGrantedBy id =>
    { s with hexproofGrantedBy := s.hexproofGrantedBy.filter (· != id) }
  | .pushPreventDamageGrantedBy id =>
    { s with preventDamageGrantedBy := s.preventDamageGrantedBy.push id }
  | .removePreventDamageGrantedBy id =>
    { s with preventDamageGrantedBy := s.preventDamageGrantedBy.filter (· != id) }
  | .pushCantUntapGrantedBy id =>
    { s with cantUntapGrantedBy := s.cantUntapGrantedBy.push id }
  | .removeCantUntapGrantedBy id =>
    { s with cantUntapGrantedBy := s.cantUntapGrantedBy.filter (· != id) }
  | .pushLosesAbilitiesGrantedBy id =>
    { s with losesAbilitiesGrantedBy := s.losesAbilitiesGrantedBy.push id }
  | .removeLosesAbilitiesGrantedBy id =>
    { s with losesAbilitiesGrantedBy := s.losesAbilitiesGrantedBy.filter (· != id) }
  | .addAdditionalSubtype sub =>
    { s with
      additionalSubtypes :=
        if s.additionalSubtypes.any (· == sub) then s.additionalSubtypes
        else s.additionalSubtypes.push sub }
  | .pushAdditionalSubtype sub =>
    { s with additionalSubtypes := s.additionalSubtypes.push sub }
  | .pushChosenMode m =>
    { s with chosenModes := s.chosenModes.push m }
  | .pushModeChosenThisTurn m =>
    { s with modesChosenThisTurn := s.modesChosenThisTurn.push m }
  | .pushAllianceModeChosen m =>
    { s with allianceModesChosen := s.allianceModesChosen.push m }
  | .pushUntilTurnOfPump p dp dt =>
    { s with untilTurnOfPump := s.untilTurnOfPump.push (p, dp, dt) }
  | .clearUntilTurnOfPumpFor p =>
    { s with untilTurnOfPump := s.untilTurnOfPump.filter (fun (q, _, _) => q != p) }
  | .pushColorlessGrantUntilCast id =>
    { s with colorlessGrantUntilCast := s.colorlessGrantUntilCast.push id }
  | .removeColorlessGrantUntilCast id =>
    { s with colorlessGrantUntilCast := s.colorlessGrantUntilCast.filter (· != id) }
  | .addCombatDamageToPlayer p =>
    { s with
      combatDamageToPlayers :=
        if s.combatDamageToPlayers.contains p then s.combatDamageToPlayers
        else s.combatDamageToPlayers.push p }
  | .resetPerTurnFlags =>
    { s with
      activationsThisTurn := 0
      abilitiesActivatedThisTurn := #[]
      loyaltyActivatedThisTurn := false
      firedOnceEachTurn := false
      optionalOnceUsed := false
      allianceModesChosen := #[]
      declaredAsAttackerThisTurn := false
      boastUsedThisTurn := false
      becameTappedThisTurn := false
      gotPlusOneThisTurn := false
      modesChosenThisTurn := #[]
      combatDamageCreatesTreasure := false
      combatDamageToPlayers := #[]
      freeCastFromGraveyard := false }
  | .tapped v => { s with tapped := v }
  | .damage v => { s with damage := v }
  | .summoningSick v => { s with summoningSick := v }
  | .pump v => { s with pump := v }
  | .attacking v => { s with attacking := v }
  | .attackingTarget v => { s with attackingTarget := v }
  | .blocking v => { s with blocking := v }
  | .blocked v => { s with blocked := v }
  | .activationsThisTurn v => { s with activationsThisTurn := v }
  | .abilitiesActivatedThisTurn v => { s with abilitiesActivatedThisTurn := v }
  | .minusOneMinusOne v => { s with minusOneMinusOne := v }
  | .loyaltyCounters v => { s with loyaltyCounters := v }
  | .loyaltyActivatedThisTurn v => { s with loyaltyActivatedThisTurn := v }
  | .prepared v => { s with prepared := v }
  | .untilEotKeywords v => { s with untilEotKeywords := v }
  | .untilEotLosesIndestructible v => { s with untilEotLosesIndestructible := v }
  | .untilEotExileIfDies v => { s with untilEotExileIfDies := v }
  | .setBasePT v => { s with setBasePT := v }
  | .additionalCreature v => { s with additionalCreature := v }
  | .additionalSubtypes v => { s with additionalSubtypes := v }
  | .grantedStaticAbilities v => { s with grantedStaticAbilities := v }
  | .grantedTriggeredAbilities v => { s with grantedTriggeredAbilities := v }
  | .hexproofGrantedBy v => { s with hexproofGrantedBy := v }
  | .preventDamageGrantedBy v => { s with preventDamageGrantedBy := v }
  | .dealtDeathtouch v => { s with dealtDeathtouch := v }
  | .hope v => { s with hope := v }
  | .charge v => { s with charge := v }
  | .stun v => { s with stun := v }
  | .firedOnceEachTurn v => { s with firedOnceEachTurn := v }
  | .optionalOnceUsed v => { s with optionalOnceUsed := v }
  | .additionalArtifactUntilEot v => { s with additionalArtifactUntilEot := v }
  | .hone v => { s with hone := v }
  | .phasedOut v => { s with phasedOut := v }
  | .phasedWith v => { s with phasedWith := v }
  | .ringBearer v => { s with ringBearer := v }
  | .allianceModesChosen v => { s with allianceModesChosen := v }
  | .shield v => { s with shield := v }
  | .finality v => { s with finality := v }
  | .declaredAsAttackerThisTurn v => { s with declaredAsAttackerThisTurn := v }
  | .boastUsedThisTurn v => { s with boastUsedThisTurn := v }
  | .plan v => { s with plan := v }
  | .powerUpUsed v => { s with powerUpUsed := v }
  | .powerUpActivations v => { s with powerUpActivations := v }
  | .becameTappedThisTurn v => { s with becameTappedThisTurn := v }
  | .gotPlusOneThisTurn v => { s with gotPlusOneThisTurn := v }
  | .cantUntapGrantedBy v => { s with cantUntapGrantedBy := v }
  | .additionalCreatureUntilEot v => { s with additionalCreatureUntilEot := v }
  | .harnessed v => { s with harnessed := v }
  | .transformed v => { s with transformed := v }
  | .cantTransform v => { s with cantTransform := v }
  | .losesAbilitiesGrantedBy v => { s with losesAbilitiesGrantedBy := v }
  | .losesAbilitiesUntilEot v => { s with losesAbilitiesUntilEot := v }
  | .chosenModes v => { s with chosenModes := v }
  | .modesChosenThisTurn v => { s with modesChosenThisTurn := v }
  | .cardsInHandPowerUntilEot v => { s with cardsInHandPowerUntilEot := v }
  | .chosenOdd v => { s with chosenOdd := v }
  | .lore v => { s with lore := v }
  | .indestructibleCounters v => { s with indestructibleCounters := v }
  | .lifelinkCounters v => { s with lifelinkCounters := v }
  | .chosenCreatureType v => { s with chosenCreatureType := v }
  | .cantBeBlockedByPlayer v => { s with cantBeBlockedByPlayer := v }
  | .cantBeBlockedExceptByHasteUntilEot v => { s with cantBeBlockedExceptByHasteUntilEot := v }
  | .cantBlockUntilEot v => { s with cantBlockUntilEot := v }
  | .manaSpentToCast v => { s with manaSpentToCast := v }
  | .dealtDamageThisTurn v => { s with dealtDamageThisTurn := v }
  | .replacedCreatureTypesUntilEot v =>
    { s with replacedCreatureTypesUntilEot := v }
  | .pumpPerArtifactUntilEot v => { s with pumpPerArtifactUntilEot := v }
  | .influence v => { s with influence := v }
  | .onlyFoodArtifact v => { s with onlyFoodArtifact := v }
  | .burden v => { s with burden := v }
  | .quest v => { s with quest := v }
  | .invasion v => { s with invasion := v }
  | .trampleCounters v => { s with trampleCounters := v }
  | .keywordCounters v => { s with keywordCounters := v }
  | .combatDamageCreatesTreasure v => { s with combatDamageCreatesTreasure := v }
  | .returnedAsArtifact v => { s with returnedAsArtifact := v }
  | .controlUntilEot v => { s with controlUntilEot := v }
  | .controlTurnEndsLeft v => { s with controlTurnEndsLeft := v }
  | .ironFistTapGrants v => { s with ironFistTapGrants := v }
  | .untilTurnOfPump v => { s with untilTurnOfPump := v }
  | .grantedTriggersUntilEot v => { s with grantedTriggersUntilEot := v }
  | .exhaustUsed v => { s with exhaustUsed := v }
  | .colorlessGrantUntilCast v => { s with colorlessGrantUntilCast := v }
  | .chosenColor v => { s with chosenColor := v }
  | .dealtCombatDamage v => { s with dealtCombatDamage := v }
  | .combatDamageToPlayers v => { s with combatDamageToPlayers := v }
  | .animatedConstruct55 v => { s with animatedConstruct55 := v }
  | .chosenName v => { s with chosenName := v }
  | .faceDown v => { s with faceDown := v }
  | .story v => { s with story := v }
  | .time v => { s with time := v }
  | .notACreature v => { s with notACreature := v }
  | .windcragMardu v => { s with windcragMardu := v }
  | .chosenCardType v => { s with chosenCardType := v }
  | .freeCastFromGraveyard v => { s with freeCastFromGraveyard := v }
  | .isCommander v => { s with isCommander := v }
  | .firstStrikeOnYourTurn v => { s with firstStrikeOnYourTurn := v }

end Status

namespace GameObject

/-- Apply one `ObjectChange` in isolation (CR 109). -/
def applyChange (o : GameObject) (c : ObjectChange) : GameObject :=
  match c with
  | .status sc => { o with status := o.status.applyChange sc }
  | .statuses scs => { o with status := scs.foldl Status.applyChange o.status }
  | .printed v => { o with printed := v }
  | .owner v => { o with owner := v }
  | .controller v => { o with controller := v }
  | .lastController v => { o with lastController := v }
  | .defaultController v => { o with defaultController := v }
  | .controlChanged v => { o with controlChanged := v }
  | .zone v => { o with zone := v }
  | .timestamp v => { o with timestamp := v }
  | .abilityEffect v => { o with abilityEffect := v }
  | .triggeredAbility v => { o with triggeredAbility := v }
  | .reflexiveResolution v => { o with reflexiveResolution := v }
  | .sourceId v => { o with sourceId := v }
  | .lastKnownPower v => { o with lastKnownPower := v }
  | .lastKnownToughness v => { o with lastKnownToughness := v }
  | .playPermission v => { o with playPermission := v }
  | .decrementPlayTurnEnds =>
    match o.playPermission with
    | none => o
    | some perm =>
      if perm.fromAdventure || perm.whileExiled then o
      else if perm.turnEndsRemaining ≤ 1 then { o with playPermission := none }
      else { o with playPermission := some { perm with turnEndsRemaining := perm.turnEndsRemaining - 1 } }
  | .attachedTo v => { o with attachedTo := v }
  | .adventurerCard v => { o with adventurerCard := v }
  | .linkedExile v => { o with linkedExile := v }
  | .pushLinkedExile id => { o with linkedExile := o.linkedExile.push id }
  | .returnToZone v => { o with returnToZone := v }
  | .leaveTriggerExile v => { o with leaveTriggerExile := v }
  | .pushLeaveTriggerExile id => { o with leaveTriggerExile := o.leaveTriggerExile.push id }
  | .castFromGraveyard v => { o with castFromGraveyard := v }
  | .exileInstantSorceryInstead v => { o with exileInstantSorceryInstead := v }
  | .castFromHand v => { o with castFromHand := v }
  | .wasCast v => { o with wasCast := v }
  | .isPreparedSpell v => { o with isPreparedSpell := v }
  | .fraCauseId v => { o with fraCauseId := v }
  | .fraCauseController v => { o with fraCauseController := v }
  | .fraCausePower v => { o with fraCausePower := v }
  | .fraCauseStatus v => { o with fraCauseStatus := v }
  | .exiledBy v => { o with exiledBy := v }
  | .fraEffectUntilTurnOf v => { o with fraEffectUntilTurnOf := v }
  | .flashbackUntilEot v => { o with flashbackUntilEot := v }
  | .kicked v => { o with kicked := v }
  | .teamworkPaid v => { o with teamworkPaid := v }
  | .sneakPaid v => { o with sneakPaid := v }
  | .sneakAttackWhom v =>
    { o with
      sneakAttackWhom := v
      sneakAttackTarget :=
        match v with
        | some p => some (.player p)
        | none => o.sneakAttackTarget }
  | .sneakAttackTarget v => { o with sneakAttackTarget := v }
  | .giftPromisedTo v => { o with giftPromisedTo := v }
  | .isCopy v => { o with isCopy := v }
  | .uncounterableThisCast v => { o with uncounterableThisCast := v }
  | .boastExiled v => { o with boastExiled := v }
  | .enterProcessed v => { o with enterProcessed := v }
  | .treasureManaSpent v => { o with treasureManaSpent := v }
  | .chosenX v => { o with chosenX := v }
  | .copyRestore v => { o with copyRestore := v }
  | .copyUntilEot v => { o with copyUntilEot := v }
  | .copyUntilNextTurn v => { o with copyUntilNextTurn := v }
  | .copyUntilSourceLeaves v => { o with copyUntilSourceLeaves := v }
  | .controlUntilSourceLeaves v => { o with controlUntilSourceLeaves := v }
  | .restoreCopy =>
    match o.copyRestore with
    | none => o
    | some card =>
      { o with
        printed := card
        copyRestore := none
        copyUntilEot := false
        copyUntilNextTurn := false
        copyUntilSourceLeaves := none }

end GameObject

namespace Player

/-- Apply one `PlayerChange` in isolation (CR 102). -/
def applyChange (pl : Player) (c : PlayerChange) : Player :=
  match c with
  | .name v => { pl with name := v }
  | .life v => { pl with life := v }
  | .startingLife v => { pl with startingLife := v }
  | .maxHandSize v => { pl with maxHandSize := v }
  | .startingHandSize v => { pl with startingHandSize := v }
  | .manaPool v => { pl with manaPool := v }
  | .addMana t n elf inst hero villain cantNonart creature fra =>
    { pl with
      manaPool :=
        pl.manaPool.add t n
          (elfRestricted := elf) (instRestricted := inst)
          (heroRestricted := hero) (villainRestricted := villain)
          (cantNonartifact := cantNonart) (creatureRestricted := creature)
          (fra := fra) }
  | .emptyManaPool becomesColorless =>
    if becomesColorless then
      let total :=
        pl.manaPool.white + pl.manaPool.blue + pl.manaPool.black +
          pl.manaPool.red + pl.manaPool.green + pl.manaPool.colorless
      { pl with manaPool := { colorless := total } }
    else
      { pl with manaPool := {} }
  | .additionalLandsThisTurn v => { pl with additionalLandsThisTurn := v }
  | .addAdditionalLandsThisTurn n =>
    { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn + n }
  | .poison v => { pl with poison := v }
  | .addPoison n => { pl with poison := pl.poison + n }
  | .lost v => { pl with lost := v }
  | .leftTheGame v => { pl with leftTheGame := v }
  | .drewFromEmpty v => { pl with drewFromEmpty := v }
  | .mulligansTaken v => { pl with mulligansTaken := v }
  | .incMulligansTaken => { pl with mulligansTaken := pl.mulligansTaken + 1 }
  | .keptOpeningHand v => { pl with keptOpeningHand := v }
  | .library v => { pl with library := v }
  | .pushLibrary id => { pl with library := pl.library.push id }
  | .prependLibrary ids => { pl with library := ids ++ pl.library }
  | .appendLibrary ids => { pl with library := pl.library ++ ids }
  | .stripLibrary id => { pl with library := pl.library.filter (· != id) }
  | .hand v => { pl with hand := v }
  | .pushHand id => { pl with hand := pl.hand.push id }
  | .stripHand id => { pl with hand := pl.hand.filter (· != id) }
  | .graveyard v => { pl with graveyard := v }
  | .pushGraveyard id => { pl with graveyard := pl.graveyard.push id }
  | .stripGraveyard id => { pl with graveyard := pl.graveyard.filter (· != id) }
  | .enduringStory v => { pl with enduringStory := v }
  | .theRingAbilities v => { pl with theRingAbilities := v }
  | .ringBearerId v => { pl with ringBearerId := v }
  | .citysBlessing v => { pl with citysBlessing := v }
  | .hasCommander v => { pl with hasCommander := v }
  | .commanderColorIdentity v => { pl with commanderColorIdentity := v }
  | .protectionFromEverything v => { pl with protectionFromEverything := v }
  | .eaglesBirdsNextUpkeep v => { pl with eaglesBirdsNextUpkeep := v }
  | .addEaglesBirdsNextUpkeep n =>
    { pl with eaglesBirdsNextUpkeep := pl.eaglesBirdsNextUpkeep + n }
  | .beheldQualities v => { pl with beheldQualities := v }
  | .pushBeheldQuality q => { pl with beheldQualities := pl.beheldQualities.push q }
  | .cantCastSpellsThisTurn v => { pl with cantCastSpellsThisTurn := v }
  | .attackPumpPerPlainsThisTurn v => { pl with attackPumpPerPlainsThisTurn := v }
  | .addAttackPumpPerPlainsThisTurn n =>
    { pl with attackPumpPerPlainsThisTurn := pl.attackPumpPerPlainsThisTurn + n }
  | .lifeLocked v => { pl with lifeLocked := v }
  | .typeSpellCostLessThisTurn v => { pl with typeSpellCostLessThisTurn := v }
  | .pushTypeSpellCostLess t n =>
    { pl with typeSpellCostLessThisTurn := pl.typeSpellCostLessThisTurn.push (t, n) }
  | .supertypeSpellCostLessThisTurn v => { pl with supertypeSpellCostLessThisTurn := v }
  | .pushSupertypeSpellCostLess s n =>
    { pl with supertypeSpellCostLessThisTurn := pl.supertypeSpellCostLessThisTurn.push (s, n) }
  | .jaceLoyaltyAtInstantSpeed v => { pl with jaceLoyaltyAtInstantSpeed := v }
  | .legendRuleOffThisTurn v => { pl with legendRuleOffThisTurn := v }
  | .copyNextInstantSorceryThisTurn v => { pl with copyNextInstantSorceryThisTurn := v }
  | .addCopyNextInstantSorceryThisTurn n =>
    { pl with copyNextInstantSorceryThisTurn := pl.copyNextInstantSorceryThisTurn + n }
  | .decCopyNextInstantSorceryThisTurn =>
    { pl with copyNextInstantSorceryThisTurn := pl.copyNextInstantSorceryThisTurn - 1 }
  | .sideboard v => { pl with sideboard := v }
  | .removeSideboardAt idx => { pl with sideboard := pl.sideboard.eraseIdx! idx }
  | .mountainExtraRedThisTurn v => { pl with mountainExtraRedThisTurn := v }
  | .addMountainExtraRedThisTurn n =>
    { pl with mountainExtraRedThisTurn := pl.mountainExtraRedThisTurn + n }
  | .nextSpellCantBeCountered v => { pl with nextSpellCantBeCountered := v }
  | .teammate v => { pl with teammate := v }
  | .isMonarch v => { pl with isMonarch := v }
  | .lifeCantChange v => { pl with lifeCantChange := v }
  | .cantAttackJaces v => { pl with cantAttackJaces := v }
  | .commanderCreatureTypes v => { pl with commanderCreatureTypes := v }
  | .resetPerTurnFlags =>
    { pl with
      cantCastSpellsThisTurn := false
      attackPumpPerPlainsThisTurn := 0
      typeSpellCostLessThisTurn := #[]
      supertypeSpellCostLessThisTurn := #[]
      jaceLoyaltyAtInstantSpeed := false
      legendRuleOffThisTurn := false
      copyNextInstantSorceryThisTurn := 0
      mountainExtraRedThisTurn := 0
      nextSpellCantBeCountered := false
      cantAttackJaces := false }

end Player

namespace StackEntry

/-- Apply one `StackEntryChange` in isolation (CR 405). -/
def applyChange (e : StackEntry) (c : StackEntryChange) : StackEntry :=
  match c with
  | .targets v => { e with targets := v }
  | .pushTarget t => { e with targets := e.targets.push t }
  | .pushTargets ts => { e with targets := e.targets ++ ts }
  | .setTargetAt idx t => { e with targets := e.targets.set! idx t }
  | .dividedDamage v => { e with dividedDamage := v }
  | .pushDividedDamage n => { e with dividedDamage := e.dividedDamage.push n }
  | .targetsAnnounced v => { e with targetsAnnounced := v }
  | .chosenMode v => { e with chosenMode := v }
  | .extraModes v => { e with extraModes := v }
  | .pushExtraMode m => { e with extraModes := e.extraModes.push m }
  | .skippedOptionalSlots v => { e with skippedOptionalSlots := v }
  | .incSkippedOptionalSlots => { e with skippedOptionalSlots := e.skippedOptionalSlots + 1 }

end StackEntry

namespace ProposedSpell

/-- Apply one `ProposalChange` in isolation (CR 601.2f–h). -/
def applyChange (p : ProposedSpell) (c : ProposalChange) : ProposedSpell :=
  match c with
  | .cost v => { p with cost := v }
  | .addGenericCost n => { p with cost := p.cost.addGeneric n }
  | .addManaCost mc => { p with cost := ManaCost.addCost p.cost mc }
  | .reduceCostBy mc => { p with cost := p.cost.reduceByCost mc }
  | .substituteX x => { p with cost := p.cost.substituteX x }
  | .tapped v => { p with tapped := v }
  | .pushTapped id => { p with tapped := p.tapped.push id }
  | .tapSource v => { p with tapSource := v }
  | .sacrificeSource v => { p with sacrificeSource := v }
  | .needsSacrificeOther v => { p with needsSacrificeOther := v }
  | .needsDiscardCard v => { p with needsDiscardCard := v }
  | .payLife v => { p with payLife := v }
  | .discardSource v => { p with discardSource := v }
  | .abilityModes v => { p with abilityModes := v }
  | .targetKindOverride v => { p with targetKindOverride := v }
  | .kicked v => { p with kicked := v }
  | .kickerAnnounced v => { p with kickerAnnounced := v }
  | .giftTo v => { p with giftTo := v }
  | .giftAnnounced v => { p with giftAnnounced := v }
  | .teamworkPaid v => { p with teamworkPaid := v }
  | .teamworkAnnounced v => { p with teamworkAnnounced := v }
  | .activation v => { p with activation := v }
  | .loyaltyX v => { p with loyaltyX := v }
  | .removePlusOneX v => { p with removePlusOneX := v }
  | .sneakAttacker v => { p with sneakAttacker := v }

end ProposedSpell

namespace Game

/-- Update `id`'s `Status` in place if `id` is in `g.objects`. -/
def modifyStatus (g : Game) (id : ObjectId) (f : Status → Status) : Game :=
  match g.objects.findIdx? (·.id == id) with
  | some i =>
    let o := g.objects[i]!
    { g with objects := g.objects.set! i { o with status := f o.status } }
  | none => g

/-- Update `id` in place if `id` is in `g.objects`. -/
def modifyObject (g : Game) (id : ObjectId) (f : GameObject → GameObject) : Game :=
  match g.objects.findIdx? (·.id == id) with
  | some i =>
    let o := g.objects[i]!
    { g with objects := g.objects.set! i (f o) }
  | none => g

/-- Update `p` in place if `p` is in `g.players`. -/
def modifyPlayer (g : Game) (p : PlayerId) (f : Player → Player) : Game :=
  if h : p.idx < g.players.size then
    let pl := g.players[p.idx]
    { g with players := g.players.set! p.idx (f pl) }
  else g

/-- The value `f` picks from the most recently created active continuous
effect it applies to (later effects win, CR 613.7). -/
def lastActive? {α : Type} (g : Game) (f : ContinuousEffect → Option α) : Option α :=
  g.activeEffects.foldl (fun acc (_, e) =>
    match f e with
    | some v => some v
    | none => acc) none

/-- Whether an active continuous effect has exactly the payload `eff`. -/
def hasActiveEffect (g : Game) (eff : ContinuousEffect) : Bool :=
  g.activeEffects.any (fun (_, e) => e == eff)

/-- A continuous effect that only sets a flag. Each recorded effect is one
contribution; the flag is cleared only when no equal effect remains active. -/
def effectIsFlag : ContinuousEffect → Bool
  | .auraConstruct55 _ | .pumpPerArtifactUntilEot _ | .firstStrikeOnYourTurn _
  | .loseIndestructibleUntilEot _ | .exileIfDiesUntilEot _ | .cardsInHandPowerUntilEot _
  | .additionalCreature _ _ | .additionalArtifactUntilEot _ | .onlyFoodArtifact _
  | .returnedAsArtifact _ | .notACreature _ | .combatDamageCreatesTreasureUntilEot _
  | .losesAbilitiesUntilEot _ | .cantBeBlockedExceptByHasteUntilEot _ | .cantBlockUntilEot _
  | .freeCastFromGraveyardUntilEot _ | .flashbackUntilEot _
  | .exileInstantSorceryInstead _ | .uncounterableThisCast _
  | .protectionFromEverything _ | .lifeCantChange _ | .lifeLocked _
  | .cantCastSpellsThisTurn _ | .jaceLoyaltyAtInstantSpeedThisTurn _
  | .legendRuleOffThisTurn _ | .nextSpellCantBeCounteredThisTurn _
  | .cantAttackJacesThisTurn _ | .creaturesWithoutFlyingCantBlockUntilEot
  | .powerUpsForbiddenThisTurn => true
  | _ => false

/-- Effective controller of `o` under `g.activeEffects` (CR 613.1b / 613.7 /
800.4a). -/
def effectiveController? (g : Game) (o : GameObject) : Option PlayerId :=
  let ctrl? := g.lastActive? (fun
    | .control oid c _ _ _ => if oid == o.id then some c else none
    | _ => none)
  match ctrl? with
  | some c => some c
  | none =>
    let p := o.defaultController.getD o.owner
    if !(g.players[p.idx]!).lost then some p else o.controller

/-- Recompute `id`'s control duration flags from every active control-changing
effect on it (CR 613.1b / 613.7). `o.controller` and `o.controlChanged` are
written only by `PermanentEvent.controlChanged`. -/
def recomputeControl (g : Game) (id : ObjectId) : Game :=
  let effs := g.activeEffects.filterMap (fun (_, e) =>
    match e with
    | .control oid c untilEot turnEndsLeft untilSourceLeaves =>
      if oid == id then some (c, untilEot, turnEndsLeft, untilSourceLeaves) else none
    | _ => none)
  g.modifyObject id (fun o =>
    match effs.back? with
    | some _ =>
      { o with
        controlUntilSourceLeaves :=
          effs.foldl (fun acc (_, _, _, usl) => usl.orElse (fun _ => acc)) none
        status :=
          { o.status with
            controlUntilEot := effs.any (fun (_, ue, _, _) => ue)
            controlTurnEndsLeft := effs.foldl (fun acc (_, _, tel, _) => max acc tel) 0 } }
    | none =>
      { o with
        controlUntilSourceLeaves := none
        status :=
          { o.status with
            controlUntilEot := false
            controlTurnEndsLeft := 0 } })

/-- Recompute `id`'s copied characteristics and copy-duration fields from the
active `.copy` continuous effects on `id` (CR 611 / 613.7 / 707), restoring the
original printed card when none remain. -/
def recomputeCopy (g : Game) (id : ObjectId) (fallbackRestore : Option CardDef := none) : Game :=
  let latest? := g.lastActive? (fun
    | .copy oid printed r ue unt usl =>
      if oid == id then some (printed, r, ue, unt, usl) else none
    | _ => none)
  g.modifyObject id (fun o =>
    match latest? with
    | some (printed, r, ue, unt, usl) =>
      { o with
        printed
        copyRestore := r
        copyUntilEot := ue
        copyUntilNextTurn := unt
        copyUntilSourceLeaves := usl }
    | none =>
      match fallbackRestore.orElse (fun _ => o.copyRestore) with
      | some card =>
        { o with
          printed := card
          copyRestore := none
          copyUntilEot := false
          copyUntilNextTurn := false
          copyUntilSourceLeaves := none }
      | none =>
        { o with
          copyUntilEot := false
          copyUntilNextTurn := false
          copyUntilSourceLeaves := none })

/-- Recompute a slot that holds a single value (or a merged set) from every
active continuous effect writing it, so creating, updating, or ending one
effect never erases another effect's contribution (CR 611 / 613.7). Returns
`none` for effects whose slot is not recomputed this way. -/
def refreshEffectSlot? (g : Game) (eff : ContinuousEffect) : Option Game :=
  match eff with
  | .keywordsUntilEot id _ =>
    let kw := g.activeEffects.foldl (fun acc (_, e) =>
      match e with
      | .keywordsUntilEot oid k => if oid == id then Keywords.merge acc k else acc
      | _ => acc) Keywords.none
    some (g.modifyStatus id (fun s => { s with untilEotKeywords := kw }))
  | .setBasePTUntilEot id _ =>
    let pt := g.lastActive? (fun | .setBasePTUntilEot oid pt => if oid == id then some pt else none | _ => none)
    some (g.modifyStatus id (fun s => { s with setBasePT := pt }))
  | .replacedCreatureTypesUntilEot id _ =>
    let subs := g.lastActive? (fun
      | .replacedCreatureTypesUntilEot oid subs => if oid == id then some subs else none
      | _ => none)
    some (g.modifyStatus id (fun s => { s with replacedCreatureTypesUntilEot := subs }))
  | .cantBeBlockedByPlayerUntilEot id _ =>
    let p := g.lastActive? (fun
      | .cantBeBlockedByPlayerUntilEot oid p => if oid == id then some p else none
      | _ => none)
    some (g.modifyStatus id (fun s => { s with cantBeBlockedByPlayer := p }))
  | .playPermission id _ =>
    let perm := g.lastActive? (fun | .playPermission oid perm => if oid == id then some perm else none | _ => none)
    some (g.modifyObject id (fun o => { o with playPermission := perm }))
  | .copy id _ restore _ _ _ => some (g.recomputeCopy id restore)
  | .control id _ _ _ _ => some (g.recomputeControl id)
  | .assignCombatDamageEqualToughnessUntilEot _ =>
    some { g with
      assignCombatDamageEqualToughness :=
        g.lastActive? (fun | .assignCombatDamageEqualToughnessUntilEot p => some p | _ => none) }
  | .pendingFreeRGCreatureThisTurn _ =>
    some { g with
      pendingFreeRGCreature :=
        g.lastActive? (fun | .pendingFreeRGCreatureThisTurn p => some p | _ => none) }
  | .pendingLokiCopy _ _ _ =>
    some { g with
      pendingLokiCopy :=
        g.lastActive? (fun | .pendingLokiCopy p src pw => some (p, src, pw) | _ => none) }
  | .playerControl _ _ _ =>
    match g.lastActive? (fun | .playerControl you them onNext => some (you, them, onNext) | _ => none) with
    | some (you, them, onNext) =>
      some { g with playerControl := some (you, them), controlOnNextTakenTurn := onNext }
    | none => some { g with playerControl := none, controlOnNextTakenTurn := false }
  | _ => none

/-- Install one `ContinuousEffect`'s contribution to the game state (CR 611).
The effect must already be in `g.activeEffects`. -/
def installEffect (g : Game) (eff : ContinuousEffect) : Game :=
  match g.refreshEffectSlot? eff with
  | some g => g
  | none =>
  match eff with
  | .staticAbility _ _ => g
  | .auraConstruct55 id =>
    g.modifyStatus id (fun s => { s with animatedConstruct55 := true })
  | .pump id dp dt =>
    g.modifyStatus id (fun s => { s with pump := (s.pump.1 + dp, s.pump.2 + dt) })
  | .untilTurnOfPump id p dp dt =>
    g.modifyStatus id (fun s => { s with untilTurnOfPump := s.untilTurnOfPump.push (p, dp, dt) })
  | .pumpPerArtifactUntilEot id =>
    g.modifyStatus id (fun s => { s with pumpPerArtifactUntilEot := true })
  | .firstStrikeOnYourTurn id =>
    g.modifyStatus id (fun s => { s with firstStrikeOnYourTurn := true })
  | .loseIndestructibleUntilEot id =>
    g.modifyStatus id (fun s => { s with untilEotLosesIndestructible := true })
  | .exileIfDiesUntilEot id =>
    g.modifyStatus id (fun s => { s with untilEotExileIfDies := true })
  | .cardsInHandPowerUntilEot id =>
    g.modifyStatus id (fun s => { s with cardsInHandPowerUntilEot := true })
  | .additionalCreature id untilEot =>
    g.modifyStatus id (fun s =>
      if untilEot then { s with additionalCreatureUntilEot := true }
      else { s with additionalCreature := true })
  | .additionalArtifactUntilEot id =>
    g.modifyStatus id (fun s => { s with additionalArtifactUntilEot := true })
  | .additionalSubtype id sub dedup =>
    g.modifyStatus id (fun s =>
      { s with
        additionalSubtypes :=
          if dedup && s.additionalSubtypes.any (· == sub) then s.additionalSubtypes
          else s.additionalSubtypes.push sub })
  | .onlyFoodArtifact id =>
    g.modifyStatus id (fun s => { s with onlyFoodArtifact := true })
  | .returnedAsArtifact id =>
    g.modifyStatus id (fun s => { s with returnedAsArtifact := true })
  | .notACreature id =>
    g.modifyStatus id (fun s => { s with notACreature := true })
  | .grantedStatic id ab =>
    g.modifyStatus id (fun s => { s with grantedStaticAbilities := s.grantedStaticAbilities.push ab })
  | .grantedTriggered id ab untilEot =>
    g.modifyStatus id (fun s =>
      if untilEot then { s with grantedTriggersUntilEot := s.grantedTriggersUntilEot.push ab }
      else { s with grantedTriggeredAbilities := s.grantedTriggeredAbilities.push ab })
  | .ironFistTapUntilEot id n =>
    g.modifyStatus id (fun s => { s with ironFistTapGrants := s.ironFistTapGrants + n })
  | .combatDamageCreatesTreasureUntilEot id =>
    g.modifyStatus id (fun s => { s with combatDamageCreatesTreasure := true })
  | .losesAbilitiesUntilEot id =>
    g.modifyStatus id (fun s => { s with losesAbilitiesUntilEot := true })
  | .losesAbilitiesWhileSource id src =>
    g.modifyStatus id (fun s => { s with losesAbilitiesGrantedBy := s.losesAbilitiesGrantedBy.push src })
  | .hexproofWhileSource id src =>
    g.modifyStatus id (fun s => { s with hexproofGrantedBy := s.hexproofGrantedBy.push src })
  | .preventDamageWhileSource id src =>
    g.modifyStatus id (fun s => { s with preventDamageGrantedBy := s.preventDamageGrantedBy.push src })
  | .cantUntapWhileSource id src =>
    g.modifyStatus id (fun s => { s with cantUntapGrantedBy := s.cantUntapGrantedBy.push src })
  | .cantBeBlockedExceptByHasteUntilEot id =>
    g.modifyStatus id (fun s => { s with cantBeBlockedExceptByHasteUntilEot := true })
  | .cantBlockUntilEot id =>
    g.modifyStatus id (fun s => { s with cantBlockUntilEot := true })
  | .colorlessGrantUntilCast id cardId =>
    g.modifyStatus id (fun s => { s with colorlessGrantUntilCast := s.colorlessGrantUntilCast.push cardId })
  | .freeCastFromGraveyardUntilEot id =>
    g.modifyStatus id (fun s => { s with freeCastFromGraveyard := true })
  | .flashbackUntilEot id =>
    g.modifyObject id (fun o => { o with flashbackUntilEot := true })
  | .exileInstantSorceryInstead id =>
    g.modifyObject id (fun o => { o with exileInstantSorceryInstead := true })
  | .uncounterableThisCast id =>
    g.modifyObject id (fun o => { o with uncounterableThisCast := true })
  | .fraEmblemUntilTurnOf id p =>
    g.modifyObject id (fun o => { o with fraEffectUntilTurnOf := some p })
  | .additionalLandsThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn + n })
  | .protectionFromEverything p =>
    g.modifyPlayer p (fun pl => { pl with protectionFromEverything := true })
  | .lifeCantChange p =>
    g.modifyPlayer p (fun pl => { pl with lifeCantChange := true })
  | .lifeLocked p =>
    g.modifyPlayer p (fun pl => { pl with lifeLocked := true })
  | .cantCastSpellsThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with cantCastSpellsThisTurn := true })
  | .attackPumpPerPlainsThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with attackPumpPerPlainsThisTurn := pl.attackPumpPerPlainsThisTurn + n })
  | .typeSpellCostLessThisTurn p ct n =>
    g.modifyPlayer p (fun pl => { pl with typeSpellCostLessThisTurn := pl.typeSpellCostLessThisTurn.push (ct, n) })
  | .supertypeSpellCostLessThisTurn p st n =>
    g.modifyPlayer p (fun pl => { pl with supertypeSpellCostLessThisTurn := pl.supertypeSpellCostLessThisTurn.push (st, n) })
  | .jaceLoyaltyAtInstantSpeedThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with jaceLoyaltyAtInstantSpeed := true })
  | .legendRuleOffThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with legendRuleOffThisTurn := true })
  | .copyNextInstantSorceryThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with copyNextInstantSorceryThisTurn := pl.copyNextInstantSorceryThisTurn + n })
  | .mountainExtraRedThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with mountainExtraRedThisTurn := pl.mountainExtraRedThisTurn + n })
  | .nextSpellCantBeCounteredThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with nextSpellCantBeCountered := true })
  | .cantAttackJacesThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with cantAttackJaces := true })
  | .creaturesWithoutFlyingCantBlockUntilEot =>
    { g with creaturesWithoutFlyingCantBlock := true }
  | .powerUpsForbiddenThisTurn =>
    { g with powerUpsForbidden := true }
  -- Recomputed from every active effect by `refreshEffectSlot?` above.
  | .keywordsUntilEot .. | .setBasePTUntilEot .. | .replacedCreatureTypesUntilEot ..
  | .cantBeBlockedByPlayerUntilEot .. | .playPermission .. | .copy .. | .control ..
  | .assignCombatDamageEqualToughnessUntilEot .. | .pendingFreeRGCreatureThisTurn ..
  | .pendingLokiCopy .. | .playerControl .. | .replacement .. | .prevention .. => g

/-- Remove one `ContinuousEffect`'s contribution from the game state (CR 611).
The effect must already be gone from `g.activeEffects`; a flag stays set while
an equal effect is still active, and recomputed slots keep the contributions
of the effects that remain. -/
def uninstallEffect (g : Game) (eff : ContinuousEffect) : Game :=
  match g.refreshEffectSlot? eff with
  | some g => g
  | none =>
  if effectIsFlag eff && g.hasActiveEffect eff then g
  else
  match eff with
  | .staticAbility _ _ => g
  | .auraConstruct55 id =>
    g.modifyStatus id (fun s => { s with animatedConstruct55 := false })
  | .pump id dp dt =>
    g.modifyStatus id (fun s => { s with pump := (s.pump.1 - dp, s.pump.2 - dt) })
  | .untilTurnOfPump id p dp dt =>
    g.modifyStatus id (fun s =>
      match s.untilTurnOfPump.findIdx? (· == (p, dp, dt)) with
      | some idx => { s with untilTurnOfPump := s.untilTurnOfPump.eraseIdx! idx }
      | none => s)
  | .pumpPerArtifactUntilEot id =>
    g.modifyStatus id (fun s => { s with pumpPerArtifactUntilEot := false })
  | .firstStrikeOnYourTurn id =>
    g.modifyStatus id (fun s => { s with firstStrikeOnYourTurn := false })
  | .loseIndestructibleUntilEot id =>
    g.modifyStatus id (fun s => { s with untilEotLosesIndestructible := false })
  | .exileIfDiesUntilEot id =>
    g.modifyStatus id (fun s => { s with untilEotExileIfDies := false })
  | .cardsInHandPowerUntilEot id =>
    g.modifyStatus id (fun s => { s with cardsInHandPowerUntilEot := false })
  | .additionalCreature id untilEot =>
    g.modifyStatus id (fun s =>
      if untilEot then { s with additionalCreatureUntilEot := false }
      else { s with additionalCreature := false })
  | .additionalArtifactUntilEot id =>
    g.modifyStatus id (fun s => { s with additionalArtifactUntilEot := false })
  | .additionalSubtype id sub _ =>
    -- Keep the subtype while another active effect still grants it (a
    -- deduplicating grant may share one entry with another effect).
    let stillGranted := g.activeEffects.any (fun (_, e) =>
      match e with
      | .additionalSubtype oid s' _ => oid == id && s' == sub
      | _ => false)
    g.modifyStatus id (fun s =>
      let count := s.additionalSubtypes.foldl (fun n x => if x == sub then n + 1 else n) 0
      if stillGranted && count ≤ 1 then s
      else
        match s.additionalSubtypes.findIdx? (· == sub) with
        | some idx => { s with additionalSubtypes := s.additionalSubtypes.eraseIdx! idx }
        | none => s)
  | .onlyFoodArtifact id =>
    g.modifyStatus id (fun s => { s with onlyFoodArtifact := false })
  | .returnedAsArtifact id =>
    g.modifyStatus id (fun s => { s with returnedAsArtifact := false })
  | .notACreature id =>
    g.modifyStatus id (fun s => { s with notACreature := false })
  | .grantedStatic id ab =>
    g.modifyStatus id (fun s =>
      match s.grantedStaticAbilities.findIdx? (· == ab) with
      | some idx => { s with grantedStaticAbilities := s.grantedStaticAbilities.eraseIdx! idx }
      | none => s)
  | .grantedTriggered id ab untilEot =>
    g.modifyStatus id (fun s =>
      if untilEot then
        match s.grantedTriggersUntilEot.findIdx? (· == ab) with
        | some idx => { s with grantedTriggersUntilEot := s.grantedTriggersUntilEot.eraseIdx! idx }
        | none => s
      else
        match s.grantedTriggeredAbilities.findIdx? (· == ab) with
        | some idx => { s with grantedTriggeredAbilities := s.grantedTriggeredAbilities.eraseIdx! idx }
        | none => s)
  | .ironFistTapUntilEot id n =>
    g.modifyStatus id (fun s => { s with ironFistTapGrants := s.ironFistTapGrants - n })
  | .combatDamageCreatesTreasureUntilEot id =>
    g.modifyStatus id (fun s => { s with combatDamageCreatesTreasure := false })
  | .losesAbilitiesUntilEot id =>
    g.modifyStatus id (fun s => { s with losesAbilitiesUntilEot := false })
  | .losesAbilitiesWhileSource id src =>
    g.modifyStatus id (fun s =>
      match s.losesAbilitiesGrantedBy.findIdx? (· == src) with
      | some idx => { s with losesAbilitiesGrantedBy := s.losesAbilitiesGrantedBy.eraseIdx! idx }
      | none => s)
  | .hexproofWhileSource id src =>
    g.modifyStatus id (fun s =>
      match s.hexproofGrantedBy.findIdx? (· == src) with
      | some idx => { s with hexproofGrantedBy := s.hexproofGrantedBy.eraseIdx! idx }
      | none => s)
  | .preventDamageWhileSource id src =>
    g.modifyStatus id (fun s =>
      match s.preventDamageGrantedBy.findIdx? (· == src) with
      | some idx => { s with preventDamageGrantedBy := s.preventDamageGrantedBy.eraseIdx! idx }
      | none => s)
  | .cantUntapWhileSource id src =>
    g.modifyStatus id (fun s =>
      match s.cantUntapGrantedBy.findIdx? (· == src) with
      | some idx => { s with cantUntapGrantedBy := s.cantUntapGrantedBy.eraseIdx! idx }
      | none => s)
  | .cantBeBlockedExceptByHasteUntilEot id =>
    g.modifyStatus id (fun s => { s with cantBeBlockedExceptByHasteUntilEot := false })
  | .cantBlockUntilEot id =>
    g.modifyStatus id (fun s => { s with cantBlockUntilEot := false })
  | .colorlessGrantUntilCast id cardId =>
    g.modifyStatus id (fun s =>
      match s.colorlessGrantUntilCast.findIdx? (· == cardId) with
      | some idx => { s with colorlessGrantUntilCast := s.colorlessGrantUntilCast.eraseIdx! idx }
      | none => s)
  | .freeCastFromGraveyardUntilEot id =>
    g.modifyStatus id (fun s => { s with freeCastFromGraveyard := false })
  | .flashbackUntilEot id =>
    g.modifyObject id (fun o => { o with flashbackUntilEot := false })
  | .exileInstantSorceryInstead id =>
    g.modifyObject id (fun o => { o with exileInstantSorceryInstead := false })
  | .uncounterableThisCast id =>
    g.modifyObject id (fun o => { o with uncounterableThisCast := false })
  | .fraEmblemUntilTurnOf id _ =>
    { g with objects := g.objects.filter (·.id != id) }
  | .additionalLandsThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn - n })
  | .protectionFromEverything p =>
    g.modifyPlayer p (fun pl => { pl with protectionFromEverything := false })
  | .lifeCantChange p =>
    g.modifyPlayer p (fun pl => { pl with lifeCantChange := false })
  | .lifeLocked p =>
    g.modifyPlayer p (fun pl => { pl with lifeLocked := false })
  | .cantCastSpellsThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with cantCastSpellsThisTurn := false })
  | .attackPumpPerPlainsThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with attackPumpPerPlainsThisTurn := pl.attackPumpPerPlainsThisTurn - n })
  | .typeSpellCostLessThisTurn p ct n =>
    g.modifyPlayer p (fun pl =>
      match pl.typeSpellCostLessThisTurn.findIdx? (· == (ct, n)) with
      | some idx => { pl with typeSpellCostLessThisTurn := pl.typeSpellCostLessThisTurn.eraseIdx! idx }
      | none => pl)
  | .supertypeSpellCostLessThisTurn p st n =>
    g.modifyPlayer p (fun pl =>
      match pl.supertypeSpellCostLessThisTurn.findIdx? (· == (st, n)) with
      | some idx => { pl with supertypeSpellCostLessThisTurn := pl.supertypeSpellCostLessThisTurn.eraseIdx! idx }
      | none => pl)
  | .jaceLoyaltyAtInstantSpeedThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with jaceLoyaltyAtInstantSpeed := false })
  | .legendRuleOffThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with legendRuleOffThisTurn := false })
  | .copyNextInstantSorceryThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with copyNextInstantSorceryThisTurn := pl.copyNextInstantSorceryThisTurn - n })
  | .mountainExtraRedThisTurn p n =>
    g.modifyPlayer p (fun pl => { pl with mountainExtraRedThisTurn := pl.mountainExtraRedThisTurn - n })
  | .nextSpellCantBeCounteredThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with nextSpellCantBeCountered := false })
  | .cantAttackJacesThisTurn p =>
    g.modifyPlayer p (fun pl => { pl with cantAttackJaces := false })
  | .creaturesWithoutFlyingCantBlockUntilEot =>
    { g with creaturesWithoutFlyingCantBlock := false }
  | .powerUpsForbiddenThisTurn =>
    { g with powerUpsForbidden := false }
  -- Recomputed from the remaining active effects by `refreshEffectSlot?` above.
  | .keywordsUntilEot .. | .setBasePTUntilEot .. | .replacedCreatureTypesUntilEot ..
  | .cantBeBlockedByPlayerUntilEot .. | .playPermission .. | .copy .. | .control ..
  | .assignCombatDamageEqualToughnessUntilEot .. | .pendingFreeRGCreatureThisTurn ..
  | .pendingLokiCopy .. | .playerControl .. | .replacement .. | .prevention .. => g

/-- Apply the creation of one `ContinuousEffect` in isolation (CR 611): record
it under `effectId` in `g.activeEffects` and install its contribution. -/
def applyEffectCreated (g : Game) (effectId : EffectId) (eff : ContinuousEffect) : Game :=
  let g :=
    { g with
      nextEffectId := max g.nextEffectId (effectId.raw + 1)
      activeEffects := g.activeEffects.push (effectId, eff) }
  g.installEffect eff

/-- Apply the expiration of the continuous effect recorded under `effectId`
(CR 611). Only that entry is removed, and its stored payload is what is rolled
back. An id that is not active changes nothing. -/
def applyEffectExpired (g : Game) (effectId : EffectId) (_eff : ContinuousEffect) : Game :=
  match g.activeEffects.findIdx? (·.1 == effectId) with
  | none => g
  | some idx =>
    let stored := g.activeEffects[idx]!.2
    let g :=
      { g with
        nextEffectId := max g.nextEffectId (effectId.raw + 1)
        activeEffects := g.activeEffects.eraseIdx! idx }
    g.uninstallEffect stored

/-- Replace the payload of the active continuous effect `effectId`, keeping its
id and position (CR 611). An id that is not active changes nothing. -/
def applyEffectUpdated (g : Game) (effectId : EffectId) (eff : ContinuousEffect) : Game :=
  match g.activeEffects.findIdx? (·.1 == effectId) with
  | none => g
  | some idx =>
    let old := g.activeEffects[idx]!.2
    let g := { g with activeEffects := g.activeEffects.set! idx (effectId, eff) }
    (g.uninstallEffect old).installEffect eff

/-- Apply one `PermanentEvent` in isolation (CR 110.5, 122, 701.3, 701.26). -/
def applyPermanentEvent (g : Game) (e : PermanentEvent) : Game :=
  let findEventIdx? (object : EventObject) : Option Nat :=
    object.id.bind (fun id => g.objects.findIdx? (·.id == id))
  match e with
  | .tapped object _ =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let s := { o.status with tapped := true, becameTappedThisTurn := true }
      { g with objects := g.objects.set! i { o with status := s } }
    | none => g
  | .untapped object =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let s := { o.status with tapped := false }
      { g with objects := g.objects.set! i { o with status := s } }
    | none => g
  | .phasedOut object indirectly =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let pw := if indirectly then o.attachedTo else none
      { g with objects := g.objects.set! i { o with status := { o.status with phasedOut := true, phasedWith := pw } } }
    | none => g
  | .phasedIn object _ =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status := { o.status with phasedOut := false, phasedWith := none, summoningSick := false } } }
    | none => g
  | .transformed object nowBackFace =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let printed :=
        if o.status.transformed != nowBackFace then
          match o.printed.otherFace with
          | some face => { face with otherFace := some { o.printed with otherFace := none } }
          | none => o.printed
        else o.printed
      { g with objects := g.objects.set! i { o with printed, status := { o.status with transformed := nowBackFace } } }
    | none => g
  | .turnedFaceUp object =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status := { o.status with faceDown := false } } }
    | none => g
  | .turnedFaceDown object =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status := { o.status with faceDown := true } } }
    | none => g
  | .counters (.player p) .poison delta _ =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      let poison :=
        match delta with
        | .put n => pl.poison + n
        | .removed n => pl.poison - n
      { g with players := g.players.set! p.idx { pl with poison } }
    else g
  | .counters (.player p) kind delta _ =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      let cur := pl.counterCount kind
      let next :=
        match delta with
        | .put n => cur + n
        | .removed n => cur - n
      let counters :=
        let without := pl.counters.filter (·.1 != kind)
        if next == 0 then without else without.push (kind, next)
      { g with players := g.players.set! p.idx { pl with counters } }
    else g
  | .counters (.object object) kind delta _ =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status := o.status.applyCounterDelta kind delta } }
    | none => g
  | .attached attachment host _ =>
    match findEventIdx? attachment with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with attachedTo := some host } }
    | none => g
  | .unattached attachment _ =>
    match findEventIdx? attachment with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with attachedTo := none } }
    | none => g
  | .controlChanged object fromPlayer toPlayer =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let defaultCtrl := o.defaultController.getD o.owner
      let hasActiveCtrl := g.activeEffects.any (fun (_, e) =>
        match e with
        | .control oid _ _ _ _ => some oid == object.id
        | _ => false)
      let changed :=
        if hasActiveCtrl || toPlayer != defaultCtrl then
          o.controlChanged || o.controller != some toPlayer || fromPlayer != toPlayer
        else false
      { g with
        objects :=
          g.objects.set! i
            { o with
              controller := some toPlayer
              controlChanged := changed } }
    | none => g
  | .designation object d gained =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let s :=
        match d with
        | .ringBearer => { o.status with ringBearer := gained }
        | .commander => { o.status with isCommander := gained }
        | .goaded byPlayer untilNextTurn =>
          let (goadedBy, goadedUntilNextTurnOf) :=
            if gained then
              let byNow :=
                if o.status.goadedBy.contains byPlayer then o.status.goadedBy
                else o.status.goadedBy.push byPlayer
              let untilNow :=
                if !untilNextTurn then
                  o.status.goadedUntilNextTurnOf.filter (· != byPlayer)
                else if !o.status.goadedBy.contains byPlayer ||
                    o.status.goadedUntilNextTurnOf.contains byPlayer then
                  if o.status.goadedUntilNextTurnOf.contains byPlayer then
                    o.status.goadedUntilNextTurnOf
                  else
                    o.status.goadedUntilNextTurnOf.push byPlayer
                else
                  o.status.goadedUntilNextTurnOf
              (byNow, untilNow)
            else
              let untilNow := o.status.goadedUntilNextTurnOf.filter (· != byPlayer)
              let byNow :=
                if !untilNextTurn || o.status.goadedUntilNextTurnOf.contains byPlayer then
                  o.status.goadedBy.filter (· != byPlayer)
                else
                  o.status.goadedBy
              (byNow, untilNow)
          { o.status with goaded := !goadedBy.isEmpty, goadedBy, goadedUntilNextTurnOf }
        | .prepared => { o.status with prepared := gained }
        | .harnessed => { o.status with harnessed := gained }
      { g with objects := g.objects.set! i { o with status := s } }
    | none => g

/-- Apply one `DamageEvent` in isolation (CR 120.3 / 120.4b). -/
def applyDamageEvent (g : Game) (e : DamageEvent) : Game :=
  match e with
  | .dealt _ | .prevented _ _ _ => g
  | .marked objectId amount =>
    match g.objects.findIdx? (·.id == objectId) with
    | some i =>
      let o := g.objects[i]!
      let s := o.status.applyChange (.addDamage (amount : Int) false)
      { g with objects := g.objects.set! i { o with status := s } }
    | none => g
  | .markedCleared objectIds =>
    objectIds.foldl (fun acc id =>
      match acc.objects.findIdx? (·.id == id) with
      | some i =>
        let o := acc.objects[i]!
        { acc with
          objects :=
            acc.objects.set! i
              { o with
                status :=
                  { o.status with
                    damage := 0
                    dealtDeathtouch := false } } }
      | none => acc) g

/-- Apply one `LifeEvent` in isolation (CR 119.2 / 119.3). -/
def applyLifeEvent (g : Game) (e : LifeEvent) : Game :=
  match e with
  | .gained p amount =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      if pl.lifeLocked || pl.lifeCantChange then g
      else { g with players := g.players.set! p.idx { pl with life := pl.life + (amount : Int) } }
    else g
  | .lost p amount _ _ =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      if pl.lifeLocked || pl.lifeCantChange then g
      else { g with players := g.players.set! p.idx { pl with life := pl.life - (amount : Int) } }
    else g

/-- Remove `id` from `zone`'s id list without recording an extra event. -/
def stripFromZoneList (g : Game) (id : ObjectId) (zone : Zone) : Game :=
  match zone with
  | .library p => g.modifyPlayer p (fun pl => { pl with library := pl.library.filter (· != id) })
  | .hand p => g.modifyPlayer p (fun pl => { pl with hand := pl.hand.filter (· != id) })
  | .graveyard p => g.modifyPlayer p (fun pl => { pl with graveyard := pl.graveyard.filter (· != id) })
  | .stack => { g with stack := g.stack.filter (·.objectId != id) }
  | .battlefield | .exile | .command | .ante | .outside _ => g

/-- Insert `id` into `dest`'s id list without recording an extra event. -/
def insertIntoZoneList (g : Game) (id : ObjectId) (dest : Zone)
    (libPos : Option LibraryPosition := none) : Game :=
  match dest with
  | .library p =>
    g.modifyPlayer p (fun pl =>
      let lib := pl.library.filter (· != id)
      let lib' :=
        match libPos with
        | some .bottom => #[id] ++ lib
        | some (.fromTop offset) =>
          let split := lib.size - Nat.min offset lib.size
          lib.extract 0 split ++ #[id] ++ lib.extract split lib.size
        | some .top | some .shuffledIn | none => lib.push id
      { pl with library := lib' })
  | .hand p =>
    g.modifyPlayer p (fun pl =>
      let h := pl.hand.filter (· != id)
      { pl with hand := h.push id })
  | .graveyard p =>
    g.modifyPlayer p (fun pl =>
      let gy := pl.graveyard.filter (· != id)
      { pl with graveyard := gy.push id })
  | .stack | .battlefield | .exile | .command | .ante | .outside _ => g

/-- Apply one `ZoneEvent` in isolation (CR 400.6, 400.7, 111.10, 704.5d–e). -/
def applyZoneEvent (g : Game) (e : ZoneEvent) : Game :=
  match e with
  | .moved before after fromZone toZone verb _ entersWith libPos =>
    let newId : ObjectId := after.id.getD ⟨g.nextObjectId⟩
    let ts : Nat := g.timestamp + 1
    let mergedCounters : CounterBag :=
      if after.counters == entersWith ||
          after.counters == (Status.withCounterBag {} entersWith).toCounterBag then
        after.counters
      else
        after.counters.merge entersWith
    let existing? : Option GameObject :=
      before.id.bind (fun bid => g.objects.find? (fun o => o.id == bid && o.zone == fromZone))
    let materialize (printed : CardDef) (existing? : Option GameObject) : GameObject :=
      let faceDown := toZone == .battlefield && after.faceDown
      let chosenCardType :=
        if toZone == .battlefield && !faceDown && printed.asEntersChooseCardType then
          some CardType.creature
        else none
      let windcragMardu :=
        toZone == .battlefield && !faceDown && printed.asEntersChooseMarduOrJeskai
      let prepared :=
        toZone == .battlefield && !faceDown && printed.entersPrepared
      let impendingNotCreature :=
        fromZone == .stack && toZone == .battlefield &&
          printed.impending.isSome && mergedCounters.count .time > 0
      let sick :=
        if after.printed.isSome then after.summoningSick
        else (after.creature || printed.isCreature) && !after.keywords.haste
      let baseStatus : Status :=
        if toZone == .battlefield then
          { faceDown := faceDown
            tapped := after.tapped
            summoningSick := sick
            attacking := after.attacking
            attackingTarget := after.attackingTarget
            phasedOut := after.phasedOut
            chosenCardType := chosenCardType
            windcragMardu := windcragMardu
            prepared := prepared
            transformed := after.transformed
            cantTransform := after.transformed
            returnedAsArtifact := after.returnedAsArtifact
            onlyFoodArtifact := after.onlyFoodArtifact
            notACreature := impendingNotCreature
            gotPlusOneThisTurn := mergedCounters.count .plusOnePlusOne > 0 }
        else {}
      let status :=
        if mergedCounters.isEmpty then baseStatus
        else baseStatus.withCounterBag mergedCounters
      let lkiPower : Option Int :=
        if after.printed.isSome then after.lastKnownPower
        else if fromZone == .battlefield then before.power
        else existing?.bind (·.lastKnownPower)
      let lkiToughness : Option Int :=
        if after.printed.isSome then after.lastKnownToughness
        else if fromZone == .battlefield then before.toughness
        else existing?.bind (·.lastKnownToughness)
      let lastCtrl : Option PlayerId :=
        if fromZone == .battlefield then
          (existing?.bind (·.controller)).orElse (fun _ => before.controller)
        else existing?.bind (·.lastController)
      let chosenX : Option Nat :=
        after.chosenX.orElse (fun _ => existing?.bind (·.chosenX))
      let wasCast : Bool :=
        if after.printed.isSome then after.wasCast
        else if toZone == .battlefield then
          fromZone == .stack && !after.isCopy
        else if toZone == .stack then
          verb == .cast || (existing?.map (·.wasCast)).getD false
        else false
      { id := newId
        printed := printed
        owner := after.owner
        controller :=
          if toZone == .battlefield || toZone == .stack || after.printed.isSome then after.controller
          else none
        lastController := lastCtrl
        defaultController := if toZone == .battlefield then after.controller else none
        zone := toZone
        status := status
        timestamp := ts
        attachedTo := if toZone == .battlefield then after.attachedTo else none
        chosenX := chosenX
        wasCast := wasCast
        lastKnownPower := lkiPower
        lastKnownToughness := lkiToughness
        isCopy := after.isCopy }
    match existing? with
    | some existing =>
      let g := g.stripFromZoneList existing.id fromZone
      let leavingPlay :=
        (fromZone == .battlefield || fromZone == .stack) &&
          toZone != .battlefield && toZone != .stack
      let printed : CardDef :=
        match after.printed with
        | some p => p
        | none =>
          if leavingPlay && existing.status.transformed then
            match existing.printed.otherFace with
            | some front => { front with otherFace := some { existing.printed with otherFace := none } }
            | none => existing.printed
          else if toZone == .battlefield && after.transformed && !existing.status.transformed then
            match existing.printed.otherFace with
            | some back => { back with otherFace := some { existing.printed with otherFace := none } }
            | none => existing.printed
          else existing.printed
      let fresh := materialize printed (some existing)
      let objs := (g.objects.filter (fun (o : GameObject) => o.id != existing.id)).push fresh
      let g :=
        { g with
          objects := objs
          nextObjectId := max g.nextObjectId (newId.raw + 1)
          timestamp := max g.timestamp ts }
      g.insertIntoZoneList newId toZone libPos
    | none =>
      if before.id != after.id || !after.name.isEmpty || !after.types.isEmpty then
        let g :=
          match before.id with
          | some bid => g.stripFromZoneList bid fromZone
          | none => g
        let printed :=
          match after.printed.orElse (fun _ => before.printed) with
          | some p => p
          | none =>
            if !after.name.isEmpty || !after.types.isEmpty then after.toCardDef
            else before.toCardDef
        let fresh := materialize printed none
        let objs :=
          match g.objects.findIdx? (fun o => o.id == newId) with
          | some i =>
            let prev := g.objects[i]!
            if before.id == after.id && prev.zone == toZone then
              let st :=
                if mergedCounters.isEmpty then prev.status
                else prev.status.withCounterBag (prev.status.toCounterBag.merge mergedCounters)
              let st :=
                { st with
                  prepared := st.prepared || (!st.faceDown && printed.entersPrepared)
                  chosenCardType := st.chosenCardType.orElse (fun _ =>
                    if !st.faceDown && printed.asEntersChooseCardType then some .creature else none)
                  windcragMardu := st.windcragMardu || (!st.faceDown && printed.asEntersChooseMarduOrJeskai)
                  gotPlusOneThisTurn := st.gotPlusOneThisTurn || mergedCounters.count .plusOnePlusOne > 0 }
              g.objects.set! i { prev with status := st }
            else
              g.objects.set! i fresh
          | none => g.objects.push fresh
        let g :=
          { g with
            objects := objs
            nextObjectId := max g.nextObjectId (newId.raw + 1)
            timestamp := max g.timestamp ts }
        g.insertIntoZoneList newId toZone libPos
      else g
  | .created object controller =>
    let newId : ObjectId := object.id.getD ⟨g.nextObjectId⟩
    let ts : Nat := g.timestamp + 1
    let printed := object.toCardDef
    let sick :=
      if object.printed.isSome then object.summoningSick
      else (object.creature || printed.isCreature) && !object.keywords.haste
    let baseStatus : Status :=
      if object.zone == Zone.battlefield then
        { tapped := object.tapped
          summoningSick := sick
          attacking := object.attacking
          attackingTarget := object.attackingTarget
          phasedOut := object.phasedOut
          faceDown := object.faceDown
          transformed := object.transformed
          returnedAsArtifact := object.returnedAsArtifact
          onlyFoodArtifact := object.onlyFoodArtifact
          gotPlusOneThisTurn := object.counters.count .plusOnePlusOne > 0 }
      else {}
    let status :=
      if object.counters.isEmpty then baseStatus
      else baseStatus.withCounterBag object.counters
    let ctrl :=
      if object.zone == Zone.battlefield || object.zone == Zone.stack then
        object.controller.orElse (fun _ => some controller)
      else object.controller
    let fresh : GameObject :=
      { id := newId
        printed := printed
        owner := object.owner
        controller := ctrl
        defaultController := if object.zone == Zone.battlefield then ctrl else none
        zone := object.zone
        status := status
        timestamp := ts
        lastKnownPower := object.lastKnownPower
        lastKnownToughness := object.lastKnownToughness
        attachedTo := if object.zone == Zone.battlefield then object.attachedTo else none
        wasCast := object.wasCast
        isCopy := object.isCopy
        chosenX := object.chosenX }
    let objs :=
      match g.objects.findIdx? (fun o => o.id == newId) with
      | some i =>
        let prev := g.objects[i]!
        if prev.zone == object.zone then
          let st :=
            if object.counters.isEmpty then prev.status
            else prev.status.withCounterBag (prev.status.toCounterBag.merge object.counters)
          g.objects.set! i { prev with status := st }
        else
          g.objects.set! i fresh
      | none => g.objects.push fresh
    let g :=
      { g with
        objects := objs
        nextObjectId := max g.nextObjectId (newId.raw + 1)
        timestamp := max g.timestamp ts }
    g.insertIntoZoneList newId fresh.zone
  | .ceasedToExist object =>
    match object.id with
    | none => g
    | some id =>
      let g :=
        match g.objects.find? (fun o => o.id == id) with
        | some cur => g.stripFromZoneList id cur.zone
        | none => g
      let g := g.stripFromZoneList id object.zone
      { g with objects := g.objects.filter (fun o => o.id != id) }

/-- Apply a `PlayerEvent` to `g` (CR 701.22, 701.25, 701.34, 701.62, 500.5, 104.3, 800.4a). -/
def applyPlayerEvent (g : Game) (e : PlayerEvent) : Game :=
  match e with
  | .beheld p quality =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx (pl.applyChange (.pushBeheldQuality quality)) }
    else g
  | .scried p top bottom _ _ =>
    if h : p.idx < g.players.size then
      if top.isEmpty && bottom.isEmpty then g
      else
        let pl := g.players[p.idx]
        let lower := pl.library.filter (fun id => !top.contains id && !bottom.contains id)
        { g with players := g.players.set! p.idx { pl with library := bottom ++ lower ++ top } }
    else g
  | .surveilled p top graveyard _ _ =>
    if h : p.idx < g.players.size then
      if top.isEmpty && graveyard.isEmpty then g
      else
        let pl := g.players[p.idx]
        let lower := pl.library.filter (fun id => !top.contains id && !graveyard.contains id)
        let keptGy := graveyard.filter (fun id => pl.library.contains id)
        { g with players := g.players.set! p.idx { pl with library := keptGy ++ lower ++ top } }
    else g
  | .manaEmptied p _ keptColorless =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx (pl.applyChange (.emptyManaPool keptColorless)) }
    else g
  | .lost p =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with lost := true } }
    else g
  | .leftGame p =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with lost := true, leftTheGame := true } }
    else g
  | .proliferated .. | .sheHulkDealtDamage .. | .ringTempted .. => g

/-- Apply a `TurnEvent` to `g` (CR 500). -/
def applyTurnEvent (g : Game) (e : TurnEvent) : Game :=
  match e with
  | .turnBegan player extra =>
    let restExtra :=
      if extra then
        let trimmed := (g.extraTurns.toList.dropWhile (fun q =>
          if h : q.idx < g.players.size then g.players[q.idx].lost else true)).toArray
        if trimmed[0]? == some player then trimmed.extract 1 trimmed.size
        else trimmed
      else
        (g.extraTurns.toList.dropWhile (fun q =>
          if h : q.idx < g.players.size then g.players[q.idx].lost else true)).toArray
    { g with
      turnNumber := g.turnNumber + 1
      activePlayer := player
      isFirstTurn := false
      extraTurns := restExtra }
  | .phaseBegan phase =>
    if phase == .combat && g.step == .endOfCombat && g.additionalCombatPhases > 0 then
      { g with additionalCombatPhases := g.additionalCombatPhases - 1 }
    else g
  | .stepBegan st _ =>
    { g with step := st }
  | .stepEnded _ | .phaseEnded _ | .turnEnded _ | .extraStepAdded _ _ => g
  | .dayNightChanged night =>
    { g with isNight := night }
  | .extraTurnAdded player _ =>
    { g with extraTurns := #[player] ++ g.extraTurns }
  | .extraPhaseAdded phase _ =>
    if phase == .combat then
      { g with additionalCombatPhases := g.additionalCombatPhases + 1 }
    else g

/-- Apply a `CastEvent` to `g` (CR 601.2 / 602.2 / 605.3b). -/
def applyCastEvent (g : Game) (e : CastEvent) : Game :=
  match e with
  | .proposed obj _ fromZone way =>
    match g.objects.findIdx? (·.id == obj) with
    | some i =>
      let o := g.objects[i]!
      let fromGy :=
        (match fromZone with | .graveyard _ => true | _ => false) ||
          way == .alternative "flashback" || o.castFromGraveyard
      let fromHand := match fromZone with | .hand _ => true | _ => o.castFromHand
      let prepSpell := way == .alternative "prepare" || o.isPreparedSpell
      { g with objects := g.objects.set! i { o with
          castFromGraveyard := fromGy
          castFromHand := fromHand
          isPreparedSpell := prepSpell } }
    | none => g
  | .announced obj modes x costs =>
    let g :=
      match g.objects.findIdx? (·.id == obj) with
      | some i =>
        let o := g.objects[i]!
        let chosenX := x.orElse (fun _ => o.chosenX)
        let kicked := o.kicked || costs.any (fun | .kicker => true | _ => false)
        let giftTo := (costs.findSome? (fun | .gift p => some p | _ => none)).orElse (fun _ => o.giftPromisedTo)
        let twPaid := o.teamworkPaid || costs.any (fun | .teamwork _ => true | _ => false)
        { g with objects := g.objects.set! i { o with
            chosenX := chosenX
            kicked := kicked
            giftPromisedTo := giftTo
            teamworkPaid := twPaid } }
      | none => g
    if modes.isEmpty then g
    else
      match g.stack.findIdx? (·.objectId == obj) with
      | some i =>
        let se := g.stack[i]!
        { g with stack := g.stack.set! i { se with
            chosenMode := some modes[0]!
            extraModes := modes.extract 1 modes.size } }
      | none => g
  | .targeted obj targets division =>
    match g.stack.findIdx? (·.objectId == obj) with
    | some i =>
      let se := g.stack[i]!
      { g with stack := g.stack.set! i { se with
          targets := targets
          dividedDamage := division
          targetsAnnounced := true } }
    | none => g
  | .spellCast spell _ fromZone =>
    match spell.id.bind (fun id => g.objects.findIdx? (·.id == id)) with
    | some i =>
      let o := g.objects[i]!
      let fromGy := match fromZone with | .graveyard _ => true | _ => o.castFromGraveyard
      let fromHand := match fromZone with | .hand _ => true | _ => o.castFromHand
      { g with objects := g.objects.set! i { o with
          wasCast := true
          castFromGraveyard := fromGy
          castFromHand := fromHand } }
    | none => g
  | .abilityActivated .. => g

/-- Apply a `TriggerQueueEvent` to `g` (CR 603.2 / 603.3). -/
def applyTriggerQueueEvent (g : Game) (_e : TriggerQueueEvent) : Game := g

/-- The object a moved object became, following `ZoneEvent.moved` records in
`g.events` (CR 400.7). -/
partial def followMoved (g : Game) (id : ObjectId) : ObjectId :=
  let next? := g.events.reverse.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved before after _ _ _ _ _ _)) =>
      if before.id == some id then
        match after.id with
        | some next => if next != id then some next else none
        | none => none
      else none
    | _ => none)
  match next? with
  | some next => g.followMoved next
  | none => id

/-- Apply a `StackObjectEvent` to `g` (CR 608 / 707.10). -/
def applyStackObjectEvent (g : Game) (e : StackObjectEvent) : Game :=
  match e with
  | .copied original copy controller =>
    let newId : ObjectId := copy.id.getD ⟨g.nextObjectId⟩
    let ts : Nat := g.timestamp + 1
    let origObj? :=
      (g.objects.find? (·.id == original)).orElse (fun _ =>
        g.objects.find? (·.id == g.followMoved original))
    let origEntry? := g.stack.find? (·.objectId == original)
    let announcedCosts : Array AdditionalCostChoice :=
      g.events.foldl (fun acc ev =>
        match ev.change with
        | .rules (.cast (.announced oid _ _ cs)) =>
          if oid == original then acc ++ cs else acc
        | _ => acc) #[]
    let kickedFromEvents := announcedCosts.any (fun | .kicker => true | _ => false)
    let giftFromEvents := announcedCosts.findSome? (fun | .gift p => some p | _ => none)
    let teamworkFromEvents := announcedCosts.any (fun | .teamwork _ => true | _ => false)
    let printed :=
      match copy.printed with
      | some p => p
      | none =>
        match origObj? with
        | some o => o.printed
        | none => copy.toCardDef
    let fresh : GameObject :=
      match origObj? with
      | some orig =>
        -- CR 707.10: A copy of a spell or ability on the stack is not cast and
        -- only copies choices made for it (modes, targets, X, whether it was
        -- kicked/gifted/etc.), not cast-origin flags or linked cards.
        { id := newId
          printed := printed
          owner := controller
          controller := some controller
          zone := .stack
          status := {}
          timestamp := ts
          isCopy := true
          kicked := orig.kicked || kickedFromEvents
          giftPromisedTo := orig.giftPromisedTo.orElse (fun _ => giftFromEvents)
          teamworkPaid := orig.teamworkPaid || teamworkFromEvents
          sneakPaid := orig.sneakPaid
          sneakAttackWhom := orig.sneakAttackWhom
          sneakAttackTarget := orig.sneakAttackTarget
          chosenX := copy.chosenX.orElse (fun _ => orig.chosenX)
          adventurerCard := orig.adventurerCard
          abilityEffect := orig.abilityEffect
          triggeredAbility := orig.triggeredAbility
          reflexiveResolution := orig.reflexiveResolution
          sourceId := orig.sourceId
          fraCauseId := orig.fraCauseId
          fraCauseController := orig.fraCauseController
          fraCausePower := orig.fraCausePower
          fraCauseStatus := orig.fraCauseStatus
          lastKnownPower := copy.lastKnownPower.orElse (fun _ => orig.lastKnownPower)
          lastKnownToughness := copy.lastKnownToughness.orElse (fun _ => orig.lastKnownToughness) }
      | none =>
        { id := newId
          printed := printed
          owner := controller
          controller := some controller
          zone := .stack
          status := {}
          timestamp := ts
          isCopy := true
          kicked := kickedFromEvents
          giftPromisedTo := giftFromEvents
          teamworkPaid := teamworkFromEvents
          chosenX := copy.chosenX
          lastKnownPower := copy.lastKnownPower
          lastKnownToughness := copy.lastKnownToughness }
    let entry : StackEntry :=
      match origEntry? with
      | some origE =>
        { origE with
          objectId := newId
          controller := controller }
      | none =>
        let modes :=
          g.events.foldl (fun acc ev =>
            match ev.change with
            | .rules (.cast (.announced oid ms _ _)) =>
              if oid == original && !ms.isEmpty then ms else acc
            | _ => acc) #[]
        let (tgts, div) :=
          g.events.foldl (fun acc ev =>
            match ev.change with
            | .rules (.cast (.targeted oid ts dv)) =>
              if oid == original then (ts, if dv.isEmpty then acc.2 else dv) else acc
            | _ => acc) (#[], #[])
        { objectId := newId
          controller := controller
          targets := tgts
          dividedDamage := div
          chosenMode := modes[0]?
          extraModes := if modes.size > 1 then modes.extract 1 modes.size else #[]
          targetsAnnounced := true }
    let objs :=
      match g.objects.findIdx? (·.id == newId) with
      | some i => g.objects.set! i fresh
      | none => g.objects.push fresh
    let stk :=
      match g.stack.findIdx? (·.objectId == newId) with
      | some i => g.stack.set! i entry
      | none => g.stack.push entry
    { g with
      objects := objs
      stack := stk
      nextObjectId := max g.nextObjectId (newId.raw + 1)
      timestamp := max g.timestamp ts }
  | .resolved .. | .removedOnResolution .. => g

/-- Apply a `CombatEvent` to `g` (CR 506–511). -/
def applyCombatEvent (g : Game) (e : CombatEvent) : Game :=
  match e with
  | .attackersDeclared _ decls =>
    decls.foldl (fun acc (attacker, target) =>
      match attacker.id.bind (fun id => acc.objects.findIdx? (·.id == id)) with
      | some i =>
        let o := acc.objects[i]!
        { acc with objects := acc.objects.set! i { o with status :=
            { o.status with
              attacking := true
              attackingTarget := some target
              declaredAsAttackerThisTurn := true } } }
      | none => acc) g
  | .becameAttacking creature target =>
    match creature.id.bind (fun id => g.objects.findIdx? (·.id == id)) with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status :=
          { o.status with
            attacking := true
            attackingTarget := some target } } }
    | none => g
  | .blockersDeclared _ decls =>
    decls.foldl (fun acc (blocker, attackerId) =>
      match blocker.id.bind (fun id => acc.objects.findIdx? (·.id == id)) with
      | some i =>
        let o := acc.objects[i]!
        let st := o.status.applyChange (.addBlocking attackerId)
        { acc with objects := acc.objects.set! i { o with status := st } }
      | none => acc) g
  | .becameBlocked attacker _ =>
    match attacker.id.bind (fun id => g.objects.findIdx? (·.id == id)) with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status :=
          { o.status with blocked := true } } }
    | none => g
  | .remainedUnblocked _ => g
  | .damageAssigned _ forAttackers batch =>
    if forAttackers then
      { g with assignedCombatDamage := batch }
    else
      { g with assignedCombatDamage := g.assignedCombatDamage ++ batch }
  | .removedFromCombat object =>
    match object.id.bind (fun id => g.objects.findIdx? (·.id == id)) with
    | some i =>
      let o := g.objects[i]!
      let rid := o.id
      let st0 := o.status.applyChange .clearCombat
      let objs := (g.objects.set! i { o with status := st0 }).map (fun x =>
        if x.status.blocking.any (· == rid) then
          let st := x.status.applyChange (.removeBlocking rid)
          { x with status := st }
        else x)
      { g with objects := objs }
    | none => g

/-- Process one `RulesEvent` in isolation. -/
def applyRulesEvent (g : Game) (r : RulesEvent) : Game :=
  match r with
  | .zone e => g.applyZoneEvent e
  | .permanent e => g.applyPermanentEvent e
  | .damage e => g.applyDamageEvent e
  | .life e => g.applyLifeEvent e
  | .player e => g.applyPlayerEvent e
  | .turn e => g.applyTurnEvent e
  | .cast e => g.applyCastEvent e
  | .triggerQueue e => g.applyTriggerQueueEvent e
  | .stackObject e => g.applyStackObjectEvent e
  | .combat e => g.applyCombatEvent e
  | .spentMana .. => g
  | .effectCreated id eff => g.applyEffectCreated id eff
  | .effectExpired id eff => g.applyEffectExpired id eff
  | .effectUpdated id eff => g.applyEffectUpdated id eff

/-- Process one `EngineChange` in isolation. -/
def applyEngineChange (g : Game) (c : EngineChange) : Game :=
  match c with
  | .player p pc =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx (pl.applyChange pc) }
    else g
  | .playerChanges p pcs =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx (pcs.foldl Player.applyChange pl) }
    else g
  | .players v => { g with players := v }
  | .setPlayer pl => { g with players := g.players.set! pl.id.idx pl }
  | .object id oc =>
    match g.objects.findIdx? (·.id == id) with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i (o.applyChange oc) }
    | none => g
  | .objectChanges id ocs =>
    match g.objects.findIdx? (·.id == id) with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i (ocs.foldl GameObject.applyChange o) }
    | none => g
  | .objects v => { g with objects := v }
  | .setObject o =>
    match g.objects.findIdx? (·.id == o.id) with
    | some i => { g with objects := g.objects.set! i o }
    | none => { g with objects := g.objects.push o }
  | .removeObject id =>
    { g with objects := g.objects.filter (·.id != id) }
  | .replaceObject oldId fresh =>
    { g with objects := g.objects.filter (·.id != oldId) |>.push fresh }
  | .stack v => { g with stack := v }
  | .pushStack e => { g with stack := g.stack.push e }
  | .popStack => { g with stack := g.stack.pop }
  | .removeFromStack objectId =>
    { g with stack := g.stack.filter (·.objectId != objectId) }
  | .setStackEntryAt idx e =>
    { g with stack := g.stack.set! idx e }
  | .stackEntry idx sc =>
    if h : idx < g.stack.size then
      let e := g.stack[idx]
      { g with stack := g.stack.set! idx (e.applyChange sc) }
    else g
  | .stackEntryById objectId sc =>
    match g.stack.findIdx? (·.objectId == objectId) with
    | some i =>
      let e := g.stack[i]!
      { g with stack := g.stack.set! i (e.applyChange sc) }
    | none => g
  | .proposedSpell v => { g with proposedSpell := v }
  | .proposal pc =>
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some (prop.applyChange pc) }
    | none => g
  | .proposalChanges pcs =>
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some (pcs.foldl ProposedSpell.applyChange prop) }
    | none => g
  | .activePlayer v => { g with activePlayer := v }
  | .priority v => { g with priority := v }
  | .step v => { g with step := v }
  | .turnNumber v => { g with turnNumber := v }
  | .startingPlayer v => { g with startingPlayer := v }
  | .isFirstTurn v => { g with isFirstTurn := v }
  | .pending v => { g with pending := v }
  | .nextObjectId v => { g with nextObjectId := v }
  | .nextEffectId v => { g with nextEffectId := v }
  | .nextBatchId v => { g with nextBatchId := v }
  | .activeEffects v => { g with activeEffects := v }
  | .timestamp v => { g with timestamp := v }
  | .afterRandom v => { g with afterRandom := v }
  | .result v => { g with result := v }
  | .log v => { g with log := v }
  | .logMsg msg => { g with log := g.log.push msg }
  | .format v => { g with format := v }
  | .brawl v => { g with brawl := v }
  | .consecutivePasses v => { g with consecutivePasses := v }
  | .cleanupGivesPriority v => { g with cleanupGivesPriority := v }
  | .creaturesWithoutFlyingCantBlock v => { g with creaturesWithoutFlyingCantBlock := v }
  | .awaitingOpeningBegin v => { g with awaitingOpeningBegin := v }
  | .mulliganToDeclare v => { g with mulliganToDeclare := v }
  | .willMulligan v => { g with willMulligan := v }
  | .pushWillMulligan p => { g with willMulligan := g.willMulligan.push p }
  | .mulliganToBottom v => { g with mulliganToBottom := v }
  | .assignedCombatDamage v => { g with assignedCombatDamage := v }
  | .blockersQueue v => { g with blockersQueue := v }
  | .waitingTriggers v => { g with waitingTriggers := v }
  | .enqueueWaitingTriggers wts =>
    if wts.isEmpty then g else { g with waitingTriggers := g.waitingTriggers ++ wts }
  | .pushWaitingTrigger wt => { g with waitingTriggers := g.waitingTriggers.push wt }
  | .removeWaitingTriggersOf p =>
    { g with waitingTriggers := g.waitingTriggers.filter (·.controller != p) }
  | .removeWaitingTriggersForEvent ev =>
    { g with waitingTriggers := g.waitingTriggers.filter (·.event != ev) }
  | .removeWaitingTriggersForPlayerSource p sourceId part2 =>
    { g with
      waitingTriggers :=
        g.waitingTriggers.filter (fun w =>
          !(w.controller == p && w.source.id == sourceId &&
            w.event.isAnotherAbilityTriggering == part2)) }
  | .eraseFirstWaitingTriggerForPlayerSource p sourceId part2 =>
    match g.waitingTriggers.findIdx? (fun w =>
        w.controller == p && w.source.id == sourceId &&
        w.event.isAnotherAbilityTriggering == part2) with
    | some i => { g with waitingTriggers := g.waitingTriggers.eraseIdx! i }
    | none => g
  | .addSourceDealtDamagePower sourceId n =>
    { g with
      waitingTriggers := g.waitingTriggers.map (fun t =>
        if t.source.id == sourceId && t.event == .sourceDealtDamage then
          { t with lastKnownPower := some ((t.lastKnownPower.getD 0) + n) }
        else t) }
  | .firstStrikeDamageDone v => { g with firstStrikeDamageDone := v }
  | .pendingRegularCombatDamage v => { g with pendingRegularCombatDamage := v }
  | .firstStrikeAssignedThisCombat v => { g with firstStrikeAssignedThisCombat := v }
  | .isNight v => { g with isNight := v }
  | .pendingDrawAfterScry v => { g with pendingDrawAfterScry := v }
  | .discardedCardThisWay v => { g with discardedCardThisWay := v }
  | .palantirAfterScry v => { g with palantirAfterScry := v }
  | .resolvingSpell v => { g with resolvingSpell := v }
  | .resolvingAbility v => { g with resolvingAbility := v }
  | .recentTokenIds v => { g with recentTokenIds := v }
  | .pushRecentTokenId id => { g with recentTokenIds := g.recentTokenIds.push id }
  | .fraAfterLook v => { g with fraAfterLook := v }
  | .pendingFreeCopies v => { g with pendingFreeCopies := v }
  | .pendingMayCastFromExile v => { g with pendingMayCastFromExile := v }
  | .mayPayAlsoPlusOneOn v => { g with mayPayAlsoPlusOneOn := v }
  | .humansTappedThisWay v => { g with humansTappedThisWay := v }
  | .permanentsDestroyedThisWay v => { g with permanentsDestroyedThisWay := v }
  | .removedHopeThisWay v => { g with removedHopeThisWay := v }
  | .permanentDealtDamageThisWay v => { g with permanentDealtDamageThisWay := v }
  | .returnedPermanentThisWay v => { g with returnedPermanentThisWay := v }
  | .nthResolveThisWay v => { g with nthResolveThisWay := v }
  | .skipTriggerSequenceRest v => { g with skipTriggerSequenceRest := v }
  | .excessDamageThisWay v => { g with excessDamageThisWay := v }
  | .destroyedForAmassThisWay v => { g with destroyedForAmassThisWay := v }
  | .amassControllerThisWay v => { g with amassControllerThisWay := v }
  | .amassAmountThisWay v => { g with amassAmountThisWay := v }
  | .amassYouControlledThisWay v => { g with amassYouControlledThisWay := v }
  | .milledIdsThisWay v => { g with milledIdsThisWay := v }
  | .pushMilledIdThisWay id => { g with milledIdsThisWay := g.milledIdsThisWay.push id }
  | .revealedIdsThisWay v => { g with revealedIdsThisWay := v }
  | .opponentsMilledThisWay v => { g with opponentsMilledThisWay := v }
  | .palantirChoiceReady v => { g with palantirChoiceReady := v }
  | .grimaImpulseReady v => { g with grimaImpulseReady := v }
  | .grimaImpulseVictim v => { g with grimaImpulseVictim := v }
  | .grimaImpulseFound v => { g with grimaImpulseFound := v }
  | .grimaImpulseOthers v => { g with grimaImpulseOthers := v }
  | .planWasSacrificed v => { g with planWasSacrificed := v }
  | .sourceWasSacrificed v => { g with sourceWasSacrificed := v }
  | .exiledIdsThisWay v => { g with exiledIdsThisWay := v }
  | .pushExiledIdThisWay id => { g with exiledIdsThisWay := g.exiledIdsThisWay.push id }
  | .notedCopyObject v => { g with notedCopyObject := v }
  | .notedHostId v => { g with notedHostId := v }
  | .handDiscardedThisWay v => { g with handDiscardedThisWay := v }
  | .notedSourceThisWay v => { g with notedSourceThisWay := v }
  | .equipmentAttachedHost v => { g with equipmentAttachedHost := v }
  | .notedCountThisWay v => { g with notedCountThisWay := v }
  | .createdTokenThisWay v => { g with createdTokenThisWay := v }
  | .putArtifactThisWay v => { g with putArtifactThisWay := v }
  | .playExiledThisWay v => { g with playExiledThisWay := v }
  | .armSurveilReturn v => { g with armSurveilReturn := v }
  | .triggerSequenceRest v => { g with triggerSequenceRest := v }
  | .setTriggerSequenceRestSteps steps =>
    match g.triggerSequenceRest with
    | none => g
    | some rest =>
      if steps.isEmpty then { g with triggerSequenceRest := none }
      else { g with triggerSequenceRest := some { rest with steps } }
  | .setTriggerSequenceRestFromMay steps =>
    match g.mayContext with
    | none => g
    | some ctx =>
      { g with
        mayContext := none
        triggerSequenceRest := if steps.isEmpty then none else some { ctx with steps } }
  | .mayThenDrop v => { g with mayThenDrop := v }
  | .mayThenSkip v => { g with mayThenSkip := v }
  | .mayThenConditional v => { g with mayThenConditional := v }
  | .mayOnAccept v => { g with mayOnAccept := v }
  | .mayOnDecline v => { g with mayOnDecline := v }
  | .mayContext v => { g with mayContext := v }
  | .sacrificedPowerThisWay v => { g with sacrificedPowerThisWay := v }
  | .mayThenResume v => { g with mayThenResume := v }
  | .triggerOr v => { g with triggerOr := v }
  | .chooseModesRest v => { g with chooseModesRest := v }
  | .unlessPaysInstead v => { g with unlessPaysInstead := v }
  | .unlessPaysController v => { g with unlessPaysController := v }
  | .unlessPaysTargets v => { g with unlessPaysTargets := v }
  | .unlessPaysDue v => { g with unlessPaysDue := v }
  | .mayEffect v => { g with mayEffect := v }
  | .mayController v => { g with mayController := v }
  | .mayTargets v => { g with mayTargets := v }
  | .spellOr v => { g with spellOr := v }
  | .spellOrController v => { g with spellOrController := v }
  | .spellOrTargets v => { g with spellOrTargets := v }
  | .spellOrLibrary v => { g with spellOrLibrary := v }
  | .surveilReturnMvAtMost v => { g with surveilReturnMvAtMost := v }
  | .surveilReturnNoncreatureNonland v => { g with surveilReturnNoncreatureNonland := v }
  | .replacementOrder ids => { g with replacementOrder := ids }
  | .pendingReplacement v => { g with pendingReplacement := v }
  | .castingFromTop v => { g with castingFromTop := v }
  | .delayedEndStepReturns v => { g with delayedEndStepReturns := v }
  | .pushDelayedEndStepReturn id cause =>
    { g with delayedEndStepReturns := g.delayedEndStepReturns.push (id, cause) }
  | .extraTurns v => { g with extraTurns := v }
  | .powerUpsForbidden v => { g with powerUpsForbidden := v }
  | .delayedEndStepExiles v => { g with delayedEndStepExiles := v }
  | .pushDelayedEndStepExile id cause =>
    { g with delayedEndStepExiles := g.delayedEndStepExiles.push (id, cause) }
  | .conniveSource v => { g with conniveSource := v }
  | .plusOneAfterDiscards v => { g with plusOneAfterDiscards := v }
  | .additionalCombatPhases v => { g with additionalCombatPhases := v }
  | .enrageGrantsAdditionalCombat v => { g with enrageGrantsAdditionalCombat := v }
  | .resolvingDivision v => { g with resolvingDivision := v }
  | .playerControl v => { g with playerControl := v }
  | .controlOnNextTakenTurn v => { g with controlOnNextTakenTurn := v }
  | .pendingLokiCopy v => { g with pendingLokiCopy := v }
  | .assignCombatDamageEqualToughness v => { g with assignCombatDamageEqualToughness := v }
  | .pendingFreeRGCreature v => { g with pendingFreeRGCreature := v }
  | .plusOneAfterSearch v => { g with plusOneAfterSearch := v }
  | .thirstDiscardsLeft v => { g with thirstDiscardsLeft := v }
  | .thirstDiscardType v => { g with thirstDiscardType := v }
  | .pendingDiscardsLeft v => { g with pendingDiscardsLeft := v }
  | .wardQueue v => { g with wardQueue := v }
  | .enqueueWard ws => { g with wardQueue := g.wardQueue ++ ws }
  | .delayedEndStepSacrifices v => { g with delayedEndStepSacrifices := v }
  | .pushDelayedEndStepSacrifice id cause =>
    { g with delayedEndStepSacrifices := g.delayedEndStepSacrifices.push (id, cause) }
  | .delayedGraveReturns v => { g with delayedGraveReturns := v }
  | .pushDelayedGraveReturn id p cause =>
    { g with delayedGraveReturns := g.delayedGraveReturns.push (id, p, cause) }
  | .delayedSynthetic v => { g with delayedSynthetic := v }
  | .pushDelayedSynthetic p n cause =>
    { g with delayedSynthetic := g.delayedSynthetic.push (p, n, cause) }
  | .eaglesBirdsCauses v => { g with eaglesBirdsCauses := v }
  | .pushEaglesBirdsCause p n cause =>
    { g with eaglesBirdsCauses := g.eaglesBirdsCauses.push (p, n, cause) }
  | .linkedExileCauses v => { g with linkedExileCauses := v }
  | .setLinkedExileCause id cause =>
    let rest := g.linkedExileCauses.filter (·.1 != id)
    { g with
      linkedExileCauses :=
        match cause with
        | some c => rest.push (id, c)
        | none => rest }
  | .untapSearchedIfLands v => { g with untapSearchedIfLands := v }
  | .ancestryLandsTapped v => { g with ancestryLandsTapped := v }
  | .pushAncestryLandTapped id =>
    { g with ancestryLandsTapped := g.ancestryLandsTapped.push id }
  | .removeAncestryLandTapped id =>
    { g with ancestryLandsTapped := g.ancestryLandsTapped.filter (· != id) }
  | .resolvingContext v => { g with resolvingContext := v }
  | .sbaChecked => g
  | .clearEvents => { g with events := #[] }

/-- Process one `GameChange` in isolation. -/
def applyChange (g : Game) (c : GameChange) : Game :=
  match c with
  | .rules r => g.applyRulesEvent r
  | .engine e => g.applyEngineChange e

/-- Active resolving source object id and controller, if a spell or ability is
currently resolving (CR 608 / 610.1). -/
def currentResolvingContext? (g : Game) : Option (Option ObjectId × Option PlayerId) :=
  let objId? := g.resolvingSpell.orElse (fun _ => g.resolvingAbility)
  match objId?.bind (fun id => g.objects.find? (·.id == id)) with
  | some o => some (o.sourceId.orElse (fun _ => some o.id), o.controller)
  | none =>
    match g.resolvingContext with
    | some (src, ctrl) => some (src, some ctrl)
    | none =>
      match g.triggerSequenceRest.orElse (fun _ => g.mayContext) with
      | some ctx => some (ctx.sourceId, some ctx.controller)
      | none =>
        match g.triggerOr with
        | some rest => some (rest.sourceId, some rest.controller)
        | none =>
          match g.chooseModesRest with
          | some rest => some (rest.sourceId, some rest.controller)
          | none =>
            if g.mayEffect.isSome then some (none, some g.mayController)
            else if !g.spellOr.isEmpty then some (none, some g.spellOrController)
            else if g.unlessPaysInstead.isSome then some (none, some g.unlessPaysController)
            else objId?.map (fun id => (some id, none))

/-- Populate a fresh `EffectId` (and fallback `source` / `controller` from the
current resolving context) on `.oneShotEffect` inside `cause`, and upgrade
`.unclassified` to `.oneShotEffect` when a spell or ability is actively
resolving (CR 610). -/
def resolveOneShotCause (g : Game) : EventCause → EventCause × Option EffectId
  | .unclassified =>
    match g.currentResolvingContext? with
    | some (src, ctrl) =>
      let actualId : EffectId := ⟨g.nextEffectId⟩
      (.oneShotEffect (some actualId) src ctrl, some actualId)
    | none => (.unclassified, none)
  | .oneShotEffect id src ctrl =>
    let actualId : EffectId := id.getD ⟨g.nextEffectId⟩
    let (defSrc, defCtrl) :=
      match g.currentResolvingContext? with
      | some (s, c) => (s, c)
      | none => (none, none)
    let src' := src.orElse (fun _ => defSrc)
    let ctrl' := ctrl.orElse (fun _ => defCtrl)
    (.oneShotEffect (some actualId) src' ctrl', some actualId)
  | .replaced rep orig =>
    let (orig', bumpId?) := g.resolveOneShotCause orig
    (.replaced rep orig', bumpId?)
  | c => (c, none)

def findObject? (g : Game) (id : ObjectId) : Option GameObject :=
  g.objects.find? (fun o => o.id == id)

def object! (g : Game) (id : ObjectId) : GameObject :=
  match g.findObject? id with
  | some o => o
  | none => panic! s!"missing object {id}"

def over (g : Game) : Bool := g.result.isSome

def player (g : Game) (p : PlayerId) : Player :=
  g.players[p.idx]!

def livingPlayers (g : Game) : Array Player :=
  g.players.filter (fun pl => !pl.lost)

/-- True while `p` has not lost and therefore has not left (CR 104 / 800.4). -/
def stillInGame (g : Game) (p : PlayerId) : Bool :=
  !(g.player p).lost

/-- Living opponents of `p` (CR 102.2). -/
def livingOpponents (g : Game) (p : PlayerId) : Array Player :=
  g.livingPlayers.filter (fun pl => pl.id != p)

def battlefield (g : Game) : Array GameObject :=
  g.objects.filter GameObject.isOnBattlefield

def permanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o => o.controlledBy p)

/-- Creatures `p` currently controls. -/
def creaturesControlledBy (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (·.isCreature)

/-- Current subtypes after Aura type-setting (e.g. Fog on the Barrow-Downs
makes the enchanted creature only a Spirit; CR 205.3m / 613.1d). -/
def currentSubtypes (g : Game) (o : GameObject) : Array CardSubtype :=
  match g.battlefield.find? (fun a =>
    a.attachedTo == some o.id &&
      a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome)) with
  | none => o.subtypes
  | some aura =>
    match aura.staticAbilities.findSome? (fun ab => ab.enchantedOnlySubtype?) with
    | some s => #[s]
    | none => o.subtypes

/-- Creature cards in `p`'s graveyard. -/
def gyCreatureCards (g : Game) (p : PlayerId) : Nat :=
  (g.player p).graveyard.filter (fun id =>
    (g.findObject? id).any (·.printed.isCreature)) |>.size

/-- Undercover Skrull: all creature types while enough creature cards are
in your graveyard. -/
def hasAllCreatureTypes (g : Game) (o : GameObject) : Bool :=
  match o.controller with
  | none => false
  | some p =>
    o.staticAbilities.any fun
      | .getsAndAllTypesIfGyCreatureCards min _ _ => g.gyCreatureCards p >= min
      | _ => false

/-- Types an attached Aura adds, including the word "legendary". -/
def auraAddedTypes (g : Game) (o : GameObject) : Array CardSubtype :=
  if !o.isOnBattlefield then #[]
  else
    g.battlefield.foldl (fun acc a =>
      if a.attachedTo != some o.id then acc
      else
        a.staticAbilities.foldl (fun acc ab =>
          match ab with
          | .enchantedCreatureGetsHasAndTypes _ _ _ types => acc ++ types
          | _ => acc) acc) #[]

/-- Whether `o` currently has subtype `s`, including Fog-style overwrites.
Changeling grants every creature type (CR 702.72 / MSH 72–73) unless a
type-setting Aura overwrites the subtypes. -/
def hasSubtype (g : Game) (o : GameObject) (s : CardSubtype) : Bool :=
  let fogged :=
    g.battlefield.any (fun a =>
      a.attachedTo == some o.id &&
        a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome))
  (g.currentSubtypes o).any (· == s) ||
    (g.auraAddedTypes o).any (· == s) ||
    (!fogged && (o.printedOrUntilEot.changeling || g.hasAllCreatureTypes o) &&
      !s.isNoncreature)

/-- The stack entry for `objectId`, if that object is on the stack. -/
def stackEntry? (g : Game) (objectId : ObjectId) : Option StackEntry :=
  g.stack.find? (fun e => e.objectId == objectId)

/-- Whether `p` currently has an enduring story. -/
def hasEnduringStory (g : Game) (p : PlayerId) : Bool :=
  (g.player p).enduringStory

/-- A permanent counts once toward Storied even if it is legendary, an
artifact, and a Saga. -/
def countsTowardStoried (_g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    (o.isLegendary || o.printed.isArtifact || o.printed.hasSubtype .saga)

/-- Number of legendary, Saga, and/or artifact permanents `p` controls. -/
def storiedPermanentCount (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (g.countsTowardStoried) |>.size

/-- Whether `p` controls a permanent with storied. -/
def controlsStoried (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.keywords.storied)

/-- Whether `p` currently has the city's blessing. -/
def hasCitysBlessing (g : Game) (p : PlayerId) : Bool :=
  (g.player p).citysBlessing

/-- Number of permanents `p` currently controls (phased-out objects do not
count). -/
def permanentCount (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).size

/-- Whether `p` controls a permanent with ascend, or a resolving spell with
ascend on the stack. -/
def controlsAscend (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.keywords.ascend) ||
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.controller == some p && o.printed.keywords.ascend &&
          o.triggeredAbility.isNone && o.abilityEffect.isNone
      | none => false)

/-- All battlefield permanents attached to `id` (Equipment, Auras, etc.),
including phased-out attachments. -/
def attachmentsOfId (g : Game) (id : ObjectId) : Array GameObject :=
  g.objects.filter (fun o => o.zone == .battlefield && o.attachedTo == some id)

/-- All battlefield permanents attached to `o` (Equipment, Auras, etc.),
including phased-out attachments. -/
def attachmentsOf (g : Game) (o : GameObject) : Array GameObject :=
  g.attachmentsOfId o.id

/-- Cards `p` has drawn this turn. Opening hands are not recorded. -/
def loggedDraws (g : Game) (p : PlayerId) : Nat :=
  GameEvent.draws g.events g.turnNumber p

/-- Life `p` has gained this turn. -/
def loggedLifeGained (g : Game) (p : PlayerId) : Nat :=
  GameEvent.lifeGained g.events g.turnNumber p

/-- Creatures that have died this turn. -/
def loggedCreatureDeaths (g : Game) : Nat :=
  GameEvent.creatureDeaths g.events g.turnNumber

/-- Spells `p` has cast this turn. -/
def loggedSpellsCast (g : Game) (p : PlayerId) : Nat :=
  GameEvent.spellsCast g.events g.turnNumber p

/-- Creature spells `p` has cast this turn. -/
def loggedCreatureSpells (g : Game) (p : PlayerId) : Nat :=
  GameEvent.creatureSpells g.events g.turnNumber p

/-- Noncreature spells `p` has cast this turn. -/
def loggedNoncreatureSpells (g : Game) (p : PlayerId) : Nat :=
  GameEvent.noncreatureSpells g.events g.turnNumber p

/-- Creatures `p` has attacked with this turn. -/
def loggedAttacks (g : Game) (p : PlayerId) : Nat :=
  GameEvent.attacks g.events g.turnNumber p

/-- Cards milled from `p`'s library this turn. -/
def loggedMilled (g : Game) (p : PlayerId) : Nat :=
  GameEvent.milled g.events g.turnNumber p

/-- `p` has scried at least one card this turn. Scry 0 does not count. -/
def loggedScried (g : Game) (p : PlayerId) : Bool :=
  GameEvent.scried g.events g.turnNumber p

/-- `p` has surveilled this turn. Surveil 0 does not count. -/
def loggedSurveilled (g : Game) (p : PlayerId) : Bool :=
  GameEvent.surveilled g.events g.turnNumber p

/-- An artifact has entered under `p`'s control this turn. -/
def loggedArtifactEntered (g : Game) (p : PlayerId) : Bool :=
  GameEvent.artifactEntered g.events g.turnNumber p

/-- `p` has attacked with a permanent of `subtype` this turn. -/
def loggedAttackedWithSubtype (g : Game) (p : PlayerId) (subtype : CardSubtype) : Bool :=
  GameEvent.attackedWithSubtype g.events g.turnNumber p subtype

/-- A permanent of `subtype` has entered under `p`'s control this turn. -/
def loggedSubtypeEntered (g : Game) (p : PlayerId) (subtype : CardSubtype) : Bool :=
  GameEvent.subtypeEntered g.events g.turnNumber p subtype

/-- `p` has activated a loyalty ability this turn. -/
def loggedActivatedLoyalty (g : Game) (p : PlayerId) : Bool :=
  GameEvent.activatedLoyalty g.events g.turnNumber p

/-- `p` was dealt noncombat damage this turn. -/
def loggedNoncombatDamage (g : Game) (p : PlayerId) : Bool :=
  GameEvent.dealtNoncombat g.events g.turnNumber p

/-- `p` was dealt noncombat damage last turn. -/
def loggedNoncombatDamageLastTurn (g : Game) (p : PlayerId) : Bool :=
  g.turnNumber > 0 && GameEvent.dealtNoncombat g.events (g.turnNumber - 1) p

/-- `id` entered the battlefield this turn. -/
def loggedEntered (g : Game) (id : ObjectId) : Bool :=
  GameEvent.objectEntered g.events g.turnNumber id

/-- Equip abilities `p` has completed this turn. -/
def loggedEquipActivations (g : Game) (p : PlayerId) : Nat :=
  GameEvent.equipActivations g.events g.turnNumber p

/-- Mana values of spells `p` has cast this turn, oldest first. -/
def loggedCastManaValues (g : Game) (p : PlayerId) : Array Nat :=
  GameEvent.castManaValues g.events g.turnNumber p

/-- Cards `p` has discarded this turn. -/
def loggedDiscards (g : Game) (p : PlayerId) : Nat :=
  GameEvent.discards g.events g.turnNumber p

/-- Life `p` has lost this turn. -/
def loggedLifeLost (g : Game) (p : PlayerId) : Nat :=
  GameEvent.lifeLost g.events g.turnNumber p

/-- Resolutions `p`'s counting ability has recorded this turn. -/
def loggedResolutions (g : Game) (p : PlayerId) : Nat :=
  GameEvent.resolutions g.events g.turnNumber p

/-- `ab` on `sourceId` has triggered this turn (CR 603.2h). -/
def loggedTriggeredThisTurn (g : Game) (sourceId : ObjectId) (ab : TriggeredAbility) : Bool :=
  GameEvent.abilityTriggeredThisTurn g.events g.turnNumber sourceId ab

/-- An ability on `sourceId` has triggered this turn (CR 603.2h). -/
def loggedSourceTriggeredThisTurn (g : Game) (sourceId : ObjectId) : Bool :=
  GameEvent.sourceTriggeredThisTurn g.events g.turnNumber sourceId

/-- Lands `p` has played this turn. -/
def loggedLandsPlayed (g : Game) (p : PlayerId) : Nat :=
  GameEvent.landsPlayed g.events g.turnNumber p

/-- Graveyard ids of creatures that died this turn. -/
def loggedCreaturesToGraveyard (g : Game) : Array ObjectId :=
  GameEvent.creaturesToGraveyard g.events g.turnNumber

/-- Graveyard id of the most recent attacking creature that died. -/
def loggedLastDiedAttacker (g : Game) : Option ObjectId :=
  GameEvent.lastDiedAttacker g.events

/-- Permanent that most recently became tapped. -/
def loggedLastBecameTapped (g : Game) : Option ObjectId :=
  GameEvent.lastBecameTapped g.events

/-- Player most recently dealt combat damage. -/
def loggedLastCombatDamagePlayer (g : Game) : Option PlayerId :=
  GameEvent.lastCombatDamagePlayer g.events

/-- The Sensational She-Hulk has dealt damage this turn. -/
def loggedSheHulkDealtDamage (g : Game) : Bool :=
  GameEvent.sheHulkDealtDamageThisTurn g.events g.turnNumber

/-- True when `id` has been dealt a positive amount of damage by a source with
deathtouch since the last time state-based actions were checked (CR 704.5h). -/
def deathtouchDealtSinceLastSba (g : Game) (id : ObjectId) : Bool :=
  g.events.foldl (fun dealt e =>
    match e.change with
    | .engine .sbaChecked => false
    | .rules (.damage (.dealt pkts)) =>
      dealt || pkts.any (fun pkt =>
        pkt.amount > 0 && pkt.source.keywords.deathtouch &&
          match pkt.recipient with
          | .permanent c => c.id == some id
          | _ => false)
    | _ => dealt) false

/-- Apply `f` to each living opponent of `controller`. -/
def forEachOpponent (g : Game) (controller : PlayerId) (f : Game → PlayerId → Game) :
    Game :=
  g.livingOpponents controller |>.foldl (fun g pl => f g pl.id) g

/-- Player targets for every member of `ps` who does not have protection
from everything. -/
def playerTargets (ps : Array Player) : Array Target :=
  ps.filter (fun pl => !pl.protectionFromEverything) |>.map (fun pl =>
    Target.player pl.id)

/-- Living players in turn order from `start` who satisfy `eligible`. -/
def playersInOrderFrom (g : Game) (start : PlayerId) (eligible : Player → Bool) :
    Array PlayerId :=
  let n := g.players.size
  Id.run do
    let mut acc : Array PlayerId := #[]
    for k in [0:n] do
      let q : PlayerId := ⟨(start.idx + k) % n⟩
      if eligible (g.player q) then
        acc := acc.push q
    return acc

def opponent (g : Game) (p : PlayerId) : PlayerId :=
  let living := g.livingPlayers
  if living.size == 2 then
    if living[0]!.id == p then living[1]!.id else living[0]!.id
  else
    PlayerId.mk ((p.idx + 1) % g.players.size)

/-- Last-known `before` snapshot of `id` when it left the battlefield, read from
`ZoneEvent.moved` in `g.events` (CR 113.7a / 608.2h). -/
def lastKnownBefore? (g : Game) (id : ObjectId) : Option EventObject :=
  g.events.reverse.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved before _ .battlefield _ _ _ _ _)) =>
      if before.id == some id then some before else none
    | _ => none)

/-- Defending player of an attacking status `s`: the player directly attacked,
or the controller of the planeswalker/battle being attacked (CR 506.2 / 506.4c). -/
def defendingPlayerOfStatus (g : Game) (s : Status) : Option PlayerId :=
  match s.attackingTarget with
  | some (.player p) => some p
  | some (.planeswalker pw) | some (.battle pw) =>
    match g.findObject? pw with
    | some o => some (o.controller.getD o.owner)
    | none =>
      match g.lastKnownBefore? pw with
      | some o => some (o.controller.getD o.owner)
      | none => none
  | none => none

/-- Player being attacked this combat (CR 508.1). Taken from an attacking
creature's `attackingTarget`, or the next opponent if none is recorded. -/
def defendingPlayer (g : Game) : PlayerId :=
  match g.blockersQueue[0]? with
  | some p => p
  | none =>
    match g.objects.findSome? (fun o =>
      if o.isOnBattlefield && o.status.attacking then g.defendingPlayerOfStatus o.status else none) with
    | some p => p
    | none => g.opponent g.activePlayer

/-- Defending player of an attacking object `o` (CR 506.2 / 506.4c), falling
back to `g.defendingPlayer`. -/
def defendingPlayerOf (g : Game) (o : GameObject) : PlayerId :=
  (g.defendingPlayerOfStatus o.status).getD g.defendingPlayer

/-- Distinct players being attacked, in APNAP order (CR 508.1 / 101.4). -/
def defendingPlayers (g : Game) : Array PlayerId :=
  let attacked :=
    g.objects.filterMap (fun o =>
      if o.isOnBattlefield && o.status.attacking then g.defendingPlayerOfStatus o.status else none)
  let n := g.players.size
  Id.run do
    let mut acc : Array PlayerId := #[]
    for k in [0:n] do
      let q : PlayerId := ⟨(g.activePlayer.idx + k) % n⟩
      if q != g.activePlayer && !(g.player q).lost && attacked.contains q then
        acc := acc.push q
    return acc

/-- Player who must declare blockers now. -/
def currentBlockersPlayer (g : Game) : PlayerId :=
  g.defendingPlayer

/-- Legal attack destination: a living opponent of `p` (CR 508.1). Omitted
means the next opponent in turn order. -/
def resolveAttackDestination (g : Game) (p : PlayerId) (defender : Option PlayerId) :
    Except String PlayerId :=
  match defender with
  | none => .ok (g.opponent p)
  | some d =>
    if d == p then throw "cannot attack yourself"
    else if (g.player d).lost then throw s!"{(g.player d).name} has already lost"
    else if !(g.livingOpponents p).any (fun pl => pl.id == d) then
      throw s!"{(g.player d).name} is not an opponent"
    else .ok d

def nextLiving (g : Game) (p : PlayerId) : PlayerId :=
  let n := g.players.size
  Id.run do
    for k in [1:n+1] do
      let q : PlayerId := ⟨(p.idx + k) % n⟩
      if !(g.player q).lost then
        return q
    return p

/-- Player who receives priority in place of `p` when `p` has left (CR 800.4j). -/
def priorityInstead (g : Game) (p : PlayerId) : PlayerId :=
  if (g.player p).lost then g.nextLiving p else p

/-- How many creatures `p` currently controls. -/
def countCreaturesControlledBy (g : Game) (p : PlayerId) : Nat :=
  (g.creaturesControlledBy p).size

/-- How many artifacts `p` currently controls. -/
def countArtifactsControlledBy (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (fun o => o.printed.isArtifact) |>.size

/-- Artifacts on the battlefield not controlled by `controller`. -/
def countOpponentArtifacts (g : Game) (controller : PlayerId) : Nat :=
  g.battlefield.filter (fun o =>
    o.printed.isArtifact && !o.controlledBy controller) |>.size

/-- Equipment attached to `o` (Whiplash last-known X). -/
def attachedEquipmentCount (g : Game) (o : GameObject) : Nat :=
  g.battlefield.filter (fun eq =>
    eq.printed.isEquipment && eq.attachedTo == some o.id) |>.size

/-- Whether `you` currently control `them`. In Two-Headed Giant, controlling
a player also controls their teammate (MSH 236). -/
def controlsPlayer (g : Game) (you them : PlayerId) : Bool :=
  match g.playerControl with
  | some (a, b) =>
    a == you && (b == them || (g.player b).teammate == some them)
  | none => false

/-- Resources used to pay `actingAs`'s costs: always that player's, even if
another player is making the choices (MSH 346). -/
def resourcesFor (g : Game) (actingAs : PlayerId) : PlayerId :=
  let _ := g
  actingAs

/-- You still make your own choices while controlling another player
(MSH 334) and you make all of that player's choices (MSH 336). -/
def decidesFor (g : Game) (actor whose : PlayerId) : Bool :=
  match g.playerControl with
  | some (you, them) =>
    if whose == them then actor == you else actor == whose
  | none => actor == whose

/-- You can see everything the controlled player can see (MSH 335). -/
def canSeeAs (g : Game) (viewer whose : PlayerId) : Bool :=
  viewer == whose || g.controlsPlayer viewer whose

/-- Cards in `whose` hand that `viewer` may look at. -/
def visibleHand (g : Game) (viewer whose : PlayerId) : Array GameObject :=
  if g.canSeeAs viewer whose then
    (g.player whose).hand.filterMap (fun id => g.findObject? id)
  else #[]

/-- Controlling a player does not let you look at their sideboard
(MSH 349). -/
def canLookAtSideboard (_g : Game) (viewer whose : PlayerId) : Bool :=
  viewer == whose

/-- You cannot have a player you're controlling choose a card from
outside the game (MSH 349). -/
def canChooseOutsideGame (g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose && !g.controlsPlayer actor whose

/-- Tournament-rule decisions stay with the actual player (MSH 350). -/
def canMakeTournamentDecision (g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose && !g.controlsPlayer actor whose

/-- You cannot make illegal choices for a player you control (MSH 351). -/
def canMakeIllegalDecision (_g : Game) (_actor _whose : PlayerId) : Bool :=
  false

/-- The controlling player cannot concede for the controlled player
(MSH 352). That player may still concede. -/
def canConcedeAs (_g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose

/-- Last-known `CounterBag` of `id` when it left the battlefield, read from
`ZoneEvent.moved` in `g.events` (CR 113.7a / 608.2h). -/
def lastKnownCounters (g : Game) (id : ObjectId) : CounterBag :=
  match g.lastKnownBefore? id with
  | some before => before.counters
  | none => #[]

/-- Last-known counter `Status` of `id` when it left the battlefield, read from
`ZoneEvent.moved` in `g.events` (CR 113.7a / 608.2h). -/
def lastKnownCounterStatus? (g : Game) (id : ObjectId) : Option Status :=
  (g.lastKnownBefore? id).map (fun before => ({} : Status).withCounterBag before.counters)

/-- Player putting counters: the resolving spell or ability's controller,
or `fallback` when none is resolving. -/
def counterPutter (g : Game) (fallback : Option PlayerId) : Option PlayerId :=
  ((g.resolvingSpell.orElse (fun _ => g.resolvingAbility)).bind g.findObject?).bind
    (·.controller) |>.orElse (fun _ => fallback)

/-- Living players in APNAP order (CR 101.4), starting from `g.activePlayer`. -/
def apnapPlayers (g : Game) : Array PlayerId :=
  let n := g.players.size
  if n == 0 then #[]
  else
    let start := g.activePlayer.idx
    (List.range n).toArray.filterMap fun offset =>
      let pl := g.players[(start + offset) % n]!
      if pl.lost then none else some pl.id

/-- Wrap `cause` in `EventCause.replaced id orig` when replacement or prevention
effect `id` applies (CR 614.6 / 615.6). Preserves batch/resolving-context cause
upgrade when `cause` is `none`, without minting a `.oneShotEffect` outside an
active spell or ability resolution. -/
def wrapReplacedCause (_g : Game) (id : ReplacementId) (cause : Option EventCause)
    (_defaultActor : Option PlayerId := none) : Option EventCause :=
  some (.replaced id (cause.getD .unclassified))

/-- Whether two replacement/prevention effects in the same CR 616.1a–e tier
produce an identical outcome regardless of application order, so the engine
can apply either first without pausing for `Pending.chooseReplacement` when no
explicit `g.replacementOrder` preference is set. -/
def replacementPairCommutes (a b : ReplacementOrPrevention) : Bool :=
  match a, b with
  | .replacement sa, .replacement sb =>
    match sa.kind, sb.kind with
    | .entersTappedSelf _, .entersTappedSelf _
    | .entersTappedExternal _, .entersTappedExternal _
    | .entersTappedSelf _, .entersTappedExternal _
    | .entersTappedExternal _, .entersTappedSelf _ => true
    | .entersTappedSelf _, .entersWithCountersSelf ..
    | .entersWithCountersSelf .., .entersTappedSelf _ => true
    | .entersWithCountersSelf _ ka _, .entersWithCountersSelf _ kb _ => ka != kb
    | .entersWithExtraCounters _ ka na, .entersWithExtraCounters _ kb nb => ka != kb || na == nb
    | .modifyCountersPut _ ka addA multA, .modifyCountersPut _ kb addB multB =>
      (ka.isSome && kb.isSome && ka != kb) ||
      (multA == 1 && multB == 1) || (addA == 0 && addB == 0)
    | .addNoncombatDamage _ _, .addNoncombatDamage _ _ => true
    | .multiplyDamage _ _, .multiplyDamage _ _ => true
    | .modifyLifeGain _ addA multA, .modifyLifeGain _ addB multB =>
      (multA == 1 && multB == 1) || (addA == 0 && addB == 0)
    | .replaceDraw _ fA exA, .replaceDraw _ fB exB => fA == fB && exA == exB
    | .extraDrawOnConnive _ _, .extraDrawOnConnive _ _ => true
    | .createExtraTokenWithFood _ _, .createExtraTokenWithFood _ _ => true
    | .multiplyTokenCreation _ _, .multiplyTokenCreation _ _ => true
    | .createExtraTokenWithFood _ _, .multiplyTokenCreation _ _
    | .multiplyTokenCreation _ _, .createExtraTokenWithFood _ _ => true
    | .stunCounterUntap _, .stunCounterUntap _ => true
    | _, _ => false
  | .prevention pa, .prevention pb =>
    match pa.kind, pb.kind with
    | .shieldCounterPreventDamage _, _ | _, .shieldCounterPreventDamage _ => false
    | _, _ => true
  | .prevention pa, .replacement sb =>
    match pa.kind, sb.kind with
    | .shieldCounterPreventDamage _, _ => false
    | _, .addNoncombatDamage _ _ | _, .multiplyDamage _ _ => true
    | _, _ => false
  | .replacement sa, .prevention pb =>
    match sa.kind, pb.kind with
    | _, .shieldCounterPreventDamage _ => false
    | .addNoncombatDamage _ _, _ | .multiplyDamage _ _, _ => true
    | _, _ => false

private def poolAllCommute (pool : Array ReplacementCandidate) : Bool :=
  Id.run do
    for i in [0:pool.size] do
      for j in [i+1:pool.size] do
        if !replacementPairCommutes pool[i]!.spec pool[j]!.spec then
          return false
    return true

/-- Selection outcome of one step in the CR 616.1 replacement/prevention loop. -/
inductive ReplacementSelection where
  /-- No unapplied candidate remains. -/
  | none
  /-- `candidate` is selected; `remainingOrder` has consumed `candidate.id` if it was chosen from `replacementOrder`. -/
  | chosen (candidate : ReplacementCandidate) (remainingOrder : Array ReplacementId)
  /-- Multiple non-commuting candidates tie for the affected player `chooser` with no preference in `replacementOrder`; pause for `Pending.chooseReplacement`. -/
  | needChoice (chooser : PlayerId) (choices : Array ReplacementId) (remainingOrder : Array ReplacementId)
deriving Repr, Inhabited, BEq

/-- Select the next replacement or prevention step according to CR 616.1:
1. Filter out candidates whose `id` is already in `applied` (CR 614.5).
2. Restrict to the lowest applicable `ReplacementTier` rank (`616.1a`–`e`).
3. If multiple players are affected, the first affected player in APNAP order
   (CR 101.4 / 616.1) chooses among candidates affecting them.
4. Consult `order` (`g.replacementOrder`, set via `Pending.chooseReplacement` /
   `Action.chooseReplacement`) for the affected player's choice, consuming that
   entry when matched; if no preference matches and multiple non-commuting
   candidates tie in `pool`, return `.needChoice chooser (pool.map (·.id)) order`. -/
def selectNextReplacementStep (g : Game) (candidates : Array ReplacementCandidate)
    (applied : Array ReplacementId)
    (order : Array ReplacementId := g.replacementOrder) : ReplacementSelection :=
  let unapplied := candidates.filter (fun (c : ReplacementCandidate) => !applied.contains c.id)
  if unapplied.isEmpty then .none
  else
    let minRank := unapplied.foldl (fun m (c : ReplacementCandidate) => min m c.tier.rank) 100
    let inTier := unapplied.filter (fun (c : ReplacementCandidate) => c.tier.rank == minRank)
    let apnap := g.apnapPlayers
    let chooser? := apnap.find? (fun p => inTier.any (fun (c : ReplacementCandidate) => c.affectedPlayer == p))
    let chooser := chooser?.getD (inTier[0]!.affectedPlayer)
    let pool :=
      match chooser? with
      | some p => inTier.filter (fun (c : ReplacementCandidate) => c.affectedPlayer == p)
      | none => inTier
    match order.findSome? (fun prefId => pool.find? (fun (c : ReplacementCandidate) => c.id == prefId)) with
    | some c => .chosen c (order.filter (· != c.id))
    | none =>
      if pool.size <= 1 || poolAllCommute pool then
        match pool[0]? with
        | some c => .chosen c order
        | none => .none
      else
        .needChoice chooser (pool.map (·.id)) order

/-- Select the next replacement or prevention candidate according to CR 616.1. -/
def selectNextReplacement (g : Game) (candidates : Array ReplacementCandidate)
    (applied : Array ReplacementId) : Option ReplacementCandidate :=
  match g.selectNextReplacementStep candidates applied with
  | .chosen c _ => some c
  | .none => none
  | .needChoice _ _ _ =>
    let unapplied := candidates.filter (fun (c : ReplacementCandidate) => !applied.contains c.id)
    let minRank := unapplied.foldl (fun m (c : ReplacementCandidate) => min m c.tier.rank) 100
    let inTier := unapplied.filter (fun (c : ReplacementCandidate) => c.tier.rank == minRank)
    inTier[0]?

/-- Distinct per-`CounterKind` offset so a source with `.extraCounterOnPermanents`
gets a distinct `ReplacementId` per kind of counter put on a permanent ("that
many plus one of each of those kinds of counters", CR 614.5). -/
private def counterKindRankOffset : CounterKind → Nat
  | .plusOnePlusOne => 0
  | .minusOneMinusOne => 1
  | .loyalty => 2
  | .hope => 3
  | .charge => 4
  | .stun => 5
  | .shield => 6
  | .finality => 7
  | .plan => 8
  | .burden => 9
  | .quest => 10
  | .invasion => 11
  | .influence => 12
  | .trample => 13
  | .indestructible => 14
  | .lifelink => 15
  | .hone => 16
  | .shadow => 17
  | .lore => 18
  | .story => 19
  | .time => 20
  | .haste => 21
  | .vigilance => 22
  | .flying => 23
  | .menace => 24
  | .reach => 25
  | .deathtouch => 26
  | .firstStrike => 27
  | .doubleStrike => 28
  | .poison => 29

/-- CR 616.1 replacement loop for putting `n` counters of `kind` on `target`
(CR 122.6 / 614.1a / 614.12), returning `(count, applied, cause, choice?, remainingOrder)`. -/
def replaceCountersPutChoice (g : Game) (target : GameObject) (kind : CounterKind) (n : Nat)
    (putter : Option PlayerId := none) (entersWith : Bool := false)
    (entering : Option GameObject := none)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none)
    (order : Array ReplacementId := g.replacementOrder) :
    Nat × Array ReplacementId × Option EventCause × Option (PlayerId × Array ReplacementId) × Array ReplacementId :=
  if n == 0 then (0, applied, cause, none, order)
  else
    let who :=
      if entersWith then target.controller
      else putter.orElse (fun _ => g.counterPutter target.controller)
    let affected := target.controller.orElse (fun _ => who) |>.getD target.owner
    Id.run do
      let mut curN := n
      let mut curApplied := applied
      let mut curCause := cause
      let mut curOrder := order
      let mut choice? : Option (PlayerId × Array ReplacementId) := none
      let mut fuel := 32
      while fuel > 0 do
        fuel := fuel - 1
        if curN == 0 then
          fuel := 0
        else
          let mut specs : Array (ReplacementSpec × Nat × Nat) := #[]
          -- Battlefield permanents controlled by `target.controller`
          match target.controller with
          | some c =>
            let perms := g.permanentsOf c
            let allPerms :=
              match entering with
              | some ent =>
                if !ent.status.faceDown && ent.controller == some c &&
                    !perms.any (·.id == ent.id) then
                  perms.push ent
                else perms
              | none => perms
            for o in allPerms do
              -- Doc Samson: `.extraCounterOnPermanents` (requires putter == controller)
              if who == some c && o.printed.staticAbilities.any (· == .extraCounterOnPermanents) then
                let rid : ReplacementId := ⟨o.id.raw * 1000 + 101 + counterKindRankOffset kind⟩
                specs := specs.push (
                  { id := rid
                    source := some o.id
                    controller := some c
                    affectedPlayer := affected
                    kind := .modifyCountersPut target.id (some kind) 1 1 }, 1, 1)
              -- The Golden Gear: `.fra .extraPlusOneCounter` on a creature you control
              if kind == .plusOnePlusOne && target.isCreature &&
                  (!o.status.faceDown && o.staticAbilities.any (· == .fra .extraPlusOneCounter)) then
                let rid : ReplacementId := ⟨o.id.raw * 1000 + 102⟩
                specs := specs.push (
                  { id := rid
                    source := some o.id
                    controller := some c
                    affectedPlayer := affected
                    kind := .modifyCountersPut target.id (some .plusOnePlusOne) 1 1 }, 1, 1)
          | none => pure ()
          -- Active `ContinuousEffect.replacement` effects matching `modifyCountersPut`
          for (_, eff) in g.activeEffects do
            match eff with
            | .replacement spec _ =>
              match spec.kind with
              | .modifyCountersPut tid k? add mult =>
                if (tid == target.id || tid == ⟨0⟩) && (k?.isNone || k? == some kind) then
                  specs := specs.push (spec, add, mult)
              | _ => pure ()
            | _ => pure ()
          let candidates := specs.map (fun (s, _, _) => (ReplacementOrPrevention.replacement s).toCandidate)
          match g.selectNextReplacementStep candidates curApplied curOrder with
          | .none => fuel := 0
          | .needChoice chooser choices ord' =>
            curOrder := ord'
            choice? := some (chooser, choices)
            fuel := 0
          | .chosen chosen ord' =>
            curOrder := ord'
            match specs.find? (fun (s, _, _) => s.id == chosen.id) with
            | none => fuel := 0
            | some (_, add, mult) =>
              curN := curN * mult + add
              curApplied := curApplied.push chosen.id
              curCause := g.wrapReplacedCause chosen.id curCause who
      return (curN, curApplied, curCause, choice?, curOrder)

/-- CR 616.1 replacement loop for putting `n` counters of `kind` on `target`
(CR 122.6 / 614.1a / 614.12). Supports printed static abilities
(`.extraCounterOnPermanents`, `.extraPlusOneCounter`) on battlefield permanents
and on `entering?` (when `target` is about to enter the battlefield, CR 614.12),
as well as active `ContinuousEffect.replacement` specs with `.modifyCountersPut`.
Returns the modified count, the updated `applied` list (CR 614.5), and the
updated `EventCause` (CR 614.6). -/
def replaceCountersPut (g : Game) (target : GameObject) (kind : CounterKind) (n : Nat)
    (putter : Option PlayerId := none) (entersWith : Bool := false)
    (entering : Option GameObject := none)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none) : Nat × Array ReplacementId × Option EventCause :=
  let (n', app', c', _, _) :=
    g.replaceCountersPutChoice target kind n (putter := putter) (entersWith := entersWith)
      (entering := entering) (applied := applied) (cause := cause)
  (n', app', c')

/-- Extra counters from each Doc Samson `putter` controls, when that player
also controls the permanent (`host`) (MSH 517 / 590). -/
def docSamsonBonus (g : Game) (putter host : Option PlayerId) : Nat :=
  match putter, host with
  | some p, some c =>
    if p != c then 0
    else
      ((g.permanentsOf p).filter (fun o =>
        o.printed.staticAbilities.any (fun
          | .extraCounterOnPermanents => true
          | _ => false))).size
  | _, _ => 0

/-- `n`, plus one of that kind per Doc Samson, when `putter` puts counters
on a permanent controlled by `host`. Zero stays zero. `host` defaults to
`putter`. -/
def extraCountersOn (g : Game) (putter : Option PlayerId) (n : Nat)
    (host : Option PlayerId := putter) : Nat :=
  if n == 0 then 0
  else
    match host with
    | some c =>
      let dummy : GameObject := { id := ⟨0⟩, printed := default, owner := c, controller := some c, zone := .battlefield }
      (g.replaceCountersPut dummy .charge n (putter := putter)).1
    | none => n

/-- Counters of one kind actually put on `o`. An enters-with replacement is
put by the permanent's controller (ruling 517). Otherwise the explicit
`putter`, the resolving spell or ability, or `o`'s controller. -/
def countersYouPut (g : Game) (o : GameObject) (n : Nat)
    (putter : Option PlayerId := none) (entersWith := false)
    (kind : CounterKind := .charge) : Nat :=
  (g.replaceCountersPut o kind n (putter := putter) (entersWith := entersWith)).1

/-- Extra +1/+1 counters from each permanent `o`'s controller controls with
`.extraPlusOneCounter` (The Golden Gear, CR 614.1a / 614.12). -/
def extraPlusOneOnCreature (g : Game) (o : GameObject) (n : Nat) : Nat :=
  if n == 0 || !o.isCreature then n
  else
    match o.controller with
    | none => n
    | some p =>
      let others := ((g.permanentsOf p).filter (fun x =>
        x.id != o.id && x.staticAbilities.any (· == .fra .extraPlusOneCounter))).size
      let self :=
        if !o.status.faceDown && o.staticAbilities.any (· == .fra .extraPlusOneCounter) then 1
        else 0
      n + others + self

/-- `extraCountersOn` extended to account for `entering`'s own
`.extraCounterOnPermanents` ability when `entering` is not yet in
`g.permanentsOf` (CR 614.12). -/
def extraCountersOnEntering (g : Game) (entering : GameObject) (n : Nat)
    (putter : Option PlayerId := entering.controller)
    (kind : CounterKind := .charge) : Nat :=
  (g.replaceCountersPut entering kind n (putter := putter) (entersWith := true)
    (entering := some entering)).1

/-- Legal players, planeswalkers, and battles that a creature put onto the
battlefield attacking under `controller`'s control may be chosen to attack
(CR 508.4). -/
def legalEnteringAttackTargets (g : Game) (controller : PlayerId) : Array AttackTarget :=
  let opps := g.livingOpponents controller
  let playerTargets : Array AttackTarget :=
    if opps.isEmpty then #[.player g.defendingPlayer]
    else opps.map (fun pl => .player pl.id)
  let noJace := (g.player controller).cantAttackJaces
  let permanentTargets : Array AttackTarget :=
    g.battlefield.filterMap fun o =>
      if !opps.any (fun pl => o.controlledBy pl.id) then none
      else if o.printed.isPlaneswalker then
        if noJace && (o.name.startsWith "Jace" || g.hasSubtype o .jace) then none
        else some (.planeswalker o.id)
      else if o.hasType .battle then
        some (.battle o.id)
      else none
  playerTargets ++ permanentTargets

/-- Mana value of other spells `p` has cast this turn. Copies that were not
cast are not recorded. -/
def otherCastManaValueThisTurn (g : Game) (p : PlayerId) : Nat :=
  (g.loggedCastManaValues p).foldl (· + ·) 0

/-- Lands `p` currently controls (CR 305.1). -/
def landsYouControl (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (·.printed.isLand) |>.size

/-- Whether `o` currently has a “P/T equal to lands you control” ability.
This characteristic-defining ability functions in all zones (CR 208.2a / 604.3). -/
def hasLandsYouControlPT (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isLandsYouControlPT

/-- Power or toughness from a lands-you-control CDA (CR 208.2a / 604.3). -/
def landsYouControlPT (g : Game) (o : GameObject) : Int :=
  Int.ofNat (g.landsYouControl o.you)

/-- Characteristic power or toughness before pumps, counters, and attached
bonuses: an until-EOT layer-7b set on the battlefield, else lands you control
when that CDA applies (in all zones), else the printed value
(CR 208.2a / 604.3 / 613.3). -/
def characteristicBase (g : Game) (o : GameObject) (printed setBase : Option Int) : Int :=
  let fromCdaOrPrinted :=
    if g.hasLandsYouControlPT o then g.landsYouControlPT o else printed.getD 0
  if o.isOnBattlefield then setBase.getD fromCdaOrPrinted else fromCdaOrPrinted

/-- Layer-7b “power becomes the number of cards in your hand” (Ms. Marvel).
This overwrites an earlier effect that set power (ruling 640). -/
def hasHandSizeSetPower (o : GameObject) : Bool :=
  o.status.cardsInHandPowerUntilEot ||
    o.status.grantedStaticAbilities.any StaticAbility.isCardsInHandPower

/-- Printed layer-7a “power equal to the number of cards in your hand”
(Minas Tirith Garrison). A layer-7b set overwrites it. -/
def hasPrintedCardsInHandPower (o : GameObject) : Bool :=
  o.printed.staticAbilities.any StaticAbility.isCardsInHandPower

/-- Characteristic power and toughness before pumps, counters, and attached
bonuses: an until-EOT layer-7b set on the battlefield, else lands you control
when that CDA applies (in all zones), else the printed values
(CR 208.2a / 604.3 / 613.3). -/
def hasCreaturesYouControlPower (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isCreaturesYouControlPower

/-- Subtype whose count defines this creature's power, if any. -/
def powerEqualSubtype? (o : GameObject) : Option CardSubtype :=
  o.staticAbilities.foldl (fun acc ab =>
    match acc, ab with
    | none, .powerEqualSubtypeYouControl s => some s
    | acc, _ => acc) none

/-- True when `o` is Super-Adaptoid's characteristic-defining power (MSH 290). -/
def hasSuperAdaptoidPowerCda (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .powerEqualLegendaryCreaturesYouControl => true
    | _ => false)

/-- Number of card types among cards in all graveyards (Tarmogoyf). Card
types, not cards, are counted, and supertypes are not card types (rulings
797 / 800). -/
def graveyardCardTypeCount (g : Game) : Nat :=
  let types := g.objects.foldl (fun acc o =>
    match o.zone with
    | .graveyard _ => o.printed.types.foldl (fun acc t =>
        if acc.contains t then acc else acc.push t) acc
    | _ => acc) (#[] : Array CardType)
  types.size

/-- True when `o` has Tarmogoyf's characteristic-defining ability. It works
in every zone, including the graveyard (ruling 799). -/
def hasGraveyardCardTypesPT (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .ptEqualGraveyardCardTypes => true
    | _ => false)

/-- Basic land types among lands `p` controls (domain; CR 305.6). -/
def basicLandTypesAmong (g : Game) (p : PlayerId) : Nat :=
  (#[CardSubtype.plains, .island, .swamp, .mountain, .forest].filter (fun t =>
    (g.permanentsOf p).any (fun o => o.printed.isLand && o.hasSubtype t))).size

def characteristicBasePT (g : Game) (o : GameObject) : Int × Int :=
  if o.status.faceDown then (2, 2)
  else if o.isOnBattlefield && o.status.animatedConstruct55 then
    (o.status.setBasePower.getD 5, o.status.setBaseToughness.getD 5)
  else if o.staticAbilities.any (· == StaticAbility.fra .powerEqualsBasicLandTypes) then
    let cda : Int := Int.ofNat (g.basicLandTypesAmong o.you)
    let power := if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
    (power, g.characteristicBase o o.printed.toughness o.status.setBaseToughness)
  else if hasGraveyardCardTypesPT o then
    let n : Int := Int.ofNat g.graveyardCardTypeCount
    -- Ruling 776: a layer-7b set (Multiply by Zero) overrides this CDA.
    if o.isOnBattlefield then
      (o.status.setBasePower.getD n, o.status.setBaseToughness.getD (n + 1))
    else (n, n + 1)
  else
  let power :=
    if hasHandSizeSetPower o then
      -- Ms. Marvel (ruling 640): this layer-7b set overwrites earlier sets.
      Int.ofNat (g.player o.you).hand.size
    else if hasPrintedCardsInHandPower o then
      let cda : Int := Int.ofNat (g.player o.you).hand.size
      if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
    else if let some subtype := powerEqualSubtype? o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p => p.hasSubtype subtype) |>.size)
      if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
    else if hasSuperAdaptoidPowerCda o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p =>
          p.isCreature && p.isLegendary) |>.size)
      if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
    else if g.hasCreaturesYouControlPower o then
      let fromTeam : Int :=
        Int.ofNat (g.countCreaturesControlledBy o.you)
      if o.isOnBattlefield then o.status.setBasePower.getD fromTeam else fromTeam
    else
      g.characteristicBase o o.printed.power o.status.setBasePower
  (power, g.characteristicBase o o.printed.toughness o.status.setBaseToughness)

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def characteristicBasePower (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).1

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def characteristicBaseToughness (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).2

/-- Componentwise sum of two power/toughness bonuses. -/
def addStats (a b : Int × Int) : Int × Int :=
  (a.1 + b.1, a.2 + b.2)

/-- True when `src` is a lord that can grant an ability to `target` (CR 604.2). -/
def isLordOf (src target : GameObject) : Bool :=
  src.id != target.id &&
  src.isOnBattlefield &&
  target.isOnBattlefield &&
  src.controller == target.controller &&
  src.controller.isSome &&
  target.isCreature

/-- Printed legendary, or an Aura that adds the legendary supertype. -/
def treatedAsLegendary (g : Game) (o : GameObject) : Bool :=
  o.isLegendary ||
    g.battlefield.any (fun a => a.attachedTo == some o.id && a.staticAbilities.any fun | .enchantedCreatureGetsHasAndTypes _ _ _ _ => true | _ => false)

/-- Continuous +P/+T `src` currently grants `target` as a lord (CR 604.2 / 613.3c). -/
def grantsStatBonusTo (g : Game) (src target : GameObject) : Int × Int :=
  src.staticAbilities.foldl
    (fun acc ab =>
      let sameController :=
        src.isOnBattlefield && target.isOnBattlefield &&
          src.controller == target.controller && src.controller.isSome &&
          target.isCreature
      match ab with
      | .otherSubtypeGetPowerPerArtifactToken subtype =>
        if sameController && src.id != target.id && g.hasSubtype target subtype then
          let n : Int :=
            match src.controller with
            | none => 0
            | some p =>
              Int.ofNat ((g.permanentsOf p).filter (fun o =>
                o.printed.isToken && o.printed.isArtifact) |>.size)
          addStats acc (n, 0)
        else acc
      | .opponentsCreaturesGet p t =>
        if src.isOnBattlefield && target.isOnBattlefield && target.isCreature &&
            src.controller.isSome && target.controller.isSome &&
            src.controller != target.controller then
          addStats acc (p, t)
        else acc
      | .chosenTypeCreaturesGet p t =>
        match src.status.chosenCreatureType with
        | some ty =>
          if sameController && g.hasSubtype target ty then addStats acc (p, t) else acc
        | none => acc
      | _ =>
        match ab.lordPump? with
        | none => acc
        | some (subtypes, p, t) =>
          let otherOk := src.id != target.id || ab.lordIncludesSelf
          let supertypeOk :=
            ab.lordSupertype?.all target.hasSupertype &&
            ab.lordNonSupertype?.all (fun s => !target.hasSupertype s)
          let subtypeOk :=
            match src.status.chosenCreatureType with
            | some t => g.hasSubtype target t
            | none => subtypes.isEmpty || subtypes.any (fun s => g.hasSubtype target s)
          if sameController && otherOk && supertypeOk && subtypeOk then
            addStats acc (p, t)
          else acc)
    (0, 0)

/-- Continuous +P/+T granted to `o` by other permanents you control (CR 613.3c). -/
def lordStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    g.battlefield.foldl
      (fun acc src => addStats acc (g.grantsStatBonusTo src o))
      (0, 0)

/-- Continuous +P/+T this Aura or Equipment currently grants its host (CR 613.3c). -/
def auraStatBonus (aura : GameObject) : Int × Int :=
  aura.staticAbilities.foldl
    (fun acc ab => addStats acc ab.hostStatBonus)
    (0, 0)

/-- Instant and sorcery cards in `p`'s graveyard (Glamdring). -/
def instantSorceryInGraveyard (g : Game) (p : PlayerId) : Nat :=
  (g.player p).graveyard.filter (fun id =>
    match g.findObject? id with
    | some c => c.printed.isInstant || c.printed.isSorcery
    | none => false) |>.size

/-- Static power/toughness from Auras and Equipment attached to `o`. -/
def attachedStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    g.battlefield.foldl
      (fun acc aura =>
        if aura.attachedTo == some o.id then
          let glam : Int × Int :=
            if aura.staticAbilities.any (fun
              | .equippedFirstStrikePlusPerInstantSorcery => true
              | _ => false) then
              match aura.controller with
              | some p => (Int.ofNat (g.instantSorceryInGraveyard p), 0)
              | none => (0, 0)
            else (0, 0)
          addStats acc
            (addStats (addStats (auraStatBonus aura) glam) ((aura.status.hone : Int), 0))
        else acc)
      (0, 0)

/-- Self +P/+T from “as long as you have an enduring story”. -/
def enduringStorySelfBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if !g.hasEnduringStory p then (0, 0)
      else
        o.staticAbilities.foldl
          (fun acc ab =>
            match ab.selfIfEnduringStory? with
            | some (pw, tw, _) => addStats acc (pw, tw)
            | none => acc)
          (0, 0)

/-- Team +P/+T from “as long as you have an enduring story, creatures you
control get …”. -/
def enduringStoryTeamBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield || !o.isCreature then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if !g.hasEnduringStory p then (0, 0)
      else
        (g.permanentsOf p).foldl
          (fun acc src =>
            src.staticAbilities.foldl
              (fun acc ab =>
                match ab.teamIfEnduringStory? with
                | some (pw, tw) => addStats acc (pw, tw)
                | none => acc)
              acc)
          (0, 0)

/-- Keywords granted while the controller has an enduring story. -/
def enduringStoryKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      if !g.hasEnduringStory p then Keywords.none
      else
        o.staticAbilities.foldl
          (fun acc ab =>
            match ab.selfIfEnduringStory? with
            | some (_, _, k) => Keywords.merge acc k
            | none => acc)
          Keywords.none

/-- +P/+0 from `powerPerMountain` (e.g. Desert Were-Worm). -/
def mountainPowerBonus (g : Game) (o : GameObject) : Int :=
  if o.printed.powerPerMountain == 0 then 0
  else
    let n :=
      (g.permanentsOf o.you).filter (fun p => g.hasSubtype p .mountain) |>.size
    Int.ofNat (o.printed.powerPerMountain * n)

/-- Threshold: +P/+T while seven or more cards are in your graveyard. -/
def thresholdBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if (g.player p).graveyard.size < 7 then (0, 0)
      else
        o.staticAbilities.foldl (fun acc ab =>
          match ab.thresholdGets? with
          | some (pw, tw) => addStats acc (pw, tw)
          | none => acc) (0, 0)

/-- +P/+0 from graveyards with seven or more cards (Master's Councillors). -/
def fatGraveyardPowerBonus (g : Game) (o : GameObject) : Int :=
  o.staticAbilities.foldl (fun acc ab =>
    match ab with
    | .powerPerFatGraveyard p =>
      let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
      acc + p * (n : Int)
    | _ => acc) 0

/-- Self +P/+T from leftover-lifted statics (other artifacts, attached
Equipment, creature cards in graveyard). -/
def leftoverSelfBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    o.staticAbilities.foldl (fun acc ab =>
      match ab with
      | .getsPowerPerOtherArtifact p =>
        let n : Int :=
          Int.ofNat ((g.permanentsOf o.you).filter (fun x =>
            x.id != o.id && x.printed.isArtifact) |>.size)
        addStats acc (p * n, 0)
      | .getsPowerPerAttachedEquipment p =>
        let n : Int := Int.ofNat (g.attachedEquipmentCount o)
        addStats acc (p * n, 0)
      | .getsIfGyCreatureCards min pw tw
      | .getsAndAllTypesIfGyCreatureCards min pw tw =>
        let gy :=
          (g.player o.you).graveyard.filter (fun id =>
            (g.object! id).printed.isCreature) |>.size
        if gy >= min then addStats acc (pw, tw) else acc
      | _ => acc) (0, 0)

/-- +1/+1 for each artifact you control (Iron Man Armor until EOT). -/
def artifactCountPump (g : Game) (o : GameObject) : Int × Int :=
  if !o.status.pumpPerArtifactUntilEot || !o.isOnBattlefield then (0, 0)
  else
    let n : Int :=
      Int.ofNat ((g.permanentsOf o.you).filter (fun p => p.printed.isArtifact ||
        p.status.additionalArtifactUntilEot) |>.size)
    (n, n)

/-- +P/+T from Reality Fracture static abilities: the creature's own
graveyard-count bonuses, grants from its controller's permanents and
emblems, attached Auras and Equipment, and effects lasting until a player's
next turn. -/
def fraStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    let untilTurn := o.status.untilTurnOfPump.foldl (fun acc (_, p, t) => addStats acc (p, t)) (0, 0)
    match o.controller with
    | none => untilTurn
    | some p =>
      let gyIds := (g.player p).graveyard
      let gy := gyIds.size
      let self := o.staticAbilities.foldl (fun acc ab =>
        match ab with
        | .fra .powerPerSevenInGraveyard => addStats acc (2 * Int.ofNat (gy / 7), 0)
        | .fra .powerAndFlyingIfSevenInGraveyard => if gy ≥ 7 then addStats acc (1, 0) else acc
        | .fra .powerPerCreatureAndPlaneswalkerCard =>
          let n := (gyIds.filter (fun id =>
            (g.findObject? id).any (fun c => c.printed.isCreature || c.printed.isPlaneswalker))).size
          addStats acc (Int.ofNat n, 0)
        | _ => acc) (0, 0)
      let fromSources (srcs : Array GameObject) : Int × Int :=
        srcs.foldl (fun acc src =>
          src.staticAbilities.foldl (fun acc ab =>
            match ab with
            | .fra .creatureTokensGetOneAndVigilance =>
              if o.isCreature && o.printed.isToken then addStats acc (1, 0) else acc
            | .fra .emblemCreaturesGetTwoTwo => if o.isCreature then addStats acc (2, 2) else acc
            | _ => acc) acc) (0, 0)
      let team := fromSources (g.permanentsOf p)
      let emblems := fromSources (g.objects.filter (fun e => e.zone == .command && e.controlledBy p))
      let attached := g.battlefield.foldl (fun acc a =>
        if a.attachedTo != some o.id then acc
        else
          a.staticAbilities.foldl (fun acc ab =>
            match ab with
            | .fra .equippedHuntersAxe => addStats acc (2, 0)
            | .fra .equippedMedicsKitesail => addStats acc (1, 0)
            | .fra .enchantedGetsOneAndDeathtouch => addStats acc (1, 0)
            | _ => acc) acc) (0, 0)
      let flyingEmblem :=
        if o.isCreature &&
            (g.objects.filter (fun e => e.zone == .command && e.controlledBy p)).any
              (·.printed.grantTeamPlusTwoFlying) then
          (2, 2)
        else (0, 0)
      let unspent :=
        if o.printed.powerPerUnspentMana then
          let n : Int := Int.ofNat (g.player p).manaPool.total
          (n, n)
        else (0, 0)
      #[untilTurn, self, team, emblems, attached, flyingEmblem, unspent].foldl addStats (0, 0)

def snapshotPT (g : Game) (o : GameObject) : Int × Int :=
  let n : Int := (o.status.plusOnePlusOne : Int) - (o.status.minusOneMinusOne : Int)
  #[g.characteristicBasePT o, o.status.pump, (n, n), g.attachedStatBonus o,
      g.lordStatBonus o, g.enduringStorySelfBonus o, g.enduringStoryTeamBonus o,
      (g.mountainPowerBonus o, (0 : Int)),
      (g.fatGraveyardPowerBonus o, (0 : Int)),
      g.artifactCountPump o, g.leftoverSelfBonus o, g.fraStatBonus o,
      g.thresholdBonus o].foldl
    addStats (0, 0)

/-- Power of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotPower (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).1

/-- Toughness of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotToughness (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).2

/-- True when an Aura attached to `o` makes it only a listed subtype and
unable to attack or block (e.g. Fog on the Barrow-Downs). -/
def enchantedCantAttackOrBlock (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any (fun a =>
    a.attachedTo == some o.id &&
      a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome))

/-- Whether `p` controls a Jace planeswalker. -/
def controlsJacePlaneswalker (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun x => x.printed.isPlaneswalker && g.hasSubtype x .jace)

/-- Keywords Reality Fracture static abilities grant `o`: its own conditional
keywords, grants from permanents its controller controls, and grants from
attached Auras and Equipment. -/
def fraGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      let gy := (g.player p).graveyard.size
      let self := o.staticAbilities.foldl (fun acc ab =>
        match ab with
        | .fra .firstStrikeDuringYourTurn =>
          if g.activePlayer == p then Keywords.merge acc Keyword.firstStrike else acc
        | .fra .vigilanceIfJace =>
          if g.controlsJacePlaneswalker p then Keywords.merge acc Keyword.vigilance else acc
        | .fra .powerAndFlyingIfSevenInGraveyard =>
          if gy ≥ 7 then Keywords.merge acc Keyword.flying else acc
        | .fra .flyingHasteIfOpponentDealtNoncombat =>
          if (g.livingOpponents p).any (fun opp => g.loggedNoncombatDamage opp.id) then
            Keywords.merge acc (Keyword.flying.merge Keyword.haste)
          else acc
        | .fra .hexproofUntilCombatDamage =>
          if o.status.dealtCombatDamage then acc else Keywords.merge acc Keyword.hexproof
        | _ => acc) Keywords.none
      let team := (g.permanentsOf p).foldl (fun acc src =>
        let other := src.id != o.id
        src.staticAbilities.foldl (fun acc ab =>
          let grant (cond : Bool) (k : Keywords) := if cond then Keywords.merge acc k else acc
          match ab with
          | .fra .creaturesYouControlHaveTrample => grant o.isCreature Keyword.trample
          | .fra .plusOneCreaturesHaveVigilance =>
            grant (o.isCreature && o.status.plusOnePlusOne > 0) Keyword.vigilance
          | .fra .creatureTokensGetOneAndVigilance =>
            grant (o.isCreature && o.printed.isToken) Keyword.vigilance
          | .fra .otherPlusOneCreaturesHaveHaste =>
            grant (other && o.isCreature && o.status.plusOnePlusOne > 0) Keyword.haste
          | .fra .creaturesYouControlHaveHaste => grant o.isCreature Keyword.haste
          | .fra .otherCreaturesHaveTrample => grant (other && o.isCreature) Keyword.trample
          | .fra .landsHaveHexproof => grant o.printed.isLand Keyword.hexproof
          | .fra .thoptersHaveHaste => grant (g.hasSubtype o .thopter) Keyword.haste
          | .fra .artifactCreaturesHaveVigilance =>
            grant (o.isCreature && o.printed.isArtifact) Keyword.vigilance
          | _ => acc) acc) Keywords.none
      let attached := g.battlefield.foldl (fun acc a =>
        if a.attachedTo != some o.id then acc
        else
          a.staticAbilities.foldl (fun acc ab =>
            match ab with
            | .fra .equippedMedicsKitesail => Keywords.merge acc Keyword.flying
            | .fra .enchantedGetsOneAndDeathtouch => Keywords.merge acc Keyword.deathtouch
            | _ => acc) acc) Keywords.none
      Keywords.mergeAll #[self, team, attached]

/-- Whether `o` may attack as though it didn't have defender (Surveillance
Phantasm; Ghalta the Immovable). -/
def mayAttackDespiteDefender (g : Game) (o : GameObject) : Bool :=
  match o.controller with
  | none => false
  | some p =>
    (o.staticAbilities.any (· == StaticAbility.fra .attackDespiteDefenderIfScried) &&
      (g.loggedScried p || g.loggedSurveilled p)) ||
    (g.permanentsOf p).any (·.staticAbilities.any (· == StaticAbility.fra .creaturesAttackDespiteDefender))

/-- Whether `p` currently controls a permanent with any of these subtypes. -/
def controlsAnySubtype (g : Game) (p : PlayerId) (subtypes : Array CardSubtype) : Bool :=
  (g.permanentsOf p).any (fun o => subtypes.any (g.hasSubtype o))

/-- Whether `p` currently controls a legendary creature. -/
def controlsLegendaryCreature (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.isCreature && o.printed.hasSupertype .legendary)

/-- Whether `p` currently controls an Equipment. -/
def controlsEquipment (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.isEquipment)

/-- Intrinsic self-replacement check for whether `card` enters the battlefield
tapped under `p`'s control (CR 614.1c / 616.1a; rulings 808 / 809). -/
private def selfEntersTapped (g : Game) (p : PlayerId) (card : CardDef) : Bool :=
  let proposed := GameEvent.moved g.turnNumber
    { controller := some p, owner := p, types := card.types
      subtypes := CardSubtype.ofSubtypes card.subtypes } .stack .battlefield
  if !proposed.watches .wouldEnterBattlefield then false
  else
  card.entersTapped || card.staticAbilities.any (· == StaticAbility.fra .entersTappedChooseColor) ||
    (card.entersTappedUnlessLegendary && !g.controlsLegendaryCreature p) ||
    (card.entersTappedUnlessEquipment && !g.controlsEquipment p) ||
    (card.entersTappedUnlessPlaneswalker &&
      !(g.permanentsOf p).any (·.printed.isPlaneswalker)) ||
    (card.entersTappedUnlessTwoOtherLands &&
      ((g.permanentsOf p).filter (·.printed.isLand)).size < 2) ||
    (!card.entersTappedUnlessAnySubtype.isEmpty &&
      !g.controlsAnySubtype p card.entersTappedUnlessAnySubtype) ||
    (match card.entersTappedUnlessNBasics with
     | some n =>
       ((g.permanentsOf p).filter (fun o => isBasicLandCard o.printed)).size < n
     | none => false) ||
    (match card.entersTappedUnlessOppLands with
     | some n =>
       let nOpp := (g.livingOpponents p).foldl (fun acc pl =>
         acc + ((g.permanentsOf pl.id).filter (·.printed.isLand)).size) 0
       nOpp < n
     | none => false)

/-- Result of applying CR 616.1a–g enters-the-battlefield replacement effects
to a permanent or token about to enter the battlefield. -/
structure EtbReplacementResult where
  candidate : GameObject
  entersWith : CounterBag := #[]
  weaverBonus : Nat := 0
  applied : Array ReplacementId := #[]
  cause : Option EventCause := none
  choice? : Option (PlayerId × Array ReplacementId) := none

/-- Run the CR 616.1a–g replacement loop for `candidate` about to enter the
battlefield (CR 614.1c / 614.12 / 616.1):
- `616.1a` (`self`): `entersTappedSelf`, `entersWithCountersSelf` (loyalty,
  printed +1/+1, X +1/+1, indestructible, shield, hope-per-creature, Saga lore).
- `616.1b` (`control`): `entersUnderControl`.
- `616.1c` (`copy`): `entersAsCopy`.
- `616.1d` (`backFaceUp`): `entersBackFaceUp` (including daybound entering
  transformed when `g.isNight`, CR 702.145b).
- `616.1e` (`other`): `entersTappedExternal`, `entersWithExtraCounters`
  (including Arwen, Weaver of Hope, `othersEnterWithPlusOneEqualToughness`).
- `616.1g`: contained counter-putting replacements via `replaceCountersPut`. -/
def applyEtbReplacements (g : Game) (candidate : GameObject)
    (fromStackTime : Nat := 0) (applyHope : Bool := true)
    (asOf : Nat := g.timestamp) (extraCounters : CounterBag := #[])
    (leavingPlay : Bool := false) (forceBackFace : Bool := false)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none)
    (order : Array ReplacementId := g.replacementOrder) : EtbReplacementResult := Id.run do
  let mut cur := candidate
  let mut bag : CounterBag :=
    if fromStackTime > 0 then #[(.time, fromStackTime)] else #[]
  let mut curApplied := applied
  let mut curCause := cause
  let mut curOrder := order
  let mut choice? : Option (PlayerId × Array ReplacementId) := none
  let mut weaverBonus : Nat := 0
  -- Any caller-supplied `extraCounters` (e.g., incubate, return with finality)
  -- have contained counter-putting replacements applied (CR 616.1g).
  for (k, n) in extraCounters do
    if n > 0 && choice?.isNone then
      let (n', app', c', subChoice?, ord') :=
        g.replaceCountersPutChoice cur k n (putter := cur.controller) (entersWith := true)
          (entering := some cur) (applied := curApplied) (cause := curCause) (order := curOrder)
      curOrder := ord'
      match subChoice? with
      | some ch => choice? := some ch
      | none =>
        bag := bag.add k n'
        curApplied := app'
        curCause := c'
  let mut fuel := if choice?.isSome then 0 else 32
  while fuel > 0 do
    fuel := fuel - 1
    let ctrl := cur.controller.getD cur.owner
    let mut specs : Array ReplacementSpec := #[]
    -- 616.1a: self enters-tapped replacement
    if !cur.status.faceDown && !cur.status.tapped && g.selfEntersTapped ctrl cur.printed then
      specs := specs.push {
        id := ⟨cur.id.raw * 1000 + 1⟩
        source := some cur.id
        controller := some ctrl
        affectedPlayer := ctrl
        kind := .entersTappedSelf cur.id
      }
    -- 616.1a: self enters-with-counters replacements
    if !cur.status.faceDown then
      if cur.printed.isPlaneswalker then
        if let some loy := cur.printed.loyalty then
          if loy > 0 then
            specs := specs.push {
              id := ⟨cur.id.raw * 1000 + 2⟩
              source := some cur.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .entersWithCountersSelf cur.id .loyalty loy.toNat
            }
      if cur.printed.entersWithPlusOneCounters > 0 then
        specs := specs.push {
          id := ⟨cur.id.raw * 1000 + 3⟩
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .plusOnePlusOne cur.printed.entersWithPlusOneCounters
        }
      if cur.staticAbilities.any (· == .entersWithXPlusOne) then
        let xVal := cur.chosenX.getD 0
        if xVal > 0 then
          specs := specs.push {
            id := ⟨cur.id.raw * 1000 + 4⟩
            source := some cur.id
            controller := some ctrl
            affectedPlayer := ctrl
            kind := .entersWithCountersSelf cur.id .plusOnePlusOne xVal
          }
      if cur.printed.entersWithIndestructibleCounter then
        specs := specs.push {
          id := ⟨cur.id.raw * 1000 + 5⟩
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .indestructible 1
        }
      if cur.printed.entersWithShield > 0 then
        specs := specs.push {
          id := ⟨cur.id.raw * 1000 + 6⟩
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .shield cur.printed.entersWithShield
        }
      if cur.printed.entersWithHopePerCreature then
        let others := ((g.creaturesControlledBy ctrl).filter (·.id != cur.id)).size
        let selfCount := if cur.isCreature then 1 else 0
        let totalHope := others + selfCount
        if totalHope > 0 then
          specs := specs.push {
            id := ⟨cur.id.raw * 1000 + 7⟩
            source := some cur.id
            controller := some ctrl
            affectedPlayer := ctrl
            kind := .entersWithCountersSelf cur.id .hope totalHope
          }
      if cur.printed.saga.isSome then
        specs := specs.push {
          id := ⟨cur.id.raw * 1000 + 8⟩
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .lore 1
        }
    -- 616.1d: intrinsic daybound / back-face-up replacement (CR 702.145b / 712.14)
    if !cur.status.transformed && cur.printed.otherFace.isSome &&
        (forceBackFace || (!leavingPlay && cur.printed.daybound && g.isNight)) then
      specs := specs.push {
        id := ⟨cur.id.raw * 1000 + 9⟩
        source := some cur.id
        controller := some ctrl
        affectedPlayer := ctrl
        kind := .entersBackFaceUp cur.id
      }
    -- 616.1e: Arwen, Weaver of Hope (`othersEnterWithPlusOneEqualToughness`)
    if applyHope && !cur.status.faceDown && cur.isCreature then
      for weaver in g.permanentsOf ctrl do
        if weaver.id != cur.id && weaver.printed.othersEnterWithPlusOneEqualToughness &&
            weaver.timestamp < asOf then
          let bonus := weaver.toughness.toNat
          if bonus > 0 then
            specs := specs.push {
              id := ⟨weaver.id.raw * 1000 + 10⟩
              source := some weaver.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .entersWithExtraCounters cur.id .plusOnePlusOne bonus
            }
    -- Active `ContinuousEffect.replacement` specs targeting `cur.id` (or `⟨0⟩` wildcard)
    for (_, eff) in g.activeEffects do
      match eff with
      | .replacement spec _ =>
        match spec.kind with
        | .entersTappedSelf tid | .entersWithCountersSelf tid ..
        | .entersUnderControl tid _ | .entersAsCopy tid _
        | .entersBackFaceUp tid | .entersTappedExternal tid
        | .entersWithExtraCounters tid .. =>
          if tid == cur.id || tid == ⟨0⟩ then
            specs := specs.push { spec with affectedPlayer := ctrl }
        | _ => pure ()
      | _ => pure ()
    let candidates := specs.map (fun s => (ReplacementOrPrevention.replacement s).toCandidate)
    match g.selectNextReplacementStep candidates curApplied curOrder with
    | .none => fuel := 0
    | .needChoice chooser choices ord' =>
      curOrder := ord'
      choice? := some (chooser, choices)
      fuel := 0
    | .chosen chosen ord' =>
      curOrder := ord'
      match specs.find? (fun s => s.id == chosen.id) with
      | none => fuel := 0
      | some spec =>
        curApplied := curApplied.push chosen.id
        curCause := g.wrapReplacedCause chosen.id curCause (some ctrl)
        match spec.kind with
        | .entersTappedSelf _ | .entersTappedExternal _ =>
          cur := { cur with status := { cur.status with tapped := true } }
        | .entersWithCountersSelf _ k n =>
          let (n', app', c', subChoice?, ord2) :=
            g.replaceCountersPutChoice cur k n (putter := cur.controller) (entersWith := true)
              (entering := some cur) (applied := curApplied) (cause := curCause) (order := curOrder)
          curOrder := ord2
          match subChoice? with
          | some ch =>
            choice? := some ch
            fuel := 0
          | none =>
            bag := bag.add k n'
            curApplied := app'
            curCause := c'
        | .entersUnderControl _ newCtrl =>
          cur := { cur with controller := some newCtrl, defaultController := some newCtrl }
        | .entersAsCopy _ template =>
          let sick := template.isCreature && !template.keywords.haste
          cur := { cur with
            printed := template
            status := { cur.status with summoningSick := sick } }
        | .entersBackFaceUp _ =>
          match cur.printed.otherFace with
          | some back =>
            let newPrinted := { back with otherFace := some { cur.printed with otherFace := none } }
            cur := { cur with
              printed := newPrinted
              status := { cur.status with transformed := true, cantTransform := true } }
          | none => pure ()
        | .entersWithExtraCounters _ k n =>
          let isWeaver :=
            match spec.source.bind g.findObject? with
            | some w => w.printed.othersEnterWithPlusOneEqualToughness
            | none => false
          let (n', app', c', subChoice?, ord2) :=
            g.replaceCountersPutChoice cur k n (putter := cur.controller) (entersWith := true)
              (entering := some cur) (applied := curApplied) (cause := curCause) (order := curOrder)
          curOrder := ord2
          match subChoice? with
          | some ch =>
            choice? := some ch
            fuel := 0
          | none =>
            if isWeaver then
              weaverBonus := weaverBonus + n'
            bag := bag.add k n'
            curApplied := app'
            curCause := c'
        | _ => pure ()
  let finalObj :=
    if bag.isEmpty then cur
    else
      { cur with
        status :=
          { (cur.status.withCounterBag bag) with
            gotPlusOneThisTurn := bag.count .plusOnePlusOne > 0 } }
  return {
    candidate := finalObj
    entersWith := bag
    weaverBonus := weaverBonus
    applied := curApplied
    cause := curCause
    choice? := choice?
  }

/-- Whether `blocker`'s static abilities currently allow it to be declared as
a blocker (CR 509.1b). Checked only when declaring blockers. -/
def mayDeclareAsBlocker (g : Game) (blocker : GameObject) : Bool :=
  blocker.staticAbilities.all (fun ab =>
    match ab.cantBlockUnless? with
    | some subtypes =>
      match blocker.controller with
      | none => false
      | some p => g.controlsAnySubtype p subtypes
    | none => true)

/-- Keywords an attached Aura or Equipment currently grants `o`. -/
def attachedGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    g.battlefield.foldl (fun acc aura =>
      if aura.attachedTo == some o.id then
        Keywords.merge acc
          (aura.staticAbilities.foldl (fun k ab =>
            Keywords.merge k ab.hostKeywords) Keywords.none)
      else acc) Keywords.none

/-- True when an attached Aura makes `o` lose all abilities (Enchanted
River's Grasp; Frozen in Ice). -/
def attachedLosesAbilities (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any (fun aura =>
    aura.attachedTo == some o.id &&
      aura.staticAbilities.any (fun
        | .enchantedLosesAbilitiesDoesntUntap => true
        | .enchantedLosesAbilitiesCantUntap => true
        | _ => false))

/-- Printed abilities still apply unless The Wondrous Wasp (or similar)
is making the permanent lose them (MSH 145 / 190), or an Aura strips them. -/
def retainsPrintedAbilities (g : Game) (o : GameObject) : Bool :=
  !o.status.faceDown &&
  !g.attachedLosesAbilities o && !o.status.losesAbilitiesUntilEot &&
  !o.status.losesAbilitiesGrantedBy.any (fun id =>
    match g.findObject? id with
    | some src => src.isOnBattlefield
    | none => false)

/-- During your turn, creatures you control that are equipped gain these
keywords (Long-Lost Lances). -/
def equippedDuringYourTurnKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield || !o.isCreature || g.attachedEquipmentCount o == 0 then
    Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      if g.activePlayer != p then Keywords.none
      else
        (g.permanentsOf p).foldl (fun acc src =>
          src.staticAbilities.foldl (fun acc ab =>
            Keywords.merge acc (ab.equippedTeamKeywordsDuringYourTurn)) acc)
          Keywords.none

def leftoverGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  let self :=
    o.staticAbilities.foldl (fun acc ab =>
      match ab with
      | .flyingIfPlusOneThisTurn =>
        if o.status.gotPlusOneThisTurn then Keywords.merge acc Keyword.flying else acc
      | _ => acc) Keywords.none
  let fromTeam :=
    match o.controller with
    | none => Keywords.none
    | some p =>
      (g.permanentsOf p).foldl (fun acc src =>
        src.staticAbilities.foldl (fun acc ab =>
          match ab with
          | .creaturesWithPlusOneHave k =>
            if o.isCreature && o.status.plusOnePlusOne > 0 then
              Keywords.merge acc k
            else acc
          | .attackingTokensHave k =>
            if o.isOnBattlefield && o.status.attacking && o.printed.isToken then
              Keywords.merge acc k
            else acc
          | _ => acc) acc) Keywords.none
  Keywords.merge (Keywords.merge self fromTeam) (g.fraGrantedKeywords o)

def currentKeywords (g : Game) (o : GameObject) : Keywords :=
  let printedKw :=
    if g.retainsPrintedAbilities o then o.printed.keywords else Keywords.none
  let base :=
    Keywords.merge
      (Keywords.merge
        (Keywords.merge
          (Keywords.merge
            (Keywords.merge (Keywords.merge printedKw o.grantedUntilEot)
              (g.attachedGrantedKeywords o))
            (g.enduringStoryKeywords o))
          (g.leftoverGrantedKeywords o))
        (g.equippedDuringYourTurnKeywords o))
      o.status.keywordCounters.toKeywords
  let base := if o.status.shadow > 0 then { base with shadow := true } else base
  let base :=
    if o.status.firstStrikeOnYourTurn && o.controller == some g.activePlayer then
      { base with firstStrike := true }
    else base
  let base :=
    match o.controller with
    | some p =>
      let flying :=
        o.isCreature &&
          (g.objects.filter (fun e => e.zone == .command && e.controlledBy p)).any
            (·.printed.grantTeamPlusTwoFlying)
      let toxicLink :=
        o.printed.toxic > 0 &&
          (g.permanentsOf p).any (·.printed.corruptedToxicLifelink) &&
          (g.livingOpponents p).any (fun opp => opp.poison >= 3)
      let base := if flying then { base with flying := true } else base
      if toxicLink then { base with lifelink := true } else base
    | none => base
  base

/-- Haste from printed text, attachments, enduring story, counters, or
“haste as long as you control another …”. Lost abilities are omitted. -/
def hasHaste (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).haste ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
      match ab.hasteIfOtherSubtype? with
      | none => false
      | some t =>
        match o.controller with
        | none => false
        | some p =>
          (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t)))

def canAttack (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.isCreature &&
  o.controlledBy g.activePlayer &&
  !o.status.tapped && (!(g.currentKeywords o).defender || g.mayAttackDespiteDefender o) &&
  !(o.status.summoningSick && !g.hasHaste o) &&
  !g.enchantedCantAttackOrBlock o &&
  o.staticAbilities.all (fun ab =>
    match ab.cantAttackUnlessNOther? with
    | none => true
    | some (n, subtype) =>
      match o.controller with
      | none => false
      | some p =>
        let others :=
          (g.permanentsOf p).filter (fun x =>
            x.id != o.id && g.hasSubtype x subtype) |>.size
        others >= n)

/-- Whether `o` currently has shadow (printed, granted, or from a counter).
Multiple instances are redundant. -/
def hasShadow (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).shadow

/-- Printed or until-end-of-turn keyword selected by `sel`. -/
def hasPrintedOrEot (o : GameObject) (sel : Keywords → Bool) : Bool :=
  sel o.printedOrUntilEot

/-- Current keyword including attached grants. -/
def hasKeyword (g : Game) (o : GameObject) (sel : Keywords → Bool) : Bool :=
  sel (g.currentKeywords o)

/-- Whether `o` has vigilance (CR 702.20). Attacking does not cause it to tap. -/
def hasVigilance (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.vigilance)

/-- Whether `o` has flying, printed or granted (CR 702.9). -/
def hasFlying (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.flying)

/-- Okoye: attacking creature tokens you control have first strike. -/
def okoyeGrantsFirstStrike (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.status.attacking && o.printed.isToken &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any (fun
          | .attackingTokensHave k => k.firstStrike
          | _ => false))

/-- Whether `o` has first strike, printed or granted (CR 702.7). -/
def hasFirstStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.firstStrike) || g.hasKeyword o (·.doubleStrike) ||
    g.okoyeGrantsFirstStrike o

/-- Whether `o` has double strike (CR 702.4). -/
def hasDoubleStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.doubleStrike)

/-- Whether `o` has islandwalk, printed or granted (CR 702.14). -/
def hasIslandwalk (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.islandwalk)

/-- During the Equipment's controller's turn, the equipped creature has
hexproof and can't be blocked (Bilbo's Ring). -/
def equippedHexproofUnblockableThisTurn (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        eq.staticAbilities.any (fun
          | .equippedHexproofUnblockableDuringYourTurn => true
          | _ => false) &&
        match eq.controller with
        | some p => g.activePlayer == p
        | none => false)

/-- Equipment that grants "can't be blocked" to its host (My Precious). -/
def equippedCantBeBlockedNow (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        eq.staticAbilities.any StaticAbility.equippedCantBeBlocked)

/-- Whether `o` can't be blocked, printed or granted until end of turn
(CR 509.1b / 611.2a), or while its power is at most a listed value. -/
def hasCantBeBlocked (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.cantBeBlocked) ||
  g.equippedHexproofUnblockableThisTurn o ||
  g.equippedCantBeBlockedNow o ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
      match ab.cantBeBlockedIfPowerAtMost? with
      | some n => g.snapshotPower o <= n
      | none => false)) ||
  (o.isOnBattlefield && o.isCreature &&
    (g.snapshotPower o <= 1 || g.snapshotToughness o <= 1) &&
    match o.controller with
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any (fun
          | .smallCreaturesYouControlUnblockable => true
          | _ => false))
    | none => false)

/-- Whether `o` has lifelink, printed, granted until end of turn, or from a
lifelink counter (CR 702.15). -/
def hasLifelink (g : Game) (o : GameObject) : Bool :=
  o.status.lifelinkCounters > 0 ||
  g.hasKeyword o (·.lifelink) ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
      match ab.lifelinkIfOtherSubtype? with
      | none => false
      | some t =>
        match o.controller with
        | none => false
        | some p =>
          (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t)))

/-- Whether `o` has menace, printed or granted until end of turn (CR 702.111).
Pairwise `canBlock` stays true; the two-or-more restriction is checked on the
declaration as a whole (CR 509.1c). -/
def hasMenace (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).menace ||
  (o.isOnBattlefield && o.status.plusOnePlusOne > 0 &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any StaticAbility.creaturesWithPlusOneHaveMenace))

/-- Minimum number of creatures required to block `o`, or `0` if unrestricted.
Menace is 2; Troll of Khazad-dûm is 3. -/
def minBlockersRequired (g : Game) (o : GameObject) : Nat :=
  let fromStatic :=
    o.staticAbilities.foldl (fun acc ab =>
      match ab.cantBeBlockedExcept? with
      | some n => max acc n
      | none => acc) 0
  max fromStatic (if g.hasMenace o then 2 else 0)

/-- Maximum number of creatures that may block `o`, if a static caps it. -/
def maxBlockersAllowed (_g : Game) (o : GameObject) : Option Nat :=
  o.staticAbilities.foldl (fun acc ab =>
    match ab.cantBeBlockedByMoreThan? with
    | some n =>
      some (match acc with
        | some m => min m n
        | none => n)
    | none => acc) none

/-- True when `n` blockers is a legal number for `attacker` (CR 702.111b).
Zero is always legal (the attacker is unblocked). -/
def legalBlockerCount (g : Game) (attacker : GameObject) (n : Nat) : Bool :=
  let need := g.minBlockersRequired attacker
  let underMax :=
    match g.maxBlockersAllowed attacker with
    | none => true
    | some m => n ≤ m
  (n == 0 || need <= 1 || n >= need) && underMax

/-- Creatures with flying can't attack this player or block their creatures. -/
def leftoverFlyingRestriction (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.staticAbilities.any (fun
      | .flyingCantAttackYouOrBlockYours => true
      | _ => false))

/-- Whether `blocker` may be assigned to `attacker` as one creature in a
declaration (CR 509.1b). Menace is not a pairwise restriction. -/
def canBlock (g : Game) (blocker attacker : GameObject) : Bool :=
  let defender := g.defendingPlayerOf attacker
  let islandwalkUnblockable :=
    g.hasIslandwalk attacker &&
      (g.permanentsOf defender).any (fun o => g.hasSubtype o .island)
  blocker.isOnBattlefield && blocker.isCreature &&
  blocker.controlledBy defender && !blocker.status.tapped &&
  blocker.status.blocking.isEmpty && !blocker.status.cantBlockUntilEot &&
  !blocker.printed.cantBlock &&
  g.mayDeclareAsBlocker blocker &&
  !g.enchantedCantAttackOrBlock blocker &&
  (!g.creaturesWithoutFlyingCantBlock || g.hasFlying blocker) &&
  attacker.status.attacking &&
  !g.hasCantBeBlocked attacker &&
  !islandwalkUnblockable &&
  !(attacker.staticAbilities.any StaticAbility.blocksTokens &&
    blocker.printed.isToken) &&
  !(attacker.staticAbilities.any (fun ab =>
      match ab.cantBeBlockedByPowerAtMost? with
      | some n => g.snapshotPower blocker <= n
      | none => false)) &&
  !(attacker.staticAbilities.any (fun ab =>
      match ab.cantBeBlockedByPowerAtLeast? with
      | some n => g.snapshotPower blocker >= n
      | none => false)) &&
  (!g.hasFlying attacker ||
    g.hasFlying blocker || (g.currentKeywords blocker).reach) &&
  !(g.hasFlying blocker &&
    match attacker.controller with
    | some p => g.leftoverFlyingRestriction p
    | none => false) &&
  (!(g.hasShadow attacker) || g.hasShadow blocker) &&
  (!(g.hasShadow blocker) || g.hasShadow attacker) &&
  !(match attacker.status.cantBeBlockedByPlayer with
    | some pid => blocker.controlledBy pid
    | none => false) &&
  !(attacker.status.cantBeBlockedExceptByHasteUntilEot && !g.hasHaste blocker)

/-- Whether `src` currently grants trample to `target` (CR 604.2). -/
def grantsTrampleTo (g : Game) (src target : GameObject) : Bool :=
  isLordOf src target &&
  src.staticAbilities.any (fun ab =>
    match ab.trampleSubtypes? with
    | some subtypes => subtypes.any (fun s => g.hasSubtype target s)
    | none => false)

/-- Lore counters among Sagas `p` controls. -/
def loreAmongSagas (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.printed.saga.isSome then acc + o.status.lore else acc) 0

/-- True when `id` is the source of a chapter ability waiting or on the stack
(CR 714.4). -/
def sagaChapterPending (g : Game) (id : ObjectId) : Bool :=
  let waiting :=
    g.waitingTriggers.any (fun wt =>
      wt.source.id == id &&
        match wt.ability.shared with
        | .chapter .. => true
        | _ => false)
  let stacked :=
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.sourceId == some id &&
          match o.triggeredAbility with
          | some t =>
            match t.shared with
            | .chapter .. => true
            | _ => false
          | none => false
      | none => false)
  waiting || stacked

/-- Whether `o` currently has hexproof and indestructible from Tom Bombadil's
lore-threshold static. -/
def loreThresholdProtection (g : Game) (o : GameObject) : Bool :=
  match o.printed.hexproofIndestructibleIfLore, o.controller with
  | some n, some p => g.loreAmongSagas p ≥ n
  | _, _ => false

/-- True when a grantor of hexproof or damage prevention is still on the
battlefield. -/
def grantorStillInPlay (g : Game) (id : ObjectId) : Bool :=
  match g.findObject? id with
  | some o => o.isOnBattlefield
  | none => false

def hasHexproof (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.hexproof) || g.loreThresholdProtection o ||
    o.status.hexproofGrantedBy.any g.grantorStillInPlay ||
    g.equippedHexproofUnblockableThisTurn o ||
    (match o.controller with
     | none => false
     | some p =>
       (o.isCreature && o.status.gotPlusOneThisTurn &&
         (g.permanentsOf p).any (fun src =>
           src.printed.staticAbilities.any (fun
             | .hexproofIfPlusOneThisTurn => true
             | _ => false))) ||
       (g.permanentsOf p).any (fun src =>
         src.status.shield > 0 &&
           src.staticAbilities.any (fun
             | .youAndOtherSubtypeHaveHexproofIfShield subtype =>
               src.id != o.id && g.hasSubtype o subtype
             | _ => false)))

/-- The player has hexproof from opponents (Captain America, Super-Soldier). -/
def playerHasHexproof (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun src =>
    src.status.shield > 0 &&
      src.staticAbilities.any (fun
        | .youAndOtherSubtypeHaveHexproofIfShield _ => true
        | _ => false))

/-- Protection from the source's colors or from its card type. -/
def frcProtectedFrom (g : Game) (o src : GameObject) : Bool :=
  let colorBlock := o.printed.protectionFromColors.any (src.printed.colors.contains ·)
  let typeMatch (em : GameObject) :=
    em.printed.protectionFromChosenCardType &&
      match em.status.chosenCardType with
      | some t => src.printed.hasType t
      | none => false
  colorBlock || typeMatch o ||
    match o.controller with
    | some p => (g.permanentsOf p).any typeMatch
    | none => false

/-- Hexproof stops an opponent from targeting that player (CR 702.11c). -/
def playerCanBeTargetedBy (g : Game) (caster target : PlayerId) : Bool :=
  let typeBlock :=
    match (g.resolvingSpell.orElse (fun _ => g.proposedSpell.map (·.spellId))).bind g.findObject? with
    | none => false
    | some src =>
      (g.permanentsOf target).any (fun em =>
        em.printed.protectionFromChosenCardType &&
          match em.status.chosenCardType with
          | some t => src.printed.hasType t
          | none => false)
  (caster == target || !g.playerHasHexproof target) &&
    !(g.player target).protectionFromEverything && !typeBlock

/-- Whether `o` has deathtouch, printed or granted until end of turn (CR 702.2). -/
def hasDeathtouch (g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.deathtouch) || o.status.keywordCounters.deathtouch > 0 ||
    (g.fraGrantedKeywords o).deathtouch

/-- Whether `o` has indestructible (CR 702.12). An until-end-of-turn effect can
make it lose the keyword. -/
def leftoverIndestructible (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    o.staticAbilities.any (fun
      | .indestructibleIfArtifactCreatureOrPlan => true
      | _ => false) &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun x =>
        (x.isCreature && x.printed.isArtifact) || g.hasSubtype x .plan)

def hasIndestructible (g : Game) (o : GameObject) : Bool :=
  ((g.currentKeywords o).indestructible ||
    o.status.indestructibleCounters > 0 ||
    g.loreThresholdProtection o ||
    g.leftoverIndestructible o) &&
  !(o.isOnBattlefield && o.status.untilEotLosesIndestructible)

/-- Mana value of `o` (CR 202.3). `{X}` is the chosen value while the object
is on the stack and 0 otherwise (rulings 178 / 185 / 186). -/
def objectManaValue (_g : Game) (o : GameObject) : Nat :=
  let printed := o.printed.manaValue
  if o.zone != .stack then printed
  else printed + o.chosenX.getD 0

/-- The Reaver Cleaver: combat damage to a player or planeswalker makes Treasures. -/
def equippedCreatesCombatTreasures (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        eq.staticAbilities.any (fun
          | .equippedGetsTrampleAndCombatTreasures _ _ => true
          | _ => false))

/-- Whether `o` has trample, printed, granted, or from a lord (CR 702.19). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).trample ||
  o.status.trampleCounters > 0 ||
  (o.isOnBattlefield && g.battlefield.any (fun src => g.grantsTrampleTo src o)) ||
  g.equippedCreatesCombatTreasures o

/-- Keywords including those granted by static abilities and until-EOT effects.
Only trample (lords) and indestructible (until-EOT loss) differ from
`printedOrUntilEot`; overlaying the other keywords would restate identity. -/
def effectiveKeywords (g : Game) (o : GameObject) : Keywords :=
  { Keywords.merge o.printedOrUntilEot (g.fraGrantedKeywords o) with
    indestructible := g.hasIndestructible o
    trample := g.hasTrample o }

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def basePower (g : Game) (o : GameObject) : Int :=
  g.characteristicBasePower o

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def baseToughness (g : Game) (o : GameObject) : Int :=
  g.characteristicBaseToughness o

/-- Current power, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def power (g : Game) (o : GameObject) : Int :=
  g.snapshotPower o

/-- Current toughness, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def toughness (g : Game) (o : GameObject) : Int :=
  g.snapshotToughness o

/-- Greatest power among creatures `p` controls; `0` if they control none. -/
def greatestPowerAmongCreatures (g : Game) (p : PlayerId) : Int :=
  let creatures := g.creaturesControlledBy p
  if creatures.isEmpty then 0
  else creatures.foldl (fun acc o => max acc (g.power o)) (g.power creatures[0]!)

/-- Greatest power among attacking creatures `p` controls; `0` if none. -/
def greatestPowerAmongAttacking (g : Game) (p : PlayerId) : Int :=
  let attackers :=
    (g.permanentsOf p).filter (fun o => o.isCreature && o.status.attacking)
  if attackers.isEmpty then 0
  else attackers.foldl (fun acc o => max acc (g.power o)) (g.power attackers[0]!)

/-- Creatures currently blocking `attackerId`. -/
def blockersOf (g : Game) (attackerId : ObjectId) : Array GameObject :=
  g.battlefield.filter (fun b => b.status.blocking.contains attackerId)

/-- Attacking creatures `blocker` is still blocking (CR 510.1d). -/
def creaturesBlockedBy (g : Game) (blocker : GameObject) : Array GameObject :=
  blocker.status.blocking.filterMap (fun id =>
    match g.findObject? id with
    | some a =>
      if a.isOnBattlefield && a.status.attacking then some a else none
    | none => none)

/-- Snapshot `o` as an `EventObject` (CR 113.7a).
Note: `colors`, `manaValue`, `types`, `subtypes`, `power`, `toughness`,
`keywords`, and `staticAbilities` are provisional until the Layer 1–7 pipeline
in Phase 8 (CR 613.1). -/
def snapshot (g : Game) (o : GameObject) : EventObject :=
  let base := o.asEvent
  let extraSubtypes : Array CardSubtype :=
    #[.hero, .villain, .goblin, .orc, .army, .elf, .merfolk].foldl
      (fun acc s => if g.hasSubtype o s && !acc.contains s then acc.push s else acc)
      base.subtypes
  let pw : Option Int :=
    if o.zone == .battlefield then
      if o.isCreature || o.printed.power.isSome then some (g.snapshotPower o) else none
    else
      o.lastKnownPower.orElse (fun _ =>
        if o.isCreature || o.printed.power.isSome then some (g.snapshotPower o) else none)
  let tg : Option Int :=
    if o.zone == .battlefield then
      if o.isCreature || o.printed.toughness.isSome then some (g.snapshotToughness o) else none
    else
      o.lastKnownToughness.orElse (fun _ =>
        if o.isCreature || o.printed.toughness.isSome then some (g.snapshotToughness o) else none)
  let curKw := g.currentKeywords o
  { base with
    subtypes := extraSubtypes
    power := pw
    toughness := tg
    keywords := { curKw with
      haste := g.hasHaste o
      vigilance := g.hasVigilance o
      flying := g.hasFlying o
      menace := g.hasMenace o
      hexproof := g.hasHexproof o
      indestructible := g.hasIndestructible o
      reach := curKw.reach
      trample := g.hasTrample o
      deathtouch := g.hasDeathtouch o
      defender := curKw.defender
      lifelink := g.hasLifelink o
      firstStrike := g.hasFirstStrike o
      doubleStrike := g.hasDoubleStrike o
      shadow := g.hasShadow o } }

/-- Total power among creatures `p` controls. -/
def totalPowerOfCreatures (g : Game) (p : PlayerId) : Int :=
  (g.creaturesControlledBy p).foldl (fun sum o => sum + max 0 (g.power o)) 0

/-- Number of creatures `p` controls with power ≥ `minPower` (Ferocious). -/
def countCreaturesWithPowerAtLeast (g : Game) (p : PlayerId) (minPower : Int) : Nat :=
  (g.creaturesControlledBy p).filter (fun o => g.power o >= minPower) |>.size

/-- Extra times a trigger of `source` fires from Bifur / Chief / Wizard's Staff
statics. Each such ability adds one additional instance; they stack. -/
def extraTriggerCopies (g : Game) (controller : PlayerId) (source : GameObject) : Nat :=
  let story :=
    (g.player controller).enduringStory ||
      (g.controlsStoried controller && g.storiedPermanentCount controller >= 3)
  (g.permanentsOf controller).foldl (fun acc o =>
    o.staticAbilities.foldl (fun acc ab =>
      match ab with
      | .extraTriggerIfEnduringStorySubtype subtype =>
        if story && g.hasSubtype source subtype then acc + 1 else acc
      | .extraTriggerAnotherYouControl subtypes types =>
        if o.id == source.id then acc
        else
          let matchSubtype := subtypes.any (fun s => g.hasSubtype source s)
          let matchType := types.any source.printed.hasType
          if matchSubtype || matchType then acc + 1 else acc
      | .equippedTriggersAgain =>
        if o.attachedTo == some source.id then acc + 1 else acc
      | _ => acc) acc) 0

/-- Append waiting-trigger snapshots. -/
def enqueueWaitingTriggers (g : Game) (wts : Array WaitingTrigger) : Game :=
  if wts.isEmpty then g
  else
    let e := GameEvent.engine g.turnNumber (.enqueueWaitingTriggers wts)
    ({ g with events := g.events.push e }).applyEngineChange (.enqueueWaitingTriggers wts)

/-- Karn, Argent Defender: an artifact or creature entering doesn't cause
abilities to trigger (rulings 891–893). -/
def eventSuppressedByKarn (g : Game) (e : GameEvent) : Bool :=
  let hasKarn := g.battlefield.any (fun src =>
    src.staticAbilities.any (fun
      | .enteringArtifactsCreaturesDontTrigger => true
      | _ => false))
  if !hasKarn then false
  else
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) =>
      after.creature || after.artifact
    | .rules (.zone (.created obj _)) =>
      obj.zone == .battlefield && (obj.creature || obj.artifact)
    | _ => false

/-- A Reality Fracture intervening “if” clause on the trigger's options. -/
def fraConditionHolds (g : Game) (controller : PlayerId) (cond : FraCondition)
    (source : Option GameObject) (causeStatus : Option Status := none) : Bool :=
  match cond with
  | .none => true
  | .sourceNotToken => !(source.any (·.printed.isToken))
  | .twoCreaturesDiedThisTurn => g.loggedCreatureDeaths ≥ 2
  | .opponentDealtNoncombatDamageLastTurn =>
    (g.livingOpponents controller).any (fun opp => g.loggedNoncombatDamageLastTurn opp.id)
  | .drewThreeThisTurn => g.loggedDraws controller ≥ 3
  | .castNoSpellThisTurn => g.loggedSpellsCast controller == 0
  | .activatedLoyaltyThisTurn => g.loggedActivatedLoyalty controller
  | .sourceWasCast => source.any (·.wasCast)
  | .causeHadCounters => causeStatus.any (·.hasCounters)
  | .sourceHasCounters =>
    source.any (fun o => ((g.findObject? o.id).getD o).status.hasCounters)

/-- Reality Fracture intervening “if” clauses, checked when the ability would
trigger and again as it resolves (rulings 743 / 889). -/
def fraInterveningHolds (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (source : Option GameObject) (cause : Option GameObject := none) : Bool :=
  match ab.shared with
  | .pumpIfFiveOtherForests =>
    ((g.permanentsOf controller).filter (fun o =>
      g.hasSubtype o .forest && some o.id != cause.map (·.id))).size ≥ 5
  | .destroyOppPermanentIfSixLands =>
    ((g.permanentsOf controller).filter (·.printed.isLand)).size ≥ 6
  | .prepareSource .ifNotPrepared =>
    match source.map (fun o => (g.findObject? o.id).getD o) with
    | some o => !o.status.prepared
    | none => true
  | .prepareSource .ifThreeCreaturesDied => g.loggedCreaturesToGraveyard.size ≥ 3
  | .sacrificeSourceIfNoPlaneswalker =>
    !(g.permanentsOf controller).any (·.printed.isPlaneswalker)
  | .surveilReturnIfGainedLife => g.loggedLifeGained controller > 0
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
    | some n => g.loggedLifeGained controller ≥ n
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
        ab.opts.anotherSupertype.all o.hasSupertype
    | none => true
  -- Intervening “if” clauses checked as the ability triggers (CR 603.4);
  -- they are checked again on resolution.
  let interveningOk :=
    match ab.shared with
    | .beginCombatIfDrawnTwoPump => g.loggedDraws controller ≥ 2
    | .thisAttack .equippedDrain =>
      source.any (fun s => g.battlefield.any (fun e => e.attachedTo == some s.id && e.printed.isEquipment))
    | .thisAttack .ifArtifactEnteredDraw =>
      g.loggedArtifactEntered controller
    | .resource .drawIfAnotherHeroDamage =>
      (g.permanentsOf controller).any (fun o => g.hasSubtype o .hero && some o.id != source.map (·.id))
    | .step .drawToTen => (g.player controller).hand.size < 10
    | .step .harnessedFlicker => source.any (·.status.harnessed)
    | .protectionEverything => source.any (·.wasCast)
    | .death .deathtouchOppSac => cause.any (g.hasDeathtouch ·)
    | .resource .plusOneCreateInsectOnce => cause.any (·.isCreature)
    | .resource .plusOneOnThisOnce =>
      cause.any (fun c => c.isCreature && some c.id != source.map (·.id))
    | .resource .plusOneOnHeroesCreateWall =>
      cause.any (fun c => some c.id != source.map (·.id) && c.controlledBy controller &&
        g.hasSubtype c .hero)
    | .watch .sheHulkRedirectOnce => !g.loggedSheHulkDealtDamage
    | _ => true
  powerOk && otherOk && lifeOk && hulklingOk && causeOk && interveningOk &&
    g.fraInterveningHolds controller ab source cause &&
    g.fraConditionHolds controller ab.opts.fraCondition source (cause.map (·.status))

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
              (.chooseKeyword [0, 3]))
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

/-- Match all triggered abilities over a committed batch of simultaneous rules
events (CR 603.2 / 603.2c / 603.10 / 603.10a–f). Look-back events (`e.isLookBack`,
covering CR 603.10a–f) consult `pre`; all other events consult `post` (CR 603.10). -/
def matchTriggers (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) : Array WaitingTrigger :=
  if batch.isEmpty then #[]
  else Id.run do
    let mut waiting : Array WaitingTrigger := #[]
    let mut firedSources : Array (ObjectId × TriggeredAbility) := #[]
    let mut tappedInBatch : Array ObjectId := #[]
    let queueAb (board : Game) (controller : PlayerId) (source : GameObject)
        (ab : TriggeredAbility) (event : TriggerEvent)
        (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
        (cause : Option GameObject := none) (causeController : Option PlayerId := none)
        (eventCause : Option EventCause := none)
        (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
        Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
      if (post.player controller).lost then (w, fs)
      else if !board.triggerConditionHolds controller ab cause (some source) then (w, fs)
      else if ab.onceEachTurn &&
          (post.loggedTriggeredThisTurn source.id ab ||
            fs.any (fun (sid, a) => sid == source.id && a == ab)) then (w, fs)
      else if ab.optionalOnceEachTurn &&
          (((post.findObject? source.id).map (·.status.optionalOnceUsed)).getD
            source.status.optionalOnceUsed) then (w, fs)
      else
        let fs := if ab.onceEachTurn then fs.push (source.id, ab) else fs
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
          if attackEvent && (board.permanentsOf controller).any (fun o =>
              o.printed.asEntersChooseMarduOrJeskai && o.status.windcragMardu) then 1 else 0
        let curSource :=
          if board.findObject? source.id == some source then source
          else (post.findObject? source.id).getD source
        let copies := board.extraTriggerCopies controller source + 1 + mardu
        let wt : WaitingTrigger :=
          { controller, source := curSource, ability := ab, event,
            lastKnownPower, lastKnownToughness,
            causeId := cause.map (·.id), cause, causeController,
            checked := true, eventCause }
        (w ++ Array.replicate copies wt, fs)
    let queueSrc (board : Game) (controller : PlayerId) (source : GameObject)
        (event : TriggerEvent)
        (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
        (cause : Option GameObject := none) (causeController : Option PlayerId := none)
        (eventCause : Option EventCause := none)
        (keep : TriggeredAbility → Bool := fun _ => true)
        (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
        Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
      if (post.player controller).lost then (w, fs)
      else
        let abs :=
          (source.matchingTriggers event ++
            (board.attachedGrantedTriggers source ++ board.prowessTriggers source).filter (·.firesOn event)).filter keep
        abs.foldl (fun (w, fs) ab =>
          queueAb board controller source ab event lastKnownPower lastKnownToughness
            cause causeController eventCause w fs) (w, fs)
    let queueCtrl (board : Game) (p : PlayerId) (event : TriggerEvent)
        (excludeId : Option ObjectId := none)
        (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
        (cause : Option GameObject := none) (causeController : Option PlayerId := none)
        (eventCause : Option EventCause := none)
        (keep : TriggeredAbility → Bool := fun _ => true)
        (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
        Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
      let (w, fs) := (board.permanentsOf p).foldl (fun (w, fs) o =>
        if excludeId == some o.id then (w, fs)
        else
          queueSrc board p o event lastKnownPower lastKnownToughness
            cause causeController eventCause keep w fs) (w, fs)
      (board.objects.filter (fun o => o.zone == .command && o.controlledBy p)).foldl
        (fun (w, fs) o =>
          if excludeId == some o.id then (w, fs)
          else
            queueSrc board p o event lastKnownPower lastKnownToughness
              cause causeController eventCause keep w fs) (w, fs)
    let queueFraWhere (board : Game) (p : PlayerId) (pred : FraEvent → Bool)
        (cause : Option GameObject := none) (excludeId : Option ObjectId := none)
        (lastKnownPower : Option Int := none) (causeController : Option PlayerId := none)
        (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
        Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
      let fireObj (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility))
          (o : GameObject) : Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
        if excludeId == some o.id then (w, fs)
        else
          (o.printed.triggeredAbilities ++ o.status.grantedTriggeredAbilities ++
              o.status.grantedTriggersUntilEot).foldl (fun (w, fs) ab =>
            match ab.timing.events.find? (fun ev =>
                match ev with
                | .fra fe => pred fe
                | _ => false) with
            | some ev =>
              queueAb board p o ab ev lastKnownPower none cause causeController none w fs
            | none => (w, fs)) (w, fs)
      let (w, fs) := (board.permanentsOf p).foldl (fun (w, fs) o => fireObj w fs o) (w, fs)
      (board.objects.filter (fun o => o.zone == .command && o.controlledBy p)).foldl
        (fun (w, fs) o => fireObj w fs o) (w, fs)
    let queueFra (board : Game) (p : PlayerId) (fe : FraEvent)
        (cause : Option GameObject := none) (excludeId : Option ObjectId := none)
        (lastKnownPower : Option Int := none) (causeController : Option PlayerId := none)
        (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
        Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
      queueFraWhere board p (· == fe) cause excludeId lastKnownPower causeController w fs
    let uniquePermTargets (board : Game) (targets : Array Target) : Array GameObject :=
      Id.run do
        let mut seen : Array ObjectId := #[]
        let mut out : Array GameObject := #[]
        for t in targets do
          match t with
          | .permanent id =>
            if !seen.contains id then
              seen := seen.push id
              match board.findObject? id with
              | some o => if o.isOnBattlefield then out := out.push o
              | none => pure ()
          | _ => pure ()
        return out
    -- Batch-level (“one or more”) triggers (1–13)
    -- 1. “Whenever one or more other creatures die” (look-back on pre, CR 603.10a(1)).
    for o in pre.battlefield do
      match o.controller with
      | some p =>
        if !(post.player p).lost && batch.any (·.matchesTrigger p o.id .oneOrMoreOtherCreaturesDie) then
          let (w, fs) := queueSrc pre p o .oneOrMoreOtherCreaturesDie (w := waiting) (fs := firedSources)
          waiting := w; firedSources := fs
      | none => pure ()
    -- 2. “Whenever one or more creature cards are put into your graveyard from anywhere” (post-batch, CR 603.10).
    for o in post.battlefield do
      match o.controller with
      | some p =>
        if !(post.player p).lost && batch.any (·.matchesTrigger p o.id .creatureCardsPutIntoYourGy) then
          let (w, fs) := queueSrc post p o .creatureCardsPutIntoYourGy (w := waiting) (fs := firedSources)
          waiting := w; firedSources := fs
      | none => pure ()
    -- 3. “Whenever a player discards one or more cards” (post-batch, once per discarding player).
    for pl in post.players do
      if batch.any (·.matchesTrigger pl.id ⟨0⟩ .youDiscard) then
        for o in post.battlefield do
          match o.controller with
          | some c =>
            if !(post.player c).lost then
              let (w, fs) := queueSrc post c o (.fra .playerDiscards) (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          | none => pure ()
    -- 4. “Whenever you create one or more creature tokens” (post-batch).
    for pl in post.livingPlayers do
      let p := pl.id
      if batch.any (·.matchesTrigger p ⟨0⟩ (.fra .youCreateCreatureTokens)) then
        let (w, fs) := queueCtrl post p (.fra .youCreateCreatureTokens) (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 5. “Whenever one or more tokens you control enter” (Mister Fantastic, post-batch).
    for pl in post.livingPlayers do
      let p := pl.id
      let tokenEntered := batch.any (fun e =>
        if post.eventSuppressedByKarn e then false
        else
          match e.change with
          | .rules (.zone (.created obj ctrl)) =>
            ctrl == p && obj.zone == .battlefield && obj.token
          | .rules (.zone (.moved _ after _ .battlefield ..)) =>
            after.controller == some p && after.token
          | _ => false)
      if tokenEntered then
        let (w, fs) :=
          queueCtrl post p .tokenYouControlEnters
            (keep := fun ab => ab.shared == .watch .tokensEnterMayDraw)
            (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 6. “Whenever one or more creatures you control become tapped” (post-batch).
    for pl in post.livingPlayers do
      let p := pl.id
      if batch.any (·.matchesTrigger p ⟨0⟩ .creaturesYouControlBecomeTapped) then
        let (w, fs) := queueCtrl post p .creaturesYouControlBecomeTapped (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 7. “Whenever one or more creatures deal combat damage to you” (post-batch).
    for pl in post.livingPlayers do
      let defn := pl.id
      if batch.any (·.matchesTrigger defn ⟨0⟩ .combatDamageToYou) then
        let firstDamager : Option GameObject :=
          batch.findSome? (fun e =>
            match e.change with
            | .rules (.damage (.dealt pkts)) =>
              pkts.findSome? (fun pkt =>
                if pkt.combat && pkt.recipient == .player defn then
                  (pkt.source.id.bind post.findObject?).orElse (fun _ => pkt.source.id.bind pre.findObject?)
                else none)
            | _ => none)
        let (w, fs) := queueCtrl post defn .combatDamageToYou (cause := firstDamager) (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 8. “Whenever one or more opponents are dealt combat damage during your turn” (post-batch).
    let pid := post.activePlayer
    if pid.idx < post.players.size && !(post.player pid).lost &&
        batch.any (·.matchesTrigger pid ⟨0⟩ .opponentsDealtCombatDamageYourTurn) then
      let (w, fs) := queueCtrl post pid .opponentsDealtCombatDamageYourTurn (w := waiting) (fs := firedSources)
      waiting := w; firedSources := fs
    -- 9. “Whenever one or more opponents are dealt noncombat damage” (post-batch).
    for pl in post.livingPlayers do
      let q := pl.id
      if batch.any (·.matchesTrigger q ⟨0⟩ (.fra .opponentsDealtNoncombatDamage)) then
        let (w, fs) := queueCtrl post q (.fra .opponentsDealtNoncombatDamage) (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 10. “Whenever one or more Heroes you control deal damage to a player” (post-batch).
    for pl in post.livingPlayers do
      let q := pl.id
      if batch.any (fun e =>
          match e.change with
          | .rules (.damage (.dealt pkts)) =>
            pkts.any (fun pkt => pkt.amount > 0) && e.matchesTrigger q ⟨0⟩ .heroesDealDamageToPlayer
          | _ => false) then
        let (w, fs) := queueCtrl post q .heroesDealDamageToPlayer (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 11. “Whenever you put one or more counters on a Goblin, Orc, or Army you control” (post-batch).
    for pl in post.livingPlayers do
      let p := pl.id
      let matched := batch.any (fun e =>
        e.matchesTrigger p ⟨0⟩ .youPutCountersOnGoblinOrcArmy ||
          e.countersPutInEvent.any (fun (eo, _, n, actor?) =>
            actor? == some p && n > 0 &&
              (eo.id.bind post.findObject?).any (fun obj =>
                obj.controlledBy p &&
                  (post.hasSubtype obj .goblin || post.hasSubtype obj .orc || post.hasSubtype obj .army))))
      if matched then
        let (w, fs) := queueCtrl post p .youPutCountersOnGoblinOrcArmy (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 12. “Whenever you put one or more loyalty counters on a planeswalker” (post-batch).
    for pl in post.livingPlayers do
      let p := pl.id
      if batch.any (·.matchesTrigger p ⟨0⟩ (.fra .youPutLoyaltyCounters)) then
        let (w, fs) := queueCtrl post p (.fra .youPutLoyaltyCounters) (w := waiting) (fs := firedSources)
        waiting := w; firedSources := fs
    -- 13. “Whenever you put one or more +1/+1 counters on …” (post-batch, including enters-with per CR 122.6).
    for pl in post.livingPlayers do
      let q := pl.id
      let putObjs : Array GameObject :=
        batch.foldl (fun objs e =>
          e.countersPutInEvent.foldl (fun objs (eo, kind, n, actor?) =>
            if kind == .plusOnePlusOne && n > 0 && actor? == some q then
              match eo.id.bind post.findObject? with
              | some obj => objs.push obj
              | none => objs
            else objs) objs) #[]
      if !putObjs.isEmpty then
        for src in post.permanentsOf q do
          for ab in src.matchingTriggers .youPutPlusOne do
            let matchesAb (obj : GameObject) : Bool :=
              match ab.shared with
              | .resource .plusOneOnHeroesCreateWall =>
                obj.id != src.id && obj.controlledBy q && post.hasSubtype obj .hero
              | .resource .plusOneOnThisOnce =>
                obj.isCreature && obj.id != src.id
              | _ => obj.isCreature
            match putObjs.find? matchesAb with
            | some causeObj =>
              let (w, fs) :=
                queueAb post q src ab .youPutPlusOne (cause := some causeObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            | none => pure ()
    -- Per-event triggers across the batch
    let findEventObj (board : Game) (eo : EventObject) : GameObject :=
      match eo.id.bind board.findObject? with
      | some o => o
      | none =>
        let id := eo.id.getD ⟨0⟩
        let printed := eo.toCardDef
        let st := ({} : Status).withCounterBag eo.counters
        { id
          printed
          owner := eo.owner
          controller := eo.controller
          zone := eo.zone
          status :=
            { st with
              tapped := eo.tapped
              summoningSick := eo.summoningSick
              attacking := eo.attacking
              attackingTarget := eo.attackingTarget
              phasedOut := eo.phasedOut
              faceDown := eo.faceDown
              transformed := eo.transformed
              returnedAsArtifact := eo.returnedAsArtifact
              onlyFoodArtifact := eo.onlyFoodArtifact }
          attachedTo := eo.attachedTo
          chosenX := eo.chosenX
          wasCast := eo.wasCast
          isCopy := eo.isCopy
          lastKnownPower := eo.power.orElse (fun _ => eo.lastKnownPower)
          lastKnownToughness := eo.toughness.orElse (fun _ => eo.lastKnownToughness) }
    -- Pre-sum damage dealt to each permanent across the entire batch so
    -- `.sourceDealtDamage` queues once per `(source, ability)` per batch with
    -- the summed damage before `queueAb` replicates `extraTriggerCopies`.
    let mut batchDamageByPerm : Array (ObjectId × Nat) := #[]
    for e in batch do
      match e.change with
      | .rules (.damage (.dealt pkts)) =>
        for pkt in pkts do
          if pkt.amount > 0 then
            match pkt.recipient with
            | .permanent recSnap =>
              let recObj := findEventObj post recSnap
              match batchDamageByPerm.findIdx? (fun (id, _) => id == recObj.id) with
              | some idx =>
                let (id, amt) := batchDamageByPerm[idx]!
                batchDamageByPerm := batchDamageByPerm.set! idx (id, amt + pkt.amount)
              | none =>
                batchDamageByPerm := batchDamageByPerm.push (recObj.id, pkt.amount)
            | _ => pure ()
      | _ => pure ()
    let mut firedSourceDealtDamage : Array ObjectId := #[]
    for e in batch do
      -- Saga chapter and Nth-plan-counter triggers on counters put in this event
      let isZoneArrival :=
        match e.change with
        | .rules (.zone (.moved _ _ _ .battlefield ..))
        | .rules (.zone (.created ..)) => true
        | _ => false
      for (eo, kind, n, _) in e.countersPutInEvent do
        if n > 0 then
          match eo.id.bind post.findObject? with
          | some postObj =>
            if postObj.isOnBattlefield && !postObj.status.faceDown then
              if kind == .lore then
                match postObj.controller, postObj.printed.saga with
                | some p, some sdef =>
                  let prevLore := if isZoneArrival then 0 else eo.counters.count .lore
                  for i in [0:n] do
                    let lore := prevLore + i + 1
                    for ch in sdef.chaptersForLore lore do
                      match ch.chapterEffect with
                      | some ce =>
                        let (w, fs) :=
                          queueAb post p postObj (TriggeredAbility.sagaChapter lore ce) .sagaChapter
                            (w := waiting) (fs := firedSources)
                        waiting := w; firedSources := fs
                      | none => pure ()
                | _, _ => pure ()
              else if kind == .plan && !isZoneArrival then
                match postObj.controller with
                | some p =>
                  let prevPlan := eo.counters.count .plan
                  for i in [0:n] do
                    let planCnt := prevPlan + i + 1
                    let (w, fs) :=
                      queueSrc post p postObj (.nthPlanCounter planCnt)
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                | none => pure ()
          | none => pure ()
      match e.change with
      | .engine _ => pure ()
      | .rules r =>
        match r with
        | .zone (.created obj ctrl) =>
          if obj.zone == .battlefield && !post.eventSuppressedByKarn e then
            let entered := findEventObj post obj
            -- Self enters triggers
            let (w, fs) := queueSrc post ctrl entered .entering (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
            -- Another Elf you control enters
            if post.hasSubtype entered .elf then
              let (w, fs) :=
                queueCtrl post ctrl .anotherElfYouControlEnters (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Another creature you control enters
            if entered.isCreature then
              let (w, fs) :=
                queueCtrl post ctrl .anotherCreatureYouControlEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Subtype enter triggers (Balin, Fíli, Kíli, Thorin)
            for src in post.permanentsOf ctrl do
              let self := src.id == entered.id
              for ab in src.printed.triggeredAbilities ++ src.status.grantedTriggeredAbilities do
                let opts := ab.opts
                let fireSub (ev : TriggerEvent) (cond : Bool)
                    (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :=
                  if ab.firesOn ev && cond then
                    queueAb post ctrl src ab ev (cause := some entered) (w := w) (fs := fs)
                  else (w, fs)
                let (w, fs) :=
                  match opts.thisOrNontokenSubtype with
                  | some s =>
                    fireSub .thisOrNontokenSubtypeYouControlEnters
                      (self || (!entered.printed.isToken && post.hasSubtype entered s))
                      waiting firedSources
                  | none => (waiting, firedSources)
                let (w, fs) :=
                  match opts.thisOrAnotherSubtype with
                  | some s =>
                    fireSub .thisOrAnotherSubtypeYouControlEnters
                      (self || post.hasSubtype entered s) w fs
                  | none => (w, fs)
                let (w, fs) :=
                  match opts.anotherSubtypeOrEquipment with
                  | some s =>
                    fireSub .anotherSubtypeOrEquipmentYouControlEnters
                      (!self && (post.hasSubtype entered s || entered.printed.isEquipment)) w fs
                  | none => (w, fs)
                waiting := w; firedSources := fs
            -- Per-token enter triggers (Belladonna Took; Mister Fantastic is batch group 5)
            if entered.printed.isToken then
              let (w, fs) :=
                queueCtrl post ctrl .tokenYouControlEnters
                  (keep := fun ab => ab.shared != .watch .tokensEnterMayDraw)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.printed.isArtifact then
              let (w, fs) := queueCtrl post ctrl .artifactYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.isCreature then
              let (w, fs) := queueCtrl post ctrl .creatureYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for sub in entered.subtypes do
              let (w, fs) := queueCtrl post ctrl (.subtypeYouControlEnters sub) (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.printed.isEquipment then
              let (w, fs) := queueCtrl post ctrl .equipmentYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if post.hasSubtype entered .villain || entered.printed.isArtifact then
              let (w, fs) :=
                queueCtrl post ctrl .anotherVillainOrArtifactEnters (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if post.hasSubtype entered .villain then
              let (w, fs) :=
                queueCtrl post ctrl .anotherVillainEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.types.contains .artifact then
              let (w, fs) :=
                queueCtrl post ctrl .anotherArtifactEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if !entered.printed.isToken && post.hasSubtype entered .hero then
              let (w, fs) :=
                queueCtrl post ctrl .anotherNontokenHeroEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if !entered.printed.isToken && entered.types.contains .artifact then
              let (w, fs) :=
                queueCtrl post ctrl .anotherNontokenArtifactEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            let isCreature := entered.isCreature
            if isCreature || entered.printed.isPlaneswalker then
              let (w, fs) :=
                queueFra post ctrl .anotherCreatureOrPlaneswalkerYouControlEnters
                  (cause := some entered) (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if isCreature then
              let (w, fs) :=
                queueFra post ctrl .thisOrAnotherCreatureYouControlEnters
                  (cause := some entered) (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if isCreature && !entered.printed.isToken then
              let (w, fs) :=
                queueFra post ctrl .anotherNontokenCreatureYouControlEnters
                  (cause := some entered) (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if isCreature then
              for opp in post.livingOpponents ctrl do
                let (w, fs) :=
                  queueFra post opp.id .creatureOpponentControlsEnters
                    (cause := some entered) (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              let pw := post.power entered
              let (w, fs) :=
                queueFraWhere post ctrl (fun
                  | .creatureYouControlPowerAtLeastEnters n => pw ≥ n
                  | _ => false) (cause := some entered) (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Landfall triggers
            if entered.printed.isLand then
              let fromGraveyard (ab : TriggeredAbility) : Bool :=
                match ab.shared with
                | .payReturnFromGy => true
                | _ => false
              let (w, fs) :=
                queueCtrl post ctrl .landYouControlEnters
                  (cause := some entered) (keep := (!fromGraveyard ·))
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
              if post.hasSubtype entered .mountain then
                let (w, fs) := queueCtrl post ctrl .mountainYouControlEnters (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              if post.hasSubtype entered .forest then
                let (w, fs) :=
                  queueCtrl post ctrl .forestYouControlEnters (cause := some entered)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              for gid in (post.player ctrl).graveyard do
                match post.findObject? gid with
                | some gyObj =>
                  let (w, fs) :=
                    queueSrc post ctrl gyObj .landYouControlEnters (keep := fromGraveyard)
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
                | none => pure ()
        | .zone (.moved before after fromZone toZone verb actor _ _) =>
          let beforeObj := findEventObj pre before
          let afterObj := findEventObj post after
          let ctrl := (before.controller.orElse (fun _ => after.controller)).getD before.owner
          -- Leaving the battlefield (CR 603.10a(1)): look-back on `pre`
          if fromZone == .battlefield && toZone != .battlefield then
            let lkp : Option Int := some (pre.snapshotPower beforeObj)
            let toGy : Bool := match toZone with | .graveyard _ => true | _ => false
            let died : Bool := toGy && before.creature
            let pwDied : Bool := toGy && before.planeswalker
            -- Self dies (.dying)
            if toGy then
              let keepDying (ab : TriggeredAbility) : Bool :=
                beforeObj.isCreature ||
                  match ab.shared with
                  | .returnAsArtifact => false
                  | _ => true
              let (w, fs) :=
                queueSrc pre ctrl beforeObj .dying
                  (lastKnownPower := lkp)
                  (keep := keepDying)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Self leaves the battlefield (.leaving)
            let (w, fs) :=
              queueSrc pre ctrl beforeObj .leaving
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
            -- Attached Aura triggers when enchanted creature dies (Ferocity of the Hunt)
            if died then
              for aura in pre.battlefield do
                if aura.attachedTo == some beforeObj.id then
                  match aura.controller with
                  | some p =>
                    let (w, fs) :=
                      queueSrc pre p aura (.fra .enchantedDies)
                        (cause := some beforeObj) (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                  | none => pure ()
            -- Nontoken creature you control dies
            if died && !beforeObj.printed.isToken then
              let (w, fs) :=
                queueSrc pre ctrl beforeObj (.fra .nontokenCreatureYouControlDies)
                  (cause := some beforeObj) (w := waiting) (fs := firedSources)
              let (w, fs) :=
                queueCtrl pre ctrl (.fra .nontokenCreatureYouControlDies)
                  (excludeId := some beforeObj.id) (cause := some beforeObj)
                  (w := w) (fs := fs)
              let (w, fs) :=
                queueCtrl pre ctrl .nontokenYouControlDies
                  (excludeId := some beforeObj.id)
                  (w := w) (fs := fs)
              waiting := w; firedSources := fs
            -- Another creature or planeswalker you control dies
            if died || pwDied then
              let (w, fs) :=
                queueCtrl pre ctrl (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
                  (excludeId := some beforeObj.id) (cause := some beforeObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- The Ozolith: a creature you control leaving with counters on it
            if beforeObj.isCreature && (beforeObj.status.hasCounters || !before.counters.isEmpty) then
              let (w, fs) :=
                queueCtrl pre ctrl (.fra .creatureYouControlLeaves)
                  (excludeId := some beforeObj.id) (cause := some beforeObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Villain you control dies
            if died && (pre.hasSubtype beforeObj .villain || before.villain) then
              let (w, fs) :=
                queueCtrl pre ctrl .villainYouControlDies
                  (excludeId := some beforeObj.id) (cause := some beforeObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Return-to-hand from battlefield (CR 603.10a(4)): look-back on `pre`
            if !beforeObj.printed.isLand && (match toZone with | .hand _ => true | _ => false) then
              let (w, fs) :=
                queueCtrl pre ctrl .anotherNonlandReturned
                  (excludeId := some beforeObj.id) (cause := some beforeObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Creature you control dies / Goblin, Orc, or Army dies / Attacking creature dies
            if died then
              let (w, fs) :=
                queueCtrl pre ctrl .creatureYouControlDies
                  (excludeId := some beforeObj.id) (cause := some beforeObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
              if pre.hasSubtype beforeObj .goblin || pre.hasSubtype beforeObj .orc ||
                  pre.hasSubtype beforeObj .army || before.goblinOrcArmy then
                let (w, fs) :=
                  queueCtrl pre ctrl .anotherGoblinOrcArmyDies
                    (excludeId := some beforeObj.id)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              if beforeObj.status.attacking || before.attacking then
                let (w, fs) :=
                  queueCtrl pre ctrl .attackingCreatureYouControlDies
                    (excludeId := some beforeObj.id) (cause := some afterObj)
                    (w := waiting) (fs := firedSources)
                let (w, fs) :=
                  queueSrc pre ctrl beforeObj .attackingCreatureYouControlDies
                    (cause := some afterObj) (w := w) (fs := fs)
                waiting := w; firedSources := fs
            -- Sacrifice triggers (CR 603.10a(2)): look-back on `pre`
            if verb == .sacrifice then
              let sacPlayer := actor.getD ctrl
              if e.matchesTrigger sacPlayer beforeObj.id .youSacrificeToken then
                let (w, fs) :=
                  queueCtrl pre sacPlayer .youSacrificeToken (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              -- Bolg reflexive sacrifice trigger (CR 603.10a(2) / 603.12): look-back on `pre`
              match pre.pending with
              | .maySacrificeAnotherBolg _ bolgId =>
                match (post.findObject? bolgId).orElse (fun _ => pre.findObject? bolgId) with
                | some bolg =>
                  match bolg.controller with
                  | some c =>
                    let (w, fs) :=
                      queueAb pre c bolg .onBolgDealSacrificedPower .bolgSacrificedForReflexive
                        (lastKnownPower := lkp) (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                  | none => pure ()
                | none => pure ()
              | _ => pure ()
          -- Card leaving a graveyard (CR 603.10a(3)): look-back on `pre`
          match fromZone with
          | .graveyard gyOwner =>
            if (beforeObj.printed.isCreature || before.creature) &&
                (match toZone with | .graveyard _ => false | _ => true) then
              let (w, fs) :=
                queueCtrl pre gyOwner .creatureCardLeavesYourGy
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          | _ => pure ()
          -- Entering the battlefield from another zone (CR 603.6a / 603.10): post-state
          if fromZone != .battlefield && toZone == .battlefield && !post.eventSuppressedByKarn e then
            let entered := afterObj
            let p := (after.controller.orElse (fun _ => entered.controller)).getD entered.owner
            let (w, fs) := queueSrc post p entered .entering (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
            if post.hasSubtype entered .elf then
              let (w, fs) :=
                queueCtrl post p .anotherElfYouControlEnters (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.isCreature then
              let (w, fs) :=
                queueCtrl post p .anotherCreatureYouControlEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for src in post.permanentsOf p do
              let self := src.id == entered.id
              for ab in src.printed.triggeredAbilities ++ src.status.grantedTriggeredAbilities do
                let opts := ab.opts
                let fireSub (ev : TriggerEvent) (cond : Bool)
                    (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :=
                  if ab.firesOn ev && cond then
                    queueAb post p src ab ev (cause := some entered) (w := w) (fs := fs)
                  else (w, fs)
                let (w, fs) :=
                  match opts.thisOrNontokenSubtype with
                  | some s =>
                    fireSub .thisOrNontokenSubtypeYouControlEnters
                      (self || (!entered.printed.isToken && post.hasSubtype entered s))
                      waiting firedSources
                  | none => (waiting, firedSources)
                let (w, fs) :=
                  match opts.thisOrAnotherSubtype with
                  | some s =>
                    fireSub .thisOrAnotherSubtypeYouControlEnters
                      (self || post.hasSubtype entered s) w fs
                  | none => (w, fs)
                let (w, fs) :=
                  match opts.anotherSubtypeOrEquipment with
                  | some s =>
                    fireSub .anotherSubtypeOrEquipmentYouControlEnters
                      (!self && (post.hasSubtype entered s || entered.printed.isEquipment)) w fs
                  | none => (w, fs)
                waiting := w; firedSources := fs
            if entered.printed.isToken then
              let (w, fs) :=
                queueCtrl post p .tokenYouControlEnters
                  (keep := fun ab => ab.shared != .watch .tokensEnterMayDraw)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.printed.isArtifact then
              let (w, fs) := queueCtrl post p .artifactYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.isCreature then
              let (w, fs) := queueCtrl post p .creatureYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for sub in entered.subtypes do
              let (w, fs) := queueCtrl post p (.subtypeYouControlEnters sub) (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.printed.isEquipment then
              let (w, fs) := queueCtrl post p .equipmentYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if post.hasSubtype entered .villain || entered.printed.isArtifact then
              let (w, fs) :=
                queueCtrl post p .anotherVillainOrArtifactEnters (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if post.hasSubtype entered .villain then
              let (w, fs) :=
                queueCtrl post p .anotherVillainEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if entered.types.contains .artifact then
              let (w, fs) :=
                queueCtrl post p .anotherArtifactEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if !entered.printed.isToken && post.hasSubtype entered .hero then
              let (w, fs) :=
                queueCtrl post p .anotherNontokenHeroEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if !entered.printed.isToken && entered.types.contains .artifact then
              let (w, fs) :=
                queueCtrl post p .anotherNontokenArtifactEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            let isCreature := entered.isCreature
            if isCreature || entered.printed.isPlaneswalker then
              let (w, fs) :=
                queueFra post p .anotherCreatureOrPlaneswalkerYouControlEnters
                  (cause := some entered) (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if isCreature then
              let (w, fs) :=
                queueFra post p .thisOrAnotherCreatureYouControlEnters
                  (cause := some entered) (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if isCreature && !entered.printed.isToken then
              let (w, fs) :=
                queueFra post p .anotherNontokenCreatureYouControlEnters
                  (cause := some entered) (excludeId := some entered.id)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            if isCreature then
              for opp in post.livingOpponents p do
                let (w, fs) :=
                  queueFra post opp.id .creatureOpponentControlsEnters
                    (cause := some entered) (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              let pw := post.power entered
              let (w, fs) :=
                queueFraWhere post p (fun
                  | .creatureYouControlPowerAtLeastEnters n => pw ≥ n
                  | _ => false) (cause := some entered) (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Landfall triggers
            if entered.printed.isLand then
              let fromGraveyard (ab : TriggeredAbility) : Bool :=
                match ab.shared with
                | .payReturnFromGy => true
                | _ => false
              let (w, fs) :=
                queueCtrl post p .landYouControlEnters
                  (cause := some entered) (keep := (!fromGraveyard ·))
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
              if post.hasSubtype entered .mountain then
                let (w, fs) := queueCtrl post p .mountainYouControlEnters (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              if post.hasSubtype entered .forest then
                let (w, fs) :=
                  queueCtrl post p .forestYouControlEnters (cause := some entered)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              for gid in (post.player p).graveyard do
                match post.findObject? gid with
                | some gyObj =>
                  let (w, fs) :=
                    queueSrc post p gyObj .landYouControlEnters (keep := fromGraveyard)
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
                | none => pure ()
          -- Draw triggers (post-state, CR 603.10)
          match fromZone, toZone, verb with
          | .library libP, .hand handP, .draw _ _ =>
            if libP == handP && (post.player handP).keptOpeningHand then
              let p := handP
              for o in post.permanentsOf p do
                if e.matchesTrigger p o.id .youDraw then
                  let (w, fs) := queueSrc post p o .youDraw (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
                if e.matchesTrigger p o.id .youDrawSecondCard then
                  let (w, fs) := queueSrc post p o .youDrawSecondCard (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
              if e.matchesTrigger p ⟨0⟩ .anyPlayerDrawsSecond then
                for q in post.livingPlayers do
                  for o in post.permanentsOf q.id do
                    if e.matchesTrigger q.id o.id .anyPlayerDrawsSecond then
                      let (w, fs) :=
                        queueSrc post q.id o .anyPlayerDrawsSecond (w := waiting) (fs := firedSources)
                      waiting := w; firedSources := fs
              for opp in post.livingOpponents p do
                for o in post.permanentsOf opp.id do
                  if e.matchesTrigger opp.id o.id .opponentDrawsExceptFirstDrawStep then
                    let (w, fs) :=
                      queueSrc post opp.id o .opponentDrawsExceptFirstDrawStep
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                  if e.matchesTrigger opp.id o.id .opponentDrawsSecondCard then
                    let (w, fs) :=
                      queueSrc post opp.id o .opponentDrawsSecondCard
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
          | _, _, _ => pure ()
          -- Discard / cycle triggers (post-state, CR 603.10 / 701.9 / 702.29a)
          match fromZone, toZone with
          | .hand handP, .graveyard _ =>
            if e.matchesTrigger handP beforeObj.id .youDiscard then
              let (w, fs) :=
                queueSrc post handP afterObj (.fra .youDiscardThis) (w := waiting) (fs := firedSources)
              let (w, fs) :=
                queueCtrl post handP .youDiscard
                  (lastKnownPower := some (Int.ofNat afterObj.id.raw))
                  (w := w) (fs := fs)
              let (w, fs) :=
                queueCtrl post handP (.fra .youDiscardOne)
                  (cause := some afterObj) (w := w) (fs := fs)
              waiting := w; firedSources := fs
            if afterObj.printed.cycling.isSome && e.matchesTrigger handP beforeObj.id (.fra .youCycle) then
              let x :=
                (post.proposedSpell.bind (fun prop =>
                  (post.findObject? prop.spellId).bind (·.chosenX))).orElse
                  (fun _ => afterObj.chosenX)
              let (w, fs) :=
                queueSrc post handP afterObj (.fra .youCycle)
                  (lastKnownPower := x.map Int.ofNat)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          | _, _ => pure ()
        | .zone (.ceasedToExist _) => pure ()
        | .permanent (.tapped obj _) =>
          let tObj := findEventObj post obj
          match tObj.controller.orElse (fun _ => obj.controller) with
          | some p =>
            if e.matchesTrigger p tObj.id .sourceBecomesTapped then
              let (w, fs) := queueSrc post p tObj .sourceBecomesTapped (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for eq in post.attachmentsOf tObj do
              if eq.printed.isEquipment && e.matchesTrigger p eq.id .equippedBecomesTapped then
                let (w, fs) := queueSrc post p eq .equippedBecomesTapped (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            let wasAlreadyTapped :=
              (pre.findObject? tObj.id).any (·.status.becameTappedThisTurn) ||
                tappedInBatch.contains tObj.id
            tappedInBatch := tappedInBatch.push tObj.id
            if !wasAlreadyTapped && e.matchesTrigger p tObj.id .creatureYouControlTapped then
              let (w, fs) :=
                queueCtrl post p .creatureYouControlTapped (cause := some tObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            match e.cause with
            | .costPayment .teamwork actor _ =>
              if e.matchesTrigger actor tObj.id .tappedForTeamwork then
                let (w, fs) :=
                  queueSrc post actor tObj .tappedForTeamwork (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            | _ => pure ()
          | none => pure ()
        | .permanent (.untapped _)
        | .permanent (.phasedOut _ _)
        | .permanent (.phasedIn _ _)
        | .permanent (.transformed _ _)
        | .permanent (.turnedFaceUp _)
        | .permanent (.turnedFaceDown _)
        | .permanent (.counters _ _ _ _)
        | .permanent (.attached _ _ _)
        | .permanent (.unattached _ _)
        | .permanent (.controlChanged _ _ _)
        | .permanent (.designation _ _ _) => pure ()
        | .damage (.dealt pkts) =>
          let mut dealtToPerm : Array (GameObject × Nat × Nat × Bool) := #[]
          for pkt in pkts do
            if pkt.amount > 0 then
              let srcObj? :=
                (pkt.source.id.bind post.findObject?).orElse (fun _ => pkt.source.id.bind pre.findObject?)
              let srcCtrl? :=
                pkt.source.controller.orElse (fun _ => srcObj?.bind (·.controller))
              match pkt.recipient with
              | .permanent recSnap =>
                let recObj := findEventObj post recSnap
                let noncombatAdd := if pkt.combat then 0 else pkt.amount
                match dealtToPerm.findIdx? (fun (ro, _, _, _) => ro.id == recObj.id) with
                | some idx =>
                  let (ro, amt, ncAmt, comb) := dealtToPerm[idx]!
                  dealtToPerm := dealtToPerm.set! idx (ro, amt + pkt.amount, ncAmt + noncombatAdd, comb || pkt.combat)
                | none =>
                  dealtToPerm := dealtToPerm.push (recObj, pkt.amount, noncombatAdd, pkt.combat)
              | .battle _ =>
                match srcCtrl? with
                | some pid =>
                  let srcObj := srcObj?.getD (findEventObj post pkt.source)
                  if pkt.combat then
                    let (w, fs) :=
                      queueSrc post pid srcObj .dealsCombatDamageToPlayerOrBattle
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                    if srcObj.isCreature then
                      for o in post.permanentsOf pid do
                        for ab in o.printed.triggeredAbilities do
                          match ab with
                          | .triggered _ _ opts =>
                            match ab.shared, opts.watchedSubtype with
                            | .createTokens .., some subtype =>
                              if o.id != srcObj.id && post.hasSubtype srcObj subtype then
                                let (w, fs) :=
                                  queueAb post pid o ab .dealsCombatDamageToPlayerOrBattle
                                    (w := waiting) (fs := firedSources)
                                waiting := w; firedSources := fs
                            | _, _ => pure ()
                | none => pure ()
              | .player defn =>
                if pkt.combat then
                  if !(post.player defn).lost then
                    match srcCtrl? with
                    | some pid =>
                      let srcObj := srcObj?.getD (findEventObj post pkt.source)
                      let pktEv :=
                        GameEvent.damagedPlayer e.turn pkt.source defn pkt.amount true (cause := some e.cause)
                      if pktEv.matchesTrigger pid srcObj.id .dealsCombatDamageToPlayer then
                        let (w, fs) :=
                          queueSrc post pid srcObj .dealsCombatDamageToPlayer
                            (lastKnownToughness := some (Int.ofNat defn.idx))
                            (w := waiting) (fs := firedSources)
                        waiting := w; firedSources := fs
                      let (w, fs) :=
                        queueSrc post pid srcObj .dealsCombatDamageToPlayerOrBattle
                          (w := waiting) (fs := firedSources)
                      waiting := w; firedSources := fs
                      if srcObj.isCreature then
                        for o in post.permanentsOf pid do
                          for ab in o.printed.triggeredAbilities do
                            match ab with
                            | .triggered _ _ opts =>
                              match ab.shared, opts.watchedSubtype with
                              | .createTokens .., some subtype =>
                                if o.id != srcObj.id && post.hasSubtype srcObj subtype then
                                  let (w, fs) :=
                                    queueAb post pid o ab .dealsCombatDamageToPlayerOrBattle
                                      (w := waiting) (fs := firedSources)
                                  waiting := w; firedSources := fs
                              | _, _ => pure ()
                      if post.hasSubtype srcObj .army then
                        let (w, fs) :=
                          queueCtrl post pid .armyYouControlCombatDamage
                            (w := waiting) (fs := firedSources)
                        waiting := w; firedSources := fs
                      for eq in post.battlefield do
                        if eq.attachedTo == some srcObj.id then
                          match eq.controller with
                          | some c =>
                            let (w, fs) :=
                              queueSrc post c eq .equippedDealsCombatDamageToPlayer
                                (lastKnownPower := some (Int.ofNat pkt.amount))
                                (w := waiting) (fs := firedSources)
                            waiting := w; firedSources := fs
                          | none => pure ()
                    | none => pure ()
                else
                  for q in post.livingPlayers do
                    if q.id != defn then
                      let (w, fs) :=
                        queueFra post q.id .opponentDealtNoncombatDamage
                          (w := waiting) (fs := firedSources)
                      waiting := w; firedSources := fs
          -- Per-permanent dealt-damage triggers
          for (recObj, totalAmt, noncombatAmt, _) in dealtToPerm do
            let pktEv :=
              GameEvent.damaged e.turn { owner := recObj.owner } recObj.asEvent totalAmt (noncombatAmt == 0)
            match recObj.controller with
            | some c =>
              if !firedSourceDealtDamage.contains recObj.id &&
                  pktEv.matchesTrigger c recObj.id .sourceDealtDamage then
                firedSourceDealtDamage := firedSourceDealtDamage.push recObj.id
                let batchTotal :=
                  (batchDamageByPerm.find? (fun (id, _) => id == recObj.id)).map Prod.snd |>.getD totalAmt
                let (w, fs) :=
                  queueSrc post c recObj .sourceDealtDamage
                    (lastKnownPower := some (Int.ofNat batchTotal))
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              if recObj.isCreature && pktEv.matchesTrigger c recObj.id .creatureYouControlDealtDamage then
                let (w, fs) :=
                  queueCtrl post c .creatureYouControlDealtDamage
                    (lastKnownPower := some (Int.ofNat totalAmt))
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              if noncombatAmt > 0 then
                let ncEv :=
                  GameEvent.damaged e.turn { owner := recObj.owner } recObj.asEvent noncombatAmt false
                if ncEv.matchesTrigger c recObj.id .sourceDealtNoncombatDamage then
                  let (w, fs) :=
                    queueSrc post c recObj .sourceDealtNoncombatDamage
                      (lastKnownPower := some (Int.ofNat noncombatAmt))
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
            | none => pure ()
        | .damage (.marked _ _) | .damage (.markedCleared _) | .damage (.prevented _ _ _) => pure ()
        | .life (.gained p amount) =>
          if amount > 0 && e.matchesTrigger p ⟨0⟩ .youGainLife then
            let (w, fs) :=
              queueCtrl post p .youGainLife
                (lastKnownPower := some (Int.ofNat amount))
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
        | .life (.lost p amount _ _) =>
          if amount > 0 && e.matchesTrigger p ⟨0⟩ .playerLosesLife then
            for pl in post.livingPlayers do
              for o in post.permanentsOf pl.id do
                if e.matchesTrigger pl.id o.id .playerLosesLife then
                  let (w, fs) :=
                    queueSrc post pl.id o .playerLosesLife
                      (lastKnownPower := some (Int.ofNat amount))
                      (lastKnownToughness := some (Int.ofNat p.idx))
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
        | .player (.scried p _ _ lookedAt _) =>
          if e.matchesTrigger p ⟨0⟩ .youScry then
            let (w, fs) :=
              queueCtrl post p .youScry
                (lastKnownPower := some (Int.ofNat lookedAt))
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if e.matchesTrigger p ⟨0⟩ .youScryOrSurveil then
            let (w, fs) := queueCtrl post p .youScryOrSurveil (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
        | .player (.surveilled p _ _ _ _) =>
          if e.matchesTrigger p ⟨0⟩ .youScryOrSurveil then
            let (w, fs) := queueCtrl post p .youScryOrSurveil (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
        | .player (.proliferated p _ _) =>
          let (w, fs) := queueFra post p .youProliferate (w := waiting) (fs := firedSources)
          waiting := w; firedSources := fs
        | .player (.ringTempted p _ _) =>
          if e.matchesTrigger p ⟨0⟩ .theRingTemptsYou then
            let (w, fs) := queueCtrl post p .theRingTemptsYou (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if e.matchesTrigger p ⟨0⟩ .youChooseRingBearer then
            let (w, fs) := queueCtrl post p .youChooseRingBearer (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
        | .player (.beheld _ _)
        | .player (.manaEmptied _ _ _)
        | .player (.lost _)
        | .player (.leftGame _)
        | .player (.sheHulkDealtDamage _) => pure ()
        | .turn (.stepBegan step ap) =>
          match step with
          | .upkeep =>
            if e.matchesTrigger ap ⟨0⟩ .yourUpkeep then
              let (w, fs) := queueCtrl post ap .yourUpkeep (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for pl in post.livingPlayers do
              if e.matchesTrigger pl.id ⟨0⟩ .eachUpkeep then
                let (w, fs) := queueCtrl post pl.id .eachUpkeep (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            -- Abilities that trigger from a graveyard (Command the Stage)
            for pl in post.livingPlayers do
              for gid in (post.player pl.id).graveyard do
                match post.findObject? gid with
                | some card =>
                  let (w, fs) :=
                    queueSrc post pl.id card (.fra .eachUpkeepFromGraveyard)
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
                | none => pure ()
            -- Auras with “at the beginning of the upkeep of enchanted creature's controller”
            for aura in post.battlefield do
              match aura.attachedTo.bind post.findObject?, aura.controller with
              | some host, some c =>
                if host.controlledBy ap then
                  let (w, fs) :=
                    queueSrc post c aura .enchantedControllerUpkeep
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
              | _, _ => pure ()
          | .draw =>
            for opp in post.livingOpponents ap do
              let (w, fs) :=
                queueCtrl post opp.id .eachOpponentDrawStep (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          | .precombatMain =>
            let (w, fs) := queueCtrl post ap .yourFirstMain (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          | .beginningOfCombat =>
            for pl in post.livingPlayers do
              if pl.id != ap then
                let (w, fs) :=
                  queueFra post pl.id .opponentBeginCombat (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            if e.matchesTrigger ap ⟨0⟩ .yourBeginCombat then
              let (w, fs) := queueCtrl post ap .yourBeginCombat (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for pl in post.livingPlayers do
              if e.matchesTrigger pl.id ⟨0⟩ .eachBeginCombat then
                let (w, fs) := queueCtrl post pl.id .eachBeginCombat (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            for gid in (post.player ap).graveyard do
              match post.findObject? gid with
              | some card =>
                let (w, fs) :=
                  queueSrc post ap card (.fra .yourBeginCombatFromGraveyard)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              | none => pure ()
          | .end =>
            for pl in post.livingPlayers do
              if e.matchesTrigger pl.id ⟨0⟩ .eachEndStep then
                let (w, fs) := queueCtrl post pl.id .eachEndStep (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            if e.matchesTrigger ap ⟨0⟩ .yourEndStep then
              let (w, fs) := queueCtrl post ap .yourEndStep (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          | _ => pure ()
        | .turn (.turnBegan _ _)
        | .turn (.phaseBegan _)
        | .turn (.stepEnded _)
        | .turn (.phaseEnded _)
        | .turn (.turnEnded _)
        | .turn (.extraStepAdded _ _)
        | .turn (.dayNightChanged _)
        | .turn (.extraTurnAdded _ _)
        | .turn (.extraPhaseAdded _ _) => pure ()
        | .combat (.attackersDeclared activePlayer decls) =>
          let attackerIds := decls.map (fun (eo, _) => eo.id.getD ⟨0⟩)
          let attackers := attackerIds.filterMap post.findObject?
          if !attackers.isEmpty then
            -- Zombie token with power >= 6 and Sphinxes count (from declareAttackers)
            let mut sphinxes := 0
            for a in attackers do
              if a.printed.isToken && post.hasSubtype a .zombie && post.snapshotPower a >= 6 then
                let (w, fs) :=
                  queueFra post activePlayer .zombieTokenAttacks (cause := some a)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              if post.hasSubtype a .sphinx then
                sphinxes := sphinxes + 1
            if sphinxes > 0 then
              let (w, fs) :=
                queueFra post activePlayer .sphinxesAttack
                  (lastKnownPower := some (Int.ofNat sphinxes))
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Per-attacker triggers (from putAttackTriggersOnStack)
            for a in attackers do
              let whom := post.defendingPlayerOf a
              if e.matchesTrigger activePlayer a.id .attacking then
                let (w, fs) :=
                  queueSrc post activePlayer a .attacking
                    (lastKnownPower := some (post.snapshotPower a))
                    (lastKnownToughness := some (post.snapshotToughness a))
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              if e.matchesTrigger activePlayer a.id (.fra .creatureYouControlAttacks) then
                let (w, fs) :=
                  queueFra post activePlayer .creatureYouControlAttacks (cause := some a)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              let alone :=
                !attackers.any (fun a' =>
                  a'.id != a.id && post.defendingPlayerOf a' == whom &&
                    a'.status.attackingPlaneswalker?.isNone) &&
                  a.status.attackingPlaneswalker?.isNone
              if alone then
                let (w, fs) :=
                  queueFra post activePlayer .creatureYouControlAttacksPlayerAlone (cause := some a)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
              for aura in post.battlefield do
                if aura.attachedTo == some a.id then
                  match aura.controller with
                  | some c =>
                    let (w, fs) :=
                      queueSrc post c aura .enchantedAttacksOrBlocks
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                  | none => pure ()
              let (w, fs) :=
                queueFra post whom .creatureAttacksYouOrYourPlaneswalker (cause := some a)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Garruk, Curse Breaker: once for each opponent attacked
            let attackedPlayers := attackers.foldl (fun (acc : Array PlayerId) o =>
              if o.status.attackingPlaneswalker?.isSome then acc
              else
                let d := post.defendingPlayerOf o
                if acc.contains d then acc else acc.push d) #[]
            for d in attackedPlayers do
              match attackers.find? (fun o =>
                  o.status.attackingPlaneswalker?.isNone &&
                    post.defendingPlayerOf o == d) with
              | some o =>
                for q in post.livingPlayers do
                  if q.id != d then
                    let (w, fs) :=
                      queueFra post q.id .creaturesAttackYourOpponent
                        (cause := some o) (causeController := some d)
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
              | none => pure ()
            if e.matchesTrigger activePlayer attackers[0]!.id .youAttackWithElves then
              let (w, fs) :=
                queueCtrl post activePlayer .youAttackWithElves (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            let attacksSamePlayer :=
              attackers.any (fun o =>
                match o.status.attackingPlayer? with
                | none =>
                  o.status.attackingPlaneswalker?.isNone && attackers.size >= 2
                | some d =>
                  (attackers.filter (fun o' => o'.status.attackingPlayer? == some d)).size >= 2)
            if attacksSamePlayer then
              let (w, fs) :=
                queueCtrl post activePlayer .youAttackWithTwoOrMore (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            let merfolkDefenders :=
              attackers.foldl (fun acc o =>
                if !post.hasSubtype o .merfolk then acc
                else
                  let d := post.defendingPlayerOf o
                  if acc.any (· == d) then acc else acc.push d)
                (#[] : Array PlayerId)
            for _ in merfolkDefenders do
              let (w, fs) :=
                queueCtrl post activePlayer .merfolkAttackPlayer (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for o in attackers do
              if post.battlefield.any (fun eq =>
                  eq.printed.isEquipment && eq.attachedTo == some o.id &&
                    eq.controlledBy activePlayer) then
                let (w, fs) :=
                  queueCtrl post activePlayer .equippedCreatureYouControlAttacks
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            let (w, fs) := queueCtrl post activePlayer .youAttack (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
            let pumps := (post.player activePlayer).attackPumpPerPlainsThisTurn
            if pumps > 0 then
              let src :=
                match (post.permanentsOf activePlayer).find? (fun o => o.printed.saga.isSome) with
                | some o => o
                | none =>
                  { printed := { name := "Roads Go Ever, Ever On", types := #[.enchantment] }
                    id := ⟨0⟩, owner := activePlayer, controller := some activePlayer, zone := .battlefield }
              for _ in [0:pumps] do
                let (w, fs) :=
                  queueAb post activePlayer src .onYouAttackPumpTargetPerPlains .youAttack
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            let attackingNow :=
              (post.permanentsOf activePlayer).filter (fun o => o.isCreature && o.status.attacking)
            if attackingNow.size == 1 then
              let attacker := attackingNow[0]!
              let aid := attacker.id
              for o in post.permanentsOf activePlayer do
                let (w, fs) :=
                  queueSrc post activePlayer o .creatureYouControlAttacksAlone
                    (cause := some attacker) (w := waiting) (fs := firedSources)
                let (w, fs) :=
                  if o.attachedTo == some aid then
                    queueSrc post activePlayer o .equippedAttacksAlone (w := w) (fs := fs)
                  else (w, fs)
                waiting := w; firedSources := fs
            let totalPower :=
              attackers.foldl (fun acc o => acc + post.snapshotPower o) 0
            if totalPower >= 12 then
              let (w, fs) :=
                queueCtrl post activePlayer .youAttackWithTotalPower (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for a in attackers do
              for eq in post.battlefield do
                if eq.attachedTo == some a.id then
                  match eq.controller with
                  | some c =>
                    let (w, fs) :=
                      queueSrc post c eq .equippedAttacks (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                  | none => pure ()
        | .combat (.blockersDeclared _ decls) =>
          let mut seenBlockers : Array ObjectId := #[]
          for (blockerSnap, _) in decls do
            let b := findEventObj post blockerSnap
            if !seenBlockers.contains b.id then
              seenBlockers := seenBlockers.push b.id
              for aura in post.battlefield do
                if aura.attachedTo == some b.id then
                  match aura.controller with
                  | some c =>
                    let (w, fs) :=
                      queueSrc post c aura .enchantedAttacksOrBlocks
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
                  | none => pure ()
              if post.power b ≤ 1 || post.toughness b ≤ 1 then
                for pl in post.livingPlayers do
                  if some pl.id != b.controller then
                    let (w, fs) :=
                      queueFra post pl.id .opponentSmallCreatureBlocks (cause := some b)
                        (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
        | .combat (.becameBlocked attackerSnap _) =>
          let attacker := findEventObj post attackerSnap
          match attacker.controller.orElse (fun _ => attackerSnap.controller) with
          | some p =>
            let (w, fs) :=
              queueSrc post p attacker .becomesBlocked (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          | none => pure ()
        | .combat (.remainedUnblocked _)
        | .combat (.becameAttacking _ _)
        | .combat (.damageAssigned _ _ _)
        | .combat (.removedFromCombat _) => pure ()
        | .cast (.spellCast spellSnap caster fromZone) =>
          if spellSnap.name.isEmpty then pure ()
          else
          let castObj := findEventObj post spellSnap
          let targets := ((post.stackEntry? castObj.id).map (·.targets)).getD #[]
          let uniquePerm := uniquePermTargets post targets
          -- Target triggers from casting a spell (CR 601.2i)
          for o in uniquePerm do
            match o.controller with
            | some c =>
              if c != caster then
                let (w, fs) :=
                  queueSrc post c o .becomesTarget (cause := some o)
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            | none => pure ()
          for o in uniquePerm do
            match o.controller with
            | some c =>
              let (w, fs) :=
                queueSrc post c o .spellTargetsSource (cause := some castObj)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            | none => pure ()
          let spells := post.loggedSpellsCast caster
          let nonc := post.loggedNoncreatureSpells caster
          let mvCast := spellSnap.manaValue
          if e.matchesTrigger caster castObj.id .youCastInstantOrSorcery then
            let (w, fs) := queueCtrl post caster .youCastInstantOrSorcery (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if e.matchesTrigger caster castObj.id (.fra .castThis) then
            let (w, fs) := queueSrc post caster castObj (.fra .castThis) (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          for opp in post.livingOpponents caster do
            let (w, fs) :=
              queueFraWhere post opp.id (fun
                | .opponentCastsSpellMvAtMost n => mvCast ≤ n
                | _ => false) (cause := some castObj) (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if castObj.isPreparedSpell then
            let (w, fs) :=
              queueFra post caster .youCastPreparedSpell (cause := some castObj)
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if castObj.printed.isCreature || castObj.printed.isArtifact then
            let (w, fs) :=
              queueFra post caster .youCastArtifactOrCreature (cause := some castObj)
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          let targetsOwnCreature := uniquePerm.any (fun o => o.isCreature && o.controlledBy caster)
          if castObj.printed.isEquipment || targetsOwnCreature then
            let (w, fs) :=
              queueFra post caster .youCastEquipmentOrTargetingCreatureYouControl
                (cause := some castObj) (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if castObj.printed.isCreature then
            let (w, fs) :=
              queueCtrl post caster .youCastCreature
                (lastKnownPower := some (Int.ofNat mvCast))
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          else
            let (w, fs) :=
              queueCtrl post caster .youCastNoncreature
                (cause := some castObj) (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          for opp in post.livingOpponents caster do
            let (w, fs) := queueCtrl post opp.id .opponentCastsSpell (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if spells == 2 then
            let (w, fs) :=
              queueCtrl post caster .youCastSecondSpell (cause := some castObj)
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          let colors := castObj.printed.colors
          let fromHand := (fromZone == .hand caster) || castObj.castFromHand
          for c in Color.all do
            if colors.contains c then
              let (w, fs) := queueCtrl post caster (.youCastColor c) (w := waiting) (fs := firedSources)
              let (w, fs) :=
                if fromHand then queueCtrl post caster (.youCastColorFromHand c) (w := w) (fs := fs)
                else (w, fs)
              waiting := w; firedSources := fs
          if colors.contains .green then
            let (w, fs) := queueCtrl post caster .youCastGreen (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if castObj.treasureManaSpent then
            let (w, fs) := queueCtrl post caster .youCastWithTreasure (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          for opp in post.livingOpponents caster do
            for o in post.permanentsOf opp.id do
              match o.status.chosenOdd with
              | some odd =>
                let parityOk := if odd then mvCast % 2 == 1 else mvCast % 2 == 0
                if parityOk then
                  let (w, fs) :=
                    queueSrc post opp.id o .opponentCastsMatchingParity
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
              | none => pure ()
          if spells == 2 then
            for pl in post.livingPlayers do
              let (w, fs) :=
                queueCtrl post pl.id .anyPlayerCastsSecondSpell (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          let (w, fs) := queueCtrl post caster .youCastSpell (w := waiting) (fs := firedSources)
          waiting := w; firedSources := fs
          -- Extort (CR 702.101a): each instance triggers separately.
          for o in post.permanentsOf caster do
            if o.staticAbilities.any (fun | .extort => true | _ => false) then
              let extortAb : TriggeredAbility :=
                .triggered .enter
                  { resolution := .extort
                    phrase := "You may pay {W/B}. If you do, each opponent loses 1 life and you gain that much life" }
                  {}
              let (w, fs) :=
                queueAb post caster o extortAb .youCastSpell (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          if castObj.printed.hasSubtype .villain then
            let (w, fs) := queueCtrl post caster .youCastVillain (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if targetsOwnCreature then
            let (w, fs) :=
              queueCtrl post caster .youCastTargetingCreatureYouControl (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if uniquePerm.any (·.isCreature) then
            let (w, fs) :=
              queueCtrl post caster .youCastTargetingCreature (cause := some castObj)
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if castObj.printed.isInstantOrSorcery &&
              uniquePerm.any (fun o => o.types.contains .artifact || o.types.contains .land) then
            let (w, fs) :=
              queueCtrl post caster .youCastInstantSorceryTargetingArtifactOrLand
                (cause := some castObj) (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          let targetsOpponentOrTheirCreature :=
            targets.any (fun t =>
              match t with
              | .player q => q != caster
              | .permanent id =>
                (post.findObject? id).any (fun o =>
                  o.isOnBattlefield && o.isCreature && o.controller.isSome && !o.controlledBy caster)
              | _ => false)
          if targetsOpponentOrTheirCreature then
            let (w, fs) :=
              queueCtrl post caster .youCastTargetingOpponentOrTheirCreature
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if !castObj.printed.isCreature && nonc == 1 then
            let (w, fs) :=
              queueCtrl post caster .youCastFirstNoncreature (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
            for opp in post.livingOpponents caster do
              let (w, fs) :=
                queueCtrl post opp.id .opponentCastsFirstNoncreature (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
        | .cast (.abilityActivated abilityId sourceSnap controller kind) =>
          let srcObj? := sourceSnap.id.bind post.findObject?
          let srcObj := srcObj?.getD (findEventObj post sourceSnap)
          match kind with
          | .nonMana loyaltyDelta _ _ _ =>
            match loyaltyDelta with
            | some k =>
              for opp in post.livingOpponents controller do
                for o in post.permanentsOf opp.id do
                  if e.matchesTrigger opp.id srcObj.id (.fra .opponentActivatesLoyaltyAbility) then
                    let (w, fs) :=
                      queueSrc post opp.id o (.fra .opponentActivatesLoyaltyAbility)
                        (cause := some srcObj) (w := waiting) (fs := firedSources)
                    waiting := w; firedSources := fs
              let removed : Nat := if k < 0 then (-k).toNat else 0
              if e.matchesTrigger controller ⟨0⟩ .youActivateLoyaltyAbility then
                for o in post.permanentsOf controller do
                  for ab in o.matchingTriggers .youActivateLoyaltyAbility do
                    if ab.shared != .drawIfRemovedTwoLoyalty || removed ≥ 2 then
                      let lkp :=
                        if ab.shared == .drawIfRemovedTwoLoyalty then some (Int.ofNat removed)
                        else none
                      let (w, fs) :=
                        queueAb post controller o ab .youActivateLoyaltyAbility
                          (lastKnownPower := lkp) (w := waiting) (fs := firedSources)
                      waiting := w; firedSources := fs
            | none => pure ()
            if srcObj?.any (·.isCreature) || sourceSnap.creature then
              let (w, fs) :=
                queueCtrl post controller .youActivateCreatureAbility
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            let targets :=
              ((post.stackEntry? abilityId).orElse (fun _ => post.stack.back?)).map (·.targets)
                |>.getD #[]
            for o in uniquePermTargets post targets do
              match o.controller with
              | some c =>
                if c != controller then
                  let (w, fs) :=
                    queueSrc post c o .becomesTarget (cause := some o)
                      (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
              | none => pure ()
          | .mana =>
            if srcObj?.any (·.isCreature) || sourceSnap.creature then
              let (w, fs) :=
                queueCtrl post controller .youActivateCreatureAbility
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
        | .cast (.targeted objId rawTargets _) =>
          if post.proposedSpell.isNone && !rawTargets.isEmpty then
            match post.findObject? objId, post.stackEntry? objId with
            | some obj, some se =>
              let ctrl := se.controller
              if obj.abilityEffect.isSome || obj.triggeredAbility.isSome then
                let targeting :=
                  ((obj.abilityEffect.map (·.targeting)).orElse (fun _ =>
                    obj.triggeredAbility.map (·.targeting))).getD (EffectTargeting.of .none)
                let totalSlots := targeting.kind.spec.slots.size
                if se.targets.size + se.skippedOptionalSlots ≥ totalSlots then
                  let (w, fs) :=
                    queueCtrl post ctrl .youTargetSomething (w := waiting) (fs := firedSources)
                  waiting := w; firedSources := fs
                  for o in uniquePermTargets post rawTargets do
                    match o.controller with
                    | some c =>
                      if c != ctrl then
                        let (w, fs) :=
                          queueSrc post c o .becomesTarget (cause := some o)
                            (w := waiting) (fs := firedSources)
                        waiting := w; firedSources := fs
                    | none => pure ()
              else if obj.isCopy then
                for o in uniquePermTargets post rawTargets do
                  match o.controller with
                  | some c =>
                    if c != ctrl then
                      let (w, fs) :=
                        queueSrc post c o .becomesTarget (cause := some o)
                          (w := waiting) (fs := firedSources)
                      waiting := w; firedSources := fs
                  | none => pure ()
            | _, _ => pure ()
        | .cast (.announced _ _ _ _)
        | .cast (.proposed _ _ _ _) => pure ()
        | .stackObject (.resolved obj nth) =>
          if nth == 0 then
            let ctrl := obj.controller.getD obj.owner
            let (w, fs) := queueCtrl post ctrl .finalSagaChapterResolves (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
        | .stackObject (.copied _ _ _) | .stackObject (.removedOnResolution _) => pure ()
        | .triggerQueue (.triggered _ _ _ _) | .triggerQueue (.putOnStack _ _ _) => pure ()
        | .spentMana _ _
        | .effectCreated _ _
        | .effectExpired _ _
        | .effectUpdated _ _ => pure ()
    return waiting

/-- Close an outermost rules-event batch: evaluate `matchTriggers pre g batchEvents`,
record `TriggerQueueEvent.triggered` for each triggered ability, and enqueue the
resulting `WaitingTrigger`s (CR 603.2 / 603.2c / 603.3 / 603.10). -/
def closeBatch (g : Game) (pre : GameSnapshot) (batchId : BatchId)
    (batchEvents : Array GameEvent) : Game :=
  if batchEvents.isEmpty then g
  else
    let anyEntered := batchEvents.any fun ev =>
      match ev.change with
      | .rules (.zone (.moved _ _ _ .battlefield _ _ _ _))
      | .rules (.zone (.created _ _)) => true
      | _ => false
    let g :=
      if !anyEntered then g
      else
        g.players.foldl (fun g pl =>
          let p := pl.id
          let g :=
            if !g.hasEnduringStory p && g.controlsStoried p && g.storiedPermanentCount p ≥ 3 then
              let g := g.modifyPlayer p (fun pl => { pl with enduringStory := true })
              { g with log := g.log.push s!"{(g.player p).name} has an enduring story" }
            else g
          if !g.hasCitysBlessing p && g.controlsAscend p && g.permanentCount p ≥ 10 then
            let g := g.modifyPlayer p (fun pl => { pl with citysBlessing := true })
            { g with log := g.log.push s!"{(g.player p).name} has the city's blessing" }
          else g) g
    let wts := matchTriggers pre g batchEvents
    if wts.isEmpty then g
    else
      let preWaiting := g.waitingTriggers
      let (g, toEnqueue, _, _) := wts.foldl
        (fun (acc, q, coalesced, hulkAdded) wt =>
          let key := (wt.source.id, wt.ability)
          let alreadyInPre :=
            wt.event == .sourceDealtDamage &&
              preWaiting.any (fun t =>
                t.source.id == wt.source.id && t.ability == wt.ability &&
                  t.event == .sourceDealtDamage)
          if alreadyInPre then
            if coalesced.contains key then
              (acc, q, coalesced, hulkAdded)
            else
              let amt := wt.lastKnownPower.getD 0
              let wt' := acc.waitingTriggers.map (fun t =>
                if t.source.id == wt.source.id && t.ability == wt.ability &&
                    t.event == .sourceDealtDamage then
                  { t with lastKnownPower := some (t.lastKnownPower.getD 0 + amt) }
                else t)
              ({ acc with waitingTriggers := wt' }, q, coalesced.push key, hulkAdded)
          else
            let ev :=
              { (GameEvent.triggered acc.turnNumber (acc.snapshot wt.source) wt.controller wt.ability
                  batchId) with
                batch := batchId }
            let acc := { acc with events := acc.events.push ev }
            let isHulkEnrage :=
              wt.event == .sourceDealtDamage &&
                wt.ability.shared == .watch .hulk &&
                wt.source.status.attacking
            let (acc, hulkAdded) :=
              if isHulkEnrage && !hulkAdded.contains wt.source.id then
                let eng :=
                  GameEvent.engine acc.turnNumber
                    (.enrageGrantsAdditionalCombat (acc.enrageGrantsAdditionalCombat + 1))
                (({ acc with events := acc.events.push eng }).applyChange eng.change,
                  hulkAdded.push wt.source.id)
              else (acc, hulkAdded)
            (acc, q.push wt, coalesced, hulkAdded))
        (g, #[], (#[] : Array (ObjectId × TriggeredAbility)), (#[] : Array ObjectId))
      if toEnqueue.isEmpty then g else g.enqueueWaitingTriggers toEnqueue

/-- Resolve `cause` within an active batch `batchCause?`, sharing the batch's
minted `EffectId` across all one-shot events in the batch (CR 610). -/
def resolveCauseInBatch (g : Game) (batchCause? : Option EventCause) :
    EventCause → EventCause × Option EffectId × Option EventCause
  | .unclassified =>
    match batchCause? with
    | some bc =>
      let (bc', bumpId?) := g.resolveOneShotCause bc
      (bc', bumpId?, some bc')
    | none =>
      let (c', bumpId?) := g.resolveOneShotCause .unclassified
      (c', bumpId?, if bumpId?.isSome then some c' else none)
  | .oneShotEffect none src ctrl =>
    match batchCause? with
    | some (.oneShotEffect (some bid) bsrc bctrl) =>
      let c' := EventCause.oneShotEffect (some bid) (src.orElse (fun _ => bsrc)) (ctrl.orElse (fun _ => bctrl))
      (c', some bid, batchCause?)
    | some (.oneShotEffect none bsrc bctrl) =>
      let (c', bumpId?) :=
        g.resolveOneShotCause (.oneShotEffect none (src.orElse (fun _ => bsrc)) (ctrl.orElse (fun _ => bctrl)))
      (c', bumpId?, some c')
    | _ =>
      let (c', bumpId?) := g.resolveOneShotCause (.oneShotEffect none src ctrl)
      (c', bumpId?, batchCause?.orElse (fun _ => some c'))
  | .oneShotEffect (some bid) src ctrl =>
    let (c', bumpId?) := g.resolveOneShotCause (.oneShotEffect (some bid) src ctrl)
    let nextBatchCause? :=
      match batchCause? with
      | some (.oneShotEffect none _ _) | none => some c'
      | some bc => some bc
    (c', bumpId?, nextBatchCause?)
  | .replaced rep orig =>
    let (orig', bumpId?, nextBatchCause?) := g.resolveCauseInBatch batchCause? orig
    (.replaced rep orig', bumpId?, nextBatchCause?)
  | c =>
    let (c', bumpId?) := g.resolveOneShotCause c
    (c', bumpId?, batchCause?)

/-- Apply a single `.rules` `GameEvent` under `batchId`, updating `g.currentBatch`
if a fresh one-shot cause is minted. -/
def applySingleRulesEventInBatch (g : Game) (batchId : BatchId) (e : GameEvent) :
    Game × GameEvent :=
  let batchCause? := (g.currentBatch.map Prod.snd).join
  match e.change with
  | .engine _ =>
    let g := { g with events := g.events.push e }
    (g.applyChange e.change, e)
  | .rules r =>
    let (cause', bumpId?, nextBatchCause?) := g.resolveCauseInBatch batchCause? e.cause
    let r' : RulesEvent :=
      match r with
      | .zone (.moved before after fromZone toZone verb actor entersWith libPos) =>
        if after.id.isNone then
          let newId : ObjectId := ⟨g.nextObjectId⟩
          .zone (.moved before { after with id := some newId } fromZone toZone verb actor entersWith libPos)
        else r
      | .zone (.created object controller) =>
        if object.id.isNone then
          let newId : ObjectId := ⟨g.nextObjectId⟩
          .zone (.created { object with id := some newId } controller)
        else r
      | .stackObject (.copied original copy controller) =>
        if copy.id.isNone then
          let newId : ObjectId := ⟨g.nextObjectId⟩
          .stackObject (.copied original { copy with id := some newId } controller)
        else r
      | _ => r
    let e' : GameEvent := { e with batch := batchId, cause := cause', change := .rules r' }
    let g : Game :=
      { g with
        events := g.events.push e'
        nextBatchId := max g.nextBatchId (batchId.raw + 1)
        currentBatch := g.currentBatch.map (fun (bid, _) => (bid, nextBatchCause?)) }
    let g := g.applyChange e'.change
    let g :=
      match bumpId? with
      | some actualId => { g with nextEffectId := max g.nextEffectId (actualId.raw + 1) }
      | none => g
    (g, e')

/-- Process one `GameEvent`, appending it to `g.events` and applying its
`GameChange`. When called outside an active batch, a `.rules` event forms its
own one-event batch and evaluates triggers immediately (CR 603.2c / 610). -/
def applyEvent (g : Game) (e : GameEvent) : Game :=
  match e.change with
  | .engine _ =>
    let g := { g with events := g.events.push e }
    g.applyChange e.change
  | .rules _ =>
    match g.currentBatch with
    | some (batchId, _) =>
      (g.applySingleRulesEventInBatch batchId e).1
    | none =>
      let batchId : BatchId := ⟨g.nextBatchId⟩
      let pre : GameSnapshot := g
      let g0 := { g with currentBatch := some (batchId, none) }
      let (g1, e') := g0.applySingleRulesEventInBatch batchId e
      let g2 := { g1 with currentBatch := none }
      g2.closeBatch pre batchId #[e']

/-- Record a change that happened. Replacements consult an event before
this, and do not record a change they replace (CR 614.6). -/
def record (g : Game) (e : GameEvent) : Game :=
  g.applyEvent e

/-- Record a sequence of events in order, processing each in isolation. -/
def recordAll (g : Game) (es : Array GameEvent) : Game :=
  es.foldl Game.record g

/-- Add and process an `EngineChange` on the current turn. -/
def change (g : Game) (c : EngineChange) : Game :=
  g.record (GameEvent.engine g.turnNumber c)

/-- Append `next` after the currently stored `g.pendingReplacement` (if any), so
multi-step operations resume remaining work once `Pending.chooseReplacement` finishes. -/
def chainPendingReplacement (g : Game) (next : PendingReplacement) : Game :=
  match g.pendingReplacement with
  | some first => g.change (.pendingReplacement (some (.seq first next)))
  | none => g.change (.pendingReplacement (some next))

/-- Close an outermost rules-event batch `batchId` that started at `startIdx`,
reconstructing its pre-batch `GameSnapshot` from `openBatchObjects`,
`openBatchPlayers`, `openBatchEffects`, `openBatchPending`, and `g.events[0:startIdx]`. -/
def finishOpenBatch (g : Game) (batchId : BatchId) (startIdx : Nat) : Game :=
  let pre : GameSnapshot :=
    { g with
      objects := g.openBatchObjects
      players := g.openBatchPlayers
      activeEffects := g.openBatchEffects
      pending := g.openBatchPending
      events := g.events.extract 0 (min startIdx g.events.size) }
  let g2 :=
    { g with
      currentBatch := none
      openBatchObjects := #[]
      openBatchPlayers := #[]
      openBatchEffects := #[]
      openBatchPending := .none }
  let slice := g2.events.extract (min startIdx g2.events.size) g2.events.size
  let batchEvents := slice.filter (fun ev =>
    match ev.change with
    | .rules _ => ev.batch == batchId
    | .engine _ => false)
  if batchEvents.isEmpty then g2
  else g2.closeBatch pre batchId batchEvents

/-- Run `f` inside a simultaneous rules-event batch (CR 603.2c / 608.2c / 704.3).
If a batch is already active on `g`, `f` joins the enclosing batch; otherwise a
new `BatchId` is opened and triggers are evaluated once when `f` completes (or
after `Pending.chooseReplacement` finishes if `f` pauses for a replacement choice). -/
def withBatchReturn {α : Type} (g : Game) (cause : Option EventCause := none)
    (f : Game → Game × α) : Game × α :=
  match g.currentBatch with
  | some (batchId, prevCause?) =>
    let mergedCause? := prevCause?.orElse (fun _ => cause)
    let (g1, res) := f { g with currentBatch := some (batchId, mergedCause?) }
    let g2 :=
      if prevCause?.isNone && cause.isSome then
        { g1 with currentBatch := some (batchId, none) }
      else g1
    (g2, res)
  | none =>
    let batchId : BatchId := ⟨g.nextBatchId⟩
    let startIdx := g.events.size
    let g0 :=
      { g with
        currentBatch := some (batchId, cause)
        nextBatchId := max g.nextBatchId (batchId.raw + 1)
        openBatchObjects := g.objects
        openBatchPlayers := g.players
        openBatchEffects := g.activeEffects
        openBatchPending := g.pending }
    let (g1, res) := f g0
    let keepOpen :=
      match g1.pending with
      | .chooseReplacement ..
      | .fraChoice _ (.chooseColor _)
      | .fraChoice _ (.entersCreatureType _)
      | .fraChoice _ (.entersOddEven _)
      | .fraChoice _ (.chooseCardName _) => true
      | _ => g1.pendingReplacement.isSome
    if keepOpen then
      (g1.chainPendingReplacement (.closeBatch batchId startIdx), res)
    else
      (g1.finishOpenBatch batchId startIdx, res)

/-- Run `f` inside a simultaneous rules-event batch (CR 603.2c / 608.2c / 704.3). -/
def withBatch (g : Game) (cause : Option EventCause := none) (f : Game → Game) : Game :=
  (g.withBatchReturn cause (fun g => (f g, ()))).1

/-- Commit a batch of simultaneous rules events with explicit per-event causes
under a single `BatchId`, then evaluate batch-level triggers once (CR 603.2c / 704.3). -/
def commitBatchWithCauses (g : Game) (events : Array (EventCause × RulesEvent)) : Game :=
  if events.isEmpty then g
  else
    g.withBatch none (fun g =>
      events.foldl (fun acc (cause, r) =>
        acc.record (GameEvent.rules acc.turnNumber r cause)) g)

/-- Commit a batch of simultaneous rules events sharing `cause` and a single
`BatchId` (CR 608.2c / 610). Resolves `g.resolveOneShotCause cause` once so every
event of a one-shot instruction shares one `EffectId` and one `BatchId`. -/
def commitBatch (g : Game) (cause : EventCause) (events : Array RulesEvent) : Game :=
  if events.isEmpty then g
  else
    let (cause', bumpId?) := g.resolveOneShotCause cause
    let g :=
      match bumpId? with
      | some actualId => { g with nextEffectId := max g.nextEffectId (actualId.raw + 1) }
      | none => g
    g.commitBatchWithCauses (events.map (fun r => (cause', r)))

/-- Run `f` under an active resolving context `(src, ctrl)` (CR 608 / 610.1).
If `f` leaves a pending choice or random continuation open, the context stays
set until resolution finishes. -/
def withResolvingContext (g : Game) (src : Option ObjectId) (ctrl : PlayerId)
    (f : Game → Game) : Game :=
  let prev := g.resolvingContext
  let g := f (g.change (.resolvingContext (some (src, ctrl))))
  if g.pending != .none || g.afterRandom != .none then g
  else g.change (.resolvingContext prev)

/-- Resolving one-shot cause for a player action (`p` is the fallback controller
when no resolving spell or ability is on the stack; CR 610.1). -/
def resolvingOneShotCause (g : Game) (p : PlayerId)
    (source : Option ObjectId := none) : Option EventCause :=
  match g.currentBatch with
  | some (_, some (.oneShotEffect (some bid) bsrc bctrl)) =>
    some (.oneShotEffect (some bid) (bsrc.orElse (fun _ => source)) (bctrl.orElse (fun _ => some p)))
  | _ =>
    let (src, ctrl) :=
      match g.currentResolvingContext? with
      | some (s, c) => (source.orElse (fun _ => s), c.orElse (fun _ => some p))
      | none => (source, some p)
    some (.oneShotEffect (some ⟨g.nextEffectId⟩) src ctrl)

/-- Look up the `EventCause` recorded when `eid` was created in `g.events`,
falling back to `.unclassified` when no creation event exists. -/
def effectCreatedCause (g : Game) (eid : EffectId)
    (fallbackSrc : Option ObjectId := none) (fallbackCtrl : PlayerId) : EventCause :=
  let fromEvents? :=
    g.events.findSomeRev? fun ev =>
      match ev.change with
      | .rules (.effectCreated id eff) =>
        if id == eid then
          let effSrc :=
            match eff with
            | .pendingLokiCopy _ s _ => s.orElse (fun _ => fallbackSrc)
            | _ => fallbackSrc
          match ev.cause with
          | .oneShotEffect oid src ctrl =>
            some (.oneShotEffect oid (src.orElse (fun _ => effSrc))
              (ctrl.orElse (fun _ => some fallbackCtrl)))
          | c => some c
        else none
      | _ => none
  fromEvents?.getD .unclassified

/-- Resolving one-shot cause for a batch when a spell or ability is actively
resolving, or `none` when called outside a resolving context (CR 608.2c / 610.1). -/
def resolvingBatchCause (g : Game) (p : PlayerId)
    (source : Option ObjectId := none) : Option EventCause :=
  g.currentResolvingContext?.map fun (src, ctrl) =>
    .oneShotEffect none (source.orElse (fun _ => src)) (ctrl.orElse (fun _ => some p))

/-- Allocate a one-shot `EventCause` for a delayed triggered ability (CR 603.7)
or linked-exile return (CR 610.3), bumping `g.nextEffectId` so the stored cause
carries the `EffectId` allocated when the delay or link was set up. -/
def allocDelayedCause (g : Game) (fallbackCtrl : Option PlayerId := none)
    (source : Option ObjectId := none) : Game × EventCause :=
  let (src, ctrl) :=
    match g.currentResolvingContext? with
    | some (s, c) => (source.orElse (fun _ => s), c.orElse (fun _ => fallbackCtrl))
    | none => (source, fallbackCtrl)
  let id : EffectId := ⟨g.nextEffectId⟩
  let g := g.change (.nextEffectId (g.nextEffectId + 1))
  (g, .oneShotEffect (some id) src ctrl)

/-- Look up the stored exiling `EventCause` for a card in `linkedExile` (CR 610.3). -/
def linkedExileCause? (g : Game) (id : ObjectId) : Option EventCause :=
  (g.linkedExileCauses.find? (·.1 == id)).map (·.2)

/-- Add and process a sequence of `EngineChange`s on the current turn. -/
def changes (g : Game) (cs : Array EngineChange) : Game :=
  cs.foldl Game.change g

/-- Remove any `ReplacementId`s that were applied during an event from
`g.replacementOrder` so player preferences apply only to the current event
and do not stick across subsequent events (CR 616.1). -/
def consumeReplacementOrder (g : Game) (applied : Array ReplacementId) : Game :=
  if g.replacementOrder.isEmpty || applied.isEmpty then g
  else
    let next := g.replacementOrder.filter (fun id => !applied.contains id)
    if next == g.replacementOrder then g
    else g.change (.replacementOrder next)

/-- Open `Pending.chooseReplacement` for `chooser` over `choices` and stash
`cont` in `g.pendingReplacement` so `Action.chooseReplacement` can resume the
event once the player chooses (CR 616.1). -/
def promptChooseReplacement (g : Game) (chooser : PlayerId)
    (choices : Array ReplacementId) (cont : PendingReplacement) : Game :=
  g.changes #[
    .pending (.chooseReplacement chooser choices),
    .pendingReplacement (some cont)
  ]

/-- Add and process a `PlayerChange` for `p`. -/
def changePlayer (g : Game) (p : PlayerId) (c : PlayerChange) : Game :=
  g.change (.player p c)

/-- Add and process multiple `PlayerChange`s for `p`. -/
def changePlayers (g : Game) (p : PlayerId) (cs : Array PlayerChange) : Game :=
  g.change (.playerChanges p cs)

/-- Add and process a `StackEntryChange` at stack index `idx`. -/
def changeStackEntry (g : Game) (idx : Nat) (c : StackEntryChange) : Game :=
  g.change (.stackEntry idx c)

/-- Add and process a `StackEntryChange` for the stack entry with `objectId`. -/
def changeStackEntryById (g : Game) (objectId : ObjectId) (c : StackEntryChange) : Game :=
  g.change (.stackEntryById objectId c)

/-- Add and process a `ProposalChange` on the current proposed spell or ability. -/
def changeProposal (g : Game) (c : ProposalChange) : Game :=
  g.change (.proposal c)

/-- Add and process multiple `ProposalChange`s on the current proposed spell or ability. -/
def changeProposals (g : Game) (cs : Array ProposalChange) : Game :=
  g.change (.proposalChanges cs)

def logMsg (g : Game) (msg : String) : Game :=
  g.change (.logMsg msg)

/-- Whether `o` is in a zone and state where its printed static abilities
generate continuous effects (CR 611.3b). -/
def hasActivePrintedStatics (o : GameObject) : Bool :=
  (o.zone == .battlefield && !o.status.phasedOut && !o.status.faceDown &&
    !o.status.losesAbilitiesUntilEot && o.status.losesAbilitiesGrantedBy.isEmpty) ||
  o.zone == .command

/-- The object a continuous effect applies to (the source, for a static
ability's effect). `none` for effects on players or the whole game. -/
def effectObject? : ContinuousEffect → Option ObjectId
  | .staticAbility id _ | .auraConstruct55 id | .pump id _ _ | .untilTurnOfPump id _ _ _
  | .pumpPerArtifactUntilEot id | .keywordsUntilEot id _ | .firstStrikeOnYourTurn id
  | .loseIndestructibleUntilEot id | .exileIfDiesUntilEot id | .setBasePTUntilEot id _
  | .cardsInHandPowerUntilEot id | .additionalCreature id _ | .additionalArtifactUntilEot id
  | .additionalSubtype id _ _ | .replacedCreatureTypesUntilEot id _ | .onlyFoodArtifact id
  | .returnedAsArtifact id | .notACreature id | .grantedStatic id _ | .grantedTriggered id _ _
  | .ironFistTapUntilEot id _ | .combatDamageCreatesTreasureUntilEot id
  | .losesAbilitiesUntilEot id | .losesAbilitiesWhileSource id _ | .hexproofWhileSource id _
  | .preventDamageWhileSource id _ | .cantUntapWhileSource id _
  | .cantBeBlockedByPlayerUntilEot id _ | .cantBeBlockedExceptByHasteUntilEot id
  | .cantBlockUntilEot id | .colorlessGrantUntilCast id _
  | .freeCastFromGraveyardUntilEot id | .flashbackUntilEot id | .exileInstantSorceryInstead id
  | .uncounterableThisCast id | .playPermission id _ | .fraEmblemUntilTurnOf id _
  | .copy id _ _ _ _ _ | .control id _ _ _ _ => some id
  | _ => none

/-- A continuous effect on an object that lasts until end of turn and ends in
the cleanup step (CR 514.2). -/
def effectEndsAtCleanup : ContinuousEffect → Bool
  | .pump .. | .keywordsUntilEot .. | .loseIndestructibleUntilEot _ | .exileIfDiesUntilEot _
  | .setBasePTUntilEot .. | .additionalArtifactUntilEot _ | .additionalCreature _ true
  | .cantBeBlockedByPlayerUntilEot .. | .cantBeBlockedExceptByHasteUntilEot _
  | .cantBlockUntilEot _ | .replacedCreatureTypesUntilEot .. | .pumpPerArtifactUntilEot _
  | .ironFistTapUntilEot .. | .losesAbilitiesUntilEot _ | .grantedTriggered _ _ true
  | .cardsInHandPowerUntilEot _ | .firstStrikeOnYourTurn _
  | .combatDamageCreatesTreasureUntilEot _ | .freeCastFromGraveyardUntilEot _
  | .flashbackUntilEot _ | .replacement _ true | .prevention _ true => true
  | _ => false

/-- The active continuous effect recorded under `eid`, if any. -/
def activeEffect? (g : Game) (eid : EffectId) : Option ContinuousEffect :=
  (g.activeEffects.find? (·.1 == eid)).map (·.2)

/-- Record the creation of `o`'s printed static-ability continuous effects if `o`
is active on the battlefield or in the command zone (CR 611.3). -/
def createPrintedStaticEffects (g : Game) (o : GameObject)
    (cause : Option EventCause := some (.gameRule .staticAbility)) : Game :=
  if hasActivePrintedStatics o then
    o.printed.staticAbilities.foldl (fun acc sa =>
      let eid : EffectId := ⟨acc.nextEffectId⟩
      acc.record (GameEvent.effectCreated acc.turnNumber eid (.staticAbility o.id sa) (cause := cause))) g
  else g

/-- Record the expiration of `o`'s active printed static-ability continuous
effects (CR 611.3), each under the `EffectId` it was created with. -/
def expirePrintedStaticEffects (g : Game) (o : GameObject)
    (cause : Option EventCause := some (.gameRule .leavingZone)) : Game :=
  o.printed.staticAbilities.foldl (fun acc sa =>
    let eff := ContinuousEffect.staticAbility o.id sa
    match acc.activeEffects.find? (fun (_, e) => e == eff) with
    | some (eid, _) => acc.record (GameEvent.effectExpired acc.turnNumber eid eff (cause := cause))
    | none => acc) g

/-- Record and apply the creation of a continuous effect (CR 611). Assigns a
fresh unique `EffectId` from `g.nextEffectId` and updates any dependent
static-ability continuous effects when an object loses all abilities or becomes
a copy. -/
def createEffect (g : Game) (eff : ContinuousEffect)
    (cause : Option EventCause := none) : Game :=
  let (g, cause) : Game × Option EventCause :=
    match cause with
    | some c =>
      match c with
      | .oneShotEffect (some cid) _ _ =>
        if g.nextEffectId ≤ cid.raw then
          (g.change (.nextEffectId (cid.raw + 1)), some c)
        else (g, some c)
      | .oneShotEffect none _ _ =>
        let (c', bumpId?) := g.resolveOneShotCause c
        match bumpId? with
        | some cid => (g.change (.nextEffectId (max g.nextEffectId (cid.raw + 1))), some c')
        | none => (g, some c')
      | _ => (g, some c)
    | none =>
      match g.currentBatch with
      | some (_, some (.oneShotEffect (some bid) bsrc bctrl)) =>
        (g, some (.oneShotEffect (some bid) bsrc bctrl))
      | _ =>
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause ctrl src
          (g, some c)
        | none => (g, none)
  match eff with
  | .losesAbilitiesUntilEot id | .losesAbilitiesWhileSource id _ =>
    let prev? := g.findObject? id
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff (cause := cause))
    match prev? with
    | some prev => g.expirePrintedStaticEffects prev (cause := cause)
    | none => g
  | .copy id newPrinted _ _ _ _ =>
    let prev? := g.findObject? id
    let g :=
      match prev? with
      | some prev => g.expirePrintedStaticEffects prev (cause := cause)
      | none => g
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff (cause := cause))
    match g.findObject? id with
    | some cur =>
      if hasActivePrintedStatics cur then
        newPrinted.staticAbilities.foldl (fun acc sa =>
          let sid : EffectId := ⟨acc.nextEffectId⟩
          acc.record (GameEvent.effectCreated acc.turnNumber sid (.staticAbility id sa)
            (cause := some (.gameRule .staticAbility)))) g
      else g
    | none => g
  | .control id _ _ _ _ =>
    let prevCtrl? := (g.findObject? id).bind (·.controller)
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff (cause := cause))
    match g.findObject? id with
    | some o =>
      let fromP := prevCtrl?.getD (o.defaultController.getD o.owner)
      match g.effectiveController? o with
      | some toP =>
        if fromP != toP then g.record (GameEvent.control g.turnNumber id fromP toP (cause := cause))
        else g
      | none => g
    | none => g
  | _ =>
    let eid : EffectId := ⟨g.nextEffectId⟩
    g.record (GameEvent.effectCreated g.turnNumber eid eff (cause := cause))

/-- Record and apply the creation of multiple continuous effects in order (CR 611). -/
def createEffects (g : Game) (effs : Array ContinuousEffect)
    (cause : Option EventCause := none) : Game :=
  if effs.isEmpty then g
  else
    let (g, cause) : Game × Option EventCause :=
      match cause, g.currentBatch, g.currentResolvingContext? with
      | none, some (_, some (.oneShotEffect (some bid) bsrc bctrl)), _ =>
        (g, some (.oneShotEffect (some bid) bsrc bctrl))
      | none, _, some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause ctrl src
        (g, some c)
      | some (.oneShotEffect none src ctrl), _, _ =>
        let (c', bumpId?) := g.resolveOneShotCause (.oneShotEffect none src ctrl)
        match bumpId? with
        | some cid => (g.change (.nextEffectId (max g.nextEffectId (cid.raw + 1))), some c')
        | none => (g, some c')
      | _, _, _ => (g, cause)
    effs.foldl (fun acc e => acc.createEffect e (cause := cause)) g

/-- Record and apply the expiration of the active continuous effect recorded
under `eid` (CR 611), using the payload stored when it was created or last
updated. Also updates any dependent static-ability continuous effects when an
ability-loss or copy effect ends on an object still on the battlefield. An id
that is not active records nothing. -/
def expireEffectById (g : Game) (eid : EffectId)
    (cause : Option EventCause := none) : Game :=
  match g.activeEffect? eid with
  | none => g
  | some eff =>
    match eff with
    | .losesAbilitiesUntilEot id | .losesAbilitiesWhileSource id _ =>
      let wasActive := (g.findObject? id).map hasActivePrintedStatics |>.getD false
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := cause))
      match g.findObject? id with
      | some cur =>
        if !wasActive && hasActivePrintedStatics cur then g.createPrintedStaticEffects cur
        else g
      | none => g
    | .copy id _ _ _ _ _ =>
      let prev? := g.findObject? id
      let g :=
        match prev? with
        | some prev => g.expirePrintedStaticEffects prev (cause := cause)
        | none => g
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := cause))
      match g.findObject? id with
      | some cur => g.createPrintedStaticEffects cur
      | none => g
    | .control id _ _ _ _ =>
      let prevCtrl? := (g.findObject? id).bind (·.controller)
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := cause))
      match g.findObject? id with
      | some o =>
        let fromP := prevCtrl?.getD (o.defaultController.getD o.owner)
        match g.effectiveController? o with
        | some toP =>
          if fromP != toP then g.record (GameEvent.control g.turnNumber id fromP toP (cause := cause))
          else g
        | none => g
      | none => g
    | _ => g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := cause))

/-- Record and apply the expiration of the earliest active continuous effect
equal to `eff` (CR 611). When no such effect is active, nothing is recorded
and nothing is rolled back. -/
def expireEffect (g : Game) (eff : ContinuousEffect)
    (cause : Option EventCause := none) : Game :=
  match g.activeEffects.find? (fun (_, e) => e == eff) with
  | some (eid, _) => g.expireEffectById eid (cause := cause)
  | none => g

/-- Record and apply the expiration of every active continuous effect matching
`pred`, each under its own `EffectId` (CR 611). -/
def expireMatching (g : Game) (pred : ContinuousEffect → Bool)
    (cause : Option EventCause := none) : Game :=
  let matching := g.activeEffects.filter (fun (_, e) => pred e)
  matching.foldl (fun acc (eid, _) => acc.expireEffectById eid (cause := cause)) g

/-- Record and apply the expiration of every active continuous effect equal to
`eff`, e.g. when their shared duration ends (CR 611). -/
def expireAll (g : Game) (eff : ContinuousEffect)
    (cause : Option EventCause := none) : Game :=
  g.expireMatching (· == eff) (cause := cause)

/-- Record and apply the expiration of multiple continuous effects in order (CR 611). -/
def expireEffects (g : Game) (effs : Array ContinuousEffect)
    (cause : Option EventCause := none) : Game :=
  effs.foldl (fun acc e => acc.expireEffect e (cause := cause)) g

/-- `id` is a permanent that was cast for its impending cost (CR 702.176,
ruling 970). -/
def loggedCastForImpending (g : Game) (id : ObjectId) : Bool :=
  GameEvent.castForImpending g.events id

/-- Synchronize an impending permanent's `.notACreature` continuous effect with
its time counters after an object or status change (CR 702.176, ruling 970c):
as long as a permanent cast for its impending cost has a time counter on it, it
isn't a creature; when it has no time counters, that effect ends, and if time
counters are later put or moved onto it, a new `.notACreature` effect is
created. -/
def syncImpendingNotACreature (g : Game) (id : ObjectId)
    (cause : Option EventCause := none) : Game :=
  let effCause :=
    match cause with
    | some c => some c
    | none =>
      match g.currentResolvingContext? with
      | some (src, ctrl) => some (.oneShotEffect (some ⟨g.nextEffectId⟩) src ctrl)
      | none => some (.gameRule .impending)
  match g.findObject? id with
  | none => g
  | some o =>
    if o.zone != .battlefield || !o.printed.impending.isSome then g
    else if o.status.time == 0 then
      if o.status.notACreature || g.hasActiveEffect (.notACreature id) then
        g.expireAll (.notACreature id) (cause := effCause)
      else g
    else if g.loggedCastForImpending id && !o.status.notACreature then
      g.createEffect (.notACreature id) (cause := effCause)
    else g

/-- Add and process an `ObjectChange` for `id`. -/
def changeObject (g : Game) (id : ObjectId) (c : ObjectChange) : Game :=
  (g.change (.object id c)).syncImpendingNotACreature id

/-- Add and process multiple `ObjectChange`s for `id`. -/
def changeObjects (g : Game) (id : ObjectId) (cs : Array ObjectChange) : Game :=
  (g.change (.objectChanges id cs)).syncImpendingNotACreature id

/-- Add and process a `StatusChange` for `id`. -/
def changeStatus (g : Game) (id : ObjectId) (c : StatusChange) : Game :=
  g.changeObject id (.status c)

/-- Add and process multiple `StatusChange`s for `id`. -/
def changeStatuses (g : Game) (id : ObjectId) (cs : Array StatusChange) : Game :=
  g.changeObject id (.statuses cs)

/-- Expire every until-end-of-turn continuous effect on `o`, each under its
own `EffectId` (CR 514.2). -/
def expireObjectUntilEotEffects (g : Game) (o : GameObject) : Game :=
  g.expireMatching (fun e => effectEndsAtCleanup e && effectObject? e == some o.id)
    (cause := some (.turnBased .cleanupClear))

/-- Expire every active continuous effect on `o` when `o` leaves its zone or
ceases to exist (CR 400.7, CR 611), each under its own `EffectId`. Call after
`o` has been removed/replaced in `g.objects` so ability-loss or copy expiration
does not re-create `o`'s static abilities. -/
def expireEffectsOnLeavingObject (g : Game) (o : GameObject)
    (cause : Option EventCause := some (.gameRule .leavingZone)) : Game :=
  let g := g.expirePrintedStaticEffects o (cause := cause)
  g.expireMatching (fun e => effectObject? e == some o.id) (cause := cause)

/-- Drop a stashed `unlessPays` effect. Paying, or countering for real,
clears it; leaving without paying sets `unlessPaysDue` instead. -/
def clearUnlessPays (g : Game) : Game :=
  g.changes #[.unlessPaysInstead none, .unlessPaysDue false, .unlessPaysTargets #[]]

/-- Drop a stashed `SpellResolution.may` after the player accepts or declines. -/
def clearMay (g : Game) : Game :=
  g.changes #[.mayEffect none, .mayTargets #[]]

/-- Drop a stashed `SpellResolution.or` after the player has chosen. -/
def clearSpellOr (g : Game) : Game :=
  g.changes #[.spellOr #[], .spellOrTargets #[], .spellOrLibrary false]

/-- Record that combat damage was dealt to `p`. -/
def noteCombatDamageTo (g : Game) (p : PlayerId) (source : EventObject) : Game :=
  g.record (GameEvent.damagedPlayer g.turnNumber source p 1 true)

/-- Set `p`'s life total by gaining or losing the difference (CR 119.5) and log `msg`. -/
def setLife (g : Game) (p : PlayerId) (life : Int) (msg : String) : Game :=
  let pl := g.player p
  if (pl.lifeLocked || pl.lifeCantChange) && life != pl.life then
    g.logMsg s!"{pl.name}'s life total can't change"
  else if life > pl.life then
    (g.record (GameEvent.life g.turnNumber p (life - pl.life).toNat true)).logMsg msg
  else if life < pl.life then
    (g.record (GameEvent.life g.turnNumber p (pl.life - life).toNat false)).logMsg msg
  else
    g.logMsg msg

/-- End every active copy effect on a battlefield object selected by `sel`,
each under its own `EffectId`, restoring the original printed card (CR 707).
`sel` sees the object and the effect's durations (until end of turn, until next
turn, until a source leaves). Does not cause the permanent to enter or leave
the battlefield. -/
def restoreCopiesWhere (g : Game)
    (sel : GameObject → Bool → Bool → Option ObjectId → Bool)
    (cause : Option EventCause := none) : Game :=
  g.activeEffects.foldl (fun acc (eid, e) =>
    match e with
    | .copy id printed restore untilEot untilNextTurn untilSourceLeaves =>
      match acc.findObject? id with
      | some o =>
        if o.zone == .battlefield && sel o untilEot untilNextTurn untilSourceLeaves then
          let card? := restore.orElse (fun _ => o.copyRestore)
          let acc := acc.expireEffectById eid (cause := cause)
          match card? with
          | some card => acc.logMsg s!"{card.name} is no longer a copy of {printed.name}"
          | none => acc
        else acc
      | none => acc
    | _ => acc) g

/-- End every copy effect on `o`, restoring its original printed card (CR 707).
Does not cause the permanent to enter or leave the battlefield. -/
def restoreCopy (g : Game) (o : GameObject) : Game :=
  g.restoreCopiesWhere (fun x _ _ _ => x.id == o.id)

/-- Restore copy effects on battlefield objects that satisfy `p`. -/
def restoreCopiesIf (g : Game) (p : GameObject → Bool) : Game :=
  g.restoreCopiesWhere (fun o _ _ _ => p o)

/-- Restore copy effects that last until end of turn. -/
def restoreCopiesUntilEot (g : Game) : Game :=
  g.restoreCopiesWhere (fun _ untilEot _ _ => untilEot)
    (cause := some (.turnBased .cleanupClear))

/-- Restore copy effects that last until `p`'s next turn. -/
def restoreCopiesUntilNextTurn (g : Game) (p : PlayerId) : Game :=
  g.restoreCopiesWhere (fun o _ untilNextTurn _ => untilNextTurn && o.controller == some p)
    (cause := some (.turnBased .expireAtStepBegin))

/-- Restore copy effects that last until `srcId` leaves the battlefield. -/
def restoreCopiesUntilSourceLeaves (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.gameRule .leavingZone)) : Game :=
  g.restoreCopiesWhere (fun _ _ _ untilSourceLeaves => untilSourceLeaves == some srcId)
    (cause := cause)

/-- End the control-changing effects that last until `srcId` leaves, each under
its own `EffectId` (Super Hero Civil War; MSH 143). Other control-changing
effects on the same permanent keep applying (CR 613.7). -/
def restoreControlUntilSourceLeaves (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.gameRule .leavingZone)) : Game :=
  g.activeEffects.foldl (fun acc (eid, e) =>
    match e with
    | .control id _ _ _ (some s) =>
      if s != srcId then acc
      else
        match acc.findObject? id with
        | none => acc.expireEffectById eid (cause := cause)
        | some o =>
          let acc := acc.expireEffectById eid (cause := cause)
          let p := o.defaultController.getD o.owner
          let othersRemain := acc.activeEffects.any (fun (_, e) =>
            match e with
            | .control oid _ _ _ _ => oid == id
            | _ => false)
          if othersRemain then
            match (acc.findObject? id).bind (·.controller) with
            | some q => acc.logMsg s!"{o.name} returns to {(acc.player q).name}'s control"
            | none => acc
          else if (acc.player p).lost then
            acc.logMsg s!"{o.name} does not change control (CR 800.4b)"
          else
            acc.logMsg s!"{o.name} returns to {(acc.player p).name}'s control"
    | _ => acc) g

/-- Expire all continuous effects on other objects that last for as long as
`srcId` remains on the battlefield (CR 611.2b), each under its own `EffectId`. -/
def expireWhileSourceEffects (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.gameRule .leavingZone)) : Game :=
  let g := g.restoreCopiesUntilSourceLeaves srcId (cause := cause)
  let g := g.restoreControlUntilSourceLeaves srcId (cause := cause)
  g.expireMatching (fun
    | .hexproofWhileSource _ s | .preventDamageWhileSource _ s
    | .cantUntapWhileSource _ s | .losesAbilitiesWhileSource _ s => s == srcId
    | _ => false) (cause := cause)

/-- Last player-controlling effect wins (MSH 259). The controlled player
remains the active player on their turn (MSH 300) and still controls their
permanents (MSH 358). `onNextTurn` makes the control start on the controlled
player's next turn they actually take. -/
def setPlayerControl (g : Game) (you them : PlayerId) (onNextTurn : Bool := false) : Game :=
  let g :=
    g.createEffect (.playerControl you them onNextTurn)
      |>.logMsg
        s!"{(g.player you).name} controls {(g.player them).name} during their next turn"
  match (g.player them).teammate with
  | some mate =>
    if mate == you then g
    else
      g.logMsg
        s!"{(g.player you).name} also controls {(g.player mate).name} (Two-Headed Giant team)"
  | none => g

/-- Record putting `n` counters of `kind` on `id` via `PermanentEvent.counters`
(CR 122.1). Does nothing when `n == 0`. -/
def recordPutCounters (g : Game) (id : ObjectId) (kind : CounterKind) (n : Nat)
    (byPlayer : Option PlayerId := none) (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else
    match g.findObject? id with
    | none => g
    | some o =>
      let putter := byPlayer.orElse (fun _ => g.counterPutter o.controller)
      let (_, applied, cause', choice?, _) :=
        g.replaceCountersPutChoice o kind n (putter := byPlayer) (cause := cause)
      match choice? with
      | some (chooser, choices) =>
        g.promptChooseReplacement chooser choices
          (.recordPutCounters id kind n byPlayer cause)
      | none =>
        let g := g.consumeReplacementOrder applied
        let g := g.record (GameEvent.counters g.turnNumber putter o.asEvent kind n (cause := cause'))
        if kind == .time then g.syncImpendingNotACreature id (cause := cause') else g

/-- Record removing up to `n` counters of `kind` from `id` via
`PermanentEvent.counters` (CR 122.1). Clamps to the current counter count and
does nothing when `0` counters are removed. -/
def recordRemoveCounters (g : Game) (id : ObjectId) (kind : CounterKind) (n : Nat := 1)
    (byPlayer : Option PlayerId := none) (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let actual := min n (o.status.counterCount kind)
    if actual == 0 then g
    else
      let actor := byPlayer.orElse (fun _ => g.counterPutter o.controller)
      let g := g.record (GameEvent.counters g.turnNumber actor o.asEvent kind actual (removed := true) (cause := cause))
      if kind == .time then g.syncImpendingNotACreature id (cause := cause) else g

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
      g.withBatch cause (fun g =>
        bag.foldl (fun acc (kind, cnt) =>
          acc.recordRemoveCounters id kind cnt (byPlayer := byPlayer) (cause := cause)) g)

/-- Put all non-+1/+1 counters from `«from»` (with `extra` added to each
non-zero counter kind) onto `id`, emitting one `PermanentEvent.counters` put
per non-zero counter kind in a single batch (CR 122.1). -/
def putCountersExceptPlusOne (g : Game) (id : ObjectId) («from» : Status)
    (extra : Nat := 0) (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  let bag := «from».toCounterBag.filter (fun (k, n) => k != .plusOnePlusOne && n > 0)
  if bag.isEmpty then g
  else
    g.withBatch cause fun g => Id.run do
      let mut g := g
      for (kind, cnt) in bag do
        if let .chooseReplacement .. := g.pending then
          g := g.chainPendingReplacement (.recordPutCounters id kind (cnt + extra) byPlayer cause)
        else
          g := g.recordPutCounters id kind (cnt + extra) (byPlayer := byPlayer) (cause := cause)
      return g

end Game
end Mtg.Engine
