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
  /-- Snapshot of Head-of-the-Hunt-style replacements for one SBA death
  batch, so simultaneous deaths still see those sources (Gatherer).
  Objects are stored so a source that also dies still applies (CR 614.6). -/
  lockedDeathReplacements : Option (Array GameObject) := none
  /-- While an SBA death batch is applying, `move` skips per-object
  “other creatures die” triggers; the batch queues them only for creatures
  that actually die (CR 614.6). -/
  suppressOthersDie : Bool := false
  /-- While a simultaneous graveyard batch is applying, `move` skips
  per-object “creature cards to graveyard” triggers so “one or more”
  fires once (Robot Domination; MSH 138). -/
  suppressCreatureCardsToGy : Bool := false
  /-- True while a spell is being cast from the top of a library
  (Elven Chorus cannot show the new top until that finishes). -/
  castingFromTop : Bool := false
  /-- Cards in exile that return at the beginning of the next end step
  (Roll-Roll-Roll-Roll and similar delayed blinks). -/
  delayedEndStepReturns : Array ObjectId := #[]
  /-- Extra turns to take before the next player in turn order (Kang). -/
  extraTurns : Array PlayerId := #[]
  /-- Power-up abilities can't be activated during this extra turn (Kang). -/
  powerUpsForbidden : Bool := false
  /-- Permanents exiled at the beginning of the next end step (Vindictive
  Triumph). -/
  delayedEndStepExiles : Array ObjectId := #[]
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
  /-- Tokens created since enters triggers were last processed. -/
  pendingTokenEnters : Array ObjectId := #[]
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
  /-- Permanents sacrificed at the beginning of the next end step. -/
  delayedEndStepSacrifices : Array ObjectId := #[]
  /-- Graveyard cards that return under a chosen player at the next end step. -/
  delayedGraveReturns : Array (ObjectId × PlayerId) := #[]
  /-- At the next end step, reveal this many creature cards (Synthetic Destiny). -/
  delayedSynthetic : Array (PlayerId × Nat) := #[]
  /-- After the current search, untap the land if its controller has this many lands. -/
  untapSearchedIfLands : Option Nat := none
  /-- Players who created one or more creature tokens since the last priority. -/
  pendingCreatureTokenCreators : Array PlayerId := #[]
  /-- Lands tapped for commander-identity mana that scries a matching creature. -/
  ancestryLandsTapped : Array ObjectId := #[]
  /-- State changes that happened this game, oldest first (CR 603.2 / 614.1).
  Conditions ask this log whether an action happened. Triggers and
  replacement effects match the same events. A replaced change is not
  recorded (CR 614.6). -/
  events : Array GameEvent := #[]
deriving Repr, Inhabited

namespace Status

/-- Apply one `StatusChange` in isolation (CR 110.5). -/
def applyChange (s : Status) (c : StatusChange) : Status :=
  let kw (f : KeywordCounters → KeywordCounters) : Status :=
    { s with keywordCounters := f s.keywordCounters }
  match c with
  | .set s' => s'
  | .reset => {}
  | .addDamage n deathtouch =>
    { s with
      damage := s.damage + n
      dealtDeathtouch := s.dealtDeathtouch || (deathtouch && n > 0) }
  | .withoutCounters =>
    { s with
      plusOnePlusOne := 0, minusOneMinusOne := 0, loyaltyCounters := 0, hope := 0, charge := 0
      stun := 0, shield := 0, finality := 0, plan := 0, burden := 0, quest := 0, invasion := 0
      influence := 0, trampleCounters := 0, indestructibleCounters := 0, lifelinkCounters := 0
      hone := 0, shadow := 0, lore := 0, story := 0, time := 0, poison := 0
      keywordCounters := {} }
  | .proliferatedExceptPlusOne extra =>
    let inc (n : Nat) : Nat := if n > 0 then n + 1 + extra else n
    { s with
      loyaltyCounters := inc s.loyaltyCounters, hope := inc s.hope, charge := inc s.charge
      minusOneMinusOne := inc s.minusOneMinusOne
      stun := inc s.stun
      shield := inc s.shield
      finality := inc s.finality, plan := inc s.plan, burden := inc s.burden
      quest := inc s.quest, invasion := inc s.invasion, influence := inc s.influence
      trampleCounters := inc s.trampleCounters
      indestructibleCounters := inc s.indestructibleCounters
      lifelinkCounters := inc s.lifelinkCounters, hone := inc s.hone, shadow := inc s.shadow
      lore := inc s.lore, story := inc s.story, time := inc s.time, poison := inc s.poison
      keywordCounters := s.keywordCounters.incPresent extra }
  | .addCountersExceptPlusOne «from» extra =>
    let bump (n : Nat) : Nat := if n == 0 then 0 else n + extra
    { s with
      loyaltyCounters := s.loyaltyCounters + bump «from».loyaltyCounters
      minusOneMinusOne := s.minusOneMinusOne + bump «from».minusOneMinusOne
      hope := s.hope + bump «from».hope, charge := s.charge + bump «from».charge
      stun := s.stun + bump «from».stun
      shield := s.shield + bump «from».shield, finality := s.finality + bump «from».finality
      plan := s.plan + bump «from».plan, burden := s.burden + bump «from».burden
      quest := s.quest + bump «from».quest, invasion := s.invasion + bump «from».invasion
      influence := s.influence + bump «from».influence
      trampleCounters := s.trampleCounters + bump «from».trampleCounters
      indestructibleCounters := s.indestructibleCounters + bump «from».indestructibleCounters
      lifelinkCounters := s.lifelinkCounters + bump «from».lifelinkCounters
      hone := s.hone + bump «from».hone, shadow := s.shadow + bump «from».shadow
      lore := s.lore + bump «from».lore
      story := s.story + bump «from».story, time := s.time + bump «from».time
      poison := s.poison + bump «from».poison
      keywordCounters := s.keywordCounters.add («from».keywordCounters.plusExtra extra) }
  | .addPump p t =>
    { s with pump := (s.pump.1 + p, s.pump.2 + t) }
  | .addPlusOnePlusOne n =>
    { s with plusOnePlusOne := s.plusOnePlusOne + n }
  | .addCounters kind n =>
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
  | .removeCounters kind n =>
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
      attackingWhom := none
      attackingPlaneswalker := none
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
  | .attackingWhom v => { s with attackingWhom := v }
  | .attackingPlaneswalker v => { s with attackingPlaneswalker := v }
  | .blocking v => { s with blocking := v }
  | .blocked v => { s with blocked := v }
  | .activationsThisTurn v => { s with activationsThisTurn := v }
  | .abilitiesActivatedThisTurn v => { s with abilitiesActivatedThisTurn := v }
  | .plusOnePlusOne v => { s with plusOnePlusOne := v }
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
  | .shadow v => { s with shadow := v }
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
  | .sneakAttackWhom v => { o with sneakAttackWhom := v }
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
  | .pendingLokiCopy .. | .playerControl .. => g

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
  | .pendingLokiCopy .. | .playerControl .. => g

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
  | .phasedOut object _ =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status := { o.status with phasedOut := true } } }
    | none => g
  | .phasedIn object _ =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status := { o.status with phasedOut := false } } }
    | none => g
  | .transformed object nowBackFace =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with status := { o.status with transformed := nowBackFace } } }
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
      let sc :=
        match delta with
        | .put n => StatusChange.addCounters kind n
        | .removed n => StatusChange.removeCounters kind n
      { g with objects := g.objects.set! i { o with status := o.status.applyChange sc } }
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
            attackingWhom := after.attackingWhom
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
          | some i => g.objects.set! i fresh
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
          attackingWhom := object.attackingWhom
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
        abilityEffect := object.abilityEffect
        triggeredAbility := object.triggeredAbility
        sourceId := object.sourceId
        lastKnownPower := object.lastKnownPower
        lastKnownToughness := object.lastKnownToughness
        attachedTo := if object.zone == Zone.battlefield then object.attachedTo else none
        adventurerCard := object.adventurerCard
        wasCast := object.wasCast
        kicked := object.kicked
        teamworkPaid := object.teamworkPaid
        sneakPaid := object.sneakPaid
        sneakAttackWhom := object.sneakAttackWhom
        giftPromisedTo := object.giftPromisedTo
        isCopy := object.isCopy
        chosenX := object.chosenX }
    let objs :=
      match g.objects.findIdx? (fun o => o.id == newId) with
      | some i => g.objects.set! i fresh
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

/-- Process one `RulesEvent` in isolation. -/
def applyRulesEvent (g : Game) (r : RulesEvent) : Game :=
  match r with
  | .zone e => g.applyZoneEvent e
  | .permanent e => g.applyPermanentEvent e
  | .damage e => g.applyDamageEvent e
  | .life e => g.applyLifeEvent e
  | .cast .. | .attacked .. | .stepped .. | .activated ..
  | .spentMana .. | .playedLand .. => g
  | .effectApplied id _ =>
    { g with nextEffectId := max g.nextEffectId (id.raw + 1) }
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
  | .lockedDeathReplacements v => { g with lockedDeathReplacements := v }
  | .suppressOthersDie v => { g with suppressOthersDie := v }
  | .suppressCreatureCardsToGy v => { g with suppressCreatureCardsToGy := v }
  | .castingFromTop v => { g with castingFromTop := v }
  | .delayedEndStepReturns v => { g with delayedEndStepReturns := v }
  | .pushDelayedEndStepReturn id =>
    { g with delayedEndStepReturns := g.delayedEndStepReturns.push id }
  | .extraTurns v => { g with extraTurns := v }
  | .pushExtraTurn p => { g with extraTurns := g.extraTurns.push p }
  | .powerUpsForbidden v => { g with powerUpsForbidden := v }
  | .delayedEndStepExiles v => { g with delayedEndStepExiles := v }
  | .pushDelayedEndStepExile id =>
    { g with delayedEndStepExiles := g.delayedEndStepExiles.push id }
  | .conniveSource v => { g with conniveSource := v }
  | .plusOneAfterDiscards v => { g with plusOneAfterDiscards := v }
  | .additionalCombatPhases v => { g with additionalCombatPhases := v }
  | .enrageGrantsAdditionalCombat v => { g with enrageGrantsAdditionalCombat := v }
  | .resolvingDivision v => { g with resolvingDivision := v }
  | .pendingTokenEnters v => { g with pendingTokenEnters := v }
  | .pushPendingTokenEnter id => { g with pendingTokenEnters := g.pendingTokenEnters.push id }
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
  | .pushDelayedEndStepSacrifice id =>
    { g with delayedEndStepSacrifices := g.delayedEndStepSacrifices.push id }
  | .delayedGraveReturns v => { g with delayedGraveReturns := v }
  | .pushDelayedGraveReturn id p =>
    { g with delayedGraveReturns := g.delayedGraveReturns.push (id, p) }
  | .delayedSynthetic v => { g with delayedSynthetic := v }
  | .pushDelayedSynthetic p n =>
    { g with delayedSynthetic := g.delayedSynthetic.push (p, n) }
  | .untapSearchedIfLands v => { g with untapSearchedIfLands := v }
  | .pendingCreatureTokenCreators v => { g with pendingCreatureTokenCreators := v }
  | .pushPendingCreatureTokenCreator p =>
    { g with pendingCreatureTokenCreators := g.pendingCreatureTokenCreators.push p }
  | .ancestryLandsTapped v => { g with ancestryLandsTapped := v }
  | .pushAncestryLandTapped id =>
    { g with ancestryLandsTapped := g.ancestryLandsTapped.push id }
  | .removeAncestryLandTapped id =>
    { g with ancestryLandsTapped := g.ancestryLandsTapped.filter (· != id) }
  | .sbaChecked => g
  | .clearEvents => { g with events := #[] }

/-- Process one `GameChange` in isolation. -/
def applyChange (g : Game) (c : GameChange) : Game :=
  match c with
  | .rules r => g.applyRulesEvent r
  | .engine e => g.applyEngineChange e

/-- Process one `GameEvent` in isolation, appending it to `g.events` and
applying its `GameChange`. One-shot effects receive a fresh unique `EffectId`
from `g.nextEffectId` when recorded if not already assigned one at or above
`g.nextEffectId` (CR 610). -/
def applyEvent (g : Game) (e : GameEvent) : Game :=
  let (e, bumpId?) :=
    match e.cause, e.change with
    | .oneShotEffect id src ctrl, .rules (.effectApplied _ eff) =>
      let actualId : EffectId := if id.raw < g.nextEffectId then ⟨g.nextEffectId⟩ else id
      ({ e with
          cause := .oneShotEffect actualId src ctrl
          change := .rules (.effectApplied actualId eff) },
        some actualId)
    | _, .rules (.effectApplied id eff) =>
      let actualId : EffectId := if id.raw < g.nextEffectId then ⟨g.nextEffectId⟩ else id
      ({ e with
          cause := .oneShotEffect actualId none none
          change := .rules (.effectApplied actualId eff) },
        some actualId)
    | _, .rules (.zone (.moved before after fromZone toZone verb actor entersWith libPos)) =>
      if after.id.isNone then
        let newId : ObjectId := ⟨g.nextObjectId⟩
        ({ e with
            change := .rules (.zone (.moved before { after with id := some newId } fromZone toZone verb actor entersWith libPos)) },
          none)
      else (e, none)
    | _, .rules (.zone (.created object controller)) =>
      if object.id.isNone then
        let newId : ObjectId := ⟨g.nextObjectId⟩
        ({ e with
            change := .rules (.zone (.created { object with id := some newId } controller)) },
          none)
      else (e, none)
    | _, _ => (e, none)
  let g := { g with events := g.events.push e }
  let g := g.applyChange e.change
  match bumpId? with
  | some actualId => { g with nextEffectId := max g.nextEffectId (actualId.raw + 1) }
  | none => g

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

/-- Add and process a sequence of `EngineChange`s on the current turn. -/
def changes (g : Game) (cs : Array EngineChange) : Game :=
  cs.foldl Game.change g

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

/-- Record and apply a one-shot effect (CR 610) on the current turn, assigning
it a fresh unique `EffectId` from `g.nextEffectId`. -/
def applyOneShot (g : Game) (eff : OneShotEffect) : Game :=
  g.record (GameEvent.effectApplied g.turnNumber eff (id := ⟨g.nextEffectId⟩))

def findObject? (g : Game) (id : ObjectId) : Option GameObject :=
  g.objects.find? (fun o => o.id == id)

def object! (g : Game) (id : ObjectId) : GameObject :=
  match g.findObject? id with
  | some o => o
  | none => panic! s!"missing object {id}"

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
  | .flashbackUntilEot _ => true
  | _ => false

/-- The active continuous effect recorded under `eid`, if any. -/
def activeEffect? (g : Game) (eid : EffectId) : Option ContinuousEffect :=
  (g.activeEffects.find? (·.1 == eid)).map (·.2)

/-- Record the creation of `o`'s printed static-ability continuous effects if `o`
is active on the battlefield or in the command zone (CR 611.3). -/
def createPrintedStaticEffects (g : Game) (o : GameObject) : Game :=
  if hasActivePrintedStatics o then
    o.printed.staticAbilities.foldl (fun acc sa =>
      let eid : EffectId := ⟨acc.nextEffectId⟩
      acc.record (GameEvent.effectCreated acc.turnNumber eid (.staticAbility o.id sa))) g
  else g

/-- Record the expiration of `o`'s active printed static-ability continuous
effects (CR 611.3), each under the `EffectId` it was created with. -/
def expirePrintedStaticEffects (g : Game) (o : GameObject) : Game :=
  o.printed.staticAbilities.foldl (fun acc sa =>
    let eff := ContinuousEffect.staticAbility o.id sa
    match acc.activeEffects.find? (fun (_, e) => e == eff) with
    | some (eid, _) => acc.record (GameEvent.effectExpired acc.turnNumber eid eff)
    | none => acc) g

/-- Record and apply the creation of a continuous effect (CR 611). Assigns a
fresh unique `EffectId` from `g.nextEffectId` and updates any dependent
static-ability continuous effects when an object loses all abilities or becomes
a copy. -/
def createEffect (g : Game) (eff : ContinuousEffect) : Game :=
  match eff with
  | .losesAbilitiesUntilEot id | .losesAbilitiesWhileSource id _ =>
    let prev? := g.findObject? id
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff)
    match prev? with
    | some prev => g.expirePrintedStaticEffects prev
    | none => g
  | .copy id newPrinted _ _ _ _ =>
    let prev? := g.findObject? id
    let g :=
      match prev? with
      | some prev => g.expirePrintedStaticEffects prev
      | none => g
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff)
    match g.findObject? id with
    | some cur =>
      if hasActivePrintedStatics cur then
        newPrinted.staticAbilities.foldl (fun acc sa =>
          let sid : EffectId := ⟨acc.nextEffectId⟩
          acc.record (GameEvent.effectCreated acc.turnNumber sid (.staticAbility id sa))) g
      else g
    | none => g
  | .control id _ _ _ _ =>
    let prevCtrl? := (g.findObject? id).bind (·.controller)
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff)
    match g.findObject? id with
    | some o =>
      let fromP := prevCtrl?.getD (o.defaultController.getD o.owner)
      match g.effectiveController? o with
      | some toP =>
        if fromP != toP then g.record (GameEvent.control g.turnNumber id fromP toP)
        else g
      | none => g
    | none => g
  | _ =>
    let eid : EffectId := ⟨g.nextEffectId⟩
    g.record (GameEvent.effectCreated g.turnNumber eid eff)

/-- Record and apply the creation of multiple continuous effects in order (CR 611). -/
def createEffects (g : Game) (effs : Array ContinuousEffect) : Game :=
  effs.foldl Game.createEffect g

/-- Record and apply the expiration of the active continuous effect recorded
under `eid` (CR 611), using the payload stored when it was created or last
updated. Also updates any dependent static-ability continuous effects when an
ability-loss or copy effect ends on an object still on the battlefield. An id
that is not active records nothing. -/
def expireEffectById (g : Game) (eid : EffectId) : Game :=
  match g.activeEffect? eid with
  | none => g
  | some eff =>
    match eff with
    | .losesAbilitiesUntilEot id | .losesAbilitiesWhileSource id _ =>
      let wasActive := (g.findObject? id).map hasActivePrintedStatics |>.getD false
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff)
      match g.findObject? id with
      | some cur =>
        if !wasActive && hasActivePrintedStatics cur then g.createPrintedStaticEffects cur
        else g
      | none => g
    | .copy id _ _ _ _ _ =>
      let prev? := g.findObject? id
      let g :=
        match prev? with
        | some prev => g.expirePrintedStaticEffects prev
        | none => g
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff)
      match g.findObject? id with
      | some cur => g.createPrintedStaticEffects cur
      | none => g
    | .control id _ _ _ _ =>
      let prevCtrl? := (g.findObject? id).bind (·.controller)
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff)
      match g.findObject? id with
      | some o =>
        let fromP := prevCtrl?.getD (o.defaultController.getD o.owner)
        match g.effectiveController? o with
        | some toP =>
          if fromP != toP then g.record (GameEvent.control g.turnNumber id fromP toP)
          else g
        | none => g
      | none => g
    | _ => g.record (GameEvent.effectExpired g.turnNumber eid eff)

/-- Record and apply the expiration of the earliest active continuous effect
equal to `eff` (CR 611). When no such effect is active, nothing is recorded
and nothing is rolled back. -/
def expireEffect (g : Game) (eff : ContinuousEffect) : Game :=
  match g.activeEffects.find? (fun (_, e) => e == eff) with
  | some (eid, _) => g.expireEffectById eid
  | none => g

/-- Record and apply the expiration of every active continuous effect matching
`pred`, each under its own `EffectId` (CR 611). -/
def expireMatching (g : Game) (pred : ContinuousEffect → Bool) : Game :=
  let matching := g.activeEffects.filter (fun (_, e) => pred e)
  matching.foldl (fun acc (eid, _) => acc.expireEffectById eid) g

/-- Record and apply the expiration of every active continuous effect equal to
`eff`, e.g. when their shared duration ends (CR 611). -/
def expireAll (g : Game) (eff : ContinuousEffect) : Game :=
  g.expireMatching (· == eff)

/-- Record and apply the expiration of multiple continuous effects in order (CR 611). -/
def expireEffects (g : Game) (effs : Array ContinuousEffect) : Game :=
  effs.foldl Game.expireEffect g

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
def syncImpendingNotACreature (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    if o.zone != .battlefield || !o.printed.impending.isSome then g
    else if o.status.time == 0 then
      if o.status.notACreature || g.hasActiveEffect (.notACreature id) then
        g.expireAll (.notACreature id)
      else g
    else if g.loggedCastForImpending id && !o.status.notACreature then
      g.createEffect (.notACreature id)
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

/-- Expire every active continuous effect on `o` when `o` leaves its zone or
ceases to exist (CR 400.7, CR 611), each under its own `EffectId`. Call after
`o` has been removed/replaced in `g.objects` so ability-loss or copy expiration
does not re-create `o`'s static abilities. -/
def expireEffectsOnLeavingObject (g : Game) (o : GameObject) : Game :=
  let g := g.expirePrintedStaticEffects o
  g.expireMatching (fun e => effectObject? e == some o.id)

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

def over (g : Game) : Bool := g.result.isSome

def player (g : Game) (p : PlayerId) : Player :=
  g.players[p.idx]!

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

/-- Record that combat damage was dealt to `p`. -/
def noteCombatDamageTo (g : Game) (p : PlayerId) (source : EventObject) : Game :=
  g.record (GameEvent.damagedPlayer g.turnNumber source p 1 true)

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

/-- Remember that `p` created one or more creature tokens (CR 603.2c).
One instruction notes the player once. -/
def noteCreatureTokenEvent (g : Game) (p : PlayerId) : Game :=
  if (g.player p).lost || g.pendingCreatureTokenCreators.contains p then g
  else g.change (.pushPendingCreatureTokenCreator p)

def livingPlayers (g : Game) : Array Player :=
  g.players.filter (fun pl => !pl.lost)

/-- True while `p` has not lost and therefore has not left (CR 104 / 800.4). -/
def stillInGame (g : Game) (p : PlayerId) : Bool :=
  !(g.player p).lost

/-- Living opponents of `p` (CR 102.2). -/
def livingOpponents (g : Game) (p : PlayerId) : Array Player :=
  g.livingPlayers.filter (fun pl => pl.id != p)

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

/-- Player being attacked this combat (CR 508.1). Taken from an attacking
creature's `attackingWhom`, or the next opponent if none is recorded. -/
def defendingPlayer (g : Game) : PlayerId :=
  match g.blockersQueue[0]? with
  | some p => p
  | none =>
    match g.objects.find? (fun o => o.isOnBattlefield && o.status.attackingWhom.isSome) with
    | some o => o.status.attackingWhom.getD (g.opponent g.activePlayer)
    | none => g.opponent g.activePlayer

/-- Distinct players being attacked, in APNAP order (CR 508.1 / 101.4). -/
def defendingPlayers (g : Game) : Array PlayerId :=
  let attacked :=
    g.objects.filterMap (fun o =>
      if o.isOnBattlefield && o.status.attacking then o.status.attackingWhom else none)
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

def battlefield (g : Game) : Array GameObject :=
  g.objects.filter GameObject.isOnBattlefield

def permanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o => o.controlledBy p)

/-- Creatures `p` currently controls. -/
def creaturesControlledBy (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (·.isCreature)

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

/-- End every active copy effect on a battlefield object selected by `sel`,
each under its own `EffectId`, restoring the original printed card (CR 707).
`sel` sees the object and the effect's durations (until end of turn, until next
turn, until a source leaves). Does not cause the permanent to enter or leave
the battlefield. -/
def restoreCopiesWhere (g : Game)
    (sel : GameObject → Bool → Bool → Option ObjectId → Bool) : Game :=
  g.activeEffects.foldl (fun acc (eid, e) =>
    match e with
    | .copy id printed restore untilEot untilNextTurn untilSourceLeaves =>
      match acc.findObject? id with
      | some o =>
        if o.zone == .battlefield && sel o untilEot untilNextTurn untilSourceLeaves then
          let card? := restore.orElse (fun _ => o.copyRestore)
          let acc := acc.expireEffectById eid
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

/-- Restore copy effects that last until `p`'s next turn. -/
def restoreCopiesUntilNextTurn (g : Game) (p : PlayerId) : Game :=
  g.restoreCopiesWhere (fun o _ untilNextTurn _ => untilNextTurn && o.controller == some p)

/-- Restore copy effects that last until `srcId` leaves the battlefield. -/
def restoreCopiesUntilSourceLeaves (g : Game) (srcId : ObjectId) : Game :=
  g.restoreCopiesWhere (fun _ _ _ untilSourceLeaves => untilSourceLeaves == some srcId)

/-- End the control-changing effects that last until `srcId` leaves, each under
its own `EffectId` (Super Hero Civil War; MSH 143). Other control-changing
effects on the same permanent keep applying (CR 613.7). -/
def restoreControlUntilSourceLeaves (g : Game) (srcId : ObjectId) : Game :=
  g.activeEffects.foldl (fun acc (eid, e) =>
    match e with
    | .control id _ _ _ (some s) =>
      if s != srcId then acc
      else
        match acc.findObject? id with
        | none => acc.expireEffectById eid
        | some o =>
          let acc := acc.expireEffectById eid
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
def expireWhileSourceEffects (g : Game) (srcId : ObjectId) : Game :=
  let g := g.restoreCopiesUntilSourceLeaves srcId
  let g := g.restoreControlUntilSourceLeaves srcId
  g.expireMatching (fun
    | .hexproofWhileSource _ s | .preventDamageWhileSource _ s
    | .cantUntapWhileSource _ s | .losesAbilitiesWhileSource _ s => s == srcId
    | _ => false)

/-- Equipment attached to `o` (Whiplash last-known X). -/
def attachedEquipmentCount (g : Game) (o : GameObject) : Nat :=
  g.battlefield.filter (fun eq =>
    eq.printed.isEquipment && eq.attachedTo == some o.id) |>.size

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

/-- Last-known `before` snapshot of `id` when it left the battlefield, read from
`ZoneEvent.moved` in `g.events` (CR 113.7a / 608.2h). -/
def lastKnownBefore? (g : Game) (id : ObjectId) : Option EventObject :=
  g.events.reverse.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved before _ .battlefield _ _ _ _ _)) =>
      if before.id == some id then some before else none
    | _ => none)

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
  if n == 0 then 0 else n + g.docSamsonBonus putter host

/-- Counters of one kind actually put on `o`. An enters-with replacement is
put by the permanent's controller (ruling 517). Otherwise the explicit
`putter`, the resolving spell or ability, or `o`'s controller. -/
def countersYouPut (g : Game) (o : GameObject) (n : Nat)
    (putter : Option PlayerId := none) (entersWith := false) : Nat :=
  let who :=
    if entersWith then o.controller
    else putter.orElse (fun _ => g.counterPutter o.controller)
  g.extraCountersOn who n (host := o.controller)

end Game
end Mtg.Engine
