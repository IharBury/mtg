import Mtg.Engine.Game.Player

/-!
# Game state core

The `Game` structure itself and basic accessors: players, opponents, and
turn order, object lookup, battlefield queries, restoring expired copy
effects, and who controls, sees, or decides for whom
(CR 800.4 / MSH player control).
-/

namespace Mtg.Engine

/-- Shared ability context for a triggered ability whose resolution is paused on
a pending choice (`sequence`, `or`, or `chooseModes`, CR 603.3 / CR 608.2). -/
structure TriggerResolutionContext where
  controller : PlayerId
  ability : TriggeredAbility
  sourceId : Option ObjectId := none
  targets : Array Target := #[]
  dividedDamage : Array Nat := #[]
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  sourceName : String := "This creature"
  cardPower : Option Nat := none
deriving Repr, Inhabited

/-- Later steps of a trigger `sequence`, waiting until the pending choice
opened by an earlier step finishes. They run before any player receives
priority, so they stay part of that resolution. -/
structure TriggerSequenceRest extends TriggerResolutionContext where
  steps : List TriggeredAbility.TriggerResolution := []
deriving Repr, Inhabited

/-- A pending `TriggerResolution.or`. The controller chooses one alternative,
then that step resolves with this ability context. -/
structure TriggerOrRest extends TriggerResolutionContext where
  alternatives : Array TriggeredAbility.TriggerResolution := #[]
deriving Repr, Inhabited

/-- A pending `TriggerResolution.chooseModes` that asks for one unused mode.
The chosen index resolves with this ability context. -/
structure ChooseModesRest extends TriggerResolutionContext where
  modes : List TriggeredAbility.TriggerResolution := []
  how : TriggeredAbility.TriggerModeHow := .oneUnused
deriving Repr, Inhabited

/-- Delayed triggered ability waiting to fire at the beginning of the next end
step (CR 603.7). -/
inductive DelayedEndStepTrigger where
  | returnExiled (id : ObjectId)
  | exilePermanent (id : ObjectId)
  | sacrificePermanent (id : ObjectId)
  | returnFromGraveyard (id : ObjectId) (controller : PlayerId)
  | syntheticDestiny (controller : PlayerId) (count : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Pre-game mulligan and opening-hand state (CR 103.5 / CR 103.6). -/
structure MulliganState where
  /-- Opening hands are kept and a “may begin on the battlefield” choice is
  still unfinished (CR 103.6). -/
  awaitingOpeningBegin : Bool := false
  /-- Players still to declare keep-or-mulligan in the current CR 103.5 round. -/
  toDeclare : Array PlayerId := #[]
  /-- Players who declared they will mulligan this round; taken together after
  every remaining player has declared (CR 103.5). -/
  willMulligan : Array PlayerId := #[]
  /-- Players who still must put cards on the bottom after simultaneous mulligans. -/
  toBottom : Array PlayerId := #[]
deriving Repr, Inhabited, BEq, DecidableEq

/-- Shared spell-resolution context (controller and announced targets) for a
pending `unlessPays`, `may`, or `or` choice (CR 608.2c). -/
structure SpellResolutionContext where
  controller : PlayerId := ⟨0⟩
  targets : Array Target := #[]
deriving Repr, Inhabited

/-- Stashed effect for a pending `unlessPays` (CR 118.12 / 608.2c). -/
structure UnlessPaysRest extends SpellResolutionContext where
  effect : Option Effect := none
  /-- The payer left without paying (CR 800.4f). -/
  due : Bool := false
deriving Repr, Inhabited

/-- Stashed effect for a pending `SpellResolution.may` (CR 608.2c). -/
structure MayEffectRest extends SpellResolutionContext where
  effect : Option Effect := none
deriving Repr, Inhabited

/-- Stashed alternatives for a pending `SpellResolution.or` (CR 608.2c). -/
structure SpellOrRest extends SpellResolutionContext where
  effects : Array Effect := #[]
  isLibrary : Bool := false
deriving Repr, Inhabited

/-- Pending `TriggerResolution.may` branch choice (CR 603.3 / 608.2c). -/
structure TriggerMayBranch where
  onAccept : Option TriggeredAbility.TriggerResolution := none
  onDecline : Option TriggeredAbility.TriggerResolution := none
  context : Option TriggerSequenceRest := none
deriving Repr, Inhabited

/-- Follow-up action after a library search completes (CR 701.23). -/
inductive AfterLibrarySearch where
  | none
  | plusOneOn (id : ObjectId)
  | untapSearchedIfLands (minLands : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Combat phase state: damage assignment, blockers queue, first-strike tracking,
and additional combat phases (CR 508 / CR 509 / CR 510 / CR 702.7b). -/
structure CombatPhaseState where
  /-- Combat damage assigned this step and not yet dealt (CR 510.1 / 510.2). -/
  assignedCombatDamage : Array CreatureCombatAssignment := #[]
  /-- Defending players who still must declare blockers, in APNAP order
  (CR 509.1 / 802). -/
  blockersQueue : Array PlayerId := #[]
  /-- True after a first-strike combat damage step has been dealt this combat
  (CR 702.7b). Cleared when combat ends. -/
  firstStrikeDamageDone : Bool := false
  /-- After first-strike damage, a regular combat damage step is still pending
  (CR 702.7b). -/
  pendingRegularCombatDamage : Bool := false
  /-- Creatures that assigned first-strike combat damage this combat. They
  assign regular damage only if they have double strike (Okoye; MSH 173). -/
  firstStrikeAssignedThisCombat : Array ObjectId := #[]
  /-- Extra combat phases still to begin after the current combat (Hulk enrage). -/
  additionalCombatPhases : Nat := 0
  /-- Enrage triggers that will grant an additional combat when they resolve. -/
  enrageGrantsAdditionalCombat : Nat := 0
deriving Repr, Inhabited, BEq

/-- State for a pending `TriggerResolution.mayThen` ("you may ... If you do, ...")
branch in a trigger sequence (CR 603.3 / CR 608.2c). -/
structure MayThenState where
  /-- Flattened steps of the `mayThen` conditional waiting in
  `triggerSequenceRest`. Declining the optional action drops this many. -/
  drop : Nat := 0
  /-- After an optional `mayThen` action cannot be performed, the sequence
  fold skips this many following steps. -/
  skip : Nat := 0
  /-- Conditional of the `mayThen` currently offered. The optional action
  reads it for its log and which choice to open. -/
  conditional : Option TriggeredAbility.TriggerResolution := none
  /-- An artifact-or-discard cost accepted a `mayThen`. The action handler
  resumes the conditional. -/
  resume : Bool := false
deriving Repr, Inhabited

/-- Follow-up actions after a pending scry or surveil completes (CR 701.18 / CR 701.42). -/
structure AfterScrySurveil where
  /-- Draw these cards after the current scry finishes (e.g. Hithlain Knots). -/
  pendingDrawAfterScry : Option (PlayerId × Nat) := none
  /-- After Palantír of Orthanc finishes scrying, this opponent may have
  the controller draw. Stores controller, opponent, and the Palantír. -/
  palantirAfterScry : Option (PlayerId × PlayerId × ObjectId) := none
  /-- Work left after the pending scry or surveil finishes (Eye of Jace):
  its controller, source, and what to do. -/
  fraAfterLook : Option (PlayerId × Option ObjectId × Resolution) := none
  /-- The following `surveil` returns a card with mana value at most the life
  gained this turn (ruling 750). -/
  armSurveilReturn : Bool := false
  /-- After the pending surveil, a card with mana value at most this put into
  the graveyard goes to its owner's hand (Enlightened Confidant). -/
  surveilReturnMvAtMost : Option Nat := none
  /-- A noncreature, nonland card put into the graveyard by the pending
  surveil goes to its owner's hand (Chandra, Chill of Compliance). -/
  surveilReturnNoncreatureNonland : Bool := false
deriving Repr, Inhabited

/-- Multi-card or conditional discard requirement in progress (CR 701.8). -/
structure DiscardRequirement where
  /-- Remaining discards for Thirst for Knowledge (MSH 344). An artifact
  card finishes the requirement early. -/
  thirstDiscardsLeft : Nat := 0
  /-- Discarding a card of this type finishes `thirstDiscardsLeft` early. -/
  thirstDiscardType : CardType := .artifact
  /-- Remaining discards for a required multi-card discard such as “discard
  two cards”. Unlike `thirstDiscardsLeft`, an artifact does not end this
  early. -/
  pendingDiscardsLeft : Nat := 0
  /-- Put a +1/+1 counter on this permanent after the current discard choices
  finish (Ninja of the Hand). -/
  plusOneAfterDiscards : Option ObjectId := none
deriving Repr, Inhabited, BEq

/-- Simultaneous zone-change batch state for replacement effects and batch triggers
(CR 614.6 / CR 603.2c). -/
structure BatchMoveState where
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
deriving Repr, Inhabited

/-- Most recent event parameters read by triggered abilities ("that player",
"that much", "that creature", CR 603.2 / CR 608.2c). -/
structure LastTriggerEvent where
  /-- Player most recently dealt combat damage by a creature whose
  combat-damage trigger is resolving (Cavern-Hoard Dragon). -/
  lastCombatDamagePlayer : Option PlayerId := none
  /-- Most recent life loss amount, for “mills that many” triggers. -/
  lastLifeLost : Option (PlayerId × Nat) := none
  /-- Most recent noncombat damage marked on a permanent. -/
  lastNoncombatDamage : Option (ObjectId × Nat) := none
  /-- Most recent creature that became tapped (Captain America, Living Legend). -/
  lastBecameTapped : Option ObjectId := none
  /-- Most recent attacking creature that died (new GY object id; Ares). -/
  lastDiedAttacker : Option ObjectId := none
deriving Repr, Inhabited, BEq

/-- Extra turns and player-control effects (CR 500.7 / CR 720). -/
structure TurnControlState where
  /-- Extra turns to take before the next player in turn order (Kang). -/
  extraTurns : Array PlayerId := #[]
  /-- Power-up abilities can't be activated during this extra turn (Kang). -/
  powerUpsForbidden : Bool := false
  /-- Player-controlling effect: (you, the player you control). Last created
  wins (MSH 259). -/
  playerControl : Option (PlayerId × PlayerId) := none
  /-- If the controlled player skips their next turn, control applies to the
  next turn they actually take (MSH 221). -/
  controlOnNextTakenTurn : Bool := false
deriving Repr, Inhabited, BEq

/-- Numeric counts recorded across sequential resolution steps (CR 608.2c). -/
structure ResolutionCountNotes where
  /-- Humans chosen for the current “tap any number of Humans” step.
  `.draw (amount := .forEachTappedHuman)` draws this many cards. -/
  humansTappedThisWay : Nat := 0
  /-- Permanents destroyed by `.destroy .oppArtifactsEnchantments (note := .countDestroyed)`.
  `.gainLife .forEachDestroyedThisWay` gains this much life. -/
  permanentsDestroyedThisWay : Nat := 0
  /-- Ordinal recorded by the current `noteResolveThisTurn` step.
  `«if» (.nthResolve _)` reads it and a finished sequence clears it. -/
  nthResolveThisWay : Option Nat := none
  /-- Excess damage noted by `dealDamage` with `.excess` for the following
  amass step. -/
  excessDamageThisWay : Nat := 0
  /-- Cards discarded by accepting `.discard .hand`. `none` means declined. -/
  handDiscardedThisWay : Option Nat := none
  /-- A count captured before a later step could change it (invasion counters,
  cards discarded). -/
  notedCountThisWay : Nat := 0
  /-- Power of the creature sacrificed for
  `putCounters .plusOneSacrificedPower`. -/
  sacrificedPowerThisWay : Option Nat := none
deriving Repr, Inhabited, BEq

/-- Boolean step-outcome flags recorded across sequential resolution steps (CR 608.2c). -/
structure ResolutionFlagNotes where
  /-- A hope counter was removed by the current `removeCounters .hope .source` step.
  `«if» .removedHope` draws a card when this is set. -/
  removedHopeThisWay : Bool := false
  /-- A permanent was returned to its owner's hand by the current
  `returnToHand` step when it notes `.returnedPermanent`.
  `«if» .returnedPermanent` puts a +1/+1 counter on the source when this is set. -/
  returnedPermanentThisWay : Bool := false
  /-- The current sequence step asked the rest of the sequence not to run
  (the source had already left, or no mana was spent). -/
  skipTriggerSequenceRest : Bool := false
  /-- `.mill` noted `.opponentsMilled`: an opponent milled at least one card. -/
  opponentsMilledThisWay : Bool := false
  /-- `sacrifice .you .plan .forReflexive` sacrificed the Plan. -/
  planWasSacrificed : Bool := false
  /-- `sacrifice .you .source .noted` sacrificed the source. -/
  sourceWasSacrificed : Bool := false
deriving Repr, Inhabited, BEq

/-- Amass, Palantír, and impulse-cast cross-step resolution notes (CR 608.2c / CR 701.47). -/
structure ResolutionAmassAndImpulseNotes where
  /-- `.destroy .target (note := .forAmass)` chose a legal target. The controller,
  amount, and whether you controlled it feed the following amass and draw steps. -/
  destroyedForAmassThisWay : Bool := false
  amassControllerThisWay : Option PlayerId := none
  amassAmountThisWay : Nat := 0
  amassYouControlledThisWay : Bool := false
  /-- Palantír finished putting an influence counter; the following step offers
  the opponent's draw choice. Controller, opponent, and the Palantír. -/
  palantirChoiceReady : Option (PlayerId × PlayerId × ObjectId) := none
  /-- `revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`
  stored the impulse. The following `.mayCast .impulse` offers the cast. -/
  grimaImpulseReady : Bool := false
  grimaImpulseVictim : Option PlayerId := none
  grimaImpulseFound : Option ObjectId := none
  grimaImpulseOthers : Array ObjectId := #[]
deriving Repr, Inhabited, BEq

/-- Objects and card lists noted across sequential resolution steps ("that card", "those cards", CR 608.2c / CR 608.2h). -/
structure ResolutionObjectNotes where
  /-- Card discarded while a later `.put .discardedLand (how := .tapped)`
  may put that land onto the battlefield tapped (Silvan Reveler). The
  player who discarded it, and the card. -/
  discardedCardThisWay : Option (PlayerId × ObjectId) := none
  /-- The permanent marked by the current `dealDamage` step when it notes
  `.markedPermanent`. `«if» (.dealtDamageToSubtype _)` destroys it when it
  has the subtype. -/
  permanentDealtDamageThisWay : Option ObjectId := none
  /-- Cards milled by `.mill` when it notes `.milledCards`. -/
  milledIdsThisWay : Array ObjectId := #[]
  /-- Cards `revealLibrary` just showed. A following step reads them. -/
  revealedIdsThisWay : Array ObjectId := #[]
  /-- Lands exiled by `exile .landsYouControl .forLater .lands`.
  `.put .notedLands (how := .tapped)` returns them. -/
  exiledIdsThisWay : Array ObjectId := #[]
  /-- Creature exiled by `exile .target .untilSourceLeaves .copyAndHost`, copied by the next step.
  The object is the one from before it moved. -/
  notedCopyObject : Option GameObject := none
  notedHostId : Option ObjectId := none
  /-- Source of the Balin ability, for the damage step after the discard. -/
  notedSourceThisWay : Option ObjectId := none
  /-- Creature that received Equipment from `attach .anyYouControl .target`. -/
  equipmentAttachedHost : Option ObjectId := none
  /-- Token created for the following attach or counter step. -/
  createdTokenThisWay : Option ObjectId := none
  /-- Artifact put from hand by `.put .artifactFromHand (note := .forAttach)`,
  and the creature `attach .putArtifact .notedHost` attaches it to when it
  is Equipment. -/
  putArtifactThisWay : Option (ObjectId × ObjectId) := none
  /-- Card exiled by `exile .graveyardCard .forLater .playCard`. -/
  playExiledThisWay : Option ObjectId := none
deriving Repr, Inhabited

/-- Cross-step resolution notes ("this way", "that card", "those cards", CR 608.2c / CR 608.2h). -/
structure ResolutionNotes extends
    ResolutionCountNotes,
    ResolutionFlagNotes,
    ResolutionAmassAndImpulseNotes,
    ResolutionObjectNotes where
deriving Repr, Inhabited

/-- Game-wide per-turn and until-end-of-turn state cleared during cleanup or
as the turn ends (CR 514.2 / CR 514.3). -/
structure GameTurnState where
  /-- Until-end-of-turn continuous effect: creatures without flying can't
  block (e.g. Fire of Orthanc). Cleared in cleanup (CR 514.2 / 611.2a). -/
  creaturesWithoutFlyingCantBlock : Bool := false
  /-- Until EOT, this player's creatures with toughness greater than power
  assign combat damage equal to toughness (The Kingpin of Crime; MSH 287). -/
  assignCombatDamageEqualToughness : Option PlayerId := none
  /-- A creature went to a graveyard from the battlefield this turn
  (used by cost reductions such as Dreaded Bat-Cloud). Cleared as the turn ends. -/
  creatureDiedThisTurn : Bool := false
  /-- Creatures that died this turn, tokens included. -/
  creatureDeathsThisTurn : Nat := 0
  /-- Creature cards that went from the battlefield to a graveyard this turn
  (Supper for Spiders). Cleared as the turn ends. -/
  battlefieldCreaturesToGyThisTurn : Array ObjectId := #[]
  /-- The Sensational She-Hulk chose to deal damage this turn (MSH 95 / 142). -/
  sheHulkDamageUsedThisTurn : Bool := false
  /-- World War Hulk chapter I: the next red or green creature spell this
  player casts this turn may be cast without paying its mana cost (MSH 343). -/
  pendingFreeRGCreature : Option PlayerId := none
deriving Repr, Inhabited, BEq, DecidableEq

/-- Turn-order, active-player, priority, step, and day/night state
(CR 103.2 / CR 117 / CR 500–514 / CR 702.145). -/
structure GameTurnOrderState where
  activePlayer : PlayerId := ⟨0⟩
  priority : PlayerId := ⟨0⟩
  step : Step := .untap
  turnNumber : Nat := 1
  startingPlayer : PlayerId := ⟨0⟩
  isFirstTurn : Bool := true
  consecutivePasses : Nat := 0
  /-- Set when CR 514.3a grants priority during the current cleanup step. -/
  cleanupGivesPriority : Bool := false
  /-- It is night (CR 702.145). Used by Nick Fury / daybound (MSH 191). -/
  isNight : Bool := false
deriving Repr, Inhabited, BEq, DecidableEq

/-- Active resolution and pending-choice continuation state for spells and
abilities (CR 603.3 / CR 608.2). -/
structure GameContinuationState where
  /-- Continuation after a `--norandom` result is applied. -/
  afterRandom : AfterRandom := .none
  /-- Follow-up actions after a pending scry or surveil completes (CR 701.18 / CR 701.42). -/
  afterScrySurveil : AfterScrySurveil := {}
  /-- The spell whose effect is currently resolving (CR 608.2). -/
  resolvingSpell : Option ObjectId := none
  /-- The activated or triggered ability currently resolving. -/
  resolvingAbility : Option ObjectId := none
  /-- Damage assigned to each target of the resolving divided-damage ability
  (CR 601.2d). -/
  resolvingDivision : Array Nat := #[]
  /-- Copies a player may still cast without paying their mana costs as an
  ability resolves, with the mana value left (Uldaros Theorix). -/
  pendingFreeCopies : Option (PlayerId × Array ObjectId × Nat × Nat) := none
  /-- Spells exiled by a resolving ability that may still be cast without
  paying their mana costs, and how many casts remain (Doom Reigns Supreme). -/
  pendingMayCastFromExile : Option (PlayerId × Array ObjectId × Nat) := none
  /-- Paying the pending “you may pay” cost also puts a +1/+1 counter on this
  permanent (Proft, Consulting Detective). -/
  mayPayAlsoPlusOneOn : Option ObjectId := none
  /-- Later steps of a trigger `sequence`, waiting on the pending choice an
  earlier step opened. -/
  triggerSequenceRest : Option TriggerSequenceRest := none
  /-- State for a pending `TriggerResolution.mayThen` branch (CR 603.3 / CR 608.2c). -/
  mayThen : MayThenState := {}
  /-- Pending `TriggerResolution.may` branch choice (CR 603.3 / 608.2c). -/
  triggerMayBranch : TriggerMayBranch := {}
  /-- Alternatives for a pending `TriggerResolution.or`. `chooseMode` applies
  that index. -/
  triggerOr : Option TriggerOrRest := none
  /-- Context for a pending Alliance or Gollum mode choice. `chooseMode`
  applies that index of `modes`. -/
  chooseModesRest : Option ChooseModesRest := none
  /-- Stashed effect for a pending `unlessPays` (CR 118.12 / 608.2c). -/
  unlessPays : UnlessPaysRest := {}
  /-- Stashed effect for a pending `SpellResolution.may` (CR 608.2c). -/
  mayEffectState : MayEffectRest := {}
  /-- Stashed alternatives for a pending `SpellResolution.or` (CR 608.2c). -/
  spellOrState : SpellOrRest := {}
  /-- Source of the current connive action, if any (MSH / CR 701.47). -/
  conniveSource : Option ObjectId := none
  /-- Multi-card or conditional discard requirement in progress (CR 701.8). -/
  discardReq : DiscardRequirement := {}
  /-- Follow-up action after a library search completes (CR 701.23). -/
  afterLibrarySearch : AfterLibrarySearch := .none
  /-- Ward payments still to announce after the current one (CR 702.21). -/
  wardQueue : Array WardObligation := #[]
deriving Repr, Inhabited

/-- Zone-change tracking, waiting/delayed triggers, and cross-step resolution
notes (CR 113.7a / CR 400.7 / CR 603.2 / CR 603.3 / CR 603.7 / CR 608.2h). -/
structure GameZoneBatchState where
  /-- Triggered abilities waiting to be put onto the stack the next time a
  player would receive priority (CR 603.3 / 603.3b). Distinguished by
  `WaitingTrigger.event`. -/
  waitingTriggers : Array WaitingTrigger := #[]
  /-- Cross-step resolution notes ("this way", CR 608.2c / CR 608.2h). -/
  thisWay : ResolutionNotes := {}
  /-- Last-known status of objects that left the battlefield, newest last
  (CR 113.7a / 608.2h). Only the most recent entries are kept. -/
  lastKnownStatus : Array (ObjectId × Status) := #[]
  /-- Where recently moved objects went (old id, new id), most recent last. -/
  movedTo : Array (ObjectId × ObjectId) := #[]
  /-- Tokens created by the most recent `createKindTokens` call, so a following
  sequence step can haste them or leave them out of a plus-one. -/
  recentTokenIds : Array ObjectId := #[]
  /-- Simultaneous zone-change batch state (CR 614.6 / CR 603.2c). -/
  batchMove : BatchMoveState := {}
  /-- Most recent event parameters read by triggered abilities (CR 603.2 / CR 608.2c). -/
  lastEvent : LastTriggerEvent := {}
  /-- True while a spell is being cast from the top of a library
  (Elven Chorus cannot show the new top until that finishes). -/
  castingFromTop : Bool := false
  /-- Delayed triggered abilities waiting to fire at the beginning of the next
  end step (CR 603.7). -/
  delayedEndStep : Array DelayedEndStepTrigger := #[]
  /-- Tokens created since enters triggers were last processed. -/
  pendingTokenEnters : Array ObjectId := #[]
  /-- Loki delayed copy: (controller, Loki's id if still known, last-known
  power). Compared at cast time (MSH 109). -/
  pendingLokiCopy : Option (PlayerId × Option ObjectId × Int) := none
  /-- Players who created one or more creature tokens since the last priority. -/
  pendingCreatureTokenCreators : Array PlayerId := #[]
  /-- Lands tapped for commander-identity mana that scries a matching creature. -/
  ancestryLandsTapped : Array ObjectId := #[]
deriving Repr, Inhabited

structure Game extends GameTurnOrderState, GameTurnState, GameContinuationState, GameZoneBatchState where
  players : Array Player
  objects : Array GameObject
  stack : Array StackEntry := #[]
  pending : Pending := .none
  nextObjectId : Nat := 0
  timestamp : Nat := 0
  rng : Rng := Rng.ofSeed 1
  /-- When true, random events become `Pending.resolveRandom` instead of
  using `rng`. -/
  norandom : Bool := false
  result : Option GameResult := none
  log : Array String := #[]
  format : Format := .constructed
  /-- CR 903.12 Brawl option (free first mulligan, CR 103.5c / 903.12g). -/
  brawl : Bool := false
  /-- Spell or ability proposed and waiting for mana abilities / payment
  (CR 601.2f–h / 602.2b). -/
  proposedSpell : Option ProposedSpell := none
  /-- Pre-game mulligan and opening-hand state (CR 103.5 / CR 103.6). -/
  mulligan : MulliganState := {}
  /-- Combat phase state (CR 508 / CR 509 / CR 510 / CR 702.7b). -/
  combat : CombatPhaseState := {}
  /-- Extra turns and player-control effects (CR 500.7 / CR 720). -/
  turnControl : TurnControlState := {}
deriving Repr, Inhabited

namespace Game

def awaitingOpeningBegin (g : Game) : Bool := g.mulligan.awaitingOpeningBegin
def mulliganToDeclare (g : Game) : Array PlayerId := g.mulligan.toDeclare
def willMulligan (g : Game) : Array PlayerId := g.mulligan.willMulligan
def mulliganToBottom (g : Game) : Array PlayerId := g.mulligan.toBottom

def discardedCardThisWay (g : Game) : Option (PlayerId × ObjectId) := g.thisWay.discardedCardThisWay
def humansTappedThisWay (g : Game) : Nat := g.thisWay.humansTappedThisWay
def permanentsDestroyedThisWay (g : Game) : Nat := g.thisWay.permanentsDestroyedThisWay
def removedHopeThisWay (g : Game) : Bool := g.thisWay.removedHopeThisWay
def permanentDealtDamageThisWay (g : Game) : Option ObjectId := g.thisWay.permanentDealtDamageThisWay
def returnedPermanentThisWay (g : Game) : Bool := g.thisWay.returnedPermanentThisWay
def nthResolveThisWay (g : Game) : Option Nat := g.thisWay.nthResolveThisWay
def skipTriggerSequenceRest (g : Game) : Bool := g.thisWay.skipTriggerSequenceRest
def excessDamageThisWay (g : Game) : Nat := g.thisWay.excessDamageThisWay
def destroyedForAmassThisWay (g : Game) : Bool := g.thisWay.destroyedForAmassThisWay
def amassControllerThisWay (g : Game) : Option PlayerId := g.thisWay.amassControllerThisWay
def amassAmountThisWay (g : Game) : Nat := g.thisWay.amassAmountThisWay
def amassYouControlledThisWay (g : Game) : Bool := g.thisWay.amassYouControlledThisWay
def milledIdsThisWay (g : Game) : Array ObjectId := g.thisWay.milledIdsThisWay
def revealedIdsThisWay (g : Game) : Array ObjectId := g.thisWay.revealedIdsThisWay
def opponentsMilledThisWay (g : Game) : Bool := g.thisWay.opponentsMilledThisWay
def palantirChoiceReady (g : Game) : Option (PlayerId × PlayerId × ObjectId) := g.thisWay.palantirChoiceReady
def grimaImpulseReady (g : Game) : Bool := g.thisWay.grimaImpulseReady
def grimaImpulseVictim (g : Game) : Option PlayerId := g.thisWay.grimaImpulseVictim
def grimaImpulseFound (g : Game) : Option ObjectId := g.thisWay.grimaImpulseFound
def grimaImpulseOthers (g : Game) : Array ObjectId := g.thisWay.grimaImpulseOthers
def planWasSacrificed (g : Game) : Bool := g.thisWay.planWasSacrificed
def sourceWasSacrificed (g : Game) : Bool := g.thisWay.sourceWasSacrificed
def exiledIdsThisWay (g : Game) : Array ObjectId := g.thisWay.exiledIdsThisWay
def notedCopyObject (g : Game) : Option GameObject := g.thisWay.notedCopyObject
def notedHostId (g : Game) : Option ObjectId := g.thisWay.notedHostId
def handDiscardedThisWay (g : Game) : Option Nat := g.thisWay.handDiscardedThisWay
def notedSourceThisWay (g : Game) : Option ObjectId := g.thisWay.notedSourceThisWay
def equipmentAttachedHost (g : Game) : Option ObjectId := g.thisWay.equipmentAttachedHost
def notedCountThisWay (g : Game) : Nat := g.thisWay.notedCountThisWay
def createdTokenThisWay (g : Game) : Option ObjectId := g.thisWay.createdTokenThisWay
def putArtifactThisWay (g : Game) : Option (ObjectId × ObjectId) := g.thisWay.putArtifactThisWay
def playExiledThisWay (g : Game) : Option ObjectId := g.thisWay.playExiledThisWay
def sacrificedPowerThisWay (g : Game) : Option Nat := g.thisWay.sacrificedPowerThisWay

def assignedCombatDamage (g : Game) : Array CreatureCombatAssignment := g.combat.assignedCombatDamage
def blockersQueue (g : Game) : Array PlayerId := g.combat.blockersQueue
def firstStrikeDamageDone (g : Game) : Bool := g.combat.firstStrikeDamageDone
def pendingRegularCombatDamage (g : Game) : Bool := g.combat.pendingRegularCombatDamage
def firstStrikeAssignedThisCombat (g : Game) : Array ObjectId := g.combat.firstStrikeAssignedThisCombat
def additionalCombatPhases (g : Game) : Nat := g.combat.additionalCombatPhases
def enrageGrantsAdditionalCombat (g : Game) : Nat := g.combat.enrageGrantsAdditionalCombat

def mayThenDrop (g : Game) : Nat := g.mayThen.drop
def mayThenSkip (g : Game) : Nat := g.mayThen.skip
def mayThenConditional (g : Game) : Option TriggeredAbility.TriggerResolution := g.mayThen.conditional
def mayThenResume (g : Game) : Bool := g.mayThen.resume

def pendingDrawAfterScry (g : Game) : Option (PlayerId × Nat) := g.afterScrySurveil.pendingDrawAfterScry
def palantirAfterScry (g : Game) : Option (PlayerId × PlayerId × ObjectId) := g.afterScrySurveil.palantirAfterScry
def fraAfterLook (g : Game) : Option (PlayerId × Option ObjectId × Resolution) := g.afterScrySurveil.fraAfterLook
def armSurveilReturn (g : Game) : Bool := g.afterScrySurveil.armSurveilReturn
def surveilReturnMvAtMost (g : Game) : Option Nat := g.afterScrySurveil.surveilReturnMvAtMost
def surveilReturnNoncreatureNonland (g : Game) : Bool := g.afterScrySurveil.surveilReturnNoncreatureNonland

def thirstDiscardsLeft (g : Game) : Nat := g.discardReq.thirstDiscardsLeft
def thirstDiscardType (g : Game) : CardType := g.discardReq.thirstDiscardType
def pendingDiscardsLeft (g : Game) : Nat := g.discardReq.pendingDiscardsLeft
def plusOneAfterDiscards (g : Game) : Option ObjectId := g.discardReq.plusOneAfterDiscards

def lockedDeathReplacements (g : Game) : Option (Array GameObject) := g.batchMove.lockedDeathReplacements
def suppressOthersDie (g : Game) : Bool := g.batchMove.suppressOthersDie
def suppressCreatureCardsToGy (g : Game) : Bool := g.batchMove.suppressCreatureCardsToGy

def lastCombatDamagePlayer (g : Game) : Option PlayerId := g.lastEvent.lastCombatDamagePlayer
def lastLifeLost (g : Game) : Option (PlayerId × Nat) := g.lastEvent.lastLifeLost
def lastNoncombatDamage (g : Game) : Option (ObjectId × Nat) := g.lastEvent.lastNoncombatDamage
def lastBecameTapped (g : Game) : Option ObjectId := g.lastEvent.lastBecameTapped
def lastDiedAttacker (g : Game) : Option ObjectId := g.lastEvent.lastDiedAttacker

def extraTurns (g : Game) : Array PlayerId := g.turnControl.extraTurns
def powerUpsForbidden (g : Game) : Bool := g.turnControl.powerUpsForbidden
def playerControl (g : Game) : Option (PlayerId × PlayerId) := g.turnControl.playerControl
def controlOnNextTakenTurn (g : Game) : Bool := g.turnControl.controlOnNextTakenTurn

def mayOnAccept (g : Game) : Option TriggeredAbility.TriggerResolution := g.triggerMayBranch.onAccept
def mayOnDecline (g : Game) : Option TriggeredAbility.TriggerResolution := g.triggerMayBranch.onDecline
def mayContext (g : Game) : Option TriggerSequenceRest := g.triggerMayBranch.context

def unlessPaysInstead (g : Game) : Option Effect := g.unlessPays.effect
def unlessPaysController (g : Game) : PlayerId := g.unlessPays.controller
def unlessPaysTargets (g : Game) : Array Target := g.unlessPays.targets
def unlessPaysDue (g : Game) : Bool := g.unlessPays.due

def mayEffect (g : Game) : Option Effect := g.mayEffectState.effect
def mayController (g : Game) : PlayerId := g.mayEffectState.controller
def mayTargets (g : Game) : Array Target := g.mayEffectState.targets

def spellOr (g : Game) : Array Effect := g.spellOrState.effects
def spellOrController (g : Game) : PlayerId := g.spellOrState.controller
def spellOrTargets (g : Game) : Array Target := g.spellOrState.targets
def spellOrLibrary (g : Game) : Bool := g.spellOrState.isLibrary

def delayedEndStepReturns (g : Game) : Array ObjectId :=
  g.delayedEndStep.filterMap fun
    | .returnExiled id => some id
    | _ => none

def delayedEndStepExiles (g : Game) : Array ObjectId :=
  g.delayedEndStep.filterMap fun
    | .exilePermanent id => some id
    | _ => none

def delayedEndStepSacrifices (g : Game) : Array ObjectId :=
  g.delayedEndStep.filterMap fun
    | .sacrificePermanent id => some id
    | _ => none

def delayedGraveReturns (g : Game) : Array (ObjectId × PlayerId) :=
  g.delayedEndStep.filterMap fun
    | .returnFromGraveyard id p => some (id, p)
    | _ => none

def delayedSynthetic (g : Game) : Array (PlayerId × Nat) :=
  g.delayedEndStep.filterMap fun
    | .syntheticDestiny p n => some (p, n)
    | _ => none

def plusOneAfterSearch (g : Game) : Option ObjectId :=
  match g.afterLibrarySearch with
  | .plusOneOn id => some id
  | _ => none

def untapSearchedIfLands (g : Game) : Option Nat :=
  match g.afterLibrarySearch with
  | .untapSearchedIfLands n => some n
  | _ => none

def logMsg (g : Game) (msg : String) : Game :=
  { g with log := g.log.push msg }

/-- Drop a stashed `unlessPays` effect. Paying, or countering for real,
clears it; leaving without paying sets `unlessPaysDue` instead. -/
def clearUnlessPays (g : Game) : Game :=
  { g with unlessPays := {} }

/-- Drop a stashed `SpellResolution.may` after the player accepts or declines. -/
def clearMay (g : Game) : Game :=
  { g with mayEffectState := {} }

/-- Drop a stashed `SpellResolution.or` after the player has chosen. -/
def clearSpellOr (g : Game) : Game :=
  { g with spellOrState := {} }

def over (g : Game) : Bool := g.result.isSome

def player (g : Game) (p : PlayerId) : Player :=
  g.players[p.idx]!

def setPlayer (g : Game) (pl : Player) : Game :=
  { g with players := g.players.set! pl.id.idx pl }

def modifyPlayer (g : Game) (p : PlayerId) (f : Player → Player) : Game :=
  g.setPlayer (f (g.player p))

/-- Set `p`'s life total and log `msg`. -/
def setLife (g : Game) (p : PlayerId) (life : Int) (msg : String) : Game :=
  let pl := g.player p
  if (pl.lifeLocked || pl.lifeCantChange) && life != pl.life then
    g.logMsg s!"{pl.name}'s life total can't change"
  else
    g.setPlayer { pl with life := life } |>.logMsg msg

/-- Remember that `p` created one or more creature tokens (CR 603.2c).
One instruction notes the player once. -/
def noteCreatureTokenEvent (g : Game) (p : PlayerId) : Game :=
  if (g.player p).lost || g.pendingCreatureTokenCreators.contains p then g
  else { g with pendingCreatureTokenCreators := g.pendingCreatureTokenCreators.push p }

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

def findObject? (g : Game) (id : ObjectId) : Option GameObject :=
  g.objects.find? (fun o => o.id == id)

def object! (g : Game) (id : ObjectId) : GameObject :=
  match g.findObject? id with
  | some o => o
  | none => panic! s!"missing object {id}"

def setObject (g : Game) (o : GameObject) : Game :=
  match g.objects.findIdx? (fun x => x.id == o.id) with
  | some i => { g with objects := g.objects.set! i o }
  | none => { g with objects := g.objects.push o }

/-- Update `o`'s status in place. -/
def mapObjectStatus (g : Game) (o : GameObject) (f : Status → Status) : Game :=
  g.setObject { o with status := f o.status }

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

/-- End a copy effect on `o`, restoring its original printed card (CR 707).
Does not cause the permanent to enter or leave the battlefield. -/
def restoreCopy (g : Game) (o : GameObject) : Game :=
  match o.copyRestore with
  | none => g
  | some card =>
    let copied := o.printed.name
    g.setObject { o with
      printed := card
      copyEffect := none }
    |>.logMsg s!"{card.name} is no longer a copy of {copied}"

/-- Restore copy effects on battlefield objects that satisfy `p`. -/
def restoreCopiesIf (g : Game) (p : GameObject → Bool) : Game :=
  g.battlefield.foldl (fun acc o => if p o then acc.restoreCopy o else acc) g

/-- Restore copy effects that last until end of turn. -/
def restoreCopiesUntilEot (g : Game) : Game :=
  g.restoreCopiesIf (·.copyUntilEot)

/-- Restore copy effects that last until `p`'s next turn. -/
def restoreCopiesUntilNextTurn (g : Game) (p : PlayerId) : Game :=
  g.restoreCopiesIf (fun o => o.copyUntilNextTurn && o.controller == some p)

/-- Restore copy effects that last until `srcId` leaves the battlefield. -/
def restoreCopiesUntilSourceLeaves (g : Game) (srcId : ObjectId) : Game :=
  g.restoreCopiesIf (fun o => o.copyUntilSourceLeaves == some srcId)

/-- Restore control-changing effects that last until `srcId` leaves
(Super Hero Civil War; MSH 143). -/
def restoreControlUntilSourceLeaves (g : Game) (srcId : ObjectId) : Game :=
  g.battlefield.foldl (fun acc o =>
    if o.controlUntilSourceLeaves == some srcId then
      let p := o.defaultController.getD o.owner
      if (acc.player p).lost then
        acc.logMsg s!"{o.name} does not change control (CR 800.4b)"
      else
        acc.setObject { o with
          controller := some p
          controlChanged := false
          controlUntilSourceLeaves := none }
          |>.logMsg s!"{o.name} returns to {(acc.player p).name}'s control"
    else acc) g

/-- Equipment attached to `o` (Whiplash last-known X). -/
def attachedEquipmentCount (g : Game) (o : GameObject) : Nat :=
  g.battlefield.filter (fun eq =>
    eq.printed.isEquipment && eq.attachedTo == some o.id) |>.size

/-- Last player-controlling effect wins (MSH 259). The controlled player
remains the active player on their turn (MSH 300) and still controls their
permanents (MSH 358). -/
def setPlayerControl (g : Game) (you them : PlayerId) : Game :=
  let g :=
    { g with turnControl := { g.turnControl with
      playerControl := some (you, them), controlOnNextTakenTurn := false } }
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

/-- The object a moved object became, following zone changes (CR 400.7). -/
partial def followMoved (g : Game) (id : ObjectId) : ObjectId :=
  match g.movedTo.reverse.find? (·.1 == id) with
  | some (_, next) => if next == id then id else g.followMoved next
  | none => id

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
