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
  openBatchEffects : Array (EffectId × ContinuousEffectSpec) := #[]
  openBatchPending : Pending := .none
  /-- Active continuous effects paired with their unique `EffectId` (CR 611). -/
  activeEffects : Array (EffectId × ContinuousEffectSpec) := #[]
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
  /-- Stack of mid-resolution continuation frames (CR 608.2). Top of stack
  is `continuations.back?.getD {}`. -/
  continuations : Array ContinuationFrame := #[]
  /-- The spell whose effect is currently resolving (CR 608.2). -/
  resolvingSpell : Option ObjectId := none
  /-- The activated or triggered ability currently resolving. -/
  resolvingAbility : Option ObjectId := none
  /-- Ordered `ReplacementId` preferences supplied by players via `chooseReplacement`
  (CR 616.1); consulted by the replacement/prevention loop when multiple
  candidates tie in the lowest applicable priority tier (CR 616.1a–e). -/
  replacementOrder : Array ReplacementId := #[]
  /-- True while a spell is being cast from the top of a library
  (Elven Chorus cannot show the new top until that finishes). -/
  castingFromTop : Bool := false
  /-- Delayed triggered abilities waiting for their trigger condition (CR 603.7). -/
  delayedTriggers : Array DelayedTrigger := #[]
  /-- Extra turns to take before the next player in turn order (Kang). -/
  extraTurns : Array PlayerId := #[]
  /-- Extra combat phases still to begin after the current combat (Hulk enrage). -/
  additionalCombatPhases : Nat := 0
  /-- Damage assigned to each target of the resolving divided-damage ability
(CR 601.2d). -/
  resolvingDivision : Array Nat := #[]
  /-- Ward payments still to announce after the current one (CR 702.21). -/
  wardQueue : Array WardObligation := #[]
  /-- Lands tapped for commander-identity mana that scries a matching creature. -/
  ancestryLandsTapped : Array ObjectId := #[]
  /-- State changes that happened this game, oldest first (CR 603.2 / 614.1).
  Conditions ask this log whether an action happened. Triggers and
  replacement effects match the same events. A replaced change is not
  recorded (CR 614.6). -/
  events : Array GameEvent := #[]
deriving Repr, Inhabited

/-- Pre-batch game state snapshot for CR 603.10 look-back trigger evaluation. -/
abbrev GameSnapshot := Game

namespace Game

/-- Top continuation frame, or `{}` when no frame has been pushed yet. -/
@[inline] def topFrame (g : Game) : ContinuationFrame :=
  g.continuations.back?.getD {}

/-- Update the top continuation frame, creating one if `g.continuations` is empty. -/
@[inline] def modifyTopFrame (g : Game) (f : ContinuationFrame → ContinuationFrame) : Game :=
  match g.continuations.back? with
  | none => { g with continuations := #[f {}] }
  | some top => { g with continuations := g.continuations.pop.push (f top) }

@[inline] def pendingDrawAfterScry (g : Game) := g.topFrame.pendingDrawAfterScry
@[inline] def discardedCardThisWay (g : Game) := g.topFrame.discardedCardThisWay
@[inline] def palantirAfterScry (g : Game) := g.topFrame.palantirAfterScry
@[inline] def recentTokenIds (g : Game) := g.topFrame.recentTokenIds
@[inline] def fraAfterLook (g : Game) := g.topFrame.fraAfterLook
@[inline] def pendingFreeCopies (g : Game) := g.topFrame.pendingFreeCopies
@[inline] def pendingMayCastFromExile (g : Game) := g.topFrame.pendingMayCastFromExile
@[inline] def mayPayAlsoPlusOneOn (g : Game) := g.topFrame.mayPayAlsoPlusOneOn
@[inline] def humansTappedThisWay (g : Game) := g.topFrame.humansTappedThisWay
@[inline] def permanentsDestroyedThisWay (g : Game) := g.topFrame.permanentsDestroyedThisWay
@[inline] def removedHopeThisWay (g : Game) := g.topFrame.removedHopeThisWay
@[inline] def permanentDealtDamageThisWay (g : Game) := g.topFrame.permanentDealtDamageThisWay
@[inline] def returnedPermanentThisWay (g : Game) := g.topFrame.returnedPermanentThisWay
@[inline] def nthResolveThisWay (g : Game) := g.topFrame.nthResolveThisWay
@[inline] def skipTriggerSequenceRest (g : Game) := g.topFrame.skipTriggerSequenceRest
@[inline] def excessDamageThisWay (g : Game) := g.topFrame.excessDamageThisWay
@[inline] def destroyedForAmassThisWay (g : Game) := g.topFrame.destroyedForAmassThisWay
@[inline] def amassControllerThisWay (g : Game) := g.topFrame.amassControllerThisWay
@[inline] def amassAmountThisWay (g : Game) := g.topFrame.amassAmountThisWay
@[inline] def amassYouControlledThisWay (g : Game) := g.topFrame.amassYouControlledThisWay
@[inline] def milledIdsThisWay (g : Game) := g.topFrame.milledIdsThisWay
@[inline] def revealedIdsThisWay (g : Game) := g.topFrame.revealedIdsThisWay
@[inline] def opponentsMilledThisWay (g : Game) := g.topFrame.opponentsMilledThisWay
@[inline] def palantirChoiceReady (g : Game) := g.topFrame.palantirChoiceReady
@[inline] def grimaImpulseReady (g : Game) := g.topFrame.grimaImpulseReady
@[inline] def grimaImpulseVictim (g : Game) := g.topFrame.grimaImpulseVictim
@[inline] def grimaImpulseFound (g : Game) := g.topFrame.grimaImpulseFound
@[inline] def grimaImpulseOthers (g : Game) := g.topFrame.grimaImpulseOthers
@[inline] def planWasSacrificed (g : Game) := g.topFrame.planWasSacrificed
@[inline] def sourceWasSacrificed (g : Game) := g.topFrame.sourceWasSacrificed
@[inline] def exiledIdsThisWay (g : Game) := g.topFrame.exiledIdsThisWay
@[inline] def notedCopyObject (g : Game) := g.topFrame.notedCopyObject
@[inline] def notedHostId (g : Game) := g.topFrame.notedHostId
@[inline] def handDiscardedThisWay (g : Game) := g.topFrame.handDiscardedThisWay
@[inline] def notedSourceThisWay (g : Game) := g.topFrame.notedSourceThisWay
@[inline] def equipmentAttachedHost (g : Game) := g.topFrame.equipmentAttachedHost
@[inline] def notedCountThisWay (g : Game) := g.topFrame.notedCountThisWay
@[inline] def createdTokenThisWay (g : Game) := g.topFrame.createdTokenThisWay
@[inline] def putArtifactThisWay (g : Game) := g.topFrame.putArtifactThisWay
@[inline] def playExiledThisWay (g : Game) := g.topFrame.playExiledThisWay
@[inline] def armSurveilReturn (g : Game) := g.topFrame.armSurveilReturn
@[inline] def triggerSequenceRest (g : Game) := g.topFrame.triggerSequenceRest
@[inline] def mayThenDrop (g : Game) := g.topFrame.mayThenDrop
@[inline] def mayThenSkip (g : Game) := g.topFrame.mayThenSkip
@[inline] def mayThenConditional (g : Game) := g.topFrame.mayThenConditional
@[inline] def mayOnAccept (g : Game) := g.topFrame.mayOnAccept
@[inline] def mayOnDecline (g : Game) := g.topFrame.mayOnDecline
@[inline] def mayContext (g : Game) := g.topFrame.mayContext
@[inline] def sacrificedPowerThisWay (g : Game) := g.topFrame.sacrificedPowerThisWay
@[inline] def mayThenResume (g : Game) := g.topFrame.mayThenResume
@[inline] def triggerOr (g : Game) := g.topFrame.triggerOr
@[inline] def chooseModesRest (g : Game) := g.topFrame.chooseModesRest
@[inline] def unlessPaysInstead (g : Game) := g.topFrame.unlessPaysInstead
@[inline] def unlessPaysController (g : Game) := g.topFrame.unlessPaysController
@[inline] def unlessPaysTargets (g : Game) := g.topFrame.unlessPaysTargets
@[inline] def unlessPaysDue (g : Game) := g.topFrame.unlessPaysDue
@[inline] def mayEffect (g : Game) := g.topFrame.mayEffect
@[inline] def mayController (g : Game) := g.topFrame.mayController
@[inline] def mayTargets (g : Game) := g.topFrame.mayTargets
@[inline] def spellOr (g : Game) := g.topFrame.spellOr
@[inline] def spellOrController (g : Game) := g.topFrame.spellOrController
@[inline] def spellOrTargets (g : Game) := g.topFrame.spellOrTargets
@[inline] def spellOrLibrary (g : Game) := g.topFrame.spellOrLibrary
@[inline] def surveilReturnMvAtMost (g : Game) := g.topFrame.surveilReturnMvAtMost
@[inline] def surveilReturnNoncreatureNonland (g : Game) := g.topFrame.surveilReturnNoncreatureNonland
@[inline] def pendingReplacement (g : Game) := g.topFrame.pendingReplacement
@[inline] def conniveSource (g : Game) := g.topFrame.conniveSource
@[inline] def plusOneAfterDiscards (g : Game) := g.topFrame.plusOneAfterDiscards
@[inline] def plusOneAfterSearch (g : Game) := g.topFrame.plusOneAfterSearch
@[inline] def thirstDiscardsLeft (g : Game) := g.topFrame.thirstDiscardsLeft
@[inline] def thirstDiscardType (g : Game) := g.topFrame.thirstDiscardType
@[inline] def pendingDiscardsLeft (g : Game) := g.topFrame.pendingDiscardsLeft
@[inline] def untapSearchedIfLands (g : Game) := g.topFrame.untapSearchedIfLands
@[inline] def resolvingContext (g : Game) := g.topFrame.resolvingContext
@[inline] def stashedCause (g : Game) := g.topFrame.stashedCause

end Game

namespace Status

/-- Apply one `CounterDelta` of `kind` directly to `s` (CR 122.1). -/
def applyCounterDelta (s : Status) (kind : CounterKind) (delta : CounterDelta) : Status :=
  match delta with
  | .put n =>
    { s with counters := s.counters.add kind n }
  | .removed n =>
    { s with counters := s.counters.sub kind n }

/-- Apply one `StatusChange` in isolation (CR 110.5). -/
def applyChange (s : Status) (c : StatusChange) : Status :=
  match c with
  | .set s' => s'
  | .reset => {}
  | .tapped v => { s with tapped := v }
  | .damage v => { s with damage := v }
  | .summoningSick v => { s with summoningSick := v }
  | .phasedOut v => { s with phasedOut := v }
  | .phasedWith v => { s with phasedWith := v }
  | .transformed v => { s with transformed := v }
  | .chosenOdd v => { s with chosenOdd := v }
  | .chosenCreatureType v => { s with chosenCreatureType := v }
  | .chosenColor v => { s with chosenColor := v }
  | .chosenName v => { s with chosenName := v }
  | .faceDown v => { s with faceDown := v }
  | .windcragMardu v => { s with windcragMardu := v }
  | .chosenCardType v => { s with chosenCardType := v }

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
  | .defaultController v => { o with defaultController := v }
  | .zone v => { o with zone := v }
  | .timestamp v => { o with timestamp := v }
  | .abilityEffect v => { o with abilityEffect := v }
  | .triggeredAbility v => { o with triggeredAbility := v }
  | .reflexiveResolution v => { o with reflexiveResolution := v }
  | .sourceId v => { o with sourceId := v }
  | .attachedTo v => { o with attachedTo := v }
  | .adventurerCard v => { o with adventurerCard := v }
  | .linkedExile v => { o with linkedExile := v }
  | .pushLinkedExile id => { o with linkedExile := o.linkedExile.push id }
  | .returnToZone v => { o with returnToZone := v }
  | .leaveTriggerExile v => { o with leaveTriggerExile := v }
  | .pushLeaveTriggerExile id => { o with leaveTriggerExile := o.leaveTriggerExile.push id }
  | .fraCauseId v => { o with fraCauseId := v }
  | .fraCauseController v => { o with fraCauseController := v }
  | .fraCausePower v => { o with fraCausePower := v }
  | .fraCauseStatus v => { o with fraCauseStatus := v }
  | .exiledBy v => { o with exiledBy := v }
  | .isCopy v => { o with isCopy := v }
  | .chosenX v => { o with chosenX := v }

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
  | .poison v => { pl with poison := v }
  | .addPoison n => { pl with poison := pl.poison + n }
  | .lost v => { pl with lost := v }
  | .leftTheGame v => { pl with leftTheGame := v }
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
  | .sideboard v => { pl with sideboard := v }
  | .removeSideboardAt idx => { pl with sideboard := pl.sideboard.eraseIdx! idx }
  | .teammate v => { pl with teammate := v }
  | .isMonarch v => { pl with isMonarch := v }
  | .commanderCreatureTypes v => { pl with commanderCreatureTypes := v }

end Player

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
def lastActive? {α : Type} (g : Game) (f : ContinuousEffectSpec → Option α) : Option α :=
  g.activeEffects.foldl (fun acc (_, e) =>
    match f e with
    | some v => some v
    | none => acc) none

/-- Whether an active continuous effect has exactly the payload `eff`. -/
def hasActiveEffect (g : Game) (eff : ContinuousEffectSpec) : Bool :=
  g.activeEffects.any (fun (_, e) => e == eff)

/-- Effective controller of `o` under `g.activeEffects` (CR 613.1b / 613.7 /
800.4a). -/
def effectiveController? (g : Game) (o : GameObject) : Option PlayerId :=
  let ctrl? := g.lastActive? (fun
    | .layered (.objects #[oid]) (.control c) _ => if oid == o.id then some c else none
    | _ => none)
  match ctrl? with
  | some c => some c
  | none =>
    let p := o.defaultController.getD o.owner
    if !(g.players[p.idx]!).lost then some p else o.controller

/-- Original printed `CardDef` before any active Layer 1 `.copy` effect on `id`
(CR 613.1a / 707). -/
def copyRestoreOf? (g : Game) (id : ObjectId) : Option CardDef :=
  g.activeEffects.findSome? fun (_, e) =>
    match e with
    | .layered (.objects #[oid]) (.copy _ r) _ =>
      if oid == id then r else none
    | _ => none

/-- Recompute `id`'s copied characteristics from the active `.copy` continuous
effects on `id` (CR 611 / 613.7 / 707), restoring the original printed card when
none remain. -/
def recomputeCopy (g : Game) (id : ObjectId) (fallbackRestore : Option CardDef := none) : Game :=
  let latest? := g.lastActive? (fun
    | .layered (.objects #[oid]) (.copy printed r) _ =>
      if oid == id then some (printed, r) else none
    | _ => none)
  g.modifyObject id (fun o =>
    match latest? with
    | some (printed, _) => { o with printed := printed }
    | none =>
      match fallbackRestore with
      | some card => { o with printed := card }
      | none => o)

/-- Apply one `ContinuousEffectEvent` in isolation (CR 611). -/
def applyContinuousEffectEvent (g : Game) (e : ContinuousEffectEvent) : Game :=
  match e with
  | .created effectId spec =>
    let g :=
      { g with
        nextEffectId := max g.nextEffectId (effectId.raw + 1)
        activeEffects := g.activeEffects.push (effectId, spec) }
    match spec with
    | .layered (.objects #[id]) (.copy _ restore) _ => g.recomputeCopy id restore
    | _ => g
  | .expired effectId =>
    match g.activeEffects.findIdx? (·.1 == effectId) with
    | none => g
    | some idx =>
      let stored := g.activeEffects[idx]!.2
      let g :=
        { g with
          nextEffectId := max g.nextEffectId (effectId.raw + 1)
          activeEffects := g.activeEffects.eraseIdx! idx }
      match stored with
      | .layered (.objects #[id]) (.copy _ restore) _ => g.recomputeCopy id restore
      | .gameRule (.fraEmblem id) _ => { g with objects := g.objects.filter (·.id != id) }
      | _ => g

/-- Apply one `PermanentEvent` in isolation (CR 110.5, 122, 701.3, 701.26). -/
def applyPermanentEvent (g : Game) (e : PermanentEvent) : Game :=
  let findEventIdx? (object : EventObject) : Option Nat :=
    object.id.bind (fun id => g.objects.findIdx? (·.id == id))
  match e with
  | .tapped object _ =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let s := { o.status with tapped := true }
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
  | .controlChanged object _ toPlayer =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with controller := some toPlayer } }
    | none => g
  | .designation object d gained =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let (g, s) :=
        match d with
        | .ringBearer =>
          let g :=
            match o.controller with
            | some c =>
              if gained then
                g.modifyPlayer c (fun pl => { pl with ringBearerId := some o.id })
              else
                g.modifyPlayer c (fun pl =>
                  if pl.ringBearerId == some o.id then { pl with ringBearerId := none } else pl)
            | none => g
          (g, { o.status with ringBearer := gained })
        | .commander => (g, { o.status with isCommander := gained })
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
          (g, { o.status with goaded := !goadedBy.isEmpty, goadedBy, goadedUntilNextTurnOf })
        | .prepared => (g, { o.status with prepared := gained })
        | .harnessed => (g, { o.status with harnessed := gained })
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
      let s := { o.status with damage := o.status.damage + (amount : Int) }
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
                    damage := 0 } } }
      | none => acc) g

/-- Apply one `LifeEvent` in isolation (CR 119.2 / 119.3). -/
def applyLifeEvent (g : Game) (e : LifeEvent) : Game :=
  let locked (p : PlayerId) : Bool :=
    g.activeEffects.any fun (_, s) =>
      match s with
      | .playerRule q .lifeLocked _ | .playerRule q .lifeCantChange _ => q == p
      | _ => false
  match e with
  | .gained p amount =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      if locked p then g
      else { g with players := g.players.set! p.idx { pl with life := pl.life + (amount : Int) } }
    else g
  | .lost p amount _ _ =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      if locked p then g
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
  | .moved before after fromZone toZone _ _ entersWith libPos =>
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
            transformed := after.transformed }
        else {}
      let status :=
        if mergedCounters.isEmpty then baseStatus
        else baseStatus.withCounterBag mergedCounters
      let chosenX : Option Nat :=
        if toZone == .stack then after.chosenX.orElse (fun _ => existing?.bind (·.chosenX))
        else none
      { id := newId
        printed := printed
        owner := after.owner
        controller :=
          if toZone == .battlefield || toZone == .stack || after.printed.isSome then after.controller
          else none
        defaultController := if toZone == .battlefield then after.controller else none
        zone := toZone
        status := status
        timestamp := ts
        attachedTo := if toZone == .battlefield then after.attachedTo else none
        chosenX := chosenX
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
                  windcragMardu := st.windcragMardu || (!st.faceDown && printed.asEntersChooseMarduOrJeskai) }
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
          transformed := object.transformed }
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
        attachedTo := if object.zone == Zone.battlefield then object.attachedTo else none
        isCopy := object.isCopy
        chosenX := if object.zone == Zone.stack then object.chosenX else none }
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

/-- Apply a `PlayerEvent` to `g` (CR 104, 106.4, 500.5, 701.20–25, 701.34, 701.54, 701.62, 702.131, 725, 800.4a). -/
def applyPlayerEvent (g : Game) (e : PlayerEvent) : Game :=
  match e with
  | .manaAdded p units =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with manaPool := pl.manaPool.addUnits units } }
    else g
  | .manaSpent p units _ =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with manaPool := pl.manaPool.removeUnits units } }
    else g
  | .manaEmptied p _ keptColorless =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx (pl.applyChange (.emptyManaPool keptColorless)) }
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
  | .shuffled p newOrder =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with library := newOrder } }
    else g
  | .ringTempted p bearer stage =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with theRingAbilities := stage, ringBearerId := bearer } }
    else g
  | .becameMonarch p _ =>
    { g with players := g.players.map (fun pl => { pl with isMonarch := pl.id == p }) }
  | .gainedDesignation p d =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      let pl' :=
        match d with
        | .citysBlessing => { pl with citysBlessing := true }
        | .enduringStory => { pl with enduringStory := true }
      { g with players := g.players.set! p.idx pl' }
    else g
  | .lost p _ =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with lost := true } }
    else g
  | .leftGame p =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx { pl with lost := true, leftTheGame := true } }
    else g
  | .gameEnded res =>
    { g with result := some res }
  | .proliferated .. | .sheHulkDealtDamage .. | .beheld ..
  | .optionalOnceActed .. | .drawFromEmptyAttempted ..
  | .lookedAt .. | .revealed .. | .searched .. => g

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
    { g with step := st, assignedCombatDamage := #[] }
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
  | .proposed .. => g
  | .announced obj modes x costs =>
    let g :=
      match g.objects.findIdx? (·.id == obj) with
      | some i =>
        let o := g.objects[i]!
        let chosenX := x.orElse (fun _ => o.chosenX)
        let status :=
          match costs.findSome? (fun | .impending n => some n | _ => none) with
          | some n => { o.status with counters := o.status.counters.set .time n }
          | none => o.status
        { g with objects := g.objects.set! i { o with
            status := status
            chosenX := chosenX } }
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
  | .spellCast .. => g
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
          chosenX := copy.chosenX.orElse (fun _ => orig.chosenX)
          adventurerCard := orig.adventurerCard
          abilityEffect := orig.abilityEffect
          triggeredAbility := orig.triggeredAbility
          reflexiveResolution := orig.reflexiveResolution
          sourceId := orig.sourceId
          fraCauseId := orig.fraCauseId
          fraCauseController := orig.fraCauseController
          fraCausePower := orig.fraCausePower
          fraCauseStatus := orig.fraCauseStatus }
      | none =>
        { id := newId
          printed := printed
          owner := controller
          controller := some controller
          zone := .stack
          status := {}
          timestamp := ts
          isCopy := true
          chosenX := copy.chosenX }
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
              attackingTarget := some target } } }
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
        let st :=
          { o.status with
            blocking :=
              if o.status.blocking.contains attackerId then o.status.blocking
              else o.status.blocking.push attackerId }
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
      let st0 :=
        { o.status with
          attacking := false
          attackingTarget := none
          blocking := #[]
          blocked := false }
      let objs := (g.objects.set! i { o with status := st0 }).map (fun x =>
        if x.status.blocking.any (· == rid) then
          { x with status := { x.status with blocking := x.status.blocking.filter (· != rid) } }
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
  | .continuousEffect e => g.applyContinuousEffectEvent e

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
  | .proposedSpell v => { g with proposedSpell := v }
  | .proposal pc =>
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some (prop.applyChange pc) }
    | none => g
  | .proposalChanges pcs =>
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some (pcs.foldl ProposedSpell.applyChange prop) }
    | none => g
  | .continuations frames => { g with continuations := frames }
  | .pushContinuationFrame frame =>
    let base := if g.continuations.isEmpty then #[{}] else g.continuations
    { g with continuations := base.push frame }
  | .popContinuationFrame => { g with continuations := g.continuations.pop }
  | .continuation cc =>
    g.modifyTopFrame (fun f =>
      match cc with
      | .pendingDrawAfterScry v => { f with pendingDrawAfterScry := v }
      | .discardedCardThisWay v => { f with discardedCardThisWay := v }
      | .palantirAfterScry v => { f with palantirAfterScry := v }
      | .recentTokenIds v => { f with recentTokenIds := v }
      | .pushRecentTokenId id => { f with recentTokenIds := f.recentTokenIds.push id }
      | .fraAfterLook v => { f with fraAfterLook := v }
      | .pendingFreeCopies v => { f with pendingFreeCopies := v }
      | .pendingMayCastFromExile v => { f with pendingMayCastFromExile := v }
      | .mayPayAlsoPlusOneOn v => { f with mayPayAlsoPlusOneOn := v }
      | .humansTappedThisWay v => { f with humansTappedThisWay := v }
      | .permanentsDestroyedThisWay v => { f with permanentsDestroyedThisWay := v }
      | .removedHopeThisWay v => { f with removedHopeThisWay := v }
      | .permanentDealtDamageThisWay v => { f with permanentDealtDamageThisWay := v }
      | .returnedPermanentThisWay v => { f with returnedPermanentThisWay := v }
      | .nthResolveThisWay v => { f with nthResolveThisWay := v }
      | .skipTriggerSequenceRest v => { f with skipTriggerSequenceRest := v }
      | .excessDamageThisWay v => { f with excessDamageThisWay := v }
      | .destroyedForAmassThisWay v => { f with destroyedForAmassThisWay := v }
      | .amassControllerThisWay v => { f with amassControllerThisWay := v }
      | .amassAmountThisWay v => { f with amassAmountThisWay := v }
      | .amassYouControlledThisWay v => { f with amassYouControlledThisWay := v }
      | .milledIdsThisWay v => { f with milledIdsThisWay := v }
      | .pushMilledIdThisWay id => { f with milledIdsThisWay := f.milledIdsThisWay.push id }
      | .revealedIdsThisWay v => { f with revealedIdsThisWay := v }
      | .opponentsMilledThisWay v => { f with opponentsMilledThisWay := v }
      | .palantirChoiceReady v => { f with palantirChoiceReady := v }
      | .grimaImpulseReady v => { f with grimaImpulseReady := v }
      | .grimaImpulseVictim v => { f with grimaImpulseVictim := v }
      | .grimaImpulseFound v => { f with grimaImpulseFound := v }
      | .grimaImpulseOthers v => { f with grimaImpulseOthers := v }
      | .planWasSacrificed v => { f with planWasSacrificed := v }
      | .sourceWasSacrificed v => { f with sourceWasSacrificed := v }
      | .exiledIdsThisWay v => { f with exiledIdsThisWay := v }
      | .pushExiledIdThisWay id => { f with exiledIdsThisWay := f.exiledIdsThisWay.push id }
      | .notedCopyObject v => { f with notedCopyObject := v }
      | .notedHostId v => { f with notedHostId := v }
      | .handDiscardedThisWay v => { f with handDiscardedThisWay := v }
      | .notedSourceThisWay v => { f with notedSourceThisWay := v }
      | .equipmentAttachedHost v => { f with equipmentAttachedHost := v }
      | .notedCountThisWay v => { f with notedCountThisWay := v }
      | .createdTokenThisWay v => { f with createdTokenThisWay := v }
      | .putArtifactThisWay v => { f with putArtifactThisWay := v }
      | .playExiledThisWay v => { f with playExiledThisWay := v }
      | .armSurveilReturn v => { f with armSurveilReturn := v }
      | .triggerSequenceRest v => { f with triggerSequenceRest := v }
      | .setTriggerSequenceRestSteps steps =>
        match f.triggerSequenceRest with
        | none => f
        | some rest =>
          if steps.isEmpty then { f with triggerSequenceRest := none }
          else { f with triggerSequenceRest := some { rest with steps } }
      | .setTriggerSequenceRestFromMay steps =>
        match f.mayContext with
        | none => f
        | some ctx =>
          { f with
            mayContext := none
            triggerSequenceRest := if steps.isEmpty then none else some { ctx with steps } }
      | .mayThenDrop v => { f with mayThenDrop := v }
      | .mayThenSkip v => { f with mayThenSkip := v }
      | .mayThenConditional v => { f with mayThenConditional := v }
      | .mayOnAccept v => { f with mayOnAccept := v }
      | .mayOnDecline v => { f with mayOnDecline := v }
      | .mayContext v => { f with mayContext := v }
      | .sacrificedPowerThisWay v => { f with sacrificedPowerThisWay := v }
      | .mayThenResume v => { f with mayThenResume := v }
      | .triggerOr v => { f with triggerOr := v }
      | .chooseModesRest v => { f with chooseModesRest := v }
      | .unlessPaysInstead v => { f with unlessPaysInstead := v }
      | .unlessPaysController v => { f with unlessPaysController := v }
      | .unlessPaysTargets v => { f with unlessPaysTargets := v }
      | .unlessPaysDue v => { f with unlessPaysDue := v }
      | .mayEffect v => { f with mayEffect := v }
      | .mayController v => { f with mayController := v }
      | .mayTargets v => { f with mayTargets := v }
      | .spellOr v => { f with spellOr := v }
      | .spellOrController v => { f with spellOrController := v }
      | .spellOrTargets v => { f with spellOrTargets := v }
      | .spellOrLibrary v => { f with spellOrLibrary := v }
      | .surveilReturnMvAtMost v => { f with surveilReturnMvAtMost := v }
      | .surveilReturnNoncreatureNonland v => { f with surveilReturnNoncreatureNonland := v }
      | .pendingReplacement v => { f with pendingReplacement := v }
      | .conniveSource v => { f with conniveSource := v }
      | .plusOneAfterDiscards v => { f with plusOneAfterDiscards := v }
      | .plusOneAfterSearch v => { f with plusOneAfterSearch := v }
      | .thirstDiscardsLeft v => { f with thirstDiscardsLeft := v }
      | .thirstDiscardType v => { f with thirstDiscardType := v }
      | .pendingDiscardsLeft v => { f with pendingDiscardsLeft := v }
      | .untapSearchedIfLands v => { f with untapSearchedIfLands := v }
      | .resolvingContext v => { f with resolvingContext := v }
      | .stashedCause v => { f with stashedCause := v })
  | .priority v => { g with priority := v }
  | .startingPlayer v => { g with startingPlayer := v, activePlayer := v }
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
  | .awaitingOpeningBegin v => { g with awaitingOpeningBegin := v }
  | .mulliganToDeclare v => { g with mulliganToDeclare := v }
  | .willMulligan v => { g with willMulligan := v }
  | .pushWillMulligan p => { g with willMulligan := g.willMulligan.push p }
  | .mulliganToBottom v => { g with mulliganToBottom := v }
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
  | .firstStrikeDamageDone v => { g with firstStrikeDamageDone := v }
  | .pendingRegularCombatDamage v => { g with pendingRegularCombatDamage := v }
  | .firstStrikeAssignedThisCombat v => { g with firstStrikeAssignedThisCombat := v }
  | .resolvingSpell v => { g with resolvingSpell := v }
  | .resolvingAbility v => { g with resolvingAbility := v }
  | .replacementOrder ids => { g with replacementOrder := ids }
  | .castingFromTop v => { g with castingFromTop := v }
  | .delayedTriggers v => { g with delayedTriggers := v }
  | .pushDelayedTrigger dt =>
    { g with delayedTriggers := g.delayedTriggers.push dt }
  | .resolvingDivision v => { g with resolvingDivision := v }
  | .wardQueue v => { g with wardQueue := v }
  | .enqueueWard ws => { g with wardQueue := g.wardQueue ++ ws }
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
  | .oneShotEffect (some actualId) src ctrl =>
    (.oneShotEffect (some actualId) src ctrl, some actualId)
  | .oneShotEffect none src ctrl =>
    let actualId : EffectId := ⟨g.nextEffectId⟩
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

/-- Whether a turn of `p` has begun (`TurnEvent.turnBegan p _`) in `g.events`
after the creation of continuous effect `eid` (CR 611.2a). -/
def hasTurnBegunSince (g : Game) (eid : EffectId) (p : PlayerId) : Bool :=
  g.events.foldl (fun (seenCreate, seenTurn) ev =>
    match ev.change with
    | .rules (.continuousEffect (.created id _)) =>
      if id == eid then (true, false) else (seenCreate, seenTurn)
    | .rules (.turn (.turnBegan q _)) =>
      if seenCreate && q == p then (seenCreate, true) else (seenCreate, seenTurn)
    | _ => (seenCreate, seenTurn)) (false, false) |>.2

/-- Timestamp `(tier, sub)` of `k` counters on `oid` (CR 613.7c): putting a new
counter of kind `k` on `oid` gives all `k` counters on `oid` that new timestamp. -/
def counterTimestamp (g : Game) (oid : ObjectId) (k : CounterKind) : Nat × Nat :=
  Id.run do
    let mut ts? : Option Nat := none
    let mut prevCount? : Option Nat := none
    for i in [0:g.events.size] do
      let ev := g.events[i]!
      match ev.change with
      | .rules (.permanent (.counters (.object eo) k' (.put n) _)) =>
        if eo.id == some oid && k' == k then
          let base := prevCount?.getD (eo.counters.count k)
          if n > 0 then
            ts? := some i
            prevCount? := some (base + n)
          else
            prevCount? := some base
      | .rules (.permanent (.counters (.object eo) k' (.removed n) _)) =>
        if eo.id == some oid && k' == k then
          let base := prevCount?.getD (eo.counters.count k)
          let next := base - n
          if next == 0 then ts? := none
          prevCount? := some next
      | .rules (.zone (.moved _ after _ _ _ _ entersWith _)) =>
        if after.id == some oid then
          let c := max (after.counters.count k) (entersWith.count k)
          ts? := if c > 0 then some i else none
          prevCount? := some c
      | .rules (.zone (.created eo _)) =>
        if eo.id == some oid then
          let c := eo.counters.count k
          ts? := if c > 0 then some i else none
          prevCount? := some c
      | .engine (.setObject obj) | .engine (.replaceObject _ obj) =>
        if obj.id == oid then
          let c := obj.status.counterCount k
          let grew : Bool := match prevCount? with | some prev => decide (c > prev) | none => decide (c > 0)
          if c == 0 then ts? := none
          else if grew then ts? := some i
          prevCount? := some c
      | .engine (.object id (.status (.set s))) =>
        if id == oid then
          let c := s.counterCount k
          let grew : Bool := match prevCount? with | some prev => decide (c > prev) | none => decide (c > 0)
          if c == 0 then ts? := none
          else if grew then ts? := some i
          prevCount? := some c
      | .engine (.object id (.status .reset)) =>
        if id == oid then
          ts? := none
          prevCount? := some 0
      | .engine (.objectChanges id cs) =>
        if id == oid then
          for ch in cs do
            match ch with
            | .status (.set s) =>
              let c := s.counterCount k
              let grew : Bool := match prevCount? with | some prev => decide (c > prev) | none => decide (c > 0)
              if c == 0 then ts? := none
              else if grew then ts? := some i
              prevCount? := some c
            | .status .reset =>
              ts? := none
              prevCount? := some 0
            | _ => pure ()
      | _ => pure ()
    return match ts? with
      | some idx => (1, idx)
      | none => (0, 1)

/-- Timestamp `(tier, sub)` when `aura` most recently became attached to `hostId` (CR 613.7e). -/
def attachmentTimestamp (g : Game) (aura : GameObject) (hostId : ObjectId) : Nat × Nat :=
  Id.run do
    let mut ts? : Option Nat := none
    let mut prevAtt? : Option (Option ObjectId) := none
    for i in [0:g.events.size] do
      let ev := g.events[i]!
      match ev.change with
      | .rules (.permanent (.attached aEo hid _)) =>
        if aEo.id == some aura.id then
          ts? := if hid == hostId then some i else none
          prevAtt? := some (some hid)
      | .rules (.permanent (.unattached aEo _)) =>
        if aEo.id == some aura.id then
          ts? := none
          prevAtt? := some none
      | .rules (.zone (.moved _ after _ .battlefield ..)) =>
        if after.id == some aura.id then
          ts? := if after.attachedTo == some hostId then some i else none
          prevAtt? := some after.attachedTo
      | .rules (.zone (.created eo _)) =>
        if eo.id == some aura.id then
          ts? := if eo.attachedTo == some hostId then some i else none
          prevAtt? := some eo.attachedTo
      | .engine (.setObject obj) | .engine (.replaceObject _ obj) =>
        if obj.id == aura.id then
          let newly :=
            match prevAtt? with
            | some prev => prev != some hostId && obj.attachedTo == some hostId
            | none => obj.attachedTo == some hostId
          if obj.attachedTo != some hostId then ts? := none
          else if newly then ts? := some i
          prevAtt? := some obj.attachedTo
      | .engine (.object id (.attachedTo v)) =>
        if id == aura.id then
          let newly :=
            match prevAtt? with
            | some prev => prev != some hostId && v == some hostId
            | none => v == some hostId
          if v != some hostId then ts? := none
          else if newly then ts? := some i
          prevAtt? := some v
      | .engine (.objectChanges id cs) =>
        if id == aura.id then
          for ch in cs do
            match ch with
            | .attachedTo v =>
              let newly :=
                match prevAtt? with
                | some prev => prev != some hostId && v == some hostId
                | none => v == some hostId
              if v != some hostId then ts? := none
              else if newly then ts? := some i
              prevAtt? := some v
            | _ => pure ()
      | _ => pure ()
    return match ts? with
      | some idx => (1, idx)
      | none => (0, 2 + aura.timestamp)

/-- Timestamp `(tier, sub)` when `obj` entered its current zone (CR 613.7d). -/
def objectEntryTimestamp (g : Game) (obj : GameObject) : Nat × Nat :=
  Id.run do
    let mut ts? : Option Nat := none
    for i in [0:g.events.size] do
      let ev := g.events[i]!
      match ev.change with
      | .rules (.zone (.moved _ after ..)) =>
        if after.id == some obj.id then ts? := some i
      | .rules (.zone (.created eo _)) =>
        if eo.id == some obj.id then ts? := some i
      | .engine (.setObject o) | .engine (.replaceObject _ o) =>
        if o.id == obj.id then ts? := some i
      | _ => pure ()
    return match ts? with
      | some idx => (1, idx)
      | none => (0, 2 + obj.timestamp)

/-- Timestamp `(tier, sub)` when continuous effect `eid` was created (CR 613.7b). -/
def effectTimestamp (g : Game) (eid : EffectId) (pos : Nat) : Nat × Nat :=
  Id.run do
    let mut ts? : Option Nat := none
    for i in [0:g.events.size] do
      match g.events[i]!.change with
      | .rules (.continuousEffect (.created id _)) =>
        if id == eid then ts? := some i
      | _ => pure ()
    return match ts? with
      | some idx => (1, idx)
      | none => (0, 1000000 + pos)

/-- Whether `d` is currently active in `g` (e.g. `.whileSourceOnBattlefield src`
requires `src` to be on the battlefield, CR 611.2b). -/
def durationActive (g : Game) (d : EffectDuration) : Bool :=
  match d with
  | .whileSourceOnBattlefield src =>
    (g.findObject? src).any (·.isOnBattlefield)
  | .whileSourceHasCounter src k =>
    (g.findObject? src).any (fun o => o.isOnBattlefield && o.status.counterCount k > 0)
  | .whileInZone oid z =>
    (g.findObject? oid).any (fun o => o.zone == z)
  | _ => true

-- Game-wide rule queries (CR 611.2c / 613.10)

def creaturesWithoutFlyingCantBlock (g : Game) : Bool :=
  g.activeEffects.any (fun (_, s) => s == .creaturesWithoutFlyingCantBlockUntilEot)

def powerUpsForbidden (g : Game) : Bool :=
  g.activeEffects.any (fun (_, s) => s == .powerUpsForbiddenThisTurn)

def assignCombatDamageEqualToughness (g : Game) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule p .assignCombatDamageEqualToughness _ => some p
    | _ => acc) none

def playerControl (g : Game) : Option (PlayerId × PlayerId) :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule you (.controlsPlayer them _) _ => some (you, them)
    | _ => acc) none

def controlOnNextTakenTurn (g : Game) : Array (PlayerId × PlayerId) :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .playerRule you (.controlsPlayer them true) _ => some (you, them)
    | _ => none

def pendingLokiCopy (g : Game) : Option (PlayerId × Option ObjectId × Int) :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule p (.pendingLokiCopy src pw) _ => some (p, src, pw)
    | _ => acc) none

def pendingFreeRGCreature (g : Game) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule p .pendingFreeRGCreature _ => some p
    | _ => acc) none

-- Player-rule queries (CR 611.2c / 613.10)

def additionalLandsThisTurn (g : Game) (p : PlayerId) : Nat :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule q (.additionalLands n) _ => if q == p then acc + n else acc
    | _ => acc) 0

def protectionFromEverything (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .protectionFromEverything _ => q == p
    | _ => false

def cantCastSpellsThisTurn (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .cantCastSpells _ => q == p
    | _ => false

def lifeLocked (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .lifeLocked _ => q == p
    | _ => false

def lifeCantChange (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .lifeCantChange _ => q == p
    | _ => false

def typeSpellCostLessThisTurn (g : Game) (p : PlayerId) : Array (CardType × Nat) :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .playerRule q (.typeSpellCostLess t n) _ => if q == p then some (t, n) else none
    | _ => none

def supertypeSpellCostLessThisTurn (g : Game) (p : PlayerId) : Array (Supertype × Nat) :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .playerRule q (.supertypeSpellCostLess st n) _ => if q == p then some (st, n) else none
    | _ => none

def jaceLoyaltyAtInstantSpeed (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .jaceLoyaltyAtInstantSpeed _ => q == p
    | _ => false

def legendRuleOffThisTurn (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .legendRuleOff _ => q == p
    | _ => false

def copyNextInstantSorceryThisTurn (g : Game) (p : PlayerId) : Nat :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule q (.copyNextInstantSorcery n) _ => if q == p then acc + n else acc
    | _ => acc) 0

def mountainExtraRedThisTurn (g : Game) (p : PlayerId) : Nat :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule q (.mountainExtraRed n) _ => if q == p then acc + n else acc
    | _ => acc) 0

def nextSpellCantBeCountered (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .nextSpellCantBeCountered _ => q == p
    | _ => false

def cantAttackJaces (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .cantAttackJaces _ => q == p
    | _ => false

-- Object / status rule and permission queries (CR 611.2 / 613)

def playPermissionEntryOf? (g : Game) (id : ObjectId) :
    Option (EffectId × PlayerId × PlayPermission × EffectDuration) :=
  let active :=
    g.activeEffects.foldl (fun acc (eid, s) =>
      match s with
      | .permission p (.playFromExile oid perm) d =>
        if oid == id then some (eid, p, perm, d) else acc
      | _ => acc) none
  if active.isSome || (g.findObject? id).isSome then active
  else
    g.events.findSomeRev? fun e =>
      match e.change with
      | .rules (.continuousEffect (.created eid (.permission p (.playFromExile oid perm) d))) =>
        if oid == id then some (eid, p, perm, d) else none
      | _ => none

def playPermissionOf? (g : Game) (o : GameObject) : Option PlayPermission :=
  (g.playPermissionEntryOf? o.id).map fun (_, _, perm, _) => perm

@[inline] def playPermission (g : Game) (o : GameObject) : Option PlayPermission :=
  g.playPermissionOf? o

def playPermissionDuration (g : Game) (o : GameObject) : Option EffectDuration :=
  (g.playPermissionEntryOf? o.id).map fun (_, _, _, d) => d

def flashbackUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .permission _ (.flashback id) _ => id == o.id
    | _ => false

def freeCastFromGraveyard (g : Game) (o : GameObject) : Bool :=
  let active :=
    g.activeEffects.any fun (_, s) =>
      match s with
      | .permission _ (.freeCastFromGraveyard id) _ => id == o.id
      | _ => false
  if active || (g.findObject? o.id).isSome then active
  else
    g.events.any fun e =>
      match e.change with
      | .rules (.continuousEffect (.created _ (.permission _ (.freeCastFromGraveyard id) _))) =>
        id == o.id
      | _ => false

def colorlessGrantUntilCast (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .permission _ (.colorlessGrant landId cardId) _ =>
      if landId == o.id then some cardId else none
    | _ => none

def uncounterableThisCast (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule (.uncounterable id) _ => id == o.id
    | _ => false

def exileInstantSorceryInstead (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .replacement r _ =>
      r.id.kind == .exileInstantSorceryInstead && r.id.object == some o.id
    | _ => false

def untilEotExileIfDies (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .replacement r _ =>
      r.id.kind == .untilEotExileIfDies && r.id.object == some o.id
    | _ => false

def preventDamageGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .prevention p (.whileSourceOnBattlefield src) =>
      match p.kind with
      | .preventAllDamageFromSource id => if id == o.id then some src else none
      | _ => none
    | _ => none

def cantUntapGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .gameRule (.cantUntap id src) (.whileSourceOnBattlefield _) =>
      if id == o.id then some src else none
    | _ => none

def cantTransform (_g : Game) (o : GameObject) : Bool :=
  o.status.transformed

def cantBlockUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule (.cantBlock id) _ => id == o.id
    | _ => false

def cantBeBlockedByPlayer (g : Game) (o : GameObject) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .gameRule (.cantBeBlockedByPlayer id p) _ => if id == o.id then some p else acc
    | _ => acc) none

def cantBeBlockedExceptByHasteUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule (.cantBeBlockedExceptByHaste id) _ => id == o.id
    | _ => false

def combatDamageCreatesTreasure (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities add _) _ =>
      id == o.id && add.combatDamageCreatesTreasure
    | _ => false

def ironFistTapGrants (g : Game) (o : GameObject) : Nat :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities add _) _ =>
      if id == o.id then acc + add.ironFistTapGrants else acc
    | _ => acc) 0

def hexproofGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities add _) (.whileSourceOnBattlefield src) =>
      if id == o.id && add.keywords.hexproof then some src else none
    | _ => none

def losesAbilitiesUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities _ .all) .untilEndOfTurn => id == o.id
    | _ => false

def losesAbilitiesGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities _ .all) (.whileSourceOnBattlefield src) =>
      if id == o.id then some src else none
    | _ => none

def untilEotLosesIndestructible (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects ids) (.abilities _ .loseIndestructible) d =>
      ids.contains o.id && g.durationActive d
    | _ => false

def firstStrikeOnYourTurn (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities add _) _ =>
      id == o.id && add.firstStrikeOnYourTurn
    | _ => false

def onlyFoodArtifact (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .set ts subs _) _ =>
      id == o.id && ts == #[.artifact] && subs == #[.food]
    | _ => false

def returnedAsArtifact (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .addArtifactRemoveCreature _ _ _) _ => id == o.id
    | _ => false

def notACreature (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .removeCreature _ _ _) _ => id == o.id
    | _ => false

def animatedConstruct55 (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .addConstruct55 _ _ _) _ => id == o.id
    | _ => false

def additionalArtifactUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .add ts _ _) .untilEndOfTurn =>
      id == o.id && ts.contains .artifact
    | _ => false

def additionalCreature (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .add ts _ _) .indefinite =>
      id == o.id && ts.contains .creature
    | _ => false

def additionalCreatureUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .add ts _ _) .untilEndOfTurn =>
      id == o.id && ts.contains .creature
    | _ => false

def pumpPerArtifactUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.ptCda .pumpPerArtifact) _ => id == o.id
    | _ => false

def cardsInHandPowerUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.ptCda .cardsInHandPower) _ => id == o.id
    | _ => false

def fraEffectUntilTurnOf (g : Game) (o : GameObject) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .gameRule (.fraEmblem id) (.untilNextTurnOf p) => if id == o.id then some p else acc
    | _ => acc) none

def controlUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.control _) .untilEndOfTurn => id == o.id
    | _ => false

def controlTurnEndsLeft (g : Game) (o : GameObject) : Nat :=
  g.activeEffects.foldl (fun acc (eid, s) =>
    match s with
    | .layered (.objects #[id]) (.control _) (.untilNextTurnOf _) =>
      if id == o.id then max acc 1 else acc
    | .layered (.objects #[id]) (.control _) (.untilEndOfNextTurnOf p) =>
      if id == o.id then
        let rem := if g.hasTurnBegunSince eid p then 1 else 2
        max acc rem
      else acc
    | _ => acc) 0

def controlUntilSourceLeaves (g : Game) (o : GameObject) : Option ObjectId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects #[id]) (.control _) (.whileSourceOnBattlefield src) =>
      if id == o.id then some src else acc
    | _ => acc) none

def controlChanged (g : Game) (o : GameObject) : Bool :=
  let defCtrl := o.defaultController.getD o.owner
  o.controller != some defCtrl ||
    g.activeEffects.any (fun (_, s) =>
      match s with
      | .layered (.objects #[id]) (.control _) _ => id == o.id
      | _ => false) ||
    g.events.any (fun ev =>
      match ev.change with
      | .rules (.permanent (.controlChanged eo _ _)) => eo.id == some o.id
      | _ => false)

def copyRestore (g : Game) (o : GameObject) : Option CardDef :=
  g.copyRestoreOf? o.id

def copyUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.copy _ _) .untilEndOfTurn => id == o.id
    | _ => false

def copyUntilNextTurn (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.copy _ _) (.untilNextTurnOf _) => id == o.id
    | _ => false

def copyUntilSourceLeaves (g : Game) (o : GameObject) : Option ObjectId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects #[id]) (.copy _ _) (.whileSourceOnBattlefield src) =>
      if id == o.id then some src else acc
    | _ => acc) none

-- Layer 4: Type-changing effects (CR 613.1d / 613.7 / 613.8)

def replacedCreatureTypesUntilEot (g : Game) (o : GameObject) : Option (Array CardSubtype) :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects ids) (.types .setAndKeepNoncreatureSubtypes _ subs _) d =>
      if ids.contains o.id && g.durationActive d then some subs else acc
    | _ => acc) none

def additionalSubtypes (g : Game) (o : GameObject) : Array CardSubtype :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects ids) (.types .add _ subs _) d =>
      if ids.contains o.id && g.durationActive d then acc ++ subs else acc
    | .layered (.objects ids) (.types .addDedup _ subs _) d =>
      if ids.contains o.id && g.durationActive d then
        subs.foldl (fun a sub => if a.contains sub then a else a.push sub) acc
      else acc
    | _ => acc) #[]

private structure Layer4Entry where
  idx : Nat
  ts : Nat × Nat
  scope : ObjectScope
  mode : SetOrAdd
  tsAdd : Array CardType
  subs : Array CardSubtype
  sups : Array Supertype
deriving Inhabited

/-- Unified Layer 4 evaluation of `(types, subtypes, supertypes)` on `o` in
CR 613.7 timestamp order with CR 613.8 dependency ordering. -/
def evalLayer4 (g : Game) (o : GameObject) : Array CardType × Array CardSubtype × Array Supertype :=
  if o.status.faceDown then (#[.creature], #[], #[])
  else if !o.isOnBattlefield then
    (o.printed.types, CardSubtype.ofSubtypes o.printed.subtypes, o.printed.supertypes)
  else
    let pushDedup {α : Type} [BEq α] (acc elems : Array α) : Array α :=
      elems.foldl (fun a x => if a.contains x then a else a.push x) acc
    let subtypeCorrelatedWith (ts : Array CardType) (sub : CardSubtype) : Bool :=
      match sub.kind with
      | .artifact => ts.contains .artifact
      | .enchantment => ts.contains .enchantment
      | .land => ts.contains .land
      | .planeswalker => ts.contains .planeswalker
      | .spell => ts.contains .instant || ts.contains .sorcery
      | .creature => ts.contains .creature || ts.contains .kindred
      | .planar => ts.contains .plane
      | .dungeon => ts.contains .dungeon
      | .battle => ts.contains .battle
    let effectiveSubs (ts : Array CardType) (subs : Array CardSubtype) : Array CardSubtype :=
      if ts.contains .creature || ts.contains .kindred then subs
      else subs.filter CardSubtype.isNoncreature
    let initTypes :=
      match o.status.chosenCardType with
      | some t => if o.printed.types.contains t then o.printed.types else o.printed.types.push t
      | none => o.printed.types
    -- Layer 3: Text-changing effects (CR 613.1c)
    let initSubs :=
      g.activeEffects.foldl (fun acc (_, s) =>
        match s with
        | .layered (.objects ids) (.text (.replaceCreatureType fromSub toSub)) d =>
          if ids.contains o.id && g.durationActive d then
            acc.map (fun sub => if sub == fromSub then toSub else sub)
          else acc
        | _ => acc) (CardSubtype.ofSubtypes o.printed.subtypes)
    let initSups := o.printed.supertypes
    let baseKw : Keywords :=
      g.activeEffects.foldl (fun acc (_, s) =>
        match s with
        | .layered (.objects ids) (.abilities add rem) d =>
          if ids.contains o.id && g.durationActive d then
            Keywords.merge (if rem == .all then Keywords.none else acc) add.keywords
          else acc
        | _ => acc) o.printed.keywords
    let scopeMatchesL4 (cur : Array CardType × Array CardSubtype × Array Supertype)
        (sc : ObjectScope) : Bool :=
      match sc with
      | .objects ids => ids.contains o.id
      | .creaturesControlledBy p => o.controlledBy p && cur.1.contains .creature
      | .creaturesWithout kw =>
        cur.1.contains .creature && Keywords.merge baseKw kw != baseKw
      | .permanentsOfSubtype p s =>
        o.controlledBy p &&
          ((effectiveSubs cur.1 cur.2.1).contains s ||
            (o.printed.keywords.changeling &&
              (cur.1.contains .creature || cur.1.contains .kindred) && !s.isNoncreature))
    let applyStep (cur : Array CardType × Array CardSubtype × Array Supertype)
        (e : Layer4Entry) : Array CardType × Array CardSubtype × Array Supertype :=
      let (ts, subs, sups) := cur
      match e.mode with
      | .set =>
        let ts' := if e.tsAdd.isEmpty then ts else e.tsAdd
        let subs' := if !e.subs.isEmpty then e.subs else subs.filter (subtypeCorrelatedWith ts')
        let sups' := if e.sups.isEmpty then sups else e.sups
        (ts', subs', sups')
      | .add =>
        (pushDedup ts e.tsAdd, subs ++ e.subs, pushDedup sups e.sups)
      | .addDedup =>
        (pushDedup ts e.tsAdd, pushDedup subs e.subs, pushDedup sups e.sups)
      | .addConstruct55 =>
        let addTs := if e.tsAdd.isEmpty then #[.artifact, .creature] else e.tsAdd
        let addSubs := if e.subs.isEmpty then #[.construct] else e.subs
        (pushDedup ts addTs, pushDedup subs addSubs, pushDedup sups e.sups)
      | .setAndKeepNoncreatureSubtypes =>
        (pushDedup ts e.tsAdd, subs.filter CardSubtype.isNoncreature ++ e.subs, pushDedup sups e.sups)
      | .addArtifactRemoveCreature =>
        let ts1 := ts.filter (· != .creature)
        let ts2 := pushDedup ts1 (if e.tsAdd.isEmpty then #[.artifact] else e.tsAdd)
        (ts2, subs.filter CardSubtype.isNoncreature ++ e.subs, pushDedup sups e.sups)
      | .removeCreature =>
        (ts.filter (· != .creature), subs.filter CardSubtype.isNoncreature, sups)
    Id.run do
      let mut raw : Array Layer4Entry := #[]
      for pos in [0:g.activeEffects.size] do
        let (eid, s) := g.activeEffects[pos]!
        match s with
        | .layered sc (.types mode ts subs sups) d =>
          if g.durationActive d then
            raw := raw.push {
              idx := raw.size
              ts := g.effectTimestamp eid pos
              scope := sc
              mode := mode
              tsAdd := ts
              subs := subs
              sups := sups
            }
        | _ => pure ()
      let sorted := raw.qsort fun a b =>
        if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
        else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
        else a.idx < b.idx
      let mut rem := sorted
      let mut cur := (initTypes, initSubs, initSups)
      for _ in [0:sorted.size] do
        let applicable := rem.filter (fun e => scopeMatchesL4 cur e.scope)
        if applicable.isEmpty then break
        let dependsOn (a b : Layer4Entry) : Bool :=
          a.idx != b.idx &&
            scopeMatchesL4 cur a.scope != scopeMatchesL4 (applyStep cur b) a.scope
        let chosen :=
          (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
        cur := applyStep cur chosen
        rem := rem.filter (fun e => e.idx != chosen.idx)
      return (cur.1, effectiveSubs cur.1 cur.2.1, cur.2.2)

/-- Evaluated card types of `o` after Layer 4 type-changing effects (CR 613.1d). -/
def types (g : Game) (o : GameObject) : Array CardType :=
  (g.evalLayer4 o).1

def hasType (g : Game) (o : GameObject) (t : CardType) : Bool :=
  (g.types o).contains t

def isCreature (g : Game) (o : GameObject) : Bool :=
  if o.isOnBattlefield then g.hasType o .creature else o.isCreature

def isArtifact (g : Game) (o : GameObject) : Bool :=
  if o.isOnBattlefield then g.hasType o .artifact else o.printed.isArtifact

def isLand (g : Game) (o : GameObject) : Bool :=
  if o.isOnBattlefield then g.hasType o .land else o.printed.isLand

def isEnchantment (g : Game) (o : GameObject) : Bool :=
  if o.isOnBattlefield then g.hasType o .enchantment else o.printed.isEnchantment

def isPlaneswalker (g : Game) (o : GameObject) : Bool :=
  if o.isOnBattlefield then g.hasType o .planeswalker else o.printed.isPlaneswalker

/-- Evaluated supertypes of `o` after Layer 4 type-changing effects (CR 613.1d). -/
def supertypes (g : Game) (o : GameObject) : Array Supertype :=
  (g.evalLayer4 o).2.2

def hasSupertype (g : Game) (o : GameObject) (st : Supertype) : Bool :=
  (g.supertypes o).contains st

def isLegendary (g : Game) (o : GameObject) : Bool :=
  g.hasSupertype o .legendary

/-- Evaluated subtypes of `o` after Layer 4 type-changing effects (CR 613.1d). -/
def subtypes (g : Game) (o : GameObject) : Array CardSubtype :=
  (g.evalLayer4 o).2.1

/-- Evaluated type line of `o` after Layer 4 type-changing effects (CR 205.1a / 613.1d). -/
def typeLine (g : Game) (o : GameObject) : String :=
  formatTypeLine (g.supertypes o) (g.types o) ((g.subtypes o).map CardSubtype.englishName)

-- Layer 5: Color-changing effects (CR 613.1e)

def colors (g : Game) (o : GameObject) : ColorSet :=
  if o.status.faceDown then ColorSet.empty
  else if !o.isOnBattlefield then o.printed.colors
  else
    g.activeEffects.foldl (fun acc (_, s) =>
      match s with
      | .layered (.objects ids) (.colors mode cols) d =>
        if !ids.contains o.id || !g.durationActive d then acc
        else
          match mode with
          | .set => cols
          | .add | .addDedup => ColorSet.union acc cols
          | _ => acc
      | .layered (.creaturesControlledBy p) (.colors mode cols) d =>
        if !o.controlledBy p || !g.isCreature o || !g.durationActive d then acc
        else
          match mode with
          | .set => cols
          | .add | .addDedup => ColorSet.union acc cols
          | _ => acc
      | _ => acc) o.printed.colors

-- Layer 6: Ability-adding and ability-removing effects (CR 613.1f / 613.7 / 613.8)

private structure StaticAbEntry where
  idx : Nat
  ts : Nat × Nat
  rem : AbilityRemoval
  add : Array StaticAbility

private def evalStaticAbilitiesAux (g : Game) : Nat → GameObject → Array StaticAbility
  | 0, _ => #[]
  | fuel + 1, o =>
    if o.status.faceDown then #[]
    else
      let scopeOk (sc : ObjectScope) : Bool :=
        match sc with
        | .objects ids => ids.contains o.id
        | .creaturesControlledBy p => o.isOnBattlefield && o.controlledBy p && g.isCreature o
        | .creaturesWithout _ => o.isOnBattlefield && g.isCreature o
        | .permanentsOfSubtype p s =>
          o.isOnBattlefield && o.controlledBy p &&
            ((g.subtypes o).contains s ||
              (o.printed.keywords.changeling && g.isCreature o && !s.isNoncreature))
      Id.run do
        let mut raw : Array StaticAbEntry := #[]
        if o.isOnBattlefield then
          for aura in g.battlefield do
            if aura.attachedTo == some o.id then
              let auraAbs := evalStaticAbilitiesAux g fuel aura
              let strips := auraAbs.any fun
                | .enchantedLosesAbilitiesDoesntUntap => true
                | .enchantedLosesAbilitiesCantUntap => true
                | _ => false
              if strips then
                raw := raw.push {
                  idx := raw.size
                  ts := g.attachmentTimestamp aura o.id
                  rem := .all
                  add := #[]
                }
        for pos in [0:g.activeEffects.size] do
          let (eid, s) := g.activeEffects[pos]!
          match s with
          | .layered sc (.abilities add rem) d =>
            if scopeOk sc && g.durationActive d &&
                (rem == .all || !add.staticAbilities.isEmpty) then
              raw := raw.push {
                idx := raw.size
                ts := g.effectTimestamp eid pos
                rem := rem
                add := add.staticAbilities
              }
          | _ => pure ()
        let sorted := raw.qsort fun a b =>
          if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
          else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
          else a.idx < b.idx
        let mut acc := o.printed.staticAbilities
        for e in sorted do
          if e.rem == .all then acc := #[]
          acc := acc ++ e.add
        return acc

/-- Evaluated static abilities of `o` in Layer 6 (CR 613.1f / 613.7). -/
def staticAbilities (g : Game) (o : GameObject) : Array StaticAbility :=
  evalStaticAbilitiesAux g (g.objects.size + 1) o

/-- True when an attached Aura makes `o` lose all abilities (Enchanted
River's Grasp; Frozen in Ice). -/
def attachedLosesAbilities (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun aura =>
      aura.attachedTo == some o.id &&
        (g.staticAbilities aura).any (fun
          | .enchantedLosesAbilitiesDoesntUntap => true
          | .enchantedLosesAbilitiesCantUntap => true
          | _ => false))

/-- Printed abilities still apply unless an active Layer 6 ability-removal
effect (e.g., The Wondrous Wasp) or an attached Aura strips them (CR 613.1f). -/
def retainsPrintedAbilities (g : Game) (o : GameObject) : Bool :=
  !o.status.faceDown &&
  !g.attachedLosesAbilities o &&
  !g.activeEffects.any (fun (_, s) =>
    match s with
    | .layered (.objects ids) (.abilities _ .all) d =>
      ids.contains o.id && g.durationActive d
    | .layered (.creaturesControlledBy p) (.abilities _ .all) d =>
      o.isOnBattlefield && o.controlledBy p && g.isCreature o && g.durationActive d
    | .layered (.permanentsOfSubtype p sub) (.abilities _ .all) d =>
      o.isOnBattlefield && o.controlledBy p && (g.subtypes o).contains sub && g.durationActive d
    | _ => false)

def grantedStaticAbilities (g : Game) (o : GameObject) : Array StaticAbility :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects ids) (.abilities add rem) d =>
      if ids.contains o.id && g.durationActive d then
        let base := if rem == .all then #[] else acc
        base ++ add.staticAbilities
      else acc
    | .layered (.creaturesControlledBy p) (.abilities add rem) d =>
      if o.isOnBattlefield && o.controlledBy p && g.isCreature o && g.durationActive d then
        let base := if rem == .all then #[] else acc
        base ++ add.staticAbilities
      else acc
    | _ => acc) #[]

def grantedTriggeredAbilities (g : Game) (o : GameObject) : Array TriggeredAbility :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects ids) (.abilities add _) .indefinite =>
      if ids.contains o.id then acc ++ add.triggeredAbilities else acc
    | _ => acc) #[]

def grantedTriggersUntilEot (g : Game) (o : GameObject) : Array TriggeredAbility :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects ids) (.abilities add _) .untilEndOfTurn =>
      if ids.contains o.id then acc ++ add.triggeredAbilities else acc
    | _ => acc) #[]

def untilEotKeywords (g : Game) (o : GameObject) : Keywords :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered (.objects ids) (.abilities add rem) d =>
      if ids.contains o.id && g.durationActive d then
        let base := if rem == .all then Keywords.none else acc
        Keywords.merge base add.keywords
      else acc
    | .layered (.creaturesControlledBy p) (.abilities add rem) d =>
      if o.isOnBattlefield && o.controlledBy p && g.isCreature o && g.durationActive d then
        let base := if rem == .all then Keywords.none else acc
        Keywords.merge base add.keywords
      else acc
    | _ => acc) Keywords.none

def printedOrUntilEot (g : Game) (o : GameObject) : Keywords :=
  if o.status.faceDown then g.untilEotKeywords o
  else Keywords.merge o.printed.keywords (g.untilEotKeywords o)

/-- Creatures `p` currently controls (evaluated after Layer 4, CR 613.1d). -/
def creaturesControlledBy (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (g.isCreature ·)

/-- Current subtypes after Aura type-setting (e.g. Fog on the Barrow-Downs
makes the enchanted creature only a Spirit; CR 205.3m / 613.1d). -/
def currentSubtypes (g : Game) (o : GameObject) : Array CardSubtype :=
  match g.battlefield.find? (fun a =>
    a.attachedTo == some o.id &&
      (g.staticAbilities a).any (fun ab => ab.enchantedOnlySubtype?.isSome)) with
  | none => g.subtypes o
  | some aura =>
    match (g.staticAbilities aura).findSome? (fun ab => ab.enchantedOnlySubtype?) with
    | some s => #[s]
    | none => g.subtypes o

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
    (g.staticAbilities o).any fun
      | .getsAndAllTypesIfGyCreatureCards min _ _ => g.gyCreatureCards p >= min
      | _ => false

/-- Types an attached Aura adds, including the word "legendary". -/
def auraAddedTypes (g : Game) (o : GameObject) : Array CardSubtype :=
  if !o.isOnBattlefield then #[]
  else
    g.battlefield.foldl (fun acc a =>
      if a.attachedTo != some o.id then acc
      else
        (g.staticAbilities a).foldl (fun acc ab =>
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
        (g.staticAbilities a).any (fun ab => ab.enchantedOnlySubtype?.isSome))
  (g.currentSubtypes o).any (· == s) ||
    (g.auraAddedTypes o).any (· == s) ||
    (!fogged && ((g.printedOrUntilEot o).changeling || g.hasAllCreatureTypes o) &&
      !s.isNoncreature)

/-- Whether `o` matches `scope` (CR 611.2c / 611.3 / 613.8). -/
def scopeMatches (g : Game) (scope : ObjectScope) (o : GameObject) : Bool :=
  match scope with
  | .objects ids => ids.contains o.id
  | .creaturesControlledBy p => o.isOnBattlefield && o.controlledBy p && g.isCreature o
  | .creaturesWithout kw =>
    o.isOnBattlefield && g.isCreature o &&
      Keywords.merge (g.printedOrUntilEot o) kw != g.printedOrUntilEot o
  | .permanentsOfSubtype p s => o.isOnBattlefield && o.controlledBy p && g.hasSubtype o s

-- Layer 7b / 7c queries (CR 613.4b–c)

def setBasePT (g : Game) (o : GameObject) : Option (Int × Int) :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .layered scope (.ptSet pw tg) d =>
      if g.scopeMatches scope o && g.durationActive d then some (pw, tg) else acc
    | _ => acc) none

def setBasePower (g : Game) (o : GameObject) : Option Int :=
  (g.setBasePT o).map Prod.fst

def setBaseToughness (g : Game) (o : GameObject) : Option Int :=
  (g.setBasePT o).map Prod.snd

def pumpOf (g : Game) (o : GameObject) : Int × Int :=
  g.activeEffects.foldl (fun (ap, atg) (_, s) =>
    match s with
    | .layered scope (.ptModify pw tg) d =>
      let isUntilTurn := match d with | .untilNextTurnOf _ => true | _ => false
      if !isUntilTurn && g.scopeMatches scope o && g.durationActive d then
        (ap + pw, atg + tg)
      else (ap, atg)
    | _ => (ap, atg)) (0, 0)

def untilTurnOfPump (g : Game) (o : GameObject) : Array (PlayerId × Int × Int) :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .layered scope (.ptModify pw tg) (.untilNextTurnOf p) =>
      if g.scopeMatches scope o then some (p, pw, tg) else none
    | _ => none

/-- The stack entry for `objectId`, if that object is on the stack. -/
def stackEntry? (g : Game) (objectId : ObjectId) : Option StackEntry :=
  g.stack.find? (fun e => e.objectId == objectId)

/-- Whether `p` currently has an enduring story. -/
def hasEnduringStory (g : Game) (p : PlayerId) : Bool :=
  (g.player p).enduringStory

/-- A permanent counts once toward Storied even if it is legendary, an
artifact, and a Saga. -/
def countsTowardStoried (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    (g.isLegendary o || g.isArtifact o || g.hasSubtype o .saga)

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

/-- The `EventCause` recorded on the most recent zone-change event that moved
an object into `id`. Used to thread a one-shot instruction's `EffectId` across
multi-step library reveal / exile / bottom-of-library effects and linked-exile
returns (CR 610.3). -/
def lastMoveCauseOf? (g : Game) (id : ObjectId) : Option EventCause :=
  g.events.findSomeRev? fun e =>
    match e.change with
    | .rules (.zone (.moved _ after ..)) =>
      if after.id == some id then some e.cause else none
    | _ => none

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

/-- How many times an activated ability of `id` has been activated this turn (CR 602.5b). -/
def activationsThisTurn (g : Game) (id : ObjectId) : Nat :=
  g.events.foldl (fun n e =>
    if e.turn != g.turnNumber then n
    else
      match e.change with
      | .rules (.cast (.abilityActivated _ src _ _)) =>
        if src.id == some id then n + 1 else n
      | _ => n) 0

/-- Indices of activated abilities of `id` activated this turn (CR 602.5b). -/
def abilitiesActivatedThisTurn (g : Game) (id : ObjectId) : Array Nat :=
  g.events.foldl (fun acc e =>
    if e.turn != g.turnNumber then acc
    else
      match e.change with
      | .rules (.cast (.abilityActivated _ src _ (.nonMana _ _ _ _ (some idx) _)))
      | .rules (.cast (.abilityActivated _ src _ (.mana (some idx)))) =>
        if src.id == some id then acc.push idx else acc
      | _ => acc) #[]

/-- True when a loyalty ability of `id` was activated this turn (CR 606.3). -/
def loyaltyActivatedThisTurn (g : Game) (id : ObjectId) : Bool :=
  g.events.any fun e =>
    e.turn == g.turnNumber &&
      match e.change with
      | .rules (.cast (.abilityActivated _ src _ (.nonMana (some _) ..))) =>
        src.id == some id
      | _ => false

/-- True when a boast ability of `id` was activated this turn (CR 702.142a). -/
def boastUsedThisTurn (g : Game) (id : ObjectId) : Bool :=
  g.events.any fun e =>
    e.turn == g.turnNumber &&
      match e.change with
      | .rules (.cast (.abilityActivated _ src _ (.nonMana _ _ _ true ..))) =>
        src.id == some id
      | _ => false

/-- How many times a power-up ability of `id` has been activated since `id` entered (CR 702.193). -/
def powerUpActivations (g : Game) (id : ObjectId) : Nat :=
  g.events.foldl (fun n e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) =>
      if after.id == some id then 0 else n
    | .rules (.zone (.created obj _)) =>
      if obj.id == some id then 0 else n
    | .rules (.cast (.abilityActivated _ src _ (.nonMana _ _ true ..))) =>
      if src.id == some id then n + 1 else n
    | _ => n) 0

/-- True when a power-up ability of `id` has been activated since `id` entered (CR 702.193). -/
def powerUpUsed (g : Game) (id : ObjectId) : Bool :=
  g.powerUpActivations id > 0

/-- True when an exhaust ability of `id` has been activated since `id` entered (CR 702.177). -/
def exhaustUsed (g : Game) (id : ObjectId) : Bool :=
  g.events.foldl (fun used e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) =>
      if after.id == some id then false else used
    | .rules (.zone (.created obj _)) =>
      if obj.id == some id then false else used
    | .rules (.cast (.abilityActivated _ src _ (.nonMana _ _ _ _ _ true))) =>
      used || src.id == some id
    | _ => used) false

/-- True when `id` was declared as an attacker this turn (CR 508.1k / 702.142a). -/
def declaredAsAttackerThisTurn (g : Game) (id : ObjectId) : Bool :=
  g.events.any fun e =>
    e.turn == g.turnNumber &&
      match e.change with
      | .rules (.combat (.attackersDeclared _ decls)) =>
        decls.any (fun (attacker, _) => attacker.id == some id)
      | _ => false

/-- True when `id` became tapped this turn (CR 701.26a). -/
def becameTappedThisTurn (g : Game) (id : ObjectId) : Bool :=
  g.events.any fun e =>
    e.turn == g.turnNumber &&
      match e.change with
      | .rules (.permanent (.tapped obj _)) => obj.id == some id
      | _ => false

/-- True when a +1/+1 counter was put on `id` this turn (CR 122.1 / 122.6). -/
def gotPlusOneThisTurn (g : Game) (id : ObjectId) : Bool :=
  g.events.any fun e =>
    e.turn == g.turnNumber &&
      e.countersPutInEvent.any (fun (eo, kind, n, _) =>
        eo.id == some id && kind == .plusOnePlusOne && n > 0)

/-- True when `id` dealt a positive amount of damage this turn (CR 120.2). -/
def dealtDamageThisTurn (g : Game) (id : ObjectId) : Bool :=
  g.events.any fun e =>
    e.turn == g.turnNumber &&
      match e.change with
      | .rules (.damage (.dealt pkts)) =>
        pkts.any (fun pkt => pkt.amount > 0 && pkt.source.id == some id)
      | _ => false

/-- True when `id` has dealt combat damage since it entered the battlefield. -/
def dealtCombatDamage (g : Game) (id : ObjectId) : Bool :=
  g.events.foldl (fun dealt e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) =>
      if after.id == some id then false else dealt
    | .rules (.zone (.created obj _)) =>
      if obj.id == some id then false else dealt
    | .rules (.damage (.dealt pkts)) =>
      dealt || pkts.any (fun pkt => pkt.combat && pkt.amount > 0 && pkt.source.id == some id)
    | _ => dealt) false

/-- Distinct players `id` dealt combat damage to this turn. -/
def combatDamageToPlayers (g : Game) (id : ObjectId) : Array PlayerId :=
  g.events.foldl (fun acc e =>
    if e.turn != g.turnNumber then acc
    else
      match e.change with
      | .rules (.damage (.dealt pkts)) =>
        pkts.foldl (fun acc pkt =>
          if pkt.combat && pkt.amount > 0 && pkt.source.id == some id then
            match pkt.recipient with
            | .player p => if acc.contains p then acc else acc.push p
            | _ => acc
          else acc) acc
      | _ => acc) #[]

/-- True when the optional once-each-turn action of `sourceId` was chosen this turn. -/
def optionalOnceUsedThisTurn (g : Game) (sourceId : ObjectId) : Bool :=
  g.events.any fun e =>
    e.turn == g.turnNumber &&
      match e.change with
      | .rules (.player (.optionalOnceActed _ sid)) => sid == sourceId
      | _ => false

/-- Modes chosen this turn for `sourceId`'s modal triggered ability (CR 700.2). -/
def modesChosenThisTurn (g : Game) (sourceId : ObjectId) : Array Nat :=
  g.events.foldl (fun acc e =>
    if e.turn != g.turnNumber then acc
    else
      match e.change with
      | .rules (.triggerQueue (.modeChosen sid m false)) =>
        if sid == sourceId then acc.push m else acc
      | _ => acc) #[]

/-- Modes chosen for `sourceId`'s lifetime modal triggered ability since it entered (CR 700.2). -/
def modesChosenEver (g : Game) (sourceId : ObjectId) : Array Nat :=
  g.events.foldl (fun acc e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) =>
      if after.id == some sourceId then #[] else acc
    | .rules (.zone (.created obj _)) =>
      if obj.id == some sourceId then #[] else acc
    | .rules (.triggerQueue (.modeChosen sid m true)) =>
      if sid == sourceId then acc.push m else acc
    | _ => acc) #[]

/-- Qualities `p` has beheld this game (CR 701.62). -/
def beheldQualities (g : Game) (p : PlayerId) : Array CardSubtype :=
  g.events.foldl (fun acc e =>
    match e.change with
    | .rules (.player (.beheld q qual)) =>
      if q == p then acc.push qual else acc
    | _ => acc) #[]

/-- True when `p` has attempted to draw a card from an empty library (CR 121.4 / 704.5b). -/
def drewFromEmpty (g : Game) (p : PlayerId) : Bool :=
  g.events.any fun e =>
    match e.change with
    | .rules (.player (.drawFromEmptyAttempted q)) => q == p
    | _ => false

/-- Apply `f` to each living opponent of `controller`. -/
def forEachOpponent (g : Game) (controller : PlayerId) (f : Game → PlayerId → Game) :
    Game :=
  g.livingOpponents controller |>.foldl (fun g pl => f g pl.id) g

/-- Player targets for every member of `ps` who does not have protection
from everything. -/
def playerTargets (g : Game) (ps : Array Player) : Array Target :=
  ps.filter (fun pl => !(g.protectionFromEverything pl.id)) |>.map (fun pl =>
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

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast and is not a copy (CR 707.10). -/
def wasCast (g : Game) (id : ObjectId) : Bool :=
  GameEvent.wasCast g.events id ((g.findObject? id).any (·.isCopy))

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast from a graveyard. -/
def castFromGraveyard (g : Game) (id : ObjectId) : Bool :=
  GameEvent.castFromGraveyard g.events id ((g.findObject? id).any (·.isCopy))

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast from a hand. -/
def castFromHand (g : Game) (id : ObjectId) : Bool :=
  GameEvent.castFromHand g.events id ((g.findObject? id).any (·.isCopy))

/-- Whether `id` was proposed as a prepared spell copy (`way == .alternative "prepare"`). -/
def isPreparedSpell (g : Game) (id : ObjectId) : Bool :=
  GameEvent.isPreparedSpell g.events id

/-- Whether `id` was kicked (or copied from a kicked spell, CR 707.10 / 400.7d). -/
def wasKicked (g : Game) (id : ObjectId) : Bool :=
  GameEvent.wasKicked g.events id

/-- Opponent promised a gift when `id` was cast (or copied, CR 707.10 / 400.7d). -/
def giftPromisedTo? (g : Game) (id : ObjectId) : Option PlayerId :=
  GameEvent.giftPromisedTo? g.events id

/-- Whether `id` was cast using teamwork (or copied from a teamwork spell, CR 707.10 / 400.7d). -/
def teamworkPaid (g : Game) (id : ObjectId) : Bool :=
  GameEvent.teamwork g.events id

/-- Whether `id` was cast for its sneak cost (or copied from a sneak spell, CR 707.10 / 400.7d). -/
def sneakPaid (g : Game) (id : ObjectId) : Bool :=
  (GameEvent.sneakAttackTarget? g.events id).isSome

/-- Attack target of the creature returned to pay `id`'s sneak cost (CR 508.4 / 707.10). -/
def sneakAttackTarget? (g : Game) (id : ObjectId) : Option AttackTarget :=
  (GameEvent.sneakAttackTarget? g.events id).join

/-- Defending player of the creature returned to pay `id`'s sneak cost. -/
def sneakAttackWhom? (g : Game) (id : ObjectId) : Option PlayerId :=
  match g.sneakAttackTarget? id with
  | some (.player p) => some p
  | _ => none

/-- Whether mana from a Treasure was spent to cast `id` (CR 106.6 / 400.7d). -/
def treasureManaSpent (g : Game) (id : ObjectId) : Bool :=
  if (g.findObject? id).any (·.isCopy) then false
  else
    GameEvent.treasureManaSpentOn g.events (GameEvent.stackSpellIdOf g.events id) ||
      GameEvent.treasureManaSpentOn g.events id

/-- Cards exiled from a graveyard to pay the boast activation cost of `abilityId` (MSH 227). -/
def boastExiledOf (g : Game) (abilityId : ObjectId) : Array ObjectId :=
  GameEvent.boastExiledOf g.events abilityId

/-- Value of X for `id`: its stack `chosenX` if on the stack, or else the announced X from `g.events` (CR 107.3a / 400.7d / 707.10). -/
def chosenXOf? (g : Game) (id : ObjectId) : Option Nat :=
  ((g.findObject? id).bind (·.chosenX)).orElse (fun _ => GameEvent.chosenXOf? g.events id)

/-- Last-known `before` snapshot for `id` from `ZoneEvent.moved` (CR 113.7a / 608.2h). -/
def lastKnownBefore? (g : Game) (id : ObjectId) : Option EventObject :=
  GameEvent.lastKnownBefore? g.events id

/-- Last-known power for `id`: stack entry parameter if `id` is on the stack, or else `before.power` from `ZoneEvent.moved` (CR 113.7a / 608.2h). -/
def lastKnownPowerOf? (g : Game) (id : ObjectId) : Option Int :=
  ((g.stack.find? (·.objectId == id)).bind (·.lastKnownPower)).orElse
    (fun _ => (g.lastKnownBefore? id).bind (·.power))

/-- Last-known toughness for `id`: stack entry parameter if `id` is on the stack, or else `before.toughness` from `ZoneEvent.moved` (CR 113.7a / 608.2h). -/
def lastKnownToughnessOf? (g : Game) (id : ObjectId) : Option Int :=
  ((g.stack.find? (·.objectId == id)).bind (·.lastKnownToughness)).orElse
    (fun _ => (g.lastKnownBefore? id).bind (·.toughness))

/-- Controller of `o`, or its last-known battlefield controller from `ZoneEvent.moved` (CR 113.7a / 608.2h). -/
def lastControllerOf? (g : Game) (o : GameObject) : Option PlayerId :=
  if o.zone == .battlefield then o.controller
  else ((g.lastKnownBefore? o.id).bind (·.controller)).orElse (fun _ => o.controller)

/-- Update `lastKnownPower` / `lastKnownToughness` on the `StackEntry` for `objectId`. -/
def setStackEntryLastKnown (g : Game) (objectId : ObjectId)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none) : Game :=
  match g.stack.findIdx? (·.objectId == objectId) with
  | none => g
  | some i =>
    let se := g.stack[i]!
    let se' := { se with
      lastKnownPower := lastKnownPower.orElse (fun _ => se.lastKnownPower)
      lastKnownToughness := lastKnownToughness.orElse (fun _ => se.lastKnownToughness) }
    { g with stack := g.stack.set! i se' }

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
                let rid : ReplacementId := { kind := .extraCounterOnPermanents, object := some o.id, counterKind := some kind }
                specs := specs.push (
                  { id := rid
                    source := some o.id
                    controller := some c
                    affectedPlayer := affected
                    kind := .modifyCountersPut target.id (some kind) 1 1 }, 1, 1)
              -- The Golden Gear: `.fra .extraPlusOneCounter` on a creature you control
              if kind == .plusOnePlusOne && g.isCreature target &&
                  (!o.status.faceDown && (g.staticAbilities o).any (· == .fra .extraPlusOneCounter)) then
                let rid : ReplacementId := { kind := .extraPlusOneCounter, object := some o.id }
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
  if n == 0 || !g.isCreature o then n
  else
    match o.controller with
    | none => n
    | some p =>
      let others := ((g.permanentsOf p).filter (fun x =>
        x.id != o.id && (g.staticAbilities x).any (· == .fra .extraPlusOneCounter))).size
      let self :=
        if !o.status.faceDown && (g.staticAbilities o).any (· == .fra .extraPlusOneCounter) then 1
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
  let noJace := g.cantAttackJaces controller
  let permanentTargets : Array AttackTarget :=
    g.battlefield.filterMap fun o =>
      if !opps.any (fun pl => o.controlledBy pl.id) then none
      else if o.printed.isPlaneswalker then
        if noJace && (o.name.startsWith "Jace" || g.hasSubtype o .jace) then none
        else some (.planeswalker o.id)
      else if g.hasType o .battle then
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
def hasLandsYouControlPT (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any StaticAbility.isLandsYouControlPT

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
def hasHandSizeSetPower (g : Game) (o : GameObject) : Bool :=
  g.cardsInHandPowerUntilEot o ||
    (g.grantedStaticAbilities o).any StaticAbility.isCardsInHandPower

/-- Printed layer-7a “power equal to the number of cards in your hand”
(Minas Tirith Garrison). A layer-7b set overwrites it. -/
def hasPrintedCardsInHandPower (o : GameObject) : Bool :=
  o.printed.staticAbilities.any StaticAbility.isCardsInHandPower

/-- Characteristic power and toughness before pumps, counters, and attached
bonuses: an until-EOT layer-7b set on the battlefield, else lands you control
when that CDA applies (in all zones), else the printed values
(CR 208.2a / 604.3 / 613.3). -/
def hasCreaturesYouControlPower (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any StaticAbility.isCreaturesYouControlPower

/-- Subtype whose count defines this creature's power, if any. -/
def powerEqualSubtype? (g : Game) (o : GameObject) : Option CardSubtype :=
  (g.staticAbilities o).foldl (fun acc ab =>
    match acc, ab with
    | none, .powerEqualSubtypeYouControl s => some s
    | acc, _ => acc) none

/-- True when `o` is Super-Adaptoid's characteristic-defining power (MSH 290). -/
def hasSuperAdaptoidPowerCda (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (fun
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
def hasGraveyardCardTypesPT (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (fun
    | .ptEqualGraveyardCardTypes => true
    | _ => false)

/-- Basic land types among lands `p` controls (domain; CR 305.6). -/
def basicLandTypesAmong (g : Game) (p : PlayerId) : Nat :=
  (#[CardSubtype.plains, .island, .swamp, .mountain, .forest].filter (fun t =>
    (g.permanentsOf p).any (fun o => o.printed.isLand && g.hasSubtype o t))).size

def characteristicBasePT (g : Game) (o : GameObject) : Int × Int :=
  if o.status.faceDown then (2, 2)
  else if o.isOnBattlefield && g.animatedConstruct55 o then
    ((g.setBasePower o).getD 5, (g.setBaseToughness o).getD 5)
  else if (g.staticAbilities o).any (· == StaticAbility.fra .powerEqualsBasicLandTypes) then
    let cda : Int := Int.ofNat (g.basicLandTypesAmong o.you)
    let power := if o.isOnBattlefield then (g.setBasePower o).getD cda else cda
    (power, g.characteristicBase o o.printed.toughness (g.setBaseToughness o))
  else if g.hasGraveyardCardTypesPT o then
    let n : Int := Int.ofNat g.graveyardCardTypeCount
    -- Ruling 776: a layer-7b set (Multiply by Zero) overrides this CDA.
    if o.isOnBattlefield then
      ((g.setBasePower o).getD n, (g.setBaseToughness o).getD (n + 1))
    else (n, n + 1)
  else
  let power :=
    if g.hasHandSizeSetPower o then
      -- Ms. Marvel (ruling 640): this layer-7b set overwrites earlier sets.
      Int.ofNat (g.player o.you).hand.size
    else if hasPrintedCardsInHandPower o then
      let cda : Int := Int.ofNat (g.player o.you).hand.size
      if o.isOnBattlefield then (g.setBasePower o).getD cda else cda
    else if let some subtype := g.powerEqualSubtype? o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p => g.hasSubtype p subtype) |>.size)
      if o.isOnBattlefield then (g.setBasePower o).getD cda else cda
    else if g.hasSuperAdaptoidPowerCda o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p =>
          g.isCreature p && g.isLegendary p) |>.size)
      if o.isOnBattlefield then (g.setBasePower o).getD cda else cda
    else if g.hasCreaturesYouControlPower o then
      let fromTeam : Int :=
        Int.ofNat (g.countCreaturesControlledBy o.you)
      if o.isOnBattlefield then (g.setBasePower o).getD fromTeam else fromTeam
    else
      g.characteristicBase o o.printed.power (g.setBasePower o)
  (power, g.characteristicBase o o.printed.toughness (g.setBaseToughness o))

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
def isLordOf (g : Game) (src target : GameObject) : Bool :=
  src.id != target.id &&
  src.isOnBattlefield &&
  target.isOnBattlefield &&
  src.controller == target.controller &&
  src.controller.isSome &&
  g.isCreature target

/-- Printed legendary, or an Aura that adds the legendary supertype. -/
def treatedAsLegendary (g : Game) (o : GameObject) : Bool :=
  g.isLegendary o ||
    g.battlefield.any (fun a => a.attachedTo == some o.id && (g.staticAbilities a).any fun | .enchantedCreatureGetsHasAndTypes _ _ _ _ => true | _ => false)

/-- Continuous +P/+T `src` currently grants `target` as a lord (CR 604.2 / 613.3c). -/
def grantsStatBonusTo (g : Game) (src target : GameObject) : Int × Int :=
  (g.staticAbilities src).foldl
    (fun acc ab =>
      let sameController :=
        src.isOnBattlefield && target.isOnBattlefield &&
          src.controller == target.controller && src.controller.isSome &&
          g.isCreature target
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
        if src.isOnBattlefield && target.isOnBattlefield && g.isCreature target &&
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
            ab.lordSupertype?.all (g.hasSupertype target) &&
            ab.lordNonSupertype?.all (fun s => !g.hasSupertype target s)
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
def auraStatBonus (g : Game) (aura : GameObject) : Int × Int :=
  (g.staticAbilities aura).foldl
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
            if (g.staticAbilities aura).any (fun
              | .equippedFirstStrikePlusPerInstantSorcery => true
              | _ => false) then
              match aura.controller with
              | some p => (Int.ofNat (g.instantSorceryInGraveyard p), 0)
              | none => (0, 0)
            else (0, 0)
          addStats acc
            (addStats (addStats (g.auraStatBonus aura) glam) ((aura.status.hone : Int), 0))
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
        (g.staticAbilities o).foldl
          (fun acc ab =>
            match ab.selfIfEnduringStory? with
            | some (pw, tw, _) => addStats acc (pw, tw)
            | none => acc)
          (0, 0)

/-- Team +P/+T from “as long as you have an enduring story, creatures you
control get …”. -/
def enduringStoryTeamBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield || !g.isCreature o then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if !g.hasEnduringStory p then (0, 0)
      else
        (g.permanentsOf p).foldl
          (fun acc src =>
            (g.staticAbilities src).foldl
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
        (g.staticAbilities o).foldl
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
        (g.staticAbilities o).foldl (fun acc ab =>
          match ab.thresholdGets? with
          | some (pw, tw) => addStats acc (pw, tw)
          | none => acc) (0, 0)

/-- +P/+0 from graveyards with seven or more cards (Master's Councillors). -/
def fatGraveyardPowerBonus (g : Game) (o : GameObject) : Int :=
  (g.staticAbilities o).foldl (fun acc ab =>
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
    (g.staticAbilities o).foldl (fun acc ab =>
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
  if !g.pumpPerArtifactUntilEot o || !o.isOnBattlefield then (0, 0)
  else
    let n : Int :=
      Int.ofNat ((g.permanentsOf o.you).filter (fun p => p.printed.isArtifact ||
        g.additionalArtifactUntilEot p) |>.size)
    (n, n)

/-- +P/+T from Reality Fracture static abilities: the creature's own
graveyard-count bonuses, grants from its controller's permanents and
emblems, attached Auras and Equipment, and effects lasting until a player's
next turn. -/
def fraStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    let untilTurn := (g.untilTurnOfPump o).foldl (fun acc (_, p, t) => addStats acc (p, t)) (0, 0)
    match o.controller with
    | none => untilTurn
    | some p =>
      let gyIds := (g.player p).graveyard
      let gy := gyIds.size
      let self := (g.staticAbilities o).foldl (fun acc ab =>
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
          (g.staticAbilities src).foldl (fun acc ab =>
            match ab with
            | .fra .creatureTokensGetOneAndVigilance =>
              if g.isCreature o && o.printed.isToken then addStats acc (1, 0) else acc
            | .fra .emblemCreaturesGetTwoTwo => if g.isCreature o then addStats acc (2, 2) else acc
            | _ => acc) acc) (0, 0)
      let team := fromSources (g.permanentsOf p)
      let emblems := fromSources (g.objects.filter (fun e => e.zone == .command && e.controlledBy p))
      let attached := g.battlefield.foldl (fun acc a =>
        if a.attachedTo != some o.id then acc
        else
          (g.staticAbilities a).foldl (fun acc ab =>
            match ab with
            | .fra .equippedHuntersAxe => addStats acc (2, 0)
            | .fra .equippedMedicsKitesail => addStats acc (1, 0)
            | .fra .enchantedGetsOneAndDeathtouch => addStats acc (1, 0)
            | _ => acc) acc) (0, 0)
      let flyingEmblem :=
        if g.isCreature o &&
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
  let (pw, tg) :=
    #[g.characteristicBasePT o, g.pumpOf o, (n, n), g.attachedStatBonus o,
        g.lordStatBonus o, g.enduringStorySelfBonus o, g.enduringStoryTeamBonus o,
        (g.mountainPowerBonus o, (0 : Int)),
        (g.fatGraveyardPowerBonus o, (0 : Int)),
        g.artifactCountPump o, g.leftoverSelfBonus o, g.fraStatBonus o,
        g.thresholdBonus o].foldl
      addStats (0, 0)
  -- Layer 7d: P/T-switching effects (CR 613.4d)
  g.activeEffects.foldl (fun (p, t) (_, s) =>
    match s with
    | .layered scope .ptSwitch d =>
      if g.scopeMatches scope o && g.durationActive d then (t, p) else (p, t)
    | _ => (p, t)) (pw, tg)

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
      (g.staticAbilities a).any (fun ab => ab.enchantedOnlySubtype?.isSome))

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
      let self := (g.staticAbilities o).foldl (fun acc ab =>
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
          if g.dealtCombatDamage o.id then acc else Keywords.merge acc Keyword.hexproof
        | _ => acc) Keywords.none
      let team := (g.permanentsOf p).foldl (fun acc src =>
        let other := src.id != o.id
        (g.staticAbilities src).foldl (fun acc ab =>
          let grant (cond : Bool) (k : Keywords) := if cond then Keywords.merge acc k else acc
          match ab with
          | .fra .creaturesYouControlHaveTrample => grant (g.isCreature o) Keyword.trample
          | .fra .plusOneCreaturesHaveVigilance =>
            grant (g.isCreature o && o.status.plusOnePlusOne > 0) Keyword.vigilance
          | .fra .creatureTokensGetOneAndVigilance =>
            grant (g.isCreature o && o.printed.isToken) Keyword.vigilance
          | .fra .otherPlusOneCreaturesHaveHaste =>
            grant (other && g.isCreature o && o.status.plusOnePlusOne > 0) Keyword.haste
          | .fra .creaturesYouControlHaveHaste => grant (g.isCreature o) Keyword.haste
          | .fra .otherCreaturesHaveTrample => grant (other && g.isCreature o) Keyword.trample
          | .fra .landsHaveHexproof => grant o.printed.isLand Keyword.hexproof
          | .fra .thoptersHaveHaste => grant (g.hasSubtype o .thopter) Keyword.haste
          | .fra .artifactCreaturesHaveVigilance =>
            grant (g.isCreature o && o.printed.isArtifact) Keyword.vigilance
          | _ => acc) acc) Keywords.none
      let attached := g.battlefield.foldl (fun acc a =>
        if a.attachedTo != some o.id then acc
        else
          (g.staticAbilities a).foldl (fun acc ab =>
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
    ((g.staticAbilities o).any (· == StaticAbility.fra .attackDespiteDefenderIfScried) &&
      (g.loggedScried p || g.loggedSurveilled p)) ||
    (g.permanentsOf p).any (fun x => (g.staticAbilities x).any (· == StaticAbility.fra .creaturesAttackDespiteDefender))

/-- Whether `p` currently controls a permanent with any of these subtypes. -/
def controlsAnySubtype (g : Game) (p : PlayerId) (subtypes : Array CardSubtype) : Bool :=
  (g.permanentsOf p).any (fun o => subtypes.any (g.hasSubtype o))

/-- Whether `p` currently controls a legendary creature. -/
def controlsLegendaryCreature (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    g.isCreature o && o.printed.hasSupertype .legendary)

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
        id := { kind := .entersTappedSelf, object := some cur.id }
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
              id := { kind := .entersWithLoyalty, object := some cur.id }
              source := some cur.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .entersWithCountersSelf cur.id .loyalty loy.toNat
            }
      if cur.printed.entersWithPlusOneCounters > 0 then
        specs := specs.push {
          id := { kind := .entersWithPlusOneCounters, object := some cur.id }
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .plusOnePlusOne cur.printed.entersWithPlusOneCounters
        }
      if (g.staticAbilities cur).any (· == .entersWithXPlusOne) then
        let xVal := (cur.chosenX.orElse (fun _ => g.chosenXOf? cur.id)).getD 0
        if xVal > 0 then
          specs := specs.push {
            id := { kind := .entersWithXPlusOne, object := some cur.id }
            source := some cur.id
            controller := some ctrl
            affectedPlayer := ctrl
            kind := .entersWithCountersSelf cur.id .plusOnePlusOne xVal
          }
      if cur.printed.entersWithIndestructibleCounter then
        specs := specs.push {
          id := { kind := .entersWithIndestructibleCounter, object := some cur.id }
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .indestructible 1
        }
      if cur.printed.entersWithShield > 0 then
        specs := specs.push {
          id := { kind := .entersWithShield, object := some cur.id }
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .shield cur.printed.entersWithShield
        }
      if cur.printed.entersWithHopePerCreature then
        let others := ((g.creaturesControlledBy ctrl).filter (·.id != cur.id)).size
        let selfCount := if g.isCreature cur then 1 else 0
        let totalHope := others + selfCount
        if totalHope > 0 then
          specs := specs.push {
            id := { kind := .entersWithHopePerCreature, object := some cur.id }
            source := some cur.id
            controller := some ctrl
            affectedPlayer := ctrl
            kind := .entersWithCountersSelf cur.id .hope totalHope
          }
      if cur.printed.saga.isSome then
        specs := specs.push {
          id := { kind := .entersWithSagaLore, object := some cur.id }
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .lore 1
        }
    -- 616.1d: intrinsic daybound / back-face-up replacement (CR 702.145b / 712.14)
    if !cur.status.transformed && cur.printed.otherFace.isSome &&
        (forceBackFace || (!leavingPlay && cur.printed.daybound && g.isNight)) then
      specs := specs.push {
        id := { kind := .entersBackFaceUp, object := some cur.id }
        source := some cur.id
        controller := some ctrl
        affectedPlayer := ctrl
        kind := .entersBackFaceUp cur.id
      }
    -- 616.1e: Arwen, Weaver of Hope (`othersEnterWithPlusOneEqualToughness`)
    if applyHope && !cur.status.faceDown && g.isCreature cur then
      for weaver in g.permanentsOf ctrl do
        if weaver.id != cur.id && weaver.printed.othersEnterWithPlusOneEqualToughness &&
            weaver.timestamp < asOf then
          let bonus := (g.snapshotToughness weaver).toNat
          if bonus > 0 then
            specs := specs.push {
              id := { kind := .othersEnterWithPlusOneEqualToughness, object := some weaver.id }
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
              status := { cur.status with transformed := true } }
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
    else { cur with status := cur.status.withCounterBag bag }
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
  (g.staticAbilities blocker).all (fun ab =>
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
          ((g.staticAbilities aura).foldl (fun k ab =>
            Keywords.merge k ab.hostKeywords) Keywords.none)
      else acc) Keywords.none

/-- During your turn, creatures you control that are equipped gain these
keywords (Long-Lost Lances). -/
def equippedDuringYourTurnKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield || !g.isCreature o || g.attachedEquipmentCount o == 0 then
    Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      if g.activePlayer != p then Keywords.none
      else
        (g.permanentsOf p).foldl (fun acc src =>
          (g.staticAbilities src).foldl (fun acc ab =>
            Keywords.merge acc (ab.equippedTeamKeywordsDuringYourTurn)) acc)
          Keywords.none

def leftoverGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  let self :=
    (g.staticAbilities o).foldl (fun acc ab =>
      match ab with
      | .flyingIfPlusOneThisTurn =>
        if g.gotPlusOneThisTurn o.id then Keywords.merge acc Keyword.flying else acc
      | _ => acc) Keywords.none
  let fromTeam :=
    match o.controller with
    | none => Keywords.none
    | some p =>
      (g.permanentsOf p).foldl (fun acc src =>
        (g.staticAbilities src).foldl (fun acc ab =>
          match ab with
          | .creaturesWithPlusOneHave k =>
            if g.isCreature o && o.status.plusOnePlusOne > 0 then
              Keywords.merge acc k
            else acc
          | .attackingTokensHave k =>
            if o.isOnBattlefield && o.status.attacking && o.printed.isToken then
              Keywords.merge acc k
            else acc
          | _ => acc) acc) Keywords.none
  Keywords.merge (Keywords.merge self fromTeam) (g.fraGrantedKeywords o)

/-- During the Equipment's controller's turn, the equipped creature has
hexproof and can't be blocked (Bilbo's Ring). -/
def equippedHexproofUnblockableThisTurn (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        (g.staticAbilities eq).any (fun
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
        (g.staticAbilities eq).any StaticAbility.equippedCantBeBlocked)

/-- Whether `src` currently grants trample to `target` (CR 604.2). -/
def grantsTrampleTo (g : Game) (src target : GameObject) : Bool :=
  g.isLordOf src target &&
  (g.staticAbilities src).any (fun ab =>
    match ab.trampleSubtypes? with
    | some subtypes => subtypes.any (fun s => g.hasSubtype target s)
    | none => false)

/-- Lore counters among Sagas `p` controls. -/
def loreAmongSagas (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.printed.saga.isSome then acc + o.status.lore else acc) 0

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

/-- Whether `o` has indestructible from `indestructibleIfArtifactCreatureOrPlan`. -/
def leftoverIndestructible (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    (g.staticAbilities o).any (fun
      | .indestructibleIfArtifactCreatureOrPlan => true
      | _ => false) &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun x =>
        (g.isCreature x && (g.isArtifact x || x.printed.isArtifact)) || g.hasSubtype x .plan)

/-- The Reaver Cleaver: combat damage to a player or planeswalker makes Treasures. -/
def equippedCreatesCombatTreasures (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        (g.staticAbilities eq).any (fun
          | .equippedGetsTrampleAndCombatTreasures _ _ => true
          | _ => false))

private def keywordCounterTable : Array (CounterKind × Keywords) :=
  #[(.trample, Keyword.trample),
    (.indestructible, Keyword.indestructible),
    (.lifelink, Keyword.lifelink),
    (.shadow, Keyword.shadow),
    (.haste, Keyword.haste),
    (.vigilance, Keyword.vigilance),
    (.flying, Keyword.flying),
    (.menace, Keyword.menace),
    (.reach, Keyword.reach),
    (.deathtouch, Keyword.deathtouch),
    (.firstStrike, Keyword.firstStrike),
    (.doubleStrike, Keyword.doubleStrike)]

/-- Keywords granted to `o` by conditional self-targeting static abilities in `abs`. -/
private def evalSelfStaticKeywords (g : Game) (o : GameObject) (abs : Array StaticAbility) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    abs.foldl (fun acc ab =>
      let k1 : Keywords :=
        match ab with
        | .flyingIfPlusOneThisTurn =>
          if g.gotPlusOneThisTurn o.id then Keyword.flying else Keywords.none
        | .indestructibleIfArtifactCreatureOrPlan =>
          match o.controller with
          | none => Keywords.none
          | some p =>
            if (g.permanentsOf p).any (fun x =>
                (g.isCreature x && (g.isArtifact x || x.printed.isArtifact)) || g.hasSubtype x .plan) then
              Keyword.indestructible
            else Keywords.none
        | .fra .firstStrikeDuringYourTurn =>
          if o.controller == some g.activePlayer then Keyword.firstStrike else Keywords.none
        | .fra .vigilanceIfJace =>
          match o.controller with
          | some p => if g.controlsJacePlaneswalker p then Keyword.vigilance else Keywords.none
          | none => Keywords.none
        | .fra .powerAndFlyingIfSevenInGraveyard =>
          match o.controller with
          | some p => if (g.player p).graveyard.size >= 7 then Keyword.flying else Keywords.none
          | none => Keywords.none
        | .fra .flyingHasteIfOpponentDealtNoncombat =>
          match o.controller with
          | some p =>
            if (g.livingOpponents p).any (fun opp => g.loggedNoncombatDamage opp.id) then
              Keyword.flying.merge Keyword.haste
            else Keywords.none
          | none => Keywords.none
        | .fra .hexproofUntilCombatDamage =>
          if g.dealtCombatDamage o.id then Keywords.none else Keyword.hexproof
        | _ => Keywords.none
      let k2 : Keywords :=
        match ab.selfIfEnduringStory? with
        | some (_, _, k) =>
          match o.controller with
          | some p => if g.hasEnduringStory p then k else Keywords.none
          | none => Keywords.none
        | none => Keywords.none
      let k3 : Keywords :=
        match ab.hasteIfOtherSubtype? with
        | some t =>
          match o.controller with
          | some p =>
            if (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t) then
              Keyword.haste
            else Keywords.none
          | none => Keywords.none
        | none => Keywords.none
      let k4 : Keywords :=
        match ab.lifelinkIfOtherSubtype? with
        | some t =>
          match o.controller with
          | some p =>
            if (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t) then
              Keyword.lifelink
            else Keywords.none
          | none => Keywords.none
        | none => Keywords.none
      Keywords.merge (Keywords.merge (Keywords.merge (Keywords.merge acc k1) k2) k3) k4) Keywords.none

private structure Layer6Entry where
  idx : Nat
  ts : Nat × Nat
  scope : ObjectScope
  rem : AbilityRemoval
  addKw : Keywords
deriving Inhabited

/-- Evaluated keywords of `o` in Layer 6 (CR 613.1f / 613.7 / 613.8), applying
intrinsic abilities, all 12 keyword counters (CR 613.7c), attached Auras and
Equipment (CR 613.7e), continuous team/lord/emblem grants (CR 613.7d), and
one-shot Layer 6 continuous effects (CR 613.7b) in timestamp / dependency order. -/
def currentKeywords (g : Game) (o : GameObject) : Keywords :=
  let initKw : Keywords :=
    if o.status.faceDown then
      -- Face-down permanents have no printed abilities (CR 708.2a).
      Keywords.none
    else
      let printedKw : Keywords :=
        if o.printed.prowessInstances > 0 then
          { o.printed.keywords with prowess := true }
        else o.printed.keywords
      let loreKw : Keywords :=
        if g.loreThresholdProtection o then { hexproof := true, indestructible := true }
        else Keywords.none
      Keywords.merge (Keywords.merge printedKw loreKw)
        (g.evalSelfStaticKeywords o o.printed.staticAbilities)
  let scopeMatchesL6 (cur : Keywords) (sc : ObjectScope) : Bool :=
    match sc with
    | .objects ids => ids.contains o.id
    | .creaturesControlledBy p => o.isOnBattlefield && o.controlledBy p && g.isCreature o
    | .creaturesWithout kw =>
      o.isOnBattlefield && g.isCreature o && Keywords.merge cur kw != cur
    | .permanentsOfSubtype p s => o.isOnBattlefield && o.controlledBy p && g.hasSubtype o s
  let applyStep (cur : Keywords) (e : Layer6Entry) : Keywords :=
    let base :=
      match e.rem with
      | .none => cur
      | .all => Keywords.none
      | .loseIndestructible => if o.isOnBattlefield then { cur with indestructible := false } else cur
    Keywords.merge base e.addKw
  Id.run do
    let mut raw : Array Layer6Entry := #[]
    for (k, kw) in keywordCounterTable do
      if o.status.counterCount k > 0 then
        raw := raw.push {
          idx := raw.size
          ts := g.counterTimestamp o.id k
          scope := .objects #[o.id]
          rem := .none
          addKw := kw
        }
    if o.isOnBattlefield then
      for att in g.battlefield do
        if att.attachedTo == some o.id then
          let attAbs := g.staticAbilities att
          let strips := attAbs.any fun
            | .enchantedLosesAbilitiesDoesntUntap => true
            | .enchantedLosesAbilitiesCantUntap => true
            | _ => false
          let addKw := attAbs.foldl (fun acc ab =>
            let extra : Keywords :=
              match ab with
              | .fra .equippedMedicsKitesail => Keyword.flying
              | .fra .enchantedGetsOneAndDeathtouch => Keyword.deathtouch
              | .equippedHexproofUnblockableDuringYourTurn =>
                if att.controller == some g.activePlayer then
                  { hexproof := true, cantBeBlocked := true }
                else Keywords.none
              | .equippedGetsTrampleAndCombatTreasures _ _ => Keyword.trample
              | _ => Keywords.none
            let unblockable : Keywords :=
              if ab.equippedCantBeBlocked then Keyword.cantBeBlocked else Keywords.none
            Keywords.merge (Keywords.merge (Keywords.merge acc ab.hostKeywords) extra) unblockable) Keywords.none
          if strips || addKw != Keywords.none then
            raw := raw.push {
              idx := raw.size
              ts := g.attachmentTimestamp att o.id
              scope := .objects #[o.id]
              rem := if strips then .all else .none
              addKw := addKw
            }
      for src in g.battlefield do
        let trampleGrant := if g.grantsTrampleTo src o then Keyword.trample else Keywords.none
        let teamGrant : Keywords :=
          match o.controller with
          | none => Keywords.none
          | some p =>
            if !src.controlledBy p then Keywords.none
            else
              let other := src.id != o.id
              let fromAbs := (g.staticAbilities src).foldl (fun acc ab =>
                let eqTeam :=
                  if g.isCreature o && g.attachedEquipmentCount o > 0 && g.activePlayer == p then
                    ab.equippedTeamKeywordsDuringYourTurn
                  else Keywords.none
                let menacePlus :=
                  if ab.creaturesWithPlusOneHaveMenace && o.status.plusOnePlusOne > 0 then
                    Keyword.menace
                  else Keywords.none
                let byPat : Keywords :=
                  match ab with
                  | .creaturesWithPlusOneHave k =>
                    if g.isCreature o && o.status.plusOnePlusOne > 0 then k else Keywords.none
                  | .attackingTokensHave k =>
                    if o.status.attacking && o.printed.isToken then k else Keywords.none
                  | .hexproofIfPlusOneThisTurn =>
                    if g.isCreature o && g.gotPlusOneThisTurn o.id then Keyword.hexproof else Keywords.none
                  | .youAndOtherSubtypeHaveHexproofIfShield subtype =>
                    if src.status.shield > 0 && other && g.hasSubtype o subtype then Keyword.hexproof else Keywords.none
                  | .fra .creaturesYouControlHaveTrample =>
                    if g.isCreature o then Keyword.trample else Keywords.none
                  | .fra .plusOneCreaturesHaveVigilance =>
                    if g.isCreature o && o.status.plusOnePlusOne > 0 then Keyword.vigilance else Keywords.none
                  | .fra .creatureTokensGetOneAndVigilance =>
                    if g.isCreature o && o.printed.isToken then Keyword.vigilance else Keywords.none
                  | .fra .otherPlusOneCreaturesHaveHaste =>
                    if other && g.isCreature o && o.status.plusOnePlusOne > 0 then Keyword.haste else Keywords.none
                  | .fra .creaturesYouControlHaveHaste =>
                    if g.isCreature o then Keyword.haste else Keywords.none
                  | .fra .otherCreaturesHaveTrample =>
                    if other && g.isCreature o then Keyword.trample else Keywords.none
                  | .fra .landsHaveHexproof =>
                    if g.isLand o || o.printed.isLand then Keyword.hexproof else Keywords.none
                  | .fra .thoptersHaveHaste =>
                    if g.hasSubtype o .thopter then Keyword.haste else Keywords.none
                  | .fra .artifactCreaturesHaveVigilance =>
                    if g.isCreature o && (g.isArtifact o || o.printed.isArtifact) then Keyword.vigilance else Keywords.none
                  | _ => Keywords.none
                Keywords.merge (Keywords.merge (Keywords.merge acc eqTeam) menacePlus) byPat) Keywords.none
              let toxicKw :=
                if o.printed.toxic > 0 && src.printed.corruptedToxicLifelink &&
                    (g.livingOpponents p).any (fun opp => opp.poison >= 3) then
                  Keyword.lifelink
                else Keywords.none
              Keywords.merge fromAbs toxicKw
        let srcKw := Keywords.merge trampleGrant teamGrant
        if srcKw != Keywords.none then
          raw := raw.push {
            idx := raw.size
            ts := g.objectEntryTimestamp src
            scope := .objects #[o.id]
            rem := .none
            addKw := srcKw
          }
      if let some p := o.controller then
        for emb in g.objects do
          if emb.zone == .command && emb.controlledBy p && g.isCreature o &&
              emb.printed.grantTeamPlusTwoFlying then
            raw := raw.push {
              idx := raw.size
              ts := g.objectEntryTimestamp emb
              scope := .objects #[o.id]
              rem := .none
              addKw := Keyword.flying
            }
    for pos in [0:g.activeEffects.size] do
      let (eid, s) := g.activeEffects[pos]!
      match s with
      | .layered sc (.abilities add rem) d =>
        if g.durationActive d then
          let fsKw :=
            if add.firstStrikeOnYourTurn && o.controller == some g.activePlayer then
              Keyword.firstStrike
            else Keywords.none
          let stKw := g.evalSelfStaticKeywords o add.staticAbilities
          let addKw := Keywords.merge (Keywords.merge add.keywords fsKw) stKw
          if rem != .none || addKw != Keywords.none then
            raw := raw.push {
              idx := raw.size
              ts := g.effectTimestamp eid pos
              scope := sc
              rem := rem
              addKw := addKw
            }
      | _ => pure ()
    let sorted := raw.qsort fun a b =>
      if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
      else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
      else a.idx < b.idx
    let mut rem := sorted
    let mut cur := initKw
    for _ in [0:sorted.size] do
      let applicable := rem.filter (fun e => scopeMatchesL6 cur e.scope)
      if applicable.isEmpty then break
      let dependsOn (a b : Layer6Entry) : Bool :=
        a.idx != b.idx &&
          scopeMatchesL6 cur a.scope != scopeMatchesL6 (applyStep cur b) a.scope
      let chosen :=
        (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
      cur := applyStep cur chosen
      rem := rem.filter (fun e => e.idx != chosen.idx)
    return cur

/-- Haste from printed text, attachments, enduring story, counters, or
“haste as long as you control another …”. Lost abilities are omitted. -/
def hasHaste (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).haste

def canAttack (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && g.isCreature o &&
  o.controlledBy g.activePlayer &&
  !o.status.tapped && (!(g.currentKeywords o).defender || g.mayAttackDespiteDefender o) &&
  !(o.status.summoningSick && !g.hasHaste o) &&
  !g.enchantedCantAttackOrBlock o &&
  (g.staticAbilities o).all (fun ab =>
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
def hasPrintedOrEot (g : Game) (o : GameObject) (sel : Keywords → Bool) : Bool :=
  sel (g.printedOrUntilEot o)

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
        (g.staticAbilities src).any (fun
          | .attackingTokensHave k => k.firstStrike
          | _ => false))

/-- Whether `o` has first strike, printed or granted (CR 702.7). -/
def hasFirstStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.firstStrike) || g.hasKeyword o (·.doubleStrike)

/-- Whether `o` has double strike (CR 702.4). -/
def hasDoubleStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.doubleStrike)

/-- Whether `o` has islandwalk, printed or granted (CR 702.14). -/
def hasIslandwalk (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.islandwalk)

/-- Whether `o` can't be blocked, printed or granted in Layer 6
(CR 509.1b / 611.2a / 613.1f), or while its power is at most a listed value. -/
def hasCantBeBlocked (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.cantBeBlocked) ||
  (o.isOnBattlefield &&
    (g.staticAbilities o).any (fun ab =>
      match ab.cantBeBlockedIfPowerAtMost? with
      | some n => g.snapshotPower o <= n
      | none => false)) ||
  (o.isOnBattlefield && g.isCreature o &&
    (g.snapshotPower o <= 1 || g.snapshotToughness o <= 1) &&
    match o.controller with
    | some p =>
      (g.permanentsOf p).any (fun src =>
        (g.staticAbilities src).any (fun
          | .smallCreaturesYouControlUnblockable => true
          | _ => false))
    | none => false)

/-- Whether `o` has lifelink, printed, granted, or from a lifelink counter (CR 702.15). -/
def hasLifelink (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.lifelink)

/-- Whether `o` has menace, printed, granted, or from a menace counter (CR 702.111).
Pairwise `canBlock` stays true; the two-or-more restriction is checked on the
declaration as a whole (CR 509.1c). -/
def hasMenace (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.menace)

/-- Minimum number of creatures required to block `o`, or `0` if unrestricted.
Menace is 2; Troll of Khazad-dûm is 3. -/
def minBlockersRequired (g : Game) (o : GameObject) : Nat :=
  let fromStatic :=
    (g.staticAbilities o).foldl (fun acc ab =>
      match ab.cantBeBlockedExcept? with
      | some n => max acc n
      | none => acc) 0
  max fromStatic (if g.hasMenace o then 2 else 0)

/-- Maximum number of creatures that may block `o`, if a static caps it. -/
def maxBlockersAllowed (g : Game) (o : GameObject) : Option Nat :=
  (g.staticAbilities o).foldl (fun acc ab =>
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
    (g.staticAbilities o).any (fun
      | .flyingCantAttackYouOrBlockYours => true
      | _ => false))

/-- Whether `blocker` may be assigned to `attacker` as one creature in a
declaration (CR 509.1b). Menace is not a pairwise restriction. -/
def canBlock (g : Game) (blocker attacker : GameObject) : Bool :=
  let defender := g.defendingPlayerOf attacker
  let islandwalkUnblockable :=
    g.hasIslandwalk attacker &&
      (g.permanentsOf defender).any (fun o => g.hasSubtype o .island)
  blocker.isOnBattlefield && g.isCreature blocker &&
  blocker.controlledBy defender && !blocker.status.tapped &&
  blocker.status.blocking.isEmpty && !g.cantBlockUntilEot blocker &&
  !blocker.printed.cantBlock &&
  g.mayDeclareAsBlocker blocker &&
  !g.enchantedCantAttackOrBlock blocker &&
  (!g.creaturesWithoutFlyingCantBlock || g.hasFlying blocker) &&
  attacker.status.attacking &&
  !g.hasCantBeBlocked attacker &&
  !islandwalkUnblockable &&
  !((g.staticAbilities attacker).any StaticAbility.blocksTokens &&
    blocker.printed.isToken) &&
  !((g.staticAbilities attacker).any (fun ab =>
      match ab.cantBeBlockedByPowerAtMost? with
      | some n => g.snapshotPower blocker <= n
      | none => false)) &&
  !((g.staticAbilities attacker).any (fun ab =>
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
  !(match g.cantBeBlockedByPlayer attacker with
    | some pid => blocker.controlledBy pid
    | none => false) &&
  !(g.cantBeBlockedExceptByHasteUntilEot attacker && !g.hasHaste blocker)

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

def hasHexproof (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.hexproof)

/-- The player has hexproof from opponents (Captain America, Super-Soldier). -/
def playerHasHexproof (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun src =>
    src.status.shield > 0 &&
      (g.staticAbilities src).any (fun
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
    !(g.protectionFromEverything target) && !typeBlock

/-- Whether `o` has deathtouch, printed, granted, or from a deathtouch counter (CR 702.2). -/
def hasDeathtouch (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.deathtouch)

def hasIndestructible (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.indestructible)

/-- Mana value of `o` (CR 202.3). `{X}` is the chosen value while the object
is on the stack and 0 otherwise (rulings 178 / 185 / 186). -/
def objectManaValue (_g : Game) (o : GameObject) : Nat :=
  let printed := o.printed.manaValue
  if o.zone != .stack then printed
  else printed + o.chosenX.getD 0

/-- Whether `o` has trample, printed, granted, from a trample counter, or from a lord (CR 702.19). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.trample)

/-- Current Layer 6 keywords of `o`, including printed keywords, keyword
counters, static grants, and continuous effects in timestamp order
(CR 613.1f / 613.7). -/
def effectiveKeywords (g : Game) (o : GameObject) : Keywords :=
  g.currentKeywords o

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
    (g.permanentsOf p).filter (fun o => g.isCreature o && o.status.attacking)
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

/-- Snapshot `o` as an `EventObject` with Layer 1–7 characteristics (CR 113.7a / 613.1). -/
def snapshot (g : Game) (o : GameObject) : EventObject :=
  let base := o.asEvent
  let extraSubtypes : Array CardSubtype :=
    #[.hero, .villain, .goblin, .orc, .army, .elf, .merfolk].foldl
      (fun acc s => if g.hasSubtype o s && !acc.contains s then acc.push s else acc)
      (g.currentSubtypes o)
  let pw : Option Int :=
    if o.zone == .battlefield then
      if g.isCreature o || o.printed.power.isSome then some (g.snapshotPower o) else none
    else
      (g.lastKnownPowerOf? o.id).orElse (fun _ =>
        if g.isCreature o || o.printed.power.isSome then some (g.snapshotPower o) else none)
  let tg : Option Int :=
    if o.zone == .battlefield then
      if g.isCreature o || o.printed.toughness.isSome then some (g.snapshotToughness o) else none
    else
      (g.lastKnownToughnessOf? o.id).orElse (fun _ =>
        if g.isCreature o || o.printed.toughness.isSome then some (g.snapshotToughness o) else none)
  let curKw := g.currentKeywords o
  { base with
    colors := g.colors o
    types := g.types o
    supertypes := g.supertypes o
    subtypes := extraSubtypes
    power := pw
    toughness := tg
    staticAbilities := g.staticAbilities o
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
    (g.staticAbilities o).foldl (fun acc ab =>
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
    (g.staticAbilities src).any (fun
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
  | .sourceWasCast => source.any (fun s => g.wasCast s.id)
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
        ab.opts.anotherSupertype.all (g.hasSupertype o ·)
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
    | .protectionEverything => source.any (fun s => g.wasCast s.id)
    | .death .deathtouchOppSac => cause.any (g.hasDeathtouch ·)
    | .resource .plusOneCreateInsectOnce => cause.any (g.isCreature ·)
    | .resource .plusOneOnThisOnce =>
      cause.any (fun c => g.isCreature c && some c.id != source.map (·.id))
    | .resource .plusOneOnHeroesCreateWall =>
      cause.any (fun c => some c.id != source.map (·.id) && c.controlledBy controller &&
        g.hasSubtype c .hero)
    | .watch .sheHulkRedirectOnce => !g.loggedSheHulkDealtDamage
    | _ => true
  powerOk && otherOk && lifeOk && hulklingOk && causeOk && interveningOk &&
    g.fraInterveningHolds controller ab source cause &&
    g.fraConditionHolds controller ab.opts.fraCondition source (cause.map (·.status))

private structure TriggerAbEntry where
  idx : Nat
  ts : Nat × Nat
  rem : AbilityRemoval
  add : Array TriggeredAbility
deriving Inhabited

/-- Evaluated triggered abilities of `o` in Layer 6 (CR 613.1f / 613.7).
Printed triggers start at `(0, 0)` and attached Aura/Equipment grants or
removals (`attachmentTimestamp`) and active `.abilities` continuous effects
(`effectTimestamp`) apply in timestamp order. -/
def triggeredAbilities (g : Game) (o : GameObject) : Array TriggeredAbility :=
  if o.status.faceDown then #[]
  else
    let scopeOk (sc : ObjectScope) : Bool :=
      match sc with
      | .objects ids => ids.contains o.id
      | .creaturesControlledBy p => o.isOnBattlefield && o.controlledBy p && g.isCreature o
      | .creaturesWithout kw =>
        o.isOnBattlefield && g.isCreature o &&
          Keywords.merge (g.currentKeywords o) kw != g.currentKeywords o
      | .permanentsOfSubtype p s => o.isOnBattlefield && o.controlledBy p && g.hasSubtype o s
    Id.run do
      let mut raw : Array TriggerAbEntry := #[]
      if o.isOnBattlefield then
        for att in g.battlefield do
          if att.attachedTo == some o.id then
            let attAbs := g.staticAbilities att
            let strips := attAbs.any fun
              | .enchantedLosesAbilitiesDoesntUntap => true
              | .enchantedLosesAbilitiesCantUntap => true
              | _ => false
            let addTrigs : Array TriggeredAbility :=
              attAbs.foldl (fun acc ab =>
                match ab with
                | .fra .equippedHuntersAxe =>
                  acc.push (TriggeredAbility.fra .attack
                    "Whenever this creature attacks, it gains your choice of trample or deathtouch until end of turn."
                    (.chooseKeyword [0, 3]))
                | .fra .equippedMedicsKitesail =>
                  acc.push (TriggeredAbility.fra .attack
                    "Whenever this creature attacks, you gain 1 life." (.gainLife 1))
                | _ => acc) #[]
            if strips || !addTrigs.isEmpty then
              raw := raw.push {
                idx := raw.size
                ts := g.attachmentTimestamp att o.id
                rem := if strips then .all else .none
                add := addTrigs
              }
      for pos in [0:g.activeEffects.size] do
        let (eid, s) := g.activeEffects[pos]!
        match s with
        | .layered sc (.abilities add rem) d =>
          if scopeOk sc && g.durationActive d &&
              (rem == .all || !add.triggeredAbilities.isEmpty) then
            raw := raw.push {
              idx := raw.size
              ts := g.effectTimestamp eid pos
              rem := rem
              add := add.triggeredAbilities
            }
        | _ => pure ()
      let sorted := raw.qsort fun a b =>
        if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
        else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
        else a.idx < b.idx
      let mut acc := o.printed.triggeredAbilities
      for e in sorted do
        if e.rem == .all then acc := #[]
        acc := acc ++ e.add
      return acc

def matchingTriggers (g : Game) (o : GameObject) (e : TriggerEvent) : Array TriggeredAbility :=
  (g.triggeredAbilities o).filter (·.firesOn e)

private structure ProwessEntry where
  idx : Nat
  ts : Nat × Nat
  rem : AbilityRemoval
  addCount : Nat
deriving Inhabited

/-- Prowess triggers of `o`, one for each instance evaluated in Layer 6
timestamp order (CR 613.1f / 613.7 / 702.108). -/
def prowessTriggers (g : Game) (o : GameObject) : Array TriggeredAbility :=
  if !o.isOnBattlefield then #[]
  else
    let initCount : Nat :=
      if o.status.faceDown then 0
      else
        max o.printed.prowessInstances (if o.printed.keywords.prowess then 1 else 0) +
          (if (g.evalSelfStaticKeywords o o.printed.staticAbilities).prowess then 1 else 0)
    let scopeOk (sc : ObjectScope) : Bool :=
      match sc with
      | .objects ids => ids.contains o.id
      | .creaturesControlledBy p => o.isOnBattlefield && o.controlledBy p && g.isCreature o
      | .creaturesWithout kw =>
        o.isOnBattlefield && g.isCreature o &&
          Keywords.merge (g.currentKeywords o) kw != g.currentKeywords o
      | .permanentsOfSubtype p s => o.isOnBattlefield && o.controlledBy p && g.hasSubtype o s
    let n : Nat := Id.run do
      let mut raw : Array ProwessEntry := #[]
      for att in g.battlefield do
        if att.attachedTo == some o.id then
          let attAbs := g.staticAbilities att
          let strips := attAbs.any fun
            | .enchantedLosesAbilitiesDoesntUntap => true
            | .enchantedLosesAbilitiesCantUntap => true
            | _ => false
          let addCount := attAbs.foldl (fun acc ab =>
            acc + (if ab.hostKeywords.prowess then 1 else 0)) 0
          if strips || addCount > 0 then
            raw := raw.push {
              idx := raw.size
              ts := g.attachmentTimestamp att o.id
              rem := if strips then .all else .none
              addCount
            }
      if let some p := o.controller then
        for src in g.battlefield do
          if src.controlledBy p then
            let teamCount := (g.staticAbilities src).foldl (fun acc ab =>
              let eqProwess :=
                g.isCreature o && g.attachedEquipmentCount o > 0 && g.activePlayer == p &&
                  ab.equippedTeamKeywordsDuringYourTurn.prowess
              let patProwess :=
                match ab with
                | .creaturesWithPlusOneHave k =>
                  g.isCreature o && o.status.plusOnePlusOne > 0 && k.prowess
                | .attackingTokensHave k =>
                  o.status.attacking && o.printed.isToken && k.prowess
                | _ => false
              acc + (if eqProwess then 1 else 0) + (if patProwess then 1 else 0)) 0
            if teamCount > 0 then
              raw := raw.push {
                idx := raw.size
                ts := g.objectEntryTimestamp src
                rem := .none
                addCount := teamCount
              }
      for pos in [0:g.activeEffects.size] do
        let (eid, s) := g.activeEffects[pos]!
        match s with
        | .layered sc (.abilities add rem) d =>
          if scopeOk sc && g.durationActive d then
            let addCount :=
              (if add.keywords.prowess then 1 else 0) +
                (if (g.evalSelfStaticKeywords o add.staticAbilities).prowess then 1 else 0)
            if rem == .all || addCount > 0 then
              raw := raw.push {
                idx := raw.size
                ts := g.effectTimestamp eid pos
                rem := rem
                addCount
              }
        | _ => pure ()
      let sorted := raw.qsort fun a b =>
        if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
        else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
        else a.idx < b.idx
      let mut cnt := initCount
      for e in sorted do
        if e.rem == .all then cnt := 0
        cnt := cnt + e.addCount
      return cnt
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
      else if ab.optionalOnceEachTurn && post.optionalOnceUsedThisTurn source.id then (w, fs)
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
          (board.matchingTriggers source event ++
            (board.prowessTriggers source).filter (·.firesOn event)).filter keep
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
          (board.triggeredAbilities o).foldl (fun (w, fs) ab =>
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
          for ab in post.matchingTriggers src .youPutPlusOne do
            let matchesAb (obj : GameObject) : Bool :=
              match ab.shared with
              | .resource .plusOneOnHeroesCreateWall =>
                obj.id != src.id && obj.controlledBy q && post.hasSubtype obj .hero
              | .resource .plusOneOnThisOnce =>
                post.isCreature obj && obj.id != src.id
              | _ => post.isCreature obj
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
              transformed := eo.transformed }
          attachedTo := eo.attachedTo
          chosenX := eo.chosenX
          isCopy := eo.isCopy }
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
                if post.retainsPrintedAbilities postObj then
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
            if post.isCreature entered then
              let (w, fs) :=
                queueCtrl post ctrl .anotherCreatureYouControlEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            -- Subtype enter triggers (Balin, Fíli, Kíli, Thorin)
            for src in post.permanentsOf ctrl do
              let self := src.id == entered.id
              for ab in post.triggeredAbilities src do
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
            if post.isCreature entered then
              let (w, fs) := queueCtrl post ctrl .creatureYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for sub in post.subtypes entered do
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
            if (post.types entered).contains .artifact then
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
            if !entered.printed.isToken && (post.types entered).contains .artifact then
              let (w, fs) :=
                queueCtrl post ctrl .anotherNontokenArtifactEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            let isCreature := post.isCreature entered
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
                pre.isCreature beforeObj ||
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
            if pre.isCreature beforeObj && (beforeObj.status.hasCounters || !before.counters.isEmpty) then
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
            if post.isCreature entered then
              let (w, fs) :=
                queueCtrl post p .anotherCreatureYouControlEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for src in post.permanentsOf p do
              let self := src.id == entered.id
              for ab in post.triggeredAbilities src do
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
            if post.isCreature entered then
              let (w, fs) := queueCtrl post p .creatureYouControlEnters (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            for sub in post.subtypes entered do
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
            if (post.types entered).contains .artifact then
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
            if !entered.printed.isToken && (post.types entered).contains .artifact then
              let (w, fs) :=
                queueCtrl post p .anotherNontokenArtifactEnters
                  (excludeId := some entered.id) (cause := some entered)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
            let isCreature := post.isCreature entered
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
                  post.chosenXOf? prop.spellId)).orElse
                  (fun _ => post.chosenXOf? afterObj.id)
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
              pre.becameTappedThisTurn tObj.id ||
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
                    if post.isCreature srcObj then
                      for o in post.permanentsOf pid do
                        for ab in post.triggeredAbilities o do
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
                      if post.isCreature srcObj then
                        for o in post.permanentsOf pid do
                          for ab in post.triggeredAbilities o do
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
              if post.isCreature recObj && pktEv.matchesTrigger c recObj.id .creatureYouControlDealtDamage then
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
        | .player (.manaAdded _ _)
        | .player (.manaSpent _ _ _)
        | .player (.manaEmptied _ _ _)
        | .player (.lookedAt _ _)
        | .player (.revealed _ _)
        | .player (.searched _ _ _)
        | .player (.shuffled _ _)
        | .player (.beheld _ _)
        | .player (.becameMonarch _ _)
        | .player (.gainedDesignation _ _)
        | .player (.lost _ _)
        | .player (.leftGame _)
        | .player (.gameEnded _)
        | .player (.sheHulkDealtDamage _)
        | .player (.optionalOnceActed _ _)
        | .player (.drawFromEmptyAttempted _) => pure ()
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
            -- Delayed upkeep triggers (CR 603.7; The Eagles Are Coming!)
            for dt in post.delayedTriggers do
              match dt.kind with
              | .eaglesBirds n =>
                let src := dt.source.getD
                  { printed := { name := "The Eagles Are Coming!", types := #[.sorcery] }
                    id := ⟨0⟩, owner := dt.controller, controller := some dt.controller, zone := .exile }
                let ab : TriggeredAbility :=
                  .triggered .eachUpkeep
                    { phrase := s!"Create {n} 1/1 white Bird Soldier creature token(s) with flying" } {}
                waiting := waiting.push
                  { controller := dt.controller
                    source := src
                    ability := ab
                    event := .eachUpkeep
                    eventCause := some dt.cause
                    delayedTrigger := some (dt.kind, dt.cause)
                    checked := true }
              | _ => pure ()
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
            -- Delayed end-step triggers (CR 603.7)
            for dt in post.delayedTriggers do
              match dt.kind with
              | .endStepReturn _ | .endStepExile _ | .endStepSacrifice _
              | .endStepGraveReturn _ _ | .endStepSynthetic _ =>
                let obj? : Option GameObject :=
                  match dt.kind with
                  | .endStepReturn oid | .endStepExile oid | .endStepSacrifice oid
                  | .endStepGraveReturn oid _ => post.findObject? oid
                  | _ => none
                let src := (dt.source.orElse (fun _ => obj?)).getD
                  { printed := { name := "Delayed Trigger", types := #[] }
                    id := ⟨0⟩, owner := dt.controller, controller := some dt.controller, zone := .exile }
                let ab : TriggeredAbility :=
                  .triggered .eachEndStep { phrase := "At the beginning of the next end step" } {}
                waiting := waiting.push
                  { controller := dt.controller
                    source := src
                    ability := ab
                    event := .eachEndStep
                    eventCause := some dt.cause
                    delayedTrigger := some (dt.kind, dt.cause)
                    checked := true }
              | _ => pure ()
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
            for dt in post.delayedTriggers do
              if dt.kind == .attackPumpPerPlains && dt.controller == activePlayer then
                let src := dt.source.getD
                  (match (post.permanentsOf activePlayer).find? (fun o => o.printed.saga.isSome) with
                   | some o => o
                   | none =>
                     { printed := { name := "Roads Go Ever, Ever On", types := #[.enchantment] }
                       id := ⟨0⟩, owner := activePlayer, controller := some activePlayer, zone := .battlefield })
                let (w, fs) :=
                  queueAb post activePlayer src .onYouAttackPumpTargetPerPlains .youAttack
                    (eventCause := some dt.cause) (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
            let attackingNow :=
              (post.permanentsOf activePlayer).filter (fun o => post.isCreature o && o.status.attacking)
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
          if post.isPreparedSpell castObj.id then
            let (w, fs) :=
              queueFra post caster .youCastPreparedSpell (cause := some castObj)
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if castObj.printed.isCreature || castObj.printed.isArtifact then
            let (w, fs) :=
              queueFra post caster .youCastArtifactOrCreature (cause := some castObj)
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          let targetsOwnCreature := uniquePerm.any (fun o => post.isCreature o && o.controlledBy caster)
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
          let fromHand := (fromZone == .hand caster) || post.castFromHand castObj.id
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
          if post.treasureManaSpent castObj.id then
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
            if (post.staticAbilities o).any (fun | .extort => true | _ => false) then
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
          if uniquePerm.any (post.isCreature ·) then
            let (w, fs) :=
              queueCtrl post caster .youCastTargetingCreature (cause := some castObj)
                (w := waiting) (fs := firedSources)
            waiting := w; firedSources := fs
          if castObj.printed.isInstantOrSorcery &&
              uniquePerm.any (fun o => (post.types o).contains .artifact || (post.types o).contains .land) then
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
                  o.isOnBattlefield && post.isCreature o && o.controller.isSome && !o.controlledBy caster)
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
          | .nonMana loyaltyDelta .. =>
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
                  for ab in post.matchingTriggers o .youActivateLoyaltyAbility do
                    if ab.shared != .drawIfRemovedTwoLoyalty || removed ≥ 2 then
                      let lkp :=
                        if ab.shared == .drawIfRemovedTwoLoyalty then some (Int.ofNat removed)
                        else none
                      let (w, fs) :=
                        queueAb post controller o ab .youActivateLoyaltyAbility
                          (lastKnownPower := lkp) (w := waiting) (fs := firedSources)
                      waiting := w; firedSources := fs
            | none => pure ()
            if srcObj?.any (post.isCreature ·) || sourceSnap.creature then
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
          | .mana _ =>
            if srcObj?.any (post.isCreature ·) || sourceSnap.creature then
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
        | .triggerQueue (.triggered _ _ _ _)
        | .triggerQueue (.putOnStack _ _ _)
        | .triggerQueue (.modeChosen _ _ _) => pure ()
        | .continuousEffect _ => pure ()
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
      let firedDelayed := wts.filterMap (fun wt =>
        match wt.delayedTrigger with
        | some (k, c) => if k.isOneShot then some (wt.controller, k, c) else none
        | none => none)
      let g :=
        if firedDelayed.isEmpty then g
        else
          let remaining := firedDelayed.foldl (fun (acc : Array DelayedTrigger) (ctrl, k, c) =>
            match acc.findIdx? (fun dt => dt.controller == ctrl && dt.kind == k && dt.cause == c) with
            | some idx => acc.eraseIdx! idx
            | none => acc) g.delayedTriggers
          let eng := GameEvent.engine g.turnNumber (.delayedTriggers remaining)
          ({ g with events := g.events.push eng }).applyChange eng.change
      let preWaiting := g.waitingTriggers
      let (g, toEnqueue, _) := wts.foldl
        (fun (acc, q, coalesced) wt =>
          let key := (wt.source.id, wt.ability)
          let alreadyInPre :=
            wt.event == .sourceDealtDamage &&
              preWaiting.any (fun t =>
                t.source.id == wt.source.id && t.ability == wt.ability &&
                  t.event == .sourceDealtDamage)
          if alreadyInPre then
            if coalesced.contains key then
              (acc, q, coalesced)
            else
              let amt := wt.lastKnownPower.getD 0
              let wt' := acc.waitingTriggers.map (fun t =>
                if t.source.id == wt.source.id && t.ability == wt.ability &&
                    t.event == .sourceDealtDamage then
                  { t with lastKnownPower := some (t.lastKnownPower.getD 0 + amt) }
                else t)
              ({ acc with waitingTriggers := wt' }, q, coalesced.push key)
          else
            let ev :=
              { (GameEvent.triggered acc.turnNumber (acc.snapshot wt.source) wt.controller wt.ability
                  batchId) with
                batch := batchId }
            let acc := { acc with events := acc.events.push ev }
            (acc, q.push wt, coalesced))
        (g, #[], (#[] : Array (ObjectId × TriggeredAbility)))
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

/-- Run `f` under an active resolving context `(src, ctrl)` (CR 608 / 610.1),
pushing a `ContinuationFrame` for the resolution and popping it if no pending
choice or random continuation remains open. -/
def withResolvingContext (g : Game) (src : Option ObjectId) (ctrl : PlayerId)
    (f : Game → Game) : Game :=
  let prevDepth := g.continuations.size
  let g := f (g.change (.pushContinuationFrame { resolvingContext := some (src, ctrl) }))
  if g.pending != .none || g.afterRandom != .none then g
  else if g.continuations.size > prevDepth then g.change .popContinuationFrame
  else g

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
      | .rules (.continuousEffect (.created id eff)) =>
        if id == eid then
          let effSrc :=
            match eff with
            | .playerRule _ (.pendingLokiCopy s _) _ => s.orElse (fun _ => fallbackSrc)
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
def hasActivePrintedStatics (g : Game) (o : GameObject) : Bool :=
  (o.zone == .battlefield && !o.status.phasedOut && !o.status.faceDown &&
    !g.losesAbilitiesUntilEot o && (g.losesAbilitiesGrantedBy o).isEmpty) ||
  o.zone == .command

/-- The object a continuous effect applies to (the source, for a static
ability's effect). `none` for effects on players or the whole game. -/
def effectObject? : ContinuousEffectSpec → Option ObjectId
  | .gameRule (.staticAbility id _) _ => some id
  | .layered (.objects #[id]) _ _ => some id
  | .permission _ (.playFromExile id _) _
  | .permission _ (.freeCastFromGraveyard id) _
  | .permission _ (.flashback id) _
  | .permission _ (.colorlessGrant id _) _ => some id
  | .gameRule (.cantUntap id _) _
  | .gameRule (.cantBeBlockedByPlayer id _) _
  | .gameRule (.cantBeBlockedExceptByHaste id) _
  | .gameRule (.cantBlock id) _
  | .gameRule (.uncounterable id) _
  | .gameRule (.fraEmblem id) _ => some id
  | .replacement r _ => r.id.object
  | .prevention p _ => p.id.object
  | _ => none

/-- A continuous effect on an object that lasts until end of turn and ends in
the cleanup step (CR 514.2). -/
def effectEndsAtCleanup : ContinuousEffectSpec → Bool
  | .layered _ (.copy ..) _ | .layered _ (.control _) _ => false
  | .layered _ _ .untilEndOfTurn => true
  | .permission _ _ .untilEndOfTurn => true
  | .gameRule _ .untilEndOfTurn => true
  | .replacement _ .untilEndOfTurn | .prevention _ .untilEndOfTurn => true
  | _ => false

/-- The active continuous effect recorded under `eid`, if any. -/
def activeEffect? (g : Game) (eid : EffectId) : Option ContinuousEffect :=
  (g.activeEffects.find? (·.1 == eid)).map (·.2)

/-- Record the creation of `o`'s printed static-ability continuous effects if `o`
is active on the battlefield or in the command zone (CR 611.3). -/
def createPrintedStaticEffects (g : Game) (o : GameObject)
    (cause : Option EventCause := some (.gameRule .staticAbility)) : Game :=
  if g.hasActivePrintedStatics o then
    o.printed.staticAbilities.foldl (fun acc sa =>
      let eid : EffectId := ⟨acc.nextEffectId⟩
      acc.record (GameEvent.effectCreated acc.turnNumber eid (.staticAbility o.id sa) (cause := cause))) g
  else g

/-- Record the expiration of `o`'s active printed static-ability continuous
effects (CR 611.3), each under the `EffectId` it was created with. -/
def expirePrintedStaticEffects (g : Game) (o : GameObject)
    (cause : Option EventCause := some (.gameRule .leavingZone)) : Game :=
  o.printed.staticAbilities.foldl (fun acc sa =>
    let eff := ContinuousEffectSpec.staticAbility o.id sa
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
  | .layered (.objects #[id]) (.abilities _ .all) _ =>
    let prev? := g.findObject? id
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff (cause := cause))
    match prev? with
    | some prev => g.expirePrintedStaticEffects prev (cause := cause)
    | none => g
  | .layered (.objects #[id]) (.copy newPrinted _) _ =>
    let prev? := g.findObject? id
    let g :=
      match prev? with
      | some prev => g.expirePrintedStaticEffects prev (cause := cause)
      | none => g
    let eid : EffectId := ⟨g.nextEffectId⟩
    let g := g.record (GameEvent.effectCreated g.turnNumber eid eff (cause := cause))
    match g.findObject? id with
    | some cur =>
      if g.hasActivePrintedStatics cur then
        newPrinted.staticAbilities.foldl (fun acc sa =>
          let sid : EffectId := ⟨acc.nextEffectId⟩
          acc.record (GameEvent.effectCreated acc.turnNumber sid (.staticAbility id sa)
            (cause := some (.gameRule .staticAbility)))) g
      else g
    | none => g
  | .layered (.objects #[id]) (.control _) _ =>
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
    | .layered (.objects #[id]) (.abilities _ .all) _ =>
      let wasActive := (g.findObject? id).map g.hasActivePrintedStatics |>.getD false
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := cause))
      match g.findObject? id with
      | some cur =>
        if !wasActive && g.hasActivePrintedStatics cur then g.createPrintedStaticEffects cur
        else g
      | none => g
    | .layered (.objects #[id]) (.copy _ _) _ =>
      let prev? := g.findObject? id
      let g :=
        match prev? with
        | some prev => g.expirePrintedStaticEffects prev (cause := cause)
        | none => g
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := cause))
      match g.findObject? id with
      | some cur => g.createPrintedStaticEffects cur
      | none => g
    | .layered (.objects #[id]) (.control _) _ =>
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
      if g.notACreature o || g.hasActiveEffect (.notACreature id) then
        g.expireAll (.notACreature id) (cause := effCause)
      else g
    else if g.loggedCastForImpending id && !g.notACreature o then
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

/-- Record `CombatEvent.becameAttacking` for `id` targeting `target` (defaulting
to `id`'s opponent) (CR 508.4). -/
def markAttacking (g : Game) (id : ObjectId) (target : Option AttackTarget := none)
    (cause : Option EventCause := some (.turnBased .declareAttackers)) : Game :=
  match g.findObject? id with
  | some o =>
    let tgt := target.getD (.player (g.opponent (o.controller.getD g.activePlayer)))
    g.record (GameEvent.becameAttacking g.turnNumber (g.snapshot o) tgt (cause := cause))
  | none => g

/-- Record `CombatEvent.blockersDeclared` for `id` blocking `attackers` (CR 509.1g). -/
def markBlocking (g : Game) (id : ObjectId) (attackers : Array ObjectId)
    (cause : Option EventCause := some (.turnBased .declareBlockers)) : Game :=
  match g.findObject? id with
  | some o =>
    let p := o.controller.getD o.owner
    let snap := g.snapshot o
    g.record (GameEvent.blockersDeclared g.turnNumber p (attackers.map (fun a => (snap, a)))
      (cause := cause))
  | none => g

/-- Record `CombatEvent.becameBlocked` for `id` (CR 509.1h). -/
def markBlocked (g : Game) (id : ObjectId) (blockers : Array ObjectId := #[])
    (cause : Option EventCause := some (.turnBased .declareBlockers)) : Game :=
  match g.findObject? id with
  | some o =>
    g.record (GameEvent.becameBlocked g.turnNumber (g.snapshot o) blockers (cause := cause))
  | none => g

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
  if (g.lifeLocked p || g.lifeCantChange p) && life != pl.life then
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
    | .layered (.objects #[id]) (.copy printed restore) d =>
      let untilEot := d == .untilEndOfTurn
      let untilNextTurn := match d with | .untilNextTurnOf _ => true | _ => false
      let untilSourceLeaves := match d with | .whileSourceOnBattlefield s => some s | _ => none
      match acc.findObject? id with
      | some o =>
        if o.zone == .battlefield && sel o untilEot untilNextTurn untilSourceLeaves then
          let card? := restore.orElse (fun _ => acc.copyRestore o)
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
    | .layered (.objects #[id]) (.control _) (.whileSourceOnBattlefield s) =>
      if s != srcId then acc
      else
        match acc.findObject? id with
        | none => acc.expireEffectById eid (cause := cause)
        | some o =>
          let acc := acc.expireEffectById eid (cause := cause)
          let p := o.defaultController.getD o.owner
          let othersRemain := acc.activeEffects.any (fun (_, e) =>
            match e with
            | .layered (.objects #[oid]) (.control _) _ => oid == id
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
  g.expireMatching (fun s =>
    match s.duration with
    | .whileSourceOnBattlefield src => src == srcId && Game.effectObject? s != some srcId
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
