import Std.Data.HashMap
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

/-- Pre-proposal game checkpoint for CR 734.1 reversal, paired with the length
of `Game.events` immediately before the proposal began so speculative proposal
and mana-ability events can be truncated cleanly. -/
structure ProposalCheckpoint where
  eventsSize : Nat := 0
  players : Array Player := #[]
  objects : Array GameObject := #[]
  stack : Array StackEntry := #[]
  activePlayer : PlayerId := ⟨0⟩
  priority : PlayerId := ⟨0⟩
  pendingPriority : Option PlayerId := none
  step : Step := .untap
  turnNumber : Nat := 1
  startingPlayer : PlayerId := ⟨0⟩
  isFirstTurn : Bool := true
  pending : Pending := .none
  nextObjectId : Nat := 0
  nextEffectId : Nat := 0
  nextBatchId : Nat := 0
  currentBatch : Option (BatchId × Option EventCause) := none
  openBatchObjects : Array GameObject := #[]
  openBatchPlayers : Array Player := #[]
  openBatchEffects : Array (EffectId × ContinuousEffectSpec) := #[]
  openBatchPending : Pending := .none
  openBatchStack : Array StackEntry := #[]
  activeEffects : Array (EffectId × ContinuousEffectSpec) := #[]
  timestamp : Nat := 0
  pregameRandom : PregameRandom := .none
  result : Option GameResult := none
  log : Array String := #[]
  format : Format := .constructed
  brawl : Bool := false
  consecutivePasses : Nat := 0
  cleanupGivesPriority : Bool := false
  proposedSpell : Option ProposedSpell := none
  awaitingOpeningBegin : Bool := false
  mulliganToDeclare : Array PlayerId := #[]
  willMulligan : Array PlayerId := #[]
  mulliganToBottom : Array PlayerId := #[]
  assignedCombatDamage : Array CreatureCombatAssignment := #[]
  pendingBlockerAssignments : Array CreatureCombatAssignment := #[]
  blockersQueue : Array PlayerId := #[]
  waitingTriggers : Array WaitingTrigger := #[]
  queuedLinkedExile : Array ObjectId := #[]
  isNight : Bool := false
  continuations : Array ContinuationFrame := #[]
  replacementOrder : Array ReplacementId := #[]
  castingFromTop : Bool := false
  delayedTriggers : Array DelayedTrigger := #[]
  extraTurns : Array PlayerId := #[]
  additionalCombatPhases : Nat := 0
deriving Inhabited, BEq

structure Game where
  players : Array Player := #[]
  objects : Array GameObject := #[]
  stack : Array StackEntry := #[]
  activePlayer : PlayerId := ⟨0⟩
  priority : PlayerId := ⟨0⟩
  /-- Player slated to receive priority once SBA / trigger-stacking pauses finish (CR 117.3 / 117.5). -/
  pendingPriority : Option PlayerId := none
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
  openBatchStack : Array StackEntry := #[]
  openBatchSuppressInteractive : Bool := false
  /-- Active continuous effects paired with their unique `EffectId` (CR 611). -/
  activeEffects : Array (EffectId × ContinuousEffectSpec) := #[]
  timestamp : Nat := 0
  /-- Pre-game `--norandom` continuation state (CR 103.1–103.5). -/
  pregameRandom : PregameRandom := .none
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
  /-- Pre-proposal checkpoint captured before a spell or ability proposal begins (CR 734.1). -/
  proposalCheckpoint : Option ProposalCheckpoint := none
  /-- Outer proposal checkpoints saved while a nested cast-during-resolution proposal is active. -/
  outerProposalCheckpoints : Array ProposalCheckpoint := #[]
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
  /-- Partial blocker combat damage assignments accumulated across defending players in APNAP order (CR 510.1d / 802.5). -/
  pendingBlockerAssignments : Array CreatureCombatAssignment := #[]
  /-- Defending players who still must declare blockers, in APNAP order
  (CR 509.1 / 802). -/
  blockersQueue : Array PlayerId := #[]
  /-- Triggered abilities waiting to be put onto the stack the next time a
  player would receive priority (CR 603.3 / 603.3b). Distinguished by
  `WaitingTrigger.pattern`. -/
  waitingTriggers : Array WaitingTrigger := #[]
  /-- Exiled `ObjectId`s linked via CR 610.3 “until ~ leaves” waiting to return
  once the enclosing departure batch closes. -/
  queuedLinkedExile : Array ObjectId := #[]
  /-- It is night (CR 732 / 702.145). Used by Nick Fury / daybound (MSH 191). -/
  isNight : Bool := false
  /-- Stack of mid-resolution continuation frames (CR 608.2). Top of stack
  is `continuations.back?.getD {}`. -/
  continuations : Array ContinuationFrame := #[]
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
  /-- State changes that happened this game, oldest first (CR 603.2 / 614.1).
  Conditions ask this log whether an action happened. Triggers and
  replacement effects match the same events. A replaced change is not
  recorded (CR 614.6). -/
  events : Array GameEvent := #[]
  /-- Derived invariant (`== continuationsHaveSuppressedReplay continuations`):
  true while a suppressed checkpoint replay continuation is active. -/
  suppressInteractiveReplay : Bool := false
deriving Inhabited, BEq

/-- Pre-batch game state snapshot for CR 603.10 look-back trigger evaluation. -/
abbrev GameSnapshot := Game

namespace Game

/-- Top continuation frame, or `{}` when no frame has been pushed yet. -/
@[inline] def topFrame (g : Game) : ContinuationFrame :=
  g.continuations.back?.getD {}

/-- Update the top continuation frame when an active frame is on `g.continuations`. -/
@[inline] def modifyTopFrame (g : Game) (f : ContinuationFrame → ContinuationFrame) : Game :=
  match g.continuations.back? with
  | none => g
  | some top => { g with continuations := g.continuations.pop.push (f top) }

@[inline] def pendingDrawAfterScry (g : Game) := g.topFrame.pendingDrawAfterScry
@[inline] def recentTokenIds (g : Game) := g.topFrame.recentTokenIds
@[inline] def pendingFreeCopies (g : Game) := g.topFrame.pendingFreeCopies
@[inline] def pendingMayCastFromExile (g : Game) := g.topFrame.pendingMayCastFromExile
@[inline] def postCastCleanup (g : Game) := g.topFrame.postCastCleanup
@[inline] def surveilReturnMvAtMost (g : Game) := g.topFrame.surveilReturnMvAtMost
@[inline] def pendingReplacement (g : Game) := g.topFrame.pendingReplacement
@[inline] def outerPendingReplacements (g : Game) := g.topFrame.outerPendingReplacements
@[inline] def conniveSource (g : Game) := g.topFrame.conniveSource
@[inline] def thirstDiscardsLeft (g : Game) := g.topFrame.thirstDiscardsLeft
@[inline] def thirstDiscardType (g : Game) := g.topFrame.thirstDiscardType
@[inline] def pendingDiscardsLeft (g : Game) := g.topFrame.pendingDiscardsLeft
@[inline] def discardCountPerPlayer (g : Game) := g.topFrame.discardCountPerPlayer
@[inline] def discardBatch (g : Game) := g.topFrame.discardBatch
@[inline] def stagedAttackTokenBatches (g : Game) := g.topFrame.stagedAttackTokenBatches
@[inline] def resolvingContext (g : Game) := g.topFrame.resolvingContext
@[inline] def stashedCause (g : Game) := g.topFrame.stashedCause
@[inline] def resolvingSpell (g : Game) : Option ObjectId :=
  g.continuations.reverse.findSome? (·.resolvingSpell)
@[inline] def resolvingAbility (g : Game) : Option ObjectId :=
  g.continuations.reverse.findSome? (·.resolvingAbility)
@[inline] def resolvingModes (g : Game) : Option (Array Nat) :=
  g.topFrame.resolvingModes
@[inline] def resolvingDivision (g : Game) := g.topFrame.resolvingDivision
@[inline] def resolvingSkippedSlots (g : Game) := g.topFrame.resolvingSkippedSlots
@[inline] def afterRandom (g : Game) := g.topFrame.afterRandom
@[inline] def resolutionFinish (g : Game) := g.topFrame.resolutionFinish
@[inline] def pendingResolvedEvent (g : Game) := g.topFrame.pendingResolvedEvent
@[inline] def currentStepEnv (g : Game) : Array (VarId × StepOutcome) := g.topFrame.stepEnv
@[inline] def currentInterpWait? (g : Game) : Option InterpState := g.topFrame.interpWait?

end Game

namespace Status

/-- Apply one `CounterDelta` of `kind` directly to `s` (CR 122.1). -/
def applyCounterDelta (s : Status) (kind : CounterKind) (delta : CounterDelta) : Status :=
  match delta with
  | .put n =>
    { s with counters := s.counters.add kind n }
  | .removed n =>
    { s with counters := s.counters.sub kind n }

end Status

namespace GameObject

/-- Apply one `ObjectChange` in isolation (CR 109 / 607). -/
def applyChange (o : GameObject) (c : ObjectChange) : GameObject :=
  match c with
  | .abilityEffect v => { o with abilityEffect := v }
  | .linkedExile v => { o with linkedExile := v }
  | .pushLinkedExile id => { o with linkedExile := o.linkedExile.push id }
  | .returnToZone v => { o with returnToZone := v }
  | .leaveTriggerExile v => { o with leaveTriggerExile := v }
  | .pushLeaveTriggerExile id => { o with leaveTriggerExile := o.leaveTriggerExile.push id }
  | .exiledBy v => { o with exiledBy := v }

end GameObject

namespace Player

/-- Apply one `PlayerChange` in isolation (CR 102 / 103). -/
def applyChange (pl : Player) (c : PlayerChange) : Player :=
  match c with
  | .mulligansTaken v => { pl with mulligansTaken := v }
  | .keptOpeningHand v => { pl with keptOpeningHand := v }
  | .sideboard v => { pl with sideboard := v }

end Player

namespace ProposedSpell

/-- Apply one `ProposalChange` in isolation (CR 601.2f–h). -/
def applyChange (p : ProposedSpell) (c : ProposalChange) : ProposedSpell :=
  match c with
  | .cost v => { p with cost := v }
  | .reduceCostBy mc => { p with cost := p.cost.reduceByCost mc }
  | .tapped v => { p with tapped := v }
  | .pushTapped id => { p with tapped := p.tapped.push id }
  | .needsSacrificeOther v => { p with needsSacrificeOther := v }
  | .needsDiscardCard v => { p with needsDiscardCard := v }
  | .kicked v => { p with kicked := v }
  | .kickerAnnounced v => { p with kickerAnnounced := v }
  | .giftTo v => { p with giftTo := v }
  | .giftAnnounced v => { p with giftAnnounced := v }
  | .teamworkPaid v => { p with teamworkPaid := v }
  | .teamworkAnnounced v => { p with teamworkAnnounced := v }
  | .teamworkCreatures v => { p with teamworkCreatures := v }
  | .additionalGeneric v => { p with additionalGeneric := v }
  | .needsBehold v => { p with needsBehold := v }
  | .payLife v => { p with payLife := v }
  | .alternativeCost v => { p with alternativeCost := v }
  | .loyaltyPaid v => { p with loyaltyPaid := v }
  | .choiceCostPaid v => { p with choiceCostPaid := v }

end ProposedSpell

namespace Game

/-- Update `p` in place if `p` is in `g.players`. -/
def modifyPlayer (g : Game) (p : PlayerId) (f : Player → Player) : Game :=
  if h : p.idx < g.players.size then
    let pl := g.players[p.idx]
    { g with players := g.players.set! p.idx (f pl) }
  else g

def findObject? (g : Game) (id : ObjectId) : Option GameObject :=
  g.objects.find? (fun o => o.id == id)

/-- Whether `d` is currently active in `g` (e.g. `.whileSourceOnBattlefield src`
requires `src` to be phased in on the battlefield per CR 611.2b / 702.26f,
whereas `.untilSourceLeaves src` stays active through phasing as long as `src`
has not left the battlefield per CR 611.2a / 702.26d). -/
def durationActive (g : Game) (d : EffectDuration) : Bool :=
  match d with
  | .whileSourceOnBattlefield src =>
    (g.findObject? src).any (·.isOnBattlefield)
  | .untilSourceLeaves src =>
    (g.findObject? src).any (fun o => o.zone == .battlefield)
  | .whileSourceHasCounter src k =>
    (g.findObject? src).any (fun o => o.isOnBattlefield && o.status.counterCount k > 0)
  | .whileInZone oid z =>
    (g.findObject? oid).any (fun o => o.zone == z)
  | _ => true

/-- Whether an active continuous effect has exactly the payload `eff` (CR 611.2b / 702.26f). -/
def hasActiveEffect (g : Game) (eff : ContinuousEffectSpec) : Bool :=
  g.activeEffects.any (fun (_, e) => e == eff && g.durationActive e.duration)

/-- Apply one `ContinuousEffectEvent` in isolation (CR 611). -/
def applyContinuousEffectEvent (g : Game) (e : ContinuousEffectEvent) : Game :=
  match e with
  | .created effectId spec =>
    { g with
      nextEffectId := max g.nextEffectId (effectId.raw + 1)
      activeEffects := g.activeEffects.push (effectId, spec) }
  | .expired effectId _ =>
    match g.activeEffects.findIdx? (·.1 == effectId) with
    | none => g
    | some idx =>
      { g with
        nextEffectId := max g.nextEffectId (effectId.raw + 1)
        activeEffects := g.activeEffects.eraseIdx! idx }

/-- All seats on `p`'s team in seat order, including `p` (CR 102.3 / 810.2 / 810.11). -/
def teamMembers (g : Game) (p : PlayerId) : Array PlayerId := Id.run do
  let n := g.players.size
  if p.idx ≥ n then return #[p]
  if !g.players.any (·.teammate.isSome) then return #[p]
  let linked (a b : PlayerId) : Bool :=
    a.idx < n && b.idx < n && a != b &&
      (g.players[a.idx]!.teammate == some b || g.players[b.idx]!.teammate == some a)
  let mut comp : Array PlayerId := #[p]
  let mut idx := 0
  while idx < comp.size do
    let u := comp[idx]!
    for pl in g.players do
      if !comp.contains pl.id && linked u pl.id then
        comp := comp.push pl.id
    idx := idx + 1
  return g.players.filterMap (fun pl => if comp.contains pl.id then some pl.id else none)

/-- True when `a` and `b` are distinct Two-Headed Giant teammates (CR 102.3 / 810.2 / 810.11). -/
def areTeammates (g : Game) (a b : PlayerId) : Bool :=
  if a == b || !g.players.any (·.teammate.isSome) then false
  else (g.teamMembers a).contains b

/-- Total poison counters shared by `p`'s team (CR 810.10 / 810.10a,d). -/
def teamPoison (g : Game) (p : PlayerId) : Nat :=
  (g.teamMembers p).foldl (fun acc q =>
    if h : q.idx < g.players.size then acc + g.players[q.idx].poison else acc) 0

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
      { g with objects := g.objects.set! i { o with status := { o.status with phasedOut := false, phasedWith := none } } }
    | none => g
  | .transformed object nowBackFace =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let printed :=
        if o.status.transformed != nowBackFace then
          match o.printed.otherFace with
          | some face =>
            let keepToken := o.printed.isToken
            { face with
              isToken := keepToken
              otherFace := some { o.printed with isToken := keepToken, otherFace := none } }
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
      match delta with
      | .put n =>
        { g with players := g.players.set! p.idx { pl with poison := pl.poison + n } }
      | .removed n =>
        -- CR 810.10b: remove from `p` first, spilling any remainder across teammates.
        let takeSelf := Nat.min pl.poison n
        let players0 := g.players.set! p.idx { pl with poison := pl.poison - takeSelf }
        let rem0 := n - takeSelf
        if rem0 == 0 then { g with players := players0 }
        else
          let (playersFinal, _) :=
            (g.teamMembers p).foldl (fun (pls, rem) q =>
              if rem == 0 || q == p then (pls, rem)
              else if hq : q.idx < pls.size then
                let mq := pls[q.idx]
                let takeMate := Nat.min mq.poison rem
                (pls.set! q.idx { mq with poison := mq.poison - takeMate }, rem - takeMate)
              else (pls, rem)) (players0, rem0)
          { g with players := playersFinal }
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
      let ts := g.timestamp + 1
      { g with timestamp := ts, objects := g.objects.set! i { o with attachedTo := some host, timestamp := ts } }
    | none => g
  | .unattached attachment _ =>
    match findEventIdx? attachment with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i { o with attachedTo := none } }
    | none => g
  | .designation object d gained =>
    match findEventIdx? object with
    | some i =>
      let o := g.objects[i]!
      let (g, o') : Game × GameObject :=
        match d with
        | .ringBearer =>
          let clearAll (g : Game) : Game :=
            { g with players := g.players.map fun (pl : Player) =>
                if pl.ringBearerId == some o.id then { pl with ringBearerId := none } else pl }
          let g :=
            match object.controller.orElse (fun _ => o.controller) with
            | some c =>
              if gained then
                g.modifyPlayer c (fun pl => { pl with ringBearerId := some o.id })
              else clearAll g
            | none =>
              if gained then g else clearAll g
          (g, o)
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
          (g, { o with status := { o.status with goaded := !goadedBy.isEmpty, goadedBy, goadedUntilNextTurnOf } })
        | .prepared => (g, { o with status := { o.status with prepared := gained } })
        | .harnessed => (g, { o with status := { o.status with harnessed := gained } })
      { g with objects := g.objects.set! i o' }
    | none =>
      match d, gained, object.id with
      | .ringBearer, false, some oid =>
        { g with players := g.players.map fun (pl : Player) =>
            if pl.ringBearerId == some oid then { pl with ringBearerId := none } else pl }
      | _, _, _ => g

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

/-- Apply one `LifeEvent` in isolation (CR 119.2 / 119.3 / 810.9). -/
def applyLifeEvent (g : Game) (e : LifeEvent) : Game :=
  let locked (p : PlayerId) : Bool :=
    g.activeEffects.any fun (_, s) =>
      match s with
      | .playerRule q .lifeLocked d | .playerRule q .lifeCantChange d =>
        (q == p || g.areTeammates q p) && g.durationActive d
      | _ => false
  let setTeamLife (p : PlayerId) (newLife : Int) : Game :=
    let team := g.teamMembers p
    { g with
      players :=
        team.foldl (fun pls q =>
          if hq : q.idx < pls.size then
            pls.set! q.idx { pls[q.idx] with life := newLife }
          else pls) g.players }
  match e with
  | .gained p amount =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      if locked p then g
      else setTeamLife p (pl.life + (amount : Int))
    else g
  | .lost p amount _ _ =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      if locked p then g
      else setTeamLife p (pl.life - (amount : Int))
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

private def adjustTokenCardDef (isTok : Bool) (p : CardDef) : CardDef :=
  if isTok && !p.isToken then
    { p with isToken := true, otherFace := p.otherFace.map ({ · with isToken := true }) }
  else p

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
      let prepared :=
        toZone == .battlefield && !faceDown &&
          if after.copiable.isSome then after.prepared
          else after.prepared || printed.entersPrepared
      let sick :=
        if after.printed.isSome then after.summoningSick
        else true
      let baseStatus : Status :=
        if toZone == .battlefield then
          { faceDown := faceDown
            tapped := after.tapped
            summoningSick := sick
            attacking := after.attacking
            attackingTarget := after.attackingTarget
            phasedOut := after.phasedOut
            chosenOdd := if !faceDown then after.chosenOdd else none
            chosenCreatureType := if !faceDown then after.chosenCreatureType else none
            chosenColor := if !faceDown then after.chosenColor else none
            chosenName := if !faceDown then after.chosenName else none
            chosenCardType := if !faceDown then after.chosenCardType else none
            chosenAnchor := if !faceDown then after.chosenAnchor else none
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
        defaultController :=
          if toZone == .battlefield then
            after.defaultController.orElse (fun _ => after.controller)
          else none
        zone := toZone
        status := status
        timestamp := ts
        attachedTo := if toZone == .battlefield then after.attachedTo else none
        adventurerCard := if toZone == .stack then after.adventurerCard else none
        chosenX := chosenX
        isCopy := after.isCopy
        isCommander := after.isCommander || before.isCommander || existing?.any (·.isCommander) }
    match existing? with
    | some existing =>
      let g := g.stripFromZoneList existing.id fromZone
      let leavingPlay :=
        (fromZone == .battlefield || fromZone == .stack) &&
          toZone != .battlefield && toZone != .stack
      let printed0 : CardDef :=
        match after.printed with
        | some p => p
        | none =>
          if leavingPlay && existing.status.transformed then
            match existing.printed.otherFace with
            | some front =>
              let keepToken := existing.printed.isToken
              { front with
                isToken := keepToken
                otherFace := some { existing.printed with isToken := keepToken, otherFace := none } }
            | none => existing.printed
          else if toZone == .battlefield && after.transformed && !existing.status.transformed then
            match existing.printed.otherFace with
            | some back =>
              let keepToken := existing.printed.isToken
              { back with
                isToken := keepToken
                otherFace := some { existing.printed with isToken := keepToken, otherFace := none } }
            | none => existing.printed
          else existing.printed
      let printed : CardDef := adjustTokenCardDef after.token printed0
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
        let printed0 :=
          match after.printed.orElse (fun _ => before.printed) with
          | some p => p
          | none =>
            if !after.name.isEmpty || !after.types.isEmpty then after.toCardDef
            else before.toCardDef
        let printed := adjustTokenCardDef after.token printed0
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
    let printed := adjustTokenCardDef object.token object.toCardDef
    let baseStatus : Status :=
      if object.zone == Zone.battlefield then
        let faceDown := object.faceDown
        let prepared :=
          !faceDown &&
            if object.copiable.isSome then object.prepared
            else object.prepared || printed.entersPrepared
        { tapped := object.tapped
          summoningSick := true
          attacking := object.attacking
          attackingTarget := object.attackingTarget
          phasedOut := object.phasedOut
          faceDown := faceDown
          chosenOdd := if !faceDown then object.chosenOdd else none
          chosenCreatureType := if !faceDown then object.chosenCreatureType else none
          chosenColor := if !faceDown then object.chosenColor else none
          chosenName := if !faceDown then object.chosenName else none
          chosenCardType := if !faceDown then object.chosenCardType else none
          chosenAnchor := if !faceDown then object.chosenAnchor else none
          prepared := prepared
          transformed := object.transformed }
      else if object.zone == Zone.stack || object.zone == Zone.exile then
        { faceDown := object.faceDown }
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
        defaultController :=
          if object.zone == Zone.battlefield then
            object.defaultController.orElse (fun _ => ctrl)
          else none
        zone := object.zone
        status := status
        timestamp := ts
        attachedTo := if object.zone == Zone.battlefield then object.attachedTo else none
        adventurerCard := object.adventurerCard
        isCopy := object.isCopy
        isCommander := object.isCommander
        chosenX := if object.zone == Zone.stack then object.chosenX else none }
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

/-- Apply a `PlayerEvent` to `g` (CR 104, 106.4, 500.5, 701.4, 701.20–25, 701.34, 701.54, 702.131, 726, 800.4a). -/
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
      let pool' : ManaPool :=
        if keptColorless then
          { units := pl.manaPool.units.map (fun u => { u with mana := .colorless }) }
        else
          {}
      { g with players := g.players.set! p.idx { pl with manaPool := pool' } }
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
      let ringBearerId := bearer.orElse (fun _ => pl.ringBearerId)
      { g with players := g.players.set! p.idx { pl with theRingAbilities := stage, ringBearerId } }
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
    let g :=
      if h : p.idx < g.players.size then
        let pl := g.players[p.idx]
        { g with players := g.players.set! p.idx { pl with lost := true, leftTheGame := true, isMonarch := false } }
      else g
    { g with
      waitingTriggers := g.waitingTriggers.filter (·.controller != p)
      delayedTriggers := g.delayedTriggers.filter (·.controller != p) }
  | .gameEnded res =>
    { g with result := some res }
  | .proliferated .. | .sheHulkDealtDamage .. | .beheld ..
  | .optionalOnceActed .. | .drawFromEmptyAttempted ..
  | .lookedAt .. | .revealed .. | .searched .. => g

/-- Apply a `TriggerQueueEvent` to `g` (CR 603.2 / 603.3). -/
def applyTriggerQueueEvent (g : Game) (e : TriggerQueueEvent) : Game :=
  match e with
  | .putOnStack stackObj source controller spec =>
    if g.objects.any (·.id == stackObj) then g
    else
      let ts : Nat := g.timestamp + 1
      let abilityName := spec.abilityName.getD s!"{source.name}'s ability"
      let fresh : GameObject :=
        { id := stackObj
          printed := { name := abilityName, types := #[] }
          owner := source.owner
          controller := some controller
          zone := .stack
          timestamp := ts
          abilityEffect := spec.abilityEffect
          triggeredAbility := spec.triggeredAbility
          isReflexive := spec.isReflexive
          sourceId := spec.sourceId.orElse (fun _ => source.id)
          triggerCauseId := spec.triggerCauseId
          triggerCauseIds := spec.triggerCauseIds
          triggerCauseController := spec.triggerCauseController
          triggerCausePower := spec.triggerCausePower
          triggerCauseStatus := spec.triggerCauseStatus }
      let se : StackEntry :=
        { objectId := stackObj
          controller := controller
          targets := #[]
          delayedTrigger := spec.delayedTrigger
          lastKnownPower := spec.lastKnownPower
          lastKnownToughness := spec.lastKnownToughness }
      { g with
        objects := g.objects.push fresh
        stack := g.stack.push se
        nextObjectId := max g.nextObjectId (stackObj.raw + 1)
        timestamp := max g.timestamp ts
        consecutivePasses := 0 }
  | .triggered .. | .modeChosen .. => g

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

/-- Single-hop CR 400.7e new-object lookup into `expectedZone`: returns `o` if
`id` itself is live in `expectedZone`, or if `id`'s immediate `ZoneEvent.moved`
placed it into `toZone` (`expectedZone toZone`) as `afterId` and `afterId` is
still live in `toZone` (has not flickered or moved again). -/
def followMovedToZone? (g : Game) (id : ObjectId) (expectedZone : Zone → Bool) :
    Option GameObject :=
  match g.objects.find? (·.id == id) with
  | some o => if expectedZone o.zone then some o else none
  | none =>
    match g.events.reverse.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved before after _ toZone _ _ _ _)) =>
        if before.id == some id then
          after.id.filter (· != id) |>.map (·, toZone)
        else none
      | _ => none) with
    | some (afterId, toZone) =>
      if !expectedZone toZone then none
      else (g.objects.find? (·.id == afterId)).filter (·.zone == toZone)
    | none => none

/-- Resolve `id` on the battlefield when it is still a battlefield permanent
(CR 400.7 / 608.2h). -/
def followToBattlefield? (g : Game) (id : ObjectId) : Option GameObject :=
  (g.findObject? id).filter (·.isOnBattlefield)

/-- Like `followMovedToZone?`, also returning the `fromZone` recorded on `id`'s
immediate `ZoneEvent.moved` (or `o.zone` when `id` itself is in `expectedZone`). -/
def followMovedWithOrigin? (g : Game) (id : ObjectId) (expectedZone : Zone → Bool) :
    Option (GameObject × Zone) :=
  match g.objects.find? (·.id == id) with
  | some o => if expectedZone o.zone then some (o, o.zone) else none
  | none =>
    match g.events.reverse.findSome? (fun e =>
      match e.change with
      | .rules (.zone (.moved before after fromZone toZone _ _ _ _)) =>
        if before.id == some id then
          after.id.filter (· != id) |>.map (·, fromZone, toZone)
        else none
      | _ => none) with
    | some (afterId, fromZone, toZone) =>
      if !expectedZone toZone then none
      else ((g.objects.find? (·.id == afterId)).filter (·.zone == toZone)).map (·, fromZone)
    | none => none

/-- Whether `z` is a public zone (CR 400.2). -/
@[inline] def isPublicZone (z : Zone) : Bool :=
  z.isPublic

/-- CR 701.17c: find the object resulting from milling `preId` (`ZoneVerb.mill`)
if it moved from a library into a public zone and is still live in that zone. -/
def followMilledPublic? (g : Game) (preId : ObjectId) : Option GameObject :=
  match g.events.reverse.findSome? (fun e =>
    match e.change with
    | .rules (.zone (.moved before after (.library _) toZone .mill _ _ _)) =>
      if before.id == some preId && isPublicZone toZone then
        after.id.map (·, toZone)
      else none
    | _ => none) with
  | some (afterId, toZone) =>
    (g.objects.find? (·.id == afterId)).filter (·.zone == toZone)
  | none => none

/-- Apply a `StackObjectEvent` to `g` (CR 608 / 707.10). -/
def applyStackObjectEvent (g : Game) (e : StackObjectEvent) : Game :=
  match e with
  | .copied original copy controller =>
    let newId : ObjectId := copy.id.getD ⟨g.nextObjectId⟩
    let ts : Nat := g.timestamp + 1
    let origObj? := (g.objects.find? (·.id == original)).filter (·.zone == .stack)
    let origEntry? := g.stack.find? (·.objectId == original)
    let isFaceDown := copy.faceDown || origObj?.any (·.status.faceDown)
    let faceDownCard : CardDef :=
      { name := "", types := #[.creature], power := some (.fixed 2), toughness := some (.fixed 2) }
    let printed :=
      if isFaceDown then
        copy.copiable.getD faceDownCard
      else
        match copy.copiable.orElse (fun _ => copy.printed) with
        | some p => p
        | none =>
          match origObj? with
          | some o => o.printed
          | none => copy.toCardDef
    let timeCounters :=
      let c := copy.counters.count .time
      if c > 0 then c else origObj?.map (·.status.time) |>.getD 0
    let baseStatus : Status := { faceDown := isFaceDown }
    let copyStatus : Status :=
      if timeCounters > 0 then { baseStatus with counters := baseStatus.counters.set .time timeCounters }
      else baseStatus
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
          status := copyStatus
          timestamp := ts
          isCopy := true
          chosenX := copy.chosenX.orElse (fun _ => orig.chosenX)
          adventurerCard := if isFaceDown then none else orig.adventurerCard
          abilityEffect := orig.abilityEffect
          triggeredAbility := orig.triggeredAbility
          isReflexive := orig.isReflexive
          sourceId := orig.sourceId
          triggerCauseId := orig.triggerCauseId
          triggerCauseIds := orig.triggerCauseIds
          triggerCauseController := orig.triggerCauseController
          triggerCausePower := orig.triggerCausePower
          triggerCauseStatus := orig.triggerCauseStatus }
      | none =>
        { id := newId
          printed := printed
          owner := controller
          controller := some controller
          zone := .stack
          status := copyStatus
          timestamp := ts
          isCopy := true
          chosenX := copy.chosenX
          adventurerCard := if isFaceDown then none else copy.adventurerCard }
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
        let (tgts, div, skipped) :=
          g.events.foldl (fun acc ev =>
            match ev.change with
            | .rules (.cast (.targeted oid ts dv sk)) =>
              if oid == original then
                let ( _, prevDiv, prevSk ) := acc
                (ts, if dv.isEmpty then prevDiv else dv, if sk.isEmpty then prevSk else sk)
              else acc
            | _ => acc) (#[], #[], #[])
        { objectId := newId
          controller := controller
          targets := tgts
          dividedDamage := div
          skippedOptionalSlots := skipped
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
      let st0 :=
        { o.status with
          attacking := false
          attackingTarget := none
          blocking := #[]
          blocked := false }
      { g with objects := g.objects.set! i { o with status := st0 } }
    | none => g

/-- Active resolving source object id and controller, if a spell or ability is
currently resolving (CR 608 / 610.1 / 113.8). -/
def currentResolvingContext? (g : Game) : Option (Option ObjectId × Option PlayerId) :=
  match g.resolvingSpell with
  | some sid =>
    match g.objects.find? (·.id == sid) with
    | some o => some (o.sourceId.orElse (fun _ => some o.id), o.controller)
    | none => some (some sid, g.resolvingContext.map Prod.snd)
  | none =>
    match g.resolvingAbility.bind (fun id => g.objects.find? (·.id == id)) with
    | some o => some (o.sourceId, o.controller)
    | none =>
      match g.resolvingContext with
      | some (src, ctrl) => some (src, some ctrl)
      | none =>
        g.currentInterpWait?.bind fun st =>
          if st.ctx.oneShotEffectId.raw != 0 then some (st.ctx.sourceId, some st.ctx.controller)
          else none

/-- Populate a fresh `EffectId` (and fallback `source` / `controller` from the
current resolving context) on `.oneShotEffect` inside `cause` (CR 610). -/
def resolveOneShotCause (g : Game) : EventCause → EventCause × Option EffectId
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

/-- Resolve an optional `EventCause` for a `Game` action helper:
1. An explicit `some c` wins.
2. Otherwise an active batch's cause (`g.currentBatch`) is reused so every
   sub-event in the batch shares one cause / `EffectId` (CR 608.2c / 610).
3. Otherwise if a spell or ability is actively resolving (`g.currentResolvingContext?`),
   return `.oneShotEffect none ...` (whose `EffectId` is minted when recorded).
4. Otherwise fall back to `defaultCause` without allocating an `EffectId`. -/
def resolveOptionalCause (g : Game) (cause : Option EventCause := none)
    (fallbackSrc : Option ObjectId := none)
    (fallbackCtrl : Option PlayerId := none)
    (defaultCause : EventCause := .gameRule .spellCast) : EventCause :=
  match cause with
  | some c => c
  | none =>
    match g.currentBatch with
    | some (_, some bc) => bc
    | _ =>
      match g.currentResolvingContext? with
      | some (s, c) =>
        .oneShotEffect none (fallbackSrc.orElse (fun _ => s)) (c.orElse (fun _ => fallbackCtrl))
      | none =>
        defaultCause

def object! (g : Game) (id : ObjectId) : GameObject :=
  match g.findObject? id with
  | some o => o
  | none => panic! s!"missing object {id}"

def over (g : Game) : Bool := g.result.isSome

def player (g : Game) (p : PlayerId) : Player :=
  g.players[p.idx]!

def livingPlayers (g : Game) : Array Player :=
  g.players.filter (fun pl => !pl.lost && !pl.leftTheGame)

/-- True while `p` has neither lost nor left the game (CR 104 / 800.4). -/
def stillInGame (g : Game) (p : PlayerId) : Bool :=
  !(g.player p).lost && !(g.player p).leftTheGame

/-- True when living player `p` is the active player or a teammate of the active
player, i.e., it is `p`'s team's turn (CR 805.4a / 810.2). -/
def isOnActiveTeam (g : Game) (p : PlayerId) : Bool :=
  p.idx < g.players.size && g.stillInGame p &&
    (g.activePlayer == p || g.areTeammates g.activePlayer p)

/-- Legal only during the declare blockers step of the caster's (or shared team's) turn (CR 805.4a / 810.2). -/
def canCastForSneak (g : Game) (p : PlayerId) : Bool :=
  g.isOnActiveTeam p && g.step == .declareBlockers

/-- Format a list of player seats' names with English conjunctions
(`"A"`, `"A and B"`, `"A, B, and C"`). -/
def formatPlayerNames (g : Game) (pids : Array PlayerId) : String :=
  let names := pids.map (fun p => (g.player p).name)
  match names.size with
  | 0 => ""
  | 1 => names[0]!
  | 2 => s!"{names[0]!} and {names[1]!}"
  | n =>
    let prefixNames := (names.extract 0 (n - 1)).toList
    s!"{String.intercalate ", " prefixNames}, and {names[n - 1]!}"

/-- Format the win-the-game log message for one or more winning teammates
(CR 104.1 / 810.8a / 810.11). -/
def formatWinMessage (g : Game) (winners : Array PlayerId) : String :=
  if winners.size ≤ 1 then
    s!"{g.formatPlayerNames winners} wins the game"
  else
    s!"{g.formatPlayerNames winners} win the game"

/-- Living opponents of `p` (CR 102.2 / 810). -/
def livingOpponents (g : Game) (p : PlayerId) : Array Player :=
  g.livingPlayers.filter (fun pl => pl.id != p && !g.areTeammates p pl.id)

/-- True when any living opponent of `p` (or that opponent's Two-Headed Giant
team, CR 810.10a,d) has at least `n` poison counters. -/
def opponentPoisonedAtLeast (g : Game) (p : PlayerId) (n : Nat) : Bool :=
  (g.livingOpponents p).any (fun opp => g.teamPoison opp.id ≥ n)

def battlefield (g : Game) : Array GameObject :=
  g.objects.filter GameObject.isOnBattlefield

/-- True when a `.gameRule .powerUpsForbidden _` continuous effect was already
active at index `0` before `g.events` (created solely on extra turns, CR 500.7). -/
def hasPreLogPowerUpsForbidden (g : Game) : Bool :=
  let isPowerUpsForbidden (s : ContinuousEffectSpec) : Bool :=
    match s with
    | .gameRule .powerUpsForbidden _ => true
    | _ => false
  let createdEids : Array EffectId :=
    g.events.foldl (fun acc ev =>
      match ev.change with
      | .rules (.continuousEffect (.created eid _)) => acc.push eid
      | _ => acc) #[]
  g.activeEffects.any (fun (eid, s) =>
    isPowerUpsForbidden s && !createdEids.contains eid) ||
    g.events.any (fun ev =>
      match ev.change with
      | .rules (.continuousEffect (.expired eid (some s))) =>
        isPowerUpsForbidden s && !createdEids.contains eid
      | _ => false)

/-- Infer whether a pre-`turnBegan` slice on turn `t0` with active player `ap`
began inside an extra turn (CR 500.7 / 805.8). -/
def inferPreLogTurnIsExtra (g : Game) (ap : PlayerId) (t0 : Nat) : Bool :=
  let sameTeam (a b : PlayerId) : Bool := a == b || g.areTeammates a b
  match g.events.findSome? (fun ev =>
    match ev.change with
    | .rules (.turn (.turnBegan p extra)) =>
      if ev.turn == t0 && sameTeam ap p then some extra else none
    | _ => none) with
  | some extra => extra
  | none =>
    if g.hasPreLogPowerUpsForbidden then true
    else Id.run do
      let n := g.players.size
      if n == 0 then return false
      let hasStartingPlayer :=
        g.events.any fun ev =>
          match ev.change with
          | .engine (.startingPlayer _) => true
          | _ => false
      let addedMidLog (p : PlayerId) : Bool :=
        g.events.any fun ev =>
          match ev.change with
          | .engine (.addPlayer pl) => pl.id == p
          | _ => false
      let hasLeaveEvent (p : PlayerId) : Bool :=
        g.events.any fun ev =>
          match ev.change with
          | .rules (.player (.lost q ..))
          | .rules (.player (.leftGame q)) => q == p
          | _ => false
      let alive0 : Array Bool := Array.ofFn (n := n) fun ⟨k, _⟩ =>
        let pk : PlayerId := ⟨k⟩
        !addedMidLog pk && (g.stillInGame pk || hasLeaveEvent pk)
      let isAliveAt (al : Array Bool) (q : PlayerId) : Bool :=
        q.idx < n && al[q.idx]!
      if !hasStartingPlayer && t0 >= 2 && g.startingPlayer.idx < n then
        let startSeat := g.startingPlayer
        let startEnd := (g.teamMembers startSeat).back? |>.getD startSeat
        if sameTeam ap startSeat then
          let mut otherTeams : Array PlayerId := #[]
          for k in [1 : n + 1] do
            let s : PlayerId := ⟨(startEnd.idx + k) % n⟩
            if !sameTeam s startSeat &&
                (g.teamMembers s).any (isAliveAt alive0) &&
                !otherTeams.any (sameTeam · s) then
              otherTeams := otherTeams.push s
          if !otherTeams.isEmpty && t0 <= otherTeams.size + 1 then
            return true
        else
          let mut betweenTeams : Array PlayerId := #[]
          for k in [1 : n + 1] do
            let s : PlayerId := ⟨(startEnd.idx + k) % n⟩
            if sameTeam s ap then
              break
            if !sameTeam s startSeat &&
                (g.teamMembers s).any (isAliveAt alive0) &&
                !betweenTeams.any (sameTeam · s) then
              betweenTeams := betweenTeams.push s
          if t0 <= betweenTeams.size + 1 then
            return true
      let team := g.teamMembers ap
      let apTeamEnd := team.back? |>.getD ap
      let mut scanAlive := alive0
      for ev in g.events do
        match ev.change with
        | .engine (.startingPlayer _) => break
        | .engine (.addPlayer pl) =>
          if pl.id.idx < n then
            scanAlive := scanAlive.set! pl.id.idx (!pl.lost && !pl.leftTheGame)
        | .rules (.player (.lost q ..))
        | .rules (.player (.leftGame q)) =>
          if q.idx < n then
            scanAlive := scanAlive.set! q.idx false
        | .rules (.turn (.turnBegan q false)) =>
          let mut exp? : Option PlayerId := none
          for k in [1 : n + 1] do
            if exp?.isNone then
              let cand : PlayerId := ⟨(apTeamEnd.idx + k) % n⟩
              if isAliveAt scanAlive cand then
                exp? := some cand
          if let some exp := exp? then
            if !sameTeam exp ap && q != exp then
              return true
          break
        | _ => pure ()
      let apIdx := (team.findIdx? (· == ap)).getD 0
      let remTeammates := team.extract (apIdx + 1) team.size
      if remTeammates.isEmpty then return false
      let countInProg (stSeats : Array PlayerId) (stExtra : Bool)
          (q : Array PlayerId) : Nat :=
        if !stExtra || stSeats.isEmpty then 0
        else Id.run do
          let curTeam := g.teamMembers stSeats[0]!
          let lastSeat := stSeats.back!
          let mut remIdx : Nat :=
            match curTeam.findIdx? (· == lastSeat) with
            | some k => k + 1
            | none => curTeam.size
          let mut cnt : Nat := 0
          for x in q do
            match (curTeam.extract remIdx curTeam.size).findIdx? (· == x) with
            | some rel =>
              remIdx := remIdx + rel + 1
              cnt := cnt + 1
            | none =>
              return cnt
          return cnt
      let seats0 := team.extract 0 (apIdx + 1)
      let mut simSeats := if seats0.isEmpty then #[ap] else seats0
      let mut simExtra := false
      let mut simAlive := alive0
      let mut simQ : Array PlayerId := #[]
      for ev in g.events do
        match ev.change with
        | .engine (.startingPlayer _) => return false
        | .engine (.addPlayer pl) =>
          if pl.id.idx < n then
            simAlive := simAlive.set! pl.id.idx (!pl.lost && !pl.leftTheGame)
        | .rules (.player (.lost q ..))
        | .rules (.player (.leftGame q)) =>
          if q.idx < n then
            simAlive := simAlive.set! q.idx false
        | .rules (.turn (.extraTurnAdded player _)) =>
          let inProg := countInProg simSeats simExtra simQ
          let pTeam := g.teamMembers player
          simQ := simQ.extract 0 inProg ++ pTeam ++ simQ.extract inProg simQ.size
        | .rules (.turn (.turnBegan p extra)) =>
          let sameShared :=
            extra == simExtra && !simSeats.isEmpty &&
              g.areTeammates simSeats[0]! p && !simSeats.contains p
          let trimmed := (simQ.toList.dropWhile (fun q => !isAliveAt simAlive q)).toArray
          if extra then
            if trimmed[0]? == some p then
              simQ := trimmed.extract 1 trimmed.size
            else
              if remTeammates.contains p && isAliveAt simAlive ap then
                return true
              let pTeam := g.teamMembers p
              let pPos := (pTeam.findIdx? (· == p)).getD 0
              simQ := pTeam.extract (pPos + 1) pTeam.size
          else if !sameShared then
            simQ := trimmed
          if sameShared then
            simSeats := simSeats.push p
          else
            simSeats := #[p]
            simExtra := extra
        | _ => pure ()
      let survivingPre :=
        if simQ.size < g.extraTurns.size then
          g.extraTurns.extract simQ.size g.extraTurns.size
        else #[]
      let survCount (q : PlayerId) : Nat := (survivingPre.filter (· == q)).size
      let apSurv := survCount ap
      return remTeammates.any (fun tm => survCount tm > apSurv)

/-- `(seats, isExtra)` for the current shared turn in `g.events` (up to `limit?`,
defaulting to all of `g.events`), tracking whether the shared turn is an extra
turn (CR 805.4 / 805.8 / 810.2). -/
def currentSharedTurnState (g : Game) (limit? : Option Nat := none) :
    Array PlayerId × Bool :=
  let endIdx := min (limit?.getD g.events.size) g.events.size
  Id.run do
    let mut seats : Array PlayerId := #[⟨0⟩]
    let mut seatsExtra : Bool := false
    let mut seenStartOrTurnBegan : Bool := false
    let mut seenPreLogStep : Bool := false
    for i in [0:endIdx] do
      let ev := g.events[i]!
      match ev.change with
      | .engine (.startingPlayer v) =>
        seats := #[v]
        seatsExtra := false
        seenStartOrTurnBegan := true
      | .rules (.turn (.turnBegan q extra)) =>
        seenStartOrTurnBegan := true
        if extra == seatsExtra && !seats.isEmpty &&
            g.areTeammates seats[0]! q && !seats.contains q then
          seats := seats.push q
        else
          seats := #[q]
          seatsExtra := extra
      | .rules (.turn (.stepBegan _ ap))
      | .rules (.turn (.turnEnded ap)) =>
        if !seenStartOrTurnBegan then
          if !seenPreLogStep then
            seenPreLogStep := true
            let team := g.teamMembers ap
            let apPos := (team.findIdx? (· == ap)).getD 0
            let s0 := team.extract 0 (apPos + 1)
            seats := if s0.isEmpty then #[ap] else s0
            seatsExtra := g.inferPreLogTurnIsExtra ap ev.turn
          else if !seats.isEmpty && g.areTeammates seats[0]! ap && !seats.contains ap then
            seats := seats.push ap
      | _ => pure ()
    if !seenStartOrTurnBegan && !seenPreLogStep then
      let ap := g.activePlayer
      let team := g.teamMembers ap
      let apPos := (team.findIdx? (· == ap)).getD 0
      let s0 := team.extract 0 (apPos + 1)
      seats := if s0.isEmpty then #[ap] else s0
      seatsExtra := g.inferPreLogTurnIsExtra ap g.turnNumber
    return (seats, seatsExtra)

/-- Seats that have begun as part of the current shared turn in `g.events`
(CR 805.4 / 805.8 / 810.2). In non-team games this has size 1 (`#[g.activePlayer]`). -/
def currentSharedTurnSeats (g : Game) : Array PlayerId :=
  (g.currentSharedTurnState).1

/-- True when the current shared turn is an extra turn (CR 500.7 / 805.8). -/
def currentSharedTurnIsExtra (g : Game) : Bool :=
  (g.currentSharedTurnState).2

/-- Seat of the most recent regular (non-extra) turn in `g.events`, defaulting
to `g.startingPlayer` before any turn events (CR 500.7 / 805.4 / 805.8). -/
def lastRegularTurnSeat (g : Game) : PlayerId := Id.run do
  let mut seat : PlayerId := g.startingPlayer
  let mut seenStart : Bool := false
  let mut seenTurnBegan : Bool := false
  let mut seenPreLogStep : Bool := false
  for ev in g.events do
    match ev.change with
    | .engine (.startingPlayer v) =>
      seat := v
      seenStart := true
      seenTurnBegan := false
    | .rules (.turn (.turnBegan q extra)) =>
      seenTurnBegan := true
      if !extra then
        seat := q
    | .rules (.turn (.stepBegan _ ap))
    | .rules (.turn (.turnEnded ap)) =>
      if !seenTurnBegan then
        seenPreLogStep := true
        if !g.inferPreLogTurnIsExtra ap ev.turn then
          seat := ap
    | _ => pure ()
  if !seenStart && !seenTurnBegan && !seenPreLogStep &&
      !g.inferPreLogTurnIsExtra g.activePlayer g.turnNumber then
    seat := g.activePlayer
  return seat

/-- True when `g.activePlayer` is the first living seat of the current shared turn
(CR 805.4 / 810.2). Always true in non-team games. -/
def isSharedTurnFirstSeat (g : Game) : Bool :=
  g.currentSharedTurnSeats.size ≤ 1

/-- True when no further living teammate seat remains in the current shared turn
(CR 805.4 / 805.8 / 810.2). Always true in non-team games. -/
def isSharedTurnFinalSeat (g : Game) : Bool :=
  let n := g.players.size
  if n == 0 then true
  else
    let seats := g.currentSharedTurnSeats
    Id.run do
      for k in [1:n+1] do
        let q : PlayerId := ⟨(g.activePlayer.idx + k) % n⟩
        if g.stillInGame q then
          return !(g.areTeammates g.activePlayer q && !seats.contains q)
      return true

/-- Whether a new shared turn of `p` (or `p`'s Two-Headed Giant teammate, CR 805.4 /
805.8 / 810.2) has begun (`TurnEvent.turnBegan`) in `g.events` after the creation of
continuous effect `eid` (CR 611.2a). -/
def hasTurnBegunSince (g : Game) (eid : EffectId) (p : PlayerId) : Bool :=
  g.events.foldl (fun (seats, seatsExtra, seenCreate, seenTurn) ev =>
    match ev.change with
    | .engine (.startingPlayer v) => (#[v], false, seenCreate, seenTurn)
    | .rules (.continuousEffect (.created id _)) =>
      if id == eid then (seats, seatsExtra, true, false)
      else (seats, seatsExtra, seenCreate, seenTurn)
    | .rules (.turn (.turnBegan q extra)) =>
      let sameSharedTurn :=
        extra == seatsExtra && !seats.isEmpty &&
          g.areTeammates seats[0]! q && !seats.contains q
      let seats' := if sameSharedTurn then seats.push q else #[q]
      if !sameSharedTurn && seenCreate && (q == p || g.areTeammates q p) then
        (seats', extra, seenCreate, true)
      else
        (seats', extra, seenCreate, seenTurn)
    | _ => (seats, seatsExtra, seenCreate, seenTurn)) (#[⟨0⟩], false, false, false) |>.2.2.2

/-- Whether another shared turn has begun (`TurnEvent.turnBegan _ _`) in `g.events`
after the first new shared turn of `p` (and `p`'s Two-Headed Giant teammate, CR 805.4 /
805.8 / 810.2) that began since continuous effect `eid` was created (CR 724.1: "during
their next turn" lasts until the beginning of the next turn). -/
def hasTurnAfterBegunSince (g : Game) (eid : EffectId) (p : PlayerId) : Bool :=
  g.events.foldl (fun (seats, seatsExtra, seenCreate, seenTeamTurn, seenAfter) ev =>
    match ev.change with
    | .engine (.startingPlayer v) => (#[v], false, seenCreate, seenTeamTurn, seenAfter)
    | .rules (.continuousEffect (.created id _)) =>
      if id == eid then (seats, seatsExtra, true, false, false)
      else (seats, seatsExtra, seenCreate, seenTeamTurn, seenAfter)
    | .rules (.turn (.turnBegan q extra)) =>
      let sameSharedTurn :=
        extra == seatsExtra && !seats.isEmpty &&
          g.areTeammates seats[0]! q && !seats.contains q
      let seats' := if sameSharedTurn then seats.push q else #[q]
      if sameSharedTurn || !seenCreate || seenAfter then
        (seats', extra, seenCreate, seenTeamTurn, seenAfter)
      else if seenTeamTurn then
        (seats', extra, seenCreate, seenTeamTurn, true)
      else if q == p || g.areTeammates q p then
        (seats', extra, seenCreate, true, false)
      else
        (seats', extra, seenCreate, seenTeamTurn, seenAfter)
    | _ => (seats, seatsExtra, seenCreate, seenTeamTurn, seenAfter))
    (#[⟨0⟩], false, false, false, false) |>.2.2.2.2

/-- Timestamp `(tier, sub)` of `k` counters on `oid` (CR 613.7c): putting a new
counter of kind `k` on `oid` gives all `k` counters on `oid` that new timestamp. -/
def counterTimestamp (g : Game) (oid : ObjectId) (k : CounterKind) : Nat × Nat :=
  Id.run do
    let mut alive := false
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
      | .rules (.zone (.moved before after _ _ _ _ entersWith _)) =>
        if before.id == some oid && after.id != some oid then
          alive := false
        if after.id == some oid then
          alive := true
          let c := max (after.counters.count k) (entersWith.count k)
          ts? := if c > 0 then some i else none
          prevCount? := some c
      | .rules (.zone (.created eo _)) =>
        if eo.id == some oid then
          alive := true
          let c := eo.counters.count k
          ts? := if c > 0 then some i else none
          prevCount? := some c
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some oid then
          alive := false
      | .rules (.stackObject (.copied _ copy _)) =>
        if copy.id == some oid then
          alive := true
          let c := copy.counters.count k
          ts? := if c > 0 then some i else none
          prevCount? := some c
      | .rules (.triggerQueue (.putOnStack stackObj _ _ _)) =>
        if stackObj == oid && !alive then
          alive := true
          ts? := none
          prevCount? := some 0
      | .rules (.cast (.abilityActivated ability source _ (.nonMana ..))) =>
        if ability == oid && !alive && source.id != some oid then
          alive := true
          ts? := none
          prevCount? := some 0
      | .engine (.materializeObject o _) =>
        if o.id == oid then
          alive := true
          let c := o.status.counters.count k
          ts? := if c > 0 then some i else none
          prevCount? := some c
      | _ => pure ()
    return match ts? with
      | some idx => (1, idx)
      | none => (0, 1)

/-- Timestamp `(tier, sub)` when `aura` most recently became attached to `hostId` (CR 613.7e). -/
def attachmentTimestamp (g : Game) (aura : GameObject) (hostId : ObjectId) : Nat × Nat :=
  Id.run do
    let aid := aura.id
    let mut alive := false
    let mut ts? : Option Nat := none
    for i in [0:g.events.size] do
      let ev := g.events[i]!
      match ev.change with
      | .rules (.permanent (.attached aEo hid _)) =>
        if aEo.id == some aid then
          ts? := if hid == hostId then some i else none
      | .rules (.permanent (.unattached aEo _)) =>
        if aEo.id == some aid then
          ts? := none
      | .rules (.zone (.moved before after _ toZone ..)) =>
        if before.id == some aid && after.id != some aid then
          alive := false
        if after.id == some aid then
          alive := true
          ts? := if toZone == .battlefield && after.attachedTo == some hostId then some i else none
      | .rules (.zone (.created eo _)) =>
        if eo.id == some aid then
          alive := true
          ts? := if eo.zone == .battlefield && eo.attachedTo == some hostId then some i else none
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some aid then
          alive := false
      | .rules (.stackObject (.copied _ copy _)) =>
        if copy.id == some aid then
          alive := true
          ts? := none
      | .rules (.triggerQueue (.putOnStack stackObj _ _ _)) =>
        if stackObj == aid && !alive then
          alive := true
          ts? := none
      | .rules (.cast (.abilityActivated ability source _ (.nonMana ..))) =>
        if ability == aid && !alive && source.id != some aid then
          alive := true
          ts? := none
      | .engine (.materializeObject o _) =>
        if o.id == aid then
          alive := true
          ts? := if o.zone == .battlefield && o.attachedTo == some hostId then some i else none
      | _ => pure ()
    return match ts? with
      | some idx => (1, idx)
      | none => (0, 2 + aura.timestamp)

/-- Timestamp `(tier, sub)` when `obj` entered its current zone (CR 613.7d). -/
def objectEntryTimestamp (g : Game) (obj : GameObject) : Nat × Nat :=
  Id.run do
    let oid := obj.id
    let mut alive := false
    let mut ts? : Option Nat := none
    for i in [0:g.events.size] do
      match g.events[i]!.change with
      | .rules (.zone (.moved before after ..)) =>
        if before.id == some oid && after.id != some oid then
          alive := false
        if after.id == some oid then
          alive := true
          ts? := some i
      | .rules (.zone (.created eo _)) =>
        if eo.id == some oid then
          alive := true
          ts? := some i
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some oid then
          alive := false
      | .rules (.stackObject (.copied _ copy _)) =>
        if copy.id == some oid then
          alive := true
          ts? := some i
      | .rules (.triggerQueue (.putOnStack stackObj _ _ _)) =>
        if stackObj == oid && !alive then
          alive := true
          ts? := some i
      | .rules (.cast (.abilityActivated ability source _ (.nonMana ..))) =>
        if ability == oid && !alive && source.id != some oid then
          alive := true
          ts? := some i
      | .engine (.materializeObject o _) =>
        if o.id == oid then
          alive := true
          ts? := some i
      | _ => pure ()
    return match ts? with
      | some idx => (1, idx)
      | none => (0, 2 + obj.timestamp)

/-- Timestamp `(tier, sub)` when continuous effect `eid` was created (CR 613.7b). -/
def effectTimestamp (g : Game) (eid : EffectId) (pos : Nat) : Nat × Nat :=
  Id.run do
    for rev in [0:g.events.size] do
      let i := g.events.size - 1 - rev
      match g.events[i]!.change with
      | .rules (.continuousEffect (.created id _)) =>
        if id == eid then return (1, i)
      | _ => pure ()
    return (0, 1000000 + pos)

/-- Later of two CR 613.7 `(tier, sub)` timestamps (CR 613.7a). -/
def maxTs (a b : Nat × Nat) : Nat × Nat :=
  if a.1 != b.1 then
    if a.1 > b.1 then a else b
  else
    if a.2 >= b.2 then a else b

-- Layer 1: Copy effects and face-down status (CR 613.1a / 613.2 / 613.7 / 613.8)

private structure Layer1Entry where
  idx : Nat
  eid : EffectId
  ts : Nat × Nat
  scope : ObjectScope
  card : CardDef
deriving Inhabited

private def isOneShotEffectCause : EventCause → Bool
  | .oneShotEffect .. => true
  | .replaced _ orig => isOneShotEffectCause orig
  | _ => false

/-- `(createdIdx, cause)` recorded on `ContinuousEffectEvent.created` for `eid` (CR 611.2b–c). -/
private def effectCreatedInfo? (g : Game) (eid : EffectId) : Option (Nat × EventCause) :=
  Id.run do
    for rev in [0:g.events.size] do
      let i := g.events.size - 1 - rev
      match g.events[i]! with
      | .rules _ (.continuousEffect (.created id _)) cause _ =>
        if id == eid then return some (i, cause)
      | _ => pure ()
    return none

private def checkValidObjId (pred : ObjectId → Bool) (id : ObjectId) : Bool :=
  id != noSourceSentinelId && pred id

private def checkValidOptObjId (pred : ObjectId → Bool) : Option ObjectId → Bool
  | some id => checkValidObjId pred id
  | none => false

private def checkValidObjIds (pred : ObjectId → Bool) (ids : Array ObjectId) : Bool :=
  ids.any (checkValidObjId pred)

private def attackTargetAnyObjId (pred : ObjectId → Bool) : AttackTarget → Bool
  | .planeswalker pid | .battle pid => checkValidObjId pred pid
  | .player _ => false

private def targetAnyObjId (pred : ObjectId → Bool) : Target → Bool
  | .permanent tid | .card tid => checkValidObjId pred tid
  | .player _ => false

private def statusAnyObjId (pred : ObjectId → Bool) (s : Status) : Bool :=
  s.attackingTarget.any (attackTargetAnyObjId pred) ||
    checkValidObjIds pred s.blocking ||
    checkValidOptObjId pred s.phasedWith

private def gameObjAnyObjId (pred : ObjectId → Bool) (o : GameObject) : Bool :=
  checkValidObjId pred o.id ||
    statusAnyObjId pred o.status ||
    checkValidOptObjId pred o.sourceId ||
    checkValidOptObjId pred o.attachedTo ||
    checkValidObjIds pred o.linkedExile ||
    checkValidObjIds pred o.leaveTriggerExile ||
    checkValidOptObjId pred o.triggerCauseId ||
    o.triggerCauseStatus.any (statusAnyObjId pred) ||
    checkValidObjIds pred o.triggerCauseIds ||
    checkValidOptObjId pred o.exiledBy

private def eventObjAnyObjId (pred : ObjectId → Bool) (eo : EventObject) : Bool :=
  checkValidOptObjId pred eo.id ||
    checkValidObjIds pred eo.blockingIds ||
    checkValidOptObjId pred eo.attachedTo ||
    eo.attackingTarget.any (attackTargetAnyObjId pred)

private def repEffKindIsProspectiveEnter : ReplacementEffectKind → Bool
  | .entersTappedSelf
  | .entersUntappedPayLife _
  | .entersTappedDeclinePayLife
  | .entersUntappedBehold _ _
  | .entersTappedDeclineBehold
  | .asEntersChooseColor _
  | .asEntersChooseCreatureTypePrompt
  | .asEntersChooseCreatureType _
  | .asEntersChooseOdd _
  | .asEntersChooseCardNamePrompt
  | .asEntersChooseCardName _
  | .asEntersChooseCardType _
  | .asEntersChooseAnchor _
  | .entersWithLoyalty
  | .entersWithPlusOneCounters
  | .entersWithXPlusOne
  | .entersWithIndestructibleCounter
  | .entersWithShield
  | .entersWithHopePerCreature
  | .entersWithSagaLore
  | .entersUnderControl
  | .entersAsCopy
  | .entersAsCopyCreatureUntilEot _
  | .declineEntersAsCopy
  | .entersBackFaceUp
  | .asEntersAttachAura _
  | .entersWithExtraCounters => true
  | _ => false

private def repEffKindAnyObjId (pred : ObjectId → Bool) : ReplacementEffectKind → Bool
  | .entersUntappedBehold bid _ => checkValidObjId pred bid
  | .entersAsCopyCreatureUntilEot tid => checkValidObjId pred tid
  | .asEntersAttachAura hid => checkValidObjId pred hid
  | _ => false

private def repIdAnyObjId (pred : ObjectId → Bool) (r : ReplacementId)
    (prospectivePred : ObjectId → Bool := pred) : Bool :=
  let objPred := if repEffKindIsProspectiveEnter r.kind then prospectivePred else pred
  checkValidOptObjId objPred r.object ||
    checkValidOptObjId pred r.grantor ||
    repEffKindAnyObjId pred r.kind

private def repKindAnyObjId (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred) : ReplacementKind → Bool
  | .entersTappedSelf oid
  | .entersUntappedPayLife oid _
  | .entersTappedDeclinePayLife oid
  | .entersTappedDeclineBehold oid
  | .asEntersChooseColor oid _
  | .asEntersChooseCreatureType oid _
  | .asEntersChooseOdd oid _
  | .asEntersChooseCardName oid _
  | .asEntersChooseCardType oid _
  | .asEntersChooseAnchor oid _
  | .entersWithCountersSelf oid _ _
  | .declineEntersAsCopy oid => checkValidObjId prospectivePred oid
  | .entersUntappedBehold oid bid _ =>
    checkValidObjId prospectivePred oid || checkValidObjId pred bid
  | .entersAsCopyCreatureUntilEot oid tid =>
    checkValidObjId prospectivePred oid || checkValidObjId pred tid
  | .asEntersAttachAura oid hid =>
    checkValidObjId prospectivePred oid || checkValidObjId pred hid
  | .entersUnderControl oid _
  | .entersAsCopy oid _
  | .entersBackFaceUp oid
  | .entersWithExtraCounters oid _ _ => checkValidOptObjId prospectivePred oid
  | .shieldCounterDestroy oid
  | .stunCounterUntap oid => checkValidObjId pred oid
  | .modifyCountersPut oid _ _ _
  | .exileInsteadOfStackLeave oid
  | .exileInsteadOfGraveyard oid _
  | .addNoncombatDamage oid _
  | .multiplyDamage oid _ => checkValidOptObjId pred oid
  | _ => false

private def prevKindAnyObjId (pred : ObjectId → Bool) : PreventionKind → Bool
  | .preventAllDamageToPermanent tid => checkValidObjId pred tid
  | .preventAllDamageFromSource sid => checkValidObjId pred sid
  | .protectionPreventDamage pid sid => checkValidObjId pred pid || checkValidObjId pred sid
  | .shieldCounterPreventDamage oid => checkValidObjId pred oid
  | _ => false

private def eventCauseAnyObjId (c : EventCause) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  match c with
  | .costPayment kind _ (some id) =>
    let p :=
      match kind with
      | .life | .behold => if etbCostProspective? kind id then prospectivePred else pred
      | _ => pred
    checkValidObjId p id
  | .costPayment _ _ none => false
  | .oneShotEffect _ src _ => checkValidOptObjId pred src
  | .replaced rep orig =>
    repIdAnyObjId pred rep prospectivePred ||
      eventCauseAnyObjId orig pred prospectivePred etbCostProspective?
  | _ => false

private def eventCauseReferencesObject (c : EventCause) (oid : ObjectId) : Bool :=
  eventCauseAnyObjId c (· == oid)

private def specAnyObjId (spec : ContinuousEffectSpec) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred) : Bool :=
  (match spec with
   | .layered (.objects ids) _ _ => checkValidObjIds pred ids
   | .playerRule _ (.protectionFrom _ srcId? _) _
   | .playerRule _ (.hexproof _ srcId? _) _ => checkValidOptObjId pred srcId?
   | .permission _ (.playFromExile id perm) _ =>
     checkValidObjId pred id || checkValidOptObjId pred perm.prepareSource
   | .permission _ (.flashback id) _ => checkValidObjId pred id
   | .permission _ (.colorlessGrant id c) _ => checkValidObjId pred id || checkValidObjId pred c
   | .gameRule (.cantUntap id s) _ => checkValidObjId pred id || checkValidObjId pred s
   | .gameRule (.cantBeBlockedByPlayer id _) _
   | .gameRule (.cantBeBlockedExceptByHaste id) _
   | .gameRule (.cantBlock id) _
   | .gameRule (.uncounterable id) _
   | .gameRule (.commandEmblem id) _ => checkValidObjId pred id
   | .replacement r _ =>
     repIdAnyObjId pred r.id prospectivePred ||
       checkValidOptObjId pred r.source ||
       repKindAnyObjId pred prospectivePred r.kind
   | .prevention p _ =>
     repIdAnyObjId pred p.id prospectivePred ||
       checkValidOptObjId pred p.source ||
       prevKindAnyObjId pred p.kind
   | _ => false) ||
  match spec.duration with
  | .whileSourceOnBattlefield src | .untilSourceLeaves src
  | .whileSourceHasCounter src _ | .whileInZone src _ => checkValidObjId pred src
  | _ => false

private def specReferencesObject (spec : ContinuousEffectSpec) (oid : ObjectId) : Bool :=
  specAnyObjId spec (· == oid)

private def delayedKindAnyObjId (pred : ObjectId → Bool) : DelayedTriggerKind → Bool
  | .endStepReturn oid
  | .endStepExile oid
  | .endStepSacrifice oid
  | .endOfCombatExile oid
  | .endOfCombatSacrifice oid
  | .endStepGraveReturn oid _ => checkValidObjId pred oid
  | .lokiCopyNextInstantSorceryThisTurn sid _ => checkValidOptObjId pred sid
  | _ => false

private def delayedTriggerAnyObjId (dt : DelayedTrigger) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  dt.source.any (gameObjAnyObjId pred) ||
    delayedKindAnyObjId pred dt.kind ||
    eventCauseAnyObjId dt.cause pred prospectivePred etbCostProspective?

private def stackEntryAnyObjId (e : StackEntry) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  checkValidObjId pred e.objectId ||
    e.targets.any (targetAnyObjId pred) ||
    e.delayedTrigger.any (fun (k, c) =>
      delayedKindAnyObjId pred k || eventCauseAnyObjId c pred prospectivePred etbCostProspective?)

private def playerAnyObjId (pl : Player) (pred : ObjectId → Bool) : Bool :=
  checkValidObjIds pred pl.library ||
    checkValidObjIds pred pl.hand ||
    checkValidObjIds pred pl.graveyard ||
    checkValidOptObjId pred pl.ringBearerId ||
    pl.manaPool.units.any (fun u => checkValidOptObjId pred u.source)

private def enteringAttackItemAnyObjId (it : EnteringAttackItem) (pred : ObjectId → Bool) : Bool :=
  match it with
  | .token _ _ _ opts _ => opts.any (attackTargetAnyObjId pred)
  | .card cid _ _ _ _ _ _ _ opts =>
    checkValidObjId pred cid || opts.any (attackTargetAnyObjId pred)

private def searchDestAnyObjId (d : SearchDest) (pred : ObjectId → Bool) : Bool :=
  match d with
  | .exileLinked sid => checkValidOptObjId pred sid
  | _ => false

private def afterRandomAnyObjId (ar : AfterRandom) (pred : ObjectId → Bool) : Bool :=
  match ar with
  | .revealRandomCreatureThenBottom _ ids | .putOnTop _ ids => checkValidObjIds pred ids
  | .beholdUntap _ lid _ => checkValidObjId pred lid
  | _ => false

private def postCastCleanupAnyObjId (pc : PostCastCleanup) (pred : ObjectId → Bool) : Bool :=
  match pc with
  | .cascadeBottom _ id os
  | .grimaBottom _ id os
  | .lookedBottom _ id os => checkValidObjId pred id || checkValidObjIds pred os
  | .copyCeaseToExist cid => checkValidObjId pred cid

private def stepOutcomeAnyObjId (o : StepOutcome) (pred : ObjectId → Bool) : Bool :=
  checkValidObjIds pred o.objects

private def storedEvalEnvAnyObjId (env : StoredEvalEnv) (pred : ObjectId → Bool) : Bool :=
  checkValidOptObjId pred env.sourceId ||
    env.sourceSnapshot.any (eventObjAnyObjId pred) ||
    env.targetSlots.any (·.any (targetAnyObjId pred)) ||
    checkValidOptObjId pred env.triggerSubjectId ||
    checkValidObjIds pred env.triggerSubjectIds ||
    env.triggerSubjectSnapshot.any (eventObjAnyObjId pred) ||
    checkValidObjIds pred env.costPaidObjects ||
    env.stepEnv.any (fun (_, o) => stepOutcomeAnyObjId o pred) ||
    env.lkiObjects.any (fun (id, eo) => checkValidObjId pred id || eventObjAnyObjId pred eo)

private def interpContAnyObjId (k : InterpCont) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  match k with
  | .bindClose _ _ _ _ extra? => extra?.any (stepOutcomeAnyObjId · pred)
  | .forEachObjectRest _ ids _ => checkValidObjIds pred ids
  | .afterPutToBattlefield fid _ _ c
  | .afterExileReturnBriefly _ fid _ _ c
  | .afterReturnTappedEndStepExile _ fid _ c =>
    checkValidObjId pred fid || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .logIfCountersIncreased tid _ _
  | .exploreAfterLandMove _ tid _ _
  | .exploreOfferGraveyard _ tid => checkValidObjId pred tid
  | .applyAggregatedLifelink _ c
  | .afterTokensEnter _ _ _ c => eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterRevealUntil _ rest _ dack c =>
    checkValidObjIds pred rest || checkValidObjIds pred dack ||
      eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterDistinctSearchMove _ rem c =>
    checkValidObjIds pred rem || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterMoveLoop rem _ _ _ c _ =>
    checkValidObjIds pred rem || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterMillOfferPermanentOrGainLife _ preIds _
  | .worldsCollectPlayers _ _ preIds => checkValidObjIds pred preIds
  | .afterDrawAddPlusOnesForDiscards _ tid? => checkValidOptObjId pred tid?
  | .worldsAfterPut _ vc => vc.any (fun (id, _, _) => checkValidObjId pred id)
  | .afterDamagePermanentsLoop rem _ _ src? _ _ c =>
    checkValidObjIds pred rem || src?.any (eventObjAnyObjId pred) ||
      eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterDividedDamageLoop rem _ src? _ c =>
    rem.any (fun (_, t, _) => targetAnyObjId pred t) || src?.any (eventObjAnyObjId pred) ||
      eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterMixedDamageLoop rem _ src? _ c _ _ pe? =>
    rem.any (fun (t, _) => targetAnyObjId pred t) || src?.any (eventObjAnyObjId pred) ||
      pe?.any (fun (oid, _, _) => checkValidObjId pred oid) ||
      eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterCounterOpLoop rem _ c _ =>
    checkValidObjIds pred rem || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterCopyAndCastExileLoop rem ex _ c pf? _ =>
    checkValidObjIds pred rem || checkValidObjIds pred ex ||
      pf?.any (fun (id, _) => checkValidObjId pred id) ||
      eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .afterMoveCountersPut tid _ c =>
    checkValidObjId pred tid || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | _ => false

private def interpStateAnyObjId (st : InterpState) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  st.ctx.targets.any (targetAnyObjId pred) ||
    st.ctx.targetSlots.any (·.any (targetAnyObjId pred)) ||
    checkValidOptObjId pred st.ctx.sourceId ||
    checkValidOptObjId pred st.ctx.triggerSubjectId ||
    checkValidObjIds pred st.ctx.triggerSubjectIds ||
    st.ctx.sourceSnapshot.any (eventObjAnyObjId pred) ||
    st.ctx.triggerSubjectSnapshot.any (eventObjAnyObjId pred) ||
    st.stack.any (interpContAnyObjId · pred prospectivePred etbCostProspective?)

private def resolutionChoiceAnyObjId (fc : ResolutionChoice) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  match fc with
  | .topOrBottomDamage id _ sid => checkValidObjId pred id || checkValidOptObjId pred sid
  | .sphinxsApproach id
  | .mayMovePlusOne id
  | .allianceMode id _
  | .gollumMode id _
  | .triggerModes id _ _
  | .upToTriggerModes id _ _
  | .stackHydeMode id
  | .chooseKeyword id _
  | .costPicks id _ _
  | .maySacrificeAnotherCreatureForPower id
  | .maySacrificeAnotherForDrawTreasure id
  | .mayPaySymbolsThen _ _ id
  | .mayBecomeBasePT id _ _
  | .mayTapSourceThen _ id
  | .palantirMayDraw _ id
  | .mayCastCopy id
  | .ultronMayPay id
  | .visionMode id _
  | .moonstoneMayExile id
  | .blackGatePlayer id _ => checkValidObjId pred id
  | .extrapolatePick _ ids
  | .mayPutMilledPermanent ids _
  | .castCopiesFree ids _ _
  | .sacrificeCreatureEach _ _ ids
  | .maySacrificeThese _ ids
  | .sacrificeLeastPower ids
  | .sacrificeNontokenEach _ ids
  | .orderLibraryBottom ids
  | .mayCastFromGraveyard ids
  | .mayCastCards ids _ _
  | .mayCastInstantSorceryFromHand ids
  | .mayCastUpToFromExile ids _
  | .hydeRemoveCounter ids
  | .mayPutHeroFromHandOrDraw ids
  | .visionQuestPick ids _ _
  | .newTargetsForCopies ids
  | .riddlesSplit ids
  | .worldsPutCreatures ids
  | .mayBeginOnBattlefield ids => checkValidObjIds pred ids
  | .mayThen _ sid
  | .mayPayThen _ _ sid
  | .mayDiscardThen _ sid
  | .discardThenStun _ sid
  | .maySacrificeThen _ _ sid
  | .exileFromRevealedHand _ sid
  | .mayPayPickThen _ _ sid
  | .mayPayExtort sid
  | .mayPayManaForReflexive _ _ _ sid
  | .hawkeyeModes _ _ sid
  | .mayDiscardHandBalin sid
  | .hydeMode sid
  | .oddOrEvenDestroy sid
  | .daredevilMayExile sid => checkValidOptObjId pred sid
  | .exploreMayGraveyard cid => checkValidObjId pred cid
  | .mayCreateTokens _ _ env => storedEvalEnvAnyObjId env pred
  | .discardThen _ sid cid => checkValidOptObjId pred sid || checkValidOptObjId pred cid
  | .stackTriggerUnusedMode oid sid _ _ =>
    checkValidObjId pred oid || checkValidOptObjId pred sid
  | .discardTwo _ _ _ chosen => chosen.any (fun (_, ids) => checkValidObjIds pred ids)
  | .mayMoveAllCounters fid tid
  | .crew fid tid _
  | .zemoBoastExile fid tid => checkValidObjId pred fid || checkValidObjId pred tid
  | .attachAnyEquipment hid elig => checkValidObjId pred hid || checkValidObjIds pred elig
  | .mayRevealToHand l e _
  | .nickFuryPut l e
  | .visionQuestZones l e _
  | .riddlesChoosePile _ l e
  | .revealPutCreatures l e _ => checkValidObjIds pred l || checkValidObjIds pred e
  | .nickFuryMayTransform id os
  | .mayCastCascade id os
  | .mayCastGrima id os _ => checkValidObjId pred id || checkValidObjIds pred os
  | .searchLibrary elig _ dest _ _
  | .maySearchLibrary elig _ dest _ _ =>
    checkValidObjIds pred elig || searchDestAnyObjId dest pred
  | .sacrificeDamager ids _ _ chosen =>
    checkValidObjIds pred ids || chosen.any (fun (_, id) => checkValidObjId pred id)
  | .sheHulkMayDamage _ tgt sid => targetAnyObjId pred tgt || checkValidOptObjId pred sid
  | .widowMayCounter sid ex => checkValidOptObjId pred sid || checkValidOptObjId pred ex
  | .tricksterLibrary _ cid conn sid =>
    checkValidObjId pred cid || checkValidOptObjId pred conn || checkValidOptObjId pred sid
  | .mayChangeSpellTarget sid _ stg =>
    checkValidObjId pred sid || stg.any (targetAnyObjId pred)
  | .newTargetsForCopySlot copies _ stg =>
    checkValidObjIds pred copies || stg.any (targetAnyObjId pred)
  | .chooseCards ids _ purpose =>
    checkValidObjIds pred ids ||
      match purpose with
      | .amassArmy _ _ att => checkValidOptObjId pred att
      | _ => false
  | .chooseEnteringAttackTarget rem chosen c =>
    rem.any (enteringAttackItemAnyObjId · pred) ||
      chosen.any (fun (it, atgt) =>
        enteringAttackItemAnyObjId it pred || atgt.any (attackTargetAnyObjId pred)) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .chooseTokenCopyObject ids _ _ _ _ atgt _ c sid =>
    checkValidObjIds pred ids ||
      atgt.any (attackTargetAnyObjId pred) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      checkValidOptObjId pred sid
  | _ => false

private def pendingAnyObjId (p : Pending) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  match p with
  | .sacrificePermanent _ sid
  | .maySacrificeAnotherBolg _ sid => checkValidObjId pred sid
  | .payWard _ sid _ chosen =>
    checkValidObjId pred sid || checkValidObjIds pred chosen
  | .chooseSacrificeCreature _ ids _
  | .chooseLegend _ _ ids
  | .mayCastFromLooked _ ids _ => checkValidObjIds pred ids
  | .chooseLibraryPlacement _ (some id)
  | .payOrLetCounter _ _ (some id)
  | .mayPutArtifactFromHand _ (some id) => checkValidObjId pred id
  | .mayAttachEquipment _ hid sid => checkValidObjId pred hid || checkValidOptObjId pred sid
  | .mayHaveVillainConnive _ sid vid => checkValidObjId pred sid || checkValidObjId pred vid
  | .mayCastExiledElseDamage _ cid _ sid =>
    checkValidObjId pred cid || checkValidOptObjId pred sid
  | .chooseReplacement _ rids => rids.any (repIdAnyObjId pred · prospectivePred)
  | .resolutionChoice _ fc => resolutionChoiceAnyObjId fc pred prospectivePred etbCostProspective?
  | .resolveRandom (.orderInto ids _ c) =>
    checkValidObjIds pred ids || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .resolveRandom (.chooseObject ids) => checkValidObjIds pred ids
  | _ => false

private def postStepAnyObjId (st : PostStep) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  match st with
  | .putArtifactOntoBattlefield _ cid hid =>
    checkValidObjId pred cid || checkValidOptObjId pred hid
  | .enteredBattlefieldSilent id _
  | .returnedBattlefieldEndStep id _
  | .returnedToBattlefield id _
  | .putOntoBattlefieldHasteAtFour _ id _ _
  | .addPlusOnesToSource id _
  | .logPutsIntoHand _ id _
  | .logInfluenceThenScryTwo id _
  | .millSourceInfluenceCount _ id
  | .resumeTriggerModesAfterLeave _ id _ _
  | .resumeUpToTriggerModesAfterLeave _ id _ _
  | .resumeHawkeyeModesAfterLeave _ id _ _
  | .logExiledIfInExile id _
  | .logReturnedToHand id _ _
  | .finishMoveToOwnerGraveyardLog id _ _ _ _ _
  | .logPutOnOwnerLibrary id _ _ _ _
  | .logDiscardIfInGraveyard id _ _
  | .logIfCountersIncreased id _ _ => checkValidObjId pred id
  | .logExpiredPlayFromExile ids _ => checkValidObjIds pred ids
  | .drawOneThenPlusOnesForDiscards _ sid
  | .addPlusOnesForLoggedDiscards _ sid
  | .queueTapAndStunReflexive _ _ sid
  | .incrementPlanSource _ sid => checkValidOptObjId pred sid
  | .conniveTricksterTarget _ s1 s2 => checkValidOptObjId pred s1 || checkValidOptObjId pred s2
  | .continueDiscardTwo _ _ _ chosen => chosen.any (fun (_, ids) => checkValidObjIds pred ids)
  | .enteredBattlefieldPutRestBottomRandom _ cid rest c
  | .nickFuryMayTransformOrBottom _ cid rest c =>
    checkValidObjId pred cid || checkValidObjIds pred rest ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishSurveilHandMove _ fid _ rem c _ =>
    checkValidObjId pred fid || checkValidObjIds pred rem ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .hawkeyeArrows _ _ tgts _ sid =>
    tgts.any (targetAnyObjId pred) || checkValidOptObjId pred sid
  | .dealDamageToEachOpponent _ _ sid c _
  | .dealDamageToEachNonSubtypeAndOpponents _ _ _ sid c =>
    checkValidOptObjId pred sid || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .revealPutCreaturesStep _ r p e c _ =>
    checkValidObjIds pred r || checkValidObjIds pred p ||
      checkValidObjIds pred e || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .gainLifePlayer _ _ c
  | .drawCardsPlayer _ _ c
  | .millOpponentsOnly _ _ c _
  | .opponentsDrawOneLoop _ _ c
  | .applyAggregatedLifelink _ c =>
    c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .discardCleanupIds _ rem jd _ =>
    checkValidObjIds pred rem || jd.any (fun (id, _) => checkValidObjId pred id)
  | .loseLifeForMilledManaValue _ ids c
  | .discardHandIdsLoop _ ids _ c _
  | .putRestOnBottomRandom _ ids c
  | .returnToHandLoop ids c _
  | .exileCardsLoop ids c _ =>
    checkValidObjIds pred ids || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .discardMultiHandIdsLoop rem _ c _ =>
    rem.any (fun (_, id) => checkValidObjId pred id) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .continueOpeningBegin ids
  | .offerMayCastUpToFromExile _ ids _ => checkValidObjIds pred ids
  | .exileFromRevealedHandAfterMove _ _ eid _ sid
  | .topOrBottomDamageFollowup eid _ _ _ _ sid =>
    checkValidObjId pred eid || checkValidOptObjId pred sid
  | .resumeProposalCostAfterLeave _ savedP =>
    pendingAnyObjId savedP pred prospectivePred etbCostProspective?
  | .runAfterRandom ar => afterRandomAnyObjId ar pred
  | .grantLifelinkUntilEot id c
  | .grantAdventureExilePermission _ id c
  | .grantPlayUntilEndOfNextTurn _ id c =>
    checkValidObjId pred id || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishExileUntilNextEndStep _ id c =>
    checkValidObjId pred id || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .damageUpToOneAndPlayerLoop _ _ rem _ _ sid c _ =>
    rem.any (fun (_, t) => targetAnyObjId pred t) ||
      checkValidOptObjId pred sid || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .exileZemoBoastCards _ aid rem _ =>
    checkValidObjId pred aid || checkValidObjIds pred rem
  | .exileSearchedLinkedLoop _ rem sid c pf _ =>
    checkValidObjIds pred rem || checkValidOptObjId pred sid ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) || checkValidOptObjId pred pf
  | .exileUntilInstantOrSorceryLoop _ _ _ c rem pf _ =>
    checkValidObjIds pred rem || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      checkValidOptObjId pred pf
  | .finishExileUntilSourceLeaves sid fid
  | .finishExileForLeaveTrigger sid fid
  | .recordCostSacrificedPower sid fid _ =>
    checkValidOptObjId pred sid || checkValidObjId pred fid
  | .exileTopForPlayLoop _ _ _ _ c pf _
  | .exileTopPlayIfYouControlSubtypeLoop _ _ _ c pf _ =>
    c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) || checkValidOptObjId pred pf
  | .exileTopMayCastUpToLoop _ _ _ _ c ex pf _ =>
    c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) || checkValidObjIds pred ex ||
      checkValidOptObjId pred pf
  | .resolveCascadeLoop _ _ c ex pf _ =>
    eventCauseAnyObjId c pred prospectivePred etbCostProspective? || checkValidObjIds pred ex ||
      checkValidOptObjId pred pf
  | .finishGrimaDirectCast _ _ fid os c =>
    checkValidObjId pred fid || checkValidObjIds pred os ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishPaySneak _ sid aid atk c =>
    checkValidObjId pred sid || checkValidObjId pred aid ||
      attackTargetAnyObjId pred atk || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishZemoBoastExileLogs _ sid pids =>
    checkValidObjId pred sid || checkValidObjIds pred pids
  | .moveIdsInOrderLoop ids _ _ c _ pm _ =>
    checkValidObjIds pred ids || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pm.any (fun (id, _) => checkValidObjId pred id)
  | .dealDamageLoseIndestructibleExileTo tid _ src =>
    checkValidObjId pred tid || eventObjAnyObjId pred src
  | .movePublicCardsToHandLoop _ rem _ _ c pc _ _ =>
    checkValidObjIds pred rem || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pc.any (fun (id, _) => checkValidObjId pred id)
  | .exileOpponentLibrariesLoop _ _ cids _ pid _ =>
    checkValidObjIds pred cids || checkValidOptObjId pred pid
  | .chooseCardsToHandLoop _ rem c pc _ =>
    checkValidObjIds pred rem || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pc.any (fun (id, _, _) => checkValidObjId pred id)
  | .returnOwnedCreaturesLoop _ rem c sid _ pc _ =>
    checkValidObjIds pred rem || eventCauseAnyObjId c pred prospectivePred etbCostProspective? ||
      checkValidOptObjId pred sid || pc.any (fun (id, _, _) => checkValidObjId pred id)
  | .placeSearchedHandLoop _ rem c pc _ =>
    checkValidObjIds pred rem || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pc.any (fun (id, _) => checkValidObjId pred id)
  | .applyRiddlesToHandLoop _ rem toGy _ =>
    checkValidObjIds pred rem || checkValidObjIds pred toGy
  | .finishInspectLibraryRest _ _ rest c =>
    checkValidObjIds pred rest || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .fightCreatures sid tid c =>
    checkValidObjId pred sid || checkValidObjId pred tid ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishAbilityResolution snap _ sid _ _ _ =>
    eventObjAnyObjId pred snap || checkValidOptObjId pred sid
  | _ => false

mutual

private partial def pendingReplacementAnyObjId (pr : PendingReplacement)
    (pred : ObjectId → Bool) (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  match pr with
  | .seq a b =>
    pendingReplacementAnyObjId a pred prospectivePred etbCostProspective? ||
      pendingReplacementAnyObjId b pred prospectivePred etbCostProspective?
  | .dealDamageToPlayer _ _ src _ c _
  | .dealDamageToPlayers _ _ src c _ _ =>
    src.any (eventObjAnyObjId pred) || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .dealDamageFrom _ src tid _ _ c _ _ =>
    src.any (eventObjAnyObjId pred) || checkValidObjId pred tid ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .dealFightDamage sid tid c _ _ _ =>
    checkValidObjId pred sid || checkValidObjId pred tid ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .dealDamageToPermanent tid _ src c _ _
  | .markDamageOn tid _ _ _ src _ _ c _ _ _ =>
    checkValidObjId pred tid || src.any (eventObjAnyObjId pred) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .gainLife _ _ c
  | .createTreasureTokens _ _ _ c
  | .draw _ _ c
  | .copyNontokenCreatures _ _ c
  | .copyPermanentTokens _ _ _ c _ _
  | .setLife _ _ _ c
  | .loseLifeAfterDraw _ _ c => c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .addPlusOnePlusOneTo tid _ _ _ c
  | .addCounters tid _ _ _ _ c
  | .recordPutCounters tid _ _ _ c
  | .putCountersDeferredLog tid _ _ _ _ c
  | .untapPermanent tid _ _ c _
  | .addLoreCounters tid _ c
  | .finishPlaceSearched _ tid _ _ c
  | .addFinalityTo tid _ _ _ c
  | .counterStackSpell tid _ _ _ c _ _ =>
    checkValidObjId pred tid || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .destroyPermanent tid c pb _ _ =>
    checkValidObjId pred tid || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pb.any (·.any (gameObjAnyObjId pred))
  | .logPutCounterDelta tid _ _ _
  | .finishManaAbilityMountainTrigger _ tid
  | .finishPutLandFromHand tid
  | .putShadowCounter tid
  | .finishShadowCounter tid _
  | .returnStackSpell tid _ _ _
  | .finishTurnFaceUp _ tid _
  | .finishBecomeCast _ tid _ _ _ => checkValidObjId pred tid
  | .move id _ _ _ _ _ _ _ atgt _ _ _ _ _ _ _ pb _ _ _ _ att _ c _ skip _ =>
    checkValidObjId pred id || atgt.any (attackTargetAnyObjId pred) ||
      pb.any (·.any (gameObjAnyObjId pred)) || checkValidOptObjId pred att ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) || checkValidObjIds pred skip
  | .moveSimultaneousToGraveyard ids pb c _ _ =>
    checkValidObjIds pred ids || pb.any (·.any (gameObjAnyObjId pred)) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .createToken _ _ _ _ atgt _ _ _ c _ =>
    atgt.any (attackTargetAnyObjId pred) || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .createKindTokens _ _ _ _ _ atgt _ c copyEnv =>
    storedEvalEnvAnyObjId copyEnv pred ||
      atgt.any (attackTargetAnyObjId pred) || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .createTokenBatches batches _ atgt _ _ c =>
    batches.any (fun b =>
      b.attackingTarget.any (attackTargetAnyObjId pred) ||
        b.cause.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)) ||
      atgt.any (attackTargetAnyObjId pred) || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .createAndMarkTokensAttacking _ _ _ _ _ sid c copyEnv =>
    checkValidOptObjId pred sid ||
      storedEvalEnvAnyObjId copyEnv pred ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .commitEnteringAttackItems chosen c _ pe pb _ =>
    chosen.any (fun (it, atgt) =>
      enteringAttackItemAnyObjId it pred || atgt.any (attackTargetAnyObjId pred)) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pe.any (fun (id, _, _, _, _) => checkValidObjId pred id) ||
      pb.any (·.any (gameObjAnyObjId pred))
  | .finishEnteringAttackCards pe c _ =>
    pe.any (fun (id, _, _, _, _) => checkValidObjId pred id) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishEnteringAttackCard nid _ _ _ _ c =>
    checkValidOptObjId pred nid || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .afterLastPermanentEnters fid _ hid =>
    checkValidOptObjId pred fid || checkValidOptObjId pred hid
  | .shuffleThen _ ar => afterRandomAnyObjId ar pred
  | .drawOne _ app _ c
  | .drawSubDraws _ _ app c =>
    app.any (repIdAnyObjId pred · prospectivePred) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .connive _ sid => checkValidOptObjId pred sid
  | .finishSbaSweep moves pb _ pwm sm tok cop ia ie ica lg _ =>
    (moves ++ pwm ++ sm).any (fun m => checkValidObjId pred m.objectId) ||
      pb.any (gameObjAnyObjId pred) || checkValidObjIds pred tok ||
      checkValidObjIds pred cop || checkValidObjIds pred ia ||
      (ie ++ ica).any (fun (a, b) => checkValidObjId pred a || checkValidObjId pred b) ||
      lg.any (fun (_, _, ids) => checkValidObjIds pred ids)
  | .finishDealDamageLoseIndestructibleExile tid _ _ c
  | .finishProliferateEachKind _ tid _ _ c =>
    checkValidObjId pred tid || eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .untapStepPermanents ids _
  | .addLoreAfterDrawStep ids
  | .continueConnives _ ids => checkValidObjIds pred ids
  | .restorePending p _ _ _ _ => pendingAnyObjId p pred prospectivePred etbCostProspective?
  | .restorePausedBatch _ _ _ c objs pls effs pend stk _ qle =>
    c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) || objs.any (gameObjAnyObjId pred) ||
      pls.any (playerAnyObjId · pred) ||
      effs.any (fun (_, sp) => specAnyObjId sp pred prospectivePred) ||
      pendingAnyObjId pend pred prospectivePred etbCostProspective? ||
      stk.any (stackEntryAnyObjId · pred prospectivePred etbCostProspective?) ||
      checkValidObjIds pred qle
  | .finishBecomeActivated _ _ sid _ aid snap orig _ _
  | .finishPostLoyaltyActivated _ _ sid _ aid snap orig _ _ =>
    checkValidOptObjId pred sid || checkValidOptObjId pred aid ||
      snap.any (eventObjAnyObjId pred) || orig.any (gameObjAnyObjId pred)
  | .payCostPickItems _ aid sid _ rem _ =>
    checkValidOptObjId pred aid || checkValidOptObjId pred sid || checkValidObjIds pred rem
  | .finishActivationExtraCosts _ sid fo .. =>
    checkValidObjId pred sid || checkValidOptObjId pred fo
  | .finishActivateManaAbilityPicks _ id _ _ _ rem _ _ _ _ _ _ prevP _ _ _ _ _ _ exileSymIds _ _ _ crewIds _ _ _ =>
    checkValidObjId pred id || checkValidObjIds pred rem || checkValidObjIds pred exileSymIds ||
      checkValidObjIds pred crewIds ||
      pendingAnyObjId prevP pred prospectivePred etbCostProspective?
  | .finishActivateManaAbilityPostSac _ id _ snap _ _ _ _ _ _ prevP _ _ _ _ =>
    checkValidObjId pred id || eventObjAnyObjId pred snap ||
      pendingAnyObjId prevP pred prospectivePred etbCostProspective?
  | .runModalManaEffect _ sid _ =>
    checkValidObjId pred sid
  | .finishConniveDraws _ ed c _ =>
    ed.any (fun (_, r) => repIdAnyObjId pred r prospectivePred) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .amass _ _ _ att c
  | .finishFreshAmass _ _ _ att c _ =>
    checkValidOptObjId pred att || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishAmassOn _ aid _ _ att _ c =>
    checkValidObjId pred aid || checkValidOptObjId pred att ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .placeSearchedBatch _ rem _ c ent pb _ =>
    checkValidObjIds pred rem || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      ent.any (fun (id, _) => checkValidObjId pred id) ||
      pb.any (·.any (gameObjAnyObjId pred))
  | .finishSearchAfterPlace _ fid dest _ _ hr c =>
    checkValidOptObjId pred fid || searchDestAnyObjId dest pred ||
      checkValidObjIds pred hr || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishSurveilPostMove _ card fid rem c _ =>
    gameObjAnyObjId pred card || checkValidObjId pred fid ||
      checkValidObjIds pred rem || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .untapPermanentsLoop ids c _ sid _ =>
    checkValidObjIds pred ids || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      checkValidOptObjId pred sid
  | .surveilMoveLoop _ ids c _
  | .requestOrderInto ids _ _ c
  | .millCardsLoop _ ids _ c _ _ _ _
  | .moveCardsToGraveyardLoop ids c _
  | .phaseInControlledLoop ids c _ _ _ =>
    checkValidObjIds pred ids || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishProliferateTarget _ tid _ _ rtgts pids _ _ _ c =>
    checkValidObjId pred tid || rtgts.any (targetAnyObjId pred) ||
      checkValidObjIds pred pids || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishChooseDiscardCard _ card _ => gameObjAnyObjId pred card
  | .finishBeginOnBattlefield fid rem =>
    checkValidObjId pred fid || checkValidObjIds pred rem
  | .continueSpellModes _ _ tgts _ _ _ _ sid _ _ _ =>
    tgts.any (targetAnyObjId pred) || checkValidOptObjId pred sid
  | .continueInterpreter st =>
    interpStateAnyObjId st pred prospectivePred etbCostProspective?
  | .empowerJace _ _ _ tid c =>
    checkValidOptObjId pred tid || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .dealDamageToEachCreatureMatching rem _ _ _ _ src c _ _ =>
    checkValidObjIds pred rem || src.any (eventObjAnyObjId pred) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .destroyPermanentsLoop r a _ _ _ pb c _ =>
    checkValidObjIds pred r || checkValidObjIds pred a ||
      pb.any (·.any (gameObjAnyObjId pred)) || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .sacrificePermanentsLoop rem pb c _ _ _ =>
    rem.any (fun (_, id) => checkValidObjId pred id) ||
      pb.any (·.any (gameObjAnyObjId pred)) || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .putToBattlefieldLoop _ r e _ _ _ _ _ _ c pb _ =>
    checkValidObjIds pred r || checkValidObjIds pred e ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) || pb.any (·.any (gameObjAnyObjId pred))
  | .returnLinkedExileLoop r c e pb pl _ =>
    checkValidObjIds pred r || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      checkValidObjIds pred e || pb.any (·.any (gameObjAnyObjId pred)) ||
      pl.any (fun (id, _) => checkValidObjId pred id)
  | .finishLinkedExileMove r pb pl e _ =>
    checkValidObjIds pred r || pb.any (·.any (gameObjAnyObjId pred)) ||
      pl.any (fun (id, _) => checkValidObjId pred id) || checkValidObjIds pred e
  | .exilePermanentsLoop r _ c lc _ =>
    checkValidObjIds pred r || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      lc.any (fun (id, _) => checkValidObjId pred id)
  | .flickerLoop r ex ent _ _ _ _ _ c pb _ _ =>
    checkValidObjIds pred r || checkValidObjIds pred ex || checkValidObjIds pred ent ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) || pb.any (·.any (gameObjAnyObjId pred))
  | .finishMillChooseForHand _ p _ m _ _ _ _ c =>
    checkValidObjIds pred p || checkValidObjIds pred m ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .finishPostStep st => postStepAnyObjId st pred prospectivePred etbCostProspective?
  | .leavePlayersWhoLost sp _ _ _ _
  | .finishConcede _ _ _ sp _ _ _ _
  | .concedePlayersLoop _ _ _ _ _ _ sp _ _ _ _ =>
    sp.any (pendingAnyObjId · pred prospectivePred etbCostProspective?)
  | .endControlExileLoop rem c pl extra _ _ =>
    rem.any (fun (id, _, _) => checkValidObjId pred id) ||
      c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pl.any (fun (id, _) => checkValidObjId pred id) ||
      checkValidObjIds pred extra
  | .placeSearchedGraveyardLoop ids c pl _ =>
    checkValidObjIds pred ids || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      pl.any (fun (id, _, _) => checkValidObjId pred id)
  | .runPostCastCleanup pc => postCastCleanupAnyObjId pc pred
  | .continueCheckpointReplay rem full rev lm _ _ _ _ =>
    (rem ++ full).any (fun (_, ev) =>
      gameChangeAnyObjId ev.change pred prospectivePred etbCostProspective? ||
        ev.cause?.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)) ||
      (rev ++ lm).any (fun (a, b) => checkValidObjId pred a || checkValidObjId pred b)
  | .phaseOutPermanentsLoop rem c ps _ _ =>
    checkValidObjIds pred rem || c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      ps.any (fun (id, eo) => checkValidObjId pred id || eventObjAnyObjId pred eo)
  | _ => false

private partial def continuationChangeAnyObjId (cc : ContinuationChange)
    (pred : ObjectId → Bool) (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  match cc with
  | .recentTokenIds v => checkValidObjIds pred v
  | .pendingFreeCopies v => v.any (fun (_, ids, _, _) => checkValidObjIds pred ids)
  | .pendingMayCastFromExile v => v.any (fun (_, ids, _) => checkValidObjIds pred ids)
  | .postCastCleanup v => v.any (postCastCleanupAnyObjId · pred)
  | .conniveSource v
  | .resolvingSpell v
  | .resolvingAbility v => checkValidOptObjId pred v
  | .pendingReplacement v =>
    v.any (pendingReplacementAnyObjId · pred prospectivePred etbCostProspective?)
  | .pushOuterPendingReplacement v =>
    pendingReplacementAnyObjId v pred prospectivePred etbCostProspective?
  | .stagedAttackTokenBatches v =>
    v.any (fun b =>
      b.attackingTarget.any (attackTargetAnyObjId pred) ||
        b.cause.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?))
  | .stashedCause v => v.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)
  | .afterRandom v => afterRandomAnyObjId v pred
  | .resolutionFinish v =>
    v.any fun
      | .ability oid snap _ sid _ =>
        checkValidObjId pred oid || eventObjAnyObjId pred snap || checkValidOptObjId pred sid
      | .spell se snap _ =>
        stackEntryAnyObjId se pred prospectivePred etbCostProspective? || eventObjAnyObjId pred snap
  | .pendingResolvedEvent v =>
    v.any (fun (eo, _, c) =>
      eventObjAnyObjId pred eo || eventCauseAnyObjId c pred prospectivePred etbCostProspective?)
  | .stepEnv v => v.any (fun (_, o) => stepOutcomeAnyObjId o pred)
  | .bindStepOutcome _ o => stepOutcomeAnyObjId o pred
  | .interpWait? v => v.any (interpStateAnyObjId · pred prospectivePred etbCostProspective?)
  | _ => false

private partial def continuationFrameAnyObjId (f : ContinuationFrame)
    (pred : ObjectId → Bool) (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  checkValidObjIds pred f.recentTokenIds ||
    f.pendingFreeCopies.any (fun (_, ids, _, _) => checkValidObjIds pred ids) ||
    f.pendingMayCastFromExile.any (fun (_, ids, _) => checkValidObjIds pred ids) ||
    f.postCastCleanup.any (postCastCleanupAnyObjId · pred) ||
    f.pendingReplacement.any (pendingReplacementAnyObjId · pred prospectivePred etbCostProspective?) ||
    f.outerPendingReplacements.any (pendingReplacementAnyObjId · pred prospectivePred etbCostProspective?) ||
    checkValidOptObjId pred f.conniveSource ||
    f.stagedAttackTokenBatches.any (fun b =>
      b.attackingTarget.any (attackTargetAnyObjId pred) ||
        b.cause.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?)) ||
    f.resolvingContext.any (fun (sid, _) => checkValidOptObjId pred sid) ||
    f.stashedCause.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
    checkValidOptObjId pred f.resolvingSpell ||
    checkValidOptObjId pred f.resolvingAbility ||
    afterRandomAnyObjId f.afterRandom pred ||
    f.resolutionFinish.any (fun
      | .ability oid snap _ sid _ =>
        checkValidObjId pred oid || eventObjAnyObjId pred snap || checkValidOptObjId pred sid
      | .spell se snap _ =>
        stackEntryAnyObjId se pred prospectivePred etbCostProspective? || eventObjAnyObjId pred snap) ||
    f.pendingResolvedEvent.any (fun (eo, _, c) =>
      eventObjAnyObjId pred eo || eventCauseAnyObjId c pred prospectivePred etbCostProspective?) ||
    f.stepEnv.any (fun (_, o) => stepOutcomeAnyObjId o pred) ||
    f.interpWait?.any (interpStateAnyObjId · pred prospectivePred etbCostProspective?)

private partial def gameChangeAnyObjId (ch : GameChange) (pred : ObjectId → Bool)
    (prospectivePred : ObjectId → Bool := pred)
    (etbCostProspective? : CostKind → ObjectId → Bool := fun _ _ => false) : Bool :=
  let proposalChangeRefs : ProposalChange → Bool
    | .tapped ids | .teamworkCreatures ids => checkValidObjIds pred ids
    | .pushTapped id => checkValidObjId pred id
    | _ => false
  match ch with
  | .engine (.addPlayer pl) => playerAnyObjId pl pred
  | .engine (.materializeObject obj _) => gameObjAnyObjId pred obj
  | .engine (.object id oc) =>
    checkValidObjId pred id ||
      match oc with
      | .linkedExile ids | .leaveTriggerExile ids => checkValidObjIds pred ids
      | .pushLinkedExile tid | .pushLeaveTriggerExile tid => checkValidObjId pred tid
      | .exiledBy tid => checkValidOptObjId pred tid
      | _ => false
  | .engine (.removeStackEntry id)
  | .engine (.stackEntry id _) => checkValidObjId pred id
  | .engine (.pushStack e) => stackEntryAnyObjId e pred prospectivePred etbCostProspective?
  | .engine (.proposedSpell (some prop)) =>
    checkValidObjId pred prop.spellId ||
      checkValidOptObjId pred prop.sourceId ||
      gameObjAnyObjId pred prop.original ||
      eventObjAnyObjId pred prop.originalSnapshot ||
      checkValidObjIds pred prop.tapped ||
      checkValidObjIds pred prop.teamworkCreatures ||
      checkValidOptObjId pred prop.sneakAttacker ||
      prop.origPerm.any (fun p => checkValidOptObjId pred p.prepareSource)
  | .engine (.proposal pc) => proposalChangeRefs pc
  | .engine (.proposalChanges pcs) => pcs.any proposalChangeRefs
  | .engine (.beginProposalAction (.manaAbility sid)) => checkValidOptObjId pred sid
  | .engine (.pauseBatch _ c objs pls effs pend stk) =>
    c.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
      objs.any (gameObjAnyObjId pred) ||
      pls.any (playerAnyObjId · pred) ||
      effs.any (fun (_, sp) => specAnyObjId sp pred prospectivePred) ||
      pendingAnyObjId pend pred prospectivePred etbCostProspective? ||
      stk.any (stackEntryAnyObjId · pred prospectivePred etbCostProspective?)
  | .engine (.setPausedBatchCause (some c)) =>
    eventCauseAnyObjId c pred prospectivePred etbCostProspective?
  | .engine (.pushContinuationFrame f) =>
    continuationFrameAnyObjId f pred prospectivePred etbCostProspective?
  | .engine (.continuation cc) =>
    continuationChangeAnyObjId cc pred prospectivePred etbCostProspective?
  | .engine (.waitingTriggers wts)
  | .engine (.enqueueWaitingTriggers wts) =>
    wts.any fun wt =>
      gameObjAnyObjId pred wt.source ||
        checkValidOptObjId pred wt.causeId ||
        checkValidObjIds pred wt.causeIds ||
        wt.cause.any (gameObjAnyObjId pred) ||
        wt.eventCause.any (eventCauseAnyObjId · pred prospectivePred etbCostProspective?) ||
        wt.delayedTrigger.any (fun (k, c) =>
          delayedKindAnyObjId pred k ||
            eventCauseAnyObjId c pred prospectivePred etbCostProspective?)
  | .engine (.queueLinkedExile ids) => checkValidObjIds pred ids
  | .engine (.replacementOrder rids) => rids.any (repIdAnyObjId pred · prospectivePred)
  | .engine (.pendingBlockerAssignments asgns) =>
    asgns.any (fun a =>
      checkValidObjId pred a.source || a.toCreatures.any (fun (cid, _) => checkValidObjId pred cid))
  | .engine (.pending p) => pendingAnyObjId p pred prospectivePred etbCostProspective?
  | .rules (.zone (.created eo _))
  | .rules (.zone (.ceasedToExist eo))
  | .rules (.permanent (.tapped eo _))
  | .rules (.permanent (.untapped eo))
  | .rules (.permanent (.phasedOut eo _))
  | .rules (.permanent (.phasedIn eo _))
  | .rules (.permanent (.transformed eo _))
  | .rules (.permanent (.turnedFaceUp eo))
  | .rules (.permanent (.turnedFaceDown eo))
  | .rules (.permanent (.counters (.object eo) ..))
  | .rules (.permanent (.designation eo _ _)) => eventObjAnyObjId pred eo
  | .rules (.permanent (.attached eo host prev)) =>
    eventObjAnyObjId pred eo || checkValidObjId pred host || checkValidOptObjId pred prev
  | .rules (.permanent (.unattached eo fromHost)) =>
    eventObjAnyObjId pred eo || checkValidObjId pred fromHost
  | .rules (.zone (.moved before after ..)) =>
    eventObjAnyObjId pred before || eventObjAnyObjId pred after
  | .rules (.damage (.dealt pkts)) =>
    pkts.any fun pkt =>
      eventObjAnyObjId pred pkt.source ||
        match pkt.recipient with
        | .permanent eo | .battle eo => eventObjAnyObjId pred eo
        | .player _ => false
  | .rules (.damage (.marked id _)) => checkValidObjId pred id
  | .rules (.damage (.markedCleared ids)) => checkValidObjIds pred ids
  | .rules (.damage (.prevented src rec _)) =>
    eventObjAnyObjId pred src ||
      match rec with
      | .permanent eo | .battle eo => eventObjAnyObjId pred eo
      | .player _ => false
  | .rules (.combat (.attackersDeclared _ decls)) =>
    decls.any (fun (eo, tgt) => eventObjAnyObjId pred eo || attackTargetAnyObjId pred tgt)
  | .rules (.combat (.becameAttacking eo tgt)) =>
    eventObjAnyObjId pred eo || attackTargetAnyObjId pred tgt
  | .rules (.combat (.blockersDeclared _ decls)) =>
    decls.any (fun (eo, aid) => eventObjAnyObjId pred eo || checkValidObjId pred aid)
  | .rules (.combat (.becameBlocked eo blks)) =>
    eventObjAnyObjId pred eo || checkValidObjIds pred blks
  | .rules (.combat (.remainedUnblocked eo))
  | .rules (.combat (.removedFromCombat eo)) => eventObjAnyObjId pred eo
  | .rules (.combat (.damageAssigned _ _ asgns)) =>
    asgns.any (fun a =>
      checkValidObjId pred a.source || a.toCreatures.any (fun (cid, _) => checkValidObjId pred cid))
  | .rules (.cast (.proposed obj ..)) => checkValidObjId pred obj
  | .rules (.cast (.announced obj _ _ costs)) =>
    checkValidObjId pred obj || costs.any fun
      | .teamwork ids => checkValidObjIds pred ids
      | .behold id | .sacrifice id | .discard id => checkValidObjId pred id
      | .sneak id atk => checkValidObjId pred id || atk.any (attackTargetAnyObjId pred)
      | _ => false
  | .rules (.cast (.targeted obj tgts ..)) =>
    checkValidObjId pred obj || tgts.any (targetAnyObjId pred)
  | .rules (.cast (.spellCast spell ..)) => eventObjAnyObjId pred spell
  | .rules (.cast (.abilityActivated ab src ..)) =>
    checkValidObjId pred ab || eventObjAnyObjId pred src
  | .rules (.triggerQueue (.triggered src _ _ _)) => eventObjAnyObjId pred src
  | .rules (.triggerQueue (.putOnStack stObj src _ spec)) =>
    checkValidObjId pred stObj ||
      eventObjAnyObjId pred src ||
      checkValidOptObjId pred spec.sourceId ||
      checkValidOptObjId pred spec.triggerCauseId ||
      checkValidObjIds pred spec.triggerCauseIds ||
      spec.triggerCauseStatus.any (statusAnyObjId pred) ||
      spec.delayedTrigger.any (fun (k, c) =>
        delayedKindAnyObjId pred k || eventCauseAnyObjId c pred prospectivePred etbCostProspective?)
  | .rules (.triggerQueue (.modeChosen src ..)) => checkValidObjId pred src
  | .rules (.stackObject (.copied orig copy _)) =>
    checkValidObjId pred orig || eventObjAnyObjId pred copy
  | .rules (.stackObject (.resolved eo _ srcId _)) =>
    eventObjAnyObjId pred eo || checkValidOptObjId pred srcId
  | .rules (.stackObject (.removedOnResolution eo)) => eventObjAnyObjId pred eo
  | .rules (.player (.manaAdded _ units))
  | .rules (.player (.manaEmptied _ units _)) =>
    units.any (fun u => checkValidOptObjId pred u.source)
  | .rules (.player (.manaSpent _ units forObj)) =>
    checkValidOptObjId pred forObj || units.any (fun u => checkValidOptObjId pred u.source)
  | .rules (.player (.scried _ top bot ..)) =>
    checkValidObjIds pred top || checkValidObjIds pred bot
  | .rules (.player (.surveilled _ top gy ..)) =>
    checkValidObjIds pred top || checkValidObjIds pred gy
  | .rules (.player (.lookedAt _ cs))
  | .rules (.player (.revealed _ cs))
  | .rules (.player (.searched _ _ cs))
  | .rules (.player (.shuffled _ cs))
  | .rules (.player (.proliferated _ cs _)) => checkValidObjIds pred cs
  | .rules (.player (.ringTempted _ b _)) => checkValidOptObjId pred b
  | .rules (.player (.optionalOnceActed _ s)) => checkValidObjId pred s
  | .rules (.continuousEffect (.created _ spec))
  | .rules (.continuousEffect (.expired _ (some spec))) =>
    specAnyObjId spec pred prospectivePred
  | .rules (.delayedTrigger (.created dt))
  | .rules (.delayedTrigger (.consumed dt))
  | .rules (.delayedTrigger (.expired dt)) =>
    delayedTriggerAnyObjId dt pred prospectivePred etbCostProspective?
  | _ => false

end

private def gameChangeReferencesObject (ch : GameChange) (oid : ObjectId) : Bool :=
  gameChangeAnyObjId ch (· == oid)

mutual

private partial def pendingReplacementMaxTs (pr : PendingReplacement) : Nat :=
  let objTs (o : GameObject) : Nat :=
    if o.id != noSourceSentinelId then o.timestamp else 0
  let objsTs (os : Array GameObject) : Nat :=
    os.foldl (fun acc o => max acc (objTs o)) 0
  let optObjsTs (pb : Option (Array GameObject)) : Nat :=
    pb.map objsTs |>.getD 0
  match pr with
  | .seq a b => max (pendingReplacementMaxTs a) (pendingReplacementMaxTs b)
  | .move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pb ..
  | .moveSimultaneousToGraveyard _ pb ..
  | .destroyPermanent _ _ pb _ _
  | .commitEnteringAttackItems _ _ _ _ pb ..
  | .placeSearchedBatch _ _ _ _ _ pb ..
  | .destroyPermanentsLoop _ _ _ _ _ pb ..
  | .sacrificePermanentsLoop _ pb ..
  | .putToBattlefieldLoop _ _ _ _ _ _ _ _ _ _ pb ..
  | .returnLinkedExileLoop _ _ _ pb ..
  | .finishLinkedExileMove _ pb ..
  | .flickerLoop _ _ _ _ _ _ _ _ _ pb .. => optObjsTs pb
  | .finishSbaSweep _ pb .. => objsTs pb
  | .restorePausedBatch _ _ _ _ objs .. => objsTs objs
  | .finishBecomeActivated _ _ _ _ _ _ orig ..
  | .finishPostLoyaltyActivated _ _ _ _ _ _ orig .. => orig.map objTs |>.getD 0
  | .finishSurveilPostMove _ card ..
  | .finishChooseDiscardCard _ card _ => objTs card
  | .continueCheckpointReplay rem full .. =>
    (rem ++ full).foldl (fun acc (_, ev) => max acc (gameChangeMaxTs ev.change)) 0
  | _ => 0

private partial def gameChangeMaxTs (ch : GameChange) : Nat :=
  let objTs (o : GameObject) : Nat :=
    if o.id != noSourceSentinelId then o.timestamp else 0
  match ch with
  | .engine (.materializeObject obj _) => objTs obj
  | .engine (.pauseBatch _ _ objs ..) =>
    objs.foldl (fun acc o => max acc (objTs o)) 0
  | .engine (.waitingTriggers wts)
  | .engine (.enqueueWaitingTriggers wts) =>
    wts.foldl (fun acc wt =>
      max acc (max (objTs wt.source) (wt.cause.map objTs |>.getD 0))) 0
  | .engine (.proposedSpell (some prop)) => objTs prop.original
  | .engine (.pushContinuationFrame f) =>
    let prTs := f.pendingReplacement.map pendingReplacementMaxTs |>.getD 0
    let outerTs :=
      f.outerPendingReplacements.foldl (fun acc pr => max acc (pendingReplacementMaxTs pr)) 0
    max prTs outerTs
  | .engine (.continuation (.pendingReplacement (some pr)))
  | .engine (.continuation (.pushOuterPendingReplacement pr)) => pendingReplacementMaxTs pr
  | .rules (.delayedTrigger (.created dt))
  | .rules (.delayedTrigger (.consumed dt))
  | .rules (.delayedTrigger (.expired dt)) => dt.source.map objTs |>.getD 0
  | _ => 0

end

private def newlyCreatedIdsOfChange (ch : GameChange) : Array ObjectId :=
  match ch with
  | .engine (.materializeObject obj _) =>
    if obj.id != noSourceSentinelId then #[obj.id] else #[]
  | .engine (.pending (.chooseReplacement _ rids))
  | .engine (.replacementOrder rids) =>
    rids.foldl (fun acc r =>
      match r.object with
      | some id =>
        if repEffKindIsProspectiveEnter r.kind && id != noSourceSentinelId && !acc.contains id then
          acc.push id
        else acc
      | none => acc) #[]
  | .rules (.zone (.created eo _)) =>
    match eo.id with
    | some id => if id != noSourceSentinelId then #[id] else #[]
    | none => #[]
  | .rules (.zone (.moved before after ..)) =>
    match after.id with
    | some aid => if before.id != some aid && aid != noSourceSentinelId then #[aid] else #[]
    | none => #[]
  | .rules (.cast (.proposed id ..)) =>
    if id != noSourceSentinelId then #[id] else #[]
  | .rules (.cast (.abilityActivated ab src _ (.nonMana ..))) =>
    if src.id != some ab && ab != noSourceSentinelId then #[ab] else #[]
  | .rules (.triggerQueue (.putOnStack stObj src ..)) =>
    if src.id != some stObj && stObj != noSourceSentinelId then #[stObj] else #[]
  | .rules (.stackObject (.copied orig copy _)) =>
    match copy.id with
    | some cid => if cid != orig && cid != noSourceSentinelId then #[cid] else #[]
    | none => #[]
  | _ => #[]

/-- Precomputed per-`Game` indices allowing `isInitialMaterializeWith` to answer
`wasMaterializedBefore`, `isUnmaterializedRepLookaheadId`, `isEtbCostProspectiveAt`,
`postBoundObjectCreatedOrTsUpdated`, and `prefixMaxTs` in $O(1)$ per query instead of
rescanning `g.events` for every materialize event and object. -/
private structure InitialMaterializeIndex where
  firstMatIdx : Std.HashMap ObjectId Nat
  unmatLookahead : Std.HashMap ObjectId Unit
  etbCostLifeFirst : Std.HashMap ObjectId Nat
  etbCostBeholdFirst : Std.HashMap ObjectId Nat
  lastCreatedIdx : Std.HashMap ObjectId Nat
  lastTsUpdatedIdx : Std.HashMap ObjectId Nat
  prefixMaxTs : Array Nat

@[noinline] private def buildInitialMaterializeIndex (g : Game) : InitialMaterializeIndex := Id.run do
  let recordFirst (m : Std.HashMap ObjectId Nat) (id : ObjectId) (idx : Nat) :
      Std.HashMap ObjectId Nat :=
    if m.contains id then m else m.insert id idx
  let recordFirstOpt (m : Std.HashMap ObjectId Nat) (id? : Option ObjectId) (idx : Nat) :
      Std.HashMap ObjectId Nat :=
    match id? with
    | some id => recordFirst m id idx
    | none => m
  let mut firstMatIdx : Std.HashMap ObjectId Nat := {}
  let mut prospectiveEnterIds : Array ObjectId := #[]
  let mut etbCostLifeFirst : Std.HashMap ObjectId Nat := {}
  let mut etbCostBeholdFirst : Std.HashMap ObjectId Nat := {}
  let mut lastCreatedIdx : Std.HashMap ObjectId Nat := {}
  let mut lastTsUpdatedIdx : Std.HashMap ObjectId Nat := {}
  let mut prefixMaxTs : Array Nat := Array.mkEmpty (g.events.size + 1)
  let mut curMaxTs : Nat := 0
  prefixMaxTs := prefixMaxTs.push 0
  for j in [0 : g.events.size] do
    let ch := g.events[j]!.change
    curMaxTs := max curMaxTs (gameChangeMaxTs ch)
    prefixMaxTs := prefixMaxTs.push curMaxTs
    match ch with
    | .engine (.materializeObject obj _) =>
      firstMatIdx := recordFirst firstMatIdx obj.id j
      lastCreatedIdx := lastCreatedIdx.insert obj.id j
      lastTsUpdatedIdx := lastTsUpdatedIdx.insert obj.id j
    | .engine (.pending (.chooseReplacement _ rids))
    | .engine (.replacementOrder rids) =>
      for r in rids do
        if let some id := r.object then
          if repEffKindIsProspectiveEnter r.kind && id != noSourceSentinelId then
            prospectiveEnterIds := prospectiveEnterIds.push id
          match r.kind with
          | .entersUntappedPayLife .. =>
            etbCostLifeFirst := recordFirst etbCostLifeFirst id j
          | .entersUntappedBehold .. =>
            etbCostBeholdFirst := recordFirst etbCostBeholdFirst id j
          | _ => pure ()
    | .rules (.zone (.created eo _)) =>
      if let some id := eo.id then
        firstMatIdx := recordFirst firstMatIdx id j
        lastCreatedIdx := lastCreatedIdx.insert id j
        lastTsUpdatedIdx := lastTsUpdatedIdx.insert id j
    | .rules (.zone (.ceasedToExist eo)) =>
      firstMatIdx := recordFirstOpt firstMatIdx eo.id j
    | .rules (.zone (.moved before after ..)) =>
      firstMatIdx := recordFirstOpt firstMatIdx before.id j
      if let some aid := after.id then
        firstMatIdx := recordFirst firstMatIdx aid j
        if before.id != some aid then
          lastCreatedIdx := lastCreatedIdx.insert aid j
        lastTsUpdatedIdx := lastTsUpdatedIdx.insert aid j
    | .rules (.permanent (.turnedFaceUp eo))
    | .rules (.permanent (.turnedFaceDown eo))
    | .rules (.permanent (.transformed eo _))
    | .rules (.permanent (.attached eo ..)) =>
      if let some id := eo.id then
        lastTsUpdatedIdx := lastTsUpdatedIdx.insert id j
    | .rules (.cast (.proposed id ..)) =>
      firstMatIdx := recordFirst firstMatIdx id j
      lastCreatedIdx := lastCreatedIdx.insert id j
      lastTsUpdatedIdx := lastTsUpdatedIdx.insert id j
    | .rules (.cast (.spellCast eo ..)) =>
      if let some id := eo.id then
        lastTsUpdatedIdx := lastTsUpdatedIdx.insert id j
    | .rules (.cast (.abilityActivated ab src _ kind)) =>
      firstMatIdx := recordFirst firstMatIdx ab j
      firstMatIdx := recordFirstOpt firstMatIdx src.id j
      match kind with
      | .nonMana .. =>
        if src.id != some ab then
          lastCreatedIdx := lastCreatedIdx.insert ab j
          lastTsUpdatedIdx := lastTsUpdatedIdx.insert ab j
      | _ => pure ()
    | .rules (.triggerQueue (.putOnStack stObj src ..)) =>
      firstMatIdx := recordFirst firstMatIdx stObj j
      firstMatIdx := recordFirstOpt firstMatIdx src.id j
      if src.id != some stObj then
        lastCreatedIdx := lastCreatedIdx.insert stObj j
        lastTsUpdatedIdx := lastTsUpdatedIdx.insert stObj j
    | .rules (.stackObject (.copied orig copy _)) =>
      firstMatIdx := recordFirst firstMatIdx orig j
      if let some cid := copy.id then
        firstMatIdx := recordFirst firstMatIdx cid j
        if copy.id != some orig then
          lastCreatedIdx := lastCreatedIdx.insert cid j
          lastTsUpdatedIdx := lastTsUpdatedIdx.insert cid j
    | _ => pure ()
  let mut unmatLookahead : Std.HashMap ObjectId Unit := {}
  if !prospectiveEnterIds.isEmpty then
    let mut liveIds : Std.HashMap ObjectId Unit := {}
    for o in g.objects do
      liveIds := liveIds.insert o.id ()
    for id in prospectiveEnterIds do
      if !liveIds.contains id && !firstMatIdx.contains id then
        unmatLookahead := unmatLookahead.insert id ()
  return {
    firstMatIdx, unmatLookahead, etbCostLifeFirst, etbCostBeholdFirst,
    lastCreatedIdx, lastTsUpdatedIdx, prefixMaxTs
  }

@[noinline] private def isInitialMaterializeWith (idxData : InitialMaterializeIndex)
    (g : Game) (oid : ObjectId) (matIdx : Nat) : Bool := Id.run do
  if oid == noSourceSentinelId then return false
  let bound := min matIdx g.events.size
  let matTs : Nat :=
    match g.events[bound]? with
    | some (.engine _ (.materializeObject obj _) _) => obj.timestamp
    | _ => (g.findObject? oid).map (·.timestamp) |>.getD 0
  if matTs > 0 && idxData.prefixMaxTs[bound]! > matTs then
    return false
  for other in g.objects do
    if other.id != oid && other.id != noSourceSentinelId then
      let checkId := other.id.raw > oid.raw
      let checkTs := matTs > 0 && other.timestamp > matTs
      if checkId || checkTs then
        let createdAfter := (idxData.lastCreatedIdx.get? other.id).any (· ≥ bound)
        if !createdAfter && checkId then return false
        if !createdAfter && checkTs && !((idxData.lastTsUpdatedIdx.get? other.id).any (· ≥ bound)) then
          return false
  let hasEtbCostProsp := !idxData.etbCostLifeFirst.isEmpty || !idxData.etbCostBeholdFirst.isEmpty
  let wasMatBefore (lim : Nat) (id : ObjectId) : Bool :=
    (idxData.firstMatIdx.get? id).any (· < lim)
  let isEtbCostProspectiveAt (idx : Nat) (ck : CostKind) (id : ObjectId) : Bool :=
    if !hasEtbCostProsp || id == noSourceSentinelId then false
    else
      let first? :=
        match ck with
        | .life => idxData.etbCostLifeFirst.get? id
        | .behold => idxData.etbCostBeholdFirst.get? id
        | _ => none
      first?.any (· < idx) && !wasMatBefore idx id
  let preBoundReject (id : ObjectId) : Bool :=
    id == oid || (id.raw > oid.raw && !idxData.unmatLookahead.contains id)
  let preBoundProspectiveReject (id : ObjectId) : Bool :=
    (id == oid || id.raw > oid.raw) && wasMatBefore bound id
  for j in [0:bound] do
    let ev := g.events[j]!
    let etbProsp := isEtbCostProspectiveAt j
    if gameChangeAnyObjId ev.change preBoundReject preBoundProspectiveReject etbProsp then
      return false
    if ev.cause?.any (fun c =>
        eventCauseAnyObjId c preBoundReject preBoundProspectiveReject etbProsp) then
      return false
  let mut createdSinceBound : Std.HashMap ObjectId Unit := {}
  for i in [bound : g.events.size] do
    let ev := g.events[i]!
    let isRepChoiceChange :=
      match ev.change with
      | .engine (.pending (.chooseReplacement ..))
      | .engine (.replacementOrder ..) => true
      | _ => false
    for cid in newlyCreatedIdsOfChange ev.change do
      let validNewId :=
        !isRepChoiceChange ||
          (idxData.lastCreatedIdx.get? cid).any (· ≥ bound) ||
          idxData.unmatLookahead.contains cid
      if cid != oid && validNewId then
        createdSinceBound := createdSinceBound.insert cid ()
    let isPreExistingNewer (refId : ObjectId) : Bool :=
      refId != oid && refId.raw > oid.raw && !createdSinceBound.contains refId
    let isPreExistingNewerProspective (refId : ObjectId) : Bool :=
      isPreExistingNewer refId && wasMatBefore bound refId
    let etbProsp := isEtbCostProspectiveAt i
    if gameChangeAnyObjId ev.change isPreExistingNewer isPreExistingNewerProspective etbProsp then
      return false
    if ev.cause?.any (fun c =>
        eventCauseAnyObjId c isPreExistingNewer isPreExistingNewerProspective etbProsp) then
      return false
  return true

private def isInitialMaterialize (g : Game) (oid : ObjectId) (matIdx : Nat) : Bool :=
  isInitialMaterializeWith (buildInitialMaterializeIndex g) g oid matIdx

/-- Pre-event `EventObject` snapshot recorded for `oid` on `ch`, if any (CR 113.7a). -/
private def eventObjectPreSnapshotOf? (ch : GameChange) (oid : ObjectId) : Option EventObject :=
  match ch with
  | .rules (.permanent (.counters (.object eo) ..))
  | .rules (.permanent (.tapped eo _))
  | .rules (.permanent (.untapped eo))
  | .rules (.permanent (.phasedOut eo _))
  | .rules (.permanent (.phasedIn eo _))
  | .rules (.permanent (.transformed eo _))
  | .rules (.permanent (.turnedFaceUp eo))
  | .rules (.permanent (.turnedFaceDown eo))
  | .rules (.permanent (.attached eo _ _))
  | .rules (.permanent (.unattached eo _))
  | .rules (.permanent (.designation eo _ _))
  | .rules (.combat (.becameAttacking eo _))
  | .rules (.combat (.becameBlocked eo _))
  | .rules (.combat (.remainedUnblocked eo))
  | .rules (.combat (.removedFromCombat eo))
  | .rules (.cast (.spellCast eo ..))
  | .rules (.cast (.abilityActivated _ eo ..))
  | .rules (.triggerQueue (.triggered eo ..))
  | .rules (.triggerQueue (.putOnStack _ eo ..))
  | .rules (.stackObject (.resolved eo ..))
  | .rules (.stackObject (.removedOnResolution eo))
  | .rules (.zone (.ceasedToExist eo)) =>
    if eo.id == some oid then some eo else none
  | .rules (.zone (.moved before _ ..)) =>
    if before.id == some oid then some before else none
  | .rules (.combat (.attackersDeclared _ decls)) =>
    decls.findSome? (fun (eo, _) => if eo.id == some oid then some eo else none)
  | .rules (.combat (.blockersDeclared _ decls)) =>
    decls.findSome? (fun (eo, _) => if eo.id == some oid then some eo else none)
  | .rules (.damage (.dealt pkts)) =>
    (pkts.findSome? fun pkt =>
      match pkt.recipient with
      | .permanent eo | .battle eo => if eo.id == some oid then some eo else none
      | .player _ => none).orElse fun _ =>
      pkts.findSome? (fun pkt => if pkt.source.id == some oid then some pkt.source else none)
  | .rules (.damage (.prevented src rec _)) =>
    match rec with
    | .permanent eo | .battle eo =>
      if eo.id == some oid then some eo
      else if src.id == some oid then some src
      else none
    | .player _ =>
      if src.id == some oid then some src else none
  | _ => none

private def abilitySourceLiveAt (g : Game) (evIdx : Nat) (eo : EventObject)
    (oid : ObjectId) : Bool := Id.run do
  if eo.id != some oid then return false
  match eo.zone with
  | .outside _ => return false
  | _ => pure ()
  if eo.zone == .battlefield && eo.name.isEmpty && eo.types.isEmpty &&
      eo.printed.isNone && !eo.faceDown then
    return false
  let mut b := min evIdx g.events.size
  while b > 0 do
    b := b - 1
    match g.events[b]!.change with
    | .rules (.zone (.ceasedToExist x)) =>
      if x.id == some oid then return false
    | .rules (.zone (.moved before after _ toZ ..)) =>
      if after.id == some oid then return toZ == eo.zone
      if before.id == some oid then return false
    | .rules (.zone (.created x _)) =>
      if x.id == some oid then return x.zone == eo.zone
    | .engine (.materializeObject obj _) =>
      if obj.id == oid then return obj.zone == eo.zone
    | .rules (.cast (.proposed obj ..)) =>
      if obj == oid then return eo.zone == .stack
    | .rules (.triggerQueue (.putOnStack stObj src ..)) =>
      if stObj == oid && src.id != some oid then return eo.zone == .stack
    | .rules (.cast (.abilityActivated ab src _ (.nonMana ..))) =>
      if ab == oid && src.id != some oid then return eo.zone == .stack
    | .rules (.stackObject (.copied orig copy _)) =>
      if copy.id == some oid && copy.id != some orig then return eo.zone == .stack
    | _ => pure ()
  for k in [evIdx + 1 : g.events.size] do
    match g.events[k]!.change with
    | .rules (.zone (.ceasedToExist x)) =>
      if x.id == some oid then return x.zone == eo.zone
    | .rules (.zone (.moved before after fromZ ..)) =>
      if before.id == some oid then return fromZ == eo.zone
      if after.id == some oid then return false
    | .rules (.zone (.created x _)) =>
      if x.id == some oid then return false
    | .engine (.materializeObject obj _) =>
      if obj.id == oid then
        return !g.isInitialMaterialize oid k
    | _ => pure ()
  return (g.findObject? oid).any (fun cur => cur.zone == eo.zone)

private def eventObjectIsLiveSubject (g : Game) (evIdx : Nat) (ch : GameChange)
    (oid : ObjectId) : Bool :=
  match ch with
  | .rules (.permanent (.designation eo .ringBearer false)) =>
    abilitySourceLiveAt g evIdx eo oid
  | .rules (.permanent _)
  | .rules (.combat _)
  | .rules (.cast (.spellCast ..)) => true
  | .rules (.stackObject (.resolved eo ..))
  | .rules (.stackObject (.removedOnResolution eo)) =>
    abilitySourceLiveAt g evIdx eo oid
  | .rules (.stackObject _) => true
  | .rules (.cast (.abilityActivated _ eo ..)) => abilitySourceLiveAt g evIdx eo oid
  | .rules (.damage (.dealt pkts)) =>
    pkts.any fun pkt =>
      match pkt.recipient with
      | .permanent eo | .battle eo => eo.id == some oid
      | .player _ => false
  | .rules (.damage (.prevented _ rec _)) =>
    match rec with
    | .permanent eo | .battle eo => eo.id == some oid
    | .player _ => false
  | _ => false

def objectZoneAndPhasedOutAt? (g : Game) (oid : ObjectId) (evIdx : Nat) :
    Option (Zone × Bool) :=
  let bound := min evIdx g.events.size
  Id.run do
    let mut seenPhased? : Option Bool := none
    for rev in [0:bound] do
      let i := bound - 1 - rev
      match g.events[i]!.change with
      | .rules (.permanent (.phasedOut eo _)) =>
        if eo.id == some oid && seenPhased?.isNone then seenPhased? := some true
      | .rules (.permanent (.phasedIn eo _)) =>
        if eo.id == some oid && seenPhased?.isNone then seenPhased? := some false
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some oid then return none
      | .rules (.zone (.moved before after _ toZone ..)) =>
        if after.id == some oid then
          return some (toZone, toZone == .battlefield && seenPhased?.getD after.phasedOut)
        if before.id == some oid then return none
      | .rules (.zone (.created eo _)) =>
        if eo.id == some oid then
          return some (eo.zone, eo.zone == .battlefield && seenPhased?.getD eo.phasedOut)
      | .engine (.materializeObject obj _) =>
        if obj.id == oid then
          return some (obj.zone, obj.zone == .battlefield && seenPhased?.getD obj.status.phasedOut)
      | _ => pure ()
    if let some ph := seenPhased? then
      return some (.battlefield, ph)
    let mut cur? : Option (Zone × Bool) :=
      (g.findObject? oid).map fun obj => (obj.zone, obj.zone == .battlefield && obj.status.phasedOut)
    for rev in [0 : g.events.size - bound] do
      let i := g.events.size - 1 - rev
      let ch := g.events[i]!.change
      match ch with
      | .rules (.permanent (.phasedOut eo _)) =>
        if eo.id == some oid then cur? := some (.battlefield, false)
      | .rules (.permanent (.phasedIn eo _)) =>
        if eo.id == some oid then cur? := some (.battlefield, true)
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some oid then
          cur? := some (eo.zone, eo.zone == .battlefield && eo.phasedOut)
      | .rules (.zone (.moved before after fromZone _ ..)) =>
        if before.id == some oid then
          cur? := some (fromZone, fromZone == .battlefield && before.phasedOut)
        else if after.id == some oid then
          cur? := none
      | .rules (.zone (.created eo _)) =>
        if eo.id == some oid then
          cur? := none
      | .engine (.materializeObject obj _) =>
        if obj.id == oid && g.isInitialMaterialize oid i then
          cur? := none
      | _ =>
        if eventObjectIsLiveSubject g i ch oid then
          if let some eo := eventObjectPreSnapshotOf? ch oid then
            cur? := some (eo.zone, eo.zone == .battlefield && eo.phasedOut)
    return cur?

/-- Whether `o` was phased out on the battlefield immediately before event
`evIdx` in `g.events` (CR 611.2b–c / 702.26b,e). -/
def objectWasPhasedOutAt (g : Game) (o : GameObject) (evIdx : Nat) : Bool :=
  (g.objectZoneAndPhasedOutAt? o.id evIdx).any (fun (z, ph) => z == .battlefield && ph)

/-- Latest `PermanentEvent.phasedOut` (or phased-out `.materializeObject` /
arrival) index for `o` in `g.events` when currently phased out (CR 702.26b,e). -/
def latestPhaseOutIdxOf? (g : Game) (o : GameObject) : Option Nat :=
  if !o.status.phasedOut then none
  else Id.run do
    for rev in [0:g.events.size] do
      let i := g.events.size - 1 - rev
      match g.events[i]!.change with
      | .rules (.permanent (.phasedOut eo _)) =>
        if eo.id == some o.id then return some i
      | .engine (.materializeObject obj _) =>
        if obj.id == o.id && obj.zone == .battlefield && obj.status.phasedOut &&
            !g.objectWasPhasedOutAt o i then
          return some i
      | .rules (.zone (.moved before after _ toZone ..)) =>
        if after.id == some o.id && toZone == .battlefield && after.phasedOut &&
            (before.id != some o.id || !g.objectWasPhasedOutAt o i) then
          return some i
      | .rules (.zone (.created eo _)) =>
        if eo.id == some o.id && eo.zone == .battlefield && eo.phasedOut then
          return some i
      | _ => pure ()
    return none

def objectCounterCountAt (g : Game) (oid : ObjectId) (k : CounterKind)
    (evIdx : Nat) : Nat :=
  let bound := min evIdx g.events.size
  Id.run do
    let mut count? : Option Nat := none
    let mut departed : Bool := false
    for i in [0:bound] do
      let ch := g.events[i]!.change
      match ch with
      | .rules (.permanent (.counters (.object eo) k' (.put n) _)) =>
        if eo.id == some oid then
          let base := count?.getD (eo.counters.count k)
          count? := some (if k' == k then base + n else base)
          departed := false
      | .rules (.permanent (.counters (.object eo) k' (.removed n) _)) =>
        if eo.id == some oid then
          let base := count?.getD (eo.counters.count k)
          count? := some (if k' == k then base - n else base)
          departed := false
      | .rules (.zone (.moved before after _ _ _ _ entersWith _)) =>
        if before.id == some oid && after.id != some oid then
          count? := some 0
          departed := true
        if after.id == some oid then
          count? := some (max (after.counters.count k) (entersWith.count k))
          departed := false
      | .rules (.zone (.created eo _)) =>
        if eo.id == some oid then
          count? := some (eo.counters.count k)
          departed := false
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some oid then
          count? := some 0
          departed := true
      | .engine (.materializeObject obj _) =>
        if obj.id == oid then
          count? := some (obj.status.counters.count k)
          departed := false
      | _ =>
        if count?.isNone then
          if let some eo := eventObjectPreSnapshotOf? ch oid then
            if !departed && eventObjectIsLiveSubject g i ch oid then
              count? := some (eo.counters.count k)
    if let some c := count? then
      return c
    for i in [bound : g.events.size] do
      let ch := g.events[i]!.change
      match ch with
      | .rules (.zone (.moved before after ..)) =>
        if before.id == some oid then return before.counters.count k
        else if after.id == some oid then return 0
      | .rules (.zone (.created eo _)) =>
        if eo.id == some oid then return 0
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some oid then return eo.counters.count k
      | .engine (.materializeObject obj _) =>
        if obj.id == oid && g.isInitialMaterialize oid i then
          return 0
      | _ =>
        if eventObjectIsLiveSubject g i ch oid then
          if let some eo := eventObjectPreSnapshotOf? ch oid then
            return eo.counters.count k
    return ((g.findObject? oid).map (·.status.counters.count k)).getD 0

private def durationActiveAt (g : Game) (d : EffectDuration) (evIdx : Nat) : Bool :=
  match d with
  | .whileSourceOnBattlefield src =>
    (g.objectZoneAndPhasedOutAt? src evIdx).any (fun (z, ph) => z == .battlefield && !ph)
  | .untilSourceLeaves src =>
    (g.objectZoneAndPhasedOutAt? src evIdx).any (fun (z, _) => z == .battlefield)
  | .whileSourceHasCounter src k =>
    (g.objectZoneAndPhasedOutAt? src evIdx).any (fun (z, ph) => z == .battlefield && !ph) &&
      g.objectCounterCountAt src k evIdx > 0
  | .whileInZone oid z =>
    (g.objectZoneAndPhasedOutAt? oid evIdx).any (fun (z', _) => z' == z)
  | _ => true

def durationActiveContinuouslySince (g : Game) (d : EffectDuration) (pIdx : Nat) : Bool :=
  if !g.durationActiveAt d pIdx then false
  else
    let start := min pIdx g.events.size
    match d with
    | .whileSourceOnBattlefield src =>
      Id.run do
        for i in [start : g.events.size] do
          match g.events[i]!.change with
          | .rules (.permanent (.phasedOut eo _)) =>
            if eo.id == some src then return false
          | .rules (.zone (.ceasedToExist eo)) =>
            if eo.id == some src then return false
          | .rules (.zone (.moved before ..)) =>
            if before.id == some src then return false
          | .engine (.materializeObject obj _) =>
            if obj.id == src && (obj.zone != .battlefield || obj.status.phasedOut) then
              return false
          | _ => pure ()
        return g.durationActive d
    | .untilSourceLeaves src =>
      Id.run do
        for i in [start : g.events.size] do
          match g.events[i]!.change with
          | .rules (.zone (.ceasedToExist eo)) =>
            if eo.id == some src then return false
          | .rules (.zone (.moved before ..)) =>
            if before.id == some src then return false
          | .engine (.materializeObject obj _) =>
            if obj.id == src && obj.zone != .battlefield then
              return false
          | _ => pure ()
        return g.durationActive d
    | .whileSourceHasCounter src k =>
      Id.run do
        let mut cnt := g.objectCounterCountAt src k start
        if cnt == 0 then return false
        for i in [start : g.events.size] do
          match g.events[i]!.change with
          | .rules (.permanent (.phasedOut eo _)) =>
            if eo.id == some src then return false
          | .rules (.zone (.ceasedToExist eo)) =>
            if eo.id == some src then return false
          | .rules (.zone (.moved before ..)) =>
            if before.id == some src then return false
          | .rules (.permanent (.counters (.object eo) k' (.put n) _)) =>
            if eo.id == some src && k' == k then
              cnt := cnt + n
          | .rules (.permanent (.counters (.object eo) k' (.removed n) _)) =>
            if eo.id == some src && k' == k then
              cnt := cnt - n
              if cnt == 0 then return false
          | .engine (.materializeObject obj _) =>
            if obj.id == src then
              if obj.zone != .battlefield || obj.status.phasedOut then return false
              cnt := obj.status.counters.count k
              if cnt == 0 then return false
          | _ => pure ()
        return g.durationActive d
    | .whileInZone oid z =>
      Id.run do
        for i in [start : g.events.size] do
          match g.events[i]!.change with
          | .rules (.zone (.ceasedToExist eo)) =>
            if eo.id == some oid then return false
          | .rules (.zone (.moved before after _ toZone ..)) =>
            if before.id == some oid && !(after.id == some oid && toZone == z) then
              return false
          | .engine (.materializeObject obj _) =>
            if obj.id == oid && obj.zone != z then
              return false
          | _ => pure ()
        return g.durationActive d
    | _ => g.durationActive d

/-- Whether continuous effect `(eid, sc, d)` is eligible to affect `o` under
CR 611.2b–c resolving-effect scope lock-in (Layers 1–7) and, when `phaseOutIdx?`
is supplied (Layers 1–2 while `o.status.phasedOut`), continuous active duration
across `[pIdx .. now]` (CR 611.3a / 702.26b,d,e,f). -/
private def effectPhasingAllows (g : Game) (o : GameObject) (eid : EffectId)
    (sc : ObjectScope) (d : EffectDuration)
    (phaseOutIdx? : Option Nat := none)
    (ignoreDuration : Bool := false) : Bool :=
  let isExplicitObjects := match sc with | .objects _ => true | _ => false
  if isExplicitObjects && phaseOutIdx?.isNone then true
  else
    let contActive (pIdx : Nat) : Bool :=
      ignoreDuration || d.isTimedResolvingDuration || g.durationActiveContinuouslySince d pIdx
    match g.effectCreatedInfo? eid with
    | none =>
      match phaseOutIdx? with
      | none => true
      | some pIdx => contActive pIdx
    | some (createdIdx, createdCause) =>
      let isLocked := d.isTimedResolvingDuration || isOneShotEffectCause createdCause
      let lockOk := isExplicitObjects || !isLocked || !g.objectWasPhasedOutAt o createdIdx
      let curPhaseOutOk :=
        match phaseOutIdx? with
        | none => true
        | some pIdx => createdIdx < pIdx && contActive pIdx
      lockOk && curPhaseOutOk

/-- Initial Layer 2 controller of `o` before active `LayerEffect.control` effects,
used internally by Layer 1 and Layer 2 (CR 110.2 / 613.1a–b / 800.4a). -/
private def initialControllerOf (g : Game) (o : GameObject) : Option PlayerId :=
  if o.zone != .battlefield then o.controller
  else
    let playerAlive (p : PlayerId) : Bool :=
      if p.idx < g.players.size then !(g.player p).leftTheGame
      else true
    let defP := (o.defaultController.orElse (fun _ => o.controller)).getD o.owner
    if playerAlive defP then some defP else none

/-- Ordered `(EffectId, CardDef)` chain of active Layer 1a copy effects applied
to `o` in CR 613.7 timestamp and CR 613.8 dependency order (CR 613.2a / 707.2). -/
def activeLayer1CopyChain (g : Game) (o : GameObject)
    (ignoreDurationFor : Array EffectId := #[]) : Array (EffectId × CardDef) :=
  if o.isLkiSnapshot then #[]
  else
    let hasCopy := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.copy _) _ => true
      | _ => false
    if !hasCopy then #[]
    else
      let initCtrl := g.initialControllerOf o
      let phaseOutIdx? :=
        if o.status.phasedOut then some ((g.latestPhaseOutIdxOf? o).getD 0) else none
      let scopeMatchesL1 (cur : CardDef) (sc : ObjectScope) : Bool :=
        match sc with
        | .objects ids => ids.contains o.id
        | .creaturesControlledBy p =>
          o.isBattlefieldObject && initCtrl == some p && cur.types.contains .creature
        | .creaturesWithout kw =>
          o.isBattlefieldObject && cur.types.contains .creature &&
            kw.any (fun k => !cur.keywords.contains k)
        | .permanentsOfSubtype p s =>
          o.isBattlefieldObject && initCtrl == some p &&
            ((CardSubtype.ofSubtypes cur.subtypes).contains s ||
              (cur.hasSimpleKeyword .changeling &&
                (cur.types.contains .creature || cur.types.contains .kindred) && !s.isNoncreature))
      Id.run do
        let mut raw : Array Layer1Entry := #[]
        for pos in [0:g.activeEffects.size] do
          let (eid, s) := g.activeEffects[pos]!
          match s with
          | .layered sc (.copy card) d =>
            let ig := ignoreDurationFor.contains eid
            if (ig || g.durationActive d) &&
                g.effectPhasingAllows o eid sc d (phaseOutIdx? := phaseOutIdx?) (ignoreDuration := ig) then
              raw := raw.push {
                idx := raw.size
                eid := eid
                ts := g.effectTimestamp eid pos
                scope := sc
                card := card
              }
          | _ => pure ()
        let sorted := raw.qsort fun a b =>
          if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
          else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
          else a.idx < b.idx
        let mut rem := sorted
        let mut cur := o.printed
        let mut applied : Array (EffectId × CardDef) := #[]
        for _ in [0:sorted.size] do
          let applicable := rem.filter (fun e => scopeMatchesL1 cur e.scope)
          if applicable.isEmpty then break
          let dependsOn (a b : Layer1Entry) : Bool :=
            a.idx != b.idx &&
              scopeMatchesL1 cur a.scope != scopeMatchesL1 b.card a.scope
          let chosen :=
            (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
          cur := chosen.card
          applied := applied.push (chosen.eid, chosen.card)
          rem := rem.filter (fun e => e.idx != chosen.idx)
        return applied

/-- Layer 1a copiable values of `o` before Layer 1b face-down masking, paired with
the CR 613.7a base ability timestamp (`max(objectEntryTimestamp,
lastCopyEffectTimestamp)`) (CR 613.2a / 702.37e). Used only where rules look past
face-down status (such as reading a face-down permanent's morph cost). -/
def unmaskedCopiableValuesWithTs (g : Game) (o : GameObject) : CardDef × (Nat × Nat) :=
  let objTs := g.objectEntryTimestamp o
  if o.isLkiSnapshot then (o.printed, objTs)
  else
  let hasCopy := g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.copy _) _ => true
    | _ => false
  if !hasCopy then (o.printed, objTs)
  else
    let initCtrl := g.initialControllerOf o
    let phaseOutIdx? :=
      if o.status.phasedOut then some ((g.latestPhaseOutIdxOf? o).getD 0) else none
    let scopeMatchesL1 (cur : CardDef) (sc : ObjectScope) : Bool :=
      match sc with
      | .objects ids => ids.contains o.id
      | .creaturesControlledBy p =>
        o.isBattlefieldObject && initCtrl == some p && cur.types.contains .creature
      | .creaturesWithout kw =>
        o.isBattlefieldObject && cur.types.contains .creature &&
          kw.any (fun k => !cur.keywords.contains k)
      | .permanentsOfSubtype p s =>
        o.isBattlefieldObject && initCtrl == some p &&
          ((CardSubtype.ofSubtypes cur.subtypes).contains s ||
            (cur.hasSimpleKeyword .changeling &&
              (cur.types.contains .creature || cur.types.contains .kindred) && !s.isNoncreature))
    Id.run do
      let mut raw : Array Layer1Entry := #[]
      for pos in [0:g.activeEffects.size] do
        let (eid, s) := g.activeEffects[pos]!
        match s with
        | .layered sc (.copy card) d =>
          if g.durationActive d && g.effectPhasingAllows o eid sc d (phaseOutIdx? := phaseOutIdx?) then
            raw := raw.push {
              idx := raw.size
              eid := eid
              ts := g.effectTimestamp eid pos
              scope := sc
              card := card
            }
        | _ => pure ()
      let sorted := raw.qsort fun a b =>
        if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
        else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
        else a.idx < b.idx
      let mut rem := sorted
      let mut cur := o.printed
      let mut curTs := objTs
      for _ in [0:sorted.size] do
        let applicable := rem.filter (fun e => scopeMatchesL1 cur e.scope)
        if applicable.isEmpty then break
        let dependsOn (a b : Layer1Entry) : Bool :=
          a.idx != b.idx &&
            scopeMatchesL1 cur a.scope != scopeMatchesL1 b.card a.scope
        let chosen :=
          (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
        cur := chosen.card
        curTs := maxTs curTs chosen.ts
        rem := rem.filter (fun e => e.idx != chosen.idx)
      return (cur, curTs)

/-- Layer 1a copiable values of `o` before Layer 1b face-down masking (CR 613.2a / 702.37e). -/
def unmaskedCopiableValues (g : Game) (o : GameObject) : CardDef :=
  if o.isLkiSnapshot then o.printed
  else
  let hasCopy := g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.copy _) _ => true
    | _ => false
  if !hasCopy then o.printed
  else (g.unmaskedCopiableValuesWithTs o).1

/-- Whether `o` is face down in a zone where CR 708.2 masks its characteristics
as a 2/2 colorless nameless creature (battlefield or stack only). -/
@[inline] def isFaceDownMasked (o : GameObject) : Bool :=
  o.status.faceDown && (o.zone == .battlefield || o.zone == .stack)

/-- Layer 1 copiable values of `o` after both Layer 1a copy effects and Layer 1b
face-down status (CR 613.2a–c / 707.2 / 708.2), paired with the CR 613.7a base
timestamp. -/
def copiableValuesWithTs (g : Game) (o : GameObject) : CardDef × (Nat × Nat) :=
  if isFaceDownMasked o then
    ({ name := "", types := #[.creature], power := some (.fixed 2), toughness := some (.fixed 2) },
     g.objectEntryTimestamp o)
  else if o.isLkiSnapshot then (o.printed, g.objectEntryTimestamp o)
  else
    g.unmaskedCopiableValuesWithTs o

/-- Layer 1 copiable values of `o` after Layer 1a copy effects and Layer 1b
face-down status (CR 613.2a–c / 707.2 / 708.2). -/
def copiableValues (g : Game) (o : GameObject) : CardDef :=
  if isFaceDownMasked o then
    { name := "", types := #[.creature], power := some (.fixed 2), toughness := some (.fixed 2) }
  else if o.isLkiSnapshot then o.printed
  else
    g.unmaskedCopiableValues o

/-- Layer 1 characteristics of `o` after both Layer 1a copy effects and Layer 1b
face-down status (CR 613.2a–c / 708.2), paired with the CR 613.7a base timestamp. -/
@[inline] def baseCardWithTs (g : Game) (o : GameObject) : CardDef × (Nat × Nat) :=
  g.copiableValuesWithTs o

/-- Layer 1 characteristics of `o` after Layer 1a copy effects and Layer 1b
face-down status (CR 613.2a–c / 708.2). -/
@[inline] def baseCard (g : Game) (o : GameObject) : CardDef :=
  g.copiableValues o

/-- Evaluated name of `o` after Layer 1 copy and face-down effects (CR 201 / 613.1a / 708.2a). -/
def name (g : Game) (o : GameObject) : String :=
  (g.baseCard o).name

/-- Evaluated console/log name of `o`, marking tokens (CR 111 / 613.1a). -/
def nameWithToken (g : Game) (o : GameObject) : String :=
  if o.printed.isToken then s!"{g.name o} (token)" else g.name o

-- Layer 2: Control-changing effects (CR 613.1b / 613.7 / 613.8)

private structure Layer2Entry where
  idx : Nat
  eid : EffectId
  ts : Nat × Nat
  scope : ObjectScope
  ctrl : PlayerId
deriving Inhabited

/-- Evaluated controller of `o` in Layer 2 together with the `EffectId`s of all
active `LayerEffect.control` effects that applied to `o` in CR 613.7 timestamp
and CR 613.8 dependency order (CR 613.1b). -/
def effectiveControllerWithApplied (g : Game) (o : GameObject) :
    Option PlayerId × Array EffectId :=
  if o.isLkiSnapshot then (o.controller, #[])
  else
  let initCtrl := g.initialControllerOf o
  if o.zone != .battlefield then (initCtrl, #[])
  else
    let hasCtrl := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.control _) _ => true
      | _ => false
    if !hasCtrl then (initCtrl, #[])
    else
      let bc := g.baseCard o
      let phaseOutIdx? :=
        if o.status.phasedOut then some ((g.latestPhaseOutIdxOf? o).getD 0) else none
      let scopeMatchesL2 (cur : Option PlayerId) (sc : ObjectScope) : Bool :=
        match sc with
        | .objects ids => ids.contains o.id
        | .creaturesControlledBy p =>
          o.isBattlefieldObject && cur == some p && bc.types.contains .creature
        | .creaturesWithout kw =>
          o.isBattlefieldObject && bc.types.contains .creature &&
            kw.any (fun k => !bc.keywords.contains k)
        | .permanentsOfSubtype p s =>
          o.isBattlefieldObject && cur == some p &&
            ((CardSubtype.ofSubtypes bc.subtypes).contains s ||
              (bc.hasSimpleKeyword .changeling &&
                (bc.types.contains .creature || bc.types.contains .kindred) && !s.isNoncreature))
      Id.run do
        let mut cands : Array (EffectId × Nat × ObjectScope × PlayerId) := #[]
        for pos in [0:g.activeEffects.size] do
          let (eid, s) := g.activeEffects[pos]!
          match s with
          | .layered sc (.control c) d =>
            if g.durationActive d && g.effectPhasingAllows o eid sc d (phaseOutIdx? := phaseOutIdx?) then
              cands := cands.push (eid, pos, sc, c)
          | _ => pure ()
        if cands.isEmpty then return (initCtrl, #[])
        let needTs := cands.size >= 2
        let mut raw : Array Layer2Entry := #[]
        for (eid, pos, sc, c) in cands do
          raw := raw.push {
            idx := raw.size
            eid := eid
            ts := if needTs then g.effectTimestamp eid pos else (0, 0)
            scope := sc
            ctrl := c
          }
        let sorted :=
          if !needTs then raw
          else raw.qsort fun a b =>
            if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
            else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
            else a.idx < b.idx
        let mut rem := sorted
        let mut cur := initCtrl
        let mut applied : Array EffectId := #[]
        for _ in [0:sorted.size] do
          let applicable := rem.filter (fun e => scopeMatchesL2 cur e.scope)
          if applicable.isEmpty then break
          let dependsOn (a b : Layer2Entry) : Bool :=
            a.idx != b.idx &&
              scopeMatchesL2 cur a.scope != scopeMatchesL2 (some b.ctrl) a.scope
          let chosen :=
            (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
          cur := some chosen.ctrl
          applied := applied.push chosen.eid
          rem := rem.filter (fun e => e.idx != chosen.idx)
        return (cur, applied)

/-- Evaluated controller of `o` in Layer 2 across all active `LayerEffect.control`
effects in CR 613.7 timestamp and CR 613.8 dependency order (CR 613.1b). -/
@[inline] def effectiveController? (g : Game) (o : GameObject) : Option PlayerId :=
  (g.effectiveControllerWithApplied o).1

/-- Active Layer 2 `EffectId`s currently applying to `o` (CR 613.1b). -/
@[inline] def appliedControlEffectIds (g : Game) (o : GameObject) : Array EffectId :=
  (g.effectiveControllerWithApplied o).2

/-- Evaluated controller of `o` after Layer 2 control-changing effects (CR 613.1b). -/
@[inline] def controllerOf (g : Game) (o : GameObject) : Option PlayerId :=
  g.effectiveController? o

/-- Whether `o` is currently controlled by `p` after Layer 2 (CR 613.1b). -/
def controlledBy (g : Game) (o : GameObject) (p : PlayerId) : Bool :=
  g.controllerOf o == some p

/-- The player “you” and “your” refer to on `o` after Layer 2 (CR 109.5 / 613.1b). -/
def you (g : Game) (o : GameObject) : PlayerId :=
  (g.controllerOf o).getD o.owner

/-- Permanents `p` currently controls on the battlefield after Layer 2 (CR 613.1b). -/
def permanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o => g.controlledBy o p)

/-- Whether `o` is a non-token, non-copy card that can legally be discarded
from hand (CR 108.2b / 111.8 / 707.10a). -/
def isDiscardableCard (o : GameObject) : Bool :=
  !o.printed.isToken && !o.isCopy

/-- Whether `o` can legally be cast (excluding tokens in all zones and non-exile
copies awaiting SBAs, while allowing CR 707.12 card copies in exile; CR 111.8 / 707.12). -/
def isCastableObject (o : GameObject) : Bool :=
  !o.printed.isToken && (o.zone == .exile || !o.isCopy)

/-- Object IDs of cards in `p`'s hand that can legally be discarded, excluding
bounced tokens and non-card copies awaiting SBAs (CR 108.2b / 111.7–8 / 704.5d–e). -/
def discardableHandIds (g : Game) (p : PlayerId) : Array ObjectId :=
  (g.player p).hand.filter fun id =>
    (g.findObject? id).any isDiscardableCard

/-- Clear `summoningSick` on every battlefield permanent controlled by `ap` or
any teammate on `ap`'s team as their shared turn or first-seat untap step begins
(CR 302.6 / 805.4a / 810.2). Includes phased-out permanents (CR 702.26d) and
permanents controlled via Layer 2 effects. -/
private def clearSummoningSickFor (g : Game) (ap : PlayerId) : Game :=
  let team := g.teamMembers ap
  { g with
    objects := g.objects.map fun o =>
      if o.zone == .battlefield && o.status.summoningSick &&
          team.any (fun tm => g.controlledBy o tm) then
        { o with status := { o.status with summoningSick := false } }
      else o }

/-- Apply a `TurnEvent` to `g` (CR 500 / 302.6 / 805.4 / 805.8 / 810.2). -/
def applyTurnEvent (g : Game) (e : TurnEvent) : Game :=
  let priorLimit : Nat :=
    match g.events.back? with
    | some last =>
      if last.change == .rules (.turn e) then g.events.size - 1 else g.events.size
    | none => 0
  match e with
  | .turnBegan player extra =>
    let (seats, seatsExtra) := g.currentSharedTurnState (some priorLimit)
    let sameShared :=
      extra == seatsExtra && !seats.isEmpty &&
        g.areTeammates seats[0]! player && !seats.contains player
    let dropLost (xs : Array PlayerId) : Array PlayerId :=
      (xs.toList.dropWhile (fun q =>
        if q.idx < g.players.size then !g.stillInGame q else true)).toArray
    let restExtra :=
      if extra then
        let trimmed := dropLost g.extraTurns
        if trimmed[0]? == some player then trimmed.extract 1 trimmed.size
        else trimmed
      else if sameShared then
        g.extraTurns
      else
        dropLost g.extraTurns
    let g :=
      { g with
        turnNumber := if sameShared then g.turnNumber else g.turnNumber + 1
        activePlayer := player
        isFirstTurn := g.isFirstTurn && sameShared
        extraTurns := restExtra }
    if sameShared then g else g.clearSummoningSickFor player
  | .phaseBegan phase =>
    if phase == .combat && g.step == .endOfCombat && g.additionalCombatPhases > 0 then
      { g with additionalCombatPhases := g.additionalCombatPhases - 1 }
    else g
  | .stepBegan st active =>
    let (seats, _) := g.currentSharedTurnState (some priorLimit)
    let firstSeatUntap :=
      seats.isEmpty || seats == #[active] || !g.areTeammates seats[0]! active
    let g := { g with step := st, assignedCombatDamage := #[] }
    if st == .untap && firstSeatUntap then g.clearSummoningSickFor active else g
  | .stepEnded st =>
    if st == .combatDamage then { g with assignedCombatDamage := #[] } else g
  | .phaseEnded phase =>
    if phase == .combat then { g with assignedCombatDamage := #[] } else g
  | .extraStepAdded step where_ =>
    if step == .combatDamage && where_ == .afterCurrent then
      { g with assignedCombatDamage := #[] }
    else g
  | .turnEnded _ => g
  | .dayNightChanged night =>
    { g with isNight := night }
  | .extraTurnAdded player _ =>
    let (seats, seatsExtra) := g.currentSharedTurnState (some priorLimit)
    let team := g.teamMembers player
    let inProgress :=
      if !seatsExtra || seats.isEmpty then 0
      else Id.run do
        let curTeam := g.teamMembers seats[0]!
        let lastSeat := seats.back!
        let mut remIdx : Nat :=
          match curTeam.findIdx? (· == lastSeat) with
          | some k => k + 1
          | none => curTeam.size
        let mut cnt : Nat := 0
        for q in g.extraTurns do
          match (curTeam.extract remIdx curTeam.size).findIdx? (· == q) with
          | some rel =>
            remIdx := remIdx + rel + 1
            cnt := cnt + 1
          | none =>
            return cnt
        return cnt
    { g with
      extraTurns :=
        g.extraTurns.extract 0 inProgress ++ team ++
          g.extraTurns.extract inProgress g.extraTurns.size }
  | .extraPhaseAdded phase _ =>
    if phase == .combat then
      { g with additionalCombatPhases := g.additionalCombatPhases + 1 }
    else g

/-- Process one `DelayedTriggerEvent` in isolation (CR 603.7). -/
def applyDelayedTriggerEvent (g : Game) (e : DelayedTriggerEvent) : Game :=
  match e with
  | .created dt =>
    { g with delayedTriggers := g.delayedTriggers.push dt }
  | .consumed dt | .expired dt =>
    match g.delayedTriggers.findIdx? (fun x =>
        x.controller == dt.controller && x.kind == dt.kind && x.cause == dt.cause) with
    | some idx => { g with delayedTriggers := g.delayedTriggers.eraseIdx! idx }
    | none => g

/-- Capture a CR 734.1 pre-proposal checkpoint at event index `eventsSize`. -/
def captureProposalCheckpoint (g : Game) (eventsSize : Nat) : ProposalCheckpoint :=
  { eventsSize
    players := g.players
    objects := g.objects
    stack := g.stack
    activePlayer := g.activePlayer
    priority := g.priority
    pendingPriority := g.pendingPriority
    step := g.step
    turnNumber := g.turnNumber
    startingPlayer := g.startingPlayer
    isFirstTurn := g.isFirstTurn
    pending := g.pending
    nextObjectId := g.nextObjectId
    nextEffectId := g.nextEffectId
    nextBatchId := g.nextBatchId
    currentBatch := g.currentBatch
    openBatchObjects := g.openBatchObjects
    openBatchPlayers := g.openBatchPlayers
    openBatchEffects := g.openBatchEffects
    openBatchPending := g.openBatchPending
    openBatchStack := g.openBatchStack
    activeEffects := g.activeEffects
    timestamp := g.timestamp
    pregameRandom := g.pregameRandom
    result := g.result
    log := g.log
    format := g.format
    brawl := g.brawl
    consecutivePasses := g.consecutivePasses
    cleanupGivesPriority := g.cleanupGivesPriority
    proposedSpell := g.proposedSpell
    awaitingOpeningBegin := g.awaitingOpeningBegin
    mulliganToDeclare := g.mulliganToDeclare
    willMulligan := g.willMulligan
    mulliganToBottom := g.mulliganToBottom
    assignedCombatDamage := g.assignedCombatDamage
    pendingBlockerAssignments := g.pendingBlockerAssignments
    blockersQueue := g.blockersQueue
    waitingTriggers := g.waitingTriggers
    queuedLinkedExile := g.queuedLinkedExile
    isNight := g.isNight
    continuations := g.continuations
    replacementOrder := g.replacementOrder
    castingFromTop := g.castingFromTop
    delayedTriggers := g.delayedTriggers
    extraTurns := g.extraTurns
    additionalCombatPhases := g.additionalCombatPhases }

/-- Whether any frame in `frames` holds a `PendingReplacement` continuation
with `suppressInteractive == true`. -/
def continuationsHaveSuppressedReplay (frames : Array ContinuationFrame) : Bool :=
  frames.any fun f =>
    f.pendingReplacement.any (·.hasSuppressedCheckpointReplay) ||
      f.outerPendingReplacements.any (·.hasSuppressedCheckpointReplay)

/-- Restore `g` from `ckpt`, truncating `g.events` back to `ckpt.eventsSize` (CR 734.1). -/
def restoreProposalCheckpoint (g : Game) (ckpt : ProposalCheckpoint) : Game :=
  { players := ckpt.players
    objects := ckpt.objects
    stack := ckpt.stack
    activePlayer := ckpt.activePlayer
    priority := ckpt.priority
    pendingPriority := ckpt.pendingPriority
    step := ckpt.step
    turnNumber := ckpt.turnNumber
    startingPlayer := ckpt.startingPlayer
    isFirstTurn := ckpt.isFirstTurn
    pending := ckpt.pending
    nextObjectId := ckpt.nextObjectId
    nextEffectId := ckpt.nextEffectId
    nextBatchId := ckpt.nextBatchId
    currentBatch := ckpt.currentBatch
    openBatchObjects := ckpt.openBatchObjects
    openBatchPlayers := ckpt.openBatchPlayers
    openBatchEffects := ckpt.openBatchEffects
    openBatchPending := ckpt.openBatchPending
    openBatchStack := ckpt.openBatchStack
    openBatchSuppressInteractive := false
    activeEffects := ckpt.activeEffects
    timestamp := ckpt.timestamp
    pregameRandom := ckpt.pregameRandom
    result := ckpt.result
    log := ckpt.log
    format := ckpt.format
    brawl := ckpt.brawl
    consecutivePasses := ckpt.consecutivePasses
    cleanupGivesPriority := ckpt.cleanupGivesPriority
    proposedSpell := ckpt.proposedSpell
    proposalCheckpoint := g.outerProposalCheckpoints.back?
    outerProposalCheckpoints := g.outerProposalCheckpoints.pop
    awaitingOpeningBegin := ckpt.awaitingOpeningBegin
    mulliganToDeclare := ckpt.mulliganToDeclare
    willMulligan := ckpt.willMulligan
    mulliganToBottom := ckpt.mulliganToBottom
    assignedCombatDamage := ckpt.assignedCombatDamage
    pendingBlockerAssignments := ckpt.pendingBlockerAssignments
    blockersQueue := ckpt.blockersQueue
    waitingTriggers := ckpt.waitingTriggers
    queuedLinkedExile := ckpt.queuedLinkedExile
    isNight := ckpt.isNight
    continuations := ckpt.continuations
    replacementOrder := ckpt.replacementOrder
    castingFromTop := ckpt.castingFromTop
    delayedTriggers := ckpt.delayedTriggers
    extraTurns := ckpt.extraTurns
    additionalCombatPhases := ckpt.additionalCombatPhases
    events := g.events.extract 0 (min ckpt.eventsSize g.events.size)
    suppressInteractiveReplay := continuationsHaveSuppressedReplay ckpt.continuations }

/-- Players who have left the game since `ckpt` was captured (`pl.leftTheGame` now,
not at `ckpt`), deduplicated and merged with `extra` (CR 734.1 / 800.4a). -/
def playersDepartedSinceCheckpoint (g : Game) (ckpt : ProposalCheckpoint)
    (extra : Array PlayerId := #[]) : Array PlayerId :=
  let since := g.players.foldl (fun acc pl =>
    if pl.leftTheGame && !ckpt.players.any (fun cpl => cpl.id == pl.id && cpl.leftTheGame) &&
        !acc.contains pl.id then
      acc.push pl.id
    else acc) #[]
  extra.foldl (fun acc p => if acc.contains p then acc else acc.push p) since

/-- Whether `ckpt`'s top continuation frame held a `pendingReplacement` that
remained unconsumed across `ckpt.eventsSize .. g.events.size`, tracking
temporary cost/mana outer-continuation stashes, `outerPendingReplacements`
bundles, and `Leaving.playerLeavesGameCore`'s pre-`leftGame` header / popped
outer bundle (CR 734.1 / 800.4a). -/
def ckptPendingReplacementUntouchedBeforeLeave (g : Game) (ckpt : ProposalCheckpoint)
    (_allDeparted : Array PlayerId)
    (poppedOuter? : Option PendingReplacement := none) : Bool :=
  Id.run do
    let some origCont := (ckpt.continuations.back?.getD {}).pendingReplacement
      | return false
    let origBase := origCont.withoutDeparted
    let slice := g.events.extract (min ckpt.eventsSize g.events.size) g.events.size
    let mut hasRootFrame : Bool := true
    let mut frameDepth : Nat := 0
    let mut poppedOrigInFlight : Bool := false
    let mut proposalActionDepth : Nat := 0
    let mut curHasOrig : Bool := true
    let mut outerStack : Array Bool := #[]
    let mut stashedPreAction : Bool := false
    let mut stashedInProposalAction : Bool := false
    let mut stashedForLeaveHeader : Bool := false
    let mut heldInLeaveBatch? : Option BatchId := none
    for ev in slice do
      match ev with
      | .engine _ (.pushContinuationFrame _) _ =>
        if !hasRootFrame then
          if poppedOrigInFlight then
            hasRootFrame := true
            poppedOrigInFlight := false
          else
            return false
        else
          frameDepth := frameDepth + 1
      | .engine _ .popContinuationFrame _ =>
        if !hasRootFrame then
          return false
        else if frameDepth > 0 then
          frameDepth := frameDepth - 1
        else if poppedOrigInFlight then
          hasRootFrame := false
        else
          return false
      | .engine _ (.beginProposalAction _) _ =>
        if !hasRootFrame then return false
        poppedOrigInFlight := false
        stashedForLeaveHeader := false
        if stashedPreAction then
          stashedInProposalAction := true
          stashedPreAction := false
        proposalActionDepth := proposalActionDepth + 1
      | .engine _ .endProposalAction _ =>
        if !hasRootFrame then return false
        poppedOrigInFlight := false
        stashedForLeaveHeader := false
        stashedPreAction := false
        if proposalActionDepth > 0 then
          proposalActionDepth := proposalActionDepth - 1
          if proposalActionDepth == 0 then
            stashedInProposalAction := false
      | .engine _ (.continuation (.pendingReplacement none)) _ =>
        if !hasRootFrame then return false
        if frameDepth == 0 then
          let hadOrig := curHasOrig
          curHasOrig := false
          if hadOrig then
            if proposalActionDepth > 0 then
              stashedInProposalAction := true
            else
              stashedPreAction := true
            stashedForLeaveHeader := true
      | .engine _ (.continuation (.pendingReplacement (some pr))) _ =>
        if !hasRootFrame then return false
        if frameDepth == 0 then
          poppedOrigInFlight := false
          stashedForLeaveHeader := false
          let has := PendingReplacement.containsModDeparted origBase pr
          curHasOrig := has
          if has then
            stashedPreAction := false
            stashedInProposalAction := false
            heldInLeaveBatch? := none
      | .engine _ (.continuation (.pushOuterPendingReplacement pr)) _ =>
        if !hasRootFrame then return false
        if frameDepth == 0 then
          poppedOrigInFlight := false
          stashedForLeaveHeader := false
          let has := PendingReplacement.containsModDeparted origBase pr
          outerStack := outerStack.push has
          if has then
            heldInLeaveBatch? := none
            stashedPreAction := false
      | .engine _ (.continuation .popOuterPendingReplacement) _ =>
        if !hasRootFrame then return false
        if frameDepth == 0 then
          stashedForLeaveHeader := false
          let poppedHas := outerStack.back?.getD false
          if !outerStack.isEmpty then
            outerStack := outerStack.pop
          if poppedHas then
            poppedOrigInFlight := true
      | .engine _ .saveProposalCheckpoint _ =>
        if !hasRootFrame then return false
        poppedOrigInFlight := false
        stashedForLeaveHeader := false
      | .engine _ (.proposedSpell (some _)) _
      | .engine _ (.afterRandom _) _ =>
        if !hasRootFrame then return false
        poppedOrigInFlight := false
        stashedForLeaveHeader := false
        if proposalActionDepth == 0 then
          stashedPreAction := false
      | .engine _ (.pending p) _ =>
        if !hasRootFrame then return false
        if p != .none then
          poppedOrigInFlight := false
          stashedForLeaveHeader := false
          if proposalActionDepth == 0 then
            stashedPreAction := false
      | .rules _ (.player (.leftGame _)) _ (some bid) =>
        if !hasRootFrame then return false
        poppedOrigInFlight := false
        if stashedForLeaveHeader then
          heldInLeaveBatch? := some bid
          stashedForLeaveHeader := false
        stashedPreAction := false
      | .rules .. =>
        if !hasRootFrame then return false
        poppedOrigInFlight := false
        stashedForLeaveHeader := false
        stashedPreAction := false
      | _ =>
        if !hasRootFrame then return false
    if heldInLeaveBatch?.isSome && g.currentBatch.map Prod.fst != heldInLeaveBatch? then
      heldInLeaveBatch? := none
    return (hasRootFrame && (curHasOrig || stashedInProposalAction || outerStack.any id ||
      heldInLeaveBatch?.isSome)) ||
      (poppedOrigInFlight && poppedOuter?.any (PendingReplacement.containsModDeparted origBase))

@[noinline] private def applyContinuationChange (f : ContinuationFrame)
    (cc : ContinuationChange) : ContinuationFrame :=
  match cc with
  | .pendingDrawAfterScry v => { f with pendingDrawAfterScry := v }
  | .recentTokenIds v => { f with recentTokenIds := v }
  | .pendingFreeCopies v => { f with pendingFreeCopies := v }
  | .pendingMayCastFromExile v => { f with pendingMayCastFromExile := v }
  | .postCastCleanup v => { f with postCastCleanup := v }
  | .surveilReturnMvAtMost v => { f with surveilReturnMvAtMost := v }
  | .pendingReplacement v => { f with pendingReplacement := v }
  | .pushOuterPendingReplacement v => { f with outerPendingReplacements := f.outerPendingReplacements.push v }
  | .popOuterPendingReplacement => { f with outerPendingReplacements := f.outerPendingReplacements.pop }
  | .conniveSource v => { f with conniveSource := v }
  | .thirstDiscardsLeft v => { f with thirstDiscardsLeft := v }
  | .thirstDiscardType v => { f with thirstDiscardType := v }
  | .pendingDiscardsLeft v => { f with pendingDiscardsLeft := v }
  | .discardCountPerPlayer v => { f with discardCountPerPlayer := v }
  | .discardBatch v => { f with discardBatch := v }
  | .stagedAttackTokenBatches v => { f with stagedAttackTokenBatches := v }
  | .stashedCause v => { f with stashedCause := v }
  | .resolvingSpell v => { f with resolvingSpell := v }
  | .resolvingAbility v => { f with resolvingAbility := v }
  | .resolvingDivision v => { f with resolvingDivision := v }
  | .resolvingSkippedSlots v => { f with resolvingSkippedSlots := v }
  | .afterRandom v => { f with afterRandom := v }
  | .resolutionFinish v => { f with resolutionFinish := v }
  | .pendingResolvedEvent v => { f with pendingResolvedEvent := v }
  | .stepEnv v => { f with stepEnv := v }
  | .bindStepOutcome v o =>
    { f with stepEnv := (f.stepEnv.filter (·.1 != v)).push (v, o) }
  | .interpWait? v => { f with interpWait? := v }

/-- Process one `EngineChange` in isolation. -/
def applyEngineChange (g : Game) (c : EngineChange) : Game :=
  match c with
  | .player p pc =>
    if h : p.idx < g.players.size then
      let pl := g.players[p.idx]
      { g with players := g.players.set! p.idx (pl.applyChange pc) }
    else g
  | .addPlayer pl => { g with players := g.players.push pl }
  | .materializeObject obj libPos =>
    let ts : Nat := if obj.timestamp > 0 then obj.timestamp else g.timestamp + 1
    let defaultCtrl : Option PlayerId :=
      if obj.zone == .battlefield then obj.defaultController.orElse (fun _ => obj.controller)
      else none
    let attached : Option ObjectId :=
      if obj.zone == .battlefield then obj.attachedTo else none
    let chosenX : Option Nat :=
      if obj.zone == .stack then obj.chosenX else none
    let fresh : GameObject :=
      { obj with
        timestamp := ts
        defaultController := defaultCtrl
        attachedTo := attached
        chosenX := chosenX }
    let objs :=
      match g.objects.findIdx? (·.id == fresh.id) with
      | some i => g.objects.set! i fresh
      | none => g.objects.push fresh
    let g :=
      { g with
        objects := objs
        nextObjectId := max g.nextObjectId (fresh.id.raw + 1)
        timestamp := max g.timestamp ts }
    g.insertIntoZoneList fresh.id fresh.zone libPos
  | .object id oc =>
    match g.objects.findIdx? (·.id == id) with
    | some i =>
      let o := g.objects[i]!
      { g with objects := g.objects.set! i (o.applyChange oc) }
    | none => g
  | .removeStackEntry oid => { g with stack := g.stack.filter (·.objectId != oid) }
  | .pushStack e => { g with stack := g.stack.push e }
  | .popStack => { g with stack := g.stack.pop }
  | .stackEntry oid sc =>
    match g.stack.findIdx? (·.objectId == oid) with
    | some i =>
      let e := g.stack[i]!
      let e' :=
        match sc with
        | .skipOptionalSlot slot =>
          if e.skippedOptionalSlots.contains slot then e
          else { e with skippedOptionalSlots := e.skippedOptionalSlots.push slot }
        | .targetsAnnounced done => { e with targetsAnnounced := done }
        | .lastKnownPT pw tg =>
          { e with
            lastKnownPower := pw.orElse (fun _ => e.lastKnownPower)
            lastKnownToughness := tg.orElse (fun _ => e.lastKnownToughness) }
        | .clearChosenModes => { e with chosenMode := none, extraModes := #[] }
      { g with stack := g.stack.set! i e' }
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
  | .saveProposalCheckpoint =>
    let outers :=
      match g.proposalCheckpoint with
      | some prev => g.outerProposalCheckpoints.push prev
      | none => g.outerProposalCheckpoints
    { g with
      proposalCheckpoint := some (g.captureProposalCheckpoint (g.events.size - 1))
      outerProposalCheckpoints := outers }
  | .clearProposalCheckpoint =>
    { g with
      proposalCheckpoint := g.outerProposalCheckpoints.back?
      outerProposalCheckpoints := g.outerProposalCheckpoints.pop }
  | .beginProposalAction _ | .endProposalAction => g
  | .pauseBatch batchId cause objs pls effs pend stk =>
    { g with
      currentBatch := some (batchId, cause)
      nextBatchId := max g.nextBatchId (batchId.raw + 1)
      openBatchObjects := objs
      openBatchPlayers := pls
      openBatchEffects := effs
      openBatchPending := pend
      openBatchStack := stk }
  | .setPausedBatchCause cause =>
    match g.currentBatch with
    | some (bid, _) => { g with currentBatch := some (bid, cause) }
    | none => g
  | .clearPausedBatch =>
    { g with
      currentBatch := none
      openBatchObjects := #[]
      openBatchPlayers := #[]
      openBatchEffects := #[]
      openBatchPending := .none
      openBatchStack := #[]
      openBatchSuppressInteractive := false }
  | .pushContinuationFrame frame =>
    let nextConts := g.continuations.push frame
    { g with
      continuations := nextConts
      suppressInteractiveReplay := continuationsHaveSuppressedReplay nextConts }
  | .popContinuationFrame =>
    let nextConts := g.continuations.pop
    { g with
      continuations := nextConts
      suppressInteractiveReplay := continuationsHaveSuppressedReplay nextConts }
  | .continuation cc =>
    let g' := g.modifyTopFrame (applyContinuationChange · cc)
    match cc with
    | .pendingReplacement _ | .pushOuterPendingReplacement _ | .popOuterPendingReplacement =>
      { g' with suppressInteractiveReplay := continuationsHaveSuppressedReplay g'.continuations }
    | _ => g'
  | .priority v => { g with priority := v }
  | .pendingPriority v => { g with pendingPriority := v }
  | .pendingBlockerAssignments v => { g with pendingBlockerAssignments := v }
  | .startingPlayer v => { g with startingPlayer := v, activePlayer := v }
  | .pending v => { g with pending := v }
  | .nextEffectId v => { g with nextEffectId := v }
  | .pregameRandom v => { g with pregameRandom := v }
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
  | .queueLinkedExile ids =>
    if ids.isEmpty then g
    else
      let merged := ids.foldl (fun acc id => if acc.contains id then acc else acc.push id) g.queuedLinkedExile
      { g with queuedLinkedExile := merged }
  | .clearQueuedLinkedExile => { g with queuedLinkedExile := #[] }
  | .replacementOrder ids => { g with replacementOrder := ids }
  | .castingFromTop v => { g with castingFromTop := v }
  | .sbaChecked => g

-- Game-wide rule queries (CR 611.2c / 613.11)

def creaturesWithoutFlyingCantBlock (g : Game) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule .creaturesWithoutFlyingCantBlock d => g.durationActive d
    | _ => false

def powerUpsForbidden (g : Game) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule .powerUpsForbidden d => g.durationActive d
    | _ => false

def assignCombatDamageEqualToughness (g : Game) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule p .assignCombatDamageEqualToughness d =>
      if g.durationActive d then some p else acc
    | _ => acc) none

def playerControl (g : Game) : Option (PlayerId × PlayerId) :=
  g.activeEffects.foldl (fun acc (eid, s) =>
    match s with
    | .playerRule you (.controlsPlayer them onNextTurn) d =>
      let inWindow := !onNextTurn || (g.hasTurnBegunSince eid them && !g.hasTurnAfterBegunSince eid them)
      if g.durationActive d && inWindow then some (you, them) else acc
    | _ => acc) none

def controlOnNextTakenTurn (g : Game) : Array (PlayerId × PlayerId) :=
  g.activeEffects.filterMap fun (eid, s) =>
    match s with
    | .playerRule you (.controlsPlayer them true) d =>
      if g.durationActive d && !g.hasTurnAfterBegunSince eid them then some (you, them) else none
    | _ => none

def pendingFreeRGCreature (g : Game) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule p .pendingFreeRGCreature d =>
      if g.durationActive d then some p else acc
    | _ => acc) none

-- Player-rule queries (CR 611.2c / 613.11)

def additionalLandsThisTurn (g : Game) (p : PlayerId) : Nat :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule q (.additionalLands n) d =>
      if q == p && g.durationActive d then acc + n else acc
    | _ => acc) 0

def protectionFromEverything (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .protectionFromEverything d
    | .playerRule q (.protectionFrom .everything _ _) d => q == p && g.durationActive d
    | _ => false

def cantCastSpellsThisTurn (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .cantCastSpells d => q == p && g.durationActive d
    | _ => false

def lifeLocked (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .lifeLocked d =>
      (q == p || g.areTeammates q p) && g.durationActive d
    | _ => false

def lifeCantChange (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .lifeCantChange d =>
      (q == p || g.areTeammates q p) && g.durationActive d
    | _ => false

def typeSpellCostLessThisTurn (g : Game) (p : PlayerId) : Array (CardType × Nat) :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .playerRule q (.typeSpellCostLess t n) d =>
      if q == p && g.durationActive d then some (t, n) else none
    | _ => none

def supertypeSpellCostLessThisTurn (g : Game) (p : PlayerId) : Array (Supertype × Nat) :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .playerRule q (.supertypeSpellCostLess st n) d =>
      if q == p && g.durationActive d then some (st, n) else none
    | _ => none

def jaceLoyaltyAtInstantSpeed (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .jaceLoyaltyAtInstantSpeed d => q == p && g.durationActive d
    | _ => false

def legendRuleOffThisTurn (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .legendRuleOff d => q == p && g.durationActive d
    | _ => false

def mountainExtraRedThisTurn (g : Game) (p : PlayerId) : Nat :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .playerRule q (.mountainExtraRed n) d =>
      if q == p && g.durationActive d then acc + n else acc
    | _ => acc) 0

/-- Active `.mountainExtraRed` delayed triggered mana entries for `p` paired
with the resolving source `ObjectId` that created each effect (CR 106.12b / 603.7). -/
def mountainExtraRedEntriesThisTurn (g : Game) (p : PlayerId) : Array (Nat × Option ObjectId) :=
  g.activeEffects.foldl (fun acc (eid, s) =>
    match s with
    | .playerRule q (.mountainExtraRed n) d =>
      if q == p && g.durationActive d && n > 0 then
        let src? := (g.effectCreatedInfo? eid).bind (fun (_, c) => c.oneShotSourceId?)
        acc.push (n, src?)
      else acc
    | _ => acc) #[]

def nextSpellCantBeCountered (g : Game) (p : PlayerId) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q .nextSpellCantBeCountered d => q == p && g.durationActive d
    | _ => false

-- Object / status rule and permission queries (CR 611.2 / 613)

private def playerStillInGameAt (g : Game) (p : PlayerId) (evIdx : Nat) : Bool := Id.run do
  let hasAddPlayer :=
    g.events.any fun e =>
      match e.change with
      | .engine (.addPlayer pl) => pl.id == p
      | _ => false
  let hasDepartureInLog :=
    g.events.any fun e =>
      match e.change with
      | .rules (.player (.lost q _)) | .rules (.player (.leftGame q)) => q == p
      | _ => false
  let mut alive : Bool :=
    if hasAddPlayer then false
    else
      match g.players[p.idx]? with
      | some pl => (!pl.lost && !pl.leftTheGame) || hasDepartureInLog
      | none => false
  let bound := min evIdx g.events.size
  for i in [0:bound] do
    match g.events[i]!.change with
    | .engine (.addPlayer pl) =>
      if pl.id == p then
        alive := !pl.lost && !pl.leftTheGame
    | .rules (.player (.lost q _)) | .rules (.player (.leftGame q)) =>
      if q == p then
        alive := false
    | _ => pure ()
  return alive

def playPermissionEntriesOf (g : Game) (id : ObjectId) :
    Array (EffectId × PlayerId × PlayPermission × EffectDuration) :=
  let active :=
    g.activeEffects.foldl (fun acc (eid, s) =>
      match s with
      | .permission p (.playFromExile oid perm) d =>
        let grantee := p.getD perm.player
        if oid == id && g.durationActive d &&
            (perm.prepareSource.isSome || g.stillInGame grantee) then
          acc.push (eid, grantee, { perm with player := grantee }, d)
        else acc
      | _ => acc) #[]
  if !active.isEmpty then active
  else
    let targetId? : Option ObjectId :=
      match g.findObject? id with
      | some o =>
        if o.zone == .stack then
          Id.run do
            let mut i := g.events.size
            while i > 0 do
              i := i - 1
              match g.events[i]!.change with
              | .rules (.zone (.moved before after .exile .stack ..)) =>
                if after.id == some id then
                  return before.id
              | _ => pure ()
            return none
        else none
      | none =>
        Id.run do
          let mut i := g.events.size
          while i > 0 do
            i := i - 1
            match g.events[i]!.change with
            | .rules (.zone (.moved before after .exile .stack ..)) =>
              if after.id == some id then
                return before.id
              if before.id == some id then
                return some id
            | _ => pure ()
          return some id
    match targetId? with
    | none => #[]
    | some targetId =>
      let depIdx? : Option Nat := Id.run do
        let mut i := g.events.size
        while i > 0 do
          i := i - 1
          match g.events[i]!.change with
          | .rules (.zone (.moved before _ .exile ..)) =>
            if before.id == some targetId then
              return some i
          | .rules (.zone (.ceasedToExist eo)) =>
            if eo.id == some targetId then
              return some i
          | _ => pure ()
        return none
      match depIdx? with
      | none => #[]
      | some depIdx =>
        let preLogEffs : Array (EffectId × ContinuousEffectSpec) := Id.run do
          let mut createdEids : Array EffectId := #[]
          let mut init : Array (EffectId × ContinuousEffectSpec) := #[]
          for ev in g.events do
            match ev.change with
            | .rules (.continuousEffect (.created eid _)) =>
              if !createdEids.contains eid then createdEids := createdEids.push eid
            | .rules (.continuousEffect (.expired eid (some sp))) =>
              if !createdEids.contains eid && !init.any (·.1 == eid) then
                init := init.push (eid, sp)
            | _ => pure ()
          for (eid, sp) in g.activeEffects do
            if !createdEids.contains eid && !init.any (·.1 == eid) then
              init := init.push (eid, sp)
          return init
        let effsAtDep : Array (EffectId × ContinuousEffectSpec) :=
          (g.events.extract 0 depIdx).foldl (fun acc ev =>
            match ev.change with
            | .rules (.continuousEffect (.created eid sp)) =>
              (acc.filter (·.1 != eid)).push (eid, sp)
            | .rules (.continuousEffect (.expired eid _)) =>
              acc.filter (·.1 != eid)
            | _ => acc) preLogEffs
        effsAtDep.foldl (fun acc (eid, sp) =>
          match sp with
          | .permission p (.playFromExile oid perm) d =>
            let grantee := p.getD perm.player
            if oid == targetId &&
                g.durationActiveAt d depIdx &&
                (perm.prepareSource.isSome || playerStillInGameAt g grantee depIdx) then
              acc.push (eid, grantee, { perm with player := grantee }, d)
            else acc
          | _ => acc) #[]

def playPermissionEntryOf? (g : Game) (id : ObjectId) :
    Option (EffectId × PlayerId × PlayPermission × EffectDuration) :=
  (g.playPermissionEntriesOf id).back?

def playPermissionOf? (g : Game) (o : GameObject) : Option PlayPermission :=
  (g.playPermissionEntryOf? o.id).map fun (_, _, perm, _) => perm

@[inline] def playPermission (g : Game) (o : GameObject) : Option PlayPermission :=
  g.playPermissionOf? o

def playPermissionDuration (g : Game) (o : GameObject) : Option EffectDuration :=
  (g.playPermissionEntryOf? o.id).map fun (_, _, _, d) => d

/-- The copy of `srcId`'s prepare spell in exile, if any. -/
def preparedCopyOf? (g : Game) (srcId : ObjectId) : Option GameObject :=
  g.objects.find? (fun o =>
    o.zone == .exile &&
      (g.playPermissionEntriesOf o.id).any (fun (_, _, perm, _) => perm.prepareSource == some srcId))

def flashbackUntilEot (g : Game) (o : GameObject) : Bool :=
  let originId := GameEvent.castOriginIdOf g.events o.id
  g.activeEffects.any fun (_, s) =>
    match s with
    | .permission _ (.flashback id) d =>
      g.durationActive d && (id == o.id || id == originId)
    | _ => false

/-- Whether `o` (or the graveyard card it was cast from, CR 400.7) has a flashback
permission whose duration is still active (CR 611.2a / 702.34a). Once the card moves
onto the stack its graveyard permission expires on leaving the zone (CR 400.7), so the
fallback reads the creating event — but only while `g.durationActive d` holds and the
effect did not expire for any other reason (such as an earlier turn's cleanup, CR
514.2), so a stale "until end of turn" grant from a previous turn never matches. -/
def hasFlashbackPermission (g : Game) (o : GameObject) : Bool :=
  if g.flashbackUntilEot o then true
  else
    let originId := GameEvent.castOriginIdOf g.events o.id
    if originId == o.id && (g.findObject? o.id).isSome then false
    else
      let expiredOtherwise (eid : EffectId) : Bool :=
        g.events.any fun x =>
          match x.change, x.cause? with
          | .rules (.continuousEffect (.expired ..)), some (.gameRule .leavingZone) => false
          | .rules (.continuousEffect (.expired xid _)), _ => xid == eid
          | _, _ => false
      g.events.any fun e =>
        match e.change with
        | .rules (.continuousEffect (.created eid (.permission _ (.flashback id) d))) =>
          (id == originId || id == o.id) && g.durationActive d && !expiredOtherwise eid
        | _ => false

/-- Whether spell `o` was actually cast via Flashback (CR 702.34a / 601.2b,f): proposed
for its flashback cost (`GameEvent.castWithFlashback`, `CastWay.alternative "flashback"`)
or carrying the active flashback permission `castSpell` re-creates on the stack spell
itself. A graveyard cast through any other permission — *Bilbo, Thief in the Night*'s
`ResolutionChoice.mayCastFromGraveyard` (`CastWay.normal`), a free-cast permission — is not a
Flashback cast even when the card has (or was granted) flashback, so neither the
flashback cost nor the "exile instead" replacement applies to it. Copies are never
cast via Flashback (CR 707.10). -/
def castViaFlashback (g : Game) (o : GameObject) : Bool :=
  !o.isCopy &&
    (GameEvent.castWithFlashback g.events o.id ||
      (o.zone == .stack &&
        g.activeEffects.any fun (_, s) =>
          match s with
          | .permission _ (.flashback id) d => id == o.id && g.durationActive d
          | _ => false))

def colorlessGrantUntilCast (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .permission _ (.colorlessGrant landId cardId) d =>
      if landId == o.id && g.durationActive d then some cardId else none
    | _ => none

def uncounterableThisCast (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule (.uncounterable id) d => id == o.id && g.durationActive d
    | _ => false

def exileInstantSorceryInstead (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .replacement r d =>
      g.durationActive d && r.id.kind == .exileInstantSorceryInstead && r.id.object == some o.id
    | _ => false

def untilEotExileIfDies (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .replacement r d =>
      g.durationActive d && r.id.kind == .untilEotExileIfDies && r.id.object == some o.id
    | _ => false

def preventDamageGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .prevention p d =>
      match d with
      | .whileSourceOnBattlefield src =>
        if !g.durationActive d then none
        else
          match p.kind with
          | .preventAllDamageFromSource id => if id == o.id then some src else none
          | _ => none
      | _ => none
    | _ => none

def cantUntapGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .gameRule (.cantUntap id src) d =>
      match d with
      | .whileSourceOnBattlefield _ =>
        if id == o.id && g.durationActive d then some src else none
      | _ => none
    | _ => none

def cantTransform (_g : Game) (o : GameObject) : Bool :=
  o.status.transformed

def cantBlockUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule (.cantBlock id) d => id == o.id && g.durationActive d
    | _ => false

def cantBeBlockedByPlayer (g : Game) (o : GameObject) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .gameRule (.cantBeBlockedByPlayer id p) d =>
      if id == o.id && g.durationActive d then some p else acc
    | _ => acc) none

def cantBeBlockedExceptByHasteUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .gameRule (.cantBeBlockedExceptByHaste id) d => id == o.id && g.durationActive d
    | _ => false

def hexproofGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities add _) d =>
      match d with
      | .whileSourceOnBattlefield src =>
        if id == o.id && KeywordAbility.hasHexproof add.keywords && g.durationActive d then some src else none
      | _ => none
    | _ => none

def losesAbilitiesUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities _ .all) .untilEndOfTurn => id == o.id
    | _ => false

def losesAbilitiesGrantedBy (g : Game) (o : GameObject) : Array ObjectId :=
  g.activeEffects.filterMap fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.abilities _ .all) d =>
      match d with
      | .whileSourceOnBattlefield src =>
        if id == o.id && g.durationActive d then some src else none
      | _ => none
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
    | .layered (.objects #[id]) (.abilities add _) d =>
      id == o.id && add.firstStrikeOnYourTurn && g.durationActive d
    | _ => false

def onlyFoodArtifact (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .set ts subs _ _ _ _) d =>
      id == o.id && ts == #[.artifact] && subs == #[.food] && g.durationActive d
    | _ => false

def returnedAsArtifact (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .add ts _ _ remTs _ _) d =>
      id == o.id && ts.contains .artifact && remTs.contains .creature && g.durationActive d
    | _ => false

def notACreature (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .add ts _ _ remTs _ _) d =>
      id == o.id && ts.isEmpty && remTs.contains .creature && g.durationActive d
    | _ => false

def additionalArtifactUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .add ts _ _ _ _ _) .untilEndOfTurn =>
      id == o.id && ts.contains .artifact
    | _ => false

def additionalCreature (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.types .add ts _ _ _ _ _) .indefinite =>
      id == o.id && ts.contains .creature
    | _ => false

def pumpPerArtifactUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.ptCda .pumpPerArtifact) d =>
      id == o.id && g.durationActive d
    | _ => false

def cardsInHandPowerUntilEot (g : Game) (o : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.objects #[id]) (.ptCda .cardsInHandPower) d =>
      id == o.id && g.durationActive d
    | _ => false

def commandEffectUntilTurnOf (g : Game) (o : GameObject) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (_, s) =>
    match s with
    | .gameRule (.commandEmblem id) (.untilNextTurnOf p) => if id == o.id then some p else acc
    | _ => acc) none

def controlUntilEot (g : Game) (o : GameObject) : Bool :=
  let applied := g.appliedControlEffectIds o
  g.activeEffects.any fun (eid, s) =>
    match s with
    | .layered (.objects ids) (.control _) .untilEndOfTurn => ids.contains o.id
    | .layered _ (.control _) .untilEndOfTurn => applied.contains eid
    | _ => false

def controlTurnEndsLeft (g : Game) (o : GameObject) : Nat :=
  let applied := g.appliedControlEffectIds o
  g.activeEffects.foldl (fun acc (eid, s) =>
    let hits :=
      match s with
      | .layered (.objects ids) (.control _) d => ids.contains o.id && g.durationActive d
      | .layered _ (.control _) d => applied.contains eid && g.durationActive d
      | _ => false
    if !hits then acc
    else
      match s with
      | .layered _ (.control _) (.untilNextTurnOf _) => max acc 1
      | .layered _ (.control _) (.untilEndOfNextTurnOf p) =>
        let rem := if g.hasTurnBegunSince eid p then 1 else 2
        max acc rem
      | _ => acc) 0

def controlUntilSourceLeaves (g : Game) (o : GameObject) : Option ObjectId :=
  let applied := g.appliedControlEffectIds o
  g.activeEffects.foldl (fun acc (eid, s) =>
    match s with
    | .layered (.objects ids) (.control _) d =>
      match d with
      | .whileSourceOnBattlefield src | .untilSourceLeaves src | .whileSourceHasCounter src _ =>
        if g.durationActive d && ids.contains o.id then some src else acc
      | _ => acc
    | .layered _ (.control _) d =>
      match d with
      | .whileSourceOnBattlefield src | .untilSourceLeaves src | .whileSourceHasCounter src _ =>
        if g.durationActive d && applied.contains eid then some src else acc
      | _ => acc
    | _ => acc) none

/-- Whether `o` currently has an active Layer 1 copy effect (CR 613.1a / 707). -/
def hasActiveCopy (g : Game) (o : GameObject) : Bool :=
  if o.isLkiSnapshot then false
  else
    g.activeEffects.any fun (_, s) =>
      match s with
      | .layered sc (.copy _) d =>
        g.durationActive d &&
          match sc with
          | .objects ids => ids.contains o.id
          | _ => (g.unmaskedCopiableValuesWithTs o).1 != o.printed
      | _ => false

def copyRestore (g : Game) (o : GameObject) : Option CardDef :=
  if o.isLkiSnapshot then none
  else if g.hasActiveCopy o then some o.printed else none

def copyUntilEot (g : Game) (o : GameObject) : Bool :=
  if o.isLkiSnapshot then false
  else
    g.activeEffects.any fun (_, s) =>
      match s with
      | .layered (.objects #[id]) (.copy _) .untilEndOfTurn => id == o.id
      | _ => false

def copyUntilNextTurn (g : Game) (o : GameObject) : Bool :=
  if o.isLkiSnapshot then false
  else
    g.activeEffects.any fun (_, s) =>
      match s with
      | .layered (.objects #[id]) (.copy _) (.untilNextTurnOf _) => id == o.id
      | _ => false

def copyUntilSourceLeaves (g : Game) (o : GameObject) : Option ObjectId :=
  if o.isLkiSnapshot then none
  else
    g.activeEffects.foldl (fun acc (_, s) =>
      match s with
      | .layered (.objects #[id]) (.copy _) d =>
        match d with
        | .untilSourceLeaves src | .whileSourceOnBattlefield src | .whileSourceHasCounter src _ =>
          if id == o.id && g.durationActive d then some src else acc
        | _ => acc
      | _ => acc) none

-- Layer 3: Text-changing effects (CR 612 / 613.1c / 613.7 / 613.8)

private structure Layer3Entry where
  idx : Nat
  ts : Nat × Nat
  scope : ObjectScope
  tc : TextChange
deriving Inhabited

/-- Apply Layer 3 text changes to a `StaticAbility` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applyStaticAbility (tcs : Array TextChange) (ab : StaticAbility) : StaticAbility :=
  HasTextChange.applyTextChanges tcs ab

/-- Apply Layer 3 text changes to a `TriggerPattern` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applyTriggerPattern (tcs : Array TextChange) (p : TriggerPattern) : TriggerPattern :=
  HasTextChange.applyTextChanges tcs p

/-- Apply Layer 3 text changes to a `TargetSpec` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applyTargetSpec (tcs : Array TextChange) (ts : TargetSpec) : TargetSpec :=
  HasTextChange.applyTextChanges tcs ts

/-- Apply Layer 3 text changes to a one-shot `Effect` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applyEffect (tcs : Array TextChange) (e : Effect) : Effect :=
  HasTextChange.applyTextChanges tcs e

/-- Apply Layer 3 text changes to an `ActivatedAbility` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applyActivatedAbility (tcs : Array TextChange) (ab : ActivatedAbility) : ActivatedAbility :=
  HasTextChange.applyTextChanges tcs ab

/-- Apply Layer 3 text changes to a `TriggeredAbility` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applyTriggeredAbility (tcs : Array TextChange) (ab : TriggeredAbility) : TriggeredAbility :=
  HasTextChange.applyTextChanges tcs ab

/-- Evaluate Layer 3 text-changing effects on `o` across every `ObjectScope` in
CR 613.7 timestamp and CR 613.8 dependency order (CR 612 / 613.1c). -/
def evalLayer3 (g : Game) (o : GameObject) : Array TextChange :=
  if o.isLkiSnapshot || isFaceDownMasked o then #[]
  else
    let hasText := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.text _) _ => true
      | _ => false
    if !hasText then #[]
    else
      let bc := g.baseCard o
      let baseSubs := CardSubtype.ofSubtypes bc.subtypes
      let isCreaOrKind := bc.types.contains .creature || bc.types.contains .kindred
      let scopeMatchesL3 (cur : Array TextChange) (sc : ObjectScope) : Bool :=
        match sc with
        | .objects ids => ids.contains o.id
        | .creaturesControlledBy p =>
          o.isOnBattlefield && g.controlledBy o p && bc.types.contains .creature
        | .creaturesWithout kw =>
          o.isOnBattlefield && bc.types.contains .creature &&
            kw.any (fun k => !bc.keywords.contains k)
        | .permanentsOfSubtype p s =>
          o.isOnBattlefield && g.controlledBy o p &&
            ((baseSubs.map (TextChange.applySubtype cur)).contains s ||
              (bc.hasSimpleKeyword .changeling && isCreaOrKind && !s.isNoncreature))
      Id.run do
        let mut cands : Array (EffectId × Nat × ObjectScope × TextChange) := #[]
        for pos in [0:g.activeEffects.size] do
          let (eid, s) := g.activeEffects[pos]!
          match s with
          | .layered sc (.text tc) d =>
            if g.durationActive d && g.effectPhasingAllows o eid sc d then
              cands := cands.push (eid, pos, sc, tc)
          | _ => pure ()
        if cands.isEmpty then return #[]
        let needTs := cands.size >= 2
        let mut raw : Array Layer3Entry := #[]
        for (eid, pos, sc, tc) in cands do
          raw := raw.push {
            idx := raw.size
            ts := if needTs then g.effectTimestamp eid pos else (0, 0)
            scope := sc
            tc := tc
          }
        let sorted :=
          if !needTs then raw
          else raw.qsort fun a b =>
            if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
            else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
            else a.idx < b.idx
        let mut rem := sorted
        let mut cur : Array TextChange := #[]
        for _ in [0:sorted.size] do
          let applicable := rem.filter (fun e => scopeMatchesL3 cur e.scope)
          if applicable.isEmpty then break
          let dependsOn (a b : Layer3Entry) : Bool :=
            a.idx != b.idx &&
              scopeMatchesL3 cur a.scope != scopeMatchesL3 (cur.push b.tc) a.scope
          let chosen :=
            (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
          cur := cur.push chosen.tc
          rem := rem.filter (fun e => e.idx != chosen.idx)
        return cur

/-- Apply Layer 3 text changes to an `AdditionalCostSpec` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applyAdditionalCost (tcs : Array TextChange)
    (ac : AdditionalCostSpec) : AdditionalCostSpec :=
  HasTextChange.applyTextChanges tcs ac

/-- Apply Layer 3 text changes to a `SpellAbility` (CR 612.2 / 613.1c). -/
@[inline] def TextChange.applySpellAbility (tcs : Array TextChange)
    (sa : SpellAbility) : SpellAbility :=
  HasTextChange.applyTextChanges tcs sa

/-- Additional casting costs on `face` after Layer 3 text-changing effects on `o`
(CR 118.8 / 612 / 613.1c). -/
def additionalCostsFor (g : Game) (o : GameObject) (face : CardDef) :
    Array AdditionalCostSpec :=
  let tcs := g.evalLayer3 o
  if tcs.isEmpty then face.additionalCosts
  else HasTextChange.applyTextChanges tcs face.additionalCosts

/-- Additional casting costs on `face` after Layer 3 text-changing effects on
`id` when present (CR 118.8 / 612 / 613.1c). -/
def additionalCostsForId (g : Game) (id : ObjectId) (face : CardDef) :
    Array AdditionalCostSpec :=
  match g.findObject? id with
  | some o => g.additionalCostsFor o face
  | none => face.additionalCosts

/-- Mandatory non-choice single-object sacrifice additional-cost predicate on
`face` after Layer 3 text changes on `o` (CR 118.8 / 612 / 613.1c). -/
def mandatorySacrificeFilterFor? (g : Game) (o : GameObject) (face : CardDef) :
    Option ObjectPred :=
  (g.additionalCostsFor o face).findSome? fun a =>
    if a.optional then none
    else a.cost.items.findSome? fun
      | .sacrifice _ (.filter pred) => some pred
      | _ => none

/-- `mandatorySacrificeFilterFor?` keyed by `ObjectId` (CR 118.8 / 612 / 613.1c). -/
def mandatorySacrificeFilterForId? (g : Game) (id : ObjectId) (face : CardDef) :
    Option ObjectPred :=
  (g.additionalCostsForId id face).findSome? fun a =>
    if a.optional then none
    else a.cost.items.findSome? fun
      | .sacrifice _ (.filter pred) => some pred
      | _ => none

/-- Mandatory choice additional-cost branches (`"A or B"`) on `face` after
Layer 3 text changes on `o` (CR 118.8 / 601.2b / 612 / 613.1c). -/
def additionalChoiceCostFor? (g : Game) (o : GameObject) (face : CardDef) :
    Option (Array CostSpec) :=
  (g.additionalCostsFor o face).findSome? fun a =>
    if a.optional then none
    else a.cost.items.findSome? fun
      | .or choices => some choices
      | _ => none

/-- Object predicate for a spell's additional-cost sacrifice (mandatory or chosen
from an `"or pay {N}"` additional cost) after Layer 3 text changes on `o`
(CR 118.8 / 601.2b,h / 612 / 613.1c). -/
def spellSacrificeCostPredFor? (g : Game) (o : GameObject) (face : CardDef) :
    Option ObjectPred :=
  (g.mandatorySacrificeFilterFor? o face).orElse fun _ =>
    (g.additionalChoiceCostFor? o face).bind fun branches =>
      branches.findSome? fun cs =>
        cs.items.findSome? fun
          | .sacrifice _ (.filter pred) => some pred
          | _ => none

@[extern "mtg_game_gy_creature_cards"]
private opaque gyCreatureCardsFwd (g : Game) (p : PlayerId) : Nat

-- Layer 4: Type-changing effects (CR 613.1d / 205.3d / 613.3 / 613.7 / 613.8 / 702.73a)

private inductive L4TsSource where
  | base
  | attach (att : GameObject)
  | eff (eid : EffectId) (pos : Nat)
deriving Inhabited

private structure Layer4Entry where
  idx : Nat
  ts : Nat × Nat
  scope : ObjectScope
  mod : TypeSetMod
deriving Inhabited

/-- Extended Layer 4 evaluation result: `(types, subtypes, supertypes)` plus
whether a CR 305.7 subtype-setting effect set a basic land type on this land
(which strips printed rules text before Layer 6). -/
structure Layer4Result where
  types : Array CardType
  subtypes : Array CardSubtype
  supertypes : Array Supertype
  strippedRulesTextByBasicLandSet : Bool := false
deriving Inhabited

private def typeModIsBasicLandSet (tm : TypeSetMod) : Bool :=
  tm.mode == .set &&
    let landSubs := tm.subtypes.filter (fun sub => sub.kind == .land && !tm.removeSubtypes.contains sub)
    !landSubs.isEmpty && landSubs.all CardSubtype.isBasicLandType

private partial def modAnyLeaf (pred : ContinuousModification → Bool) :
    ContinuousModification → Bool
  | .all ms => ms.any (modAnyLeaf pred)
  | m => pred m

private def staticIsBasicLandSet : Nat → StaticAbility → Bool
  | 0, _ => false
  | fuel + 1, .continuous _ _ mod =>
    modAnyLeaf (fun
      | .modifyTypes tm => typeModIsBasicLandSet tm
      | .grantStatic sas => sas.any (staticIsBasicLandSet fuel)
      | _ => false) mod
  | _, _ => false

/-- Whether any active Layer 4 continuous effect or battlefield/emblem static
ability sets a land's subtype exclusively to one or more basic land types
(CR 305.7, e.g. Blood Moon / Harbinger of the Seas / Spreading Seas / Song of the Dryads). -/
def hasActiveBasicLandSetEffect (g : Game) : Bool :=
  let hasCopy := g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.copy _) _ => true
    | _ => false
  g.activeEffects.any (fun (_, s) =>
    match s with
    | .layered _ (.types .set _ subs _ _ remSubs _) d =>
      let landSubs := subs.filter (fun sub => sub.kind == .land && !remSubs.contains sub)
      g.durationActive d && !landSubs.isEmpty && landSubs.all CardSubtype.isBasicLandType
    | .layered _ (.abilities add _) d =>
      g.durationActive d && add.staticAbilities.any (staticIsBasicLandSet 3)
    | _ => false) ||
  g.objects.any fun src =>
    (src.isOnBattlefield && !src.status.faceDown &&
      let bc := if hasCopy then g.baseCard src else src.printed
      !bc.staticAbilities.isEmpty && bc.staticAbilities.any (staticIsBasicLandSet 3)) ||
    (src.zone == .command && !src.printed.staticAbilities.isEmpty &&
      (if hasCopy then g.baseCard src else src.printed).types.isEmpty &&
      src.printed.staticAbilities.any (staticIsBasicLandSet 3))

/-- Unified Layer 4 evaluation of `(types, subtypes, supertypes)` plus CR 305.7
basic-land-type stripping on `o` in CR 613.7 timestamp order with CR 613.8
dependency ordering, applying changeling first per CR 613.3 / 702.73a and
enforcing CR 205.3d subtype correlation. -/
def evalLayer4Full (g : Game) (o : GameObject) : Layer4Result :=
  let pushDedup {α : Type} [BEq α] (acc elems : Array α) : Array α :=
    elems.foldl (fun a x => if a.contains x then a else a.push x) acc
  if o.isLkiSnapshot then
    let bc := o.printed
    { types := bc.types, subtypes := CardSubtype.ofSubtypes bc.subtypes, supertypes := bc.supertypes }
  else if !o.isOnBattlefield then
    let bc := g.baseCard o
    let tcs := g.evalLayer3 o
    let rawSubs := CardSubtype.ofSubtypes bc.subtypes
    let baseSubs := if tcs.isEmpty then rawSubs else rawSubs.map (TextChange.applySubtype tcs)
    let mappedOwnL4 :=
      if isFaceDownMasked o || bc.staticAbilities.isEmpty then #[]
      else if tcs.isEmpty then bc.staticAbilities
      else bc.staticAbilities.map (TextChange.applyStaticAbility tcs)
    let (initTypes, initSubs0, initSups) :=
      mappedOwnL4.foldl (fun (ts, subs, sups) ab =>
        match ab with
        | .characteristicDefining (.setTypes tm) => tm.apply ts subs sups
        | _ => (ts, subs, sups)) (bc.types, baseSubs, bc.supertypes)
    let hasAllCreatureTypesCda :=
      !isFaceDownMasked o &&
        (bc.hasSimpleKeyword .changeling ||
          mappedOwnL4.any (fun | .characteristicDefining .allCreatureTypes => true | _ => false))
    let subs0 :=
      if hasAllCreatureTypesCda && (initTypes.contains .creature || initTypes.contains .kindred) then
        pushDedup initSubs0 CardSubtype.allCreatureSubtypes
      else initSubs0
    let subs :=
      if initTypes.contains .creature || initTypes.contains .kindred then subs0
      else subs0.filter CardSubtype.isNoncreature
    { types := initTypes, subtypes := subs, supertypes := initSups }
  else
    let bc := g.baseCard o
    let oTcs := g.evalLayer3 o
    let effectiveSubs (ts : Array CardType) (subs : Array CardSubtype) : Array CardSubtype :=
      if ts.contains .creature || ts.contains .kindred then subs
      else subs.filter CardSubtype.isNoncreature
    let initTypes0 :=
      if o.status.faceDown || bc.hasProtectionFromChosenCardType then bc.types
      else
        match o.status.chosenCardType with
        | some t => if bc.types.contains t then bc.types else bc.types.push t
        | none => bc.types
    let rawSubs := CardSubtype.ofSubtypes bc.subtypes
    let textSubs := if oTcs.isEmpty then rawSubs else rawSubs.map (TextChange.applySubtype oTcs)
    let mappedOwnL4 :=
      if o.status.faceDown || bc.staticAbilities.isEmpty then #[]
      else if oTcs.isEmpty then bc.staticAbilities
      else bc.staticAbilities.map (TextChange.applyStaticAbility oTcs)
    -- CR 613.3 / 702.73a: Changeling and type/subtype CDAs apply first in Layer 4 before non-CDA effects.
    let (initTypes, initSubs0, initSups) :=
      mappedOwnL4.foldl (fun (ts, subs, sups) ab =>
        match ab with
        | .characteristicDefining (.setTypes tm) => tm.apply ts subs sups
        | _ => (ts, subs, sups)) (initTypes0, textSubs, bc.supertypes)
    let hasAllCreatureTypesCda :=
      bc.hasSimpleKeyword .changeling ||
        mappedOwnL4.any (fun | .characteristicDefining .allCreatureTypes => true | _ => false)
    let initSubs :=
      if hasAllCreatureTypesCda && (initTypes.contains .creature || initTypes.contains .kindred) then
        pushDedup initSubs0 CardSubtype.allCreatureSubtypes
      else initSubs0
    Id.run do
      let mut pending : Array (L4TsSource × Layer4Entry) := #[]
      -- 1. Attached Aura static type/subtype/supertype effects at CR 613.7a / 613.7e timestamp.
      for att in g.objects do
        if att.isOnBattlefield && att.attachedTo == some o.id && !att.status.faceDown then
          let attBc := g.baseCard att
          if !attBc.staticAbilities.isEmpty then
            let attTcs := g.evalLayer3 att
            for ab0 in attBc.staticAbilities do
              let ab := TextChange.applyStaticAbility attTcs ab0
              match ab with
              | .continuous none sc mod =>
                if StaticAbility.isAttachedHostScope sc then
                  for m in mod.flatten do
                    match m with
                    | .modifyTypes tm =>
                      pending := pending.push (.attach att, {
                        idx := pending.size, ts := (0, 0), scope := .objects #[o.id]
                        mod := tm
                      })
                    | .addAllCreatureTypes =>
                      pending := pending.push (.attach att, {
                        idx := pending.size, ts := (0, 0), scope := .objects #[o.id]
                        mod := { mode := .addDedup, subtypes := CardSubtype.allCreatureSubtypes }
                      })
                    | _ => pure ()
              | _ => pure ()
      -- 2. Conditional self subtype/type statics (e.g. Undercover Skrull `getsAndAllTypesIfGyCreatureCards`).
      if !mappedOwnL4.isEmpty then
        for ab in mappedOwnL4 do
          match ab with
          | .continuous cond? sc mod =>
            if StaticAbility.isScopeSelf sc then
              let condOk : Bool :=
                match cond? with
                | none => true
                | some (.cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature]))) (.const min))
                | some (.cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.hasType .creature, .isCard]))) (.const min)) =>
                  match g.controllerOf o with
                  | some p => decide (gyCreatureCardsFwd g p >= min.toNat)
                  | none => false
                | some .isYourTurn => (g.controllerOf o).any g.isOnActiveTeam
                | some .isNight => g.isNight
                | _ => false
              if condOk then
                for m in mod.flatten do
                  match m with
                  | .modifyTypes tm =>
                    pending := pending.push (.base, {
                      idx := pending.size, ts := (0, 0), scope := .objects #[o.id]
                      mod := tm
                    })
                  | .addAllCreatureTypes =>
                    pending := pending.push (.base, {
                      idx := pending.size, ts := (0, 0), scope := .objects #[o.id]
                      mod := { mode := .addDedup, subtypes := CardSubtype.allCreatureSubtypes }
                    })
                  | _ => pure ()
          | _ => pure ()
      -- 3. Active `.layered sc (.types ...)` continuous effects.
      for pos in [0:g.activeEffects.size] do
        let (eid, s) := g.activeEffects[pos]!
        match s with
        | .layered sc (.types mode ts subs sups remTs remSubs remSups) d =>
          if g.durationActive d && g.effectPhasingAllows o eid sc d then
            pending := pending.push (.eff eid pos, {
              idx := pending.size, ts := (0, 0), scope := sc
              mod := {
                mode := mode, types := ts, subtypes := subs, supertypes := sups
                removeTypes := remTs, removeSubtypes := remSubs, removeSupertypes := remSups
              }
            })
        | _ => pure ()
      if pending.isEmpty then
        return { types := initTypes, subtypes := effectiveSubs initTypes initSubs, supertypes := initSups }
      let scopeMatchesL4 (cur : Array CardType × Array CardSubtype × Array Supertype)
          (sc : ObjectScope) : Bool :=
        match sc with
        | .objects ids => ids.contains o.id
        | .creaturesControlledBy p => g.controlledBy o p && cur.1.contains .creature
        | .creaturesWithout kw =>
          cur.1.contains .creature && kw.any (fun k => !bc.keywords.contains k)
        | .permanentsOfSubtype p s =>
          g.controlledBy o p && (effectiveSubs cur.1 cur.2.1).contains s
      let applyStep (cur : Array CardType × Array CardSubtype × Array Supertype)
          (e : Layer4Entry) : Array CardType × Array CardSubtype × Array Supertype :=
        e.mod.apply cur.1 cur.2.1 cur.2.2
      let needTs := pending.size >= 2
      let sorted : Array Layer4Entry :=
        if !needTs then
          pending.map Prod.snd
        else
          let raw := pending.map fun (src, e) =>
            let ts :=
              match src with
              | .base => (g.baseCardWithTs o).2
              | .attach att => maxTs (g.attachmentTimestamp att o.id) (g.baseCardWithTs att).2
              | .eff eid pos => g.effectTimestamp eid pos
            { e with ts := ts }
          raw.qsort fun a b =>
            if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
            else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
            else a.idx < b.idx
      let mut rem := sorted
      let mut cur := (initTypes, initSubs, initSups)
      let mut stripped := false
      for _ in [0:sorted.size] do
        let applicable := rem.filter (fun e => scopeMatchesL4 cur e.scope)
        if applicable.isEmpty then break
        let dependsOn (a b : Layer4Entry) : Bool :=
          a.idx != b.idx &&
            scopeMatchesL4 cur a.scope != scopeMatchesL4 (applyStep cur b) a.scope
        let chosen :=
          (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
        let next := applyStep cur chosen
        -- CR 305.7 / 613.7: Setting a land's subtype exclusively to one or more
        -- basic land types without preserving existing types/abilities strips
        -- printed rules text. Derive this from the latest Layer 4 effect
        -- determining the land subtypes, clearing it if a later effect removes
        -- the land type, overwrites land subtypes with non-basic/mixed subtypes,
        -- or removes all basic land types.
        if !next.1.contains .land then
          stripped := false
        else if chosen.mod.mode == .set && !chosen.mod.subtypes.isEmpty then
          let setLandSubs :=
            chosen.mod.subtypes.filter (fun s =>
              s.kind == .land && !chosen.mod.removeSubtypes.contains s)
          stripped := !setLandSubs.isEmpty && setLandSubs.all CardSubtype.isBasicLandType
        else if stripped && !next.2.1.any CardSubtype.isBasicLandType then
          stripped := false
        cur := next
        rem := rem.filter (fun e => e.idx != chosen.idx)
      return {
        types := cur.1
        subtypes := effectiveSubs cur.1 cur.2.1
        supertypes := cur.2.2
        strippedRulesTextByBasicLandSet := stripped
      }

/-- Unified Layer 4 evaluation of `(types, subtypes, supertypes)` on `o` in
CR 613.7 timestamp order with CR 613.8 dependency ordering, applying changeling
first per CR 613.3 / 702.73a and enforcing CR 205.3d subtype correlation. -/
def evalLayer4 (g : Game) (o : GameObject) : Array CardType × Array CardSubtype × Array Supertype :=
  let r := g.evalLayer4Full o
  (r.types, r.subtypes, r.supertypes)

/-- Evaluated card types of `o` after Layer 4 type-changing effects (CR 613.1d / 604.3). -/
def types (g : Game) (o : GameObject) : Array CardType :=
  if o.isLkiSnapshot then o.printed.types
  else if !o.isOnBattlefield then
    let bc := g.baseCard o
    let hasTypeCda :=
      !isFaceDownMasked o &&
        bc.staticAbilities.any fun
          | .characteristicDefining (.setTypes tm) => !tm.types.isEmpty || !tm.removeTypes.isEmpty
          | _ => false
    if hasTypeCda then (g.evalLayer4 o).1 else bc.types
  else
    let hasTypesEff := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.types ..) d => g.durationActive d
      | _ => false
    if hasTypesEff then (g.evalLayer4 o).1
    else
      let hasStaticEff := g.activeEffects.any fun (_, s) =>
        match s with
        | .layered _ (.abilities add rem) d =>
          g.durationActive d && (rem == .all || !add.staticAbilities.isEmpty)
        | _ => false
      let modChangesTypes (mod : ContinuousModification) : Bool :=
        mod.flatten.any fun
          | .modifyTypes tm => !tm.types.isEmpty || !tm.removeTypes.isEmpty
          | _ => false
      let hasTypeChangingAtt :=
        g.objects.any fun att =>
          att.isOnBattlefield && att.attachedTo == some o.id && att.id != o.id &&
            (hasStaticEff || (!att.status.faceDown &&
              (g.baseCard att).staticAbilities.any fun
                | .continuous none sc mod => StaticAbility.isAttachedHostScope sc && modChangesTypes mod
                | _ => false))
      let bc := g.baseCard o
      let hasSelfTypeStatic :=
        !o.status.faceDown &&
          bc.staticAbilities.any fun
            | .characteristicDefining (.setTypes tm) => !tm.types.isEmpty || !tm.removeTypes.isEmpty
            | .continuous _ sc mod => StaticAbility.isScopeSelf sc && modChangesTypes mod
            | _ => false
      if !hasTypeChangingAtt && !hasSelfTypeStatic then
        if o.status.faceDown || bc.hasProtectionFromChosenCardType then bc.types
        else
          match o.status.chosenCardType with
          | some t => if bc.types.contains t then bc.types else bc.types.push t
          | none => bc.types
      else
        (g.evalLayer4 o).1

def hasType (g : Game) (o : GameObject) (t : CardType) : Bool :=
  (g.types o).contains t

def isCreature (g : Game) (o : GameObject) : Bool :=
  g.hasType o .creature

/-- Creature cards in `p`'s graveyard (evaluated via Layer 1–4 `g.isCreature`, CR 113.6). -/
@[export mtg_game_gy_creature_cards]
def gyCreatureCards (g : Game) (p : PlayerId) : Nat :=
  (g.player p).graveyard.filter (fun id =>
    (g.findObject? id).any (fun c => isDiscardableCard c && g.isCreature c)) |>.size

def isArtifact (g : Game) (o : GameObject) : Bool :=
  g.hasType o .artifact

def isLand (g : Game) (o : GameObject) : Bool :=
  g.hasType o .land

def isEnchantment (g : Game) (o : GameObject) : Bool :=
  g.hasType o .enchantment

def isPlaneswalker (g : Game) (o : GameObject) : Bool :=
  g.hasType o .planeswalker

def isBattle (g : Game) (o : GameObject) : Bool :=
  g.hasType o .battle

def isInstant (g : Game) (o : GameObject) : Bool :=
  g.hasType o .instant

def isSorcery (g : Game) (o : GameObject) : Bool :=
  g.hasType o .sorcery

def isInstantOrSorcery (g : Game) (o : GameObject) : Bool :=
  g.isInstant o || g.isSorcery o

def isPermanentCard (g : Game) (o : GameObject) : Bool :=
  (g.types o).any CardType.isPermanentType

/-- Evaluated supertypes of `o` after Layer 4 type-changing effects (CR 613.1d / 604.3). -/
def supertypes (g : Game) (o : GameObject) : Array Supertype :=
  if o.isLkiSnapshot then o.printed.supertypes
  else if !o.isOnBattlefield then
    let bc := g.baseCard o
    let hasSupCda :=
      !isFaceDownMasked o &&
        bc.staticAbilities.any fun
          | .characteristicDefining (.setTypes tm) => !tm.supertypes.isEmpty || !tm.removeSupertypes.isEmpty
          | _ => false
    if hasSupCda then (g.evalLayer4 o).2.2 else bc.supertypes
  else
    let hasTypesEff := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.types ..) d => g.durationActive d
      | _ => false
    if hasTypesEff then (g.evalLayer4 o).2.2
    else
      let hasStaticEff := g.activeEffects.any fun (_, s) =>
        match s with
        | .layered _ (.abilities add rem) d =>
          g.durationActive d && (rem == .all || !add.staticAbilities.isEmpty)
        | _ => false
      let modChangesSups (mod : ContinuousModification) : Bool :=
        mod.flatten.any fun
          | .modifyTypes tm => !tm.supertypes.isEmpty || !tm.removeSupertypes.isEmpty
          | _ => false
      let hasLegendAura :=
        g.objects.any fun att =>
          att.isOnBattlefield && att.attachedTo == some o.id && att.id != o.id &&
            (hasStaticEff || (!att.status.faceDown &&
              (g.baseCard att).staticAbilities.any fun
                | .continuous none sc mod => StaticAbility.isAttachedHostScope sc && modChangesSups mod
                | _ => false))
      let bc := g.baseCard o
      let hasSelfSupStatic :=
        !o.status.faceDown &&
          bc.staticAbilities.any fun
            | .characteristicDefining (.setTypes tm) => !tm.supertypes.isEmpty || !tm.removeSupertypes.isEmpty
            | .continuous _ sc mod => StaticAbility.isScopeSelf sc && modChangesSups mod
            | _ => false
      if !hasLegendAura && !hasSelfSupStatic then bc.supertypes
      else (g.evalLayer4 o).2.2

def hasSupertype (g : Game) (o : GameObject) (st : Supertype) : Bool :=
  (g.supertypes o).contains st

def isLegendary (g : Game) (o : GameObject) : Bool :=
  g.hasSupertype o .legendary

@[inline] def treatedAsLegendary (g : Game) (o : GameObject) : Bool :=
  g.isLegendary o

/-- Evaluated subtypes of `o` after Layer 4 type-changing effects (CR 613.1d). -/
def subtypes (g : Game) (o : GameObject) : Array CardSubtype :=
  (g.evalLayer4 o).2.1

@[inline] def currentSubtypes (g : Game) (o : GameObject) : Array CardSubtype :=
  g.subtypes o

/-- Whether `o` currently has subtype `s` after Layer 4 (CR 205.3d / 604.3 / 613.1d / 702.73a). -/
def hasSubtype (g : Game) (o : GameObject) (s : CardSubtype) : Bool :=
  if o.isLkiSnapshot then (g.subtypes o).contains s
  else
    let bc := g.baseCard o
    if !o.isOnBattlefield then
      let hasSubCda :=
        !isFaceDownMasked o &&
          bc.staticAbilities.any fun
            | .characteristicDefining .allCreatureTypes => true
            | .characteristicDefining (.setTypes tm) => !tm.subtypes.isEmpty
            | _ => false
      if bc.subtypes.isEmpty && !bc.hasSimpleKeyword .changeling && !hasSubCda then false
      else (g.subtypes o).contains s
    else if bc.subtypes.isEmpty && !bc.hasSimpleKeyword .changeling && bc.staticAbilities.isEmpty &&
        !g.activeEffects.any (fun (_, sp) =>
          match sp with | .layered _ (.types ..) d => g.durationActive d | _ => false) &&
        !g.objects.any (fun att => att.isOnBattlefield && att.attachedTo == some o.id) then
      false
    else
      (g.subtypes o).contains s

def cantAttackJace (g : Game) (attacker : PlayerId) (pw : GameObject) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .playerRule q (.cantAttackJaces jaceCtrl) d =>
      q == attacker && g.durationActive d && g.controlledBy pw jaceCtrl && g.hasSubtype pw .jace
    | _ => false

def isAura (g : Game) (o : GameObject) : Bool :=
  g.isEnchantment o && g.hasSubtype o .aura

def isEquipment (g : Game) (o : GameObject) : Bool :=
  g.isArtifact o && g.hasSubtype o .equipment

def isBasicLand (g : Game) (o : GameObject) : Bool :=
  g.hasSupertype o .basic && g.isLand o

/-- True when `p` controls a basic land after Layer 4 (CR 205.4c / 305.8 / 613.1d). -/
def controlsBasicLand (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (g.isBasicLand ·)

/-- Evaluated type line of `o` after Layer 4 type-changing effects (CR 205.1a / 613.1d). -/
def typeLine (g : Game) (o : GameObject) : String :=
  formatTypeLine (g.supertypes o) (g.types o) ((g.subtypes o).map CardSubtype.englishName)

/-- Creatures `p` currently controls (evaluated after Layer 4, CR 613.1d). -/
def creaturesControlledBy (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (g.isCreature ·)

/-- Cards of `subtype` in `p`'s graveyard (evaluated via Layer 4, CR 113.6 / 702.73a). -/
def graveyardCardsOfSubtype (g : Game) (p : PlayerId) (subtype : CardSubtype) :
    Array GameObject :=
  (g.player p).graveyard.filterMap (fun id =>
    match g.findObject? id with
    | some card => if g.hasSubtype card subtype then some card else none
    | none => none)

/-- Equipment attached to `o` after Layer 4 (CR 301.5 / 613.1d). -/
def attachedEquipmentCount (g : Game) (o : GameObject) : Nat :=
  g.battlefield.filter (fun eq =>
    g.isEquipment eq && eq.attachedTo == some o.id) |>.size

-- Layer 5: Base color + CR 604.3 color CDA evaluation (CR 202.2 / 305.7 / 613.1e / 613.3 / 708.2a)

private def baseColorsL5 (g : Game) (o : GameObject) : ColorSet :=
  if o.isLkiSnapshot then o.printed.colors
  else if isFaceDownMasked o then ColorSet.empty
  else
    let bc := g.baseCard o
    let hasColorCda := bc.staticAbilities.any fun
      | .characteristicDefining (.setColors _) => true
      | _ => false
    if !hasColorCda then bc.colors
    else
      let strippedByL4 :=
        o.isOnBattlefield && (g.evalLayer4Full o).strippedRulesTextByBasicLandSet
      if strippedByL4 then bc.colors
      else
        let oTcs := g.evalLayer3 o
        let mappedOwnL5 :=
          if oTcs.isEmpty then bc.staticAbilities
          else bc.staticAbilities.map (TextChange.applyStaticAbility oTcs)
        -- CR 604.3 / 613.1e / 613.3: Color-defining CDAs function in all zones and apply first in Layer 5.
        mappedOwnL5.foldl (fun cols ab =>
          match ab with
          | .characteristicDefining (.setColors cs) => cs
          | _ => cols) bc.colors

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

/-- Whether `p` currently has the city's blessing. -/
def hasCitysBlessing (g : Game) (p : PlayerId) : Bool :=
  (g.player p).citysBlessing

/-- Number of permanents `p` currently controls (phased-out objects do not
count). -/
def permanentCount (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).size

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
      if after.id == some id then e.cause? else none
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

/-- Resolutions `p`'s counting ability has recorded this turn (optionally scoped to `sourceId` / `ability`). -/
def loggedResolutions (g : Game) (p : PlayerId)
    (sourceId : Option ObjectId := none) (ability : Option TriggeredAbility := none) : Nat :=
  GameEvent.resolutions g.events g.turnNumber p sourceId ability

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
        pkt.amount > 0 && pkt.source.hasDeathtouch &&
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

/-- Count how many leading `(PlayerId, α)` or `PlayerId` entries in `queued`
belong to the remaining seats of the currently in-progress shared extra turn
(`seatsExtra && !seats.isEmpty`), matched as an ordered subsequence of
`g.teamMembers seats[0]!` strictly after `seats.back!` (CR 500.7 / 805.8 / 810.2). -/
def countInProgressSharedExtraSeats (g : Game) (seats : Array PlayerId) (seatsExtra : Bool)
    (queued : Array PlayerId) : Nat :=
  if !seatsExtra || seats.isEmpty then 0
  else Id.run do
    let curTeam := g.teamMembers seats[0]!
    let lastSeat := seats.back!
    let mut remIdx : Nat :=
      match curTeam.findIdx? (· == lastSeat) with
      | some k => k + 1
      | none => curTeam.size
    let mut cnt : Nat := 0
    for q in queued do
      match (curTeam.extract remIdx curTeam.size).findIdx? (· == q) with
      | some rel =>
        remIdx := remIdx + rel + 1
        cnt := cnt + 1
      | none =>
        return cnt
    return cnt

/-- Indices of activated abilities of `id` activated this turn (CR 602.5b). -/
def abilitiesActivatedThisTurn (g : Game) (id : ObjectId) : Array Nat :=
  g.events.foldl (fun acc e =>
    if e.turn != g.turnNumber then acc
    else
      match e.change with
      | .rules (.cast (.abilityActivated _ src _ (.nonMana _ _ _ _ (some idx) _)))
      | .rules (.cast (.abilityActivated _ src _ (.mana (some idx) ..))) =>
        if src.id == some id then acc.push idx else acc
      | _ => acc) #[]

/-- How many times ability `idx` of `id` was activated this turn (CR 602.5b / 702.142a).
When `isBoast` is true, also counts legacy boast events that did not record `abilityIdx`. -/
def abilityActivationsThisTurn (g : Game) (id : ObjectId) (idx : Nat)
    (isBoast : Bool := false) : Nat :=
  g.events.foldl (fun n e =>
    if e.turn != g.turnNumber then n
    else
      match e.change with
      | .rules (.cast (.abilityActivated _ src _ kind)) =>
        if src.id != some id then n
        else
          match kind.abilityIdx? with
          | some k => if k == idx then n + 1 else n
          | none =>
            if isBoast then
              match kind with
              | .nonMana _ _ _ true _ _ => n + 1
              | _ => n
            else n
      | _ => n) 0

/-- How many times ability `idx` of `id` has been activated since `id` entered
the battlefield (CR 702.177a Exhaust / CR 702.193a Power-up).
When `isPowerUp` / `isExhaust` is true, also counts legacy events without `abilityIdx`. -/
def abilityActivationsSinceEntered (g : Game) (id : ObjectId) (idx : Nat)
    (isPowerUp : Bool := false) (isExhaust : Bool := false) : Nat :=
  g.events.foldl (fun n e =>
    match e.change with
    | .rules (.zone (.moved _ after _ .battlefield ..)) =>
      if after.id == some id then 0 else n
    | .rules (.zone (.created obj _)) =>
      if obj.zone == .battlefield && obj.id == some id then 0 else n
    | .rules (.cast (.abilityActivated _ src _ kind)) =>
      if src.id != some id then n
      else
        match kind.abilityIdx? with
        | some k => if k == idx then n + 1 else n
        | none =>
          match kind with
          | .nonMana _ _ pu _ _ ex =>
            if (isPowerUp && pu) || (isExhaust && ex) then n + 1 else n
          | .mana _ pu ex =>
            if (isPowerUp && pu) || (isExhaust && ex) then n + 1 else n
    | _ => n) 0

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
      if obj.zone == .battlefield && obj.id == some id then 0 else n
    | .rules (.cast (.abilityActivated _ src _ (.nonMana _ _ true ..)))
    | .rules (.cast (.abilityActivated _ src _ (.mana _ true _))) =>
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
      if obj.zone == .battlefield && obj.id == some id then false else used
    | .rules (.cast (.abilityActivated _ src _ (.nonMana _ _ _ _ _ true)))
    | .rules (.cast (.abilityActivated _ src _ (.mana _ _ true))) =>
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
      if obj.zone == .battlefield && obj.id == some id then false else dealt
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
      if obj.zone == .battlefield && obj.id == some sourceId then #[] else acc
    | .rules (.triggerQueue (.modeChosen sid m true)) =>
      if sid == sourceId then acc.push m else acc
    | _ => acc) #[]

/-- Qualities `p` has beheld this game (CR 701.4). -/
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

-- Layer 6: Ability-adding and ability-removing effects (CR 613.1f / 613.7 / 613.7a / 613.7e / 613.8)

/-- Lore counters among Sagas `p` controls after Layer 4 (CR 613.1d). -/
def loreAmongSagas (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if g.hasSubtype o .saga then acc + o.status.lore else acc) 0

/-- Whether `p` controls a Jace planeswalker after Layer 4 (CR 613.1d). -/
def controlsJacePlaneswalker (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun x => g.isPlaneswalker x && g.hasSubtype x .jace)

/-- True when a grantor of hexproof or damage prevention is still on the
battlefield. -/
def grantorStillInPlay (g : Game) (id : ObjectId) : Bool :=
  match g.findObject? id with
  | some o => o.isOnBattlefield
  | none => false

/-- True when `q` is a living opponent of `p` (CR 102.2 / 810). -/
def isLivingOpponentOf (g : Game) (p q : PlayerId) : Bool :=
  (g.livingOpponents p).any (fun pl => pl.id == q)

/-- First living opponent of `p` in turn order after `p`, or `none` when no
living opponent remains (CR 102.2 / 810). -/
def firstLivingOpponent? (g : Game) (p : PlayerId) : Option PlayerId :=
  let opps := g.livingOpponents p
  let n := g.players.size
  if n == 0 || opps.isEmpty then none
  else
    Id.run do
      for k in [1:n+1] do
        let q : PlayerId := ⟨(p.idx + k) % n⟩
        if opps.any (fun pl => pl.id == q) then
          return some q
      return none

def opponent (g : Game) (p : PlayerId) : PlayerId :=
  match g.firstLivingOpponent? p with
  | some q => q
  | none =>
    if g.stillInGame p then p
    else
      let n := g.players.size
      if n == 0 then p
      else
        Id.run do
          for k in [1:n+1] do
            let q : PlayerId := ⟨(p.idx + k) % n⟩
            if g.stillInGame q then
              return q
          return p

/-- Look up a live `GameObject` at `sid`, treating phased-out battlefield
permanents as absent so callers consult pre-phase-out LKI (CR 702.26b). -/
def findLiveSourceObject? (g : Game) (sid : ObjectId) : Option GameObject :=
  (g.findObject? sid).filter (fun o => !(o.zone == .battlefield && o.status.phasedOut))

/-- Defending player of an attacking status `s`: the player directly attacked,
or the controller of the planeswalker/battle being attacked (CR 506.2 / 506.4c). -/
def defendingPlayerOfStatus (g : Game) (s : Status) : Option PlayerId :=
  match s.attackingTarget with
  | some (.player p) => some p
  | some (.planeswalker pw) | some (.battle pw) =>
    match g.findLiveSourceObject? pw with
    | some o => some ((g.controllerOf o).getD o.owner)
    | none =>
      match GameEvent.lastKnownBefore? g.events pw with
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
      if o.isOnBattlefield && o.status.attacking then
        let ctrl := (g.controllerOf o).getD g.activePlayer
        (g.defendingPlayerOfStatus o.status).filter (g.isLivingOpponentOf ctrl ·)
      else none) with
    | some p => p
    | none => g.opponent g.activePlayer

/-- Defending player of an attacking object `o` (CR 506.2 / 506.4c), falling
back to `g.defendingPlayer`. -/
def defendingPlayerOf (g : Game) (o : GameObject) : PlayerId :=
  (g.defendingPlayerOfStatus o.status).getD g.defendingPlayer

/-- Distinct players being attacked, in APNAP order (CR 508.1 / 101.4 / 810.7). -/
def defendingPlayers (g : Game) : Array PlayerId :=
  let attacked :=
    g.objects.filterMap (fun o =>
      if o.isOnBattlefield && o.status.attacking then
        let ctrl := (g.controllerOf o).getD g.activePlayer
        (g.defendingPlayerOfStatus o.status).filter (g.isLivingOpponentOf ctrl ·)
      else none)
  let n := g.players.size
  Id.run do
    let mut acc : Array PlayerId := #[]
    for k in [0:n] do
      let q : PlayerId := ⟨(g.activePlayer.idx + k) % n⟩
      if q != g.activePlayer && g.stillInGame q && attacked.contains q then
        acc := acc.push q
    return acc

/-! ### Layer-1–5 Recursion-Safe Static Expression Helpers (CR 604 / 613) -/

/-- Resolve source-bound protection keywords (`.protection .chosenCardType`,
`.protection (.color .chosenOnSource)`, `.protection (.subtype .chosenOnSource)`)
concretely against `src.status` in Layer 6 (CR 613.1f / 702.16). When `dropUnchosen`
is `true` (static grants from a grantor permanent), unchosen protection entries are
omitted so they never leak onto the recipient's own `status`. -/
def resolveProtectionKeywords (src : GameObject) (ks : Array KeywordAbility)
    (dropUnchosen : Bool := true) : Array KeywordAbility :=
  ks.filterMap fun
    | .protection .chosenCardType =>
      match src.status.chosenCardType with
      | some t => some (.protection (.cardType t))
      | none => if dropUnchosen then none else some (.protection .chosenCardType)
    | .protection (.color .chosenOnSource) =>
      match src.status.chosenColor with
      | some c => some (.protection (.color (.literal c)))
      | none => if dropUnchosen then none else some (.protection (.color .chosenOnSource))
    | .protection (.subtype .chosenOnSource) =>
      match src.status.chosenCreatureType with
      | some ty => some (.protection (.subtype (.literal ty)))
      | none => if dropUnchosen then none else some (.protection (.subtype .chosenOnSource))
    | .hexproof (some (.color .chosenOnSource)) =>
      match src.status.chosenColor with
      | some c => some (.hexproof (some (.color (.literal c))))
      | none => if dropUnchosen then none else some (.hexproof (some (.color .chosenOnSource)))
    | .hexproof (some (.subtype .chosenOnSource)) =>
      match src.status.chosenCreatureType with
      | some ty => some (.hexproof (some (.subtype (.literal ty))))
      | none => if dropUnchosen then none else some (.hexproof (some (.subtype .chosenOnSource)))
    | k => some k

/-- CR 122.1b keyword abilities granted by counters currently on `o`.
Cumulative keyword counters (e.g. exalted, CR 702.83b) contribute one instance per counter. -/
private def keywordCounterAbilities (o : GameObject) : Array KeywordAbility :=
  if o.status.counters.isEmpty then #[]
  else
    CounterKind.keywordCounters.foldl (fun acc (k, kw) =>
      let cnt := o.status.counterCount k
      if cnt > 0 then
        let kwArr := if kw.isCumulative then Array.replicate cnt kw else #[kw]
        KeywordAbility.merge acc kwArr
      else acc) #[]

/-- Printed keywords (after Layer 3 text changes) plus CR 122.1b keyword counters on `o`.
Used only as a recursion-safe fallback when Layer 6 peer fuel reaches 0. -/
private def baseKeywordsWithCounters (g : Game) (o : GameObject) : Array KeywordAbility :=
  if o.isLkiSnapshot then resolveProtectionKeywords o o.printed.keywords (dropUnchosen := false)
  else if isFaceDownMasked o then keywordCounterAbilities o
  else
    let bc := g.baseCard o
    let oTcs := g.evalLayer3 o
    let rawKw :=
      if oTcs.isEmpty then bc.keywords
      else HasTextChange.applyTextChanges oTcs bc.keywords
    let printedKw := resolveProtectionKeywords o rawKw (dropUnchosen := false)
    KeywordAbility.merge printedKw (keywordCounterAbilities o)

private partial def staticPredMentionsPhasedOut : ObjectPred → Bool
  | .phasedOut _ => true
  | .all ps | .any ps => ps.any staticPredMentionsPhasedOut
  | .not inner => staticPredMentionsPhasedOut inner
  | _ => false

mutual

private partial def predMentionsKeyword : ObjectPred → Bool
  | .hasKeyword _ => true
  | .all ps | .any ps => ps.any predMentionsKeyword
  | .not inner => predMentionsKeyword inner
  | .hasAttachment af => predMentionsKeyword af.pred
  | .stat _ _ rhs | .counterCount _ _ rhs => valExprMentionsKeyword rhs
  | .controlledBy pf | .ownedBy pf => playerPredMentionsKeyword pf.pred
  | .combatRole (.attackingPlayer pe) => playerExprMentionsKeyword pe
  | .combatRole (.blockingObject oe) => objExprMentionsKeyword oe
  | .attachedTo oe | .shares _ oe => objExprMentionsKeyword oe
  | .targets (.object oe) => objExprMentionsKeyword oe
  | .targets (.player pe) => playerExprMentionsKeyword pe
  | .targets (.either oe pe) => objExprMentionsKeyword oe || playerExprMentionsKeyword pe
  | .dealtDamageThisTurn _ (some (.player pf)) _ => playerPredMentionsKeyword pf.pred
  | .dealtDamageThisTurn _ (some (.object f)) _ => predMentionsKeyword f.pred
  | .dealtDamageThisTurn _ (some (.playerOrObject pf f)) _ =>
    playerPredMentionsKeyword pf.pred || predMentionsKeyword f.pred
  | .receivedCounterThisTurn _ (some pf) => playerPredMentionsKeyword pf.pred
  | _ => false

private partial def objExprMentionsKeyword : ObjectExpr → Bool
  | .inZones zs p =>
    let ownerKw :=
      match zs.owner with
      | .any => false
      | .matching pf => playerPredMentionsKeyword pf.pred
      | .ofPlayer pe => playerExprMentionsKeyword pe
    ownerKw || predMentionsKeyword p
  | .topOfLibrary pe ve => playerExprMentionsKeyword pe || valExprMentionsKeyword ve
  | .extremum _ _ oe => objExprMentionsKeyword oe
  | .union es => es.any objExprMentionsKeyword
  | .diff lhs rhs => objExprMentionsKeyword lhs || objExprMentionsKeyword rhs
  | _ => false

private partial def valExprMentionsKeyword : ValueExpr → Bool
  | .objectStat _ oe | .counterCount _ oe | .aggregate _ _ oe
  | .basicLandTypeCount oe | .cardTypeCount oe | .subtypeCount _ oe
  | .manaSymbols _ oe | .colorCountAmong oe =>
    objExprMentionsKeyword oe
  | .playerMetric _ pe => playerExprMentionsKeyword pe
  | .maxControlled who p => playerPredMentionsKeyword who.pred || predMentionsKeyword p
  | .binary _ a b => valExprMentionsKeyword a || valExprMentionsKeyword b
  | _ => false

private partial def playerPredMentionsKeyword : PlayerPred → Bool
  | .all ps | .anyOf ps => ps.any playerPredMentionsKeyword
  | .not p => playerPredMentionsKeyword p
  | .metric _ _ rhs => valExprMentionsKeyword rhs
  | .controls f v => predMentionsKeyword f.pred || valExprMentionsKeyword v
  | .matchesExpr pe => playerExprMentionsKeyword pe
  | _ => false

private partial def playerExprMentionsKeyword : PlayerExpr → Bool
  | .matching _ p => playerPredMentionsKeyword p
  | .controllerOf oe | .ownerOf oe => objExprMentionsKeyword oe
  | .chosenBy _ _ pf => playerPredMentionsKeyword pf.pred
  | _ => false

private partial def condMentionsKeyword : Condition → Bool
  | .cmp _ a b => valExprMentionsKeyword a || valExprMentionsKeyword b
  | .exists oe => objExprMentionsKeyword oe
  | .forAll oe p => objExprMentionsKeyword oe || predMentionsKeyword p
  | .playerPred pe p => playerExprMentionsKeyword pe || playerPredMentionsKeyword p
  | .all cs | .any cs => cs.any condMentionsKeyword
  | .not c => condMentionsKeyword c
  | _ => false

end

mutual

private partial def predReadsPT : ObjectPred → Bool
  | .stat .power _ _ | .stat .toughness _ _ => true
  | .statParity .power _ | .statParity .toughness _ => true
  | .stat _ _ rhs | .counterCount _ _ rhs => valExprReadsPT rhs
  | .all ps | .any ps => ps.any predReadsPT
  | .not inner => predReadsPT inner
  | .hasAttachment af => predReadsPT af.pred
  | .controlledBy pf | .ownedBy pf => playerPredReadsPT pf.pred
  | .combatRole (.attackingPlayer pe) => playerExprReadsPT pe
  | .combatRole (.blockingObject oe) => objExprReadsPT oe
  | .attachedTo oe | .shares _ oe => objExprReadsPT oe
  | .targets (.object oe) => objExprReadsPT oe
  | .targets (.player pe) => playerExprReadsPT pe
  | .targets (.either oe pe) => objExprReadsPT oe || playerExprReadsPT pe
  | .dealtDamageThisTurn _ (some (.player pf)) _ => playerPredReadsPT pf.pred
  | .dealtDamageThisTurn _ (some (.object f)) _ => predReadsPT f.pred
  | .dealtDamageThisTurn _ (some (.playerOrObject pf f)) _ =>
    playerPredReadsPT pf.pred || predReadsPT f.pred
  | .receivedCounterThisTurn _ (some pf) => playerPredReadsPT pf.pred
  | _ => false

private partial def objExprReadsPT : ObjectExpr → Bool
  | .inZones zs p =>
    let ownerPT :=
      match zs.owner with
      | .any => false
      | .matching pf => playerPredReadsPT pf.pred
      | .ofPlayer pe => playerExprReadsPT pe
    ownerPT || predReadsPT p
  | .topOfLibrary pe ve => playerExprReadsPT pe || valExprReadsPT ve
  | .extremum _ metric oe => metric == .power || metric == .toughness || objExprReadsPT oe
  | .union es => es.any objExprReadsPT
  | .diff lhs rhs => objExprReadsPT lhs || objExprReadsPT rhs
  | .linkedExile oe => objExprReadsPT oe
  | .filter oe p => objExprReadsPT oe || predReadsPT p
  | _ => false

private partial def valExprReadsPT : ValueExpr → Bool
  | .objectStat .power _ | .objectStat .toughness _ => true
  | .aggregate _ (.stat .power) _ | .aggregate _ (.stat .toughness) _ => true
  | .objectStat _ oe | .counterCount _ oe | .aggregate _ _ oe
  | .basicLandTypeCount oe | .cardTypeCount oe | .subtypeCount _ oe
  | .manaSymbols _ oe | .colorCountAmong oe =>
    objExprReadsPT oe
  | .playerMetric _ pe => playerExprReadsPT pe
  | .maxControlled who p => playerPredReadsPT who.pred || predReadsPT p
  | .binary _ a b => valExprReadsPT a || valExprReadsPT b
  | _ => false

private partial def playerPredReadsPT : PlayerPred → Bool
  | .all ps | .anyOf ps => ps.any playerPredReadsPT
  | .not p => playerPredReadsPT p
  | .metric _ _ rhs => valExprReadsPT rhs
  | .controls f v => predReadsPT f.pred || valExprReadsPT v
  | .matchesExpr pe => playerExprReadsPT pe
  | _ => false

private partial def playerExprReadsPT : PlayerExpr → Bool
  | .matching _ p => playerPredReadsPT p
  | .controllerOf oe | .ownerOf oe => objExprReadsPT oe
  | .chosenBy _ _ pf => playerPredReadsPT pf.pred
  | _ => false

private partial def condReadsPT : Condition → Bool
  | .cmp _ a b => valExprReadsPT a || valExprReadsPT b
  | .exists oe => objExprReadsPT oe
  | .forAll oe p => objExprReadsPT oe || predReadsPT p
  | .playerPred pe p => playerExprReadsPT pe || playerPredReadsPT p
  | .all cs | .any cs => cs.any condReadsPT
  | .not c => condReadsPT c
  | _ => false

end

/-- Reconstruct `(leaveTriggerExile, linkedExile)` recorded on departed source
`sid` from `g.events` (CR 607.2a). -/
def departedLinkedExiles (g : Game) (sid : ObjectId) : Array ObjectId × Array ObjectId :=
  g.events.foldl (fun (lte, le) ev =>
    match ev.change with
    | .rules (.zone (.moved _ after ..)) =>
      if after.id == some sid then (#[], #[]) else (lte, le)
    | .rules (.zone (.created after _)) =>
      if after.id == some sid then (#[], #[]) else (lte, le)
    | .engine (.materializeObject obj _) =>
      if obj.id == sid then (obj.leaveTriggerExile, obj.linkedExile) else (lte, le)
    | .engine (.object id oc) =>
      if id != sid then (lte, le)
      else
        match oc with
        | .leaveTriggerExile v => (v, le)
        | .pushLeaveTriggerExile x => (lte.push x, le)
        | .linkedExile v => (lte, v)
        | .pushLinkedExile x => (lte, le.push x)
        | _ => (lte, le)
    | _ => (lte, le)) (#[], #[])

/-- Linked-exile object ids (`leaveTriggerExile ++ linkedExile`) of `sid`,
consulting `g.events` LKI when `sid` has already left its zone (CR 607.2a). -/
def allLinkedExilesOf (g : Game) (sid : ObjectId) : Array ObjectId :=
  match g.findObject? sid with
  | some src => src.leaveTriggerExile ++ src.linkedExile
  | none =>
    let (lte, le) := g.departedLinkedExiles sid
    lte ++ le

private def matchStaticPlayerRel (g : Game) (srcCtrl : PlayerId) (rel : PlayerRelation)
    (p : PlayerId) : Bool :=
  g.stillInGame p &&
    match rel with
    | .you => p == srcCtrl
    | .opponent => (g.livingOpponents srcCtrl).any (·.id == p)
    | .teammate => g.areTeammates srcCtrl p
    | .anyPlayer => true

private def staticPlayersMatchingRel (g : Game) (srcCtrl : PlayerId) (rel : PlayerRelation) :
    Array PlayerId :=
  g.players.filterMap fun pl =>
    if g.matchStaticPlayerRel srcCtrl rel pl.id then some pl.id else none

private def evalStaticPlayerMetricSingle (g : Game) (m : PlayerMetric) (p : PlayerId)
    (excludeObjId? : Option ObjectId := none) : Int :=
  let pl := g.player p
  match m with
  | .life => pl.life
  | .handSize =>
    Int.ofNat (pl.hand.filter (fun id => (g.findObject? id).any isDiscardableCard)).size
  | .librarySize => Int.ofNat pl.library.size
  | .graveyardSize =>
    Int.ofNat (pl.graveyard.filter (fun id => (g.findObject? id).any isDiscardableCard)).size
  | .landsPlayedThisTurn => Int.ofNat (GameEvent.landsPlayed g.events g.turnNumber p)
  | .spellsCastThisTurn => Int.ofNat (GameEvent.spellsCast g.events g.turnNumber p)
  | .cardsDrawnThisTurn => Int.ofNat (GameEvent.draws g.events g.turnNumber p)
  | .cardsDiscardedThisTurn =>
    Int.ofNat (g.events.foldl (fun n e =>
      if e.turn == g.turnNumber then
        match e.change with
        | .rules (.zone (.moved _ _ (.hand q) _ .discard _ _ _)) => if q == p then n + 1 else n
        | _ => n
      else n) 0)
  | .cardsMilledThisTurn =>
    Int.ofNat (g.events.foldl (fun n e =>
      if e.turn == g.turnNumber then
        match e.change with
        | .rules (.zone (.moved _ _ (.library q) _ .mill _ _ _)) => if q == p then n + 1 else n
        | _ => n
      else n) 0)
  | .otherSpellsManaValueThisTurn =>
    let (sumOther, matchedSelf, hasUnidentified) :=
      g.events.foldl (fun (acc, matched, unid) e =>
        if e.turn == g.turnNumber then
          match e.change with
          | .rules (.cast (.spellCast spellSnap q _)) =>
            if q == p then
              if excludeObjId?.isSome && spellSnap.id == excludeObjId? then
                (acc, true, unid)
              else
                (acc + spellSnap.manaValue, matched, unid || spellSnap.id.isNone)
            else (acc, matched, unid)
          | _ => (acc, matched, unid)
        else (acc, matched, unid)) (0, false, false)
    let ownFallback :=
      if !matchedSelf && hasUnidentified then
        match excludeObjId?.bind g.findObject? with
        | some spell =>
          if spell.zone == .stack && !spell.isCopy && g.controllerOf spell == some p &&
              !g.proposedSpell.any (·.spellId == spell.id) then
            if spell.status.faceDown then 0
            else
              let mc := (g.copiableValues spell).manaCost
              let x := (spell.chosenX.orElse (fun _ => GameEvent.chosenXOf? g.events spell.id)).getD 0
              (mc.substituteX x).manaValue
          else 0
        | none => 0
      else 0
    Int.ofNat (sumOther - ownFallback)
  | .lifeGainedThisTurn => Int.ofNat (GameEvent.lifeGained g.events g.turnNumber p)
  | .lifeLostThisTurn => Int.ofNat (GameEvent.lifeLost g.events g.turnNumber p)
  | .unspentMana => Int.ofNat pl.manaPool.total
  | .poisonCounters => Int.ofNat pl.poison
  | .opponentsCount => Int.ofNat (g.livingOpponents p).size
  | .one => 1

private def swapCardFace (c : CardDef) : CardDef :=
  match c.otherFace with
  | some face =>
    let keepToken := c.isToken
    { face with
      isToken := keepToken
      otherFace := some { c with isToken := keepToken, otherFace := none } }
  | none => c

/-- Value of X for `id`: its stack `chosenX` if on the stack, or else the announced X from `g.events` (CR 107.3a / 400.7d / 707.10). -/
def chosenXOf? (g : Game) (id : ObjectId) : Option Nat :=
  ((g.findObject? id).bind (·.chosenX)).orElse (fun _ => GameEvent.chosenXOf? g.events id)

/-- Last-known `before` snapshot for `id` from `ZoneEvent.moved`,
`ZoneEvent.ceasedToExist`, or `PermanentEvent.phasedOut` (CR 113.7a / 608.2h /
702.26b). -/
def lastKnownBefore? (g : Game) (id : ObjectId) : Option EventObject :=
  GameEvent.lastKnownBefore? g.events id

/-- Last-known `EventObject` snapshots of attachments that were attached to `hostId`
when `hostId` left the battlefield (`ZoneEvent.moved` / `ZoneEvent.ceasedToExist` +
`PermanentEvent.unattached` with `.unattachOnHostLeave`) or phased out
(`PermanentEvent.phasedOut` batch with co-phased attachments whose
`attachedTo == some hostId`, CR 608.2h / 702.26b,g). Returns `none` when no
departure or phase-out event for `hostId` exists since its latest `.phasedIn`. -/
def departedOrPhasedOutAttachments? (g : Game) (hostId : ObjectId) : Option (Array EventObject) := Id.run do
  let collectUnattached (batch : Option BatchId) : Array EventObject :=
    g.events.foldl (fun acc ev =>
      if ev.batch == batch && ev.cause? == some (.gameRule .unattachOnHostLeave) then
        match ev.change with
        | .rules (.permanent (.unattached att fromHost)) =>
          if fromHost == hostId then acc.push att else acc
        | _ => acc
      else acc) #[]
  let collectPhasedOut (poIdx : Nat) (batch : Option BatchId) : Array EventObject :=
    match batch with
    | some b =>
      g.events.foldl (fun acc ev =>
        if ev.batch == some b then
          match ev.change with
          | .rules (.permanent (.phasedOut att _)) =>
            if att.id != some hostId && att.attachedTo == some hostId then acc.push att else acc
          | _ => acc
        else acc) #[]
    | none => Id.run do
      let mut acc : Array EventObject := #[]
      let mut j := poIdx + 1
      while j < g.events.size do
        match g.events[j]!.change with
        | .rules (.permanent (.phasedOut att true)) =>
          if att.id != some hostId && att.attachedTo == some hostId then
            acc := acc.push att
          j := j + 1
        | .engine (.logMsg _) | .rules (.combat _) => j := j + 1
        | _ => break
      return acc
  let mut phasedOutFallback? : Option (Array EventObject) := none
  let mut i := g.events.size
  while i > 0 do
    i := i - 1
    let ev := g.events[i]!
    match ev.change with
    | .rules (.permanent (.phasedIn eo _)) =>
      if eo.id == some hostId then
        return phasedOutFallback?
    | .rules (.zone (.moved before _ .battlefield toZ ..)) =>
      if toZ != .battlefield && before.id == some hostId then
        if before.phasedOut then
          phasedOutFallback? := phasedOutFallback?.orElse (fun _ => some (collectUnattached ev.batch))
        else
          return some (collectUnattached ev.batch)
    | .rules (.zone (.ceasedToExist before)) =>
      if before.zone == .battlefield && before.id == some hostId then
        if before.phasedOut then
          phasedOutFallback? := phasedOutFallback?.orElse (fun _ => some (collectUnattached ev.batch))
        else
          return some (collectUnattached ev.batch)
    | .rules (.permanent (.phasedOut before _)) =>
      if before.id == some hostId && !before.phasedOut then
        return some (collectPhasedOut i ev.batch)
    | _ => pure ()
  return phasedOutFallback?

/-- Index of the last combat-phase start (`phaseBegan .combat` or
`stepBegan .beginningOfCombat`) on `turn` at or before `limit` in `events`
(or `0` if none was logged at or before `limit`). -/
def combatPhaseStartIdxAtOrBefore (events : Array GameEvent) (turn limit : Nat) : Nat := Id.run do
  let hi := min limit events.size
  let mut start := 0
  for i in [0:hi] do
    let e := events[i]!
    if e.turn == turn then
      match e.change with
      | .rules (.turn (.phaseBegan .combat))
      | .rules (.turn (.stepBegan .beginningOfCombat _)) => start := i
      | _ => pure ()
  return start

/-- Locate the start index of `batch` within `[startIdx, idx]` on `wTurn`. -/
def batchStartAt (events : Array GameEvent) (wTurn startIdx idx : Nat)
    (batch : Option BatchId) : Nat :=
  match batch with
  | none => idx
  | some bid => Id.run do
    let mut s := idx
    while s > startIdx && s ≤ events.size &&
        events[s - 1]!.turn == wTurn && events[s - 1]!.batch == some bid do
      s := s - 1
    return s

/-- Locate the exclusive end index of the combat phase containing `anchorIdx` on `wTurn`,
stopping before any turn change, subsequent combat phase, or `oid`'s departure/phasing/removal. -/
def combatPhaseEndAfter (events : Array GameEvent) (oid : ObjectId)
    (wTurn anchorIdx : Nat) : Nat := Id.run do
  let mut endIdx := events.size
  for i in [(anchorIdx + 1):events.size] do
    if endIdx == events.size then
      let e := events[i]!
      if e.turn != wTurn then
        endIdx := i
      else
        match e.change with
        | .rules (.turn (.phaseBegan .combat))
        | .rules (.turn (.stepBegan .beginningOfCombat _)) => endIdx := i
        | .rules (.combat (.removedFromCombat eo)) =>
          if eo.id == some oid && eo.attacking then endIdx := i
        | .rules (.permanent (.phasedOut before _)) =>
          if before.id == some oid then endIdx := i
        | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
          if toZ != .battlefield && before.id == some oid then endIdx := i
        | .rules (.zone (.ceasedToExist before)) =>
          if before.zone == .battlefield && before.id == some oid then endIdx := i
        | _ => pure ()
  return endIdx

/-- Combat-phase event window `(windowTurn, combatStartIdx, atkEndIdx, blockEndIdx)`
for LKI object `oid`: when `eventIdx?` points to an event for `oid`, anchors directly on
that event; otherwise locates `oid`'s last attacking battlefield departure, phase-out, or
`removedFromCombat` event on any turn `≤ defaultTurn` (bounded at `eventIdx?` when
provided, or its last combat event if it did not depart while attacking), and opens the
combat window on **that event's turn**. For `.phasedOut` batches, `blockEndIdx` is `bStart`
so the same-batch `removedFromCombat` emitted by `Phasing.phaseOut` right before `phasedOut`
does not erase `becameBlocked` (CR 509.1h / 608.2h / 702.26b / 800.4a). -/
def lkiCombatWindow (events : Array GameEvent) (oid : ObjectId)
    (defaultTurn : Nat) (eventIdx? : Option Nat := none) : Nat × Nat × Nat × Nat := Id.run do
  let unbatchedAtkEnd (wTurn eIdx : Nat) : Nat := Id.run do
    let mut j := eIdx + 1
    while j < events.size && events[j]!.turn == wTurn do
      match events[j]!.change with
      | .rules (.combat (.becameAttacking atk _)) =>
        if atk.id == some oid then return j + 1
        j := j + 1
      | .rules (.turn _)
      | .rules (.damage _)
      | .rules (.cast _)
      | .rules (.stackObject _)
      | .rules (.combat (.attackersDeclared ..))
      | .rules (.combat (.blockersDeclared ..))
      | .rules (.combat (.becameBlocked ..))
      | .rules (.combat (.remainedUnblocked ..)) =>
        return eIdx + 1
      | .rules (.combat (.removedFromCombat eo)) =>
        if eo.id == some oid then return eIdx + 1
        j := j + 1
      | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
        if toZ != .battlefield && before.id == some oid then return eIdx + 1
        j := j + 1
      | .rules (.zone (.ceasedToExist before)) =>
        if before.id == some oid then return eIdx + 1
        j := j + 1
      | .rules (.permanent (.phasedOut before _)) =>
        if before.id == some oid then return eIdx + 1
        j := j + 1
      | _ => j := j + 1
    return eIdx + 1
  if let some eIdx := eventIdx? then
    if h : eIdx < events.size then
      let e := events[eIdx]
      let wTurn := e.turn
      let startIdx := combatPhaseStartIdxAtOrBefore events wTurn (eIdx + 1)
      match e.change with
      | .rules (.zone (.moved before after fromZ toZ _ _ _ _)) =>
        if fromZ == .battlefield && toZ != .battlefield && before.id == some oid then
          let bStart := batchStartAt events wTurn startIdx eIdx e.batch
          return (wTurn, startIdx, bStart, eIdx)
        else if fromZ != .battlefield && toZ == .battlefield && after.id == some oid then
          let mut atkEnd := eIdx + 1
          if let some bid := e.batch then
            while atkEnd < events.size &&
                events[atkEnd]!.turn == wTurn && events[atkEnd]!.batch == some bid do
              atkEnd := atkEnd + 1
          else
            atkEnd := unbatchedAtkEnd wTurn eIdx
          let blkEnd := combatPhaseEndAfter events oid wTurn eIdx
          return (wTurn, startIdx, atkEnd, blkEnd)
      | .rules (.zone (.ceasedToExist before)) =>
        if before.zone == .battlefield && before.id == some oid then
          let bStart := batchStartAt events wTurn startIdx eIdx e.batch
          return (wTurn, startIdx, bStart, eIdx)
      | .rules (.permanent (.phasedOut before _)) =>
        if before.id == some oid then
          let bStart := batchStartAt events wTurn startIdx eIdx e.batch
          return (wTurn, startIdx, bStart, bStart)
      | .rules (.combat (.removedFromCombat eo)) =>
        if eo.id == some oid && eo.attacking then
          let bStart := batchStartAt events wTurn startIdx eIdx e.batch
          return (wTurn, startIdx, bStart, eIdx)
      | .rules (.combat (.attackersDeclared _ decls)) =>
        if decls.any (·.1.id == some oid) then
          let blkEnd := combatPhaseEndAfter events oid wTurn eIdx
          return (wTurn, startIdx, eIdx + 1, blkEnd)
      | .rules (.combat (.becameAttacking atk _)) =>
        if atk.id == some oid then
          let blkEnd := combatPhaseEndAfter events oid wTurn eIdx
          return (wTurn, startIdx, eIdx + 1, blkEnd)
      | .rules (.zone (.created obj _)) =>
        if obj.zone == .battlefield && obj.id == some oid then
          let mut atkEnd := eIdx + 1
          if let some bid := e.batch then
            while atkEnd < events.size &&
                events[atkEnd]!.turn == wTurn && events[atkEnd]!.batch == some bid do
              atkEnd := atkEnd + 1
          else
            atkEnd := unbatchedAtkEnd wTurn eIdx
          let blkEnd := combatPhaseEndAfter events oid wTurn eIdx
          return (wTurn, startIdx, atkEnd, blkEnd)
      | _ => pure ()
  let maxTurn :=
    match eventIdx?.bind (events[·]?) with
    | some e => min defaultTurn e.turn
    | none => defaultTurn
  let scanEnd :=
    match eventIdx? with
    | some eIdx => min events.size (eIdx + 1)
    | none => events.size
  let mut atkDepart : Option (Nat × Option BatchId × Bool) := none
  let mut lastCombatIdx : Option Nat := none
  for i in [0:scanEnd] do
    let e := events[i]!
    if e.turn ≤ maxTurn then
      match e.change with
      | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
        if toZ != .battlefield && before.id == some oid && before.attacking then
          atkDepart := some (i, e.batch, false)
      | .rules (.zone (.ceasedToExist before)) =>
        if before.zone == .battlefield && before.id == some oid && before.attacking then
          atkDepart := some (i, e.batch, false)
      | .rules (.permanent (.phasedOut before _)) =>
        if before.id == some oid && before.attacking then
          atkDepart := some (i, e.batch, true)
      | .rules (.combat (.removedFromCombat eo)) =>
        if eo.id == some oid && eo.attacking then
          atkDepart := some (i, e.batch, false)
      | .rules (.combat (.attackersDeclared _ decls)) =>
        if decls.any (·.1.id == some oid) then
          lastCombatIdx := some i
          atkDepart := none
      | .rules (.combat (.becameAttacking atk _)) =>
        if atk.id == some oid then
          lastCombatIdx := some i
          atkDepart := none
      | .rules (.combat (.becameBlocked atk _)) =>
        if atk.id == some oid then
          lastCombatIdx := some i
          atkDepart := none
      | .rules (.combat (.remainedUnblocked atk)) =>
        if atk.id == some oid then
          lastCombatIdx := some i
          atkDepart := none
      | _ => pure ()
  match atkDepart with
  | some (idx, departBatch, isPhaseOut) =>
    let wTurn := events[idx]!.turn
    let startIdx := combatPhaseStartIdxAtOrBefore events wTurn (idx + 1)
    let bStart := batchStartAt events wTurn startIdx idx departBatch
    let blkEnd := if isPhaseOut then bStart else idx
    return (wTurn, startIdx, bStart, blkEnd)
  | none =>
    match lastCombatIdx with
    | some cIdx =>
      let wTurn := events[cIdx]!.turn
      let startIdx := combatPhaseStartIdxAtOrBefore events wTurn (cIdx + 1)
      let phaseEnd := combatPhaseEndAfter events oid wTurn cIdx
      let blkEnd := if eventIdx?.isSome then min phaseEnd scanEnd else phaseEnd
      let atkEnd :=
        if eventIdx?.isSome && wTurn == maxTurn then min phaseEnd scanEnd
        else cIdx + 1
      return (wTurn, startIdx, atkEnd, blkEnd)
    | none =>
      let startIdx := combatPhaseStartIdxAtOrBefore events maxTurn scanEnd
      return (maxTurn, startIdx, scanEnd, scanEnd)

/-- Whether an LKI attacking creature was attacking alone when it left combat
(CR 506.5 / 608.2h). -/
def lkiAttackingAlone (g : Game) (events : Array GameEvent) (attacking : Bool)
    (oid? : Option ObjectId) (controller? : Option PlayerId)
    (eventIdx? : Option Nat := none) : Bool :=
  if !attacking then false
  else
    let pushUniqId (acc : Array ObjectId) (x : ObjectId) : Array ObjectId :=
      if acc.contains x then acc else acc.push x
    let defaultTurn := g.turnNumber
    let (wTurn, startIdx, endIdx) : Nat × Nat × Nat :=
      match oid? with
      | some oid =>
        let (wt, s, atkEnd, _) := lkiCombatWindow events oid defaultTurn eventIdx?
        (wt, s, atkEnd)
      | none =>
        let wt :=
          match eventIdx?.bind (events[·]?) with
          | some e => e.turn
          | none => defaultTurn
        (wt, combatPhaseStartIdxAtOrBefore events wt events.size, events.size)
    let (attackers, sawSelf) : Array ObjectId × Bool := Id.run do
      let mut active : Array ObjectId := #[]
      let mut foundSelf := false
      for i in [startIdx:endIdx] do
        let e := events[i]!
        if e.turn == wTurn then
          match e.change with
          | .rules (.combat (.attackersDeclared p decls)) =>
            if some p == controller? then
              for (atk, _) in decls do
                if let some aid := atk.id then
                  active := pushUniqId active aid
                  if oid? == some aid then foundSelf := true
          | .rules (.combat (.becameAttacking atk _)) =>
            if atk.controller == controller? then
              if let some aid := atk.id then
                active := pushUniqId active aid
                if oid? == some aid then foundSelf := true
          | .rules (.combat (.removedFromCombat obj)) =>
            if let some rid := obj.id then
              active := active.filter (· != rid)
          | .rules (.permanent (.phasedOut before _)) =>
            if let some pid := before.id then
              active := active.filter (· != pid)
          | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
            if toZ != .battlefield then
              if let some lid := before.id then
                active := active.filter (· != lid)
          | .rules (.zone (.ceasedToExist before)) =>
            if before.zone == .battlefield then
              if let some lid := before.id then
                active := active.filter (· != lid)
          | _ => pure ()
      return (active, foundSelf)
    if sawSelf then
      attackers.size == 1
    else
      let liveOthers :=
        if wTurn == g.turnNumber then
          g.battlefield.filter fun x =>
            x.status.attacking && g.controllerOf x == controller? && some x.id != oid?
        else #[]
      liveOthers.isEmpty && (attackers.filter fun id => some id != oid?).isEmpty

/-- Whether an LKI attacking creature became blocked in the combat phase
containing its departure or phasing out (CR 509.1h / 608.2h). -/
def lkiWasBlocked (g : Game) (events : Array GameEvent) (attacking : Bool)
    (oid? : Option ObjectId) (eventIdx? : Option Nat := none) : Bool :=
  if !attacking then false
  else
    match oid? with
    | none => false
    | some oid =>
      let (wTurn, startIdx, _, endIdx) := lkiCombatWindow events oid g.turnNumber eventIdx?
      Id.run do
        let mut blocked := false
        for i in [startIdx:endIdx] do
          let e := events[i]!
          if e.turn == wTurn then
            match e.change with
            | .rules (.combat (.becameBlocked atk _)) =>
              if atk.id == some oid then blocked := true
            | .rules (.combat (.removedFromCombat obj)) =>
              if obj.id == some oid then blocked := false
            | _ => pure ()
        return blocked

private def staticManaValue (g : Game) (o : GameObject) : Nat :=
  if o.status.faceDown && (o.zone == .battlefield || o.zone == .stack) then 0
  else
    let mc := (g.copiableValues o).manaCost
    if o.zone != .stack then mc.manaValue
    else if o.isLkiSnapshot then
      match o.chosenX with
      | some x => (mc.substituteX x).manaValue
      | none => mc.manaValue
    else
      let x := (o.chosenX.orElse (fun _ => g.chosenXOf? o.id)).getD 0
      (mc.substituteX x).manaValue

private def evalStaticStat? (g : Game) (ptOf? : Option (GameObject → Int × Int))
    (o : GameObject) (sk : StatKind) : Option Int :=
  match sk with
  | .power =>
    let hasStat := g.isCreature o || (o.zone != .battlefield && (g.baseCard o).power.isSome)
    if !hasStat then none
    else if o.isLkiSnapshot then o.printed.powerValue
    else match ptOf? with
      | some f => some (f o).1
      | none =>
        let bc := g.baseCard o
        some (if o.status.faceDown && o.isOnBattlefield then 2 else bc.powerValue.getD 0)
  | .toughness =>
    let hasStat := g.isCreature o || (o.zone != .battlefield && (g.baseCard o).toughness.isSome)
    if !hasStat then none
    else if o.isLkiSnapshot then o.printed.toughnessValue
    else match ptOf? with
      | some f => some (f o).2
      | none =>
        let bc := g.baseCard o
        some (if o.status.faceDown && o.isOnBattlefield then 2 else bc.toughnessValue.getD 0)
  | .manaValue => some (Int.ofNat (g.staticManaValue o))
  | .loyalty =>
    if o.zone == .battlefield && g.isPlaneswalker o then
      some (Int.ofNat o.status.loyaltyCounters)
    else (g.baseCard o).loyalty
  | .defense => ((g.baseCard o).defense).map Int.ofNat

/-- Convert an `EventObject` snapshot from `g.events` into a lightweight LKI `GameObject`
with masked face-down copiable values (CR 708.2a), preserved stack `{X}` mana cost
(CR 107.3a / 202.3e), and frozen Layer-6 snapshot abilities without re-entering
Layers 6–7 (CR 113.7a / 608.2h). -/
def lkiEventObjectAsGameObject (eo : EventObject) (prepared : Option Bool := none) : GameObject :=
  let isFaceDownMasked := eo.faceDown && (eo.zone == .battlefield || eo.zone == .stack)
  let basePrinted : CardDef :=
    if isFaceDownMasked then
      adjustTokenCardDef eo.token
        { name := "", types := #[.creature], power := some (.fixed 2), toughness := some (.fixed 2) }
    else
      let rawCard := (if !isFaceDownMasked then eo.copiable else none).getD eo.toCardDef
      adjustTokenCardDef eo.token rawCard
  let kws := if eo.changeling then KeywordAbility.merge eo.keywords #[Keyword.changeling] else eo.keywords
  let kws := if eo.toxic > 0 && KeywordAbility.toxicTotal kws == 0 then kws.push (.toxic eo.toxic) else kws
  let manaCost : ManaCost :=
    if isFaceDownMasked then ManaCost.empty
    else
      let bcMc := basePrinted.manaCost
      let bcMv :=
        if eo.zone == .stack then (bcMc.substituteX (eo.chosenX.getD 0)).manaValue
        else bcMc.manaValue
      if bcMv == eo.manaValue then bcMc
      else ManaCost.ofGeneric eo.manaValue
  let retains := eo.retainsPrintedAbilities.getD (!isFaceDownMasked)
  let activated : Array ActivatedAbility :=
    match eo.activatedAbilities with
    | some abs => abs
    | none => if isFaceDownMasked || !retains then #[] else basePrinted.allActivatedAbilities
  let printed : CardDef :=
    { basePrinted with
      name := eo.name
      manaCost := manaCost
      colorIndicator := some eo.colors
      types := eo.types
      subtypes := eo.subtypes.map CardSubtype.englishName
      supertypes := eo.supertypes
      power := eo.power.map .fixed
      toughness := eo.toughness.map .fixed
      loyalty := if isFaceDownMasked then none else eo.loyalty.map Int.ofNat
      keywords := kws
      staticAbilities := eo.staticAbilities
      triggeredAbilities := eo.triggeredAbilities
      activatedAbilities := activated
      isToken := eo.token }
  let st := ({} : Status).withCounterBag eo.counters
  { id := eo.id.getD noSourceSentinelId
    printed := printed
    owner := eo.owner
    controller := eo.controller
    defaultController := eo.defaultController.orElse (fun _ => eo.controller)
    zone := eo.zone
    status := {
      st with
      tapped := eo.tapped
      summoningSick := eo.summoningSick
      attacking := eo.attacking
      attackingTarget := eo.attackingTarget
      blocking := eo.blockingIds
      phasedOut := eo.phasedOut
      faceDown := eo.faceDown
      transformed := eo.transformed
      prepared := prepared.getD eo.prepared
      harnessed := eo.harnessed
      goaded := eo.goaded || !eo.goadedBy.isEmpty
      goadedBy := eo.goadedBy
      goadedUntilNextTurnOf := eo.goadedUntilNextTurnOf
      chosenOdd := eo.chosenOdd
      chosenCreatureType := eo.chosenCreatureType
      chosenColor := eo.chosenColor
      chosenName := eo.chosenName
      chosenCardType := eo.chosenCardType
      chosenAnchor := eo.chosenAnchor
    }
    attachedTo := eo.attachedTo
    adventurerCard := eo.adventurerCard
    chosenX := eo.chosenX
    isCopy := eo.isCopy
    isCommander := eo.isCommander
    isLkiSnapshot := true
    lkiLayer6 := some {
      retainsPrintedAbilities := retains
      prowessCount := eo.prowessCount
      ironFistTapGrants := eo.ironFistTapGrants
      wardCosts := eo.wardCosts
      activatedAbilities := activated
      ringBearer := eo.ringBearer
    } }

/-- Whether `sid` last held `.prepared` designation according to the event log
(`none` when no battlefield entry, materialization, or designation event exists
for `sid`, preserving pre-log snapshot `eo.prepared`). -/
def wasPreparedAtDeparture? (g : Game) (sid : ObjectId) : Option Bool :=
  g.events.foldl (fun acc ev =>
    match ev.change with
    | .rules (.zone (.moved before after _ .battlefield _ _ _ _)) =>
      if after.id == some sid then
        some (!after.faceDown &&
          if after.copiable.isSome then after.prepared
          else after.prepared ||
            (after.printed.orElse (fun _ => before.printed) |>.getD after.toCardDef).entersPrepared)
      else acc
    | .rules (.zone (.created obj _)) =>
      if obj.id == some sid && obj.zone == .battlefield then
        some (!obj.faceDown &&
          if obj.copiable.isSome then obj.prepared
          else obj.prepared || (obj.printed.getD obj.toCardDef).entersPrepared)
      else acc
    | .engine (.materializeObject obj _) =>
      if obj.id == sid then
        some (obj.zone == .battlefield && obj.status.prepared)
      else acc
    | .rules (.permanent (.designation eo .prepared gained)) =>
      if eo.id == some sid then some gained else acc
    | _ => acc) none

/-- Whether `sid` last held `.prepared` designation before leaving the battlefield. -/
def wasPreparedAtDeparture (g : Game) (sid : ObjectId) : Bool :=
  (g.wasPreparedAtDeparture? sid).getD false

/-- Reconstruct an LKI `GameObject` from an `EventObject` snapshot so damage
replacement, protection, targeting, and lifelink queries on a departed source
use its last known characteristics and controller (CR 113.7a / 608.2h). -/
def damageSourceObjectFromLki (eo : EventObject) (prepared : Option Bool := none) : GameObject :=
  lkiEventObjectAsGameObject eo (prepared := prepared)

/-- Look up a damage or ability source by `id`: live `GameObject` if still
present (and not phased out), otherwise its `lastKnownBefore?` LKI snapshot
(CR 113.7a / 608.2h / 702.26b). -/
def damageSourceById? (g : Game) (sid : ObjectId) : Option GameObject :=
  (g.findLiveSourceObject? sid).orElse (fun _ =>
    (g.lastKnownBefore? sid).map (fun eo =>
      damageSourceObjectFromLki eo
        (prepared := if eo.copiable.isSome then none else g.wasPreparedAtDeparture? sid)))

private def staticManaUnitsSpentOn (events : Array GameEvent) (oid : ObjectId) : Array ManaUnit :=
  let spellId := GameEvent.stackSpellIdOf events oid
  if GameEvent.isUncastStackCopy events spellId || GameEvent.isUncastStackCopy events oid then #[]
  else
    let bound := GameEvent.castEventBound events spellId
    (events.extract 0 bound).foldl (fun acc e =>
      match e.change, e.cause? with
      | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
        if forObj == some spellId || oid? == some spellId then acc ++ units else acc
      | .rules (.player (.manaSpent _ units forObj)), _ =>
        if forObj == some spellId then acc ++ units else acc
      | _, _ => acc) #[]

private def staticObjectCastFrom (events : Array GameEvent) (oid : ObjectId) (zk : ZoneKind)
    (isCopy : Bool) : Bool :=
  if isCopy then false
  else
    let sid := GameEvent.stackSpellIdOf events oid
    if GameEvent.isUncastStackCopy events sid || GameEvent.isUncastStackCopy events oid then false
    else
      events.any fun e =>
        match e.change with
        | .rules (.cast (.spellCast eo _ fromZ)) =>
          (eo.id == some sid || eo.id == some oid) && fromZ.kind == zk
        | .rules (.cast (.proposed obj _ fromZ way)) =>
          (obj == sid || obj == oid) &&
            (fromZ.kind == zk || (zk == .graveyard && way == .alternative "flashback"))
        | .rules (.zone (.moved _ after fromZ .stack .cast ..)) =>
          (after.id == some sid || after.id == some oid) && fromZ.kind == zk
        | _ => false

/-- Evaluate a `CastContextPred` against `g.events` without re-entering Layers 6–7 (CR 400.7d / 707.10). -/
private def evalStaticCastPred (g : Game) (src : GameObject) (pred : CastContextPred)
    (triggerSubject? : Option GameObject := none) : Bool :=
  let resolveObjs : ObjectRef → Array GameObject
    | .this => #[src]
    | .attachedHost =>
      match (src.attachedTo.bind g.findLiveSourceObject?).orElse
          (fun _ => src.attachedTo.bind (fun hid => (g.lastKnownBefore? hid).map lkiEventObjectAsGameObject)) with
      | some h => #[h]
      | none => #[]
    | .triggerSubject =>
      match triggerSubject? with
      | some s => #[s]
      | none => #[]
    | _ => #[]
  let evalObj (ref : ObjectRef) (f : ObjectId → Bool) : Bool :=
    (resolveObjs ref).any (fun o => f o.id)
  match pred with
  | .wasKicked ref =>
    evalObj ref fun oid =>
      GameEvent.wasKicked g.events oid ||
        (match g.proposedSpell with
         | some prop => prop.spellId == oid && prop.kicked
         | none => false)
  | .giftPromised ref =>
    evalObj ref fun oid =>
      GameEvent.giftPromised g.events oid ||
        (match g.proposedSpell with
         | some prop => prop.spellId == oid && prop.giftTo.isSome
         | none => false)
  | .impendingPaid ref => evalObj ref (GameEvent.castForImpending g.events)
  | .teamworkPaid ref =>
    evalObj ref fun oid =>
      GameEvent.teamwork g.events oid ||
        (match g.proposedSpell with
         | some prop => prop.spellId == oid && prop.teamworkPaid
         | none => false)
  | .sneakPaid ref => evalObj ref fun oid => (GameEvent.sneakAttackTarget? g.events oid).isSome
  | .castFrom zk ref =>
    (resolveObjs ref).any fun o =>
      staticObjectCastFrom g.events o.id zk (o.isCopy || g.hasActiveCopy o)
  | .manaSpentMatches mp ref =>
    evalObj ref fun oid =>
      let units := staticManaUnitsSpentOn g.events oid
      match mp with
      | .fromTreasure =>
        let sid := GameEvent.stackSpellIdOf g.events oid
        !GameEvent.isUncastStackCopy g.events sid && GameEvent.treasureManaSpentOn g.events sid
      | .fromSource =>
        units.any (·.source == some src.id)
      | .ofColor c => units.any (·.mana == .colored c)
      | .amount op n => op.eval (Int.ofNat units.size) (Int.ofNat n)
      | .colorCount op n =>
        let cols := units.foldl (fun acc u =>
          match u.mana with
          | .colored c => if acc.contains c then acc else acc.push c
          | .colorless => acc) (#[] : Array Color)
        op.eval (Int.ofNat cols.size) (Int.ofNat n)
      | .withRider r => units.any (·.hasRider r)

/-- Keyword check for an `isLkiSnapshot` `GameObject` covering frozen keywords,
ward costs, and Equip abilities (CR 608.2h / 702.6a / 702.21). -/
private def staticLkiHasKeyword (target : GameObject) (kw : KeywordTag) : Bool :=
  if KeywordAbility.hasTag target.printed.keywords kw then true
  else
    match kw with
    | .ward =>
      !(target.lkiLayer6.map (·.wardCosts) |>.getD #[]).isEmpty
    | .param .equip =>
      let retains := (target.lkiLayer6.map (·.retainsPrintedAbilities)).getD (!isFaceDownMasked target)
      let acts := (target.lkiLayer6.map (·.activatedAbilities)).getD #[]
      (retains && !isFaceDownMasked target && target.printed.allActivatedAbilities.any (·.isEquip)) ||
        acts.any (·.isEquip)
    | _ => false

mutual

/-- Evaluate `PlayerPred` using Layer 1–5 state plus color, P/T, and keyword callbacks. -/
private partial def evalStaticPlayerPredCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (p : PlayerId) (pred : PlayerPred) (colorOf : GameObject → ColorSet) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  if !g.stillInGame p then false
  else
    let pl := g.player p
    match pred with
    | .any => true
    | .all ps => ps.all (fun q => g.evalStaticPlayerPredCore src srcCtrl p q colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
    | .anyOf ps => ps.any (fun q => g.evalStaticPlayerPredCore src srcCtrl p q colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
    | .not inner => !(g.evalStaticPlayerPredCore src srcCtrl p inner colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
    | .hasDesignation .citysBlessing => pl.citysBlessing
    | .hasDesignation .enduringStory => pl.enduringStory
    | .isMonarch => pl.isMonarch
    | .isActivePlayer => g.activePlayer == p
    | .isDefendingPlayer =>
      let attackerDef? : Option PlayerId :=
        let fromHost :=
          src.attachedTo.bind fun hid =>
            match (g.findLiveSourceObject? hid).orElse
                (fun _ => (g.lastKnownBefore? hid).map lkiEventObjectAsGameObject) with
            | some host => if host.status.attacking then some (g.defendingPlayerOf host) else none
            | none => none
        let fromSelf := if src.status.attacking then some (g.defendingPlayerOf src) else none
        fromHost.orElse fun _ => fromSelf
      match attackerDef? with
      | some dp => dp == p
      | none =>
        let defs := g.defendingPlayers
        if defs.isEmpty then g.defendingPlayer == p else defs.contains p
    | .metric m op rhs =>
      op.eval (g.evalStaticPlayerMetricSingle m p (some (GameEvent.stackSpellIdOf g.events src.id)))
        (g.evalStaticValCore src srcCtrl rhs colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
    | .controls filter minCount =>
      let need := g.evalStaticValCore src srcCtrl minCount colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
      let objs := g.evalStaticObjsCore src p filter.toExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
      let controlled := objs.filter (fun x => g.controllerOf x == some p)
      Int.ofNat controlled.size ≥ need
    | .isSeat idx => p.idx == idx
    | .thatPlayer => true
    | .matchesExpr pe =>
      (g.evalStaticPlayerExprCore src srcCtrl pe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).contains p

/-- Evaluate `PlayerFilter` on a candidate player `p`. -/
private partial def matchStaticPlayerFilterCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (pf : PlayerFilter) (p : PlayerId) (colorOf : GameObject → ColorSet) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  g.matchStaticPlayerRel srcCtrl pf.relation p &&
    g.evalStaticPlayerPredCore src srcCtrl p pf.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

/-- Evaluate `PlayerExpr` to matching players. -/
private partial def evalStaticPlayerExprCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (pe : PlayerExpr) (colorOf : GameObject → ColorSet) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Array PlayerId :=
  let pushUniqPl (acc : Array PlayerId) (p : PlayerId) : Array PlayerId :=
    if acc.contains p then acc else acc.push p
  match pe with
  | .you => if g.stillInGame srcCtrl then #[srcCtrl] else #[]
  | .activePlayer => if g.stillInGame g.activePlayer then #[g.activePlayer] else #[]
  | .defendingPlayer =>
    let attackerDef? : Option PlayerId :=
      let fromHost :=
        src.attachedTo.bind fun hid =>
          match (g.findLiveSourceObject? hid).orElse
              (fun _ => (g.lastKnownBefore? hid).map lkiEventObjectAsGameObject) with
          | some host => if host.status.attacking then some (g.defendingPlayerOf host) else none
          | none => none
      let fromSelf := if src.status.attacking then some (g.defendingPlayerOf src) else none
      fromHost.orElse fun _ => fromSelf
    match attackerDef? with
    | some dp => if g.stillInGame dp then #[dp] else #[]
    | none =>
      let defs := g.defendingPlayers
      if !defs.isEmpty then defs
      else if g.stillInGame g.defendingPlayer then #[g.defendingPlayer] else #[]
  | .monarch => g.players.filterMap fun pl =>
      if g.stillInGame pl.id && pl.isMonarch then some pl.id else none
  | .matching rel pred =>
    (g.staticPlayersMatchingRel srcCtrl rel).filter fun p =>
      g.evalStaticPlayerPredCore src srcCtrl p pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
  | .controllerOf obj =>
    (g.evalStaticObjsCore src srcCtrl obj colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).foldl (fun acc o =>
      match g.controllerOf o with
      | some p => pushUniqPl acc p
      | none => acc) #[]
  | .ownerOf obj =>
    (g.evalStaticObjsCore src srcCtrl obj colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).foldl (fun acc o => pushUniqPl acc o.owner) #[]
  | .target _ | .triggerPlayer _ | .stepPlayers _ | .chosenBy _ _ _ => #[]

/-- Evaluate `ObjectPred` on `target` using Layer 1–5 characteristics (CR 613.1a–e),
plus color callback `colorOf`, optional P/T callback `ptOf?` for `.stat`/`.statParity`
queries, and optional Layer 6 keyword callbacks `kwOf?`/`hasKwExtra?` for `.hasKeyword`
queries (falling back to `baseKeywordsWithCounters` on live objects and frozen
`isLkiSnapshot` state on LKI). -/
private partial def evalStaticPredCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (pred : ObjectPred) (colorOf : GameObject → ColorSet)
    (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  let resolveRefIds : ObjectRef → Array ObjectId
    | .this => #[src.id]
    | .attachedHost =>
      match src.attachedTo with
      | some hid => #[hid]
      | none => #[]
    | .triggerSubject =>
      match triggerSubject? with
      | some s => #[s.id]
      | none => #[]
    | .target _ | .stepVar _ => #[]
  match pred with
  | .all ps => ps.all (fun q => g.evalStaticPredCore src srcCtrl target q colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .any ps => ps.any (fun q => g.evalStaticPredCore src srcCtrl target q colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .not inner => !(g.evalStaticPredCore src srcCtrl target inner colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .hasType t => g.hasType target t
  | .hasSupertype s => g.hasSupertype target s
  | .hasSubtype (.literal s) => g.hasSubtype target s
  | .hasSubtype .chosenOnSource =>
    match src.status.chosenCreatureType with
    | some ty => g.hasSubtype target ty
    | none => false
  | .hasSubtype (.fromStep _) => false
  | .hasColor (.literal c) => (colorOf target).contains c
  | .hasColor .chosenOnSource =>
    match src.status.chosenColor with
    | some c => (colorOf target).contains c
    | none => false
  | .hasColor .commanderIdentity =>
    let pl := g.player srcCtrl
    if !pl.hasCommander then false
    else
      let cols := colorOf target
      Color.all.any fun c => pl.commanderColorIdentity.contains c && cols.contains c
  | .colorCount op n => op.eval (Int.ofNat (colorOf target).count) (Int.ofNat n)
  | .named (.literal nm) => g.name target == nm
  | .named .chosenOnSource => src.status.chosenName == some (g.name target)
  | .hasKeyword kw =>
    if target.isLkiSnapshot then staticLkiHasKeyword target kw
    else
      let kws :=
        match kwOf? with
        | some f => f target
        | none => g.baseKeywordsWithCounters target
      if KeywordAbility.hasTag kws kw then true
      else
        match hasKwExtra? with
        | some f => f target kw
        | none =>
          match kw with
          | .ward => !(KeywordAbility.wardCosts kws).isEmpty
          | .param .equip => !isFaceDownMasked target && (g.baseCard target).allActivatedAbilities.any (·.isEquip)
          | _ => false
  | .stat kind op rhs =>
    match g.evalStaticStat? ptOf? target kind with
    | some n => op.eval n (g.evalStaticValCore src srcCtrl rhs colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
    | none => false
  | .statParity kind parity =>
    match g.evalStaticStat? ptOf? target kind with
    | none => false
    | some val =>
      let isOdd := val.natAbs % 2 == 1
      match parity with
      | .odd => isOdd
      | .even => !isOdd
      | .chosenOnSource =>
        match src.status.chosenOdd with
        | some wantOdd => isOdd == wantOdd
        | none => false
      | .fromStep _ => false
  | .isToken want => target.printed.isToken == want
  | .isFaceDown want => target.status.faceDown == want
  | .isCopy want => (target.isCopy || g.hasActiveCopy target) == want
  | .isCommander => target.isCommander
  | .isKind .card =>
    !target.printed.isToken && !target.isCopy &&
      target.abilityEffect.isNone && target.triggeredAbility.isNone && !(g.types target).isEmpty
  | .isKind .permanentCard =>
    !target.printed.isToken && !target.isCopy &&
      target.abilityEffect.isNone && target.triggeredAbility.isNone && g.isPermanentCard target
  | .isKind .spell =>
    target.zone == .stack && target.abilityEffect.isNone && target.triggeredAbility.isNone &&
      !(g.types target).isEmpty
  | .tapped want => target.status.tapped == want
  | .phasedOut want => target.status.phasedOut == want
  | .combatRole role =>
    match role with
    | .attacking => target.status.attacking
    | .attackingPlayer who =>
      if !target.status.attacking then false
      else
        let ps := g.evalStaticPlayerExprCore src srcCtrl who colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
        match target.status.attackingTarget with
        | some (.player p) => ps.contains p
        | _ => false
    | .attackingAlone =>
      if target.isLkiSnapshot then
        let oid? := if target.id == noSourceSentinelId then none else some target.id
        g.lkiAttackingAlone g.events target.status.attacking oid? (g.controllerOf target) eventIdx?
      else
        target.status.attacking &&
          (g.battlefield.filter (fun x =>
            x.status.attacking && g.controllerOf x == g.controllerOf target)).size == 1
    | .blocking => !target.status.blocking.isEmpty
    | .blockingObject atkExpr =>
      let atkIds := (g.evalStaticObjsCore src srcCtrl atkExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).map (·.id)
      target.status.blocking.any atkIds.contains
    | .blocked =>
      if target.isLkiSnapshot then
        let oid? := if target.id == noSourceSentinelId then none else some target.id
        g.lkiWasBlocked g.events target.status.attacking oid? eventIdx?
      else
        target.status.attacking && target.status.blocked
    | .unblocked =>
      if target.isLkiSnapshot then
        let oid? := if target.id == noSourceSentinelId then none else some target.id
        target.status.attacking && !(g.lkiWasBlocked g.events target.status.attacking oid? eventIdx?)
      else
        target.status.attacking && !target.status.blocked
  | .hasDesignation .prepared => target.status.prepared
  | .hasDesignation .harnessed => target.status.harnessed
  | .hasDesignation .goaded => target.status.goaded || !target.status.goadedBy.isEmpty
  | .hasDesignation .ringBearer =>
    if target.isLkiSnapshot then
      (target.lkiLayer6.map (·.ringBearer)).getD false
    else
      target.isOnBattlefield && !target.status.phasedOut &&
        g.players.any (fun pl => pl.ringBearerId == some target.id && g.controllerOf target == some pl.id)
  | .counterCount k? op rhs =>
    let cnt : Nat :=
      match k? with
      | some k => target.status.counterCount k
      | none => target.status.toCounterBag.foldl (fun a (_, n) => a + n) 0
    op.eval (Int.ofNat cnt) (g.evalStaticValCore src srcCtrl rhs colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .sameAs ref => (resolveRefIds ref).contains target.id
  | .otherThan ref => !(resolveRefIds ref).contains target.id
  | .controlledBy pf =>
    match g.controllerOf target with
    | some c => g.matchStaticPlayerFilterCore src srcCtrl pf c colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    | none => false
  | .ownedBy pf => g.matchStaticPlayerFilterCore src srcCtrl pf target.owner colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
  | .attachedTo hostExpr =>
    let hostIds : Array ObjectId :=
      match hostExpr with
      | .this => #[src.id]
      | _ => (g.evalStaticObjsCore src srcCtrl hostExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).map (·.id)
    match target.attachedTo with
    | some hid => hostIds.contains hid
    | none =>
      if !target.isLkiSnapshot || target.id == noSourceSentinelId then false
      else
        hostIds.any fun hid =>
          !(g.findObject? hid).any (·.isOnBattlefield) &&
            (g.departedOrPhasedOutAttachments? hid).any (fun atts =>
              atts.any (·.id == some target.id))
  | .hasAttachment attFilter =>
    let liveHas :=
      (g.evalStaticObjsCore src srcCtrl attFilter.toExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).any
        (fun att => att.attachedTo == some target.id)
    if liveHas then true
    else if (g.findObject? target.id).any (·.isOnBattlefield) then false
    else if !attFilter.zones.zones.contains .battlefield then false
    else
      -- CR 608.2h / 702.26b,g LKI: departed host unattached in its departure batch
      -- or phased-out host co-phased with attachments in its phase-out batch.
      match g.departedOrPhasedOutAttachments? target.id with
      | none => false
      | some atts =>
        let restrictOwner := attFilter.zones.owner != .any
        let owners : Array PlayerId :=
          match attFilter.zones.owner with
          | .any => #[]
          | .matching pf =>
            (g.staticPlayersMatchingRel srcCtrl pf.relation).filter fun p =>
              g.evalStaticPlayerPredCore src srcCtrl p pf.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
          | .ofPlayer pe => g.evalStaticPlayerExprCore src srcCtrl pe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
        atts.any fun att =>
          let attObj := lkiEventObjectAsGameObject att
          ok attObj && (!restrictOwner || owners.contains att.owner) &&
            g.evalStaticPredCore src srcCtrl attObj
              attFilter.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
  | .targets tgtExpr =>
    let tgts? : Option (Array Target) :=
      match g.stack.find? (·.objectId == target.id) with
      | some entry => some entry.targets
      | none =>
        if target.id == noSourceSentinelId then none
        else GameEvent.lastKnownTargetsOf? g.events target.id
    match tgts? with
    | none => false
    | some tgts =>
      let matchObj (oe : ObjectExpr) : Bool :=
        let ids := (g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).map (·.id)
        tgts.any fun
          | .permanent id | .card id => ids.contains id
          | .player _ => false
      let matchPl (pe : PlayerExpr) : Bool :=
        let pids := g.evalStaticPlayerExprCore src srcCtrl pe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
        tgts.any fun
          | .player p => pids.contains p
          | .permanent _ | .card _ => false
      match tgtExpr with
      | .object oe => matchObj oe
      | .player pe => matchPl pe
      | .either oe pe => matchObj oe || matchPl pe
  | .shares ch withExpr =>
    let others := g.evalStaticObjsCore src srcCtrl withExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let myCols := colorOf target
    let myTypes := g.types target
    let mySubs := g.subtypes target
    others.any fun other =>
      match ch with
      | .color =>
        let oCols := colorOf other
        Color.all.any fun c => myCols.contains c && oCols.contains c
      | .cardType =>
        let oTypes := g.types other
        myTypes.any oTypes.contains
      | .creatureType =>
        let oSubs := g.subtypes other
        mySubs.any fun s => s.isCreatureType && oSubs.contains s
      | .subtype =>
        let oSubs := g.subtypes other
        mySubs.any oSubs.contains
      | .name =>
        let myName := g.name target
        let oName := g.name other
        !myName.isEmpty && myName == oName
  | .wasCast =>
    GameEvent.wasCast g.events target.id (target.isCopy || g.hasActiveCopy target)
  | .castFrom zk =>
    staticObjectCastFrom g.events target.id zk (target.isCopy || g.hasActiveCopy target)
  | .enteredThisTurn => g.loggedEntered target.id
  | .attackedThisTurn => g.declaredAsAttackerThisTurn target.id
  | .dealtDamageThisTurn combatOnly rec? thisTurnOnly =>
    let recMatches (r : DamageRecipient) : Bool :=
      match rec? with
      | none | some .any => true
      | some (.player pf) =>
        match r with
        | .player p => g.matchStaticPlayerFilterCore src srcCtrl pf p colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
        | _ => false
      | some (.object f) =>
        match r with
        | .permanent eo | .battle eo =>
          g.evalStaticPredCore src srcCtrl (lkiEventObjectAsGameObject eo) f.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
        | .player _ => false
      | some (.playerOrObject pf f) =>
        match r with
        | .player p => g.matchStaticPlayerFilterCore src srcCtrl pf p colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
        | .permanent eo | .battle eo =>
          g.evalStaticPredCore src srcCtrl (lkiEventObjectAsGameObject eo) f.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    if thisTurnOnly then
      g.events.any fun e =>
        e.turn == g.turnNumber &&
          match e.change with
          | .rules (.damage (.dealt pkts)) =>
            pkts.any fun pkt =>
              pkt.amount > 0 && pkt.source.id == some target.id &&
                (!combatOnly || pkt.combat) && recMatches pkt.recipient
          | _ => false
    else
      g.events.foldl (fun dealt e =>
        match e.change with
        | .rules (.zone (.moved _ after _ .battlefield ..)) =>
          if after.id == some target.id then false else dealt
        | .rules (.zone (.created obj _)) =>
          if obj.zone == .battlefield && obj.id == some target.id then false else dealt
        | .rules (.damage (.dealt pkts)) =>
          dealt || pkts.any fun pkt =>
            pkt.amount > 0 && pkt.source.id == some target.id &&
              (!combatOnly || pkt.combat) && recMatches pkt.recipient
        | _ => dealt) false
  | .wasDealtDamageThisTurn =>
    (!target.isLkiSnapshot && target.status.damage > 0) ||
      g.events.any fun e =>
        e.turn == g.turnNumber &&
          match e.change with
          | .rules (.damage (.dealt pkts)) =>
            pkts.any fun pkt =>
              pkt.amount > 0 &&
                match pkt.recipient with
                | .permanent eo | .battle eo => eo.id == some target.id
                | .player _ => false
          | _ => false
  | .receivedCounterThisTurn kind? byPlayer? =>
    g.events.any fun e =>
      e.turn == g.turnNumber &&
        e.countersPutInEvent.any fun (eo, kind, n, actor?) =>
          eo.id == some target.id && n > 0 &&
            (match kind? with | none => true | some k => kind == k) &&
            (match byPlayer? with
             | none => true
             | some pf =>
               match actor? with
               | some p => g.matchStaticPlayerFilterCore src srcCtrl pf p colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
               | none =>
                 match eo.controller with
                 | some c => g.matchStaticPlayerFilterCore src srcCtrl pf c colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
                 | none => true)
  | .putIntoGraveyardFromBattlefieldThisTurn =>
    g.events.any fun e =>
      e.turn == g.turnNumber &&
        match e.change with
        | .rules (.zone (.moved _ after .battlefield (.graveyard _) ..)) =>
          after.id == some target.id
        | _ => false
  | .chosenAnchorIs name =>
    target.status.chosenAnchor == some name

/-- Evaluate `ObjectExpr` to matching live `GameObject`s (and LKI attachments for departed/phased-out hosts). -/
private partial def evalStaticObjsCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (expr : ObjectExpr) (colorOf : GameObject → ColorSet) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Array GameObject :=
  let dedupObjs (xs : Array GameObject) : Array GameObject :=
    xs.foldl (fun acc o => if acc.any (·.id == o.id) then acc else acc.push o) #[]
  match expr with
  | .this => #[src]
  | .attachedHost =>
    match (src.attachedTo.bind g.findLiveSourceObject?).orElse
        (fun _ => src.attachedTo.bind (fun hid => (g.lastKnownBefore? hid).map lkiEventObjectAsGameObject)) with
    | some h => #[h]
    | none => #[]
  | .triggerSubject =>
    match triggerSubject? with
    | some s => #[s]
    | none => #[]
  | .inZones zs pred =>
    let allowPhased := staticPredMentionsPhasedOut pred
    let owners : Array PlayerId :=
      match zs.owner with
      | .any => g.players.map (·.id)
      | .matching pf =>
        (g.staticPlayersMatchingRel srcCtrl pf.relation).filter fun p =>
          g.evalStaticPlayerPredCore src srcCtrl p pf.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
      | .ofPlayer pe => g.evalStaticPlayerExprCore src srcCtrl pe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let restrictOwner := zs.owner != .any
    let ownerOk (o : GameObject) : Bool := !restrictOwner || owners.contains o.owner
    let rec staticAttachedToHostExprs : ObjectPred → Array ObjectExpr
      | .attachedTo h => #[h]
      | .all ps => ps.foldl (fun a p => a ++ staticAttachedToHostExprs p) #[]
      | _ => #[]
    let raw : Array GameObject := Id.run do
      let mut out : Array GameObject := #[]
      for zk in zs.zones do
        match zk with
        | .battlefield =>
          let (lkiAtts, lkiAttIds) : Array (EventObject × GameObject) × Array ObjectId :=
            if allowPhased then (#[], #[])
            else Id.run do
              let mut attsOut : Array (EventObject × GameObject) := #[]
              let mut idsOut : Array ObjectId := #[]
              for hostExpr in staticAttachedToHostExprs pred do
                let hostIds :=
                  (g.evalStaticObjsCore src srcCtrl hostExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).map (·.id)
                for hid in hostIds do
                  if !(g.findObject? hid).any (·.isOnBattlefield) then
                    if let some atts := g.departedOrPhasedOutAttachments? hid then
                      for att in atts do
                        let attObj := lkiEventObjectAsGameObject att
                        attsOut := attsOut.push (att, attObj)
                        if let some aid := att.id then
                          if !idsOut.contains aid then
                            idsOut := idsOut.push aid
              return (attsOut, idsOut)
          for o in g.objects do
            if o.zone == .battlefield && (allowPhased || !o.status.phasedOut) &&
                !(o.attachedTo.isNone && lkiAttIds.contains o.id) && ok o && ownerOk o &&
                g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
              out := out.push o
          for (att, attObj) in lkiAtts do
            if ok attObj && ownerOk attObj &&
                !(att.id.isSome && out.any (·.id == attObj.id)) &&
                g.evalStaticPredCore src srcCtrl attObj pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
              out := out.push attObj
        | .graveyard =>
          for p in owners do
            for oid in (g.player p).graveyard do
              if let some o := g.findObject? oid then
                if isDiscardableCard o && g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
                  out := out.push o
        | .hand =>
          for p in owners do
            for oid in (g.player p).hand do
              if let some o := g.findObject? oid then
                if isDiscardableCard o && g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
                  out := out.push o
        | .library =>
          for p in owners do
            for oid in (g.player p).library do
              if let some o := g.findObject? oid then
                if g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
                  out := out.push o
        | .stack =>
          for o in g.objects do
            if o.zone == .stack && ownerOk o &&
                g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
              out := out.push o
        | .exile =>
          for o in g.objects do
            if o.zone == .exile && ownerOk o &&
                g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
              out := out.push o
        | .command =>
          for o in g.objects do
            if o.zone == .command && ownerOk o &&
                g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
              out := out.push o
        | .ante =>
          for o in g.objects do
            if o.zone == .ante && ownerOk o &&
                g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
              out := out.push o
        | .outside =>
          for p in owners do
            for o in g.objects do
              if o.zone == .outside p &&
                  g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
                out := out.push o
      return out
    dedupObjs raw
  | .topOfLibrary ownerExpr countExpr =>
    let n := (g.evalStaticValCore src srcCtrl countExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).toNat
    if n == 0 then #[]
    else
      let owners := g.evalStaticPlayerExprCore src srcCtrl ownerExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
      Id.run do
        let mut out : Array GameObject := #[]
        for p in owners do
          let lib := (g.player p).library
          let takeN := min n lib.size
          for k in [0:takeN] do
            let idx := lib.size - 1 - k
            if let some o := g.findObject? lib[idx]! then
              out := out.push o
        return out
  | .extremum dir metric amongExpr =>
    let pairs := (g.evalStaticObjsCore src srcCtrl amongExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).filterMap fun o =>
      (g.evalStaticStat? ptOf? o metric).map (o, ·)
    match pairs[0]? with
    | none => #[]
    | some (_, firstVal) =>
      let best := pairs.foldl (fun acc (_, x) =>
        match dir with
        | .max => Max.max acc x
        | .min => Min.min acc x) firstVal
      (pairs.filter (·.2 == best)).map Prod.fst
  | .union es =>
    dedupObjs (es.foldl (fun acc e => acc ++ g.evalStaticObjsCore src srcCtrl e colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?) #[])
  | .diff lhs rhs =>
    let rIds := (g.evalStaticObjsCore src srcCtrl rhs colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).map (·.id)
    (g.evalStaticObjsCore src srcCtrl lhs colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).filter (fun o => !rIds.contains o.id)
  | .linkedExile srcExpr =>
    let srcs := g.evalStaticObjsCore src srcCtrl srcExpr colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    dedupObjs (srcs.foldl (fun acc s =>
      (g.allLinkedExilesOf s.id).foldl (fun a eid =>
        match g.findObject? eid with
        | some eo => if eo.zone == .exile then a.push eo else a
        | none => a) acc) #[])
  | .filter inner pred =>
    (g.evalStaticObjsCore src srcCtrl inner colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).filter fun o =>
      g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
  | .targetsOf stackObj =>
    let objs := g.evalStaticObjsCore src srcCtrl stackObj colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    dedupObjs (objs.foldl (fun acc s =>
      let tgts : Array Target :=
        match g.stack.find? (·.objectId == s.id) with
        | some entry => entry.targets
        | none =>
          if s.id == noSourceSentinelId then #[]
          else (GameEvent.lastKnownTargetsOf? g.events s.id).getD #[]
      tgts.foldl (fun a t =>
        match t with
        | .permanent tid | .card tid =>
          match g.damageSourceById? tid with
          | some o => a.push o
          | none => a
        | .player _ => a) acc) #[])
  | .target _ | .allTargets | .stepObjects _ | .costPaidObjects => #[]

/-- Evaluate `ValueExpr` (CR 107.1–2 / 604 / 613), mirroring `EvalExpr.evalValue`
with color callback `colorOf`, optional P/T callback `ptOf?`, and Layer 6 keyword callback `kwOf?`. -/
private partial def evalStaticValCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (v : ValueExpr) (colorOf : GameObject → ColorSet) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Int :=
  match v with
  | .const n => n
  | .chosenX =>
    if src.isLkiSnapshot then Int.ofNat (src.chosenX.getD 0)
    else Int.ofNat ((src.chosenX.orElse (fun _ => GameEvent.chosenXOf? g.events src.id)).getD 0)
  | .objectStat kind oe =>
    match (g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)[0]? with
    | some o => (g.evalStaticStat? ptOf? o kind).getD 0
    | none => 0
  | .counterCount k? oe =>
    match (g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)[0]? with
    | some o =>
      match k? with
      | some k => Int.ofNat (o.status.counterCount k)
      | none => Int.ofNat (o.status.toCounterBag.foldl (fun a (_, n) => a + n) 0)
    | none => 0
  | .aggregate op metric oe =>
    let objs := g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    match op with
    | .count => Int.ofNat objs.size
    | .sum | .max | .min | .countDistinct =>
      let vals : Array Int := objs.filterMap fun o =>
        match metric with
        | .one => some 1
        | .stat sk => g.evalStaticStat? ptOf? o sk
        | .counterCount (some k) => some (Int.ofNat (o.status.counterCount k))
        | .counterCount none => some (Int.ofNat (o.status.toCounterBag.foldl (fun a (_, n) => a + n) 0))
        | .colorCount => some (Int.ofNat (colorOf o).count)
      match op with
      | .sum => vals.foldl (· + ·) 0
      | .max =>
        match vals[0]? with
        | none => 0
        | some v0 => vals.foldl Max.max v0
      | .min =>
        match vals[0]? with
        | none => 0
        | some v0 => vals.foldl Min.min v0
      | .countDistinct =>
        let uniq := vals.foldl (fun acc x => if acc.contains x then acc else acc.push x) (#[] : Array Int)
        Int.ofNat uniq.size
      | .count => Int.ofNat objs.size
  | .basicLandTypeCount oe =>
    let objs := g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let basics : Array CardSubtype := #[.plains, .island, .swamp, .mountain, .forest]
    Int.ofNat (basics.filter (fun b => objs.any (fun o => g.hasSubtype o b))).size
  | .cardTypeCount oe =>
    let objs := g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let seen := objs.foldl (fun acc o =>
      (g.types o).foldl (fun a t => if a.contains t then a else a.push t) acc) (#[] : Array CardType)
    Int.ofNat seen.size
  | .subtypeCount cat oe =>
    let objs := g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let seen := objs.foldl (fun acc o =>
      (g.subtypes o).foldl (fun a sub =>
        if cat.matchesSubtype sub && !a.contains sub then a.push sub else a) acc) (#[] : Array CardSubtype)
    Int.ofNat seen.size
  | .colorCountAmong oe =>
    let objs := g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let mask := objs.foldl (fun acc o => ColorSet.union acc (colorOf o)) ColorSet.empty
    Int.ofNat mask.count
  | .playerMetric m pe =>
    (g.evalStaticPlayerExprCore src srcCtrl pe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).foldl
      (fun acc p => acc + g.evalStaticPlayerMetricSingle m p (some (GameEvent.stackSpellIdOf g.events src.id))) 0
  | .maxControlled who pred =>
    let ps := (g.staticPlayersMatchingRel srcCtrl who.relation).filter fun p =>
      g.evalStaticPlayerPredCore src srcCtrl p who.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    ps.foldl (fun acc p =>
      let cnt := (g.permanentsOf p).foldl (fun n o =>
        if ok o && g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx? then
          n + 1
        else n) 0
      Max.max acc (Int.ofNat cnt)) 0
  | .manaSymbols col? oe =>
    let objs := g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let total : Nat := objs.foldl (fun acc o =>
      let mc :=
        if o.isOnBattlefield && o.status.faceDown then ManaCost.empty
        else (g.copiableValues o).manaCost
      let contrib : Nat :=
        match col? with
        | some c => mc.symbolsIncludingColor c
        | none =>
          mc.symbols.foldl (fun n s =>
            match s with
            | .colored _ | .colorless | .hybrid _ _ | .twobrid _ => n + 1
            | .generic _ | .x => n) 0
      acc + contrib) 0
    Int.ofNat total
  | .manaSpent oe =>
    match (g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)[0]? with
    | none => 0
    | some o => Int.ofNat (staticManaUnitsSpentOn g.events o.id).size
  | .stepMetric _ _ | .eventAmount => 0
  | .binary op a b =>
    op.eval (g.evalStaticValCore src srcCtrl a colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
      (g.evalStaticValCore src srcCtrl b colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)

/-- Evaluate `Condition` using Layer 1–5 state, color callback `colorOf`, optional P/T
callback `ptOf?`, optional Layer 6 keyword callback `kwOf?`, and full `EventHistoryPred` /
`EventPattern` / `CastContextPred` event-log inspection (CR 604 / 613 / 800.4i). -/
private partial def evalStaticCondCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (c : Condition) (colorOf : GameObject → ColorSet)
    (ok : GameObject → Bool := fun _ => true)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  match c with
  | .cmp op a b =>
    op.eval (g.evalStaticValCore src srcCtrl a colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
      (g.evalStaticValCore src srcCtrl b colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .exists oe =>
    !(g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).isEmpty
  | .forAll oe pred =>
    (g.evalStaticObjsCore src srcCtrl oe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?).all
      (fun o => g.evalStaticPredCore src srcCtrl o pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .playerPred pe pred =>
    let ps := g.evalStaticPlayerExprCore src srcCtrl pe colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    !ps.isEmpty && ps.all (fun p => g.evalStaticPlayerPredCore src srcCtrl p pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .castPred cp => g.evalStaticCastPred src cp triggerSubject?
  | .turnHistory hp =>
    let histPlayers (who : PlayerFilter) : Array PlayerId :=
      if who.pred == .any then
        -- CR 800.4i: historical turn events still count players who later left the game.
        g.players.filterMap fun pl =>
          let relOk :=
            match who.relation with
            | .you => pl.id == srcCtrl
            | .opponent => pl.id != srcCtrl && !g.areTeammates srcCtrl pl.id
            | .teammate => g.areTeammates srcCtrl pl.id
            | .anyPlayer => true
          if relOk then some pl.id else none
      else
        (g.staticPlayersMatchingRel srcCtrl who.relation).filter fun p =>
          g.evalStaticPlayerPredCore src srcCtrl p who.pred colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?
    let evalEvPatOnTurn (targetTurn : Nat) (who : PlayerFilter) (pat : EventPattern) : Bool :=
      let ps := histPlayers who
      if ps.isEmpty then false
      else
        let anyPlayer := who == .any
        let matchesCtrl (p? : Option PlayerId) : Bool :=
          match p? with
          | some p => ps.contains p
          | none => anyPlayer
        let lkiMatches (eo : EventObject) (pred : ObjectPred) (eIdx? : Option Nat) : Bool :=
          g.evalStaticPredCore src srcCtrl (lkiEventObjectAsGameObject eo) pred colorOf ok ptOf? kwOf?
            triggerSubject? hasKwExtra? eIdx?
        let anyEvIdx (f : Nat → GameEvent → Bool) : Bool := Id.run do
          for i in [0:g.events.size] do
            let e := g.events[i]!
            if e.turn == targetTurn && f i e then
              return true
          return false
        let anyEv (f : GameEvent → Bool) : Bool :=
          g.events.any fun e => e.turn == targetTurn && f e
        match pat with
        | .permanentEntered pred =>
          anyEvIdx fun i e =>
            match e.change with
            | .rules (.zone (.moved _ after fromZ .battlefield _ _ _ _)) =>
              fromZ != .battlefield && !after.phasedOut &&
                matchesCtrl after.controller && lkiMatches after pred (some i)
            | .rules (.zone (.created obj ctrl)) =>
              obj.zone == .battlefield && !obj.phasedOut &&
                ps.contains (obj.controller.getD ctrl) && lkiMatches obj pred (some i)
            | _ => false
        | .permanentDied pred minCount =>
          let count : Nat := Id.run do
            let mut n : Nat := 0
            for i in [0:g.events.size] do
              let e := g.events[i]!
              if e.turn == targetTurn then
                match e.change with
                | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) =>
                  if !before.phasedOut && matchesCtrl before.controller && lkiMatches before pred (some i) then
                    n := n + 1
                | _ => pure ()
            return n
          count ≥ minCount
        | .permanentLeftBattlefield pred =>
          anyEvIdx fun i e =>
            match e.change with
            | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
              toZ != .battlefield && !before.phasedOut &&
                matchesCtrl before.controller && lkiMatches before pred (some i)
            | .rules (.zone (.ceasedToExist before)) =>
              before.zone == .battlefield && !before.phasedOut &&
                matchesCtrl before.controller && lkiMatches before pred (some i)
            | _ => false
        | .attackedWith pred minCount =>
          ps.any fun p => Id.run do
            let mut count : Nat := 0
            for i in [0:g.events.size] do
              let e := g.events[i]!
              if e.turn == targetTurn then
                match e.change with
                | .rules (.combat (.attackersDeclared q decls)) =>
                  if q == p then
                    for (eo, _) in decls do
                      if lkiMatches eo pred (some i) then count := count + 1
                | _ => pure ()
            return count ≥ minCount
        | .castSpell pred =>
          anyEvIdx fun i e =>
            match e.change with
            | .rules (.cast (.spellCast eo q _)) =>
              ps.contains q && lkiMatches eo pred (some i)
            | _ => false
        | .drewCard minCount =>
          ps.any fun p => GameEvent.draws g.events targetTurn p ≥ minCount
        | .discardedCard pred =>
          anyEvIdx fun i e =>
            match e.change with
            | .rules (.zone (.moved before _ (.hand q) toZ .discard _ _ _)) =>
              ps.contains q && toZ != .hand q && lkiMatches before pred (some i)
            | _ => false
        | .milledCard minCount =>
          ps.any fun p => GameEvent.milled g.events targetTurn p ≥ minCount
        | .gainedLife minAmount =>
          ps.any fun p => GameEvent.lifeGained g.events targetTurn p ≥ minAmount
        | .lostLife minAmount =>
          ps.any fun p => GameEvent.lifeLost g.events targetTurn p ≥ minAmount
        | .dealtDamage combatOnly noncombatOnly =>
          anyEv fun e =>
            match e.change with
            | .rules (.damage (.dealt pkts)) =>
              pkts.any fun pkt =>
                pkt.amount > 0 &&
                  (!combatOnly || pkt.combat) && (!noncombatOnly || !pkt.combat) &&
                  match pkt.recipient with
                  | .player p => ps.contains p
                  | _ => false
            | .rules (.life (.lost q amt true isCombat)) =>
              amt > 0 && ps.contains q &&
                (!combatOnly || isCombat) && (!noncombatOnly || !isCombat)
            | _ => false
        | .activatedLoyalty =>
          ps.any fun p => GameEvent.activatedLoyalty g.events targetTurn p
        | .beheld sub =>
          anyEv fun e =>
            match e.change with
            | .rules (.player (.beheld q s)) => ps.contains q && s == sub
            | _ => false
        | .proliferated =>
          anyEv fun e =>
            match e.change with
            | .rules (.player (.proliferated q _ _)) => ps.contains q
            | _ => false
    match hp with
    | .scriedThisTurn who => (histPlayers who).any (fun p => g.loggedScried p)
    | .surveilledThisTurn who => (histPlayers who).any (fun p => g.loggedSurveilled p)
    | .eventOccurredThisTurn who pat => evalEvPatOnTurn g.turnNumber who pat
    | .eventOccurredLastTurn who pat =>
      if g.turnNumber > 1 then evalEvPatOnTurn (g.turnNumber - 1) who pat else false
    | .firstResolutionThisTurn =>
      if src.id == noSourceSentinelId then true
      else
        !g.events.any fun e =>
          e.turn == g.turnNumber &&
            match e.change with
            | .rules (.stackObject (.resolved _ nth srcId? _)) => nth > 0 && srcId? == some src.id
            | .rules (.player (.optionalOnceActed _ s)) => s == src.id
            | _ => false
    | .nthResolutionThisTurn n =>
      let srcId? := if src.id == noSourceSentinelId then none else some src.id
      let ab? := g.resolvingAbility.bind fun id =>
        (g.findObject? id).bind fun abObj =>
          if abObj.sourceId == srcId? then abObj.triggeredAbility else none
      g.loggedResolutions srcCtrl srcId? ab? == n
    | .optionalOnceUnusedThisTurn =>
      if src.id == noSourceSentinelId then true
      else !g.optionalOnceUsedThisTurn src.id
  | .stepSucceeded _ => false
  | .duringStep s => g.step == s
  | .duringPhase ph => g.step.phase == ph
  | .isYourTurn => g.isOnActiveTeam srcCtrl
  | .isNight => g.isNight
  | .all cs => cs.all (fun sub => g.evalStaticCondCore src srcCtrl sub colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .any cs => cs.any (fun sub => g.evalStaticCondCore src srcCtrl sub colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)
  | .not inner => !(g.evalStaticCondCore src srcCtrl inner colorOf ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?)

end

/-- Check whether `target` matches a static ability's `ObjectFilter` scope (CR 604 / 613),
using color callback `colorOf`. Fast-paths self and attached-host scopes in $O(1)$. -/
private def matchesStaticScopeCore (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (sc : ObjectFilter) (colorOf : GameObject → ColorSet)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none) : Bool :=
  if StaticAbility.isScopeSelf sc then
    target.id == src.id && sc.zones.zones.contains target.zone.kind &&
      (target.zone != .battlefield || !target.status.phasedOut)
  else if StaticAbility.isScopeEquippedCreature sc || StaticAbility.isScopeEnchantedCreature sc then
    target.isOnBattlefield && src.attachedTo == some target.id && g.isCreature target
  else if StaticAbility.isScopeEnchantedPermanent sc then
    target.isOnBattlefield && src.attachedTo == some target.id
  else
    let phaseOk :=
      target.zone != .battlefield || !target.status.phasedOut || staticPredMentionsPhasedOut sc.pred
    let ownerOk :=
      match sc.zones.owner with
      | .any => true
      | .matching pf =>
        g.matchStaticPlayerFilterCore src srcCtrl pf target.owner colorOf (fun _ => true) ptOf? kwOf? none hasKwExtra?
      | .ofPlayer pe =>
        (g.evalStaticPlayerExprCore src srcCtrl pe colorOf (fun _ => true) ptOf? kwOf? none hasKwExtra?).contains target.owner
    sc.zones.zones.contains target.zone.kind && phaseOk && ownerOk &&
      g.evalStaticPredCore src srcCtrl target sc.pred colorOf (fun _ => true) ptOf? kwOf? none hasKwExtra?

-- Layer 5: Full color-changing effect evaluation (CR 613.1e / 613.3 / 613.7 / 613.8)

private structure Layer5Entry where
  idx : Nat
  ts : Nat × Nat
  applies : ColorSet → Bool
  mod : ColorSetMod
deriving Inhabited

private def staticHasColorMod (ab : StaticAbility) : Bool :=
  match ab with
  | .continuous _ _ mod =>
    mod.flatten.any fun
      | .modifyColors _ => true
      | _ => false
  | _ => false

private def evalLayer5Aux (g : Game) : Nat → GameObject → ColorSet
  | peerFuel, o =>
    if o.isLkiSnapshot then o.printed.colors
    else
      let initCols := g.baseColorsL5 o
      let hasActiveCol :=
        g.activeEffects.any fun (_, s) =>
          match s with
          | .layered _ (.colors ..) d => g.durationActive d
          | _ => false
      let hasCopy := g.activeEffects.any fun (_, s) =>
        match s with
        | .layered _ (.copy _) _ => true
        | _ => false
      let hasStaticCol :=
        g.objects.any fun src =>
          (src.isOnBattlefield && !src.status.faceDown &&
            let bc := if hasCopy then g.baseCard src else src.printed
            !bc.staticAbilities.isEmpty && bc.staticAbilities.any fun ab =>
              let hostOnly := match ab with
                | .continuous _ sc _ => StaticAbility.isAttachedHostScope sc
                | _ => false
              (!hostOnly || src.attachedTo == some o.id) && staticHasColorMod ab) ||
          (src.zone == .command && !src.printed.staticAbilities.isEmpty &&
            (if hasCopy then g.baseCard src else src.printed).types.isEmpty &&
            src.printed.staticAbilities.any staticHasColorMod)
      if !hasActiveCol && !hasStaticCol then initCols
      else
        let bc := g.baseCard o
        let peerColorOf (x : GameObject) : ColorSet :=
          if x.isLkiSnapshot then x.printed.colors
          else match peerFuel with
            | fuel' + 1 => evalLayer5Aux g fuel' x
            | 0 => g.baseColorsL5 x
        let scopeMatchesObjScope (sc : ObjectScope) : Bool :=
          match sc with
          | .objects ids => ids.contains o.id
          | .creaturesControlledBy p => o.isOnBattlefield && g.controlledBy o p && g.isCreature o
          | .creaturesWithout kw =>
            o.isOnBattlefield && g.isCreature o && kw.any (fun k => o.status.faceDown || !bc.keywords.contains k)
          | .permanentsOfSubtype p s => o.isOnBattlefield && g.controlledBy o p && g.hasSubtype o s
        let isStrippedL4 (x : GameObject) : Bool :=
          x.isOnBattlefield && (g.evalLayer4Full x).strippedRulesTextByBasicLandSet
        let applyStep (cur : ColorSet) (e : Layer5Entry) : ColorSet :=
          e.mod.apply cur
        Id.run do
          let mut raw : Array Layer5Entry := #[]
          let pushStaticEntries (accIn : Array Layer5Entry) (src : GameObject)
              (srcCtrl : PlayerId) (srcTs : Nat × Nat) (sas : Array StaticAbility) :
              Array Layer5Entry := Id.run do
            let mut acc := accIn
            for ab in sas do
              match ab with
              | .continuous cond? sc mod =>
                if sc.zones.zones.contains o.zone.kind then
                  for m in mod.flatten do
                    match m with
                    | .modifyColors cm =>
                      acc := acc.push {
                        idx := acc.size
                        ts := srcTs
                        applies := fun cur =>
                          let colorFn : GameObject → ColorSet := fun x =>
                            if x.id == o.id then cur else peerColorOf x
                          g.matchesStaticScopeCore src srcCtrl o sc colorFn &&
                            cond?.all (fun c => g.evalStaticCondCore src srcCtrl c colorFn)
                        mod := cm
                      }
                    | _ => pure ()
              | _ => pure ()
            return acc
          if hasStaticCol then
            if o.isOnBattlefield && !o.status.faceDown && !isStrippedL4 o then
              let (oBc, oTs) := g.baseCardWithTs o
              if oBc.staticAbilities.any staticHasColorMod then
                let oTcs := g.evalLayer3 o
                let sas :=
                  if oTcs.isEmpty then oBc.staticAbilities
                  else oBc.staticAbilities.map (TextChange.applyStaticAbility oTcs)
                let oCtrl := (g.controllerOf o).getD o.owner
                raw := pushStaticEntries raw o oCtrl oTs sas
            for src in g.objects do
              if src.isOnBattlefield && src.id != o.id && !src.status.faceDown then
                let srcBc := g.baseCard src
                if srcBc.staticAbilities.any staticHasColorMod && !isStrippedL4 src then
                  let srcTcs := g.evalLayer3 src
                  let sas :=
                    if srcTcs.isEmpty then srcBc.staticAbilities
                    else srcBc.staticAbilities.map (TextChange.applyStaticAbility srcTcs)
                  let srcCtrl := (g.controllerOf src).getD src.owner
                  let (_, baseTs) := g.baseCardWithTs src
                  let srcTs :=
                    if o.isOnBattlefield && src.attachedTo == some o.id then
                      maxTs (g.attachmentTimestamp src o.id) baseTs
                    else baseTs
                  raw := pushStaticEntries raw src srcCtrl srcTs sas
              else if src.zone == .command && (g.baseCard src).types.isEmpty &&
                  src.printed.staticAbilities.any staticHasColorMod then
                let srcCtrl := (g.controllerOf src).getD src.owner
                raw := pushStaticEntries raw src srcCtrl (g.objectEntryTimestamp src)
                  src.printed.staticAbilities
          if hasActiveCol then
            for pos in [0:g.activeEffects.size] do
              let (eid, s) := g.activeEffects[pos]!
              match s with
              | .layered sc (.colors mode cols remCols) d =>
                if g.durationActive d && g.effectPhasingAllows o eid sc d then
                  raw := raw.push {
                    idx := raw.size
                    ts := g.effectTimestamp eid pos
                    applies := fun _ => scopeMatchesObjScope sc
                    mod := { mode := mode, colors := cols, removeColors := remCols }
                  }
              | _ => pure ()
          if raw.isEmpty then return initCols
          let sorted := raw.qsort fun a b =>
            if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
            else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
            else a.idx < b.idx
          let mut rem := sorted
          let mut cur := initCols
          for _ in [0:sorted.size] do
            let applicable := rem.filter (fun e => e.applies cur)
            if applicable.isEmpty then break
            let dependsOn (a b : Layer5Entry) : Bool :=
              a.idx != b.idx &&
                a.applies cur != a.applies (applyStep cur b)
            let chosen :=
              (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
            cur := applyStep cur chosen
            rem := rem.filter (fun e => e.idx != chosen.idx)
          return cur

/-- Evaluated colors of `o` in Layer 5 across active effects and static `.modifyColors`
abilities in CR 613.7 timestamp and CR 613.8 dependency order, after Layer 1 copy/face-down
and Layer 4 CR 305.7 basic-land stripping (CR 202.2 / 305.7 / 612.1 / 613.1e / 613.3 / 708.2a). -/
def colors (g : Game) (o : GameObject) : ColorSet :=
  g.evalLayer5Aux 1 o

/-- Colorless nonland permanent evaluated through Layer 4 and Layer 5 (CR 613.1d–e). -/
def isColorlessNonland (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && !g.isLand o && (g.colors o).isColorless

private def evalStaticPlayerPredL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (p : PlayerId) (pred : PlayerPred) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  g.evalStaticPlayerPredCore src srcCtrl p pred g.colors ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

private def matchStaticPlayerFilterL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (pf : PlayerFilter) (p : PlayerId) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  g.matchStaticPlayerFilterCore src srcCtrl pf p g.colors ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

private def evalStaticPlayerExprL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (pe : PlayerExpr) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Array PlayerId :=
  g.evalStaticPlayerExprCore src srcCtrl pe g.colors ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

private def evalStaticPredL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (pred : ObjectPred) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  g.evalStaticPredCore src srcCtrl target pred g.colors ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

private def evalStaticObjsL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (expr : ObjectExpr) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Array GameObject :=
  g.evalStaticObjsCore src srcCtrl expr g.colors ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

private def evalStaticValL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (v : ValueExpr) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Int :=
  g.evalStaticValCore src srcCtrl v g.colors ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

private def evalStaticCondL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (c : Condition) (ok : GameObject → Bool := fun _ => true)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (triggerSubject? : Option GameObject := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none)
    (eventIdx? : Option Nat := none) : Bool :=
  g.evalStaticCondCore src srcCtrl c g.colors ok ptOf? kwOf? triggerSubject? hasKwExtra? eventIdx?

private def matchesStaticScopeL5 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (sc : ObjectFilter)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (kwOf? : Option (GameObject → Array KeywordAbility) := none)
    (hasKwExtra? : Option (GameObject → KeywordTag → Bool) := none) : Bool :=
  g.matchesStaticScopeCore src srcCtrl target sc g.colors ptOf? kwOf? hasKwExtra?

/-- Three-valued pre-filter for Layer 6 scope predicates: returns `some true` when
`pred` definitely matches `target` regardless of `target`'s Layer 6 keywords,
`some false` when it definitely cannot match, and `none` when it depends on
`target`'s in-progress Layer 6 keywords (including `.hasKeyword` under `.not` / `.any`). -/
private partial def evalStaticPredMaybeTargetKw (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (pred : ObjectPred) (ok : GameObject → Bool)
    (ptOf? : Option (GameObject → Int × Int) := none)
    (peerKwOf? : Option (GameObject → Array KeywordAbility) := none)
    (peerHasKwExtra? : Option (GameObject → KeywordTag → Bool) := none) : Option Bool :=
  match pred with
  | .hasKeyword kw =>
    if target.isLkiSnapshot then some (staticLkiHasKeyword target kw)
    else none
  | .all ps =>
    ps.foldl (fun acc q =>
      match acc with
      | some false => some false
      | _ =>
        match g.evalStaticPredMaybeTargetKw src srcCtrl target q ok ptOf? peerKwOf? peerHasKwExtra? with
        | some false => some false
        | some true => acc
        | none => none) (some true)
  | .any ps =>
    ps.foldl (fun acc q =>
      match acc with
      | some true => some true
      | _ =>
        match g.evalStaticPredMaybeTargetKw src srcCtrl target q ok ptOf? peerKwOf? peerHasKwExtra? with
        | some true => some true
        | some false => acc
        | none => none) (some false)
  | .not inner =>
    (g.evalStaticPredMaybeTargetKw src srcCtrl target inner ok ptOf? peerKwOf? peerHasKwExtra?).map (!·)
  | other =>
    if predMentionsKeyword other then none
    else some (g.evalStaticPredL5 src srcCtrl target other ok ptOf? peerKwOf? none peerHasKwExtra?)

/-- Complete Layer 6 state of a game object (CR 613.1f / 613.7 / 613.8). -/
structure Layer6State where
  retainsBase : Bool := false
  activeGrantedIdx : Array Nat := #[]
  kw : Array KeywordAbility := #[]
  staticsWithTs : Array (StaticAbility × (Nat × Nat)) := #[]
  triggers : Array TriggeredAbility := #[]
  activated : Array ActivatedAbility := #[]
  wards : Array CostSpec := #[]
  prowessCount : Nat := 0
  ironFistCount : Nat := 0
  manaGrants : Array ManaType := #[]
  lanternGrant : Bool := false
  colorlessGrant : Bool := false
deriving Inhabited

private def layer6StateHasExtraKeyword (g : Game) (x : GameObject) (st : Layer6State)
    (kw : KeywordTag) : Bool :=
  match kw with
  | .ward => !st.wards.isEmpty || !(KeywordAbility.wardCosts st.kw).isEmpty
  | .param .equip =>
    (st.retainsBase && !isFaceDownMasked x && (g.baseCard x).allActivatedAbilities.any (·.isEquip)) ||
      st.activated.any (·.isEquip)
  | _ => false

private def isSourceBoundProtection : KeywordAbility → Bool
  | .protection .chosenCardType
  | .protection (.color .chosenOnSource)
  | .protection (.subtype .chosenOnSource)
  | .hexproof (some (.color .chosenOnSource))
  | .hexproof (some (.subtype .chosenOnSource)) => true
  | _ => false

/-- Expand keyword-defined triggered abilities (`exalted`, `decayed`, `myriad`, `undying`)
that do not have separate dedicated trigger pipelines, preserving multiplicity for
cumulative keywords (CR 702.83 / 702.93 / 702.116 / 702.147). -/
private def expandedKeywordTriggers (ks : Array KeywordAbility) : Array TriggeredAbility :=
  ks.foldl (fun acc k =>
    match k with
    | .simple .exalted | .simple .decayed | .simple .myriad | .simple .undying =>
      acc ++ (KeywordAbility.expand k).triggeredAbilities
    | _ => acc) #[]

private def oneShotCauseSourceId? : EventCause → Option ObjectId
  | .oneShotEffect _ src _ => src
  | .replaced _ orig => oneShotCauseSourceId? orig
  | _ => none

private structure Layer6Delta where
  kwDepCheck? : Option (Layer6State → Bool) := none
  rem : AbilityRemoval := .none
  addKw : Array KeywordAbility := #[]
  addStatics : Array StaticAbility := #[]
  addTriggers : Array TriggeredAbility := #[]
  addActivated : Array ActivatedAbility := #[]
  addWards : Array CostSpec := #[]
  addProwess : Nat := 0
  addMana : Array ManaType := #[]
  addLantern : Bool := false
deriving Inhabited

private def Layer6Delta.isEmpty (d : Layer6Delta) : Bool :=
  d.rem == .none && d.addKw.isEmpty && d.addStatics.isEmpty && d.addTriggers.isEmpty &&
    d.addActivated.isEmpty && d.addWards.isEmpty && d.addProwess == 0 &&
    d.addMana.isEmpty && !d.addLantern

/-- Extract Layer 6 deltas (keywords, wards, prowess, granted static/triggered/activated/mana
abilities, graveyard-copied abilities, and ability removal) from a single stratified
`StaticAbility` `ab` on `src` (controlled by `srcCtrl`) as it applies to `target`. -/
private def extractContinuousL6 (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (ab : StaticAbility) (kwOnly : Bool := false)
    (peerKwOf? : Option (GameObject → Array KeywordAbility) := none)
    (peerHasKwExtra? : Option (GameObject → KeywordTag → Bool) := none) : Option Layer6Delta :=
  match ab with
  | .continuous cond? sc mod =>
    let isFastScope :=
      StaticAbility.isScopeSelf sc || StaticAbility.isScopeEquippedCreature sc ||
        StaticAbility.isScopeEnchantedCreature sc || StaticAbility.isScopeEnchantedPermanent sc
    let scopeMayMatch : Option Bool :=
      if isFastScope then
        some (g.matchesStaticScopeL5 src srcCtrl target sc none peerKwOf? peerHasKwExtra?)
      else if !(sc.zones.zones.contains target.zone.kind &&
          (target.zone != .battlefield || !target.status.phasedOut || staticPredMentionsPhasedOut sc.pred)) then
        some false
      else
        let ownerMayMatch : Option Bool :=
          match sc.zones.owner with
          | .any => some true
          | .matching pf =>
            if playerPredMentionsKeyword pf.pred then none
            else some (g.matchStaticPlayerFilterL5 src srcCtrl pf target.owner (fun _ => true) none peerKwOf? none peerHasKwExtra?)
          | .ofPlayer pe =>
            if playerExprMentionsKeyword pe then none
            else some ((g.evalStaticPlayerExprL5 src srcCtrl pe (fun _ => true) none peerKwOf? none peerHasKwExtra?).contains target.owner)
        match ownerMayMatch with
        | some false => some false
        | some true =>
          if predMentionsKeyword sc.pred then
            g.evalStaticPredMaybeTargetKw src srcCtrl target sc.pred (fun _ => true) none peerKwOf? peerHasKwExtra?
          else
            some (g.evalStaticPredL5 src srcCtrl target sc.pred (fun _ => true) none peerKwOf? none peerHasKwExtra?)
        | none =>
          match g.evalStaticPredMaybeTargetKw src srcCtrl target sc.pred (fun _ => true) none peerKwOf? peerHasKwExtra? with
          | some false => some false
          | _ => none
    match scopeMayMatch with
    | some false => none
    | _ =>
      let scopeNeedsDep := scopeMayMatch.isNone
      let condNeedsDep := cond?.any condMentionsKeyword
      let condOkNow :=
        condNeedsDep || cond?.all (fun c => g.evalStaticCondL5 src srcCtrl c (fun _ => true) none peerKwOf? none peerHasKwExtra?)
      if !condOkNow then none
      else
        let kwDep : Option (Layer6State → Bool) :=
          if !scopeNeedsDep && !condNeedsDep then none
          else
            let peerFn := peerKwOf?.getD g.baseKeywordsWithCounters
            let peerExtraFn : GameObject → KeywordTag → Bool :=
              peerHasKwExtra?.getD fun x kw =>
                match kw with
                | .ward => !(KeywordAbility.wardCosts (peerFn x)).isEmpty
                | .param .equip => !isFaceDownMasked x && (g.baseCard x).allActivatedAbilities.any (·.isEquip)
                | _ => false
            some fun curSt =>
              let kwFn : GameObject → Array KeywordAbility := fun x =>
                if x.id == target.id then curSt.kw else peerFn x
              let extraFn : GameObject → KeywordTag → Bool := fun x kw =>
                if x.id == target.id then g.layer6StateHasExtraKeyword target curSt kw
                else peerExtraFn x kw
              (!scopeNeedsDep || g.matchesStaticScopeL5 src srcCtrl target sc none (some kwFn) (some extraFn)) &&
                (!condNeedsDep ||
                  cond?.all (fun c => g.evalStaticCondL5 src srcCtrl c (fun _ => true) none (some kwFn) none (some extraFn)))
        let anyColorMana : Array ManaType :=
          #[.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
        let isLanternScope := sc == StaticAbility.scopeLandsYouControl
        let d := mod.flatten.foldl (fun (acc : Layer6Delta) m =>
          match m with
          | .loseAllAbilities => { acc with rem := .all }
          | .grantKeywords ks =>
            let effKs := resolveProtectionKeywords src ks (dropUnchosen := true)
            if effKs.isEmpty then acc
            else
              let expAct := (KeywordAbility.expandAll effKs).activatedAbilities
              { acc with
                addKw := KeywordAbility.merge acc.addKw effKs
                addTriggers :=
                  if kwOnly then acc.addTriggers
                  else acc.addTriggers ++ expandedKeywordTriggers effKs
                addActivated :=
                  if kwOnly then acc.addActivated ++ expAct.filter (·.isEquip)
                  else acc.addActivated ++ expAct
                addWards := acc.addWards ++ KeywordAbility.wardCosts effKs
                addProwess := if kwOnly then acc.addProwess else acc.addProwess + KeywordAbility.prowessCount effKs }
          | .grantStatic sas =>
            if sas.isEmpty then acc
            else { acc with addStatics := acc.addStatics ++ sas }
          | .grantTriggered trs =>
            if kwOnly || trs.isEmpty then acc
            else { acc with addTriggers := acc.addTriggers ++ trs }
          | .grantActivated abs =>
            if abs.isEmpty then acc
            else if kwOnly then
              let eqAbs := abs.filter (·.isEquip)
              if eqAbs.isEmpty then acc
              else { acc with addActivated := acc.addActivated ++ eqAbs }
            else
              let (mAdd, lAdd) := abs.foldl (fun (ms, lt) act =>
                match act.manaProduction? with
                | some mp =>
                  match mp.spec with
                  | .oneOf .anyColor (.const 1) =>
                    if isLanternScope then (ms, true)
                    else (ms ++ anyColorMana, lt)
                  | .oneOf (.explicit ts) (.const 1) => (ms ++ ts, lt)
                  | .sequence items =>
                    let fixedTs := items.filterMap fun (t, v) =>
                      match v with | .const 1 => some t | _ => none
                    (ms ++ fixedTs, lt)
                  | _ => (ms, lt)
                | none => (ms, lt)) (#[], false)
              { acc with
                addActivated := acc.addActivated ++ abs
                addMana := acc.addMana ++ mAdd
                addLantern := acc.addLantern || lAdd }
          | .copyActivatedFrom filter =>
            if !target.isOnBattlefield then acc
            else
              let copied := (g.evalStaticObjsL5 src srcCtrl filter.toExpr (fun _ => true) none peerKwOf? none peerHasKwExtra?).foldl
                (fun a card =>
                  let acts := (g.baseCard card).allActivatedAbilities
                  a ++ (if kwOnly then acts.filter (·.isEquip) else acts)) #[]
              if copied.isEmpty then acc
              else { acc with addActivated := acc.addActivated ++ copied }
          | _ => acc) ({ kwDepCheck? := kwDep } : Layer6Delta)
        if d.isEmpty then none else some d
  | _ => none

private structure FastStaticEntry where
  idx : Nat
  ts : Nat × Nat
  rem : AbilityRemoval
  add : Array (StaticAbility × (Nat × Nat))
  requiresRetainsBase : Bool := false
  requiresGrantedIdx? : Option Nat := none
  setsGrantedIdx : Bool := false
deriving Inhabited

private def hasAnyStaticLayer6Effect (g : Game) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.abilities add rem) d =>
      g.durationActive d && (rem == .all || !add.staticAbilities.isEmpty)
    | _ => false

private def hasCwStaticLayer6Effect (g : Game) : Bool :=
  g.activeEffects.any fun (_, s) =>
    match s with
    | .layered (.creaturesWithout _) (.abilities add rem) d =>
      g.durationActive d && (rem == .all || !add.staticAbilities.isEmpty)
    | _ => false

/-- True when `ab` either strips abilities or grants a static ability (CR 613.1f). -/
private def staticGrantsOrStripsStatic (ab : StaticAbility) : Bool :=
  match ab with
  | .continuous _ _ mod =>
    modAnyLeaf (fun
      | .loseAllAbilities => true
      | .grantStatic sas => !sas.isEmpty
      | _ => false) mod
  | _ => false

/-- True when `ab` strips abilities via `.loseAllAbilities` (CR 613.1f). -/
private def staticStripsAbilities (ab : StaticAbility) : Bool :=
  match ab with
  | .continuous _ _ mod =>
    modAnyLeaf (fun
      | .loseAllAbilities => true
      | _ => false) mod
  | _ => false

/-- True when `ab` grants or removes keywords or grants/strips abilities in Layer 6 (CR 613.1f). -/
private def staticAffectsKeywords (ab : StaticAbility) : Bool :=
  match ab with
  | .continuous _ _ mod =>
    modAnyLeaf (fun
      | .loseAllAbilities => true
      | .grantKeywords ks => !ks.isEmpty
      | .grantStatic sas => !sas.isEmpty
      | _ => false) mod
  | _ => false

/-- True when `ab` is a `.continuous` static ability scoped solely to the
permanent `src` is attached to (CR 301.5 / 303.4 / 613.1f). -/
private def isAttachedHostStatic : StaticAbility → Bool
  | .continuous _ sc _ => StaticAbility.isAttachedHostScope sc
  | _ => false

/-- True when `o` is a stacked activated or triggered ability (not a spell or permanent). -/
private def isStackAbilityObj (o : GameObject) : Bool :=
  o.zone == .stack && (o.abilityEffect.isSome || o.triggeredAbility.isSome)

/-- True when `ab` is a `.continuous` static ability whose zone scope includes `zk`. -/
private def staticMayAffectZone (zk : ZoneKind) : StaticAbility → Bool
  | .continuous _ sc _ => sc.zones.zones.contains zk
  | _ => false

/-- True when `ab` directly satisfies `pred` or transitively grants (via `.grantStatic`)
a static ability satisfying `pred`. -/
private def staticDirectlyOrTransitivelyMatches (pred : StaticAbility → Bool) :
    Nat → StaticAbility → Bool
  | 0, ab => pred ab
  | fuel + 1, ab =>
    pred ab ||
      match ab with
      | .continuous _ _ mod =>
        modAnyLeaf (fun
          | .grantStatic sas => sas.any (staticDirectlyOrTransitivelyMatches pred fuel)
          | _ => false) mod
      | _ => false

/-- True when `ab` transitively grants (via `.grantStatic`) a static ability matching `pred`. -/
private def staticTransitivelyGrants (pred : StaticAbility → Bool) (fuel : Nat) :
    StaticAbility → Bool
  | .continuous _ _ mod =>
    modAnyLeaf (fun
      | .grantStatic sas => sas.any (staticDirectlyOrTransitivelyMatches pred fuel)
      | _ => false) mod
  | _ => false

/-- True when `ab` on `src` directly matches `pred` for `target` (respecting attached-host
or non-battlefield zone scope) or transitively grants a static ability matching `pred`. -/
private def staticMayAffectTargetLayer6 (src target : GameObject) (pred : StaticAbility → Bool)
    (ab : StaticAbility) : Bool :=
  if target.isOnBattlefield then
    ((src.attachedTo == some target.id || !isAttachedHostStatic ab) && pred ab) ||
      staticTransitivelyGrants pred 3 ab
  else if !isStackAbilityObj target then
    let zk := target.zone.kind
    (staticMayAffectZone zk ab && pred ab) ||
      staticTransitivelyGrants (fun s => staticMayAffectZone zk s && pred s) 3 ab
  else false

private def zoneOwnerMentionsKeyword : ZoneOwnerSpec → Bool
  | .any => false
  | .matching pf => playerPredMentionsKeyword pf.pred
  | .ofPlayer pe => playerExprMentionsKeyword pe

private def isKwDepL6Static : Nat → StaticAbility → Bool
  | 0, _ => false
  | fuel + 1, .continuous cond? sc mod =>
    let mentionsKw :=
      zoneOwnerMentionsKeyword sc.zones.owner || predMentionsKeyword sc.pred ||
        cond?.any condMentionsKeyword
    let affectsL6 :=
      modAnyLeaf (fun
        | .loseAllAbilities => true
        | .grantStatic sas => !sas.isEmpty
        | _ => false) mod
    (mentionsKw && affectsL6) ||
      modAnyLeaf (fun
        | .grantStatic sas => sas.any (isKwDepL6Static fuel)
        | _ => false) mod
  | _, _ => false

/-- True when any battlefield permanent (including `target` itself) or command-zone
emblem has a static ability satisfying `pred` (directly or transitively via `.grantStatic`)
that could apply to `target` in any non-stack-ability zone (CR 114.4 / 613.1f). -/
private def hasPeerOrEmblemStaticLayer6 (g : Game) (target : GameObject)
    (pred : StaticAbility → Bool) (hasCopy? : Option Bool := none) : Bool :=
  if isStackAbilityObj target then false
  else
  let zk := target.zone.kind
  let hasCopy := hasCopy?.getD (g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.copy _) _ => true
    | _ => false)
  g.objects.any fun src =>
    (src.isOnBattlefield && !src.status.faceDown &&
      let bc := if hasCopy then g.baseCard src else src.printed
      !bc.staticAbilities.isEmpty &&
        bc.staticAbilities.any (staticMayAffectTargetLayer6 src target pred)) ||
    (src.zone == .command && !src.printed.staticAbilities.isEmpty &&
      (if hasCopy then g.baseCard src else src.printed).types.isEmpty &&
      src.printed.staticAbilities.any fun ab =>
        if target.isOnBattlefield then
          pred ab || staticTransitivelyGrants pred 3 ab
        else
          (staticMayAffectZone zk ab && pred ab) ||
            staticTransitivelyGrants (fun s => staticMayAffectZone zk s && pred s) 3 ab)

private def hasKwDepAttStatic (g : Game) (o : GameObject) (hasCopy? : Option Bool := none) : Bool :=
  if isStackAbilityObj o then false
  else
  let hasCopy := hasCopy?.getD (g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.copy _) _ => true
    | _ => false)
  let hasEffKwDep :=
    g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.abilities add _) d =>
        g.durationActive d && add.staticAbilities.any (isKwDepL6Static 3)
      | _ => false
  hasEffKwDep ||
    g.objects.any fun src =>
      (src.isOnBattlefield && !src.status.faceDown &&
        let bc := if hasCopy then g.baseCard src else src.printed
        !bc.staticAbilities.isEmpty &&
          bc.staticAbilities.any (isKwDepL6Static 3)) ||
      (src.zone == .command && !src.printed.staticAbilities.isEmpty &&
        (if hasCopy then g.baseCard src else src.printed).types.isEmpty &&
        src.printed.staticAbilities.any (isKwDepL6Static 3))

/-- Fast $O(1)$-peer Layer 6 static-ability evaluator for `x` when no active
`.creaturesWithout` effect or keyword-dependent static strips abilities or adds
static abilities, tracking CR 613.7a / 613.7e ability timestamps
(`max(objectEntryTimestamp, effTs)`) when `needTs` is `true`. -/
private def evalStaticsFast (g : Game) (needTs : Bool)
    (hasEff? : Option Bool := none) (hasBasicLandSet? : Option Bool := none)
    (hasCopy? : Option Bool := none) :
    Nat → GameObject → Array (StaticAbility × (Nat × Nat)) × Bool
  | 0, _ => (#[], false)
  | attFuel + 1, x =>
    let hasCopy := hasCopy?.getD (g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.copy _) _ => true
      | _ => false)
    let hasEff := hasEff?.getD g.hasAnyStaticLayer6Effect
    let hasBasicLandSet := hasBasicLandSet?.getD g.hasActiveBasicLandSetEffect
    let strippedByL4 :=
      x.isOnBattlefield && hasBasicLandSet &&
        (g.evalLayer4Full x).strippedRulesTextByBasicLandSet
    let hasRelevantAtt :=
      x.isOnBattlefield &&
        g.objects.any fun att =>
          att.isOnBattlefield && att.attachedTo == some x.id && att.id != x.id &&
            (hasEff || (!att.status.faceDown &&
              let attBc := if hasCopy then g.baseCard att else att.printed
              !attBc.staticAbilities.isEmpty && attBc.staticAbilities.any staticGrantsOrStripsStatic))
    let hasPeerOrEmb :=
      !isStackAbilityObj x &&
        g.hasPeerOrEmblemStaticLayer6 x staticGrantsOrStripsStatic (some hasCopy)
    let hasOwnGrantOrStrip :=
      x.isOnBattlefield && !isFaceDownMasked x && !strippedByL4 &&
        (let xBc0 := if hasCopy then g.baseCard x else x.printed
         !xBc0.staticAbilities.isEmpty && xBc0.staticAbilities.any staticGrantsOrStripsStatic)
    if !hasEff && !hasRelevantAtt && !hasPeerOrEmb && !hasOwnGrantOrStrip then
      if isFaceDownMasked x || strippedByL4 then (#[], false)
      else
        let (xBc, xBaseTs) := if needTs then g.baseCardWithTs x else (g.baseCard x, (0, 0))
        if xBc.staticAbilities.isEmpty then (#[], true)
        else
          let xTcs := g.evalLayer3 x
          (xBc.staticAbilities.map (fun ab => (TextChange.applyStaticAbility xTcs ab, xBaseTs)), true)
    else
      let xIsStripped := isFaceDownMasked x || strippedByL4
      let (xBc, xBaseTs) := if xIsStripped then (g.baseCard x, (0, 0)) else g.baseCardWithTs x
      let xObjTs := g.objectEntryTimestamp x
      let xCtrl := g.controllerOf x |>.getD x.owner
      let initStatics : Array (StaticAbility × (Nat × Nat)) :=
        if xIsStripped || xBc.staticAbilities.isEmpty then #[]
        else
          let xTcs := g.evalLayer3 x
          xBc.staticAbilities.map (fun ab => (TextChange.applyStaticAbility xTcs ab, xBaseTs))
      let initL6St : Layer6State :=
        if xIsStripped then
          let ckws := keywordCounterAbilities x
          { kw := ckws, wards := KeywordAbility.wardCosts ckws }
        else
          let kws := g.baseKeywordsWithCounters x
          { retainsBase := true, kw := kws, wards := KeywordAbility.wardCosts kws,
            activated := xBc.allActivatedAbilities }
      let peerL6Fallback (y : GameObject) : Layer6State :=
        let yStripped := y.isOnBattlefield && hasBasicLandSet &&
          (g.evalLayer4Full y).strippedRulesTextByBasicLandSet
        if isFaceDownMasked y || yStripped then
          let ckws := keywordCounterAbilities y
          { kw := ckws, wards := KeywordAbility.wardCosts ckws }
        else
          let kws := g.baseKeywordsWithCounters y
          { retainsBase := true
            kw := kws
            wards := KeywordAbility.wardCosts kws
            activated := (g.baseCard y).allActivatedAbilities.filter (·.isEquip) }
      let peerKwOf (y : GameObject) : Array KeywordAbility :=
        if y.isLkiSnapshot then resolveProtectionKeywords y y.printed.keywords (dropUnchosen := false)
        else (peerL6Fallback y).kw
      let peerHasKwExtra (y : GameObject) (kw : KeywordTag) : Bool :=
        match kw with
        | .ward | .param .equip =>
          if y.isLkiSnapshot then staticLkiHasKeyword y kw
          else g.layer6StateHasExtraKeyword y (peerL6Fallback y) kw
        | _ => false
      let scopeOk (sc : ObjectScope) : Bool :=
        match sc with
        | .objects ids => ids.contains x.id
        | .creaturesControlledBy p => x.isOnBattlefield && g.controlledBy x p && g.isCreature x
        | .creaturesWithout kw =>
          x.isOnBattlefield && g.isCreature x && kw.any (fun k => !initL6St.kw.contains k)
        | .permanentsOfSubtype p s => x.isOnBattlefield && g.controlledBy x p && g.hasSubtype x s
      let hasTransitiveGrantStatic : Bool :=
        g.objects.any fun src =>
          (src.isOnBattlefield && !src.status.faceDown &&
            let srcBc := if hasCopy then g.baseCard src else src.printed
            !srcBc.staticAbilities.isEmpty &&
              srcBc.staticAbilities.any (staticTransitivelyGrants staticGrantsOrStripsStatic 3)) ||
          (src.zone == .command && !src.printed.staticAbilities.isEmpty &&
            (if hasCopy then g.baseCard src else src.printed).types.isEmpty &&
            src.printed.staticAbilities.any (staticTransitivelyGrants staticGrantsOrStripsStatic 3))
      let hasGrantedPeerL6Static :=
        hasTransitiveGrantStatic ||
          (hasEff && g.activeEffects.any fun (_, s) =>
            match s with
            | .layered _ (.abilities add _) d =>
              g.durationActive d &&
                add.staticAbilities.any (staticDirectlyOrTransitivelyMatches staticGrantsOrStripsStatic 3)
            | _ => false)
      let rec pushFast : Nat → Array FastStaticEntry → (Nat × Nat) →
          AbilityRemoval → Array StaticAbility → Bool → Option Nat →
          Array FastStaticEntry
        | depth, raw, ts, rem, addStatics, requiresRetainsBase, requiresGrantedIdx? =>
          let selfDeltas : Array Layer6Delta :=
            match depth with
            | 0 => #[]
            | _ + 1 =>
              if !x.isOnBattlefield || addStatics.isEmpty then #[]
              else
                addStatics.filterMap fun ab =>
                  if staticGrantsOrStripsStatic ab then
                    match g.extractContinuousL6 x xCtrl x ab false (some peerKwOf) (some peerHasKwExtra) with
                    | some dl =>
                      if dl.kwDepCheck?.all (fun f => f initL6St) &&
                          (dl.rem == .all || !dl.addStatics.isEmpty) then
                        some dl
                      else none
                    | none => none
                  else none
          let grantIdx := raw.size
          let grantTs := maxTs xObjTs ts
          let hasSelf := !selfDeltas.isEmpty
          let raw := raw.push {
            idx := grantIdx
            ts := ts
            rem := rem
            add := addStatics.map (·, grantTs)
            requiresRetainsBase := requiresRetainsBase
            requiresGrantedIdx? := requiresGrantedIdx?
            setsGrantedIdx := hasSelf
          }
          match depth with
          | 0 => raw
          | depth' + 1 =>
            if hasSelf then
              selfDeltas.foldl (fun acc dl =>
                pushFast depth' acc ts dl.rem dl.addStatics false (some grantIdx)) raw
            else raw
      Id.run do
        let mut raw : Array FastStaticEntry := #[]
        if x.isOnBattlefield && !initStatics.isEmpty then
          for (ab, abTs) in initStatics do
            if staticGrantsOrStripsStatic ab then
              if let some d := g.extractContinuousL6 x xCtrl x ab false (some peerKwOf) (some peerHasKwExtra) then
                if d.kwDepCheck?.all (fun f => f initL6St) &&
                    (d.rem == .all || !d.addStatics.isEmpty) then
                  raw := pushFast 3 raw abTs d.rem d.addStatics true none
        if x.isOnBattlefield && (hasRelevantAtt || hasPeerOrEmb || hasGrantedPeerL6Static) then
          for src in g.objects do
            if src.isOnBattlefield && src.id != x.id then
              let srcBc := if hasCopy then g.baseCard src else src.printed
              if src.attachedTo == some x.id then
                if hasGrantedPeerL6Static ||
                    (!src.status.faceDown && !srcBc.staticAbilities.isEmpty &&
                      srcBc.staticAbilities.any staticGrantsOrStripsStatic) then
                  let (attAbs, _) := evalStaticsFast g true (some hasEff) (some hasBasicLandSet) (some hasCopy) attFuel src
                  let attTs := g.attachmentTimestamp src x.id
                  let attCtrl := g.controllerOf src |>.getD src.owner
                  for (ab, abTs) in attAbs do
                    if let some d := g.extractContinuousL6 src attCtrl x ab false (some peerKwOf) (some peerHasKwExtra) then
                      if d.kwDepCheck?.all (fun f => f initL6St) &&
                          (d.rem == .all || !d.addStatics.isEmpty) then
                        raw := pushFast 3 raw (maxTs attTs abTs) d.rem d.addStatics false none
              else if hasGrantedPeerL6Static ||
                  (!src.status.faceDown && !srcBc.staticAbilities.isEmpty &&
                    srcBc.staticAbilities.any (fun ab => !isAttachedHostStatic ab && staticGrantsOrStripsStatic ab)) then
                let (srcAbs, _) := evalStaticsFast g true (some hasEff) (some hasBasicLandSet) (some hasCopy) attFuel src
                let srcCtrl := g.controllerOf src |>.getD src.owner
                for (ab, abTs) in srcAbs do
                  if let some d := g.extractContinuousL6 src srcCtrl x ab false (some peerKwOf) (some peerHasKwExtra) then
                    if d.kwDepCheck?.all (fun f => f initL6St) &&
                        (d.rem == .all || !d.addStatics.isEmpty) then
                      raw := pushFast 3 raw abTs d.rem d.addStatics false none
            else if src.zone == .command && !src.printed.staticAbilities.isEmpty &&
                (if hasCopy then g.baseCard src else src.printed).types.isEmpty &&
                src.printed.staticAbilities.any staticGrantsOrStripsStatic then
              let embCtrl := g.controllerOf src |>.getD src.owner
              let embTs := g.objectEntryTimestamp src
              for ab in src.printed.staticAbilities do
                if let some d := g.extractContinuousL6 src embCtrl x ab false (some peerKwOf) (some peerHasKwExtra) then
                  if d.kwDepCheck?.all (fun f => f initL6St) &&
                      (d.rem == .all || !d.addStatics.isEmpty) then
                    raw := pushFast 3 raw embTs d.rem d.addStatics false none
        else if !x.isOnBattlefield && !isStackAbilityObj x && (hasPeerOrEmb || hasGrantedPeerL6Static) then
          let zk := x.zone.kind
          for src in g.objects do
            if src.isOnBattlefield then
              let srcBc := if hasCopy then g.baseCard src else src.printed
              if hasGrantedPeerL6Static ||
                  (!src.status.faceDown && !srcBc.staticAbilities.isEmpty &&
                    srcBc.staticAbilities.any (fun ab => staticMayAffectZone zk ab && staticGrantsOrStripsStatic ab)) then
                let (srcAbs, _) := evalStaticsFast g true (some hasEff) (some hasBasicLandSet) (some hasCopy) attFuel src
                let srcCtrl := g.controllerOf src |>.getD src.owner
                for (ab, abTs) in srcAbs do
                  if staticMayAffectZone zk ab then
                    if let some d := g.extractContinuousL6 src srcCtrl x ab false (some peerKwOf) (some peerHasKwExtra) then
                      if d.kwDepCheck?.all (fun f => f initL6St) &&
                          (d.rem == .all || !d.addStatics.isEmpty) then
                        raw := pushFast 3 raw abTs d.rem d.addStatics false none
            else if src.zone == .command && !src.printed.staticAbilities.isEmpty &&
                (if hasCopy then g.baseCard src else src.printed).types.isEmpty &&
                src.printed.staticAbilities.any (fun ab => staticMayAffectZone zk ab && staticGrantsOrStripsStatic ab) then
              let embCtrl := g.controllerOf src |>.getD src.owner
              let embTs := g.objectEntryTimestamp src
              for ab in src.printed.staticAbilities do
                if staticMayAffectZone zk ab then
                  if let some d := g.extractContinuousL6 src embCtrl x ab false (some peerKwOf) (some peerHasKwExtra) then
                    if d.kwDepCheck?.all (fun f => f initL6St) &&
                        (d.rem == .all || !d.addStatics.isEmpty) then
                      raw := pushFast 3 raw embTs d.rem d.addStatics false none
        for pos in [0:g.activeEffects.size] do
          let (eid, s) := g.activeEffects[pos]!
          match s with
          | .layered sc (.abilities add rem) d =>
            if scopeOk sc && g.durationActive d && g.effectPhasingAllows x eid sc d &&
                (rem == .all || !add.staticAbilities.isEmpty) then
              let effTs := g.effectTimestamp eid pos
              raw := pushFast 3 raw effTs rem add.staticAbilities false none
          | _ => pure ()
        let sorted := raw.qsort fun a b =>
          if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
          else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
          else a.idx < b.idx
        let mut acc := initStatics
        let mut retains := !xIsStripped
        let mut activeGrantedIdx : Array Nat := #[]
        for e in sorted do
          if (!e.requiresRetainsBase || retains) &&
              (match e.requiresGrantedIdx? with
               | some gi => activeGrantedIdx.contains gi
               | none => true) then
            if e.rem == .all then
              acc := #[]
              retains := false
              activeGrantedIdx := #[]
            if e.setsGrantedIdx then
              activeGrantedIdx := activeGrantedIdx.push e.idx
            acc := acc ++ e.add
        return (acc, retains)

private inductive L6TsSource where
  | fixed (ts : Nat × Nat)
  | base
  | counter (k : CounterKind)
  | attachBase (att : GameObject)
  | peerBase (src : GameObject)
  | objEntry (emb : GameObject)
  | eff (eid : EffectId) (pos : Nat)
deriving Inhabited

private structure Layer6UnifiedEntry where
  idx : Nat
  ts : Nat × Nat := (0, 0)
  scope : ObjectScope := .objects #[]
  kwDepCheck? : Option (Layer6State → Bool) := none
  requiresRetainsBase : Bool := false
  requiresGrantedIdx? : Option Nat := none
  setsGrantedIdx : Bool := false
  rem : AbilityRemoval := .none
  addKw : Array KeywordAbility := #[]
  addStaticsRaw : Array StaticAbility := #[]
  addStatics : Array (StaticAbility × (Nat × Nat)) := #[]
  addTriggers : Array TriggeredAbility := #[]
  addActivated : Array ActivatedAbility := #[]
  addWards : Array CostSpec := #[]
  addProwess : Nat := 0
  addIronFist : Nat := 0
  addMana : Array ManaType := #[]
  addLantern : Bool := false
  addColorlessGrant : Bool := false
deriving Inhabited

/-- Shared single-pass Layer 6 evaluator across keywords, static abilities,
triggered abilities, prowess, combat-Treasure grants, Iron Fist tap grants,
ward costs, graveyard-copied / loyalty activated abilities, and mana grants,
ordered by CR 613.7 / 613.7a / 613.7e timestamps and CR 613.8 dependencies. -/
private def evalLayer6Aux (g : Game) (needStaticsTs kwOnly : Bool) : Nat → GameObject → Layer6State
  | peerFuel, o =>
    if o.isLkiSnapshot then
      let ts := if needStaticsTs then g.objectEntryTimestamp o else (0, 0)
      let retains := (o.lkiLayer6.map (·.retainsPrintedAbilities)).getD (!isFaceDownMasked o)
      let acts :=
        match o.lkiLayer6 with
        | some l6 => l6.activatedAbilities
        | none => if isFaceDownMasked o then #[] else o.printed.allActivatedAbilities
      { retainsBase := retains
        kw := resolveProtectionKeywords o o.printed.keywords (dropUnchosen := false)
        staticsWithTs := if kwOnly then #[] else o.printed.staticAbilities.map (·, ts)
        triggers := if kwOnly then #[] else o.printed.triggeredAbilities
        activated := if kwOnly then acts.filter (·.isEquip) else acts
        wards := (o.lkiLayer6.map (·.wardCosts)).getD #[]
        prowessCount := if kwOnly then 0 else (o.lkiLayer6.map (·.prowessCount)).getD 0
        ironFistCount := if kwOnly then 0 else (o.lkiLayer6.map (·.ironFistTapGrants)).getD 0
        manaGrants := #[]
        lanternGrant := false
        colorlessGrant := false }
    else
    let pushUniqMana (acc xs : Array ManaType) : Array ManaType :=
      xs.foldl (fun a t => if a.contains t then a else a.push t) acc
    let peerL6Of (x : GameObject) : Layer6State :=
      match peerFuel with
      | fuel' + 1 => evalLayer6Aux g false true fuel' x
      | 0 =>
        let stripped := x.isOnBattlefield && g.hasActiveBasicLandSetEffect &&
          (g.evalLayer4Full x).strippedRulesTextByBasicLandSet
        if isFaceDownMasked x || stripped then
          let ckws := keywordCounterAbilities x
          { kw := ckws, wards := KeywordAbility.wardCosts ckws }
        else
          let kws := g.baseKeywordsWithCounters x
          { retainsBase := true
            kw := kws
            wards := KeywordAbility.wardCosts kws
            activated := (g.baseCard x).allActivatedAbilities.filter (·.isEquip) }
    let peerKwOf (x : GameObject) : Array KeywordAbility :=
      if x.isLkiSnapshot then resolveProtectionKeywords x x.printed.keywords (dropUnchosen := false)
      else match peerFuel with
        | fuel' + 1 => (evalLayer6Aux g false true fuel' x).kw
        | 0 => (peerL6Of x).kw
    let peerHasKwExtra (x : GameObject) (kw : KeywordTag) : Bool :=
      match kw with
      | .ward | .param .equip =>
        if x.isLkiSnapshot then staticLkiHasKeyword x kw
        else g.layer6StateHasExtraKeyword x (peerL6Of x) kw
      | _ => false
    let grantedColorlessTwoAct : ActivatedAbility :=
      ActivatedAbility.manaAbility (.fixed #[.colorless, .colorless])
    let (bc, initBaseTs) :=
      if needStaticsTs then g.baseCardWithTs o else (g.baseCard o, (0, 0))
    let oTcs := g.evalLayer3 o
    let ctrl? := g.controllerOf o
    let oCtrl := ctrl?.getD o.owner
    let l4 := if o.isOnBattlefield then g.evalLayer4Full o else
      let (ts, subs, sups) := g.evalLayer4 o
      { types := ts, subtypes := subs, supertypes := sups }
    let oIsCreature := o.isOnBattlefield && l4.types.contains .creature
    let oIsLand := !kwOnly && o.isOnBattlefield && l4.types.contains .land
    let strippedByL4 := o.isOnBattlefield && l4.strippedRulesTextByBasicLandSet
    -- CR 305.6: A land on the battlefield with a basic land type has the intrinsic
    -- mana ability `{T}: Add {color}` for each of its basic land types.
    let intrinsicLandMana : Array ActivatedAbility :=
      if oIsLand then
        l4.subtypes.filterMap fun sub =>
          sub.basicLandManaColor?.map ActivatedAbility.intrinsicBasicLandMana
      else #[]
    let mappedOwnStatics : Array StaticAbility :=
      if isFaceDownMasked o || strippedByL4 || bc.staticAbilities.isEmpty then #[]
      else if oTcs.isEmpty then bc.staticAbilities
      else bc.staticAbilities.map (TextChange.applyStaticAbility oTcs)
    let ownSelfDeltas : Array Layer6Delta :=
      if !o.isOnBattlefield || mappedOwnStatics.isEmpty then #[]
      else
        mappedOwnStatics.filterMap fun ab =>
          g.extractContinuousL6 o oCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra)
    let initState : Layer6State :=
      if isFaceDownMasked o || strippedByL4 then
        if kwOnly then {}
        else { activated := intrinsicLandMana }
      else
        let printedKw : Array KeywordAbility :=
          let rawKw :=
            if oTcs.isEmpty then bc.keywords
            else HasTextChange.applyTextChanges oTcs bc.keywords
          resolveProtectionKeywords o rawKw (dropUnchosen := false)
        if kwOnly then
          { retainsBase := true
            kw := printedKw
            wards := KeywordAbility.wardCosts printedKw }
        else
          let ownAct : Array ActivatedAbility :=
            if oTcs.isEmpty then bc.activatedAbilities
            else bc.activatedAbilities.map (TextChange.applyActivatedAbility oTcs)
          let expandedKwAct : Array ActivatedAbility :=
            (KeywordAbility.expandAll printedKw).activatedAbilities.filter fun ab =>
              !ownAct.contains ab
          let dedupIntrinsicLandMana : Array ActivatedAbility :=
            intrinsicLandMana.filter fun ab => !ownAct.contains ab
          let impTrig : Array TriggeredAbility :=
            if bc.impending.isSome then #[TriggeredAbility.impendingEndStep]
            else #[]
          { retainsBase := true
            kw := printedKw
            staticsWithTs :=
              if mappedOwnStatics.isEmpty then #[] else mappedOwnStatics.map (·, initBaseTs)
            triggers :=
              let rawPrintedTrigs :=
                if bc.isMarduOrJeskaiChoice && o.status.chosenAnchor != some "Jeskai" then
                  bc.triggeredAbilities.filter fun ab =>
                    match ab.effect.body with
                    | .ifCond (.exists (.filter .this (.chosenAnchorIs "Jeskai"))) _ _ => false
                    | _ => true
                else bc.triggeredAbilities
              (if oTcs.isEmpty then rawPrintedTrigs
               else rawPrintedTrigs.map (TextChange.applyTriggeredAbility oTcs)) ++
                impTrig ++ expandedKeywordTriggers printedKw
            activated :=
              ownAct ++
                expandedKwAct ++
                dedupIntrinsicLandMana
            wards := KeywordAbility.wardCosts printedKw
            prowessCount := KeywordAbility.prowessCount printedKw }
    let hasCopy := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.copy _) _ => true
      | _ => false
    let hasBasicLandSet := g.hasActiveBasicLandSetEffect
    let hasCwStaticEff := g.hasCwStaticLayer6Effect
    let hasStaticEff := g.hasAnyStaticLayer6Effect
    let hasKwDep :=
      if hasCwStaticEff then false
      else g.hasKwDepAttStatic o (some hasCopy)
    let peerStaticsWithTs (x : GameObject) : Array (StaticAbility × (Nat × Nat)) × Bool :=
      match peerFuel with
      | fuel' + 1 =>
        if hasCwStaticEff || (!isStackAbilityObj x && hasKwDep) then
          let st := evalLayer6Aux g true false fuel' x
          (st.staticsWithTs, st.retainsBase)
        else evalStaticsFast g true (some hasStaticEff) (some hasBasicLandSet) (some hasCopy) 4 x
      | 0 => evalStaticsFast g true (some hasStaticEff) (some hasBasicLandSet) (some hasCopy) 4 x
    let peerStaticsNoTs (x : GameObject) : Array (StaticAbility × (Nat × Nat)) × Bool :=
      match peerFuel with
      | fuel' + 1 =>
        if hasCwStaticEff || (!isStackAbilityObj x && hasKwDep) then
          let st := evalLayer6Aux g false false fuel' x
          (st.staticsWithTs, st.retainsBase)
        else evalStaticsFast g false (some hasStaticEff) (some hasBasicLandSet) (some hasCopy) 4 x
      | 0 => evalStaticsFast g false (some hasStaticEff) (some hasBasicLandSet) (some hasCopy) 4 x
    let scopeMatchesL6 (cur : Layer6State) (sc : ObjectScope) : Bool :=
      match sc with
      | .objects ids => ids.contains o.id
      | .creaturesControlledBy p => oIsCreature && g.controlledBy o p
      | .creaturesWithout kw =>
        oIsCreature && kw.any (fun k => !cur.kw.contains k)
      | .permanentsOfSubtype p s => o.isOnBattlefield && g.controlledBy o p && g.hasSubtype o s
    let entryApplies (cur : Layer6State) (e : Layer6UnifiedEntry) : Bool :=
      (!e.requiresRetainsBase || cur.retainsBase) &&
      (match e.requiresGrantedIdx? with
       | some gi => cur.activeGrantedIdx.contains gi
       | none => true) &&
      (match e.kwDepCheck? with | some f => f cur | none => true) &&
      scopeMatchesL6 cur e.scope
    let applyStep (cur : Layer6State) (e : Layer6UnifiedEntry) : Layer6State :=
      let base : Layer6State :=
        match e.rem with
        | .none => cur
        | .loseIndestructible =>
          if o.isOnBattlefield then
            { cur with kw := cur.kw.filter (· != Keyword.indestructible) }
          else cur
        | .all => {}
      let nextGranted :=
        if e.setsGrantedIdx then base.activeGrantedIdx.push e.idx else base.activeGrantedIdx
      if kwOnly then
        { retainsBase := base.retainsBase
          activeGrantedIdx := nextGranted
          kw := KeywordAbility.merge base.kw e.addKw
          activated := base.activated ++ e.addActivated
          wards := base.wards ++ e.addWards }
      else
        { retainsBase := base.retainsBase
          activeGrantedIdx := nextGranted
          kw := KeywordAbility.merge base.kw e.addKw
          staticsWithTs := base.staticsWithTs ++ e.addStatics
          triggers := base.triggers ++ e.addTriggers
          activated := base.activated ++ e.addActivated
          wards := base.wards ++ e.addWards
          prowessCount := base.prowessCount + e.addProwess
          ironFistCount := base.ironFistCount + e.addIronFist
          manaGrants := pushUniqMana base.manaGrants e.addMana
          lanternGrant := base.lanternGrant || e.addLantern
          colorlessGrant := base.colorlessGrant || e.addColorlessGrant }
    let rec pushDeltaAux : Nat → Array (L6TsSource × Layer6UnifiedEntry) →
        L6TsSource → Layer6Delta → ObjectScope → Bool → Option Nat →
        Array (L6TsSource × Layer6UnifiedEntry)
      | depth, pending, tsSrc, d, sc, requiresRetainsBase, requiresGrantedIdx? =>
        let grantedDeltas : Array Layer6Delta :=
          match depth with
          | 0 => #[]
          | _ + 1 =>
            if !o.isOnBattlefield || d.addStatics.isEmpty then #[]
            else
              d.addStatics.filterMap fun ab =>
                g.extractContinuousL6 o oCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra)
        let hasSelf := !grantedDeltas.isEmpty
        let hasDirect :=
          d.rem != .none || !d.addKw.isEmpty || (!kwOnly && !d.addStatics.isEmpty) ||
            !d.addTriggers.isEmpty || !d.addActivated.isEmpty || !d.addWards.isEmpty ||
            d.addProwess > 0 || !d.addMana.isEmpty || d.addLantern
        if !hasDirect && !hasSelf then pending
        else
          let gi := pending.size
          let pending := pending.push (tsSrc, {
            idx := gi
            scope := sc
            kwDepCheck? := d.kwDepCheck?
            requiresRetainsBase := requiresRetainsBase
            requiresGrantedIdx? := requiresGrantedIdx?
            setsGrantedIdx := hasSelf
            rem := d.rem
            addKw := d.addKw
            addStaticsRaw := if !kwOnly && needStaticsTs then d.addStatics else #[]
            addStatics :=
              if kwOnly || needStaticsTs || d.addStatics.isEmpty then #[]
              else d.addStatics.map (·, (0, 0))
            addTriggers := d.addTriggers
            addActivated := d.addActivated
            addWards := d.addWards
            addProwess := d.addProwess
            addMana := d.addMana
            addLantern := d.addLantern
          })
          match depth with
          | 0 => pending
          | depth' + 1 =>
            if hasSelf then
              grantedDeltas.foldl (fun p dl =>
                pushDeltaAux depth' p tsSrc dl (.objects #[o.id]) false (some gi)) pending
            else pending
    let pushDelta (pending : Array (L6TsSource × Layer6UnifiedEntry)) (tsSrc : L6TsSource)
        (d : Layer6Delta) (sc : ObjectScope := .objects #[o.id])
        (requiresRetainsBase : Bool := false) (requiresGrantedIdx? : Option Nat := none) :
        Array (L6TsSource × Layer6UnifiedEntry) :=
      pushDeltaAux 3 pending tsSrc d sc requiresRetainsBase requiresGrantedIdx?
    Id.run do
      let mut pending : Array (L6TsSource × Layer6UnifiedEntry) := #[]
      -- 0. Own printed self statics gated on `retainsBase` in CR 613.7 / 613.8 order.
      for d in ownSelfDeltas do
        pending := pushDelta pending .base d (requiresRetainsBase := true)
      -- 1. All 15 CR 122.1b keyword counters (CR 613.7c), replicating cumulative counters.
      if !o.status.counters.isEmpty then
        for (k, kw) in CounterKind.keywordCounters do
          let cnt := o.status.counterCount k
          if cnt > 0 then
            let kwArr := if kw.isCumulative then Array.replicate cnt kw else #[kw]
            pending := pending.push (.counter k, {
              idx := pending.size
              scope := .objects #[o.id]
              addKw := kwArr
              addTriggers := if kwOnly then #[] else expandedKeywordTriggers kwArr
              addProwess := KeywordAbility.prowessCount kwArr
            })
      if !isStackAbilityObj o then
        let anyAttached := g.objects.any fun a => a.isOnBattlefield && a.attachedTo.isSome
        let hasPeerStaticOrStrip :=
          g.objects.any fun p =>
            (p.isOnBattlefield && !p.status.faceDown &&
              let pBc := if hasCopy then g.baseCard p else p.printed
              !pBc.staticAbilities.isEmpty &&
                pBc.staticAbilities.any fun ab =>
                  (!isAttachedHostStatic ab && staticGrantsOrStripsStatic ab) ||
                    staticTransitivelyGrants staticGrantsOrStripsStatic 3 ab) ||
            (p.zone == .command && !p.printed.staticAbilities.isEmpty &&
              (if hasCopy then g.baseCard p else p.printed).types.isEmpty &&
              p.printed.staticAbilities.any fun ab =>
                staticGrantsOrStripsStatic ab ||
                  staticTransitivelyGrants staticGrantsOrStripsStatic 3 ab)
        if o.isOnBattlefield then
          -- 2. Attached Auras and Equipment at CR 613.7a / 613.7e timestamp (`max(attachmentTs, abTs)`).
          if anyAttached then
            for att in g.objects do
              if att.isOnBattlefield && att.attachedTo == some o.id && att.id != o.id then
                let attCtrl := g.controllerOf att |>.getD att.owner
                let attSimple :=
                  !hasStaticEff && !hasBasicLandSet && !hasPeerStaticOrStrip && !att.status.faceDown &&
                    !(g.objects.any fun a2 =>
                      a2.isOnBattlefield && a2.attachedTo == some att.id && a2.id != att.id)
                if attSimple then
                  let attBc := if hasCopy then g.baseCard att else att.printed
                  if !attBc.staticAbilities.isEmpty then
                    let attTcs := g.evalLayer3 att
                    for ab0 in attBc.staticAbilities do
                      let ab := TextChange.applyStaticAbility attTcs ab0
                      if let some d := g.extractContinuousL6 att attCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                        pending := pushDelta pending (.attachBase att) d
                else
                  let (attStatics, _) := peerStaticsWithTs att
                  let attAttachTs := g.attachmentTimestamp att o.id
                  for (ab, abTs) in attStatics do
                    if let some d := g.extractContinuousL6 att attCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                      pending := pushDelta pending (.fixed (maxTs attAttachTs abTs)) d
          -- 3. Peer battlefield permanents and command-zone emblems (CR 114.4 / 613.7a / 613.7d).
          for src in g.objects do
            if src.isOnBattlefield && src.id != o.id && src.attachedTo != some o.id then
              let srcCtrl := g.controllerOf src |>.getD src.owner
              let srcSimple :=
                !hasStaticEff && !hasBasicLandSet && !hasPeerStaticOrStrip && !src.status.faceDown &&
                  !(anyAttached && g.objects.any fun a2 =>
                    a2.isOnBattlefield && a2.attachedTo == some src.id && a2.id != src.id)
              if srcSimple then
                let srcBc := if hasCopy then g.baseCard src else src.printed
                if !srcBc.staticAbilities.isEmpty then
                  let srcTcs := g.evalLayer3 src
                  for ab0 in srcBc.staticAbilities do
                    let ab := TextChange.applyStaticAbility srcTcs ab0
                    if let some d := g.extractContinuousL6 src srcCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                      pending := pushDelta pending (.peerBase src) d
              else
                let (srcStaticsNoTs, _) := peerStaticsNoTs src
                if !srcStaticsNoTs.isEmpty then
                  let (srcStatics, _) := peerStaticsWithTs src
                  for (ab, abTs) in srcStatics do
                    if let some d := g.extractContinuousL6 src srcCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                      pending := pushDelta pending (.fixed abTs) d
            else if src.zone == .command && !src.printed.staticAbilities.isEmpty &&
                (if hasCopy then g.baseCard src else src.printed).types.isEmpty then
              let embStatics := src.printed.staticAbilities
              let srcCtrl := g.controllerOf src |>.getD src.owner
              for ab in embStatics do
                if let some d := g.extractContinuousL6 src srcCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                  pending := pushDelta pending (.objEntry src) d
        else
          -- 3b. Non-battlefield non-stack-ability objects (stack spells, hand, graveyard,
          -- exile, library, command) receiving abilities from battlefield statics and
          -- command-zone emblems, preserving granted timestamps (CR 114.4 / 613.7a).
          let zk := o.zone.kind
          for src in g.objects do
            if src.isOnBattlefield then
              let srcCtrl := g.controllerOf src |>.getD src.owner
              let srcSimple :=
                !hasStaticEff && !hasBasicLandSet && !hasPeerStaticOrStrip && !src.status.faceDown &&
                  !(anyAttached && g.objects.any fun a2 =>
                    a2.isOnBattlefield && a2.attachedTo == some src.id && a2.id != src.id)
              if srcSimple then
                let srcBc := if hasCopy then g.baseCard src else src.printed
                if !srcBc.staticAbilities.isEmpty then
                  let srcTcs := g.evalLayer3 src
                  for ab0 in srcBc.staticAbilities do
                    if staticMayAffectZone zk ab0 then
                      let ab := TextChange.applyStaticAbility srcTcs ab0
                      if let some d := g.extractContinuousL6 src srcCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                        pending := pushDelta pending (.peerBase src) d
              else
                let (srcStaticsNoTs, _) := peerStaticsNoTs src
                if srcStaticsNoTs.any (fun (ab, _) => staticMayAffectZone zk ab) then
                  let (srcStatics, _) := peerStaticsWithTs src
                  for (ab, abTs) in srcStatics do
                    if staticMayAffectZone zk ab then
                      if let some d := g.extractContinuousL6 src srcCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                        pending := pushDelta pending (.fixed abTs) d
            else if src.zone == .command && (g.baseCard src).types.isEmpty then
              let embStatics := src.printed.staticAbilities
              if !embStatics.isEmpty then
                let srcCtrl := g.controllerOf src |>.getD src.owner
                for ab in embStatics do
                  if staticMayAffectZone zk ab then
                    if let some d := g.extractContinuousL6 src srcCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra) then
                      pending := pushDelta pending (.objEntry src) d
      -- 4. Active Layer 6 continuous effects and Emrakul colorless mana grants (CR 613.7b).
      for pos in [0:g.activeEffects.size] do
        let (eid, s) := g.activeEffects[pos]!
        match s with
        | .layered sc (.abilities add rem) d =>
          if g.durationActive d && g.effectPhasingAllows o eid sc d then
            let grantedStatics := add.staticAbilities
            let fsKw : Array KeywordAbility :=
              if add.firstStrikeOnYourTurn && ctrl?.any g.isOnActiveTeam then
                #[Keyword.firstStrike]
              else #[]
            let grantedDeltas : Array Layer6Delta :=
              if !o.isOnBattlefield || grantedStatics.isEmpty then #[]
              else
                grantedStatics.filterMap fun ab =>
                  g.extractContinuousL6 o oCtrl o ab kwOnly (some peerKwOf) (some peerHasKwExtra)
            let splitGrantedDeltas := !grantedDeltas.isEmpty
            let resolvedAddKw : Array KeywordAbility :=
              if add.keywords.any isSourceBoundProtection then
                let durSrcId? : Option ObjectId :=
                  match d with
                  | .whileSourceOnBattlefield sid
                  | .untilSourceLeaves sid
                  | .whileSourceHasCounter sid _
                  | .whileInZone sid _ => some sid
                  | _ => none
                let grantorId? : Option ObjectId :=
                  ((g.effectCreatedInfo? eid).bind (fun (_, c) => oneShotCauseSourceId? c)).orElse
                    (fun _ => durSrcId?)
                match grantorId?.bind g.damageSourceById? with
                | some grantor => resolveProtectionKeywords grantor add.keywords (dropUnchosen := true)
                | none => add.keywords.filter (!isSourceBoundProtection ·)
              else add.keywords
            let addKw := KeywordAbility.merge resolvedAddKw fsKw
            let mut grantIdx? : Option Nat := none
            if kwOnly then
              let addAct :=
                (KeywordAbility.expandAll resolvedAddKw).activatedAbilities.filter (·.isEquip)
              let addWards := KeywordAbility.wardCosts resolvedAddKw
              if rem != .none || !addKw.isEmpty || !addAct.isEmpty || !addWards.isEmpty ||
                  splitGrantedDeltas then
                let gi := pending.size
                if splitGrantedDeltas then grantIdx? := some gi
                pending := pending.push (.eff eid pos, {
                  idx := gi
                  scope := sc
                  setsGrantedIdx := splitGrantedDeltas
                  rem := rem
                  addKw := addKw
                  addActivated := addAct
                  addWards := addWards
                })
            else
              let grantedTrigs := add.triggeredAbilities ++ expandedKeywordTriggers resolvedAddKw
              let addAct := (KeywordAbility.expandAll resolvedAddKw).activatedAbilities
              let addWards := KeywordAbility.wardCosts resolvedAddKw
              let addProw := KeywordAbility.prowessCount resolvedAddKw
              if rem != .none || !addKw.isEmpty || !grantedStatics.isEmpty ||
                  !grantedTrigs.isEmpty || !addAct.isEmpty || !addWards.isEmpty ||
                  addProw > 0 || add.ironFistTapGrants > 0 || splitGrantedDeltas then
                let gi := pending.size
                if splitGrantedDeltas then grantIdx? := some gi
                pending := pending.push (.eff eid pos, {
                  idx := gi
                  scope := sc
                  setsGrantedIdx := splitGrantedDeltas
                  rem := rem
                  addKw := addKw
                  addStaticsRaw := if needStaticsTs then grantedStatics else #[]
                  addStatics :=
                    if needStaticsTs || grantedStatics.isEmpty then #[]
                    else grantedStatics.map (·, (0, 0))
                  addTriggers := grantedTrigs
                  addActivated := addAct
                  addWards := addWards
                  addProwess := addProw
                  addIronFist := add.ironFistTapGrants
                })
            if let some gi := grantIdx? then
              for dl in grantedDeltas do
                pending := pushDelta pending (.eff eid pos) dl (requiresGrantedIdx? := some gi)
        | .permission _ (.colorlessGrant landId _) d =>
          if !kwOnly && o.isOnBattlefield && landId == o.id && g.durationActive d then
            pending := pending.push (.eff eid pos, {
              idx := pending.size
              scope := .objects #[o.id]
              addActivated := #[grantedColorlessTwoAct]
              addColorlessGrant := true
            })
        | _ => pure ()
      if pending.isEmpty then return initState
      if pending.size == 1 && !needStaticsTs then
        let e := pending[0]!.2
        if entryApplies initState e then return applyStep initState e
        else return initState
      let oObjTs := g.objectEntryTimestamp o
      let baseTs := if needStaticsTs then initBaseTs else (g.baseCardWithTs o).2
      let raw : Array Layer6UnifiedEntry := pending.map fun (src, e) =>
        let ts :=
          match src with
          | .fixed t => t
          | .base => baseTs
          | .counter k => g.counterTimestamp o.id k
          | .attachBase att => maxTs (g.attachmentTimestamp att o.id) (g.baseCardWithTs att).2
          | .peerBase peer => (g.baseCardWithTs peer).2
          | .objEntry emb => g.objectEntryTimestamp emb
          | .eff eid pos => g.effectTimestamp eid pos
        let statics :=
          if e.addStaticsRaw.isEmpty then e.addStatics
          else
            let grantTs := maxTs oObjTs ts
            e.addStaticsRaw.map (·, grantTs)
        { e with ts := ts, addStatics := statics }
      let sorted := raw.qsort fun a b =>
        if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
        else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
        else a.idx < b.idx
      let mut rem := sorted
      let mut cur := initState
      for _ in [0:sorted.size] do
        let applicable := rem.filter (fun e => entryApplies cur e)
        if applicable.isEmpty then break
        let dependsOn (a b : Layer6UnifiedEntry) : Bool :=
          a.idx != b.idx &&
            entryApplies cur a != entryApplies (applyStep cur b) a
        let chosen :=
          (applicable.find? (fun a => !applicable.any (fun b => dependsOn a b))).getD applicable[0]!
        cur := applyStep cur chosen
        rem := rem.filter (fun e => e.idx != chosen.idx)
      return cur

/-- Evaluate `o`'s Layer 6 state without computing static-ability timestamps when
only triggers, activated abilities, wards, or flags are needed. -/
private def evalLayer6Fast (g : Game) (o : GameObject) : Layer6State :=
  evalLayer6Aux g false false 1 o

/-- Evaluate `o`'s complete Layer 6 state including CR 613.7a static-ability
timestamps (CR 613.1f / 613.7 / 613.8). -/
def evalLayer6 (g : Game) (o : GameObject) : Layer6State :=
  evalLayer6Aux g true false 1 o

/-- Evaluated static abilities of `o` in Layer 6 (CR 613.1f / 613.7 / 613.8). -/
def staticAbilities (g : Game) (o : GameObject) : Array StaticAbility :=
  if o.isLkiSnapshot then o.printed.staticAbilities
  else
  let hasCopy := g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.copy _) _ => true
    | _ => false
  let hasEff := g.hasAnyStaticLayer6Effect
  let hasPeerOrEmb :=
    !isStackAbilityObj o &&
      g.hasPeerOrEmblemStaticLayer6 o staticGrantsOrStripsStatic (some hasCopy)
  let hasBasicLandSet? := if o.isOnBattlefield then some g.hasActiveBasicLandSetEffect else none
  if !hasEff && !hasPeerOrEmb && !(hasBasicLandSet?.getD false) then
    if isFaceDownMasked o then #[]
    else
      let bc := if hasCopy then g.baseCard o else o.printed
      if bc.staticAbilities.isEmpty then #[]
      else
        let tcs := g.evalLayer3 o
        if tcs.isEmpty then bc.staticAbilities
        else bc.staticAbilities.map (TextChange.applyStaticAbility tcs)
  else if g.hasCwStaticLayer6Effect || g.hasKwDepAttStatic o (some hasCopy) then
    (g.evalLayer6Fast o).staticsWithTs.map Prod.fst
  else
    (evalStaticsFast g false (some hasEff) (some (hasBasicLandSet?.getD g.hasActiveBasicLandSetEffect)) (some hasCopy) 4 o).1.map Prod.fst

/-- Whether `o` currently has hexproof and indestructible from a Saga lore-threshold
static ability (Tom Bombadil, CR 604.2 / 613.1f). -/
def loreThresholdProtection (g : Game) (o : GameObject) : Bool :=
  match g.controllerOf o with
  | none => false
  | some p =>
    (g.staticAbilities o).any fun
      | .continuous (some (.cmp .ge (.aggregate .sum (.counterCount (some .lore))
            (.inZones .battlefield (.all #[.hasSubtype (.literal .saga), .controlledBy .you]))) (.const n))) sc _ =>
        StaticAbility.isScopeSelf sc && g.loreAmongSagas p ≥ n.toNat
      | _ => false

/-- Whether `o`'s base/printed abilities still apply after Layer 6 ability
removals in CR 613.7 / 613.8 order (CR 613.1f). -/
def retainsPrintedAbilities (g : Game) (o : GameObject) : Bool :=
  if o.isLkiSnapshot then
    (o.lkiLayer6.map (·.retainsPrintedAbilities)).getD (!isFaceDownMasked o)
  else
  let hasCopy := g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.copy _) _ => true
    | _ => false
  let hasEff := g.hasAnyStaticLayer6Effect
  let hasPeerOrEmbStrip :=
    !isStackAbilityObj o &&
      g.hasPeerOrEmblemStaticLayer6 o staticStripsAbilities (some hasCopy)
  let hasBasicLandSet? := if o.isOnBattlefield then some g.hasActiveBasicLandSetEffect else none
  if !hasEff && !hasPeerOrEmbStrip && !(hasBasicLandSet?.getD false) then
    !isFaceDownMasked o
  else if g.hasCwStaticLayer6Effect || g.hasKwDepAttStatic o (some hasCopy) then
    (g.evalLayer6Fast o).retainsBase
  else
    (evalStaticsFast g false (some hasEff) (some (hasBasicLandSet?.getD g.hasActiveBasicLandSetEffect)) (some hasCopy) 4 o).2

/-- Evaluated keywords of `o` in Layer 6 (CR 613.1f / 613.7 / 613.8). -/
def currentKeywords (g : Game) (o : GameObject) : Array KeywordAbility :=
  if o.isLkiSnapshot then
    resolveProtectionKeywords o o.printed.keywords (dropUnchosen := false)
  else if !o.isOnBattlefield && o.zone != .stack && o.status.counters.isEmpty &&
      !g.activeEffects.any (fun (_, s) =>
        match s with | .layered _ (.abilities ..) d => g.durationActive d | _ => false) &&
      !(!isStackAbilityObj o && g.hasPeerOrEmblemStaticLayer6 o staticAffectsKeywords) then
    if isFaceDownMasked o then #[]
    else
      let bc := g.baseCard o
      let oTcs := g.evalLayer3 o
      let kws :=
        if oTcs.isEmpty then bc.keywords
        else HasTextChange.applyTextChanges oTcs bc.keywords
      resolveProtectionKeywords o kws (dropUnchosen := false)
  else
    (evalLayer6Aux g false true 1 o).kw

@[inline] def effectiveKeywords (g : Game) (o : GameObject) : Array KeywordAbility :=
  g.currentKeywords o

/-- Whether `o` matches `scope` using evaluated Layer 2, Layer 4, and Layer 6
characteristics (CR 611.2b–c / 611.3 / 613.8). -/
def scopeMatches (g : Game) (scope : ObjectScope) (o : GameObject)
    (eid? : Option EffectId := none) (dur? : Option EffectDuration := none) : Bool :=
  let phasingOk : Bool :=
    match eid?, dur? with
    | some eid, some d => g.effectPhasingAllows o eid scope d
    | _, _ => true
  match scope with
  | .objects ids => ids.contains o.id
  | .creaturesControlledBy p =>
    phasingOk && o.isOnBattlefield && g.controlledBy o p && g.isCreature o
  | .creaturesWithout kw =>
    phasingOk && o.isOnBattlefield && g.isCreature o &&
      let curKw := g.currentKeywords o
      kw.any (fun k => !curKw.contains k)
  | .permanentsOfSubtype p s =>
    phasingOk && o.isOnBattlefield && g.controlledBy o p && g.hasSubtype o s

/-- True when `o` currently has `SimpleKeyword` `sk` in Layer 6 (CR 613.1f). -/
def hasSimpleKeyword (g : Game) (o : GameObject) (sk : SimpleKeyword) : Bool :=
  KeywordAbility.hasSimple (g.currentKeywords o) sk

/-- True when any current keyword on `o` in Layer 6 satisfies `pred` (CR 613.1f). -/
def hasKeyword (g : Game) (o : GameObject) (pred : KeywordAbility → Bool) : Bool :=
  (g.currentKeywords o).any pred

def hasHaste (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .haste

def hasShadow (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .shadow

def hasVigilance (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .vigilance

def hasFlying (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .flying

def hasFirstStrike (g : Game) (o : GameObject) : Bool :=
  let kw := g.currentKeywords o
  KeywordAbility.hasSimple kw .firstStrike || KeywordAbility.hasSimple kw .doubleStrike

def hasDoubleStrike (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .doubleStrike

def hasIslandwalk (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).any (· == Keyword.islandwalk)

def hasHexproof (g : Game) (o : GameObject) : Bool :=
  KeywordAbility.hasHexproof (g.currentKeywords o)

def hasDeathtouch (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .deathtouch

def hasIndestructible (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .indestructible

def hasTrample (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .trample

def hasLifelink (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .lifelink

def hasMenace (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .menace

def hasReach (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .reach

def hasDefender (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .defender

def hasDecayed (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .decayed

def hasExalted (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .exalted

def hasFlash (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .flash

def hasChangeling (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .changeling

def hasStoried (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .storied

def hasAscend (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .ascend

def hasSplitSecond (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .splitSecond

def hasConvoke (g : Game) (o : GameObject) : Bool :=
  g.hasSimpleKeyword o .convoke

private def isCtrlOrCopyEffectSpec : ContinuousEffectSpec → Bool
  | .layered _ (.control _) _ | .layered _ (.copy _) _ => true
  | _ => false

/-- True when `eid` was created or expired as a Layer 1 copy or Layer 2 control effect. -/
private def isCtrlOrCopyEffectId (g : Game) (eid : EffectId) : Bool :=
  Id.run do
    if let some (_, spec) := g.activeEffects.find? (·.1 == eid) then
      return isCtrlOrCopyEffectSpec spec
    for rev in [0:g.events.size] do
      let i := g.events.size - 1 - rev
      match g.events[i]!.change with
      | .rules (.continuousEffect (.created id spec)) =>
        if id == eid then return isCtrlOrCopyEffectSpec spec
      | .rules (.continuousEffect (.expired id (some spec))) =>
        if id == eid then return isCtrlOrCopyEffectSpec spec
      | _ => pure ()
    return false

/-- Event index marking the end of `ctrl`'s (or `ctrl`'s team's shared turn's)
most recent turn-begin / untap-begin expiration boundary, matching the forward
turn/untap scan in $O(\text{turn window})$ (CR 302.6 / 805.4a / 810.2). -/
private def lastTurnStartIdx? (g : Game) (ctrl : PlayerId) : Option Nat :=
  Id.run do
    let mut uIdx? : Option (Nat × PlayerId) := none
    for rev in [0:g.events.size] do
      let i := g.events.size - 1 - rev
      match g.events[i]!.change with
      | .rules (.turn (.turnBegan ap extra)) =>
        if ap == ctrl || g.areTeammates ap ctrl then
          let (seats, seatsExtra) := g.currentSharedTurnState (some i)
          let sameShared :=
            extra == seatsExtra && !seats.isEmpty &&
              g.areTeammates seats[0]! ap && !seats.contains ap
          if !sameShared then
            uIdx? := some (i, ap)
            break
      | .rules (.turn (.stepBegan .untap ap)) =>
        if ap == ctrl || g.areTeammates ap ctrl then
          let (seats, _) := g.currentSharedTurnState (some i)
          if seats.isEmpty || seats == #[ap] || !g.areTeammates seats[0]! ap then
            uIdx? := some (i, ap)
            break
      | _ => pure ()
    match uIdx? with
    | none => return none
    | some (uIdx, firstSeat) =>
      let mut tsIdx := uIdx
      for j in [uIdx + 1 : g.events.size] do
        let ev := g.events[j]!
        match ev.change with
        | .rules (.turn (.turnBegan ap _)) =>
          if ap == firstSeat then tsIdx := j else break
        | .rules (.turn (.stepBegan .untap ap)) =>
          if ap == firstSeat then tsIdx := j else break
        | .rules (.turn (.stepEnded .untap)) | .rules (.turn (.stepBegan _ _)) =>
          break
        | _ =>
          if ev.cause? == some (.turnBased .expireAtStepBegin) then
            tsIdx := j
      return some tsIdx

private def applySnapshotPrinted (pr : CardDef) (isTok : Bool) (printed? : Option CardDef) : CardDef :=
  match printed? with
  | none => pr
  | some p =>
    if p.otherFace.isSome || pr.otherFace.isNone then
      adjustTokenCardDef isTok p
    else if p.name == pr.name then
      adjustTokenCardDef isTok pr
    else if pr.otherFace.any (·.name == p.name) then
      adjustTokenCardDef isTok (swapCardFace pr)
    else
      adjustTokenCardDef isTok p

private structure PerObjHistState where
  z : Zone
  fd : Bool
  ph : Bool
  prep : Bool
  pr : CardDef
  tr : Bool
  dc : Option PlayerId
  rc : Option PlayerId
deriving Inhabited

private def PerObjHistState.ofObj (o : GameObject) : PerObjHistState :=
  { z := o.zone
    fd := o.status.faceDown
    ph := o.status.phasedOut
    prep := o.status.prepared
    pr := o.printed
    tr := o.status.transformed
    dc := o.defaultController
    rc := o.controller }

private structure HistObjEntry where
  z? : Option Zone := none
  ph? : Option Bool := none
  fd? : Option Bool := none
  tr? : Option Bool := none
  pr? : Option CardDef := none
  dc? : Option (Option PlayerId) := none
  rc? : Option (Option PlayerId) := none
  tap? : Option Bool := none
  harn? : Option Bool := none
  goad? : Option (Bool × Array PlayerId × Array PlayerId) := none
  prep? : Option Bool := none
  att? : Option (Option ObjectId) := none
  missingInfo? : Option EventObject := none
deriving Inhabited

private structure HistGlobalState where
  effs : Array (EffectId × ContinuousEffectSpec)
  counterSources : Array (ObjectId × CounterKind)
  zsOrder : Array ObjectId
  objs : Std.HashMap ObjectId HistObjEntry
  ls : Array (PlayerId × Bool)
  lefts : Array (PlayerId × Bool)
  ringBearers : Array (PlayerId × Option ObjectId)
  monarchs : Array (PlayerId × Bool)
  citysBlessings : Array (PlayerId × Bool)
  enduringStories : Array (PlayerId × Bool)
  isNight : Bool

private structure HistoricalSliceState where
  global : HistGlobalState
  per : PerObjHistState

private def HistoricalSliceState.z (s : HistoricalSliceState) : Zone := s.per.z

private def mergeHistMissingInfo (cur? : Option EventObject) (eo : EventObject) : EventObject :=
  match cur? with
  | some cur =>
    { eo with
      printed := if eo.printed.isSome || cur.printed.isNone then eo.printed else cur.printed
      defaultController :=
        if eo.zone == .battlefield then
          eo.defaultController.orElse (fun _ => cur.defaultController)
        else eo.defaultController
      chosenOdd := eo.chosenOdd.orElse (fun _ => cur.chosenOdd)
      chosenCreatureType := eo.chosenCreatureType.orElse (fun _ => cur.chosenCreatureType)
      chosenColor := eo.chosenColor.orElse (fun _ => cur.chosenColor)
      chosenName := eo.chosenName.orElse (fun _ => cur.chosenName)
      chosenCardType := eo.chosenCardType.orElse (fun _ => cur.chosenCardType)
      chosenAnchor := eo.chosenAnchor.orElse (fun _ => cur.chosenAnchor) }
  | none => eo

@[inline] private def HistGlobalState.updateObj (gs : HistGlobalState) (oid : ObjectId)
    (f : HistObjEntry → HistObjEntry) : HistGlobalState :=
  let objs := gs.objs
  let gs := { gs with objs := {} }
  { gs with objs := objs.alter oid (fun cur? => some (f (cur?.getD {}))) }

@[inline] private def HistGlobalState.updateObjWithZone (gs : HistGlobalState) (oid : ObjectId)
    (z : Zone) (f : HistObjEntry → HistObjEntry) : HistGlobalState :=
  let objs := gs.objs
  let zsOrder := gs.zsOrder
  let gs := { gs with objs := {}, zsOrder := #[] }
  let hasZ := (objs.get? oid).any (·.z?.isSome)
  let zsOrder := if hasZ then zsOrder else zsOrder.push oid
  let objs := objs.alter oid (fun cur? => some (f { cur?.getD {} with z? := some z }))
  { gs with objs := objs, zsOrder := zsOrder }

private def setHistPlFlag (ls : Array (PlayerId × Bool)) (pid : PlayerId) (v : Bool) :
    Array (PlayerId × Bool) :=
  match ls.findIdx? (·.1 == pid) with
  | some k => ls.set! k (pid, v)
  | none => ls.push (pid, v)

private def setHistPlOptObj (xs : Array (PlayerId × Option ObjectId)) (pid : PlayerId)
    (v : Option ObjectId) : Array (PlayerId × Option ObjectId) :=
  match xs.findIdx? (·.1 == pid) with
  | some k => xs.set! k (pid, v)
  | none => xs.push (pid, v)

private def initHistGlobalState (g : Game)
    (initEffects : Array (EffectId × ContinuousEffectSpec))
    (counterSources : Array (ObjectId × CounterKind)) : HistGlobalState := Id.run do
  let mut objs : Std.HashMap ObjectId HistObjEntry :=
    Std.HashMap.emptyWithCapacity (g.objects.size + 16)
  for obj in g.objects do
    objs := objs.insert obj.id {
      fd? := some obj.status.faceDown
      tr? := some obj.status.transformed
      pr? := some obj.printed
      dc? := some obj.defaultController
      rc? := some obj.controller
      tap? := some obj.status.tapped
      harn? := some obj.status.harnessed
      goad? := some (obj.status.goaded || !obj.status.goadedBy.isEmpty,
        obj.status.goadedBy, obj.status.goadedUntilNextTurnOf)
    }
  let ringBearers := g.players.map fun pl => (pl.id, pl.ringBearerId)
  let monarchs := g.players.map fun pl => (pl.id, pl.isMonarch)
  let citysBlessings := g.players.map fun pl => (pl.id, pl.citysBlessing)
  let enduringStories := g.players.map fun pl => (pl.id, pl.enduringStory)
  return {
    effs := initEffects
    counterSources := counterSources
    zsOrder := #[]
    objs := objs
    ls := #[]
    lefts := #[]
    ringBearers, monarchs, citysBlessings, enduringStories
    isNight := g.isNight
  }

private def addTrackedCounterPair (acc : Array (ObjectId × CounterKind))
    (sid : ObjectId) (k : CounterKind) : Array (ObjectId × CounterKind) :=
  if acc.contains (sid, k) then acc else acc.push (sid, k)

private def addTrackedCounterSource (acc : Array (ObjectId × CounterKind))
    (spec : ContinuousEffectSpec) : Array (ObjectId × CounterKind) :=
  match spec with
  | .layered _ _ (.whileSourceHasCounter src k) => addTrackedCounterPair acc src k
  | _ => acc

private def insertPreLogEffectById (effs : Array (EffectId × ContinuousEffectSpec))
    (eid : EffectId) (spec : ContinuousEffectSpec) : Array (EffectId × ContinuousEffectSpec) :=
  if effs.any (·.1 == eid) then effs
  else
    match effs.findIdx? (fun (eid', _) => eid.raw < eid'.raw) with
    | some idx =>
      (effs.extract 0 idx |>.push (eid, spec)) ++ effs.extract idx effs.size
    | none => effs.push (eid, spec)

private def addTrackedBagFor (acc : Array (ObjectId × CounterKind))
    (targetId? : Option ObjectId) (sid : ObjectId) (bag : CounterBag) :
    Array (ObjectId × CounterKind) :=
  if bag.isEmpty then acc
  else
    bag.foldl (fun a (k, n) =>
      if n > 0 && (targetId?.isNone || targetId? == some sid || k == .lore) then
        addTrackedCounterPair a sid k
      else a) acc

private def addPreSnapshotCountersAll (acc : Array (ObjectId × CounterKind))
    (ch : GameChange) : Array (ObjectId × CounterKind) :=
  let addEo (a : Array (ObjectId × CounterKind)) (eo : EventObject) :
      Array (ObjectId × CounterKind) :=
    if eo.counters.isEmpty then a
    else
      match eo.id with
      | some sid => addTrackedBagFor a none sid eo.counters
      | none => a
  match ch with
  | .rules (.permanent (.tapped eo _))
  | .rules (.permanent (.untapped eo))
  | .rules (.permanent (.phasedOut eo _))
  | .rules (.permanent (.phasedIn eo _))
  | .rules (.permanent (.transformed eo _))
  | .rules (.permanent (.turnedFaceUp eo))
  | .rules (.permanent (.turnedFaceDown eo))
  | .rules (.permanent (.attached eo _ _))
  | .rules (.permanent (.unattached eo _))
  | .rules (.permanent (.designation eo _ _))
  | .rules (.combat (.becameAttacking eo _))
  | .rules (.combat (.becameBlocked eo _))
  | .rules (.combat (.remainedUnblocked eo))
  | .rules (.combat (.removedFromCombat eo))
  | .rules (.cast (.spellCast eo ..))
  | .rules (.cast (.abilityActivated _ eo ..))
  | .rules (.triggerQueue (.triggered eo ..))
  | .rules (.triggerQueue (.putOnStack _ eo ..))
  | .rules (.stackObject (.resolved eo ..))
  | .rules (.stackObject (.removedOnResolution eo)) => addEo acc eo
  | .rules (.combat (.attackersDeclared _ decls)) =>
    decls.foldl (fun a (eo, _) => addEo a eo) acc
  | .rules (.combat (.blockersDeclared _ decls)) =>
    decls.foldl (fun a (eo, _) => addEo a eo) acc
  | .rules (.damage (.dealt pkts)) =>
    pkts.foldl (fun a pkt =>
      let a1 :=
        match pkt.recipient with
        | .permanent eo | .battle eo => addEo a eo
        | .player _ => a
      addEo a1 pkt.source) acc
  | .rules (.damage (.prevented src rec _)) =>
    let a1 :=
      match rec with
      | .permanent eo | .battle eo => addEo acc eo
      | .player _ => acc
    addEo a1 src
  | _ => acc

@[noinline] private def preLogEffectsAndCounterSources (g : Game)
    (targetId? : Option ObjectId := none) :
    Array (EffectId × ContinuousEffectSpec) × Array (ObjectId × CounterKind) := Id.run do
  let mut createdIds : Array EffectId := #[]
  let mut expiredCandidates : Array (EffectId × ContinuousEffectSpec) := #[]
  let mut counterSources : Array (ObjectId × CounterKind) :=
    g.activeEffects.foldl (fun acc (_, spec) => addTrackedCounterSource acc spec) #[]
  for i in [0:g.events.size] do
    let ch := g.events[i]!.change
    match ch with
    | .rules (.continuousEffect (.created eid spec)) =>
      createdIds := createdIds.push eid
      counterSources := addTrackedCounterSource counterSources spec
    | .rules (.continuousEffect (.expired eid (some spec))) =>
      counterSources := addTrackedCounterSource counterSources spec
      if !expiredCandidates.any (·.1 == eid) then
        expiredCandidates := expiredCandidates.push (eid, spec)
    | .rules (.permanent (.counters (.object eo) k ..)) =>
      if let some sid := eo.id then
        if targetId?.isNone || targetId? == some sid || k == .lore then
          counterSources := addTrackedCounterPair counterSources sid k
        counterSources := addTrackedBagFor counterSources targetId? sid eo.counters
    | .engine (.materializeObject obj _) =>
      counterSources := addTrackedBagFor counterSources targetId? obj.id obj.status.counters
    | .rules (.zone (.moved before after _ _ _ _ entersWith _)) =>
      if let some bid := before.id then
        counterSources := addTrackedBagFor counterSources targetId? bid before.counters
      if let some aid := after.id then
        counterSources := addTrackedBagFor counterSources targetId? aid (after.counters.merge entersWith)
    | .rules (.zone (.created eo _))
    | .rules (.zone (.ceasedToExist eo)) =>
      if let some sid := eo.id then
        counterSources := addTrackedBagFor counterSources targetId? sid eo.counters
    | _ =>
      match targetId? with
      | some tid =>
        if let some eo := eventObjectPreSnapshotOf? ch tid then
          counterSources := addTrackedBagFor counterSources targetId? tid eo.counters
      | none =>
        counterSources := addPreSnapshotCountersAll counterSources ch
  let survivingPreLog := g.activeEffects.filter (fun (eid, _) => !createdIds.contains eid)
  let initEffects :=
    expiredCandidates.foldl
      (fun acc (eid, spec) =>
        if createdIds.contains eid then acc else insertPreLogEffectById acc eid spec)
      survivingPreLog
  return (initEffects, counterSources)

private def perObjApplyReversePreSnap (st : PerObjHistState) (eo : EventObject) :
    PerObjHistState :=
  let prevTr := eo.zone == .battlefield && eo.transformed
  let pr0 := if st.tr != prevTr then swapCardFace st.pr else st.pr
  { z := eo.zone
    ph := eo.zone == .battlefield && eo.phasedOut
    fd := (eo.zone == .battlefield || eo.zone == .stack) && eo.faceDown
    prep := if eo.zone != .battlefield then false else st.prep
    dc :=
      if eo.zone == .battlefield then
        eo.defaultController.orElse (fun _ => eo.controller)
      else none
    rc := eo.controller
    pr := applySnapshotPrinted pr0 eo.token eo.printed
    tr := prevTr }

private def perObjApplyReverseCeased (st : PerObjHistState) (eo : EventObject)
    (prepVal : Bool) : PerObjHistState :=
  let prevTr := eo.zone == .battlefield && eo.transformed
  let pr0 := if st.tr != prevTr then swapCardFace st.pr else st.pr
  { z := eo.zone
    ph := eo.zone == .battlefield && eo.phasedOut
    fd := (eo.zone == .battlefield || eo.zone == .stack) && eo.faceDown
    prep := prepVal
    dc :=
      if eo.zone == .battlefield then
        eo.defaultController.orElse (fun _ => eo.controller)
      else none
    rc := eo.controller
    pr := applySnapshotPrinted pr0 eo.token eo.printed
    tr := prevTr }

private def perObjApplyReverseMovedAfter (st : PerObjHistState) (after : EventObject)
    (toZ : Zone) : PerObjHistState :=
  let newTr := toZ == .battlefield && after.transformed
  let pr0 := if st.tr != newTr then swapCardFace st.pr else st.pr
  { z := .outside after.owner
    ph := false
    fd := false
    prep := false
    dc := none
    rc := none
    pr := applySnapshotPrinted pr0 after.token after.printed
    tr := newTr }

private def perObjApplyReverseMovedBefore (st : PerObjHistState) (before : EventObject)
    (fromZ : Zone) (prepVal : Bool) : PerObjHistState :=
  let prevTr := fromZ == .battlefield && before.transformed
  let pr0 := if st.tr != prevTr then swapCardFace st.pr else st.pr
  { z := fromZ
    ph := fromZ == .battlefield && before.phasedOut
    fd := (fromZ == .battlefield || fromZ == .stack) && before.faceDown
    prep := prepVal
    dc :=
      if fromZ == .battlefield then
        before.defaultController.orElse (fun _ => before.controller)
      else none
    rc := before.controller
    pr := applySnapshotPrinted pr0 before.token before.printed
    tr := prevTr }

private def perObjApplyReverseCreated (st : PerObjHistState) (objOwner : PlayerId)
    (eo : EventObject) : PerObjHistState :=
  let newTr := eo.zone == .battlefield && eo.transformed
  let pr0 := if st.tr != newTr then swapCardFace st.pr else st.pr
  let eoPrinted :=
    eo.printed.orElse (fun _ => if !eo.name.isEmpty then some eo.toCardDef else none)
  { z := .outside objOwner
    ph := false
    fd := false
    prep := false
    dc := none
    rc := none
    pr := applySnapshotPrinted pr0 eo.token eoPrinted
    tr := newTr }

private def perObjApplyReverseInitMat (obj : GameObject) : PerObjHistState :=
  { z := .outside obj.owner
    ph := false
    fd := false
    prep := false
    pr := obj.printed
    tr := obj.status.transformed
    dc := none
    rc := none }

private def synthEventObjForMat (obj : GameObject) : EventObject :=
  { id := some obj.id
    owner := obj.owner
    controller := obj.controller
    defaultController := obj.defaultController
    zone := obj.zone
    tapped := obj.status.tapped
    phasedOut := obj.status.phasedOut
    faceDown := obj.status.faceDown
    transformed := obj.status.transformed
    prepared := obj.status.prepared
    harnessed := obj.status.harnessed
    goaded := obj.status.goaded || !obj.status.goadedBy.isEmpty
    goadedBy := obj.status.goadedBy
    goadedUntilNextTurnOf := obj.status.goadedUntilNextTurnOf
    chosenOdd := obj.status.chosenOdd
    chosenCreatureType := obj.status.chosenCreatureType
    chosenColor := obj.status.chosenColor
    chosenName := obj.status.chosenName
    chosenCardType := obj.status.chosenCardType
    chosenAnchor := obj.status.chosenAnchor
    attachedTo := obj.attachedTo
    counters := obj.status.counters
    token := obj.printed.isToken
    printed := some obj.printed }

private def histUpdateObjEntryFromSnap (cur : HistObjEntry) (z : Zone)
    (eo : EventObject) (fallbackPr? : Option CardDef := none) : HistObjEntry :=
  let prevTr := z == .battlefield && eo.transformed
  let curTr := cur.tr?.getD prevTr
  let basePr :=
    cur.pr?.getD
      (adjustTokenCardDef eo.token ((eo.printed.orElse (fun _ => fallbackPr?)).getD eo.toCardDef))
  let pr0 := if curTr != prevTr then swapCardFace basePr else basePr
  let pr' := applySnapshotPrinted pr0 eo.token (eo.printed.orElse (fun _ => fallbackPr?))
  let dc :=
    if z == .battlefield then eo.defaultController.orElse (fun _ => eo.controller) else none
  let fd := (z == .battlefield || z == .stack) && eo.faceDown
  { cur with
    fd? := some fd
    tr? := some prevTr
    pr? := some pr'
    dc? := some dc
    rc? := some eo.controller
    tap? := some (z == .battlefield && eo.tapped)
    harn? := some (z == .battlefield && eo.harnessed)
    goad? :=
      if z == .battlefield then
        some (eo.goaded || !eo.goadedBy.isEmpty, eo.goadedBy, eo.goadedUntilNextTurnOf)
      else some (false, #[], #[]) }

private def histClearDepartedObjEntry (cur : HistObjEntry)
    (eo? : Option EventObject := none) : HistObjEntry :=
  let pr' :=
    match cur.pr?, cur.tr? with
    | some p, some true => swapCardFace p
    | some p, _ => p
    | none, _ =>
      match eo? with
      | some eo => adjustTokenCardDef eo.token (eo.printed.getD eo.toCardDef)
      | none => { name := "", types := #[] }
  { cur with
    fd? := some false
    tr? := some false
    pr? := if cur.pr?.isSome || eo?.isSome then some pr' else cur.pr?
    dc? := some none
    rc? := some none
    tap? := some false
    harn? := some false
    goad? := some (false, #[], #[]) }

@[noinline] private def reverseStepHistGlobal (g : Game) (idxData : InitialMaterializeIndex)
    (defaultBfPrep : ObjectId → EventObject → Bool) (idx : Nat) (ch : GameChange)
    (gs : HistGlobalState) (nonInitMatIds : Array ObjectId) :
    HistGlobalState × Array ObjectId × Array (ObjectId × EventObject) × Bool := Id.run do
  let mut gs := gs
  let mut nonInitMatIds := nonInitMatIds
  let mut livePreSnaps : Array (ObjectId × EventObject) := #[]
  if !nonInitMatIds.isEmpty then
    let isZoneOrMat :=
      match ch with
      | .rules (.zone (.ceasedToExist _))
      | .rules (.zone (.moved ..))
      | .rules (.zone (.created ..))
      | .engine (.materializeObject ..) => true
      | _ => false
    if !isZoneOrMat then
      for nid in nonInitMatIds do
        if eventObjectIsLiveSubject g idx ch nid then
          if let some eo := eventObjectPreSnapshotOf? ch nid then
            livePreSnaps := livePreSnaps.push (nid, eo)
            gs := gs.updateObjWithZone nid eo.zone fun cur =>
              histUpdateObjEntryFromSnap
                { cur with
                  ph? := some (eo.zone == .battlefield && eo.phasedOut)
                  prep? := if eo.zone != .battlefield then some false else cur.prep?
                  att? := some (if eo.zone == .battlefield then eo.attachedTo else none)
                  missingInfo? := some (mergeHistMissingInfo cur.missingInfo? eo) }
                eo.zone eo
  let mut wasInitMat := false
  match ch with
  | .rules (.permanent (.designation eo .prepared gained)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with prep? := some (!gained) }
  | .rules (.permanent (.designation eo .harnessed gained)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with harn? := some (!gained) }
  | .rules (.permanent (.designation eo (.goaded byP untilNext) gained)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur =>
        if !eo.goadedBy.isEmpty || !eo.goaded then
          { cur with
            goad? := some (eo.goaded || !eo.goadedBy.isEmpty, eo.goadedBy, eo.goadedUntilNextTurnOf) }
        else
          -- Fallback for synthetic `EventObject`s constructed with `goaded := true` and empty `goadedBy`.
          let (_, gBy, gUntil) := cur.goad?.getD (true, #[], #[])
          if gained then
            let gBy' := if gBy.size > 1 then gBy.filter (· != byP) else gBy
            let gUntil' := if untilNext && gBy.size > 1 then gUntil.filter (· != byP) else gUntil
            { cur with goad? := some (!gBy'.isEmpty, gBy', gUntil') }
          else
            let gBy' := if gBy.contains byP then gBy else gBy.push byP
            let gUntil' := if untilNext && !gUntil.contains byP then gUntil.push byP else gUntil
            { cur with goad? := some (true, gBy', gUntil') }
  | .rules (.permanent (.designation eo .ringBearer gained)) =>
    if let some pid := eo.id then
      if gained then
        if !eo.ringBearer then
          gs := { gs with
            ringBearers := gs.ringBearers.map fun (q, rb) =>
              if rb == some pid then (q, none) else (q, rb) }
        else if let some c := eo.controller then
          gs := { gs with ringBearers := setHistPlOptObj gs.ringBearers c (some pid) }
      else if let some c := eo.controller then
        gs := { gs with ringBearers := setHistPlOptObj gs.ringBearers c (some pid) }
  | .rules (.permanent (.tapped eo _)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with tap? := some false }
  | .rules (.permanent (.untapped eo)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with tap? := some true }
  | .rules (.permanent (.turnedFaceUp eo)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with fd? := some true }
  | .rules (.permanent (.turnedFaceDown eo)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with fd? := some false }
  | .rules (.permanent (.transformed eo _)) =>
    if let some pid := eo.id then
      let prevTr := eo.transformed
      gs := gs.updateObj pid fun cur =>
        let curTr := cur.tr?.getD prevTr
        let curPr := cur.pr?.getD (adjustTokenCardDef eo.token (eo.printed.getD eo.toCardDef))
        let pr0 := if curTr != prevTr then swapCardFace curPr else curPr
        let pr' := applySnapshotPrinted pr0 eo.token eo.printed
        { cur with tr? := some prevTr, pr? := some pr' }
  | .rules (.permanent (.attached eo _ prev)) =>
    if let some aid := eo.id then
      gs := gs.updateObj aid fun cur => { cur with att? := some prev }
  | .rules (.permanent (.unattached eo prevHost)) =>
    if let some aid := eo.id then
      gs := gs.updateObj aid fun cur => { cur with att? := some (some prevHost) }
  | .rules (.permanent (.phasedOut eo _)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with ph? := some false }
  | .rules (.permanent (.phasedIn eo _)) =>
    if let some pid := eo.id then
      gs := gs.updateObj pid fun cur => { cur with ph? := some true }
  | .rules (.zone (.ceasedToExist eo)) =>
    if let some cid := eo.id then
      nonInitMatIds := nonInitMatIds.filter (· != cid)
      gs := gs.updateObjWithZone cid eo.zone fun cur =>
        histUpdateObjEntryFromSnap
          { cur with
            ph? := some (eo.zone == .battlefield && eo.phasedOut)
            prep? := some (defaultBfPrep cid eo)
            att? := some (if eo.zone == .battlefield then eo.attachedTo else none)
            missingInfo? := some (mergeHistMissingInfo cur.missingInfo? eo) }
          eo.zone eo
  | .rules (.zone (.moved before after fromZ _ ..)) =>
    if let some bid := before.id then
      nonInitMatIds := nonInitMatIds.filter (· != bid)
      gs := gs.updateObjWithZone bid fromZ fun cur =>
        histUpdateObjEntryFromSnap
          { cur with
            ph? := some (fromZ == .battlefield && before.phasedOut)
            prep? := some (defaultBfPrep bid { before with zone := fromZ })
            att? := some (if fromZ == .battlefield then before.attachedTo else none)
            missingInfo? := some (mergeHistMissingInfo cur.missingInfo? before) }
          fromZ before
    if let some aid := after.id then
      if before.id != some aid then
        nonInitMatIds := nonInitMatIds.filter (· != aid)
        gs := gs.updateObjWithZone aid (.outside after.owner) fun cur =>
          histClearDepartedObjEntry
            { cur with
              ph? := some false
              prep? := some false
              att? := some none }
            (some after)
  | .rules (.zone (.created eo _)) =>
    if let some eid := eo.id then
      nonInitMatIds := nonInitMatIds.filter (· != eid)
      gs := gs.updateObjWithZone eid (.outside eo.owner) fun cur =>
        histClearDepartedObjEntry
          { cur with
            ph? := some false
            prep? := some false
            att? := some none
            missingInfo? := some (mergeHistMissingInfo cur.missingInfo? eo) }
          (some eo)
  | .engine (.materializeObject obj _) =>
    if isInitialMaterializeWith idxData g obj.id idx then
      wasInitMat := true
      nonInitMatIds := nonInitMatIds.filter (· != obj.id)
      gs := gs.updateObjWithZone obj.id (.outside obj.owner) fun cur =>
        { cur with
          ph? := some false
          fd? := some false
          tr? := some obj.status.transformed
          pr? := some obj.printed
          dc? := some none
          rc? := some none
          tap? := some false
          harn? := some false
          goad? := some (false, #[], #[])
          prep? := some false
          att? := some none
          missingInfo? := some (mergeHistMissingInfo cur.missingInfo? (synthEventObjForMat obj)) }
    else if !nonInitMatIds.contains obj.id then
      nonInitMatIds := nonInitMatIds.push obj.id
  | .rules (.player (.ringTempted p bearer _)) =>
    if let some b := bearer then
      let evBatch := (g.events[idx]?).bind (·.batch)
      let hasPairedDesig := Id.run do
        let mut j := idx
        while j > 0 do
          j := j - 1
          match g.events[j]? with
          | none => break
          | some pe =>
            if pe.batch != evBatch then break
            match pe.change with
            | .rules (.permanent (.designation eo .ringBearer true)) =>
              if eo.id == some b then return true
            | .engine (.logMsg _) => pure ()
            | _ => break
        return false
      if !hasPairedDesig then
        if ((gs.ringBearers.find? (·.1 == p)).bind Prod.snd) == some b then
          gs := { gs with ringBearers := setHistPlOptObj gs.ringBearers p none }
  | .rules (.player (.becameMonarch p prev?)) =>
    let m1 := setHistPlFlag gs.monarchs p false
    let m2 :=
      match prev? with
      | some prev => setHistPlFlag m1 prev true
      | none => m1
    gs := { gs with monarchs := m2 }
  | .rules (.player (.gainedDesignation p .citysBlessing)) =>
    gs := { gs with citysBlessings := setHistPlFlag gs.citysBlessings p false }
  | .rules (.player (.gainedDesignation p .enduringStory)) =>
    gs := { gs with enduringStories := setHistPlFlag gs.enduringStories p false }
  | .rules (.player (.lost p _)) =>
    gs := { gs with ls := setHistPlFlag gs.ls p false }
  | .rules (.player (.leftGame p)) =>
    gs := { gs with
      ls := setHistPlFlag gs.ls p false
      lefts := setHistPlFlag gs.lefts p false }
  | .rules (.turn (.dayNightChanged night)) =>
    gs := { gs with isNight := !night }
  | _ => pure ()
  return (gs, nonInitMatIds, livePreSnaps, wasInitMat)

@[noinline] private def reverseStepSinglePerObj (o : GameObject)
    (defaultBfPrep : ObjectId → EventObject → Bool) (ch : GameChange)
    (livePreSnaps : Array (ObjectId × EventObject)) (wasInitMat : Bool)
    (st : PerObjHistState) : PerObjHistState := Id.run do
  let mut st := st
  for (nid, eo) in livePreSnaps do
    if nid == o.id then
      st := perObjApplyReversePreSnap st eo
  match ch with
  | .rules (.permanent (.designation eo .prepared gained)) =>
    if eo.id == some o.id then st := { st with prep := !gained }
  | .rules (.permanent (.turnedFaceUp eo)) =>
    if eo.id == some o.id then st := { st with fd := true }
  | .rules (.permanent (.turnedFaceDown eo)) =>
    if eo.id == some o.id then st := { st with fd := false }
  | .rules (.permanent (.transformed eo _)) =>
    if eo.id == some o.id then
      let pr0 := if st.tr != eo.transformed then swapCardFace st.pr else st.pr
      st := { st with pr := applySnapshotPrinted pr0 eo.token eo.printed, tr := eo.transformed }
  | .rules (.permanent (.phasedOut eo _)) =>
    if eo.id == some o.id then st := { st with ph := false }
  | .rules (.permanent (.phasedIn eo _)) =>
    if eo.id == some o.id then st := { st with ph := true }
  | .rules (.zone (.ceasedToExist eo)) =>
    if eo.id == some o.id then
      st := perObjApplyReverseCeased st eo (defaultBfPrep o.id eo)
  | .rules (.zone (.moved before after fromZ toZ ..)) =>
    if after.id == some o.id && before.id != some o.id then
      st := perObjApplyReverseMovedAfter st after toZ
    if before.id == some o.id then
      st := perObjApplyReverseMovedBefore st before fromZ
        (defaultBfPrep o.id { before with zone := fromZ })
  | .rules (.zone (.created eo _)) =>
    if eo.id == some o.id then
      st := perObjApplyReverseCreated st o.owner eo
  | .engine (.materializeObject obj _) =>
    if wasInitMat && obj.id == o.id then
      st := perObjApplyReverseInitMat obj
  | _ => pure ()
  return st

@[noinline] private def reverseStepAllPerObj (objs : Array GameObject)
    (objIdxMap : Std.HashMap ObjectId Nat)
    (defaultBfPrep : ObjectId → EventObject → Bool) (ch : GameChange)
    (livePreSnaps : Array (ObjectId × EventObject)) (wasInitMat : Bool)
    (perObjs : Array PerObjHistState) : Array PerObjHistState := Id.run do
  let mut perObjs := perObjs
  for (nid, eo) in livePreSnaps do
    if let some k := objIdxMap.get? nid then
      perObjs := perObjs.set! k (perObjApplyReversePreSnap perObjs[k]! eo)
  match ch with
  | .rules (.permanent (.designation eo .prepared gained)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with prep := !gained }
  | .rules (.permanent (.turnedFaceUp eo)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with fd := true }
  | .rules (.permanent (.turnedFaceDown eo)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with fd := false }
  | .rules (.permanent (.transformed eo _)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        let st := perObjs[k]!
        let pr0 := if st.tr != eo.transformed then swapCardFace st.pr else st.pr
        perObjs := perObjs.set! k
          { st with pr := applySnapshotPrinted pr0 eo.token eo.printed, tr := eo.transformed }
  | .rules (.permanent (.phasedOut eo _)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with ph := false }
  | .rules (.permanent (.phasedIn eo _)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with ph := true }
  | .rules (.zone (.ceasedToExist eo)) =>
    if let some cid := eo.id then
      if let some k := objIdxMap.get? cid then
        perObjs := perObjs.set! k (perObjApplyReverseCeased perObjs[k]! eo (defaultBfPrep cid eo))
  | .rules (.zone (.moved before after fromZ toZ ..)) =>
    if let some aid := after.id then
      if before.id != some aid then
        if let some k := objIdxMap.get? aid then
          perObjs := perObjs.set! k (perObjApplyReverseMovedAfter perObjs[k]! after toZ)
    if let some bid := before.id then
      if let some k := objIdxMap.get? bid then
        perObjs := perObjs.set! k
          (perObjApplyReverseMovedBefore perObjs[k]! before fromZ
            (defaultBfPrep bid { before with zone := fromZ }))
  | .rules (.zone (.created eo _)) =>
    if let some eid := eo.id then
      if let some k := objIdxMap.get? eid then
        perObjs := perObjs.set! k (perObjApplyReverseCreated perObjs[k]! objs[k]!.owner eo)
  | .engine (.materializeObject obj _) =>
    if wasInitMat then
      if let some k := objIdxMap.get? obj.id then
        perObjs := perObjs.set! k (perObjApplyReverseInitMat obj)
  | _ => pure ()
  return perObjs

private def mkDefaultBfPrep (initEffects : Array (EffectId × ContinuousEffectSpec)) :
    ObjectId → EventObject → Bool :=
  let hasPreLogPrepareEffect (sid : ObjectId) : Bool :=
    initEffects.any fun (_, spec) =>
      match spec with
      | .permission _ (.playFromExile _ pm) _ => pm.prepareSource == some sid
      | _ => false
  fun sid eo =>
    eo.zone == .battlefield &&
      (hasPreLogPrepareEffect sid ||
        (!eo.faceDown &&
          if eo.copiable.isSome then eo.prepared
          else eo.prepared || eo.toCardDef.entersPrepared))

@[noinline] private def initHistoricalSliceWith (idxData : InitialMaterializeIndex)
    (g : Game) (o : GameObject) (allCounters : Bool := false) : HistoricalSliceState := Id.run do
  let (initEffects, counterSources) :=
    preLogEffectsAndCounterSources g (if allCounters then none else some o.id)
  let defaultBfPrep := mkDefaultBfPrep initEffects
  let mut gs := initHistGlobalState g initEffects counterSources
  let mut per := PerObjHistState.ofObj o
  let mut nonInitMatIds : Array ObjectId := #[]
  for rev in [0:g.events.size] do
    let idx := g.events.size - 1 - rev
    let ch := g.events[idx]!.change
    let (gs', nonInit', livePre, wasInitMat) :=
      reverseStepHistGlobal g idxData defaultBfPrep idx ch gs nonInitMatIds
    gs := gs'
    nonInitMatIds := nonInit'
    per := reverseStepSinglePerObj o defaultBfPrep ch livePre wasInitMat per
  return { global := gs, per := per }

private def initHistoricalSlice (g : Game) (o : GameObject)
    (allCounters : Bool := false) : HistoricalSliceState :=
  initHistoricalSliceWith (buildInitialMaterializeIndex g) g o allCounters

private def perObjApplyForwardDepart (st : PerObjHistState) (owner : PlayerId) :
    PerObjHistState :=
  let pr' := if st.tr then swapCardFace st.pr else st.pr
  { z := .outside owner, ph := false, fd := false, prep := false,
    pr := pr', tr := false, dc := none, rc := none }

private def perObjApplyForwardMovedAfter (st : PerObjHistState) (after : EventObject)
    (toZ : Zone) (beforePrinted? : Option CardDef := none) : PerObjHistState :=
  let newPh := toZ == .battlefield && after.phasedOut
  let newTr := toZ == .battlefield && after.transformed
  let pr0 := if st.tr != newTr then swapCardFace st.pr else st.pr
  let pr' := applySnapshotPrinted pr0 after.token (after.printed.orElse (fun _ => beforePrinted?))
  let newFd := (toZ == .battlefield || toZ == .stack) && after.faceDown
  let newPrep :=
    toZ == .battlefield && !newFd &&
      if after.copiable.isSome then after.prepared
      else after.prepared || pr'.entersPrepared
  let newDc :=
    if toZ == .battlefield then
      after.defaultController.orElse (fun _ => after.controller)
    else none
  { z := toZ, ph := newPh, fd := newFd, prep := newPrep,
    pr := pr', tr := newTr, dc := newDc, rc := after.controller }

private def perObjApplyForwardCreated (st : PerObjHistState) (eo : EventObject)
    (c : PlayerId) : PerObjHistState :=
  let newPh := eo.zone == .battlefield && eo.phasedOut
  let newTr := eo.zone == .battlefield && eo.transformed
  let pr0 := if st.tr != newTr then swapCardFace st.pr else st.pr
  let eoPrinted :=
    eo.printed.orElse (fun _ => if !eo.name.isEmpty then some eo.toCardDef else none)
  let pr' := applySnapshotPrinted pr0 eo.token eoPrinted
  let c' := eo.controller.orElse (fun _ => some c)
  let newFd := (eo.zone == .battlefield || eo.zone == .stack) && eo.faceDown
  let newPrep :=
    eo.zone == .battlefield && !newFd &&
      if eo.copiable.isSome then eo.prepared
      else eo.prepared || pr'.entersPrepared
  let newDc :=
    if eo.zone == .battlefield then
      eo.defaultController.orElse (fun _ => c')
    else none
  { z := eo.zone, ph := newPh, fd := newFd, prep := newPrep,
    pr := pr', tr := newTr, dc := newDc, rc := c' }

private def perObjApplyForwardMat (obj : GameObject) : PerObjHistState :=
  { z := obj.zone
    ph := obj.zone == .battlefield && obj.status.phasedOut
    fd := obj.status.faceDown
    prep := obj.zone == .battlefield && obj.status.prepared
    pr := obj.printed
    tr := obj.status.transformed
    dc :=
      if obj.zone == .battlefield then
        obj.defaultController.orElse (fun _ => obj.controller)
      else none
    rc := obj.controller }

@[noinline] private def forwardStepHistGlobal (gs : HistGlobalState) (ch : GameChange) :
    HistGlobalState × Bool := Id.run do
  let mut s := gs
  let mut dirty := false
  match ch with
  | .rules (.continuousEffect (.created eid spec)) =>
    let effs := s.effs
    let s0 := { s with effs := #[] }
    s := { s0 with effs := effs.push (eid, spec) }
    match spec with
    | .layered .. => dirty := true
    | _ => pure ()
  | .rules (.continuousEffect (.expired eid _)) =>
    if s.effs.any (·.1 == eid) then
      let effs := s.effs
      let s0 := { s with effs := #[] }
      s := { s0 with effs := effs.filter (·.1 != eid) }
      dirty := true
  | .rules (.permanent (.designation eo .prepared gained)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with prep? := some gained }
      dirty := true
  | .rules (.permanent (.designation eo .harnessed gained)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with harn? := some gained }
      dirty := true
  | .rules (.permanent (.designation eo (.goaded byP untilNext) gained)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur =>
        let (_, gBy, gUntil) := cur.goad?.getD (false, #[], #[])
        let (gBy', gUntil') :=
          if gained then
            let byNow := if gBy.contains byP then gBy else gBy.push byP
            let untilNow :=
              if !untilNext then gUntil.filter (· != byP)
              else if !gBy.contains byP || gUntil.contains byP then
                if gUntil.contains byP then gUntil else gUntil.push byP
              else gUntil
            (byNow, untilNow)
          else
            let untilNow := gUntil.filter (· != byP)
            let byNow :=
              if !untilNext || gUntil.contains byP then gBy.filter (· != byP)
              else gBy
            (byNow, untilNow)
        { cur with goad? := some (!gBy'.isEmpty, gBy', gUntil') }
      dirty := true
  | .rules (.permanent (.designation eo .ringBearer gained)) =>
    if let some pid := eo.id then
      if gained then
        if let some c := eo.controller then
          s := { s with ringBearers := setHistPlOptObj s.ringBearers c (some pid) }
      else
        s := { s with
          ringBearers := s.ringBearers.map fun (q, rb) =>
            if rb == some pid then (q, none) else (q, rb) }
      dirty := true
  | .rules (.permanent (.tapped eo _)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with tap? := some true }
      dirty := true
  | .rules (.permanent (.untapped eo)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with tap? := some false }
      dirty := true
  | .rules (.permanent (.turnedFaceUp eo)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with fd? := some false }
      dirty := true
  | .rules (.permanent (.turnedFaceDown eo)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with fd? := some true }
      dirty := true
  | .rules (.permanent (.transformed eo nowBackFace)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur =>
        let curTr := cur.tr?.getD eo.transformed
        let curPr := cur.pr?.getD (adjustTokenCardDef eo.token (eo.printed.getD eo.toCardDef))
        let pr' := if curTr != nowBackFace then swapCardFace curPr else curPr
        { cur with tr? := some nowBackFace, pr? := some pr' }
      dirty := true
  | .rules (.permanent (.attached eo host _)) =>
    if let some aid := eo.id then
      s := s.updateObj aid fun cur => { cur with att? := some (some host) }
      dirty := true
  | .rules (.permanent (.unattached eo _)) =>
    if let some aid := eo.id then
      s := s.updateObj aid fun cur => { cur with att? := some none }
      dirty := true
  | .rules (.permanent (.counters (.object eo) k _ _)) =>
    if eo.id.any (fun sid => s.counterSources.contains (sid, k)) then
      dirty := true
  | .rules (.permanent (.phasedOut eo _)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with ph? := some true }
      dirty := true
  | .rules (.permanent (.phasedIn eo _)) =>
    if let some pid := eo.id then
      s := s.updateObj pid fun cur => { cur with ph? := some false }
      dirty := true
  | .rules (.zone (.ceasedToExist eo)) =>
    if let some cid := eo.id then
      s := s.updateObjWithZone cid (.outside eo.owner) fun cur =>
        histClearDepartedObjEntry
          { cur with
            ph? := some false
            prep? := some false
            att? := some none }
          (some eo)
      dirty := true
  | .rules (.zone (.moved before after _ toZ ..)) =>
    if let some bid := before.id then
      if after.id != some bid then
        s := s.updateObjWithZone bid (.outside before.owner) fun cur =>
          histClearDepartedObjEntry
            { cur with
              ph? := some false
              prep? := some false
              att? := some none }
            (some before)
        dirty := true
    if let some aid := after.id then
      let effPrinted := after.printed.orElse (fun _ => before.printed)
      let afterMerged := { after with printed := effPrinted }
      let newAidPrep :=
        toZ == .battlefield && !after.faceDown &&
          if after.copiable.isSome then after.prepared
          else after.prepared || (effPrinted.getD after.toCardDef).entersPrepared
      s := s.updateObjWithZone aid toZ fun cur =>
        histUpdateObjEntryFromSnap
          { cur with
            ph? := some (toZ == .battlefield && after.phasedOut)
            prep? := some newAidPrep
            att? := some (if toZ == .battlefield then after.attachedTo else none)
            missingInfo? := some (mergeHistMissingInfo cur.missingInfo? afterMerged) }
          toZ afterMerged before.printed
      dirty := true
  | .rules (.zone (.created eo c)) =>
    if let some eid := eo.id then
      let eoWithCtrl :=
        { eo with
          controller :=
            eo.controller.orElse fun _ =>
              match eo.zone with
              | .battlefield | .stack | .command => some c
              | _ => none }
      let newEidPrep :=
        eo.zone == .battlefield && !eo.faceDown &&
          if eo.copiable.isSome then eo.prepared
          else eo.prepared || (eo.printed.getD eo.toCardDef).entersPrepared
      s := s.updateObjWithZone eid eo.zone fun cur =>
        histUpdateObjEntryFromSnap
          { cur with
            ph? := some (eo.zone == .battlefield && eo.phasedOut)
            prep? := some newEidPrep
            att? := some (if eo.zone == .battlefield then eo.attachedTo else none)
            missingInfo? := some (mergeHistMissingInfo cur.missingInfo? eoWithCtrl) }
          eo.zone eoWithCtrl
      dirty := true
  | .engine (.materializeObject obj _) =>
    s := s.updateObjWithZone obj.id obj.zone fun cur =>
      { cur with
        ph? := some (obj.zone == .battlefield && obj.status.phasedOut)
        fd? := some obj.status.faceDown
        tr? := some obj.status.transformed
        pr? := some obj.printed
        dc? := some (if obj.zone == .battlefield then obj.defaultController.orElse (fun _ => obj.controller) else none)
        rc? := some obj.controller
        tap? := some (obj.zone == .battlefield && obj.status.tapped)
        harn? := some (obj.zone == .battlefield && obj.status.harnessed)
        goad? := some (obj.zone == .battlefield && (obj.status.goaded || !obj.status.goadedBy.isEmpty),
          obj.status.goadedBy, obj.status.goadedUntilNextTurnOf)
        prep? := some (obj.zone == .battlefield && obj.status.prepared)
        att? := some (if obj.zone == .battlefield then obj.attachedTo else none)
        missingInfo? := some (mergeHistMissingInfo cur.missingInfo? (synthEventObjForMat obj)) }
    dirty := true
  | .rules (.player (.ringTempted p bearer _)) =>
    if let some b := bearer then
      s := { s with ringBearers := setHistPlOptObj s.ringBearers p (some b) }
      dirty := true
  | .rules (.player (.becameMonarch p _)) =>
    let cleared := s.monarchs.map fun (q, _) => (q, q == p)
    let monarchs' := if cleared.any (·.1 == p) then cleared else cleared.push (p, true)
    s := { s with monarchs := monarchs' }
    dirty := true
  | .rules (.player (.gainedDesignation p .citysBlessing)) =>
    s := { s with citysBlessings := setHistPlFlag s.citysBlessings p true }
    dirty := true
  | .rules (.player (.gainedDesignation p .enduringStory)) =>
    s := { s with enduringStories := setHistPlFlag s.enduringStories p true }
    dirty := true
  | .rules (.player (.lost p _)) =>
    s := { s with ls := setHistPlFlag s.ls p true }
    dirty := true
  | .rules (.player (.leftGame p)) =>
    s := { s with
      ls := setHistPlFlag s.ls p true
      lefts := setHistPlFlag s.lefts p true
      monarchs := setHistPlFlag s.monarchs p false }
    dirty := true
  | .rules (.turn (.dayNightChanged night)) =>
    s := { s with isNight := night }
    dirty := true
  | _ => pure ()
  return (s, dirty)

@[noinline] private def forwardStepSinglePerObj (o : GameObject) (st : PerObjHistState)
    (ch : GameChange) : PerObjHistState × Bool :=
  match ch with
  | .rules (.permanent (.designation eo .prepared gained)) =>
    if eo.id == some o.id then ({ st with prep := gained }, true) else (st, false)
  | .rules (.permanent (.turnedFaceUp eo)) =>
    if eo.id == some o.id then ({ st with fd := false }, true) else (st, false)
  | .rules (.permanent (.turnedFaceDown eo)) =>
    if eo.id == some o.id then ({ st with fd := true }, true) else (st, false)
  | .rules (.permanent (.transformed eo nowBackFace)) =>
    if eo.id == some o.id then
      let pr' := if st.tr != nowBackFace then swapCardFace st.pr else st.pr
      ({ st with pr := pr', tr := nowBackFace }, true)
    else (st, false)
  | .rules (.permanent (.counters (.object eo) ..)) =>
    (st, eo.id == some o.id)
  | .rules (.permanent (.phasedOut eo _)) =>
    if eo.id == some o.id then ({ st with ph := true }, true) else (st, false)
  | .rules (.permanent (.phasedIn eo _)) =>
    if eo.id == some o.id then ({ st with ph := false }, true) else (st, false)
  | .rules (.zone (.ceasedToExist eo)) =>
    if eo.id == some o.id then (perObjApplyForwardDepart st eo.owner, true) else (st, false)
  | .rules (.zone (.moved before after _ toZ ..)) =>
    if before.id == some o.id && after.id != some o.id then
      (perObjApplyForwardDepart st before.owner, true)
    else if after.id == some o.id then
      (perObjApplyForwardMovedAfter st after toZ before.printed, true)
    else (st, false)
  | .rules (.zone (.created eo c)) =>
    if eo.id == some o.id then (perObjApplyForwardCreated st eo c, true) else (st, false)
  | .engine (.materializeObject obj _) =>
    if obj.id == o.id then (perObjApplyForwardMat obj, true) else (st, false)
  | _ => (st, false)

@[noinline] private def forwardStepAllPerObj (objIdxMap : Std.HashMap ObjectId Nat)
    (perObjs : Array PerObjHistState) (ch : GameChange) : Array PerObjHistState := Id.run do
  let mut perObjs := perObjs
  match ch with
  | .rules (.permanent (.designation eo .prepared gained)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with prep := gained }
  | .rules (.permanent (.turnedFaceUp eo)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with fd := false }
  | .rules (.permanent (.turnedFaceDown eo)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with fd := true }
  | .rules (.permanent (.transformed eo nowBackFace)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        let st := perObjs[k]!
        let pr' := if st.tr != nowBackFace then swapCardFace st.pr else st.pr
        perObjs := perObjs.set! k { st with pr := pr', tr := nowBackFace }
  | .rules (.permanent (.phasedOut eo _)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with ph := true }
  | .rules (.permanent (.phasedIn eo _)) =>
    if let some pid := eo.id then
      if let some k := objIdxMap.get? pid then
        perObjs := perObjs.set! k { perObjs[k]! with ph := false }
  | .rules (.zone (.ceasedToExist eo)) =>
    if let some cid := eo.id then
      if let some k := objIdxMap.get? cid then
        perObjs := perObjs.set! k (perObjApplyForwardDepart perObjs[k]! eo.owner)
  | .rules (.zone (.moved before after _ toZ ..)) =>
    if let some bid := before.id then
      if after.id != some bid then
        if let some k := objIdxMap.get? bid then
          perObjs := perObjs.set! k (perObjApplyForwardDepart perObjs[k]! before.owner)
    if let some aid := after.id then
      if let some k := objIdxMap.get? aid then
        perObjs := perObjs.set! k (perObjApplyForwardMovedAfter perObjs[k]! after toZ before.printed)
  | .rules (.zone (.created eo c)) =>
    if let some eid := eo.id then
      if let some k := objIdxMap.get? eid then
        perObjs := perObjs.set! k (perObjApplyForwardCreated perObjs[k]! eo c)
  | .engine (.materializeObject obj _) =>
    if let some k := objIdxMap.get? obj.id then
      perObjs := perObjs.set! k (perObjApplyForwardMat obj)
  | _ => pure ()
  return perObjs

private def stepHistoricalSlice (o : GameObject) (st : HistoricalSliceState)
    (ch : GameChange) : HistoricalSliceState × Bool :=
  let (g', d1) := forwardStepHistGlobal st.global ch
  let (p', d2) := forwardStepSinglePerObj o st.per ch
  ({ global := g', per := p' }, d1 || d2)

private def buildCounterSourceMap (counterSources : Array (ObjectId × CounterKind)) :
    Std.HashMap ObjectId (Array CounterKind) :=
  counterSources.foldl (fun m (sid, k) =>
    let ks := (m.get? sid).getD #[]
    m.insert sid (ks.push k)) {}

private def applyHistTrackedCounters (g : Game) (csMap : Std.HashMap ObjectId (Array CounterKind))
    (evLen : Nat) (obj : GameObject) : GameObject :=
  match csMap.get? obj.id with
  | none => obj
  | some ks =>
    let bag :=
      ks.foldl (fun acc k => acc.set k (g.objectCounterCountAt obj.id k evLen))
        obj.status.counters
    if bag == obj.status.counters then obj
    else { obj with status := { obj.status with counters := bag } }

private def buildMissingHistObjs (g : Game) (gs : HistGlobalState)
    (isPresent : ObjectId → Bool) (fallbackOwner : PlayerId)
    (csMap : Std.HashMap ObjectId (Array CounterKind)) (evLen : Nat) : Array GameObject :=
  gs.zsOrder.filterMap fun zid =>
    if isPresent zid then none
    else
      match gs.objs.get? zid with
      | none => none
      | some ent =>
        match ent.z? with
        | none => none
        | some z =>
          let nonOutside := match z with | .outside _ => false | _ => true
          if nonOutside then
            let pOut := z == .battlefield && (ent.ph?.getD false)
            let attTo := if z == .battlefield then ent.att?.join else none
            let info? := ent.missingInfo?
            let pr : CardDef :=
              match ent.pr? with
              | some p => p
              | none =>
                match info? with
                | some eo => adjustTokenCardDef eo.token eo.toCardDef
                | none => { name := "", types := #[] }
            let own := (info?.map (·.owner)).getD fallbackOwner
            let ctrl :=
              match ent.rc? with
              | some c => c
              | none => info?.bind (·.controller)
            let dc :=
              if z == .battlefield then
                match ent.dc? with
                | some d => d.orElse (fun _ => ctrl)
                | none => (info?.bind (·.defaultController)).orElse (fun _ => ctrl)
              else none
            let fd := (z == .battlefield || z == .stack) &&
              (ent.fd?.getD (info?.any (·.faceDown)))
            let tr := z == .battlefield &&
              (ent.tr?.getD (info?.any (·.transformed)))
            let prep :=
              z == .battlefield &&
                (ent.prep?.getD
                  (!fd &&
                    match info? with
                    | some eo =>
                      if eo.copiable.isSome then eo.prepared
                      else eo.prepared || pr.entersPrepared
                    | none => pr.entersPrepared))
            let tapped := z == .battlefield && (ent.tap?.getD (info?.any (·.tapped)))
            let harnessed := z == .battlefield && (ent.harn?.getD (info?.any (·.harnessed)))
            let (goaded, goadedBy, goadedUntil) :=
              if z == .battlefield then
                ent.goad?.getD
                  (info?.any (fun eo => eo.goaded || !eo.goadedBy.isEmpty),
                   (info?.map (·.goadedBy)).getD #[],
                   (info?.map (·.goadedUntilNextTurnOf)).getD #[])
              else (false, #[], #[])
            let allowChosen := z == .battlefield && !fd
            some (applyHistTrackedCounters g csMap evLen
              ({ id := zid, printed := pr, owner := own,
                 defaultController := dc,
                 controller := ctrl,
                 attachedTo := attTo,
                 zone := z,
                 status := {
                   tapped := tapped
                   phasedOut := pOut
                   faceDown := fd
                   prepared := prep
                   transformed := tr
                   harnessed := harnessed
                   goaded := goaded
                   goadedBy := goadedBy
                   goadedUntilNextTurnOf := goadedUntil
                   chosenOdd := if allowChosen then info?.bind (·.chosenOdd) else none
                   chosenCreatureType := if allowChosen then info?.bind (·.chosenCreatureType) else none
                   chosenColor := if allowChosen then info?.bind (·.chosenColor) else none
                   chosenName := if allowChosen then info?.bind (·.chosenName) else none
                   chosenCardType := if allowChosen then info?.bind (·.chosenCardType) else none
                   chosenAnchor := if allowChosen then info?.bind (·.chosenAnchor) else none
                 } } : GameObject))
          else none

private def buildHistPlayersAt (g : Game) (gs : HistGlobalState) : Array Player :=
  g.players.map fun pl =>
    let v := (gs.ls.find? (·.1 == pl.id)).map Prod.snd |>.getD pl.lost
    let leftV := (gs.lefts.find? (·.1 == pl.id)).map Prod.snd |>.getD pl.leftTheGame
    let rb := (gs.ringBearers.find? (·.1 == pl.id)).map Prod.snd |>.getD pl.ringBearerId
    let mon := (gs.monarchs.find? (·.1 == pl.id)).map Prod.snd |>.getD pl.isMonarch
    let cb := (gs.citysBlessings.find? (·.1 == pl.id)).map Prod.snd |>.getD pl.citysBlessing
    let es := (gs.enduringStories.find? (·.1 == pl.id)).map Prod.snd |>.getD pl.enduringStory
    { pl with
      lost := v
      leftTheGame := leftV
      ringBearerId := rb
      isMonarch := mon
      citysBlessing := cb
      enduringStory := es }

@[noinline] private def mkHistoricalGameForObjAt (g : Game) (o : GameObject)
    (st : HistoricalSliceState) (evLen : Nat) : Game × GameObject :=
  let gs := st.global
  let p := st.per
  let csMap :=
    if gs.counterSources.isEmpty then {} else buildCounterSourceMap gs.counterSources
  let oEnt? := if p.z == .battlefield then gs.objs.get? o.id else none
  let oAtt :=
    if p.z == .battlefield then
      match oEnt?.bind (·.att?) with
      | some v => v
      | none => o.attachedTo
    else none
  let oTap := p.z == .battlefield && ((oEnt?.bind (·.tap?)).getD o.status.tapped)
  let oHarn := p.z == .battlefield && ((oEnt?.bind (·.harn?)).getD o.status.harnessed)
  let (oGoad, oGoadBy, oGoadUntil) :=
    if p.z == .battlefield then
      (oEnt?.bind (·.goad?)).getD (o.status.goaded || !o.status.goadedBy.isEmpty,
        o.status.goadedBy, o.status.goadedUntilNextTurnOf)
    else (false, #[], #[])
  let oAt : GameObject :=
    applyHistTrackedCounters g csMap evLen
      { o with
        printed := p.pr
        zone := p.z
        defaultController := p.dc
        controller := p.rc
        attachedTo := oAtt
        status := {
          o.status with
          tapped := oTap
          faceDown := p.fd
          phasedOut := p.ph
          prepared := p.prep
          transformed := p.tr
          harnessed := oHarn
          goaded := oGoad
          goadedBy := oGoadBy
          goadedUntilNextTurnOf := oGoadUntil } }
  let objsAt0 := g.objects.map fun obj =>
    if obj.id == o.id then oAt
    else
      let ent? := gs.objs.get? obj.id
      let z := (ent?.bind (·.z?)).getD obj.zone
      let pOut := z == .battlefield && ((ent?.bind (·.ph?)).getD obj.status.phasedOut)
      let fd := (z == .battlefield || z == .stack) && ((ent?.bind (·.fd?)).getD obj.status.faceDown)
      let tr := z == .battlefield && ((ent?.bind (·.tr?)).getD obj.status.transformed)
      let pr := (ent?.bind (·.pr?)).getD obj.printed
      let dc := (ent?.bind (·.dc?)).getD obj.defaultController
      let rc := (ent?.bind (·.rc?)).getD obj.controller
      let prep :=
        z == .battlefield && ((ent?.bind (·.prep?)).getD obj.status.prepared)
      let tap := z == .battlefield && ((ent?.bind (·.tap?)).getD obj.status.tapped)
      let harn := z == .battlefield && ((ent?.bind (·.harn?)).getD obj.status.harnessed)
      let (gd, gdBy, gdUntil) :=
        if z == .battlefield then
          (ent?.bind (·.goad?)).getD (obj.status.goaded || !obj.status.goadedBy.isEmpty,
            obj.status.goadedBy, obj.status.goadedUntilNextTurnOf)
        else (false, #[], #[])
      let attTo :=
        if z == .battlefield then
          match ent?.bind (·.att?) with
          | some v => v
          | none => obj.attachedTo
        else none
      applyHistTrackedCounters g csMap evLen
        { obj with
          printed := pr
          zone := z
          defaultController := dc
          controller := rc
          attachedTo := attTo
          status := {
            obj.status with
            tapped := tap
            faceDown := fd
            phasedOut := pOut
            prepared := prep
            transformed := tr
            harnessed := harn
            goaded := gd
            goadedBy := gdBy
            goadedUntilNextTurnOf := gdUntil } }
  let presentIds : Std.HashMap ObjectId Unit :=
    g.objects.foldl (fun m obj => m.insert obj.id ()) (Std.HashMap.emptyWithCapacity (g.objects.size + 8))
  let missingObjs := buildMissingHistObjs g gs presentIds.contains o.owner csMap evLen
  let objsAt := objsAt0 ++ missingObjs
  let plsAt := buildHistPlayersAt g gs
  ({ g with
     isNight := gs.isNight
     activeEffects := gs.effs
     objects := objsAt
     players := plsAt
     events := g.events.extract 0 (min evLen g.events.size) }, oAt)

/-- Historical `Game` state reconstructed at event prefix `g.events[0 : evLen]`
for batch-level Layer 2 / CR 800.4c control reconciliation (CR 613.1 / 702.26b / 800.4c). -/
@[noinline] def mkHistoricalGameAt (g : Game) (evLen : Nat) : Game :=
  if evLen ≥ g.events.size then g
  else Id.run do
    let bound := min evLen g.events.size
    let idxData := buildInitialMaterializeIndex g
    let (initEffects, counterSources) := preLogEffectsAndCounterSources g none
    let defaultBfPrep := mkDefaultBfPrep initEffects
    let mut gs := initHistGlobalState g initEffects counterSources
    let mut objIdxMap : Std.HashMap ObjectId Nat := Std.HashMap.emptyWithCapacity (g.objects.size + 8)
    let mut perObjs : Array PerObjHistState := Array.mkEmpty g.objects.size
    for k in [0 : g.objects.size] do
      let obj := g.objects[k]!
      objIdxMap := objIdxMap.insert obj.id k
      perObjs := perObjs.push (PerObjHistState.ofObj obj)
    let mut nonInitMatIds : Array ObjectId := #[]
    for rev in [0 : g.events.size] do
      let idx := g.events.size - 1 - rev
      let ch := g.events[idx]!.change
      let (gs', nonInit', livePre, wasInitMat) :=
        reverseStepHistGlobal g idxData defaultBfPrep idx ch gs nonInitMatIds
      gs := gs'
      nonInitMatIds := nonInit'
      perObjs := reverseStepAllPerObj g.objects objIdxMap defaultBfPrep ch livePre wasInitMat perObjs
    for i in [0 : bound] do
      let ch := g.events[i]!.change
      let (gs', _) := forwardStepHistGlobal gs ch
      gs := gs'
      perObjs := forwardStepAllPerObj objIdxMap perObjs ch
    let csMap :=
      if gs.counterSources.isEmpty then {} else buildCounterSourceMap gs.counterSources
    let mut objsAt0 : Array GameObject := Array.mkEmpty g.objects.size
    for k in [0 : g.objects.size] do
      let obj := g.objects[k]!
      let p := perObjs[k]!
      let ent? := if p.z == .battlefield then gs.objs.get? obj.id else none
      let oAtt :=
        if p.z == .battlefield then
          match ent?.bind (·.att?) with
          | some v => v
          | none => obj.attachedTo
        else none
      let tap := p.z == .battlefield && ((ent?.bind (·.tap?)).getD obj.status.tapped)
      let harn := p.z == .battlefield && ((ent?.bind (·.harn?)).getD obj.status.harnessed)
      let (gd, gdBy, gdUntil) :=
        if p.z == .battlefield then
          (ent?.bind (·.goad?)).getD (obj.status.goaded || !obj.status.goadedBy.isEmpty,
            obj.status.goadedBy, obj.status.goadedUntilNextTurnOf)
        else (false, #[], #[])
      let oAt : GameObject :=
        applyHistTrackedCounters g csMap bound
          { obj with
            printed := p.pr
            zone := p.z
            defaultController := p.dc
            controller := p.rc
            attachedTo := oAtt
            status :=
              { obj.status with
                tapped := tap
                faceDown := p.fd
                phasedOut := p.ph
                prepared := p.prep
                transformed := p.tr
                harnessed := harn
                goaded := gd
                goadedBy := gdBy
                goadedUntilNextTurnOf := gdUntil } }
      objsAt0 := objsAt0.push oAt
    let fallbackOwner :=
      (g.objects[0]?.map (·.owner)).getD ((g.players[0]?.map (·.id)).getD g.activePlayer)
    let missingObjs := buildMissingHistObjs g gs objIdxMap.contains fallbackOwner csMap bound
    let plsAt := buildHistPlayersAt g gs
    return { g with
      isNight := gs.isNight
      activeEffects := gs.effs
      objects := objsAt0 ++ missingObjs
      players := plsAt
      events := g.events.extract 0 bound }

/-- Historical Layer 2 controller of `o` at event prefix `g.events[0 : evLen]`
(CR 502.1 / 613.1a–b / 702.26m,n / 800.4a). -/
def controllerOfAt (g : Game) (o : GameObject) (evLen : Nat) : Option PlayerId :=
  if evLen ≥ g.events.size then
    if o.zone == .battlefield then g.controllerOf o else o.controller
  else
    Id.run do
      let mut cur := initHistoricalSlice g o
      for i in [0 : evLen] do
        let (next, _) := stepHistoricalSlice o cur g.events[i]!.change
        cur := next
      let (gAt, oAt) := mkHistoricalGameForObjAt g o cur evLen
      return if oAt.zone == .battlefield then gAt.controllerOf oAt else oAt.controller

/-- True when summoning sickness currently prevents `o` from attacking or
paying a `{T}` cost (CR 302.6), using Layer 4 `isCreature`, Layer 2 continuous
control since the controller's most recent turn began, and Layer 6 `hasHaste`. -/
def hasSummoningSickness (g : Game) (o : GameObject) : Bool :=
  if !o.isOnBattlefield || !g.isCreature o || g.hasHaste o then false
  else if o.status.summoningSick then true
  else
    match g.controllerOf o with
    | none => false
    | some ctrl =>
      Id.run do
        let turnStartIdx? := g.lastTurnStartIdx? ctrl
        let startScanIdx :=
          match turnStartIdx? with
          | some tsIdx => tsIdx + 1
          | none => 0
        let mut counterSourcesAtNow? : Option (Array (ObjectId × CounterKind)) := none
        let mut idxData? : Option InitialMaterializeIndex := none
        let mut sawUnoverriddenArrival : Bool := false
        let mut overrideIdx? : Option Nat := none
        let mut sawWindowCtrlChange : Bool := false
        for i in [startScanIdx : g.events.size] do
          let ev := g.events[i]!
          match ev.change with
          | .rules (.zone (.moved before after fromZ toZ ..)) =>
            if before.id == some o.id && toZ != .battlefield then
              sawWindowCtrlChange := true
              overrideIdx? := none
              sawUnoverriddenArrival := true
            if after.id == some o.id && toZ == .battlefield then
              sawWindowCtrlChange := true
              if fromZ != .battlefield then
                if !after.summoningSick && after.printed.isSome then
                  overrideIdx? := some i
                  sawUnoverriddenArrival := false
                else
                  overrideIdx? := none
                  sawUnoverriddenArrival := true
          | .rules (.zone (.created eo _)) =>
            if eo.zone == .battlefield && eo.id == some o.id then
              sawWindowCtrlChange := true
              overrideIdx? := none
              sawUnoverriddenArrival := true
          | .rules (.continuousEffect (.created _ spec)) =>
            match spec with
            | .layered .. => sawWindowCtrlChange := true
            | _ => pure ()
          | .rules (.continuousEffect (.expired eid spec?)) =>
            if spec?.any isCtrlOrCopyEffectSpec || g.isCtrlOrCopyEffectId eid then
              sawWindowCtrlChange := true
          | .rules (.permanent (.turnedFaceUp eo))
          | .rules (.permanent (.turnedFaceDown eo))
          | .rules (.permanent (.transformed eo _)) =>
            if eo.id == some o.id then
              sawWindowCtrlChange := true
          | .rules (.permanent (.attached ..))
          | .rules (.permanent (.unattached ..)) =>
            sawWindowCtrlChange := true
          | .rules (.permanent (.counters (.object eo) k _ _)) =>
            if eo.id == some o.id then
              sawWindowCtrlChange := true
            else if let some sid := eo.id then
              if counterSourcesAtNow?.isNone then
                counterSourcesAtNow? := some (preLogEffectsAndCounterSources g (some o.id)).2
              if counterSourcesAtNow?.getD #[] |>.contains (sid, k) then
                sawWindowCtrlChange := true
          | .rules (.permanent (.phasedOut ..))
          | .rules (.permanent (.phasedIn ..)) =>
            sawWindowCtrlChange := true
          | .engine (.materializeObject obj _) =>
            sawWindowCtrlChange := true
            if obj.id == o.id then
              let idxData :=
                match idxData? with
                | some d => d
                | none => buildInitialMaterializeIndex g
              if idxData?.isNone then
                idxData? := some idxData
              if isInitialMaterializeWith idxData g obj.id i then
                if obj.zone == .battlefield then
                  if !obj.status.summoningSick && !obj.printed.isToken then
                    overrideIdx? := some i
                    sawUnoverriddenArrival := false
                  else
                    overrideIdx? := none
                    sawUnoverriddenArrival := true
                else
                  overrideIdx? := none
                  sawUnoverriddenArrival := true
              else if obj.zone != .battlefield ||
                  (g.objectZoneAndPhasedOutAt? obj.id i).all (·.1 != .battlefield) then
                overrideIdx? := none
                sawUnoverriddenArrival := true
          | .rules (.player (.lost ..)) | .rules (.player (.leftGame ..)) =>
            sawWindowCtrlChange := true
          | _ => pure ()
        if sawUnoverriddenArrival then return true
        let effStartIdx? := overrideIdx?.orElse (fun _ => turnStartIdx?)
        let hasActiveCtrlOrCopy :=
          g.activeEffects.any fun (_, s) =>
            match s with
            | .layered _ (.control _) _ | .layered _ (.copy _) _ => true
            | _ => false
        if !sawWindowCtrlChange && !hasActiveCtrlOrCopy &&
            (effStartIdx?.isSome || some ctrl == g.initialControllerOf o) then
          return false
        let idxData :=
          match idxData? with
          | some d => d
          | none => buildInitialMaterializeIndex g
        let mut cur := initHistoricalSliceWith idxData g o
        match effStartIdx? with
        | none =>
          let (g0At, o0At) := mkHistoricalGameForObjAt g o cur 0
          if o0At.zone != .battlefield then
            return true
          if (!o0At.status.phasedOut && g0At.initialControllerOf o0At != some ctrl) ||
              g0At.controllerOf o0At != some ctrl then
            return true
        | some _ => pure ()
        for i in [0:g.events.size] do
          let (next, dirty) := stepHistoricalSlice o cur g.events[i]!.change
          cur := next
          let checkNow :=
            match effStartIdx? with
            | none => dirty
            | some sIdx => i == sIdx || (i > sIdx && dirty)
          if checkNow then
            let (gAt, oAt) := mkHistoricalGameForObjAt g o cur (i + 1)
            if oAt.zone != .battlefield || gAt.controllerOf oAt != some ctrl then
              return true
        return false

/-- Evaluated triggered abilities of `o` in Layer 6 (CR 613.1f / 613.7 / 613.8). -/
def triggeredAbilities (g : Game) (o : GameObject) : Array TriggeredAbility :=
  if o.isLkiSnapshot then
    o.printed.triggeredAbilities
  else
  let hasTrigEff := g.activeEffects.any fun (_, s) =>
    match s with
    | .layered _ (.abilities add rem) d =>
      g.durationActive d &&
        (rem == .all || !add.triggeredAbilities.isEmpty || !add.staticAbilities.isEmpty ||
          !(expandedKeywordTriggers add.keywords).isEmpty)
    | _ => false
  let hasAtt :=
    o.isOnBattlefield &&
      g.objects.any fun att => att.isOnBattlefield && att.attachedTo == some o.id && att.id != o.id
  let trigOrStripStatic : StaticAbility → Bool
    | .continuous _ _ mod =>
      modAnyLeaf (fun
        | .loseAllAbilities => true
        | .grantTriggered trs => !trs.isEmpty
        | .grantKeywords ks => !(KeywordAbility.expandAll ks).triggeredAbilities.isEmpty
        | .grantStatic sas => !sas.isEmpty
        | _ => false) mod
    | _ => false
  let hasSelfTrigOrStrip :=
    o.isOnBattlefield && !isFaceDownMasked o &&
      (g.baseCard o).staticAbilities.any trigOrStripStatic
  let hasPeerOrEmbTrigOrStrip :=
    !isStackAbilityObj o && g.hasPeerOrEmblemStaticLayer6 o trigOrStripStatic
  let hasTrigCounter :=
    !o.status.counters.isEmpty &&
      (o.status.counterCount .exalted > 0 || o.status.counterCount .decayed > 0)
  if !hasTrigEff && !hasAtt && !hasSelfTrigOrStrip && !hasPeerOrEmbTrigOrStrip && !hasTrigCounter &&
      !(o.isOnBattlefield && g.hasActiveBasicLandSetEffect) then
    if isFaceDownMasked o then #[]
    else
      let bc := g.baseCard o
      let impTrig : Array TriggeredAbility :=
        if bc.impending.isSome then #[TriggeredAbility.impendingEndStep]
        else #[]
      let kwTrigs := expandedKeywordTriggers bc.keywords
      let rawPrintedTrigs :=
        if bc.isMarduOrJeskaiChoice && o.status.chosenAnchor != some "Jeskai" then
          bc.triggeredAbilities.filter fun ab =>
            match ab.effect.body with
            | .ifCond (.exists (.filter .this (.chosenAnchorIs "Jeskai"))) _ _ => false
            | _ => true
        else bc.triggeredAbilities
      if rawPrintedTrigs.isEmpty then impTrig ++ kwTrigs
      else
        let tcs := g.evalLayer3 o
        let base :=
          if tcs.isEmpty then rawPrintedTrigs
          else rawPrintedTrigs.map (TextChange.applyTriggeredAbility tcs)
        base ++ impTrig ++ kwTrigs
  else
    (g.evalLayer6Fast o).triggers

/-- Greatest chapter number among the Layer-6 chapter abilities currently on `o`
(CR 715.2d / 613.1f). Returns `0` when `o` has no chapter abilities (including
after Layer-6 ability removal or while face down). -/
def finalChapterNumber (g : Game) (o : GameObject) : Nat :=
  TriggeredAbility.finalChapterNumberOf (g.triggeredAbilities o)

/-- Prowess triggers of `o`, one for each instance evaluated in Layer 6
timestamp order (CR 613.1f / 613.7 / 702.108). -/
def prowessTriggers (g : Game) (o : GameObject) : Array TriggeredAbility :=
  if o.isLkiSnapshot then
    let cnt := (o.lkiLayer6.map (·.prowessCount)).getD 0
    if cnt == 0 then #[]
    else
      Array.replicate cnt (TriggeredAbility.ofPattern .youCastNoncreature
        (Instruction.pumpFixed .this 1 1))
  else if !o.isOnBattlefield then #[]
  else
    let cnt := (g.evalLayer6Fast o).prowessCount
    if cnt == 0 then #[]
    else
      Array.replicate cnt (TriggeredAbility.ofPattern .youCastNoncreature
        (Instruction.pumpFixed .this 1 1))

/-- Number of Iron Fist tap abilities currently granted to `o` in Layer 6. -/
def ironFistTapGrants (g : Game) (o : GameObject) : Nat :=
  if o.isLkiSnapshot then
    (o.lkiLayer6.map (·.ironFistTapGrants)).getD 0
  else
    let hasEff := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.abilities add _) d => g.durationActive d && add.ironFistTapGrants > 0
      | _ => false
    if !hasEff then 0
    else (g.evalLayer6Fast o).ironFistCount

/-- Printed and granted ward costs currently on `o` in Layer 6 (CR 613.1f / 702.21). -/
def wardCostsOn (g : Game) (o : GameObject) : Array CostSpec :=
  if o.isLkiSnapshot then
    (o.lkiLayer6.map (·.wardCosts)).getD #[]
  else
    let hasWardEff := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.abilities add rem) d =>
        g.durationActive d &&
          (rem == .all || !add.staticAbilities.isEmpty ||
            !(KeywordAbility.wardCosts add.keywords).isEmpty)
      | _ => false
    if !o.isOnBattlefield && !hasWardEff &&
        !(!isStackAbilityObj o && g.hasPeerOrEmblemStaticLayer6 o staticAffectsKeywords) &&
        (g.baseCard o).staticAbilities.isEmpty then
      if isFaceDownMasked o then #[]
      else KeywordAbility.wardCosts (g.currentKeywords o)
    else
      (g.evalLayer6Fast o).wards


private def hasAnyManaGrantSource (g : Game) : Bool :=
  g.objects.any (fun src =>
    src.isOnBattlefield &&
      (g.baseCard src).staticAbilities.any fun
        | .continuous _ _ mod =>
          modAnyLeaf (fun
            | .grantActivated abs => !abs.isEmpty
            | _ => false) mod
        | _ => false) ||
  g.activeEffects.any fun (_, s) =>
    match s with
    | .permission _ (.colorlessGrant _ _) d => g.durationActive d
    | _ => false

/-- Activated abilities of `o` evaluated in Layer 6 (plus special-action morph
turn-face-up when `o.status.faceDown`, CR 613.1f / 702.37e). Includes CR 305.6
intrinsic basic-land mana abilities and Layer-6 granted mana abilities. -/
def activatedAbilitiesOf (g : Game) (o : GameObject) : Array ActivatedAbility :=
  let normalizeEquip (ab : ActivatedAbility) : ActivatedAbility :=
    if ab.effect == Effect.attachToTargetCreatureYouControl &&
        (ab.equipSubtype?.isSome || ab.isEquipWorthy) then
      { ab with effect := Effect.equipEffect ab.equipSubtype? ab.isEquipWorthy }
    else ab
  let raw :=
    if o.isLkiSnapshot then
      match o.lkiLayer6 with
      | some l6 => l6.activatedAbilities
      | none => if isFaceDownMasked o then #[] else o.printed.allActivatedAbilities
    else if !isFaceDownMasked o then
      let bc := g.baseCard o
      let hasActEff := g.activeEffects.any fun (_, s) =>
        match s with
        | .layered _ (.abilities add rem) d =>
          g.durationActive d &&
            (rem == .all || !add.staticAbilities.isEmpty ||
              !(KeywordAbility.expandAll add.keywords).activatedAbilities.isEmpty ||
              add.ironFistTapGrants > 0)
        | _ => false
      let hasPeerOrEmbActOrStrip :=
        !isStackAbilityObj o &&
          g.hasPeerOrEmblemStaticLayer6 o fun
            | .continuous _ _ mod =>
              modAnyLeaf (fun
                | .loseAllAbilities => true
                | .grantActivated abs => !abs.isEmpty
                | .grantKeywords ks => !(KeywordAbility.expandAll ks).activatedAbilities.isEmpty
                | .grantStatic sas => !sas.isEmpty
                | .copyActivatedFrom _ => true
                | _ => false) mod
            | _ => false
      let canUseFastPath :=
        bc.staticAbilities.isEmpty && bc.crew.isNone &&
          !g.isPlaneswalker o && !hasActEff && !hasPeerOrEmbActOrStrip &&
          (!o.isOnBattlefield ||
            (!g.isLand o && !g.hasActiveBasicLandSetEffect && !g.hasAnyManaGrantSource &&
              !g.objects.any fun att =>
                att.isOnBattlefield && att.attachedTo == some o.id && att.id != o.id))
      if canUseFastPath then
        let baseAct := bc.allActivatedAbilities
        if baseAct.isEmpty then #[]
        else
          let tcs := g.evalLayer3 o
          if tcs.isEmpty then baseAct
          else
            let ownAct := bc.activatedAbilities.map (TextChange.applyActivatedAbility tcs)
            let kwAct :=
              (KeywordAbility.expandAll (HasTextChange.applyTextChanges tcs bc.keywords)).activatedAbilities.filter
                fun ab => !ownAct.contains ab
            ownAct ++ kwAct
      else
        (g.evalLayer6Fast o).activated
    else
      let morphAb : Array ActivatedAbility :=
        if o.isOnBattlefield then
          match (g.unmaskedCopiableValues o).morphCost? with
          | some cost =>
            #[{ effect := { body := .permanent (.turnFaceUp .this) }
                cost := cost }]
          | none => #[]
        else #[]
      morphAb ++ (g.evalLayer6Fast o).activated
  if raw.any (fun ab => ab.effect == Effect.attachToTargetCreatureYouControl &&
      (ab.equipSubtype?.isSome || ab.isEquipWorthy)) then
    raw.map normalizeEquip
  else raw

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
        let status :=
          if costs.contains .morph then { status with faceDown := true }
          else status
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
  | .targeted obj targets division skipped =>
    match g.stack.findIdx? (·.objectId == obj) with
    | some i =>
      let se := g.stack[i]!
      { g with stack := g.stack.set! i { se with
          targets := targets
          dividedDamage := division
          skippedOptionalSlots :=
            if skipped.isEmpty then se.skippedOptionalSlots else skipped
          targetsAnnounced := true } }
    | none => g
  | .spellCast .. => g
  | .abilityActivated ability source player kind =>
    match kind with
    | .nonMana _ _ _ _ abilityIdx _ =>
      if g.objects.any (·.id == ability) then g
      else
        let ts : Nat := g.timestamp + 1
        let ab? : Option ActivatedAbility :=
          match abilityIdx with
          | some idx =>
            match source.id.bind (fun sid => g.objects.find? (·.id == sid)) with
            | some liveSrc => (g.activatedAbilitiesOf liveSrc)[idx]?
            | none =>
              (source.copiable.orElse (fun _ => source.printed)).bind (fun c => c.allActivatedAbilities[idx]?)
          | none => none
        let abilityEffect : Option Effect :=
          match ab? with
          | some ab => if ab.isModal then none else some ab.effect
          | none => none
        let fresh : GameObject :=
          { id := ability
            printed := { name := s!"{source.name}'s ability", types := #[] }
            owner := source.owner
            controller := some player
            zone := .stack
            timestamp := ts
            abilityEffect := abilityEffect
            sourceId := source.id }
        let se : StackEntry :=
          { objectId := ability
            controller := player
            targets := #[] }
        { g with
          objects := g.objects.push fresh
          stack := g.stack.push se
          nextObjectId := max g.nextObjectId (ability.raw + 1)
          timestamp := max g.timestamp ts
          consecutivePasses := 0 }
    | .mana .. => g

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
  | .delayedTrigger e => g.applyDelayedTriggerEvent e

/-- Process one `GameChange` in isolation. -/
def applyChange (g : Game) (c : GameChange) : Game :=
  match c with
  | .rules r => g.applyRulesEvent r
  | .engine e => g.applyEngineChange e

def controlChanged (g : Game) (o : GameObject) : Bool :=
  if !o.isBattlefieldObject then
    false
  else
    let defCtrl := o.defaultController.getD o.owner
    if g.controllerOf o != some defCtrl ||
        (o.controller.isSome && o.controller != some defCtrl) ||
        !(g.appliedControlEffectIds o).isEmpty then
      true
    else
      let isPotentialCtrlSpec (sp : ContinuousEffectSpec) : Bool :=
        match sp with
        | .layered (.objects ids) (.control _) _ => ids.contains o.id
        | .layered _ (.control _) _ => true
        | _ => false
      let hasPotentialHistCtrlChange :=
        g.activeEffects.any (fun (_, sp) => isPotentialCtrlSpec sp) ||
        g.events.any fun ev =>
          match ev.change with
          | .rules (.continuousEffect (.created _ sp))
          | .rules (.continuousEffect (.expired _ (some sp))) => isPotentialCtrlSpec sp
          | .rules (.continuousEffect (.expired _ none)) => true
          | .rules (.zone (.moved before after ..)) =>
            before.id == some o.id || after.id == some o.id
          | .engine (.materializeObject obj _) =>
            obj.id == o.id
          | _ => false
      if !hasPotentialHistCtrlChange then false
      else Id.run do
        let init := initHistoricalSlice g o
        let mut arrivalSlice : Nat := 0
        let mut curZ := init.z
        for i in [0 : g.events.size] do
          match g.events[i]!.change with
          | .rules (.zone (.moved before after fromZ toZ ..)) =>
            if before.id == some o.id && after.id != some o.id then
              curZ := .outside before.owner
            else if after.id == some o.id then
              if toZ == .battlefield &&
                  (curZ != .battlefield || before.id != some o.id || fromZ != .battlefield) then
                arrivalSlice := i + 1
              curZ := toZ
          | .rules (.zone (.created eo _)) =>
            if eo.id == some o.id then
              if eo.zone == .battlefield then
                arrivalSlice := i + 1
              curZ := eo.zone
          | .rules (.zone (.ceasedToExist eo)) =>
            if eo.id == some o.id then
              curZ := .outside eo.owner
          | .engine (.materializeObject obj _) =>
            if obj.id == o.id then
              if obj.zone == .battlefield &&
                  (curZ != .battlefield || g.isInitialMaterialize obj.id i) then
                arrivalSlice := i + 1
              curZ := obj.zone
          | _ => pure ()
        let curCtrl := g.controllerOf o
        let checkSlice (slice : HistoricalSliceState) (evLen : Nat) : Bool :=
          if slice.z != .battlefield then false
          else
            let (gAt, oAt) := mkHistoricalGameForObjAt g o slice evLen
            let defAt := oAt.defaultController.getD oAt.owner
            let ctrlAt := gAt.controllerOf oAt
            ctrlAt != some defAt || ctrlAt != curCtrl || ctrlAt != some defCtrl ||
              !(gAt.appliedControlEffectIds oAt).isEmpty
        if arrivalSlice == 0 && checkSlice init 0 then
          return true
        let mut cur := init
        for i in [0 : g.events.size] do
          let (next, dirty) := stepHistoricalSlice o cur g.events[i]!.change
          cur := next
          let sliceIdx := i + 1
          if sliceIdx == arrivalSlice || (sliceIdx > arrivalSlice && dirty) then
            if checkSlice cur sliceIdx then
              return true
        return false


/-- Hidden Lair's colored add ability: this land entered this turn, or you
control a basic land. -/
def canUseEnteredOrBasicAdd (g : Game) (o : GameObject) : Bool :=
  g.loggedEntered o.id ||
    match g.controllerOf o with
    | some p => g.controlsBasicLand p
    | none => false

/-- Mana types granted to `o` (`{T}: Add`) evaluated in Layer 6 (CR 605.1a / 613.1f). -/
def grantedManaAbilities (g : Game) (o : GameObject) : Array ManaType :=
  if !o.isOnBattlefield || o.isLkiSnapshot then #[] else (g.evalLayer6Fast o).manaGrants

/-- Whether `o` is a battlefield land with an active Chromatic Lantern mana grant in Layer 6. -/
def landHasLanternGrant (g : Game) (o : GameObject) : Bool :=
  if !o.isOnBattlefield || o.isLkiSnapshot || !g.isLand o then false
  else if !g.hasAnyStaticLayer6Effect &&
      !g.objects.any (fun src =>
        src.isOnBattlefield &&
          (g.baseCard src).staticAbilities.any fun
            | .continuous _ sc mod =>
              sc == StaticAbility.scopeLandsYouControl &&
                mod.flatten.any (fun | .grantActivated abs => abs.any (·.isManaAbility) | _ => false)
            | _ => false) then
    false
  else (g.evalLayer6Fast o).lanternGrant

/-- Whether `o` retains an active Emrakul `{T}: Add {C}{C}` grant in Layer 6. -/
def hasActiveColorlessGrant (g : Game) (o : GameObject) : Bool :=
  if !o.isOnBattlefield || o.isLkiSnapshot then false
  else
    let hasGrant := g.activeEffects.any fun (_, s) =>
      match s with
      | .permission _ (.colorlessGrant landId _) d => landId == o.id && g.durationActive d
      | _ => false
    if !hasGrant then false
    else (g.evalLayer6Fast o).colorlessGrant

/-- Whether `p` controls a permanent with storied in Layer 6. -/
def controlsStoried (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => g.hasStoried o)

/-- Whether `p` controls a permanent with ascend in Layer 6 (CR 702.131b). -/
def controlsAscend (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => g.hasAscend o)

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

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast and is not an uncast stack copy (CR 707.10 / 707.12). -/
def wasCast (g : Game) (id : ObjectId) : Bool :=
  GameEvent.wasCast g.events id

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast from a graveyard. -/
def castFromGraveyard (g : Game) (id : ObjectId) : Bool :=
  GameEvent.castFromGraveyard g.events id

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast from a hand. -/
def castFromHand (g : Game) (id : ObjectId) : Bool :=
  GameEvent.castFromHand g.events id

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

/-- Whether mana from a Treasure was spent to cast `id` (CR 106.6 / 400.7d / 707.10 / 707.12). -/
def treasureManaSpent (g : Game) (id : ObjectId) : Bool :=
  if !g.wasCast id then false
  else
    let spellId := GameEvent.stackSpellIdOf g.events id
    if GameEvent.isUncastStackCopy g.events spellId || GameEvent.isUncastStackCopy g.events id then false
    else GameEvent.treasureManaSpentOn g.events spellId

/-- Cards exiled from a graveyard to pay the boast activation cost of `abilityId` (MSH 227). -/
def boastExiledOf (g : Game) (abilityId : ObjectId) : Array ObjectId :=
  GameEvent.boastExiledOf g.events abilityId

/-- Whether a first-strike combat damage step has completed in the current
combat phase (CR 510.4 / 702.7b), derived from `TurnEvent.extraStepAdded .combatDamage .afterCurrent`. -/
def firstStrikeDamageDone (g : Game) : Bool :=
  Id.run do
    let mut i := g.events.size
    while i > 0 do
      i := i - 1
      match g.events[i]!.change with
      | .rules (.turn (.extraStepAdded .combatDamage .afterCurrent)) =>
        return true
      | .rules (.turn (.phaseBegan _))
      | .rules (.turn (.phaseEnded _))
      | .rules (.turn (.turnBegan _ _))
      | .rules (.turn (.turnEnded _)) =>
        return false
      | _ => pure ()
    return false

/-- Whether the second (regular) combat damage step added by CR 510.4 / 702.7b
has not yet begun in the current combat phase. -/
def pendingRegularCombatDamage (g : Game) : Bool :=
  Id.run do
    let mut i := g.events.size
    while i > 0 do
      i := i - 1
      match g.events[i]!.change with
      | .rules (.turn (.extraStepAdded .combatDamage .afterCurrent)) =>
        return true
      | .rules (.turn (.stepBegan .combatDamage _))
      | .rules (.turn (.phaseBegan _))
      | .rules (.turn (.phaseEnded _))
      | .rules (.turn (.turnBegan _ _))
      | .rules (.turn (.turnEnded _)) =>
        return false
      | _ => pure ()
    return false

/-- Creatures that assigned combat damage in the first-strike combat damage step
of the current combat phase, once that step's deal has completed (CR 702.7b). -/
def firstStrikeAssignedThisCombat (g : Game) : Array ObjectId :=
  if !g.firstStrikeDamageDone then #[]
  else Id.run do
    let mut out : Array ObjectId := #[]
    let mut i := g.events.size
    while i > 0 do
      i := i - 1
      match g.events[i]!.change with
      | .rules (.combat (.damageAssigned true _ batch)) =>
        for a in batch do
          if !out.contains a.source then
            out := out.push a.source
      | .rules (.turn (.phaseBegan _))
      | .rules (.turn (.phaseEnded _))
      | .rules (.turn (.turnBegan _ _))
      | .rules (.turn (.turnEnded _)) =>
        return out
      | _ => pure ()
    return out

/-- Whether `CombatEvent.damageAssigned (firstStrike := true)` was recorded in
the current step. -/
def hasFirstStrikeAssignmentInCurrentStep (g : Game) : Bool :=
  Id.run do
    let mut i := g.events.size
    while i > 0 do
      i := i - 1
      match g.events[i]!.change with
      | .rules (.combat (.damageAssigned true _ _)) =>
        return true
      | .rules (.turn (.stepBegan _ _))
      | .rules (.turn (.stepEnded _))
      | .rules (.turn (.phaseBegan _))
      | .rules (.turn (.phaseEnded _))
      | .rules (.turn (.turnBegan _ _))
      | .rules (.turn (.turnEnded _)) =>
        return false
      | _ => pure ()
    return false

/-- Whether `srcId` has (or last had on the battlefield before leaving or phasing
out, CR 106.6 / 608.2h / 702.26b / 707.2) Path of Ancestry's mana-spent
commander creature-type scry trigger. -/
def isAncestrySourceId (g : Game) (srcId : ObjectId) : Bool :=
  let fromBattlefieldLki : Bool :=
    (g.lastKnownBefore? srcId).any (fun snap =>
      snap.zone == .battlefield && snap.triggeredAbilities.any (·.isManaSpentCastScry))
  match g.findLiveSourceObject? srcId with
  | some l =>
    if l.isOnBattlefield then
      (g.triggeredAbilities l).any (·.isManaSpentCastScry)
    else
      fromBattlefieldLki
  | none =>
    fromBattlefieldLki

/-- Whether mana produced by a permanent with Path of Ancestry's
mana-spent commander creature-type scry trigger was spent to cast `spellId`,
resolving `ManaUnit.source` on the battlefield or via its pre-departure /
pre-phase-out battlefield LKI (CR 106.6 / 608.2h / 702.26b / 707.2). -/
def ancestryManaSpentOn (g : Game) (spellId : ObjectId) : Bool :=
  let preCast := g.events.extract 0 (GameEvent.castEventBound g.events spellId)
  preCast.any fun e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      (forObj == some spellId || oid? == some spellId) &&
        units.any (fun u => u.source.any g.isAncestrySourceId)
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      forObj == some spellId && units.any (fun u => u.source.any g.isAncestrySourceId)
    | _, _ => false

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
  if o.zone == .battlefield then g.controllerOf o
  else ((g.lastKnownBefore? o.id).bind (·.controller)).orElse (fun _ => o.controller)


/-- Player who must declare blockers now. -/
def currentBlockersPlayer (g : Game) : PlayerId :=
  g.defendingPlayer

/-- Legal attack destination: a living opponent of `p` (CR 508.1). Omitted
means the next opponent in turn order. -/
def resolveAttackDestination (g : Game) (p : PlayerId) (defender : Option PlayerId) :
    Except String PlayerId :=
  match defender with
  | none =>
    let d := g.opponent p
    if d == p || !g.stillInGame d || !(g.livingOpponents p).any (fun pl => pl.id == d) then
      throw "no living opponent to attack"
    else .ok d
  | some d =>
    if d == p then throw "cannot attack yourself"
    else if !g.stillInGame d then throw s!"{(g.player d).name} has already lost"
    else if !(g.livingOpponents p).any (fun pl => pl.id == d) then
      throw s!"{(g.player d).name} is not an opponent"
    else .ok d

def nextLiving (g : Game) (p : PlayerId) : PlayerId :=
  let n := g.players.size
  Id.run do
    for k in [1:n+1] do
      let q : PlayerId := ⟨(p.idx + k) % n⟩
      if g.stillInGame q then
        return q
    return p

/-- Player who receives priority in place of `p` when `p` has left (CR 800.4j). -/
def priorityInstead (g : Game) (p : PlayerId) : PlayerId :=
  if !g.stillInGame p then g.nextLiving p else p

/-- How many creatures `p` currently controls. -/
def countCreaturesControlledBy (g : Game) (p : PlayerId) : Nat :=
  (g.creaturesControlledBy p).size

/-- How many artifacts `p` currently controls (evaluated after Layer 4). -/
def countArtifactsControlledBy (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (g.isArtifact ·) |>.size

/-- Artifacts on the battlefield controlled by a living opponent of `controller` (after Layer 2 & Layer 4). -/
def countOpponentArtifacts (g : Game) (controller : PlayerId) : Nat :=
  g.battlefield.filter (fun o =>
    g.isArtifact o && (g.controllerOf o).any (g.isLivingOpponentOf controller ·)) |>.size

/-- Active player-controlling effect controlling `whose` (latest wins, CR 613.7 /
724.5; in Two-Headed Giant, controlling a player also controls their teammate,
CR 810 / MSH 236). -/
def controllingPlayerOf? (g : Game) (whose : PlayerId) : Option PlayerId :=
  g.activeEffects.foldl (fun acc (eid, s) =>
    match s with
    | .playerRule you (.controlsPlayer them onNextTurn) d =>
      let inWindow := !onNextTurn || (g.hasTurnBegunSince eid them && !g.hasTurnAfterBegunSince eid them)
      if g.durationActive d && inWindow &&
          you.idx < g.players.size && g.stillInGame you &&
          (them == whose || g.areTeammates them whose) then
        some you
      else acc
    | _ => acc) none

/-- Whether `you` currently control `them`. In Two-Headed Giant, controlling
a player also controls their teammate (MSH 236). -/
def controlsPlayer (g : Game) (you them : PlayerId) : Bool :=
  g.controllingPlayerOf? them == some you

/-- Resources used to pay `actingAs`'s costs: always that player's, even if
another player is making the choices (MSH 346). -/
def resourcesFor (g : Game) (actingAs : PlayerId) : PlayerId :=
  let _ := g
  actingAs

/-- You still make your own choices while controlling another player
(MSH 334) and you make all of that player's choices (MSH 336). -/
def decidesFor (g : Game) (actor whose : PlayerId) : Bool :=
  match g.controllingPlayerOf? whose with
  | some you => actor == you
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
outside the game (CR 724.5b; MSH 349). -/
def canChooseOutsideGame (_g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose

/-- Tournament-rule decisions stay with the actual player (CR 724.5; MSH 350). -/
def canMakeTournamentDecision (_g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose

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

/-- Player putting counters: the resolving spell or ability's controller,
or `fallback` when none is resolving. -/
def counterPutter (g : Game) (fallback : Option PlayerId) : Option PlayerId :=
  (((g.resolvingSpell.orElse (fun _ => g.resolvingAbility)).bind g.findObject?).bind
    (g.controllerOf ·))
    |>.orElse (fun _ => g.currentResolvingContext?.bind Prod.snd)
    |>.orElse (fun _ => fallback)

/-- Living players in APNAP order (CR 101.4 / 805.6–7), with all living members
of the active team (in seat order starting from the active team's first seat)
preceding nonactive teams in turn order. -/
def apnapPlayers (g : Game) : Array PlayerId :=
  let n := g.players.size
  if n == 0 then #[]
  else Id.run do
    let firstActiveSeat := (g.teamMembers g.activePlayer)[0]?.getD g.activePlayer
    let start := firstActiveSeat.idx % n
    let mut seen : Array PlayerId := #[]
    let mut out : Array PlayerId := #[]
    for offset in [0:n] do
      let pid : PlayerId := ⟨(start + offset) % n⟩
      if !seen.contains pid then
        for m in g.teamMembers pid do
          seen := seen.push m
          if g.stillInGame m then
            out := out.push m
    return out

/-- Wrap `cause` in `EventCause.replaced id orig` when replacement or prevention
effect `id` applies (CR 614.6 / 615.6). Preserves batch/resolving-context cause
upgrade when `cause` is `none`, without minting an `EffectId` until the event is
recorded (or falling back to `defaultCause` outside resolution). -/
def wrapReplacedCause (g : Game) (id : ReplacementId) (cause : Option EventCause)
    (defaultActor : Option PlayerId := none)
    (defaultCause : EventCause := .gameRule .continuousEffect) : Option EventCause :=
  some (.replaced id (g.resolveOptionalCause cause (fallbackCtrl := defaultActor) (defaultCause := defaultCause)))

/-- Whether two replacement/prevention effects in the same CR 616.1a–e tier
produce an identical outcome regardless of application order, so the engine
can apply either first without pausing for `Pending.chooseReplacement` when no
explicit `g.replacementOrder` preference is set. -/
def replacementPairCommutes (a b : ReplacementOrPrevention) : Bool :=
  let isTapOrCounter616e : ReplacementKind → Bool
    | .entersTappedSelf _
    | .entersTappedDeclinePayLife _ | .entersUntappedPayLife ..
    | .entersTappedDeclineBehold _ | .entersUntappedBehold ..
    | .entersWithCountersSelf .. | .entersWithExtraCounters .. => true
    | _ => false
  let isChoose616e : ReplacementKind → Bool
    | .asEntersChooseColor .. | .asEntersChooseCreatureType ..
    | .asEntersChooseOdd .. | .asEntersChooseCardName ..
    | .asEntersChooseCardType .. | .asEntersChooseAnchor .. => true
    | _ => false
  let isTap616e : ReplacementKind → Bool
    | .entersTappedSelf _
    | .entersTappedDeclinePayLife _ | .entersUntappedPayLife ..
    | .entersTappedDeclineBehold _ | .entersUntappedBehold .. => true
    | _ => false
  let isCounter616e : ReplacementKind → Bool
    | .entersWithCountersSelf .. | .entersWithExtraCounters .. => true
    | _ => false
  match a, b with
  | .replacement sa, .replacement sb =>
    if (isTapOrCounter616e sa.kind && isChoose616e sb.kind) ||
        (isChoose616e sa.kind && isTapOrCounter616e sb.kind) ||
        (isTap616e sa.kind && isCounter616e sb.kind) ||
        (isCounter616e sa.kind && isTap616e sb.kind) then
      true
    else
      match sa.kind, sb.kind with
      | .entersTappedSelf _, .entersTappedSelf _
      | .entersTappedSelf _, .entersUntappedPayLife ..
      | .entersUntappedPayLife .., .entersTappedSelf _
      | .entersTappedSelf _, .entersTappedDeclinePayLife _
      | .entersTappedDeclinePayLife _, .entersTappedSelf _
      | .entersTappedSelf _, .entersUntappedBehold ..
      | .entersUntappedBehold .., .entersTappedSelf _
      | .entersTappedSelf _, .entersTappedDeclineBehold _
      | .entersTappedDeclineBehold _, .entersTappedSelf _ => true
      | .entersWithCountersSelf _ ka _, .entersWithCountersSelf _ kb _ => ka != kb
      | .entersWithCountersSelf .., .entersWithExtraCounters ..
      | .entersWithExtraCounters .., .entersWithCountersSelf .. => true
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
      | .artifactTokensBecome _ _, .multiplyTokenCreation _ _
      | .multiplyTokenCreation _ _, .artifactTokensBecome _ _ => true
      | _, _ => false
  | .prevention pa, .replacement sb =>
    match pa.kind, sb.kind with
    | .shieldCounterPreventDamage _, _ => false
    | _, .addNoncombatDamage _ _ | _, .multiplyDamage _ _ => true
    | _, _ => false
  | .prevention pa, .prevention pb =>
    match pa.kind, pb.kind with
    | .shieldCounterPreventDamage _, _ | _, .shieldCounterPreventDamage _ => false
    | _, _ => true
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
   candidates tie in `pool` (or an open-ended prompt is present), return
   `.needChoice chooser (pool.map (·.id)) order`. -/
def selectNextReplacementStep (g : Game) (candidates : Array ReplacementCandidate)
    (applied : Array ReplacementId)
    (order : Array ReplacementId := g.replacementOrder) : ReplacementSelection :=
  let isOpenPrompt (c : ReplacementCandidate) : Bool :=
    c.id.kind == .asEntersChooseCreatureTypePrompt ||
      c.id.kind == .asEntersChooseCardNamePrompt
  let unapplied := candidates.filter (fun (c : ReplacementCandidate) => !applied.contains c.id)
  if unapplied.isEmpty then .none
  else
    let minRank := unapplied.foldl (fun m (c : ReplacementCandidate) => min m c.tier.rank) 100
    let inTier := unapplied.filter (fun (c : ReplacementCandidate) => c.tier.rank == minRank)
    let effectivePlayer (c : ReplacementCandidate) : PlayerId :=
      if g.stillInGame c.affectedPlayer then c.affectedPlayer
      else g.nextLiving c.affectedPlayer
    let apnap := g.apnapPlayers
    let chooser? := apnap.find? (fun p => inTier.any (fun (c : ReplacementCandidate) => effectivePlayer c == p))
    let chooser := chooser?.getD (effectivePlayer inTier[0]!)
    let pool :=
      match chooser? with
      | some p => inTier.filter (fun (c : ReplacementCandidate) => effectivePlayer c == p)
      | none => inTier
    let matchesPref (prefId : ReplacementId) (cid : ReplacementId) : Bool :=
      cid == prefId ||
        (prefId.counterKind.isNone && cid.counterKind.isSome && { cid with counterKind := none } == prefId)
    match order.findSome? (fun prefId => pool.find? (fun (c : ReplacementCandidate) => matchesPref prefId c.id)) with
    | some c =>
      let rem :=
        match order.findIdx? (fun prefId => matchesPref prefId c.id) with
        | some idx => order.eraseIdx! idx
        | none => order
      .chosen c rem
    | none =>
      let nonPrompts := pool.filter (!isOpenPrompt ·)
      match nonPrompts.find? (fun d =>
          pool.all (fun e => d.id == e.id || (!isOpenPrompt e && replacementPairCommutes d.spec e.spec))) with
      | some d =>
        if pool.size == 1 || !pool.any isOpenPrompt then
          .chosen d order
        else
          .needChoice chooser (pool.map (·.id)) order
      | none =>
        if !pool.any isOpenPrompt && (pool.size <= 1 || poolAllCommute pool) then
          match pool[0]? with
          | some c => .chosen c order
          | none => .none
        else
          .needChoice chooser (pool.map (·.id)) order


/-- Legal players, planeswalkers, and battles that a creature put onto the
battlefield attacking under `controller`'s control may be chosen to attack
(CR 506.2 / 506.3b / 508.4 / 805.10a / 810.7). -/
def legalEnteringAttackTargets (g : Game) (controller : PlayerId) : Array AttackTarget :=
  if g.step.phase != .combat || !g.isOnActiveTeam controller then #[]
  else
    let opps := g.livingOpponents controller
    let playerTargets : Array AttackTarget := opps.map (fun pl => .player pl.id)
    let permanentTargets : Array AttackTarget :=
      g.battlefield.filterMap fun o =>
        if !opps.any (fun pl => g.controlledBy o pl.id) then none
        else if g.isPlaneswalker o then
          if g.cantAttackJace controller o then none
          else some (.planeswalker o.id)
        else if g.hasType o .battle then
          some (.battle o.id)
        else none
    playerTargets ++ permanentTargets

/-- Default defending opponent for a creature entering attacking or made
attacking under `controller`'s control, or `none` when no living opponent
remains (CR 508.1a / 508.4 / 810.7). -/
def defaultAttackOpponent? (g : Game) (controller : PlayerId) : Option PlayerId :=
  let defn := g.defendingPlayer
  if g.isLivingOpponentOf controller defn then some defn
  else g.firstLivingOpponent? controller

/-- Resolve the `AttackTarget` for a creature entering the battlefield attacking
or made attacking under `controller`'s control, returning `none` when no legal
target exists or `controller` isn't an attacking player during combat so the
permanent is not attacking (CR 506.2 / 506.3b / 508.4c / 805.10a / 810.7). -/
def resolveEnteringAttackTarget? (g : Game) (controller : PlayerId)
    (attacking : Bool) (attackingTarget : Option AttackTarget) : Option AttackTarget :=
  if !(attacking || attackingTarget.isSome) then none
  else if g.step.phase != .combat || !g.isOnActiveTeam controller then
    none
  else
    match attackingTarget with
    | some (.player p) =>
      if g.isLivingOpponentOf controller p then some (.player p)
      else (g.defaultAttackOpponent? controller).map .player
    | some (.planeswalker pwId) =>
      if (g.findObject? pwId).any (fun pw =>
          pw.isOnBattlefield && g.isPlaneswalker pw &&
            !(g.cantAttackJace controller pw) &&
            (g.livingOpponents controller).any (fun pl => g.controlledBy pw pl.id)) then
        some (.planeswalker pwId)
      else (g.defaultAttackOpponent? controller).map .player
    | some (.battle bId) =>
      if (g.findObject? bId).any (fun b =>
          b.isOnBattlefield &&
            (g.livingOpponents controller).any (fun pl => g.controlledBy b pl.id)) then
        some (.battle bId)
      else (g.defaultAttackOpponent? controller).map .player
    | none =>
      (g.defaultAttackOpponent? controller).map .player

/-- Mana value of other spells `p` has cast this turn. Copies that were not
cast are not recorded. -/
def otherCastManaValueThisTurn (g : Game) (p : PlayerId) : Nat :=
  (g.loggedCastManaValues p).foldl (· + ·) 0

-- Layer 7a–7d: Power and toughness evaluation (CR 613.4a–d / 613.7 / 613.8)

/-- Lands `p` currently controls after Layer 4 (CR 305.1 / 613.1d). -/
def landsYouControl (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (g.isLand ·) |>.size

/-- Whether `o` currently has a “P/T equal to lands you control” ability.
This characteristic-defining ability functions in all zones (CR 208.2a / 604.3). -/
def hasLandsYouControlPT (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (· == StaticAbility.powerToughnessEqualLandsYouControl)

/-- Number of card types among cards in all graveyards (Tarmogoyf). Card
types, not cards, are counted, and supertypes are not card types (rulings
797 / 800). -/
def graveyardCardTypeCount (g : Game) : Nat :=
  let types := g.objects.foldl (fun acc o =>
    match o.zone with
    | .graveyard _ => (g.types o).foldl (fun acc t =>
        if acc.contains t then acc else acc.push t) acc
    | _ => acc) (#[] : Array CardType)
  types.size

/-- Basic land types among lands `p` controls (domain; CR 305.6). -/
def basicLandTypesAmong (g : Game) (p : PlayerId) : Nat :=
  (#[CardSubtype.plains, .island, .swamp, .mountain, .forest].filter (fun t =>
    (g.permanentsOf p).any (fun o => g.isLand o && g.hasSubtype o t))).size

/-- Componentwise sum of two power/toughness bonuses. -/
def addStats (a b : Int × Int) : Int × Int :=
  (a.1 + b.1, a.2 + b.2)

def pumpOf (g : Game) (o : GameObject) : Int × Int :=
  if o.isLkiSnapshot then (0, 0)
  else
    g.activeEffects.foldl (fun (ap, atg) (eid, s) =>
      match s with
      | .layered scope (.ptModify pw tg) d =>
        let isUntilTurn := match d with | .untilNextTurnOf _ => true | _ => false
        if !isUntilTurn && g.scopeMatches scope o (eid? := some eid) (dur? := some d) &&
            g.durationActive d then
          (ap + pw, atg + tg)
        else (ap, atg)
      | _ => (ap, atg)) (0, 0)

def untilTurnOfPump (g : Game) (o : GameObject) : Array (PlayerId × Int × Int) :=
  if o.isLkiSnapshot then #[]
  else
    g.activeEffects.filterMap fun (eid, s) =>
      match s with
      | .layered scope (.ptModify pw tg) (.untilNextTurnOf p) =>
        if g.scopeMatches scope o (eid? := some eid) (dur? := some (.untilNextTurnOf p)) then
          some (p, pw, tg)
        else none
      | _ => none

/-- Instant and sorcery cards in `p`'s graveyard (Glamdring). -/
def instantSorceryInGraveyard (g : Game) (p : PlayerId) : Nat :=
  (g.player p).graveyard.filter (fun id =>
    match g.findObject? id with
    | some c => g.isInstantOrSorcery c
    | none => false) |>.size

/-- Layer 7c `+1/+1` for each artifact you control from active
`.ptCda .pumpPerArtifact` effects (Iron Man Armor, CR 613.4c). -/
def artifactCountPump (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield || o.isLkiSnapshot then (0, 0)
  else
    let mult : Nat :=
      g.activeEffects.foldl (fun cnt (eid, s) =>
        match s with
        | .layered sc (.ptCda .pumpPerArtifact) d =>
          if g.scopeMatches sc o (eid? := some eid) (dur? := some d) && g.durationActive d then
            cnt + 1
          else cnt
        | _ => cnt) 0
    if mult == 0 then (0, 0)
    else
      let arts := (g.permanentsOf (g.you o)).filter (g.isArtifact ·) |>.size
      let bonus : Int := Int.ofNat (mult * arts)
      (bonus, bonus)

private structure Layer7bEntry where
  idx : Nat
  ts : Nat × Nat
  scope : ObjectScope
  setP : Option Int
  setT : Option Int
deriving Inhabited

private structure Layer7cDepEntry where
  idx : Nat
  ts : Nat × Nat
  src : GameObject
  srcCtrl : PlayerId
  cond? : Option Condition
  sc : ObjectFilter
  ptExprs : Array (ValueExpr × ValueExpr)
deriving Inhabited

/-- Layer-6 keyword checks beyond `currentKeywords` for live objects (ward costs
and Equip activated abilities; CR 702.6a / 702.21). -/
private def liveObjectHasExtraKeyword (g : Game) (target : GameObject) (kw : KeywordTag) : Bool :=
  match kw with
  | .ward => !(g.wardCostsOn target).isEmpty
  | .param .equip =>
    (g.retainsPrintedAbilities target && (g.baseCard target).allActivatedAbilities.any (·.isEquip)) ||
      (g.activatedAbilitiesOf target).any (·.isEquip)
  | _ => false

mutual

/-- Cycle-guarded Layer 7a power and toughness of `o` (CR 604.3 / 613.4a). -/
private partial def cdaBasePTAux (g : Game) (visited : Array (ObjectId × (Int × Int)))
    (o : GameObject) : Int × Int :=
  if o.status.faceDown && o.isOnBattlefield then (2, 2)
  else
    let bc := g.baseCard o
    let baseBox := (bc.powerValue.getD 0, bc.toughnessValue.getD 0)
    if bc.staticAbilities.isEmpty || !g.retainsPrintedAbilities o || visited.any (·.1 == o.id) then
      baseBox
    else
      let youP := g.you o
      let oTcs := g.evalLayer3 o
      let printedStatics :=
        if oTcs.isEmpty then bc.staticAbilities
        else bc.staticAbilities.map (TextChange.applyStaticAbility oTcs)
      let nextVis := visited.push (o.id, baseBox)
      let ptOf := some (fun x => g.snapshotPTAux nextVis x)
      let kwOf := some g.currentKeywords
      let kwExtra := some g.liveObjectHasExtraKeyword
      printedStatics.foldl (fun (pw, tg) ab =>
        match ab with
        | .characteristicDefining (.setPT p? t?) =>
          let pw' := match p? with | some v => g.evalStaticValL5 o youP v (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra) | none => pw
          let tg' := match t? with | some v => g.evalStaticValL5 o youP v (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra) | none => tg
          (pw', tg')
        | _ => (pw, tg)) baseBox

/-- Cycle-guarded Layer 7b base P/T-setting evaluation on `o` (CR 613.4b / 613.7 / 613.8). -/
private partial def evalLayer7bAux (g : Game) (visited : Array (ObjectId × (Int × Int)))
    (o : GameObject) (base7a : Int × Int) : Option Int × Option Int :=
  if !o.isOnBattlefield || visited.any (·.1 == o.id) then (none, none)
  else
    let has7bEff := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.ptSet ..) d
      | .layered _ (.ptCda .cardsInHandPower) d => g.durationActive d
      | _ => false
    let modSetsBasePT (mod : ContinuousModification) : Bool :=
      mod.flatten.any fun | .setBasePT p? t? => p?.isSome || t?.isSome | _ => false
    let hasBasePtAtt :=
      g.objects.any fun att =>
        att.isOnBattlefield && att.attachedTo == some o.id && att.id != o.id &&
          (g.staticAbilities att).any fun
            | .continuous _ sc mod => StaticAbility.isAttachedHostScope sc && modSetsBasePT mod
            | _ => false
    let hasCdaGrantEff := g.activeEffects.any fun (_, s) =>
      match s with
      | .layered _ (.abilities add _) d =>
        g.durationActive d && add.staticAbilities.any StaticAbility.isPTDefiningCDA
      | _ => false
    if !has7bEff && !hasBasePtAtt && !hasCdaGrantEff then (none, none)
    else
      let (bc, baseTs) := g.baseCardWithTs o
      let youP := g.you o
      let handP : Int :=
        Int.ofNat ((g.player youP).hand.filter (fun id => (g.findObject? id).any isDiscardableCard)).size
      let l6 := g.evalLayer6 o
      let hasPrintedPtCda :=
        l6.retainsBase && bc.staticAbilities.any StaticAbility.isPTDefiningCDA
      let nextVis := visited.push (o.id, base7a)
      let ptOf := some (fun x => g.snapshotPTAux nextVis x)
      let kwOf := some g.currentKeywords
      let kwExtra := some g.liveObjectHasExtraKeyword
      let applyStep (cur : Option Int × Option Int) (e : Layer7bEntry) : Option Int × Option Int :=
        (e.setP.orElse (fun _ => cur.1), e.setT.orElse (fun _ => cur.2))
      Id.run do
        let mut raw : Array Layer7bEntry := #[]
        -- 1. Attached Auras/Equipment setting base P/T at CR 613.7a / 613.7e timestamp.
        if hasBasePtAtt then
          for att in g.battlefield do
            if att.attachedTo == some o.id && att.id != o.id then
              let attL6 := g.evalLayer6 att
              let attAttachTs := g.attachmentTimestamp att o.id
              let attCtrl := g.controllerOf att |>.getD att.owner
              for (ab, abTs) in attL6.staticsWithTs do
                match ab with
                | .continuous cond? sc mod =>
                  if g.matchesStaticScopeL5 att attCtrl o sc ptOf kwOf (hasKwExtra? := kwExtra) &&
                      cond?.all (fun c => g.evalStaticCondL5 att attCtrl c (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra)) then
                    for m in mod.flatten do
                      match m with
                      | .setBasePT p? t? =>
                        if p?.isSome || t?.isSome then
                          raw := raw.push {
                            idx := raw.size
                            ts := maxTs attAttachTs abTs
                            scope := .objects #[o.id]
                            setP := p?.map (fun v => g.evalStaticValL5 att attCtrl v (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra))
                            setT := t?.map (fun v => g.evalStaticValL5 att attCtrl v (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra))
                          }
                      | _ => pure ()
                | _ => pure ()
        -- 2. Non-base Layer 6 granted P/T CDAs at their CR 613.7a grant timestamp.
        let mut skippedPrintedCda : Nat := 0
        let printedCdaCount := if hasPrintedPtCda then (bc.staticAbilities.filter StaticAbility.isPTDefiningCDA).size else 0
        for (ab, abTs) in l6.staticsWithTs do
          match ab with
          | .characteristicDefining (.setPT p? t?) =>
            if hasPrintedPtCda && skippedPrintedCda < printedCdaCount && abTs == baseTs then
              skippedPrintedCda := skippedPrintedCda + 1
            else
              raw := raw.push {
                idx := raw.size
                ts := abTs
                scope := .objects #[o.id]
                setP := p?.map (fun v => g.evalStaticValL5 o youP v (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra))
                setT := t?.map (fun v => g.evalStaticValL5 o youP v (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra))
              }
          | _ => pure ()
        -- 3. Active `.ptSet` and `.ptCda .cardsInHandPower` effects.
        if has7bEff then
          for pos in [0:g.activeEffects.size] do
            let (eid, s) := g.activeEffects[pos]!
            match s with
            | .layered sc (.ptSet pw tg) d =>
              if g.durationActive d && g.effectPhasingAllows o eid sc d then
                raw := raw.push {
                  idx := raw.size
                  ts := g.effectTimestamp eid pos
                  scope := sc
                  setP := some pw
                  setT := some tg
                }
            | .layered sc (.ptCda .cardsInHandPower) d =>
              if g.durationActive d && g.effectPhasingAllows o eid sc d then
                raw := raw.push {
                  idx := raw.size
                  ts := g.effectTimestamp eid pos
                  scope := sc
                  setP := some handP
                  setT := none
                }
            | _ => pure ()
        if raw.isEmpty then return (none, none)
        let sorted :=
          if raw.size < 2 then raw
          else raw.qsort fun a b =>
            if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
            else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
            else a.idx < b.idx
        let mut rem := sorted
        let mut cur : Option Int × Option Int := (none, none)
        for _ in [0:sorted.size] do
          let applicable := rem.filter (fun e => g.scopeMatches e.scope o)
          if applicable.isEmpty then break
          let chosen := applicable[0]!
          cur := applyStep cur chosen
          rem := rem.filter (fun e => e.idx != chosen.idx)
        return cur

/-- Cycle-guarded characteristic P/T after Layers 7a and 7b (CR 613.4a–b). -/
private partial def characteristicBasePTAux (g : Game) (visited : Array (ObjectId × (Int × Int)))
    (o : GameObject) : Int × Int :=
  if o.isLkiSnapshot then (o.printed.powerValue.getD 0, o.printed.toughnessValue.getD 0)
  else
    let (cdaP, cdaT) := g.cdaBasePTAux visited o
    let (setP, setT) := g.evalLayer7bAux visited o (cdaP, cdaT)
    (setP.getD cdaP, setT.getD cdaT)

/-- Cycle-guarded Layer 7c continuous P/T bonus on `o` (CR 114.4 / 604.2 / 613.4c / 613.7 / 613.8).
Applies non-P/T-dependent static pumps before P/T-dependent static pumps so that any
static ability reading `o`'s power/toughness sees `baseBeforeStatics` (Layers 7a–7b,
P/T counters, active pumps) plus all independent static pumps before
resolving P/T-dependent statics in CR 613.8 dependency and CR 613.7 timestamp order. -/
private partial def staticContinuousPTBonusAux (g : Game)
    (visited : Array (ObjectId × (Int × Int))) (o : GameObject)
    (baseBeforeStatics : Int × Int) : Int × Int :=
  if !o.isOnBattlefield || visited.any (·.1 == o.id) then (0, 0)
  else
    let kwOf := some g.currentKeywords
    let kwExtra := some g.liveObjectHasExtraKeyword
    let untilTurn := g.activeEffects.foldl (fun acc (eid, s) =>
      match s with
      | .layered scope (.ptModify pw tg) (.untilNextTurnOf p) =>
        if g.scopeMatches scope o (eid? := some eid) (dur? := some (.untilNextTurnOf p)) then
          addStats acc (pw, tg)
        else acc
      | _ => acc) (0, 0)
    Id.run do
      let mut indepBonus := untilTurn
      let mut depEntries : Array Layer7cDepEntry := #[]
      for src in g.objects do
        let isEmblem := src.zone == .command && (g.baseCard src).types.isEmpty
        if src.isOnBattlefield || isEmblem then
          if src.isOnBattlefield && src.attachedTo == some o.id && src.status.hone > 0 then
            indepBonus := addStats indepBonus ((src.status.hone : Int), 0)
          let sas :=
            if isEmblem then src.printed.staticAbilities
            else g.staticAbilities src
          if !sas.isEmpty then
            let srcCtrl := g.controllerOf src |>.getD src.owner
            for ab in sas do
              match ab with
              | .continuous cond? sc mod =>
                let ptExprs : Array (ValueExpr × ValueExpr) := mod.flatten.filterMap fun
                  | .modifyPT pExpr tExpr => some (pExpr, tExpr)
                  | _ => none
                if !ptExprs.isEmpty then
                  let readsPT :=
                    predReadsPT sc.pred || cond?.any condReadsPT ||
                      ptExprs.any (fun (p, t) => valExprReadsPT p || valExprReadsPT t)
                  if !readsPT then
                    if g.matchesStaticScopeL5 src srcCtrl o sc none kwOf (hasKwExtra? := kwExtra) &&
                        cond?.all (fun c => g.evalStaticCondL5 src srcCtrl c (fun _ => true) none kwOf (hasKwExtra? := kwExtra)) then
                      for (pExpr, tExpr) in ptExprs do
                        indepBonus := addStats indepBonus
                          (g.evalStaticValL5 src srcCtrl pExpr (fun _ => true) none kwOf (hasKwExtra? := kwExtra),
                           g.evalStaticValL5 src srcCtrl tExpr (fun _ => true) none kwOf (hasKwExtra? := kwExtra))
                  else
                    let ts : Nat × Nat :=
                      if isEmblem then g.objectEntryTimestamp src
                      else
                        let baseTs :=
                          if g.hasAnyStaticLayer6Effect then
                            ((g.evalLayer6 src).staticsWithTs.find? (·.1 == ab)).map Prod.snd
                              |>.getD (g.baseCardWithTs src).2
                          else (g.baseCardWithTs src).2
                        if src.isOnBattlefield && src.attachedTo == some o.id then
                          maxTs (g.attachmentTimestamp src o.id) baseTs
                        else baseTs
                    depEntries := depEntries.push {
                      idx := depEntries.size
                      ts := ts
                      src := src
                      srcCtrl := srcCtrl
                      cond? := cond?
                      sc := sc
                      ptExprs := ptExprs
                    }
              | _ => pure ()
      if depEntries.isEmpty then
        return indepBonus
      let evalEntry (pt : Int × Int) (e : Layer7cDepEntry) : Int × Int :=
        let vis := visited.push (o.id, pt)
        let ptOf := some (fun x => g.snapshotPTAux vis x)
        if g.matchesStaticScopeL5 e.src e.srcCtrl o e.sc ptOf kwOf (hasKwExtra? := kwExtra) &&
            e.cond?.all (fun c => g.evalStaticCondL5 e.src e.srcCtrl c (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra)) then
          e.ptExprs.foldl (fun a (pExpr, tExpr) =>
            addStats a
              (g.evalStaticValL5 e.src e.srcCtrl pExpr (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra),
               g.evalStaticValL5 e.src e.srcCtrl tExpr (fun _ => true) ptOf kwOf (hasKwExtra? := kwExtra))) (0, 0)
        else (0, 0)
      let mut curBonus := indepBonus
      let mut curPT := addStats baseBeforeStatics indepBonus
      if depEntries.size == 1 then
        let delta := evalEntry curPT depEntries[0]!
        return addStats curBonus delta
      let sorted := depEntries.qsort fun a b =>
        if a.ts.1 != b.ts.1 then a.ts.1 < b.ts.1
        else if a.ts.2 != b.ts.2 then a.ts.2 < b.ts.2
        else a.idx < b.idx
      let mut rem := sorted
      for _ in [0:sorted.size] do
        if rem.isEmpty then break
        let dependsOn (a b : Layer7cDepEntry) : Bool :=
          a.idx != b.idx &&
            evalEntry curPT a != evalEntry (addStats curPT (evalEntry curPT b)) a
        let chosen :=
          (rem.find? (fun a => !rem.any (fun b => dependsOn a b))).getD rem[0]!
        let delta := evalEntry curPT chosen
        curPT := addStats curPT delta
        curBonus := addStats curBonus delta
        rem := rem.filter (fun e => e.idx != chosen.idx)
      return curBonus

/-- Cycle-guarded full Layer 7a–7d P/T snapshot of `o` (CR 613.4).
When `o.id` is already in `visited`, returns `o`'s accumulated P/T from layers and
effects that do not depend on the static ability currently being evaluated. -/
private partial def snapshotPTAux (g : Game) (visited : Array (ObjectId × (Int × Int)))
    (o : GameObject) : Int × Int :=
  if o.isLkiSnapshot then (o.printed.powerValue.getD 0, o.printed.toughnessValue.getD 0)
  else
    match visited.find? (·.1 == o.id) with
    | some (_, curPT) => curPT
    | none =>
      let n : Int := (o.status.plusOnePlusOne : Int) - (o.status.minusOneMinusOne : Int)
      let s0 := addStats (g.characteristicBasePTAux visited o) (g.pumpOf o)
      let s1 := addStats (addStats s0 (n, n)) (g.artifactCountPump o)
      let (pw, tg) := addStats s1 (g.staticContinuousPTBonusAux visited o s1)
      let switchCnt : Nat :=
        g.activeEffects.foldl (fun cnt (eid, s) =>
          match s with
          | .layered scope .ptSwitch d =>
            if g.scopeMatches scope o (eid? := some eid) (dur? := some d) && g.durationActive d then
              cnt + 1
            else cnt
          | _ => cnt) 0
      if switchCnt % 2 == 1 then (tg, pw) else (pw, tg)

end

/-- Layer 7a power and toughness of `o` from Layer 1 base characteristics and
printed CR 604.3 / 613.4a characteristic-defining abilities. Layer-6-granted
P/T CDAs apply in Layer 7b at their grant timestamp (`evalLayer7b`). -/
def cdaBasePT (g : Game) (o : GameObject) : Int × Int :=
  if o.isLkiSnapshot then (o.printed.powerValue.getD 0, o.printed.toughnessValue.getD 0)
  else g.cdaBasePTAux #[] o

/-- Layer 7b base P/T-setting evaluation on `o` across `.ptSet` effects,
attached Auras/Equipment setting base P/T (`.setBasePT`, e.g. Puppet Crafting),
and Layer-6-granted P/T CDAs (`.characteristicDefining (.setPT ..)` and
`.ptCda .cardsInHandPower`) in CR 613.7 timestamp and CR 613.8 dependency
order (CR 613.4b). -/
def evalLayer7b (g : Game) (o : GameObject) : Option Int × Option Int :=
  if o.isLkiSnapshot then (none, none)
  else g.evalLayer7bAux #[] o (g.cdaBasePTAux #[] o)

def setBasePT (g : Game) (o : GameObject) : Option (Int × Int) :=
  if o.isLkiSnapshot then none
  else
    let (bp, bt) := g.evalLayer7b o
    if bp.isNone && bt.isNone then none
    else
      let (cdaP, cdaT) := g.cdaBasePT o
      some (bp.getD cdaP, bt.getD cdaT)

def setBasePower (g : Game) (o : GameObject) : Option Int :=
  if o.isLkiSnapshot then none
  else (g.evalLayer7b o).1

/-- Characteristic power and toughness after Layer 7a CDAs and Layer 7b
base-setting effects, before Layer 7c pumps/counters/bonuses and Layer 7d
switches (CR 613.4a–b). -/
def characteristicBasePT (g : Game) (o : GameObject) : Int × Int :=
  g.characteristicBasePTAux #[] o

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def characteristicBasePower (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).1

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def characteristicBaseToughness (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).2

/-- Unified Layer 7c continuous P/T bonus on `o` from all stratified
`StaticAbility.continuous _ _ (.modifyPT ...)` abilities across battlefield
permanents (self, attached Auras/Equipment, allied lords, opponent debuffers)
and command-zone emblems (CR 114.4 / 604.2 / 613.4c), plus Equipment hone
counters and `.untilNextTurnOf` P/T-modifying effects. -/
def staticContinuousPTBonus (g : Game) (o : GameObject) : Int × Int :=
  if o.isLkiSnapshot then (0, 0)
  else
    let n : Int := (o.status.plusOnePlusOne : Int) - (o.status.minusOneMinusOne : Int)
    let s0 := addStats (g.characteristicBasePTAux #[] o) (g.pumpOf o)
    let s1 := addStats (addStats s0 (n, n)) (g.artifactCountPump o)
    g.staticContinuousPTBonusAux #[] o s1

-- Layer 7d: P/T-switching effects (CR 613.4d / 613.7)

def snapshotPT (g : Game) (o : GameObject) : Int × Int :=
  g.snapshotPTAux #[] o

/-- Power of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotPower (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).1

/-- Toughness of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotToughness (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).2

/-! ### Full Post-Layer-7 Static Expression Evaluators (CR 604 / 613 / 614) -/

private def matchStaticPlayerFilterFull (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (pf : PlayerFilter) (p : PlayerId) (ok : GameObject → Bool := fun _ => true) : Bool :=
  g.matchStaticPlayerFilterL5 src srcCtrl pf p ok (some g.snapshotPT) (some g.currentKeywords)
    none (some g.liveObjectHasExtraKeyword)

private def evalStaticPredFull (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (pred : ObjectPred) (ok : GameObject → Bool := fun _ => true) : Bool :=
  g.evalStaticPredL5 src srcCtrl target pred ok (some g.snapshotPT) (some g.currentKeywords)
    none (some g.liveObjectHasExtraKeyword)

private def evalStaticObjsFull (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (expr : ObjectExpr) (ok : GameObject → Bool := fun _ => true) : Array GameObject :=
  g.evalStaticObjsL5 src srcCtrl expr ok (some g.snapshotPT) (some g.currentKeywords)
    none (some g.liveObjectHasExtraKeyword)

private def evalStaticValFull (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (v : ValueExpr) (ok : GameObject → Bool := fun _ => true) : Int :=
  g.evalStaticValL5 src srcCtrl v ok (some g.snapshotPT) (some g.currentKeywords)
    none (some g.liveObjectHasExtraKeyword)

private def evalStaticCondFull (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (c : Condition) (ok : GameObject → Bool := fun _ => true) : Bool :=
  g.evalStaticCondL5 src srcCtrl c ok (some g.snapshotPT) (some g.currentKeywords)
    none (some g.liveObjectHasExtraKeyword)

private def matchesStaticScopeFull (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (sc : ObjectFilter) : Bool :=
  g.matchesStaticScopeL5 src srcCtrl target sc (some g.snapshotPT) (some g.currentKeywords)
    (some g.liveObjectHasExtraKeyword)

/-- Evaluate a trigger `PlayerFilter` against player `p` using full Layer 1–7 state. -/
def matchTriggerPlayerFilter (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (pf : PlayerFilter) (p : PlayerId) (triggerSubject? : Option GameObject := none) : Bool :=
  g.matchStaticPlayerFilterL5 src srcCtrl pf p (fun _ => true)
    (some g.snapshotPT) (some g.currentKeywords) triggerSubject? (some g.liveObjectHasExtraKeyword)

/-- Evaluate a trigger `ObjectPred` against `target` using full Layer 1–7 state. -/
def evalTriggerPred (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (pred : ObjectPred)
    (triggerSubject? : Option GameObject := none) : Bool :=
  g.evalStaticPredL5 src srcCtrl target pred (fun _ => true)
    (some g.snapshotPT) (some g.currentKeywords) triggerSubject? (some g.liveObjectHasExtraKeyword)

/-- Evaluate a trigger `Condition` (CR 603.2 / 603.4), resolving `.this` to `source`
(live on battlefield or LKI when departed) and `.triggerSubject` to `cause`. -/
def evalTriggerCond (g : Game) (controller : PlayerId) (source : Option GameObject)
    (cause : Option GameObject) (cond : Condition) : Bool :=
  let srcObj : GameObject :=
    match source with
    | some o =>
      if o.isLkiSnapshot then o
      else
        match g.findLiveSourceObject? o.id with
        | some cur => cur
        | none =>
          ((g.lastKnownBefore? o.id).map (fun eo =>
            lkiEventObjectAsGameObject eo
              (prepared := if eo.copiable.isSome then none else g.wasPreparedAtDeparture? o.id))).getD o
    | none =>
      { printed := { name := "", types := #[] }, id := noSourceSentinelId, owner := controller,
        controller := some controller, zone := .command }
  g.evalStaticCondL5 srcObj controller cond (fun _ => true)
    (some g.snapshotPT) (some g.currentKeywords) cause (some g.liveObjectHasExtraKeyword)

/-- Collect `sel` from graveyard cards matched by `.copyActivatedFrom` static abilities. -/
def copiedFromGy {α : Type} (g : Game) (o : GameObject) (sel : CardDef → Array α) :
    Array α :=
  if !o.isOnBattlefield then #[]
  else
    match g.controllerOf o with
    | none => #[]
    | some p =>
      (g.staticAbilities o).foldl (fun acc sa =>
        match sa with
        | .continuous cond? sc mod =>
          if g.matchesStaticScopeFull o p o sc && cond?.all (fun c => g.evalStaticCondFull o p c) then
            mod.flatten.foldl (fun acc m =>
              match m with
              | .copyActivatedFrom filter =>
                (g.evalStaticObjsFull o p filter.toExpr).foldl
                  (fun a card => a ++ sel (g.baseCard card)) acc
              | _ => acc) acc
          else acc
        | _ => acc) #[]

/-- Generic mana each creature must pay to attack `defender` (Dáin, CR 508.1d / 508.1h). -/
def attackTaxPerCreature (g : Game) (defender : PlayerId) : Nat :=
  (g.permanentsOf defender).foldl (fun acc src =>
    (g.staticAbilities src).foldl (fun acc ab =>
      match ab with
      | .ruleModifying cond? rule =>
        if cond?.all (fun c => g.evalStaticCondFull src defender c) then
          rule.flatten.foldl (fun a r =>
            match r with
            | .combat (.attackTax _ df cost) =>
              if g.matchStaticPlayerFilterFull src defender df defender then
                a + cost.manaCost.manaValue
              else a
            | _ => a) acc
        else acc
      | _ => acc) acc) 0

/-- CR 616.1 replacement loop for putting `n` counters of `kind` on `target`
(CR 122.6 / 614.1a / 614.12), returning `(count, applied, cause, choice?, remainingOrder)`. -/
def replaceCountersPutChoice (g : Game) (target : GameObject) (kind : CounterKind) (n : Nat)
    (putter : Option PlayerId := none) (entersWith : Bool := false)
    (entering : Option GameObject := none)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none)
    (order : Array ReplacementId := g.replacementOrder)
    (preBattlefield : Option (Array GameObject) := none) :
    Nat × Array ReplacementId × Option EventCause × Option (PlayerId × Array ReplacementId) × Array ReplacementId :=
  if n == 0 then (0, applied, cause, none, order)
  else
    let tCtrl := g.controllerOf target
    let who :=
      if entersWith then tCtrl
      else putter.orElse (fun _ => g.counterPutter tCtrl)
    let affected := tCtrl.orElse (fun _ => who) |>.getD target.owner
    let preBfOk (pObj : GameObject) : Bool :=
      pObj.id != target.id && (entering.all (fun ent => pObj.id != ent.id)) &&
        match preBattlefield with
        | some pb => pb.any (fun pre => pre.id == pObj.id && pre.isOnBattlefield)
        | none =>
          g.currentBatch.isNone ||
            g.openBatchObjects.any (fun pre => pre.id == pObj.id && pre.isOnBattlefield)
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
          -- Battlefield permanents controlled by `target`'s controller
          match tCtrl with
          | some c =>
            let perms :=
              if entersWith then (g.permanentsOf c).filter preBfOk
              else g.permanentsOf c
            let allPerms :=
              match entering with
              | some ent =>
                if !ent.status.faceDown && g.controllerOf ent == some c &&
                    !perms.any (·.id == ent.id) then
                  perms.push ent
                else perms
              | none => perms
            let notSelfEntering (o : GameObject) : Bool :=
              match entering with
              | some ent => o.id != ent.id
              | none => true
            for o in allPerms do
              if notSelfEntering o && !o.status.faceDown then
                for ab in g.staticAbilities o do
                  match ab with
                  | .replacement cond? spec =>
                    if cond?.all (fun cd => g.evalStaticCondFull o c cd) then
                      for sp in spec.flatten do
                        match sp with
                        | .modifyCountersPut sc k? byPl? addCnt =>
                          let kindOk := match k? with | none => true | some k => k == kind
                          let putterOk :=
                            match byPl? with
                            | none => true
                            | some pf => who.any (fun p => g.matchStaticPlayerFilterFull o c pf p)
                          let scopeOk := g.matchesStaticScopeFull o c target sc
                          if kindOk && putterOk && scopeOk && addCnt > 0 then
                            let rid : ReplacementId :=
                              if k?.isNone then
                                { kind := .extraCounterOnPermanents, object := some o.id, counterKind := some kind }
                              else
                                { kind := .extraPlusOneCounter, object := some o.id }
                            specs := specs.push (
                              { id := rid
                                source := some o.id
                                controller := some c
                                affectedPlayer := affected
                                kind := .modifyCountersPut (some target.id) (some kind) addCnt 1 }, addCnt, 1)
                        | _ => pure ()
                  | _ => pure ()
          | none => pure ()
          -- Active `ContinuousEffect.replacement` effects matching `modifyCountersPut`
          for (_, eff) in g.activeEffects do
            match eff with
            | .replacement spec d =>
              if g.durationActive d then
                match spec.kind with
                | .modifyCountersPut tid k? add mult =>
                  if (tid.isNone || tid == some target.id) && (k?.isNone || k? == some kind) then
                    let spec' :=
                      if k?.isNone then
                        { spec with id := { spec.id with counterKind := some kind }, affectedPlayer := affected }
                      else { spec with affectedPlayer := affected }
                    specs := specs.push (spec', add, mult)
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
(excluding `entering` itself per CR 614.12),
as well as active `ContinuousEffect.replacement` specs with `.modifyCountersPut`.
Returns the modified count, the updated `applied` list (CR 614.5), and the
updated `EventCause` (CR 614.6). -/
def replaceCountersPut (g : Game) (target : GameObject) (kind : CounterKind) (n : Nat)
    (putter : Option PlayerId := none) (entersWith : Bool := false)
    (entering : Option GameObject := none)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none)
    (order : Array ReplacementId := g.replacementOrder)
    (preBattlefield : Option (Array GameObject) := none) :
    Nat × Array ReplacementId × Option EventCause :=
  let (n', app', c', _, _) :=
    g.replaceCountersPutChoice target kind n (putter := putter) (entersWith := entersWith)
      (entering := entering) (applied := applied) (cause := cause)
      (order := order) (preBattlefield := preBattlefield)
  (n', app', c')

/-- Counters of one kind actually put on `o`. An enters-with replacement is
put by the permanent's controller (ruling 517). Otherwise the explicit
`putter`, the resolving spell or ability, or `o`'s controller. -/
def countersYouPut (g : Game) (o : GameObject) (n : Nat)
    (putter : Option PlayerId := none) (entersWith := false)
    (kind : CounterKind := .charge) : Nat :=
  (g.replaceCountersPut o kind n (putter := putter) (entersWith := entersWith)).1

/-- True when an Aura attached to `o` prevents it from attacking or blocking via an
attached `.applyRule` combat restriction (e.g. Fog on the Barrow-Downs). -/
def enchantedCantAttackOrBlock (g : Game) (o : GameObject) : Bool :=
  g.objects.any (fun a =>
    a.isOnBattlefield && a.attachedTo == some o.id &&
      let aCtrl := g.controllerOf a |>.getD a.owner
      (g.staticAbilities a).any fun
        | .continuous cond? sc mod =>
          StaticAbility.isAttachedHostScope sc &&
            g.matchesStaticScopeFull a aCtrl o sc &&
            cond?.all (fun c => g.evalStaticCondFull a aCtrl c) &&
            mod.flatten.any fun
              | .applyRule r =>
                r.flatten.any fun
                  | .combat (.cantAttack .self) | .combat (.cantBlock .self none) => true
                  | _ => false
              | _ => false
        | _ => false)

/-- Whether `o` may attack as though it didn't have defender (CR 702.3b;
Surveillance Phantasm; Ghalta the Immovable). -/
def mayAttackDespiteDefender (g : Game) (o : GameObject) : Bool :=
  let oCtrl := g.controllerOf o |>.getD o.owner
  let selfOk := (g.staticAbilities o).any fun ab =>
    ab.anyRule fun cond? r =>
      cond?.all (fun c => g.evalStaticCondFull o oCtrl c) &&
        match r with
        | .combat (.attackDespiteDefender .self) => true
        | _ => false
  selfOk ||
    g.objects.any fun src =>
      src.isOnBattlefield &&
        let srcCtrl := g.controllerOf src |>.getD src.owner
        (g.staticAbilities src).any fun ab =>
          ab.anyRule fun cond? r =>
            cond?.all (fun c => g.evalStaticCondFull src srcCtrl c) &&
              match r with
              | .combat (.attackDespiteDefender (.matching sc)) =>
                g.matchesStaticScopeFull src srcCtrl o sc
              | _ => false

/-- Whether `p` currently controls a permanent with any of these subtypes. -/
def controlsAnySubtype (g : Game) (p : PlayerId) (subtypes : Array CardSubtype)
    (ok : GameObject → Bool := fun _ => true) : Bool :=
  (g.permanentsOf p).any (fun o => ok o && subtypes.any (g.hasSubtype o))

/-- Whether `p` can pay `n` life (CR 119.4 / 119.8 / 800.4a). Paying 0 life is always legal for a player in the game. -/
def canPayLife (g : Game) (p : PlayerId) (n : Nat) : Bool :=
  g.stillInGame p &&
    (n == 0 || ((g.player p).life ≥ (n : Int) && !g.lifeLocked p && !g.lifeCantChange p))

/-- Mana value of `o` (CR 202.3 / 613.1a / 708.2a). `{X}` is the chosen value
while the object is on the stack (or when `includeLkiX` requests LKI spell MV)
and 0 otherwise (rulings 178 / 185 / 186). -/
def objectManaValue (g : Game) (o : GameObject) (includeLkiX : Bool := false) : Nat :=
  if o.status.faceDown && (o.zone == .battlefield || o.zone == .stack) then 0
  else
    let mc := (g.copiableValues o).manaCost
    if o.zone != .stack && !includeLkiX then mc.manaValue
    else if o.isLkiSnapshot then
      match o.chosenX with
      | some x => (mc.substituteX x).manaValue
      | none => mc.manaValue
    else
      let x := (o.chosenX.orElse (fun _ => g.chosenXOf? o.id)).getD 0
      (mc.substituteX x).manaValue

private def latestExileToStackAfterController? (g : Game) (id : ObjectId) : Option PlayerId := Id.run do
  let mut i := g.events.size
  while i > 0 do
    i := i - 1
    match g.events[i]!.change with
    | .rules (.zone (.moved before after fromZ toZ ..)) =>
      if fromZ == .exile && toZ == .stack && (before.id == some id || after.id == some id) then
        return after.controller
      if (fromZ == .exile && toZ != .stack && (before.id == some id || after.id == some id)) ||
          (toZ != .stack && after.id == some id) then
        return none
    | .rules (.zone (.created obj _)) =>
      if obj.id == some id && obj.zone != .stack then
        return none
    | .engine (.materializeObject obj _) =>
      if obj.id == id && obj.zone != .stack then
        return none
    | _ => pure ()
  return none

private def exileDepartureIdx? (g : Game) (id : ObjectId) : Option Nat := Id.run do
  let targetId? : Option ObjectId :=
    match g.findObject? id with
    | some o =>
      if o.zone == .stack then
        Id.run do
          let mut j := g.events.size
          while j > 0 do
            j := j - 1
            match g.events[j]!.change with
            | .rules (.zone (.moved before after .exile .stack ..)) =>
              if after.id == some id then
                return before.id
            | _ => pure ()
          return none
      else some id
    | none =>
      Id.run do
        let mut j := g.events.size
        while j > 0 do
          j := j - 1
          match g.events[j]!.change with
          | .rules (.zone (.moved before after .exile .stack ..)) =>
            if after.id == some id then
              return before.id
          | _ => pure ()
        return some id
  match targetId? with
  | none => return none
  | some targetId =>
    let mut i := g.events.size
    while i > 0 do
      i := i - 1
      match g.events[i]!.change with
      | .rules (.zone (.moved before _ .exile ..)) =>
        if before.id == some targetId then
          return some i
      | .rules (.zone (.ceasedToExist eo)) =>
        if eo.id == some targetId then
          return some i
      | _ => pure ()
    return none

/-- Null Summoner: `p` may cast a card it exiled via a `.play (.mayPlayFrom .you .exile .. (linkedExile := true))` static. -/
def mayCastExiledBySource (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
    match o.exiledBy.bind g.findObject? with
    | some src =>
      src.isOnBattlefield && g.controlledBy src p &&
        (g.staticAbilities src).any fun ab =>
          ab.anyRule fun cond? r =>
            cond?.all (fun c => g.evalStaticCondFull src p c) &&
              match r with
              | .play (.mayPlayFrom who .exile pred _ true _ _) =>
                g.matchStaticPlayerFilterFull src p who p &&
                  g.evalStaticPredFull src p o pred
              | _ => false
    | none => false

/-- Active or pre-departure `.playFromExile` permissions granting `p` permission
to play `o` from exile (CR 601.1a / 611.2a). -/
def playPermissionsFor (g : Game) (p : PlayerId) (o : GameObject) : Array PlayPermission :=
  if !g.stillInGame p then #[]
  else
    let entries := g.playPermissionEntriesOf o.id
    if entries.isEmpty then #[]
    else
      let liveInExile := (g.findObject? o.id).any (·.zone == .exile)
      let stackCtrl? : Option PlayerId :=
        match g.findObject? o.id with
        | some live => if live.zone == .stack then live.controller.orElse (fun _ => o.controller) else none
        | none => g.latestExileToStackAfterController? o.id
      let needsHistGAt : Bool :=
        !liveInExile &&
          entries.any fun (_, _, perm, _) =>
            perm.requireSubtype.isSome || (perm.prepareSource.isSome && stackCtrl?.isNone)
      let gAt :=
        if !needsHistGAt then g
        else
          match g.exileDepartureIdx? o.id with
          | some idx => g.mkHistoricalGameAt idx
          | none => g
      let matching :=
        entries.filterMap fun (_, grantee, perm, _) =>
          let ok : Bool :=
            match perm.prepareSource with
            | some src =>
              if liveInExile then
                (g.findObject? src).any (fun prm =>
                  prm.isOnBattlefield && prm.status.prepared && g.controlledBy prm p)
              else
                match stackCtrl? with
                | some c => c == p
                | none =>
                  (gAt.findObject? src).any (fun prm =>
                    prm.isOnBattlefield && prm.status.prepared && gAt.controlledBy prm p)
            | none => grantee == p
          if ok then some { perm with player := p } else none
      matching.filter fun perm =>
        match perm.requireSubtype with
        | none => true
        | some t => gAt.controlsAnySubtype p #[t]

/-- Un-substituted printed mana cost of `card` when cast as `face` (`none` when
cast face-down via Morph, whose mana value is `0` per CR 702.37c / 708.2a). -/
def actualPrintedManaCost? (g : Game) (card : GameObject) (face : CardDef) : Option ManaCost :=
  if (card.zone != .exile && card.status.faceDown) || face.name == "" then none
  else
    let bc :=
      if card.zone == .exile && card.status.faceDown then g.unmaskedCopiableValues card
      else g.baseCard card
    match bc.adventure.filter (·.name == face.name) with
    | some adv => some adv.manaCost
    | none =>
      match bc.prepareFace.filter (·.name == face.name) with
      | some pf => some pf.manaCost
      | none =>
        match bc.otherFace with
        | some of =>
          if of.name == face.name then some of.manaCost
          else
            match of.adventure.filter (·.name == face.name) with
            | some adv => some adv.manaCost
            | none =>
              match of.prepareFace.filter (·.name == face.name) with
              | some pf => some pf.manaCost
              | none => some bc.manaCost
        | none => some bc.manaCost

/-- Layer-3 text-changed, CR 604.3 / 613.3 CDA-evaluated, and Layer-5 color-evaluated
`(types, supertypes, colors)` of `card` when cast as `face` (CR 601.2a,f / 613.1c–e / 708.2a). -/
def faceCdaCharacteristics (g : Game) (card : GameObject) (face : CardDef) :
    Array CardType × Array Supertype × ColorSet :=
  let isFaceDown := face.name == "" || (card.zone != .exile && card.status.faceDown)
  let spellObj : GameObject :=
    { card with
      printed := face
      zone := .stack
      status := { card.status with faceDown := isFaceDown } }
  let cols := g.colors spellObj
  if isFaceDown then
    (#[.creature], #[], cols)
  else
    let tcs := g.evalLayer3 spellObj
    let rawSubs :=
      (CardSubtype.ofSubtypes face.subtypes).map fun s =>
        if tcs.isEmpty then s else HasTextChange.applyTextChanges tcs s
    let sas :=
      if tcs.isEmpty then face.staticAbilities
      else face.staticAbilities.map (TextChange.applyStaticAbility tcs)
    let (cdaTypes, _, cdaSups) :=
      sas.foldl (fun (ts, subs, sups) ab =>
        match ab with
        | .characteristicDefining (.setTypes tm) => tm.apply ts subs sups
        | _ => (ts, subs, sups)) (face.types, rawSubs, face.supertypes)
    (cdaTypes, cdaSups, cols)

private def coreSorceryTimingOk (g : Game) (p : PlayerId) (o : GameObject) (face : CardDef) : Bool :=
  let actualFace : CardDef :=
    match g.actualPrintedManaCost? o face with
    | some mc => { face with manaCost := mc }
    | none => { face with manaCost := { symbols := #[] } }
  let spellObj : GameObject :=
    { o with
      printed := actualFace
      zone := .stack
      controller := some p
      status := { o.status with faceDown := (face.name == "") } }
  let faceStatics := g.staticAbilities spellObj
  let countPrevMatching (srcObj : GameObject) (srcCtrl : PlayerId) (spellPred : ObjectPred) : Nat :=
    match spellPred with
    | .anyObject => g.loggedSpellsCast p
    | .hasType .creature => g.loggedCreatureSpells p
    | _ =>
      g.events.foldl (fun acc e =>
        if e.turn != g.turnNumber then acc
        else
          match e.change with
          | .rules (.cast (.spellCast snap q _)) =>
            if q == p &&
                g.evalStaticPredFull srcObj srcCtrl (lkiEventObjectAsGameObject snap) spellPred then
              acc + 1
            else acc
          | _ => acc) 0
  let selfFlash :=
    faceStatics.any fun ab =>
      ab.anyRule fun cond? r =>
        cond?.all (fun c => g.evalStaticCondFull spellObj p c) &&
          match r with
          | .play (.castAsThoughFlash who spellPred true nth?) =>
            g.matchStaticPlayerFilterFull spellObj p who p &&
              nth?.all (fun n => countPrevMatching spellObj p spellPred + 1 == n)
          | _ => false
  let peerFlash :=
    g.battlefield.any fun perm =>
      let permCtrl := (g.controllerOf perm).getD perm.owner
      (g.staticAbilities perm).any fun ab =>
        ab.anyRule fun cond? r =>
          cond?.all (fun c => g.evalStaticCondFull perm permCtrl c) &&
            match r with
            | .play (.castAsThoughFlash who spellPred false nth?) =>
              let whoOk := g.matchStaticPlayerFilterFull perm permCtrl who p
              let predOk :=
                match spellPred with
                | .anyObject => true
                | pred => g.evalStaticPredFull perm permCtrl spellObj pred
              let nthOk :=
                match nth? with
                | none => true
                | some n => countPrevMatching perm permCtrl spellPred + 1 == n
              whoOk && predOk && nthOk
            | _ => false
  let (faceTypes, _, _) := g.faceCdaCharacteristics spellObj face
  let faceHasSorcerySpeed :=
    !faceTypes.contains .instant && !faceTypes.contains .land &&
      !KeywordAbility.hasFlash (g.currentKeywords spellObj)
  if faceHasSorcerySpeed && !selfFlash && !peerFlash then
    !g.over && !(g.stack.any (·.objectId != o.id)) &&
      g.step.isMainPhase && g.activePlayer == p && g.priority == p
  else
    true

private def isAdventureFace (g : Game) (o : GameObject) (face? : Option CardDef) : Bool :=
  let bc :=
    if o.zone == .exile && o.status.faceDown then g.unmaskedCopiableValues o
    else g.baseCard o
  o.isAdventureSpell ||
    face?.any (fun fc =>
      bc.adventure.any (fun adv =>
        adv.toCardDef == fc || (adv.name == fc.name && fc.name != bc.name)))

private def faceManaValue (g : Game) (o : GameObject) (face? : Option CardDef) : Nat :=
  let isExiledFaceDown := o.zone == .exile && o.status.faceDown
  let bc := if isExiledFaceDown then g.unmaskedCopiableValues o else g.baseCard o
  match face? with
  | some fc =>
    if !isExiledFaceDown && !isAdventureFace g o face? && fc == bc then
      g.objectManaValue o
    else
      match g.actualPrintedManaCost? o fc with
      | none => 0
      | some mc =>
        if o.zone != .stack then mc.manaValue
        else if o.isLkiSnapshot then
          match o.chosenX with
          | some x => (mc.substituteX x).manaValue
          | none => mc.manaValue
        else
          let x := (o.chosenX.orElse (fun _ => g.chosenXOf? o.id)).getD 0
          (mc.substituteX x).manaValue
  | none =>
    if isExiledFaceDown then bc.manaCost.manaValue
    else g.objectManaValue o

/-- Best active or pre-departure `.playFromExile` permission granting `p` permission
to play `o` from exile (CR 601.1a / 611.2a). -/
def playPermissionFor? (g : Game) (p : PlayerId) (o : GameObject)
    (face? : Option CardDef := none) : Option PlayPermission :=
  let perms0 :=
    let base := g.playPermissionsFor p o
    if g.stillInGame p && o.zone == .exile && g.mayCastExiledBySource p o then
      base.push { player := p, anyMana := true }
    else base
  let isAdv := isAdventureFace g o face?
  let perms :=
    if isAdv then perms0.filter (!·.fromAdventure) else perms0
  if perms.isEmpty then none
  else
    let isExiledFaceDown := o.zone == .exile && o.status.faceDown
    let bc := if isExiledFaceDown then g.unmaskedCopiableValues o else g.baseCard o
    let oKws :=
      if isExiledFaceDown then
        g.currentKeywords { o with printed := bc, status := { o.status with faceDown := false } }
      else g.currentKeywords o
    let defaultFace := { bc with keywords := oKws }
    let face :=
      match face? with
      | some fc =>
        if !isAdv && fc == bc then defaultFace
        else if !isAdv && !fc.name.isEmpty && fc.name == bc.name then
          { fc with keywords := KeywordAbility.merge fc.keywords oKws }
        else fc
      | none => defaultFace
    let timingOk := coreSorceryTimingOk g p o face
    let timingFiltered :=
      if timingOk then perms
      else
        let ign := perms.filter (·.ignoreTiming)
        if ign.isEmpty then perms else ign
    let mv := faceManaValue g o face?
    let score (perm : PlayPermission) : Nat :=
      let lifeOk := !perm.payLifeEqualManaValue || g.canPayLife p mv
      (if lifeOk then 32 else 0) +
        (if perm.withoutManaCost then 16 else 0) +
        (if perm.payLifeEqualManaValue && lifeOk then 8 else 0) +
        (if perm.anyMana then 4 else 0) +
        (if perm.ignoreTiming then 2 else 0) +
        (if !perm.fromAdventure then 1 else 0)
    timingFiltered.foldl (fun best? perm =>
      match best? with
      | none => some perm
      | some b => if score perm >= score b then some perm else some b) none

/-- Active or pre-departure `.playFromExile` permissions across all living players
(and live prepared `prepareSource` controllers while `o` is in exile). -/
def activePlayPermissions (g : Game) (o : GameObject) : Array PlayPermission :=
  let entries := g.playPermissionEntriesOf o.id
  if entries.isEmpty then #[]
  else
    let liveInExile := (g.findObject? o.id).any (·.zone == .exile)
    let stackCtrl? : Option PlayerId :=
      match g.findObject? o.id with
      | some live => if live.zone == .stack then live.controller <|> o.controller else none
      | none => g.latestExileToStackAfterController? o.id
    let needsHistGAt : Bool :=
      !liveInExile &&
        entries.any fun (_, _, perm, _) =>
          perm.requireSubtype.isSome || (perm.prepareSource.isSome && stackCtrl?.isNone)
    let gAt :=
      if !needsHistGAt then g
      else
        match g.exileDepartureIdx? o.id with
        | some idx => g.mkHistoricalGameAt idx
        | none => g
    let matching :=
      entries.filterMap fun (_, grantee, perm, _) =>
        let ctrl? : Option PlayerId :=
          match perm.prepareSource with
          | some src =>
            if liveInExile then
              match g.findObject? src with
              | some prm =>
                if prm.isOnBattlefield && prm.status.prepared then g.controllerOf prm else none
              | none => none
            else
              stackCtrl? <|>
                match gAt.findObject? src with
                | some prm =>
                  if prm.isOnBattlefield && prm.status.prepared then gAt.controllerOf prm else none
                | none => none
          | none => some grantee
        match ctrl? with
        | some c => if g.stillInGame c then some { perm with player := c } else none
        | none => none
    matching.filter fun perm =>
      match perm.requireSubtype with
      | none => true
      | some t => gAt.controlsAnySubtype perm.player #[t]

/-- Best active `.playFromExile` permission across living grantees for unattributed
mana-cost queries (`Costs.playManaCost` when `origPerm == none && card.controller == none`). -/
def bestActivePlayPermission? (g : Game) (o : GameObject)
    (face? : Option CardDef := none) : Option PlayPermission :=
  let perms0 :=
    g.activePlayPermissions o ++
      (if o.zone == .exile then
        g.livingPlayers.filterMap (fun pl =>
          if g.mayCastExiledBySource pl.id o then some { player := pl.id, anyMana := true } else none)
       else #[])
  let perms :=
    if isAdventureFace g o face? then perms0.filter (!·.fromAdventure) else perms0
  if perms.isEmpty then none
  else
    let mv := faceManaValue g o face?
    let score (perm : PlayPermission) : Nat :=
      let lifeOk := !perm.payLifeEqualManaValue || g.canPayLife perm.player mv
      (if lifeOk then 32 else 0) +
        (if perm.withoutManaCost then 16 else 0) +
        (if perm.payLifeEqualManaValue && lifeOk then 8 else 0) +
        (if perm.anyMana then 4 else 0) +
        (if perm.ignoreTiming then 2 else 0) +
        (if !perm.fromAdventure then 1 else 0)
    perms.foldl (fun best? perm =>
      match best? with
      | none => some perm
      | some b => if score perm >= score b then some perm else some b) none

/-- Whether `p` currently controls a legendary creature. -/
def controlsLegendaryCreature (g : Game) (p : PlayerId)
    (ok : GameObject → Bool := fun _ => true) : Bool :=
  (g.permanentsOf p).any (fun o =>
    ok o && g.isCreature o && g.isLegendary o)

/-- Whether `p` currently controls an Equipment. -/
def controlsEquipment (g : Game) (p : PlayerId)
    (ok : GameObject → Bool := fun _ => true) : Bool :=
  (g.permanentsOf p).any (fun o => ok o && g.isEquipment o)

/-- Intrinsic enters-tapped replacement check for whether `o` enters the battlefield
tapped under `p`'s control (CR 614.1c / 614.12 / 616.1e; rulings 808 / 809). -/
private def selfEntersTapped (g : Game) (p : PlayerId) (o : GameObject)
    (ok : GameObject → Bool := fun _ => true) : Bool :=
  let oBf : GameObject := { o with zone := .battlefield, controller := some p, defaultController := some p }
  let proposed := GameEvent.moved g.turnNumber
    { controller := some p, owner := o.owner, types := g.types oBf
      subtypes := g.subtypes oBf } .stack .battlefield
    (cause := .gameRule .permanentSpellResolved)
  if !proposed.watches .wouldEnterBattlefield then false
  else
    (g.staticAbilities oBf).any fun ab =>
      ab.anyReplacement fun cond? sp =>
        cond?.all (fun c => g.evalStaticCondFull oBf p c ok) &&
          match sp with
          | .entersTapped .self unless? =>
            match unless? with
            | none => true
            | some u => !(g.evalStaticCondFull oBf p u ok)
          | _ => false

/-- Whether `src` matches `ProtectionQuality` `q` as evaluated on `holder`
(CR 702.16b,e,f,j). -/
def matchesProtectionQuality (g : Game) (holder src : GameObject) (q : ProtectionQuality)
    (youOverride? : Option PlayerId := none) : Bool :=
  let youP := youOverride?.getD (g.you holder)
  match q with
  | .color (.literal c) => (g.colors src).contains c
  | .color .chosenOnSource =>
    match holder.status.chosenColor with
    | some c => (g.colors src).contains c
    | none => false
  | .color .commanderIdentity =>
    let pl := g.player youP
    if !pl.hasCommander then false
    else
      let cols := g.colors src
      Color.all.any fun c => pl.commanderColorIdentity.contains c && cols.contains c
  | .cardType ct => g.hasType src ct
  | .chosenCardType =>
    match holder.status.chosenCardType with
    | some t => g.hasType src t
    | none => false
  | .subtype (.literal s) => g.hasSubtype src s
  | .subtype .chosenOnSource =>
    match holder.status.chosenCreatureType with
    | some ty => g.hasSubtype src ty
    | none => false
  | .subtype (.fromStep _) => false
  | .quality pred => g.evalStaticPredFull holder youP src pred
  | .everything => true
  | .allColors => !(g.colors src).isColorless
  | .colorless => (g.colors src).isColorless

/-- Protection from the source's colors, card type, subtype, quality, or everything
(CR 702.16 / 613.1c–f). -/
def protectedFrom (g : Game) (o src : GameObject) : Bool :=
  (g.effectiveKeywords o).any fun
    | .protection q => g.matchesProtectionQuality o src q
    | _ => false

/-- Whether spell/ability source `src` matches `"hexproof from [quality]"` `q`
evaluated with respect to `holder` (CR 702.11d / 613.1c–f). -/
def matchesQualityFilter (g : Game) (holder src : GameObject) (q : QualityFilter)
    (youOverride? : Option PlayerId := none) : Bool :=
  let youP := youOverride?.getD (g.you holder)
  match q with
  | .color c => g.matchesProtectionQuality holder src (.color c) (youOverride? := some youP)
  | .cardType ct => g.hasType src ct
  | .subtype s => g.matchesProtectionQuality holder src (.subtype s) (youOverride? := some youP)
  | .objectPred pred => g.evalStaticPredFull holder youP src pred
  | .multicolored => (g.colors src).isMulticolored

/-- Whether permanent `o` has unconditional hexproof or hexproof from `src?`
(CR 702.11b,d / 613.1c–f). -/
def hasHexproofFrom (g : Game) (o : GameObject) (src? : Option GameObject := none) : Bool :=
  g.hasHexproof o ||
    match src? with
    | none => false
    | some src =>
      (g.effectiveKeywords o).any fun
        | .hexproof (some q) => g.matchesQualityFilter o src q
        | _ => false

/-- Whether battlefield Aura `auraObj` may enchant `host` after Layer 4 and
Layer 6 evaluation, including protection and CR 303.4a `enchantRestriction`
(CR 303.4 / 613.1d / 613.1f / 702.16c / 704.5m). -/
def auraObjCanEnchant (g : Game) (host auraObj : GameObject) : Bool :=
  let statics := g.staticAbilities auraObj
  let auraCtrl := g.you auraObj
  host.isOnBattlefield && !g.protectedFrom host auraObj &&
    match statics.findSome? StaticAbility.enchantRestriction? with
    | none => g.isCreature host
    | some slot =>
      let matchesDom (dom : TargetDomain) : Bool :=
        match dom with
        | .object _ pred => g.evalStaticPredFull auraObj auraCtrl host pred
        | .anyOf ds => ds.any fun
            | .object _ pred => g.evalStaticPredFull auraObj auraCtrl host pred
            | _ => false
        | _ => false
      matchesDom slot.domain

/-- Reconstruct a pre-batch `Game` board for CR 303.4f / 614.12 ETB replacement
and Aura host legality checks so co-entering permanents' static abilities do not
contaminate evaluation during simultaneous entry, while keeping effects scoped
to `enteringId?` or active replacement effects visible. -/
def preBatchAuraBoard (g : Game) (preBf? : Option (Array GameObject) := none)
    (enteringId? : Option ObjectId := none) : Game :=
  let isolatedEffects : Array (EffectId × ContinuousEffectSpec) :=
    if !g.currentBatch.isSome then g.activeEffects
    else
      match enteringId? with
      | none => g.openBatchEffects
      | some eid =>
        let extra := g.activeEffects.filter fun (efId, eff) =>
          !g.openBatchEffects.any (·.1 == efId) &&
            match eff with
            | .layered (.objects #[tid]) .. => tid == eid
            | .replacement .. => true
            | _ => false
        g.openBatchEffects ++ extra
  match preBf? with
  | some preBf =>
    let nonBf := g.objects.filter (fun o => o.zone != .battlefield && !preBf.any (·.id == o.id))
    { g with objects := preBf ++ nonBf, activeEffects := isolatedEffects }
  | none =>
    if g.currentBatch.isSome then
      let objs :=
        match enteringId? with
        | some eid =>
          if g.openBatchObjects.any (·.id == eid) then g.openBatchObjects
          else
            match g.objects.find? (·.id == eid) with
            | some eo => g.openBatchObjects.push eo
            | none => g.openBatchObjects
        | none => g.openBatchObjects
      { g with
        objects := objs
        players := g.openBatchPlayers
        activeEffects := isolatedEffects
        stack := g.openBatchStack }
    else g

/-- Result of applying CR 616.1a–g enters-the-battlefield replacement effects
to a permanent or token about to enter the battlefield. -/
structure EtbReplacementResult where
  candidate : GameObject
  entersWith : CounterBag := #[]
  weaverBonus : Nat := 0
  applied : Array ReplacementId := #[]
  cause : Option EventCause := none
  choice? : Option (PlayerId × Array ReplacementId) := none
  /-- `(originalPrinted, copyCard)` when Cursed Mirror enters as a copy of a
  creature with haste until end of turn (CR 614.1c / 614.12 / Ruling 1015). -/
  tempCopyUntilEot : Option (CardDef × CardDef) := none
  /-- True when a non-cast Aura could not legally enchant any object on the
  battlefield and therefore stays in its origin zone (CR 303.4f–g). -/
  stayInOriginNoAuraHost : Bool := false
  /-- True when a double-faced card (or copy of one) would enter the battlefield
  with an instant or sorcery face up and therefore stays in its origin zone or
  goes to its owner's graveyard from the stack (CR 701.27j / 712.11b). -/
  stayInOriginInstantOrSorceryDfc : Bool := false

/-- Run the CR 616.1a–g replacement loop for `candidate` about to enter the
battlefield (CR 614.1c / 614.12 / 614.15 / 616.1):
- `616.1a` (`self`): self-replacement effects of a resolving spell or ability (CR 614.15).
- `616.1b` (`control`): `entersUnderControl`.
- `616.1c` (`copy`): `entersAsCopy`, `entersAsCopyCreatureUntilEot` / `declineEntersAsCopy`.
- `616.1d` (`backFaceUp`): `entersBackFaceUp` (including daybound entering
  transformed when `g.isNight`, CR 702.145b).
- `303.4f–g` (`auraHost`): non-cast Aura host selection.
- `616.1e` (`other`): `entersTappedSelf`, `entersUntappedPayLife` /
  `entersTappedDeclinePayLife`, `entersUntappedBehold` / `entersTappedDeclineBehold`,
  `asEntersChoose*`, `entersWithCountersSelf` (loyalty, printed +1/+1, X +1/+1,
  indestructible, shield, hope-per-creature, Saga lore), and
  `entersWithExtraCounters` (including Arwen, Weaver of Hope,
  `othersEnterWithPlusOneEqualToughness`).
- `616.1g`: unified contained counter-putting replacements via
  `replaceCountersPutChoice` once per `CounterKind` on the combined entering
  counter bag after CR 616.1a–f modifications. -/
def applyEtbReplacements (g : Game) (candidate : GameObject)
    (fromStackTime : Nat := 0) (applyHope : Bool := true)
    (asOf : Nat := g.timestamp) (extraCounters : CounterBag := #[])
    (leavingPlay : Bool := false) (forceBackFace : Bool := false)
    (applied : Array ReplacementId := #[])
    (cause : Option EventCause := none)
    (order : Array ReplacementId := g.replacementOrder)
    (nonCastBattlefield : Bool := false)
    (preBattlefield : Option (Array GameObject) := none) : EtbReplacementResult := Id.run do
  let _ := asOf
  let preBfOk (c : GameObject) : Bool :=
    c.isOnBattlefield && c.id != candidate.id &&
      match preBattlefield with
      | some pb => pb.any (fun pre => pre.id == c.id && pre.isOnBattlefield)
      | none =>
        g.currentBatch.isNone ||
          g.openBatchObjects.any (fun pre => pre.id == c.id && pre.isOnBattlefield)
  let chosableCardTypes : Array CardType :=
    #[.creature, .artifact, .battle, .enchantment, .instant, .kindred, .land, .planeswalker, .sorcery]
  let mut cur := candidate
  let mut bag : CounterBag := #[]
  let mut rawCounters : CounterBag := #[]
  if fromStackTime > 0 then
    rawCounters := rawCounters.add .time fromStackTime
  let mut rawWeaverBonus : Nat := 0
  for (k, n) in extraCounters do
    if n > 0 then
      rawCounters := rawCounters.add k n
  let mut curApplied := applied
  let mut curCause := cause
  let mut curOrder := order
  let mut choice? : Option (PlayerId × Array ReplacementId) := none
  let mut weaverBonus : Nat := 0
  let mut tempCopy : Option (CardDef × CardDef) := none
  let mut stayInOriginNoAuraHost : Bool := false
  let mut stayInOriginInstantOrSorceryDfc : Bool := false
  let mut fuel := 32
  while fuel > 0 do
    fuel := fuel - 1
    let ctrl := cur.controller.getD cur.owner
    let curBf : GameObject :=
      { cur with zone := .battlefield, controller := some ctrl, defaultController := some ctrl }
    let board := g.preBatchAuraBoard preBattlefield (enteringId? := some cur.id)
    let bc := board.baseCard curBf
    let retains := board.retainsPrintedAbilities curBf
    let sas := board.staticAbilities curBf
    let flatSelfReps : Array StaticReplacementSpec :=
      if cur.status.faceDown then #[]
      else
        sas.foldl (fun acc ab =>
          match ab with
          | .replacement cond? spec =>
            if cond?.all (fun c => board.evalStaticCondFull curBf ctrl c preBfOk) then
              acc ++ spec.flatten
            else acc
          | _ => acc) #[]
    let mut specs : Array ReplacementSpec := #[]
    let mut pushedInteractive616e : Bool := false
    -- 616.1e / 614.12: intrinsic enters-tapped replacement
    let selfTap := !cur.status.faceDown && !cur.status.tapped && board.selfEntersTapped ctrl curBf preBfOk
    if selfTap then
      specs := specs.push {
        id := { kind := .entersTappedSelf, object := some cur.id }
        source := some cur.id
        controller := some ctrl
        affectedPlayer := ctrl
        kind := .entersTappedSelf cur.id
      }
    -- 616.1e / 614.12: interactive pay-life / behold enters-tapped replacements
    for sp in flatSelfReps do
      match sp with
      | .entersTappedUnlessPay cost =>
        if !pushedInteractive616e then
          if let some n := cost.items.findSome? (fun | .payLife (.const k) => some k.toNat | _ => none) then
            let idPay : ReplacementId :=
              { kind := .entersUntappedPayLife n, object := some cur.id, player := some ctrl }
            let idTap : ReplacementId :=
              { kind := .entersTappedDeclinePayLife, object := some cur.id, player := some ctrl }
            if !curApplied.contains idPay && !curApplied.contains idTap then
              pushedInteractive616e := true
              let canPay :=
                n == 0 || ((g.player ctrl).life ≥ (n : Int) && !g.lifeLocked ctrl && !g.lifeCantChange ctrl)
              if canPay || curOrder.contains idPay then
                specs := specs.push {
                  id := idPay
                  source := some cur.id
                  controller := some ctrl
                  affectedPlayer := ctrl
                  kind := .entersUntappedPayLife cur.id n
                }
              specs := specs.push {
                id := idTap
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .entersTappedDeclinePayLife cur.id
              }
          else if let some sub := cost.items.findSome? (fun | .behold s => some s | _ => none) then
            let idTap : ReplacementId :=
              { kind := .entersTappedDeclineBehold, object := some cur.id, player := some ctrl }
            let beheldAlready :=
              curApplied.contains idTap ||
                curApplied.any (fun rid =>
                  rid.object == some cur.id &&
                    match rid.kind with
                    | .entersUntappedBehold _ _ => true
                    | _ => false)
            if !beheldAlready then
              pushedInteractive616e := true
              let bfMatches :=
                (board.permanentsOf ctrl).filter (fun o => preBfOk o && board.hasSubtype o sub)
              let handMatches :=
                (g.player ctrl).hand.filterMap (fun hid =>
                  if hid == cur.id then none
                  else
                    match g.findObject? hid with
                    | some ho => if isDiscardableCard ho && board.hasSubtype ho sub then some ho else none
                    | none => none)
              for bo in bfMatches ++ handMatches do
                let idBehold : ReplacementId :=
                  { kind := .entersUntappedBehold bo.id sub, object := some cur.id, player := some ctrl }
                specs := specs.push {
                  id := idBehold
                  source := some cur.id
                  controller := some ctrl
                  affectedPlayer := ctrl
                  kind := .entersUntappedBehold cur.id bo.id sub
                }
              specs := specs.push {
                id := idTap
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .entersTappedDeclineBehold cur.id
              }
      | _ => pure ()
    -- 616.1e / 614.12: interactive “As ~ enters, choose ...” printed ETB choices
    for sp in flatSelfReps do
      if !pushedInteractive616e then
        match sp with
        | .asEntersChoose .color =>
          if cur.status.chosenColor.isNone &&
              !curApplied.any (fun rid =>
                rid.object == some cur.id &&
                  match rid.kind with | .asEntersChooseColor _ => true | _ => false) then
            pushedInteractive616e := true
            for col in Color.all do
              specs := specs.push {
                id := { kind := .asEntersChooseColor col, object := some cur.id, player := some ctrl }
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseColor cur.id col
              }
        | .asEntersChoose .creatureType =>
          if cur.status.chosenCreatureType.isNone &&
              !curApplied.any (fun rid =>
                rid.object == some cur.id &&
                  match rid.kind with | .asEntersChooseCreatureType _ => true | _ => false) then
            pushedInteractive616e := true
            match curOrder.findSome? (fun rid =>
              if rid.object == some cur.id && rid.player == some ctrl then
                match rid.kind with
                | .asEntersChooseCreatureType sub => some (rid, sub)
                | _ => none
              else none) with
            | some (rid, sub) =>
              specs := specs.push {
                id := rid
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseCreatureType cur.id sub
              }
            | none =>
              specs := specs.push {
                id := { kind := .asEntersChooseCreatureTypePrompt, object := some cur.id, player := some ctrl }
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseCreatureType cur.id .human
              }
        | .asEntersChoose .oddOrEven =>
          if cur.status.chosenOdd.isNone &&
              !curApplied.any (fun rid =>
                rid.object == some cur.id &&
                  match rid.kind with | .asEntersChooseOdd _ => true | _ => false) then
            pushedInteractive616e := true
            for odd in #[true, false] do
              specs := specs.push {
                id := { kind := .asEntersChooseOdd odd, object := some cur.id, player := some ctrl }
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseOdd cur.id odd
              }
        | .asEntersChoose .nonlandCardName =>
          if cur.status.chosenName.isNone &&
              !curApplied.any (fun rid =>
                rid.object == some cur.id &&
                  match rid.kind with | .asEntersChooseCardName _ => true | _ => false) then
            pushedInteractive616e := true
            match curOrder.findSome? (fun rid =>
              if rid.object == some cur.id && rid.player == some ctrl then
                match rid.kind with
                | .asEntersChooseCardName nm => some (rid, nm)
                | _ => none
              else none) with
            | some (rid, nm) =>
              specs := specs.push {
                id := rid
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseCardName cur.id nm
              }
            | none =>
              specs := specs.push {
                id := { kind := .asEntersChooseCardNamePrompt, object := some cur.id, player := some ctrl }
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseCardName cur.id ""
              }
        | .asEntersChoose .cardType =>
          if cur.status.chosenCardType.isNone &&
              !curApplied.any (fun rid =>
                rid.object == some cur.id &&
                  match rid.kind with | .asEntersChooseCardType _ => true | _ => false) then
            pushedInteractive616e := true
            for ct in chosableCardTypes do
              specs := specs.push {
                id := { kind := .asEntersChooseCardType ct, object := some cur.id, player := some ctrl }
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseCardType cur.id ct
              }
        | .asEntersChoose (.namedAnchors anchors) =>
          if cur.status.chosenAnchor.isNone &&
              !curApplied.any (fun rid =>
                rid.object == some cur.id &&
                  match rid.kind with | .asEntersChooseAnchor _ => true | _ => false) then
            pushedInteractive616e := true
            for anch in anchors do
              specs := specs.push {
                id := { kind := .asEntersChooseAnchor anch, object := some cur.id, player := some ctrl }
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .asEntersChooseAnchor cur.id anch
              }
        | _ => pure ()
    -- 616.1e / 614.12: printed enters-with-counters replacements
    if !cur.status.faceDown then
      if board.isPlaneswalker curBf then
        if let some loy := bc.loyalty then
          if loy > 0 then
            specs := specs.push {
              id := { kind := .entersWithLoyalty, object := some cur.id }
              source := some cur.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .entersWithCountersSelf cur.id .loyalty loy.toNat
            }
      for sp in flatSelfReps do
        match sp with
        | .entersWithCounters .self k amtExpr false =>
          let (ridKind, cnt) : ReplacementEffectKind × Nat :=
            if k == .plusOnePlusOne && amtExpr == .chosenX then
              (.entersWithXPlusOne, (cur.chosenX.orElse (fun _ => g.chosenXOf? cur.id)).getD 0)
            else if k == .hope && amtExpr == StaticAbility.countBf (.all #[.hasType .creature, .controlledBy .you]) then
              let others := ((board.creaturesControlledBy ctrl).filter preBfOk).size
              let selfCount := if board.isCreature curBf then 1 else 0
              (.entersWithHopePerCreature, others + selfCount)
            else
              let n := (board.evalStaticValFull curBf ctrl amtExpr preBfOk).toNat
              let rk :=
                match k with
                | .plusOnePlusOne => .entersWithPlusOneCounters
                | .indestructible => .entersWithIndestructibleCounter
                | .shield => .entersWithShield
                | .hope => .entersWithHopePerCreature
                | _ => .entersWithPlusOneCounters
              (rk, n)
          if cnt > 0 then
            let ck? := if ridKind == .entersWithPlusOneCounters && k != .plusOnePlusOne then some k else none
            specs := specs.push {
              id := { kind := ridKind, object := some cur.id, counterKind := ck? }
              source := some cur.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .entersWithCountersSelf cur.id k cnt
            }
        | _ => pure ()
      if board.hasSubtype curBf .saga && (bc.hasSagaChapters || board.finalChapterNumber curBf > 0) then
        specs := specs.push {
          id := { kind := .entersWithSagaLore, object := some cur.id }
          source := some cur.id
          controller := some ctrl
          affectedPlayer := ctrl
          kind := .entersWithCountersSelf cur.id .lore 1
        }
    -- 616.1c / 614.12: Cursed Mirror optional copy-as-enters until end of turn
    for sp in flatSelfReps do
      match sp with
      | .asEntersMayCopy copyFilter .untilEndOfTurn _ =>
        let idDecline : ReplacementId :=
          { kind := .declineEntersAsCopy, object := some cur.id, player := some ctrl }
        let copyDecided :=
          curApplied.contains idDecline ||
            curApplied.any (fun rid =>
              rid.object == some cur.id &&
                match rid.kind with | .entersAsCopyCreatureUntilEot _ => true | _ => false)
        if !copyDecided then
          let bfMatches := board.battlefield.filter (fun c =>
            preBfOk c && board.evalStaticPredFull curBf ctrl c copyFilter.pred preBfOk)
          if !bfMatches.isEmpty then
            for c in bfMatches do
              specs := specs.push {
                id := { kind := .entersAsCopyCreatureUntilEot c.id, object := some cur.id, player := some ctrl }
                source := some cur.id
                controller := some ctrl
                affectedPlayer := ctrl
                kind := .entersAsCopyCreatureUntilEot cur.id c.id
              }
            specs := specs.push {
              id := idDecline
              source := some cur.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .declineEntersAsCopy cur.id
            }
      | _ => pure ()
    -- 616.1d: intrinsic daybound / back-face-up replacement (CR 702.145b / 712.11)
    if !cur.status.transformed && (board.unmaskedCopiableValues curBf).otherFace.isSome &&
        (forceBackFace || (!leavingPlay && retains && bc.daybound && board.isNight)) then
      specs := specs.push {
        id := { kind := .entersBackFaceUp, object := some cur.id }
        source := some cur.id
        controller := some ctrl
        affectedPlayer := ctrl
        kind := .entersBackFaceUp (some cur.id)
      }
    -- 616.1e: external enters-with-additional-counters replacements (e.g. Arwen, Weaver of Hope)
    if applyHope && !cur.status.faceDown then
      for weaver in board.permanentsOf ctrl do
        if weaver.id != cur.id && preBfOk weaver then
          for ab in board.staticAbilities weaver do
            match ab with
            | .replacement cond? spec =>
              if cond?.all (fun c => board.evalStaticCondFull weaver ctrl c preBfOk) then
                for sp in spec.flatten do
                  match sp with
                  | .entersWithCounters (.matching sc) k amtExpr true =>
                    if board.matchesStaticScopeFull weaver ctrl curBf sc then
                      let bonus : Nat := (board.evalStaticValFull weaver ctrl amtExpr preBfOk).toNat
                      if bonus > 0 then
                        specs := specs.push {
                          id := { kind := .othersEnterWithPlusOneEqualToughness, object := some weaver.id }
                          source := some weaver.id
                          controller := some ctrl
                          affectedPlayer := ctrl
                          kind := .entersWithExtraCounters (some cur.id) k bonus
                        }
                  | _ => pure ()
            | _ => pure ()
    -- Active `ContinuousEffect.replacement` specs targeting `cur.id` (or `none` wildcard)
    for (_, eff) in board.activeEffects do
      match eff with
      | .replacement spec d =>
        if board.durationActive d then
          match spec.kind with
          | .entersTappedSelf tid | .entersWithCountersSelf tid .. =>
            if tid == cur.id then
              specs := specs.push { spec with affectedPlayer := ctrl }
          | .entersUnderControl tid _ | .entersAsCopy tid _
          | .entersBackFaceUp tid | .entersWithExtraCounters tid .. =>
            if tid.isNone || tid == some cur.id then
              specs := specs.push { spec with affectedPlayer := ctrl }
          | _ => pure ()
      | _ => pure ()
    -- CR 701.27j / 712.11b: a double-faced card (or copy of a double-faced card)
    -- cannot enter the battlefield with an instant or sorcery face up.
    if !cur.status.faceDown && cur.printed.otherFace.isSome &&
        cur.printed.types.any CardType.isInstantOrSorcery then
      let pendingCtrlCopyFace :=
        specs.any (fun s => !curApplied.contains s.id && s.tier.rank < ReplacementTier.auraHost.rank)
      if !pendingCtrlCopyFace then
        stayInOriginInstantOrSorceryDfc := true
        specs := #[]
        fuel := 0
    -- CR 303.4f–g,i: non-cast Aura (or untargeted Aura spell / copy) entering
    -- `.battlefield` must attach to an object it can legally enchant (or remain in
    -- its origin zone / go to graveyard / cease to exist if none exists).
    if !stayInOriginInstantOrSorceryDfc && nonCastBattlefield && !cur.status.faceDown &&
        cur.attachedTo.isNone && board.isAura curBf then
      let pendingCtrlCopyFace :=
        specs.any (fun s => !curApplied.contains s.id && s.tier.rank < ReplacementTier.auraHost.rank)
      let hostDecided :=
        curApplied.any (fun rid =>
          rid.object == some cur.id &&
            match rid.kind with | .asEntersAttachAura _ => true | _ => false)
      if !pendingCtrlCopyFace && !hostDecided then
        let candidatePool : Array GameObject :=
          match preBattlefield with
          | some pb => pb
          | none =>
            if g.currentBatch.isSome then
              g.openBatchObjects.filter GameObject.isOnBattlefield
            else g.battlefield
        let legalHosts :=
          candidatePool.filter (fun (h : GameObject) =>
            h.id != cur.id && (g.findObject? h.id).any GameObject.isOnBattlefield &&
              board.auraObjCanEnchant h curBf)
        if legalHosts.isEmpty then
          stayInOriginNoAuraHost := true
          specs := #[]
          fuel := 0
        else
          for h in legalHosts do
            specs := specs.push {
              id := { kind := .asEntersAttachAura h.id, object := some cur.id, player := some ctrl }
              source := some cur.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .asEntersAttachAura cur.id h.id
            }
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
        curCause :=
          match spec.kind with
          | .asEntersAttachAura .. => curCause
          | _ => g.wrapReplacedCause chosen.id curCause (some ctrl)
        match spec.kind with
        | .entersTappedSelf _
        | .entersTappedDeclinePayLife _ | .entersTappedDeclineBehold _ =>
          cur := { cur with status := { cur.status with tapped := true } }
        | .entersUntappedPayLife _ _ =>
          let idTap : ReplacementId :=
            { kind := .entersTappedDeclinePayLife, object := some cur.id, player := some ctrl }
          if !curApplied.contains idTap then
            curApplied := curApplied.push idTap
        | .entersUntappedBehold _ _ _ =>
          let idTap : ReplacementId :=
            { kind := .entersTappedDeclineBehold, object := some cur.id, player := some ctrl }
          if !curApplied.contains idTap then
            curApplied := curApplied.push idTap
        | .asEntersChooseColor _ col =>
          cur := { cur with status := { cur.status with chosenColor := some col } }
        | .asEntersChooseCreatureType _ sub =>
          cur := { cur with status := { cur.status with chosenCreatureType := some sub } }
        | .asEntersChooseOdd _ odd =>
          cur := { cur with status := { cur.status with chosenOdd := some odd } }
        | .asEntersChooseCardName _ nm =>
          cur := { cur with status := { cur.status with chosenName := some nm } }
        | .asEntersChooseCardType _ ct =>
          cur := { cur with status := { cur.status with chosenCardType := some ct } }
        | .asEntersChooseAnchor _ anch =>
          cur := { cur with status := { cur.status with chosenAnchor := some anch } }
        | .entersWithCountersSelf _ k n =>
          if n > 0 then
            rawCounters := rawCounters.add k n
        | .entersUnderControl _ newCtrl =>
          cur := { cur with controller := some newCtrl, defaultController := some newCtrl }
        | .entersAsCopy _ template =>
          let keepToken := cur.printed.isToken
          let newPrinted := { template with
            isToken := keepToken
            otherFace := template.otherFace.map (fun f => { f with isToken := keepToken }) }
          let st := cur.status
          let st' :=
            if st.faceDown then st
            else { st with prepared := template.entersPrepared }
          cur := { cur with printed := newPrinted, status := st' }
        | .entersAsCopyCreatureUntilEot _ targetId =>
          match board.findObject? targetId with
          | some target =>
            let baseCopy := board.copiableValues target
            let keepToken := cur.printed.isToken
            let copyCard : CardDef := { baseCopy with
              isToken := keepToken
              keywords := KeywordAbility.add baseCopy.keywords Keyword.haste
              otherFace := baseCopy.otherFace.map (fun f => { f with isToken := keepToken }) }
            let origPrinted := match tempCopy with | some (orig, _) => orig | none => cur.printed
            tempCopy := some (origPrinted, copyCard)
            let st := cur.status
            let st' :=
              if st.faceDown then st
              else { st with prepared := copyCard.entersPrepared }
            cur := { cur with printed := copyCard, status := st' }
          | none => pure ()
        | .declineEntersAsCopy _ =>
          pure ()
        | .entersBackFaceUp _ =>
          match (board.unmaskedCopiableValues curBf).otherFace with
          | some back =>
            let keepToken := cur.printed.isToken
            let newPrinted := { back with
              isToken := keepToken
              otherFace := some { cur.printed with isToken := keepToken, otherFace := none } }
            let st := cur.status
            let st' :=
              if st.faceDown then { st with transformed := true }
              else
                { st with
                  transformed := true
                  prepared := back.entersPrepared }
            cur := { cur with
              printed := newPrinted
              status := st' }
          | none => pure ()
        | .asEntersAttachAura _ hid =>
          if (g.findObject? hid).any (·.isOnBattlefield) then
            cur := { cur with attachedTo := some hid }
          else
            stayInOriginNoAuraHost := true
            fuel := 0
        | .entersWithExtraCounters _ k n =>
          let isWeaver := spec.id.kind == .othersEnterWithPlusOneEqualToughness
          if n > 0 then
            if isWeaver then
              rawWeaverBonus := rawWeaverBonus + n
            rawCounters := rawCounters.add k n
        | _ => pure ()
  -- CR 616.1g / 122.6: evaluate contained counter-putting replacements once per
  -- `CounterKind` on the combined entering counter bag after CR 616.1a–f.
  if choice?.isNone && !stayInOriginNoAuraHost && !stayInOriginInstantOrSorceryDfc && !rawCounters.isEmpty then
    let effCtrl := cur.controller.getD cur.owner
    let enterTarget : GameObject :=
      { cur with zone := .battlefield, controller := some effCtrl, defaultController := some effCtrl }
    let board := g.preBatchAuraBoard preBattlefield (enteringId? := some cur.id)
    for (k, rawN) in rawCounters do
      if rawN > 0 && choice?.isNone then
        let (n', app', c', subChoice?, ord') :=
          board.replaceCountersPutChoice enterTarget k rawN
            (putter := some effCtrl) (entersWith := true)
            (entering := some enterTarget)
            (applied := curApplied) (cause := curCause) (order := curOrder)
            (preBattlefield := preBattlefield)
        curOrder := ord'
        match subChoice? with
        | some ch => choice? := some ch
        | none =>
          if k == .plusOnePlusOne && rawWeaverBonus > 0 then
            weaverBonus :=
              if rawWeaverBonus >= rawN then n'
              else n' - (n' * (rawN - rawWeaverBonus)) / rawN
          bag := bag.add k n'
          curApplied := app'
          curCause := c'
  let curBase :=
    match tempCopy with
    | some (origPrinted, _) => { cur with printed := origPrinted, isCopy := candidate.isCopy }
    | none => cur
  let finalObj :=
    if bag.isEmpty then curBase
    else { curBase with status := curBase.status.withCounterBag bag }
  return {
    candidate := finalObj
    entersWith := bag
    weaverBonus := weaverBonus
    applied := curApplied
    cause := curCause
    choice? := choice?
    tempCopyUntilEot := tempCopy
    stayInOriginNoAuraHost := stayInOriginNoAuraHost
    stayInOriginInstantOrSorceryDfc := stayInOriginInstantOrSorceryDfc
  }

/-- Whether `blocker`'s static abilities currently allow it to be declared as
a blocker (CR 509.1b). Checked only when declaring blockers. -/
def mayDeclareAsBlocker (g : Game) (blocker : GameObject) : Bool :=
  let bCtrl := g.controllerOf blocker |>.getD blocker.owner
  (g.staticAbilities blocker).all fun ab =>
    !ab.anyRule fun cond? r =>
      cond?.all (fun c => g.evalStaticCondFull blocker bCtrl c) &&
        match r with
        | .combat (.cantBlock .self none) => true
        | .combat (.cantBlock .self (some u)) => !(g.evalStaticCondFull blocker bCtrl u)
        | _ => false

def canAttack (g : Game) (o : GameObject) : Bool :=
  let oCtrl := g.controllerOf o |>.getD o.owner
  o.isOnBattlefield && g.isCreature o &&
  g.controlledBy o g.activePlayer &&
  !o.status.tapped && (!g.hasDefender o || g.mayAttackDespiteDefender o) &&
  !g.hasSummoningSickness o &&
  !g.enchantedCantAttackOrBlock o &&
  (g.staticAbilities o).all fun ab =>
    !ab.anyRule fun cond? r =>
      cond?.all (fun c => g.evalStaticCondFull o oCtrl c) &&
        match r with
        | .combat (.cantAttack .self) => true
        | .combat (.cantAttackUnless .self need) => !(g.evalStaticCondFull o oCtrl need)
        | _ => false

/-- Evaluate a `Condition` or `ObjectPred` that may mention evaluated power/toughness
and Layer 6 keywords (for combat blocking rules such as `cantBeBlockedIfPowerAtMost` /
`smallCreaturesYouControlUnblockable`). -/
private def evalCombatStatPred (g : Game) (src : GameObject) (srcCtrl : PlayerId)
    (target : GameObject) (pred : ObjectPred) : Bool :=
  g.evalStaticPredFull src srcCtrl target pred

/-- Whether `o` can't be blocked, printed or granted in Layer 6
(CR 509.1b / 611.2a / 613.1f), or while its power/toughness satisfies a combat rule. -/
def hasCantBeBlocked (g : Game) (o : GameObject) : Bool :=
  let oCtrl := g.controllerOf o |>.getD o.owner
  let selfUnblockable :=
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        match r with
        | .combat (.cantBeBlocked .self) =>
          match cond? with
          | none => true
          | some (.forAll .this pred) => o.isOnBattlefield && g.evalCombatStatPred o oCtrl o pred
          | some c => o.isOnBattlefield && g.evalStaticCondFull o oCtrl c
        | _ => false
  selfUnblockable ||
    (!o.isLkiSnapshot && o.isOnBattlefield &&
      g.objects.any fun src =>
        src.isOnBattlefield &&
          let srcCtrl := g.controllerOf src |>.getD src.owner
          (g.staticAbilities src).any fun ab =>
            ab.anyRule fun cond? r =>
              cond?.all (fun c => g.evalStaticCondFull src srcCtrl c) &&
                match r with
                | .combat (.cantBeBlocked (.matching sc)) =>
                  sc.zones.zones.contains o.zone.kind &&
                    g.evalCombatStatPred src srcCtrl o sc.pred
                | _ => false)

/-- Minimum number of creatures required to block `o`, or `0` if unrestricted.
Menace is 2; Troll of Khazad-dûm is 3. -/
def minBlockersRequired (g : Game) (o : GameObject) : Nat :=
  let oCtrl := g.controllerOf o |>.getD o.owner
  let fromStatic :=
    (g.staticAbilities o).foldl (fun acc ab =>
      match ab with
      | .ruleModifying cond? rule =>
        if cond?.all (fun c => g.evalStaticCondFull o oCtrl c) then
          rule.flatten.foldl (fun a r =>
            match r with
            | .combat (.minBlockers .self n) => max a n
            | _ => a) acc
        else acc
      | _ => acc) 0
  max fromStatic (if g.hasMenace o then 2 else 0)

/-- Maximum number of creatures that may block `o`, if a static caps it. -/
def maxBlockersAllowed (g : Game) (o : GameObject) : Option Nat :=
  let oCtrl := g.controllerOf o |>.getD o.owner
  (g.staticAbilities o).foldl (fun acc ab =>
    match ab with
    | .ruleModifying cond? rule =>
      if cond?.all (fun c => g.evalStaticCondFull o oCtrl c) then
        rule.flatten.foldl (fun a r =>
          match r with
          | .combat (.maxBlockers .self n) =>
            some (match a with | some m => min m n | none => n)
          | _ => a) acc
      else acc
    | _ => acc) none

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
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        cond?.all (fun c => g.evalStaticCondFull o p c) &&
          match r with
          | .combat (.cantAttackPlayer (.all #[.hasType .creature, .hasKeyword .flying]) .you) => true
          | _ => false)

/-- Evaluate a CR 702.14 `[land-predicate]walk` predicate against one land `o`
controlled by the defending player. -/
private partial def landMatchesLandwalkPred (g : Game) (o : GameObject) : ObjectPred → Bool
  | .anyObject => g.isLand o
  | .hasType t => g.hasType o t
  | .hasSubtype (.literal s) => g.hasSubtype o s
  | .hasSupertype st => g.hasSupertype o st
  | .not p => !g.landMatchesLandwalkPred o p
  | .all ps => ps.all (g.landMatchesLandwalkPred o)
  | .any ps => ps.any (g.landMatchesLandwalkPred o)
  | _ => false

/-- True when `attacker` has any `.landwalk pred` keyword (already Layer-3
text-changed in Layer 6) and `defender` controls a matching land (CR 702.14). -/
def isLandwalkUnblockable (g : Game) (attacker : GameObject) (defender : PlayerId) : Bool :=
  (g.currentKeywords attacker).any fun
    | .landwalk pred =>
      (g.permanentsOf defender).any fun land =>
        g.isLand land && g.landMatchesLandwalkPred land pred
    | _ => false

/-- Whether `blocker` may be assigned to `attacker` as one creature in a
declaration (CR 509.1b / 702.14 / 702.16f / 702.147a / 805.10d–e / 810.7). Menace is not a pairwise restriction. -/
def canBlock (g : Game) (blocker attacker : GameObject) : Bool :=
  let defender := g.defendingPlayerOf attacker
  let atkCtrl := g.controllerOf attacker |>.getD attacker.owner
  let landwalkUnblockable := g.isLandwalkUnblockable attacker defender
  let controlledByDefendingTeam :=
    g.controlledBy blocker defender ||
      g.livingPlayers.any (fun m => g.areTeammates defender m.id && g.controlledBy blocker m.id)
  let blockedByStaticRule :=
    (g.staticAbilities attacker).any fun ab =>
      ab.anyRule fun cond? r =>
        cond?.all (fun c => g.evalStaticCondFull attacker atkCtrl c) &&
          match r with
          | .combat (.cantBeBlockedBy .self pred) =>
            g.evalCombatStatPred attacker atkCtrl blocker pred
          | _ => false
  blocker.isOnBattlefield && g.isCreature blocker &&
  controlledByDefendingTeam && !blocker.status.tapped &&
  blocker.status.blocking.isEmpty && !g.cantBlockUntilEot blocker &&
  !g.hasDecayed blocker &&
  g.mayDeclareAsBlocker blocker &&
  !g.enchantedCantAttackOrBlock blocker &&
  (!g.creaturesWithoutFlyingCantBlock || g.hasFlying blocker) &&
  attacker.status.attacking &&
  !g.protectedFrom attacker blocker &&
  !g.hasCantBeBlocked attacker &&
  !landwalkUnblockable &&
  !blockedByStaticRule &&
  (!g.hasFlying attacker ||
    g.hasFlying blocker || g.hasReach blocker) &&
  !(g.hasFlying blocker &&
    match g.controllerOf attacker with
    | some p => g.leftoverFlyingRestriction p
    | none => false) &&
  (!(g.hasShadow attacker) || g.hasShadow blocker) &&
  (!(g.hasShadow blocker) || g.hasShadow attacker) &&
  !(match g.cantBeBlockedByPlayer attacker with
    | some pid => g.controlledBy blocker pid
    | none => false) &&
  !(g.cantBeBlockedExceptByHasteUntilEot attacker && !g.hasHaste blocker)

/-- True when `id` is the source of a chapter ability waiting or on the stack
(CR 715.4). -/
def sagaChapterPending (g : Game) (id : ObjectId) : Bool :=
  let waiting :=
    g.waitingTriggers.any (fun wt =>
      wt.source.id == id && wt.ability.isSagaChapter)
  let stacked :=
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.sourceId == some id &&
          o.triggeredAbility.any (·.isSagaChapter)
      | none => false)
  waiting || stacked

/-- The player has hexproof (unconditional or from `src?`) from opponents via any
battlefield permanent, command-zone emblem static ability, or active `PlayerRule.hexproof`
continuous effect (CR 114.4 / 611.2c / 702.11c–d). -/
def playerHasHexproof (g : Game) (p : PlayerId) (src? : Option GameObject := none) : Bool :=
  (g.objects.any fun src =>
    (src.isOnBattlefield || (src.zone == .command && (g.baseCard src).types.isEmpty)) &&
      let srcCtrl := g.you src
      (g.staticAbilities src).any fun ab =>
        ab.anyRule fun cond? r =>
          cond?.all (fun c => g.evalStaticCondFull src srcCtrl c) &&
            match r with
            | .player (.hexproof who none) =>
              g.matchStaticPlayerFilterFull src srcCtrl who p
            | .player (.hexproof who (some q)) =>
              g.matchStaticPlayerFilterFull src srcCtrl who p &&
                match src? with
                | some s => g.matchesQualityFilter src s q
                | none => false
            | _ => false) ||
  (g.activeEffects.any fun (_, e) =>
    match e with
    | .playerRule q (.hexproof from? srcId? _) d =>
      q == p && g.durationActive d &&
        match from? with
        | none => true
        | some qf =>
          match src? with
          | none => false
          | some s =>
            let holder : GameObject :=
              (srcId?.bind g.damageSourceById?).getD
                { (default : GameObject) with id := noSourceSentinelId, owner := p, controller := some p }
            g.matchesQualityFilter holder s qf (youOverride? := some p)
    | _ => false)

/-- Damage already assigned on a “divided as you choose” stack entry (CR 601.2d). -/
def assignedDividedDamage (e : StackEntry) : Nat :=
  e.dividedDamage.foldl (· + ·) 0

/-- Whether this stacked triggered ability still needs targets or a damage
division announced (CR 603.3d / 601.2d). -/
def triggerStillNeedsTargets (e : StackEntry) (ab : TriggeredAbility) : Bool :=
  match ab.dividedDamage? with
  | some (amount, _) => assignedDividedDamage e < amount
  | none =>
    if ab.targetSpec.allowsZero || ab.targetSpec.totalPositions > 1 then
      !e.targetsAnnounced
    else ab.requiresTarget && e.targets.isEmpty

/-- Stack entry for a triggered ability that still needs targets announced
(CR 603.3d). Oldest first so targets are chosen in the order abilities were
put on the stack. -/
def triggerNeedingTargets (g : Game) : Option StackEntry :=
  g.stack.find? (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      match o.triggeredAbility, o.abilityEffect with
      | some _, some eff =>
        -- A modal trigger whose modes were chosen (CR 603.3c).
        match eff.dividedDamage? with
        | some (amount, _) => assignedDividedDamage e < amount
        | none =>
          let spec := eff.targets
          if spec.allowsZero || spec.totalPositions > 1 then
            !e.targetsAnnounced
          else eff.requiresTarget && e.targets.isEmpty
      | some ab, none =>
        if ab.isModal then false
        else triggerStillNeedsTargets e ab
      | none, _ => false
    | none => false)

/-- Resolve the spell or ability source `GameObject` (live or LKI) for CR 702.16b
protection checks during target announcement and resolution. -/
def targetingSourceObject? (g : Game) (sourceId : Option ObjectId := none) : Option GameObject :=
  match sourceId with
  | some sid =>
    match g.findObject? sid with
    | some o =>
      if o.zone == .stack && (o.abilityEffect.isSome || o.triggeredAbility.isSome) then
        o.sourceId.bind g.damageSourceById?
      else if o.zone == .battlefield && o.status.phasedOut then
        g.damageSourceById? sid
      else some o
    | none => g.damageSourceById? sid
  | none =>
    match g.proposedSpell with
    | some prop =>
      if prop.kind == .spell then g.findObject? prop.spellId
      else prop.sourceId.bind g.damageSourceById?
    | none =>
      match g.resolvingSpell with
      | some spId => g.damageSourceById? spId
      | none =>
        match g.resolvingAbility with
        | some abId =>
          match g.findObject? abId with
          | some abObj => abObj.sourceId.bind g.damageSourceById?
          | none => g.currentResolvingContext?.bind (fun (src?, _) => src?.bind g.damageSourceById?)
        | none =>
          match g.currentResolvingContext? with
          | some (some sid, _) => g.damageSourceById? sid
          | _ =>
            match g.pending with
            | .chooseTargets _ =>
              match g.triggerNeedingTargets with
              | some e =>
                match g.findObject? e.objectId with
                | some o => o.sourceId.bind g.damageSourceById?
                | none => none
              | none => none
            | _ => none

/-- Whether battlefield permanent `em` grants `target` player protection from `src?`
via a `.player (.protectionFrom who q)` static ability (CR 702.16b,e,j). When `src?`
is `none`, only `.everything` matches. -/
def permanentGrantsPlayerProtectionFrom (g : Game) (em : GameObject) (target : PlayerId)
    (src? : Option GameObject) : Bool :=
  let emCtrl := g.you em
  (g.staticAbilities em).any fun ab =>
    ab.anyRule fun cond? r =>
      cond?.all (fun c => g.evalStaticCondFull em emCtrl c) &&
        match r with
        | .player (.protectionFrom who q) =>
          g.matchStaticPlayerFilterFull em emCtrl who target &&
            match src? with
            | some src => g.matchesProtectionQuality em src q
            | none => q == .everything
        | _ => false

/-- Whether `target` has protection from `src?` granted by any battlefield permanent
or command-zone emblem's `.player (.protectionFrom ..)` static ability (CR 114.4 / 702.16b,e,j). -/
def playerProtectedFromStatic (g : Game) (target : PlayerId) (src? : Option GameObject) : Bool :=
  g.objects.any fun em =>
    (em.isOnBattlefield || (em.zone == .command && (g.baseCard em).types.isEmpty)) &&
      g.permanentGrantsPlayerProtectionFrom em target src?

/-- Whether a `PlayerRule.protectionFrom q srcId? ctrl?` active effect on `target`
protects `target` from `src?` (CR 702.16b,e,j). When `src?` is `none`, only
`.everything` matches. -/
def playerProtectionRuleMatches (g : Game) (target : PlayerId) (q : ProtectionQuality)
    (srcId? : Option ObjectId) (_ctrl? : Option PlayerId) (src? : Option GameObject) : Bool :=
  match src? with
  | some src =>
    let holder : GameObject :=
      (srcId?.bind g.damageSourceById?).getD
        { (default : GameObject) with id := noSourceSentinelId, owner := target, controller := some target }
    g.matchesProtectionQuality holder src q (youOverride? := some target)
  | none => q == .everything

/-- Whether `target` has protection from `src?` granted by an active
`PlayerRule.protectionFrom` continuous effect (CR 702.16b,e,j). -/
def playerProtectedFromRule (g : Game) (target : PlayerId) (src? : Option GameObject) : Bool :=
  g.activeEffects.any fun (_, e) =>
    match e with
    | .playerRule p (.protectionFrom q srcId? ctrl?) d =>
      p == target && g.durationActive d &&
        g.playerProtectionRuleMatches target q srcId? ctrl? src?
    | _ => false

/-- Whether `target` has protection from `src?` via either `.protectionFromEverything`,
an active `PlayerRule.protectionFrom` effect, or a static permanent/emblem ability
(CR 114.4 / 702.16b,e,j). -/
def playerProtectedFrom (g : Game) (target : PlayerId) (src? : Option GameObject) : Bool :=
  g.protectionFromEverything target ||
    g.playerProtectedFromStatic target src? ||
    g.playerProtectedFromRule target src?

/-- Hexproof and player protection stop targeting a player (CR 702.11c / 702.16j). -/
def playerCanBeTargetedBy (g : Game) (caster target : PlayerId)
    (sourceId : Option ObjectId := none) : Bool :=
  let src? := g.targetingSourceObject? sourceId
  let protBlock := g.playerProtectedFrom target src?
  g.stillInGame target &&
    (caster == target || g.areTeammates caster target || !g.playerHasHexproof target src?) &&
    !protBlock

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
  else attackers.foldl (fun acc accObj => max acc (g.power accObj)) (g.power attackers[0]!)

/-- Creatures currently blocking `attackerId` (CR 506.4 / 509.1g). -/
def blockersOf (g : Game) (attackerId : ObjectId) : Array GameObject :=
  if !(g.findObject? attackerId).any (fun a => a.isOnBattlefield && a.status.attacking) then #[]
  else g.battlefield.filter (fun b => b.status.blocking.contains attackerId)

/-- Attacking creatures `blocker` is still blocking (CR 510.1d). -/
def creaturesBlockedBy (g : Game) (blocker : GameObject) : Array GameObject :=
  blocker.status.blocking.filterMap (fun id =>
    match g.findObject? id with
    | some a =>
      if a.isOnBattlefield && a.status.attacking then some a else none
    | none => none)

/-- Snapshot `o` as an `EventObject` with Layer 1–7 characteristics (CR 113.7a / 613.1). -/
def snapshot (g : Game) (o : GameObject) : EventObject :=
  let bc := g.baseCard o
  let pw : Option Int :=
    if o.isLkiSnapshot then o.printed.powerValue
    else if o.zone == .battlefield then
      if g.isCreature o || bc.power.isSome then some (g.snapshotPower o) else none
    else
      (g.lastKnownPowerOf? o.id).orElse (fun _ =>
        if g.isCreature o || bc.power.isSome then some (g.snapshotPower o) else none)
  let tg : Option Int :=
    if o.isLkiSnapshot then o.printed.toughnessValue
    else if o.zone == .battlefield then
      if g.isCreature o || bc.toughness.isSome then some (g.snapshotToughness o) else none
    else
      (g.lastKnownToughnessOf? o.id).orElse (fun _ =>
        if g.isCreature o || bc.toughness.isSome then some (g.snapshotToughness o) else none)
  let curKw := g.currentKeywords o
  { id := some o.id
    controller := g.controllerOf o
    defaultController := o.defaultController
    owner := o.owner
    name := g.name o
    colors := g.colors o
    manaValue := g.objectManaValue o
    supertypes := g.supertypes o
    types := g.types o
    subtypes := g.subtypes o
    power := pw
    toughness := tg
    loyalty := bc.loyalty.map Int.toNat
    keywords := curKw
    toxic := KeywordAbility.toxicTotal curKw
    staticAbilities := g.staticAbilities o
    triggeredAbilities := g.triggeredAbilities o
    zone := o.zone
    tapped := o.status.tapped
    attacking := o.status.attacking
    blocking := !o.status.blocking.isEmpty
    blockingIds := o.status.blocking
    phasedOut := o.status.phasedOut
    faceDown := o.status.faceDown
    transformed := o.status.transformed
    prepared := o.status.prepared
    harnessed := o.status.harnessed
    goaded := o.status.goaded || !o.status.goadedBy.isEmpty
    goadedBy := o.status.goadedBy
    goadedUntilNextTurnOf := o.status.goadedUntilNextTurnOf
    ringBearer :=
      if o.isLkiSnapshot then (o.lkiLayer6.map (·.ringBearer)).getD false
      else o.isOnBattlefield &&
        g.players.any (fun pl => pl.ringBearerId == some o.id && g.controllerOf o == some pl.id)
    attachedTo := o.attachedTo
    counters := o.status.toCounterBag
    token := o.printed.isToken
    isCopy := o.isCopy || g.hasActiveCopy o
    isCommander := o.isCommander
    changeling := KeywordAbility.hasSimple curKw .changeling
    chosenOdd := o.status.chosenOdd
    chosenCreatureType := o.status.chosenCreatureType
    chosenColor := o.status.chosenColor
    chosenName := o.status.chosenName
    chosenCardType := o.status.chosenCardType
    chosenAnchor := o.status.chosenAnchor
    summoningSick := o.status.summoningSick
    attackingTarget := o.status.attackingTarget
    printed := some o.printed
    copiable := some (g.copiableValues o)
    adventurerCard := o.adventurerCard
    chosenX := o.chosenX
    retainsPrintedAbilities := some (g.retainsPrintedAbilities o)
    prowessCount := (g.prowessTriggers o).size
    ironFistTapGrants := g.ironFistTapGrants o
    wardCosts := g.wardCostsOn o
    activatedAbilities := some (g.activatedAbilitiesOf o) }

/-- Extra times a trigger of `source` fires from Bifur / Chief / Wizard's Staff
statics (CR 603.2d). Each such ability adds its extra count; they stack. -/
def extraTriggerCopies (g : Game) (controller : PlayerId) (source : GameObject) : Nat :=
  if !source.isOnBattlefield then 0
  else
  let story :=
    (g.player controller).enduringStory ||
      (g.controlsStoried controller && g.storiedPermanentCount controller >= 3)
  (g.permanentsOf controller).foldl (fun acc o =>
    (g.staticAbilities o).foldl (fun acc ab =>
      match ab with
      | .ruleModifying cond? rule =>
        let condOk :=
          match cond? with
          | none => true
          | some c =>
            if c == StaticAbility.condEnduringStory then story
            else g.evalStaticCondFull o controller c
        if condOk then
          rule.flatten.foldl (fun a r =>
            match r with
            | .trigger (.extraTrigger sc extra) =>
              if g.matchesStaticScopeFull o controller source sc then a + extra else a
            | _ => a) acc
        else acc
      | _ => acc) acc) 0

/-- Append waiting-trigger snapshots, skipping any controller who has already
lost or left the game (CR 800.4d). -/
def enqueueWaitingTriggers (g : Game) (wts : Array WaitingTrigger) : Game :=
  let wts := wts.filter (fun wt => g.stillInGame wt.controller)
  if wts.isEmpty then g
  else
    let e := GameEvent.engine g.turnNumber (.enqueueWaitingTriggers wts)
    ({ g with events := g.events.push e }).applyEngineChange (.enqueueWaitingTriggers wts)

/-- Karn, Argent Defender: an artifact or creature entering doesn't cause
abilities to trigger (CR 603.2 / 101.2; rulings 891–893). -/
def eventSuppressedByKarn (g : Game) (e : GameEvent) : Bool :=
  let enteringObj? : Option EventObject :=
    match e.change with
    | .rules (.zone (.moved _ after fromZone .battlefield ..)) =>
      if fromZone != .battlefield && !after.phasedOut then some after else none
    | .rules (.zone (.created obj _)) =>
      if obj.zone == .battlefield && !obj.phasedOut then some obj else none
    | _ => none
  match enteringObj? with
  | none => false
  | some eo =>
    let eoObj := damageSourceObjectFromLki eo
    g.battlefield.any fun src =>
      let srcCtrl := g.controllerOf src |>.getD src.owner
      (g.staticAbilities src).any fun ab =>
        ab.anyRule fun cond? r =>
          cond?.all (fun c => g.evalStaticCondFull src srcCtrl c) &&
            match r with
            | .trigger (.suppressEnteringTriggers sc) =>
              g.evalStaticPredFull src srcCtrl eoObj sc.pred
            | _ => false

/-- True when any CR 603.4 intervening `"if"` clause (and optional-once-per-turn
guard) holds for `ab` given `controller`, `source`, and `cause`. -/
def triggerConditionHolds (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (cause : Option GameObject := none) (source : Option GameObject := none) : Bool :=
  let optOnceOk :=
    !ab.optionalOnceEachTurn ||
      match source with
      | some s => !g.optionalOnceUsedThisTurn s.id
      | none => true
  let whenOk :=
    ab.pattern.outerWhenConds.all (g.evalTriggerCond controller source cause ·)
  optOnceOk && whenOk &&
    ab.interveningIf?.all (g.evalTriggerCond controller source cause ·)

/-- Cheap event-family bitmask over a committed `batch` so `matchTriggers` skips
non-matching `TriggerPattern`s in O(1) without running predicate evaluators. -/
private structure BatchEventMask where
  hasZoneEnter : Bool := false
  hasZoneLeave : Bool := false
  hasZoneMove : Bool := false
  hasCreate : Bool := false
  hasSacrifice : Bool := false
  hasDraw : Bool := false
  hasDiscard : Bool := false
  hasCountered : Bool := false
  hasTap : Bool := false
  hasUntap : Bool := false
  hasPhaseOut : Bool := false
  hasUnattach : Bool := false
  hasCounters : Bool := false
  hasControlLost : Bool := false
  hasAttack : Bool := false
  hasBlock : Bool := false
  hasBecameBlocked : Bool := false
  hasDamage : Bool := false
  hasLifeGain : Bool := false
  hasLifeLoss : Bool := false
  hasCast : Bool := false
  hasActivate : Bool := false
  hasTarget : Bool := false
  hasPlayerAction : Bool := false
  hasPlayerLost : Bool := false
  hasStep : Bool := false
  hasStackResolve : Bool := false
  hasTriggered : Bool := false

private def BatchEventMask.ofBatch (batch : Array GameEvent) (hasControlLost : Bool) :
    BatchEventMask :=
  batch.foldl (fun m e =>
    let m := if !e.countersPutInEvent.isEmpty then { m with hasCounters := true } else m
    match e.change with
    | .engine _ => m
    | .rules r =>
      match r with
      | .zone (.created obj _) =>
        if obj.zone == .battlefield && !obj.phasedOut then
          { m with hasZoneEnter := true, hasCreate := true, hasZoneMove := true }
        else m
      | .zone (.moved before _ fromZ toZ verb _ _ _) =>
        let isEnter := fromZ != .battlefield && toZ == .battlefield
        let isLeave := fromZ == .battlefield && toZ != .battlefield && !before.phasedOut
        let isSac := isLeave && verb == .sacrifice
        let isDraw := match fromZ, toZ, verb with | .library _, .hand _, .draw _ _ => true | _, _, _ => false
        let isDisc := match fromZ, verb with | .hand p, .discard => toZ != .hand p | _, _ => false
        let isCtr := fromZ == .stack && verb == .counter
        { m with
          hasZoneMove := true
          hasZoneEnter := m.hasZoneEnter || isEnter
          hasZoneLeave := m.hasZoneLeave || isLeave
          hasSacrifice := m.hasSacrifice || isSac
          hasDraw := m.hasDraw || isDraw
          hasDiscard := m.hasDiscard || isDisc
          hasCountered := m.hasCountered || isCtr }
      | .zone (.ceasedToExist snap) =>
        if snap.zone == .battlefield && !snap.phasedOut then
          { m with hasZoneLeave := true, hasZoneMove := true }
        else m
      | .permanent (.tapped _ _) => { m with hasTap := true }
      | .permanent (.untapped _) => { m with hasUntap := true }
      | .permanent (.phasedOut _ _) => { m with hasPhaseOut := true }
      | .permanent (.unattached _ _) => { m with hasUnattach := true }
      | .permanent (.counters ..) => { m with hasCounters := true }
      | .permanent _ => m
      | .combat (.attackersDeclared _ _) => { m with hasAttack := true }
      | .combat (.blockersDeclared _ _) => { m with hasBlock := true }
      | .combat (.becameBlocked _ _) => { m with hasBecameBlocked := true }
      | .combat _ => m
      | .damage (.dealt _) => { m with hasDamage := true }
      | .damage _ => m
      | .life (.gained _ _) => { m with hasLifeGain := true }
      | .life (.lost _ _ _ _) => { m with hasLifeLoss := true }
      | .cast (.spellCast _ _ _) => { m with hasCast := true, hasTarget := true }
      | .cast (.abilityActivated _ _ _ _) => { m with hasActivate := true, hasTarget := true }
      | .cast (.targeted _ _ _ _) => { m with hasTarget := true }
      | .cast _ => m
      | .player (.lost _ _) => { m with hasPlayerLost := true, hasPlayerAction := true }
      | .player (.scried ..) | .player (.surveilled ..) | .player (.proliferated ..)
      | .player (.ringTempted ..) | .player (.manaAdded ..) => { m with hasPlayerAction := true }
      | .player _ => m
      | .turn (.stepBegan _ _) => { m with hasStep := true }
      | .turn _ => m
      | .stackObject (.resolved ..) => { m with hasStackResolve := true }
      | .stackObject _ => m
      | .triggerQueue (.triggered ..) => { m with hasTriggered := true }
      | .triggerQueue _ => m
      | .continuousEffect _ | .delayedTrigger _ => m)
    { hasControlLost := hasControlLost }

private def patternCouldMatchMask (m : BatchEventMask) : TriggerPattern → Bool
  | .zoneChange _ fromZ toZ _ _ =>
    if !fromZ.isBattlefieldOnly && toZ.isBattlefieldOnly then m.hasZoneEnter
    else if fromZ.isBattlefieldOnly && !toZ.isBattlefieldOnly then m.hasZoneLeave
    else m.hasZoneMove
  | .createTokens .. => m.hasCreate
  | .sacrifice .. => m.hasSacrifice
  | .drawCard .. => m.hasDraw
  | .discard .. => m.hasDiscard
  | .becomesTapped .. => m.hasTap
  | .becomesUntapped .. => m.hasUntap
  | .phasesOut .. => m.hasPhaseOut
  | .becomesUnattached .. => m.hasUnattach
  | .controlLost .. => m.hasControlLost
  | .putCounters .. => m.hasCounters
  | .attacks .. => m.hasAttack
  | .blocks .. => m.hasBlock
  | .becomesBlocked .. => m.hasBecameBlocked
  | .damageDealt .. => m.hasDamage
  | .gainLife .. => m.hasLifeGain
  | .loseLife .. => m.hasLifeLoss
  | .castSpell .. => m.hasCast
  | .activateAbility .. => m.hasActivate
  | .becomesTarget .. => m.hasTarget
  | .spellCountered .. => m.hasCountered
  | .playerAction _ .losesGame => m.hasPlayerLost
  | .playerAction .. => m.hasPlayerAction
  | .stepBegins .. => m.hasStep
  | .stackObjectResolves .. => m.hasStackResolve
  | .abilityTriggers .. => m.hasTriggered
  | .whenCond inner _ => patternCouldMatchMask m inner
  | .or a b => patternCouldMatchMask m a || patternCouldMatchMask m b

/-- Matched trigger occurrence payload before `BatchGrouping` aggregation. -/
private structure TriggerMatchPayload where
  eventIdx : Nat := 0
  cause : Option GameObject := none
  causeIds : Array ObjectId := #[]
  causeController : Option PlayerId := none
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  eventCause : Option EventCause := none
  overrideAbility : Option TriggeredAbility := none
  groupPlayer? : Option PlayerId := none
  groupSourceId? : Option ObjectId := none
deriving Inhabited

private def isFullEventSnapshot (eo : EventObject) : Bool :=
  !eo.types.isEmpty || eo.printed.isSome || eo.copiable.isSome || !eo.name.isEmpty

private def findTriggerEventObj (board : Game) (eo : EventObject) : GameObject :=
  match eo.id.bind board.findObject? with
  | some o =>
    if isFullEventSnapshot eo &&
        ((!eo.phasedOut && o.zone == .battlefield && o.status.phasedOut) ||
          (eo.zone == .battlefield && !eo.phasedOut && !o.isOnBattlefield)) then
      damageSourceObjectFromLki eo
    else o
  | none => damageSourceObjectFromLki eo

private def resolveTriggerDamageSrc (pre : GameSnapshot) (post : Game) (eo : EventObject) : GameObject :=
  let filterLive (o : GameObject) : Bool :=
    !(o.zone == .battlefield && o.status.phasedOut && !eo.phasedOut)
  let postSrc? := (eo.id.bind post.findObject?).filter filterLive
  let preSrc? := (eo.id.bind pre.findObject?).filter filterLive
  match postSrc? with
  | some so =>
    if eo.zone == Zone.battlefield && !eo.phasedOut &&
        !so.isOnBattlefield && isFullEventSnapshot eo then
      damageSourceObjectFromLki eo
    else so
  | none =>
    if isFullEventSnapshot eo && eo.id.isSome then
      damageSourceObjectFromLki eo
    else preSrc?.getD (findTriggerEventObj post eo)

private def zoneEndpointMatches (board : Game) (src : GameObject) (srcCtrl : PlayerId)
    (spec : ZoneEndpointSpec) (z : Zone) : Bool :=
  let (zk, owner?) : ZoneKind × Option PlayerId :=
    match z with
    | .library p => (.library, some p)
    | .hand p => (.hand, some p)
    | .battlefield => (.battlefield, none)
    | .graveyard p => (.graveyard, some p)
    | .stack => (.stack, none)
    | .exile => (.exile, none)
    | .command => (.command, none)
    | .ante => (.ante, none)
    | .outside p => (.outside, some p)
  match spec with
  | .any => true
  | .notIn forbidden => zk != forbidden
  | .inZones zs =>
    zs.zones.contains zk &&
      match zs.owner with
      | .any => true
      | .matching pf => owner?.any (board.matchTriggerPlayerFilter src srcCtrl pf ·)
      | .ofPlayer pe =>
        let ps := board.evalStaticPlayerExprL5 src srcCtrl pe (fun _ => true)
          (some board.snapshotPT) (some board.currentKeywords)
          (hasKwExtra? := some board.liveObjectHasExtraKeyword)
        owner?.any ps.contains

private def uniquePermTargetsOn (board : Game) (targets : Array Target) : Array GameObject :=
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

private def targetMatchesRecipient (board : Game) (src : GameObject) (srcCtrl : PlayerId)
    (t : Target) (rf : RecipientFilter) : Bool :=
  match rf with
  | .any =>
    match t with
    | .player p => board.stillInGame p
    | .permanent id => (board.findObject? id).any (·.isOnBattlefield)
    | .card _ => false
  | .player pf =>
    match t with
    | .player p => board.stillInGame p && board.matchTriggerPlayerFilter src srcCtrl pf p
    | _ => false
  | .object f =>
    match t with
    | .permanent id =>
      (board.findObject? id).any fun o =>
        o.isOnBattlefield && board.evalTriggerPred src srcCtrl o f.pred
    | _ => false
  | .playerOrObject pf f =>
    match t with
    | .player p => board.stillInGame p && board.matchTriggerPlayerFilter src srcCtrl pf p
    | .permanent id =>
      (board.findObject? id).any fun o =>
        o.isOnBattlefield && board.evalTriggerPred src srcCtrl o f.pred
    | _ => false

/-- Collapse raw per-occurrence `TriggerMatchPayload`s according to CR 603.2c / 700.1
`BatchGrouping` semantics. -/
private def applyBatchGrouping (grouping : BatchGrouping) (hits : Array TriggerMatchPayload) :
    Array TriggerMatchPayload :=
  if hits.isEmpty then #[]
  else
    let mergeIds (xs : Array TriggerMatchPayload) : Array ObjectId :=
      xs.foldl (fun acc p =>
        let acc := match p.cause with
          | some o => if acc.contains o.id then acc else acc.push o.id
          | none => acc
        p.causeIds.foldl (fun a id => if a.contains id then a else a.push id) acc) #[]
    match grouping with
    | .perOccurrence | .counterThreshold .. => hits
    | .oncePerBatch =>
      let first := hits[0]!
      #[{ first with causeIds := if first.causeIds.isEmpty then #[] else mergeIds hits }]
    | .perPlayerInBatch =>
      Id.run do
        let mut seen : Array PlayerId := #[]
        let mut out : Array TriggerMatchPayload := #[]
        for h in hits do
          match h.groupPlayer?.orElse (fun _ => h.causeController) with
          | some pid =>
            if !seen.contains pid then
              seen := seen.push pid
              let group := hits.filter (fun x => x.groupPlayer?.orElse (fun _ => x.causeController) == some pid)
              let merged := if h.causeIds.isEmpty then #[] else mergeIds group
              out := out.push { h with causeIds := merged }
          | none =>
            out := out.push h
        return out
    | .perSourceInBatch =>
      Id.run do
        let mut seen : Array ObjectId := #[]
        let mut out : Array TriggerMatchPayload := #[]
        for h in hits do
          match h.groupSourceId?.orElse (fun _ => h.cause.map (·.id)) with
          | some sid =>
            if !seen.contains sid then
              seen := seen.push sid
              out := out.push h
          | none =>
            out := out.push h
        return out

/-- Pattern family 1: zone changes, token creation, sacrifice, draw, discard/cycle,
and spell countered (CR 603.6a/c / 603.10a,e / 701.6 / 701.9 / 701.21 / 702.29a). -/
@[noinline] private def matchZoneAndResourcePattern (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (board : Game) (src : GameObject) (srcCtrl : PlayerId)
    (grouping : BatchGrouping) (pat : TriggerPattern) (limit : TriggerLimit) :
    Array TriggerMatchPayload := Id.run do
  let mut hits : Array TriggerMatchPayload := #[]
  for eIdx in [0:batch.size] do
    let e := batch[eIdx]!
    match pat, e.change with
    | .zoneChange subj fromZ toZ verb? actor?, .rules (.zone (.created obj ctrl)) =>
      if obj.zone == .battlefield && !obj.phasedOut && !post.eventSuppressedByKarn e then
        let enterCtrl := obj.controller.getD ctrl
        let zOk :=
          zoneEndpointMatches board src srcCtrl fromZ (.outside ctrl) &&
            zoneEndpointMatches board src srcCtrl toZ .battlefield
        let verbOk := verb?.isNone
        let actorOk := actor?.all (board.matchTriggerPlayerFilter src srcCtrl · ctrl)
        if zOk && verbOk && actorOk then
          let entered := findTriggerEventObj board { obj with controller := some enterCtrl }
          if board.evalTriggerPred src srcCtrl entered subj then
            hits := hits.push {
              eventIdx := eIdx, cause := some entered, causeController := some enterCtrl,
              groupPlayer? := some enterCtrl, groupSourceId? := some entered.id }
    | .zoneChange subj fromZ toZ verb? actor?,
        .rules (.zone (.moved before after evFrom evTo evVerb evActor _ _)) =>
      let isEnter := evFrom != .battlefield && evTo == .battlefield
      let isLeaveBf := evFrom == .battlefield && evTo != .battlefield
      let suppressed := isEnter && (after.phasedOut || post.eventSuppressedByKarn e)
      let phasedLeave := isLeaveBf && before.phasedOut
      if !suppressed && !phasedLeave then
        let zOk :=
          zoneEndpointMatches board src srcCtrl fromZ evFrom &&
            zoneEndpointMatches board src srcCtrl toZ evTo
        let verbOk := verb?.all (· == evVerb)
        let actorOk := actor?.all (fun pf => evActor.any (board.matchTriggerPlayerFilter src srcCtrl pf ·))
        if zOk && verbOk && actorOk then
          let subjObj :=
            if pat.usesLookBack then findTriggerEventObj pre before
            else if isEnter then findTriggerEventObj post after
            else findTriggerEventObj board after
          let subjCtrl :=
            if pat.usesLookBack then
              (before.controller.orElse (fun _ => pre.controllerOf subjObj)).getD before.owner
            else
              (after.controller.orElse (fun _ => board.controllerOf subjObj)).getD after.owner
          if board.evalTriggerPred src srcCtrl subjObj subj then
            let lkp := if isLeaveBf then some (pre.snapshotPower subjObj) else none
            hits := hits.push {
              eventIdx := eIdx, cause := some subjObj, causeController := some subjCtrl,
              lastKnownPower := lkp, groupPlayer? := some subjCtrl,
              groupSourceId? := some subjObj.id }
    | .zoneChange subj fromZ toZ none none, .rules (.zone (.ceasedToExist snap)) =>
      if snap.zone == .battlefield && !snap.phasedOut then
        let zOk :=
          zoneEndpointMatches board src srcCtrl fromZ .battlefield &&
            zoneEndpointMatches board src srcCtrl toZ (.outside snap.owner)
        if zOk then
          let beforeObj := findTriggerEventObj pre snap
          let ctrl := (snap.controller.orElse (fun _ => pre.controllerOf beforeObj)).getD snap.owner
          if board.evalTriggerPred src srcCtrl beforeObj subj then
            hits := hits.push {
              eventIdx := eIdx, cause := some beforeObj, causeController := some ctrl,
              lastKnownPower := some (pre.snapshotPower beforeObj),
              groupPlayer? := some ctrl, groupSourceId? := some beforeObj.id }
    | .createTokens who tokenPred, .rules (.zone (.created obj ctrl)) =>
      if obj.zone == .battlefield && !obj.phasedOut && obj.token then
        let enterCtrl := obj.controller.getD ctrl
        let entered := findTriggerEventObj post { obj with controller := some enterCtrl }
        -- CR 111.2 / 701.7a: `who` is the player who created the token (`ctrl`),
        -- even if the token enters under another player's control (`enterCtrl`).
        if post.matchTriggerPlayerFilter src srcCtrl who ctrl &&
            post.evalTriggerPred src srcCtrl entered tokenPred then
          hits := hits.push {
            eventIdx := eIdx, cause := some entered, causeController := some ctrl,
            groupPlayer? := some ctrl, groupSourceId? := some entered.id }
    | .sacrifice who subj,
        .rules (.zone (.moved before _ .battlefield toZ .sacrifice actor _ _)) =>
      if toZ != .battlefield && !before.phasedOut then
        let beforeObj := findTriggerEventObj pre before
        let sacPlayer := actor.getD ((before.controller.orElse (fun _ => pre.controllerOf beforeObj)).getD before.owner)
        if pre.matchTriggerPlayerFilter src srcCtrl who sacPlayer &&
            pre.evalTriggerPred src srcCtrl beforeObj subj then
          hits := hits.push {
            eventIdx := eIdx, cause := some beforeObj, causeController := some sacPlayer,
            lastKnownPower := some (pre.snapshotPower beforeObj),
            groupPlayer? := some sacPlayer, groupSourceId? := some beforeObj.id }
    | .drawCard who exceptFirstDrawStep,
        .rules (.zone (.moved _ _ (.library libP) (.hand handP) (.draw drawIdx inDrawStep) _ _ _)) =>
      if libP == handP && (post.player handP).keptOpeningHand &&
          post.matchTriggerPlayerFilter src srcCtrl who handP &&
          (!exceptFirstDrawStep || !(inDrawStep && drawIdx == 1)) then
        let nthOk :=
          match limit with
          | .nthEachTurn n => drawIdx == n
          | _ => true
        if nthOk then
          hits := hits.push {
            eventIdx := eIdx, causeController := some handP, groupPlayer? := some handP }
    | .discard who cardPred mustBeCycle,
        .rules (.zone (.moved _ after (.hand handP) toZ .discard _ _ _)) =>
      if toZ != .hand handP && post.matchTriggerPlayerFilter src srcCtrl who handP then
        let cycleOk :=
          !mustBeCycle ||
            (match e.cause? with | some (.costPayment .cycle _ _) => true | _ => false)
        if cycleOk then
          let afterObj := findTriggerEventObj post after
          if post.evalTriggerPred src srcCtrl afterObj cardPred then
            let lkp :=
              if mustBeCycle then
                ((post.proposedSpell.bind (fun prop => post.chosenXOf? prop.spellId)).orElse
                  (fun _ => post.chosenXOf? afterObj.id)).map Int.ofNat
              else none
            let isBatchDiscard :=
              !mustBeCycle && (grouping == .perPlayerInBatch || grouping == .oncePerBatch)
            hits := hits.push {
              eventIdx := eIdx,
              cause := if isBatchDiscard then none else some afterObj,
              causeController := if isBatchDiscard then none else some handP,
              lastKnownPower := lkp, groupPlayer? := some handP,
              groupSourceId? := some afterObj.id }
    | .spellCountered spellPred,
        .rules (.zone (.moved before _ .stack toZ .counter _ _ _)) =>
      if toZ != .stack then
        let beforeObj := findTriggerEventObj pre before
        if pre.evalTriggerPred src srcCtrl beforeObj spellPred then
          hits := hits.push {
            eventIdx := eIdx, cause := some beforeObj,
            causeController := before.controller.orElse (fun _ => pre.controllerOf beforeObj),
            groupSourceId? := some beforeObj.id }
    | _, _ => pure ()
  return hits

/-- Pattern family 2: permanent state changes — tap/untap, phase-out, unattach,
control-lost, and counter placement including Saga chapters and plan thresholds
(CR 122.6 / 603.2e / 603.10b–d / 715.2b). -/
@[noinline] private def matchPermanentStatePattern (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (board : Game) (src : GameObject) (srcCtrl : PlayerId)
    (ab : TriggeredAbility) (pat : TriggerPattern)
    (controlLostList : Array (GameObject × PlayerId)) : Array TriggerMatchPayload := Id.run do
  let mut hits : Array TriggerMatchPayload := #[]
  match pat with
  | .controlLost subj formerCtrl =>
    for (o, oldCtrl) in controlLostList do
      if pre.matchTriggerPlayerFilter src srcCtrl formerCtrl oldCtrl &&
          pre.evalTriggerPred src srcCtrl o subj then
        hits := hits.push {
          -- Non-colliding synthetic occurrence id above all real batch indices `[0..batch.size-1]`
          -- so `.or` disjuncts never collide with batch event 0 while two `.controlLost`
          -- disjuncts matching the same permanent still deduplicate under CR 603.2c.
          eventIdx := batch.size + o.id.raw, cause := some o, causeController := some oldCtrl,
          groupPlayer? := some oldCtrl, groupSourceId? := some o.id }
    return hits
  | _ => pure ()
  let mut tappedBeforeThisIdx : Array ObjectId := #[]
  for eIdx in [0:batch.size] do
    let e := batch[eIdx]!
    match pat with
    | .putCounters putter? kind? subj =>
      let isZoneArrival : Bool :=
        match e.change with
        | .rules (.zone (.moved _ after fromZone .battlefield ..)) =>
          fromZone != .battlefield && !after.phasedOut
        | .rules (.zone (.created obj _)) => obj.zone == .battlefield && !obj.phasedOut
        | _ => false
      for (eo, kind, n, actor?) in e.countersPutInEvent do
        if n > 0 then
          match ab.grouping with
          | .counterThreshold targetKind chapters =>
            if kind == targetKind && !src.status.faceDown then
              let counterObj? : Option GameObject :=
                match (eo.id.bind post.findObject?).filter (·.isOnBattlefield) with
                | some postObj => if !postObj.status.faceDown then some postObj else none
                | none =>
                  if eo.zone == .battlefield && !eo.phasedOut && !eo.faceDown && isFullEventSnapshot eo then
                    some (damageSourceObjectFromLki eo)
                  else none
              match counterObj? with
              | some postObj =>
                if post.evalTriggerPred src srcCtrl postObj subj then
                  let prevCnt := if isZoneArrival then 0 else eo.counters.count targetKind
                  let newCnt := prevCnt + n
                  for ch in chapters do
                    if prevCnt < ch && ch ≤ newCnt then
                      let abForCh : TriggeredAbility :=
                        if targetKind == .lore then
                          { ab with grouping := .counterThreshold .lore #[ch] }
                        else ab
                      hits := hits.push {
                        eventIdx := eIdx, cause := some postObj,
                        overrideAbility := some abForCh,
                        groupSourceId? := some postObj.id }
              | none => pure ()
          | _ =>
            let kindOk := kind?.all (· == kind)
            let putterOk :=
              putter?.all fun pf =>
                actor?.any (post.matchTriggerPlayerFilter src srcCtrl pf ·)
            if kindOk && putterOk then
              let targetObj :=
                match (eo.id.bind post.findObject?).filter (·.isOnBattlefield) with
                | some live => live
                | none => damageSourceObjectFromLki eo
              if post.evalTriggerPred src srcCtrl targetObj subj then
                hits := hits.push {
                  eventIdx := eIdx, cause := some targetObj,
                  causeController := actor?.orElse (fun _ => eo.controller),
                  groupPlayer? := actor?, groupSourceId? := some targetObj.id }
    | _ =>
      match pat, e.change with
      | .becomesTapped subj onlyYourTurn firstTime costKind?, .rules (.permanent (.tapped obj _)) =>
        if !obj.phasedOut then
          let tObj := findTriggerEventObj post obj
          let priorTapped := pre.becameTappedThisTurn tObj.id || tappedBeforeThisIdx.contains tObj.id
          tappedBeforeThisIdx := tappedBeforeThisIdx.push tObj.id
          let turnOk := !onlyYourTurn || board.isOnActiveTeam srcCtrl
          let firstOk := !firstTime || !priorTapped
          let costOk :=
            costKind?.all fun ck =>
              match e.cause? with
              | some (.costPayment k _ _) => k == ck
              | _ => false
          if turnOk && firstOk && costOk && board.evalTriggerPred src srcCtrl tObj subj then
            hits := hits.push {
              eventIdx := eIdx, cause := some tObj,
              causeController := (board.controllerOf tObj).orElse (fun _ => obj.controller),
              groupSourceId? := some tObj.id }
      | .becomesUntapped subj, .rules (.permanent (.untapped obj)) =>
        if !obj.phasedOut then
          let uObj := findTriggerEventObj post obj
          if post.evalTriggerPred src srcCtrl uObj subj then
            hits := hits.push {
              eventIdx := eIdx, cause := some uObj,
              causeController := (post.controllerOf uObj).orElse (fun _ => obj.controller),
              groupSourceId? := some uObj.id }
      | .phasesOut subj, .rules (.permanent (.phasedOut before _)) =>
        if !before.phasedOut then
          let bObj := findTriggerEventObj pre before
          if pre.evalTriggerPred src srcCtrl bObj subj then
            hits := hits.push {
              eventIdx := eIdx, cause := some bObj,
              causeController := (pre.controllerOf bObj).orElse (fun _ => before.controller),
              groupSourceId? := some bObj.id }
      | .becomesUnattached attPred hostPred, .rules (.permanent (.unattached attSnap fromHost)) =>
        let attObj := findTriggerEventObj pre attSnap
        let hostOk :=
          hostPred == .anyObject ||
            (pre.findObject? fromHost).any (pre.evalTriggerPred src srcCtrl · hostPred)
        if hostOk && pre.evalTriggerPred src srcCtrl attObj attPred then
          hits := hits.push {
            eventIdx := eIdx, cause := some attObj,
            causeController := (pre.controllerOf attObj).orElse (fun _ => attSnap.controller),
            groupSourceId? := some attObj.id }
      | _, _ => pure ()
  return hits

/-- Pattern family 3: combat declaration triggers — attacks, blocks, becomes blocked
(CR 508.3 / 509.1 / 509.3c / 603.2c). -/
@[noinline] private def matchCombatPattern (post : Game) (batch : Array GameEvent)
    (src : GameObject) (srcCtrl : PlayerId) (grouping : BatchGrouping)
    (pat : TriggerPattern) : Array TriggerMatchPayload := Id.run do
  let mut hits : Array TriggerMatchPayload := #[]
  let attackTargetMatches (tgt : AttackTarget) (tf : AttackTargetFilter) : Bool :=
    match tf, tgt with
    | .any, _ => true
    | .player pf, .player d => post.matchTriggerPlayerFilter src srcCtrl pf d
    | .playerOrPlaneswalker pf, .player d => post.matchTriggerPlayerFilter src srcCtrl pf d
    | .playerOrPlaneswalker pf, .planeswalker pwId =>
      (post.damageSourceById? pwId).any fun pw =>
        (post.controllerOf pw).any (post.matchTriggerPlayerFilter src srcCtrl pf ·)
    | _, _ => false
  for eIdx in [0:batch.size] do
    let e := batch[eIdx]!
    match pat, e.change with
    | .attacks attPred tgtFilter alone minAtk minTotalPow? countIntoLk,
        .rules (.combat (.attackersDeclared _ decls)) =>
      let allAttacking := post.battlefield.filter (fun o => post.isCreature o && o.status.attacking)
      let matched : Array (GameObject × AttackTarget) :=
        decls.filterMap fun (eo, tgt) =>
          let aObj := (eo.id.bind post.findLiveSourceObject?).getD (damageSourceObjectFromLki eo)
          if post.evalTriggerPred src srcCtrl aObj attPred && attackTargetMatches tgt tgtFilter then
            let aloneOk :=
              if !alone then true
              else
                match tgtFilter, tgt with
                | .player _, .player d =>
                  !decls.any (fun (eo', tgt') => eo'.id != eo.id && tgt' == .player d)
                | .any, _ => decls.size == 1 && allAttacking.size == 1
                | _, _ => false
            if aloneOk then some (aObj, tgt) else none
          else none
      if !matched.isEmpty then
        let totalPowOk :=
          match minTotalPow? with
          | none => true
          | some need =>
            let tot : Int := matched.foldl (fun (acc : Int) (p : GameObject × AttackTarget) =>
              acc + post.snapshotPower p.1) 0
            tot ≥ need
        if totalPowOk then
          if grouping == .perPlayerInBatch then
            let players := matched.foldl (fun (acc : Array PlayerId) (_, tgt) =>
              match tgt with
              | .player d => if acc.contains d then acc else acc.push d
              | _ => acc) #[]
            for d in players do
              let grp := matched.filter (fun (_, tgt) => tgt == .player d)
              if grp.size ≥ minAtk then
                let grpIds := grp.map (·.1.id)
                hits := hits.push {
                  eventIdx := eIdx, cause := grp[0]?.map Prod.fst,
                  causeIds := grpIds, causeController := some d,
                  lastKnownPower := if countIntoLk then some (Int.ofNat grp.size) else none,
                  groupPlayer? := some d }
          else if matched.size ≥ minAtk then
            if grouping == .oncePerBatch then
              let grpIds := matched.map (·.1.id)
              hits := hits.push {
                eventIdx := eIdx, cause := matched[0]?.map Prod.fst, causeIds := grpIds,
                lastKnownPower := if countIntoLk then some (Int.ofNat matched.size) else none }
            else
              for (aObj, tgt) in matched do
                let lkp := if aObj.id == src.id then some (post.snapshotPower aObj) else none
                let lkt := if aObj.id == src.id then some (post.snapshotToughness aObj) else none
                let defP? := match tgt with | .player d => some d | _ => none
                hits := hits.push {
                  eventIdx := eIdx, cause := some aObj, causeController := defP?,
                  lastKnownPower := lkp, lastKnownToughness := lkt,
                  groupSourceId? := some aObj.id }
    | .blocks blockerPred, .rules (.combat (.blockersDeclared _ decls)) =>
      let mut seenBlockers : Array ObjectId := #[]
      for (blockerSnap, _) in decls do
        let b := findTriggerEventObj post blockerSnap
        if !seenBlockers.contains b.id then
          seenBlockers := seenBlockers.push b.id
          if post.evalTriggerPred src srcCtrl b blockerPred then
            hits := hits.push {
              eventIdx := eIdx, cause := some b,
              causeController := (post.controllerOf b).orElse (fun _ => blockerSnap.controller),
              groupSourceId? := some b.id }
    | .becomesBlocked attPred, .rules (.combat (.becameBlocked attackerSnap _)) =>
      let a := findTriggerEventObj post attackerSnap
      if post.evalTriggerPred src srcCtrl a attPred then
        hits := hits.push {
          eventIdx := eIdx, cause := some a,
          causeController := (post.controllerOf a).orElse (fun _ => attackerSnap.controller),
          groupSourceId? := some a.id }
    | _, _ => pure ()
  return hits

/-- Pattern family 4: damage dealt and life gain/loss triggers (CR 119 / 120 / 510.2). -/
@[noinline] private def matchDamageAndLifePattern (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (src : GameObject) (srcCtrl : PlayerId)
    (grouping : BatchGrouping) (pat : TriggerPattern) : Array TriggerMatchPayload := Id.run do
  match pat with
  | .damageDealt srcPred recFilter combatOnly noncombatOnly duringYourTurn =>
    if duringYourTurn && !post.isOnActiveTeam srcCtrl then return #[]
    let mut matched : Array (Nat × GameObject × Option GameObject × Option PlayerId × Nat) := #[]
    for eIdx in [0:batch.size] do
      match batch[eIdx]!.change with
      | .rules (.damage (.dealt pkts)) =>
        for pkt in pkts do
          if pkt.amount > 0 && (!combatOnly || pkt.combat) && (!noncombatOnly || !pkt.combat) then
            let dmgSrc := resolveTriggerDamageSrc pre post pkt.source
            let srcOk := srcPred == .anyObject || post.evalTriggerPred src srcCtrl dmgSrc srcPred
            if srcOk then
              let (recOk, recObj?, recPl?) : Bool × Option GameObject × Option PlayerId :=
                match recFilter, pkt.recipient with
                | .any, .player d => (post.stillInGame d, none, some d)
                | .any, .permanent eo | .any, .battle eo =>
                  (true, some (findTriggerEventObj post eo), none)
                | .player pf, .player d =>
                  (post.stillInGame d && post.matchTriggerPlayerFilter src srcCtrl pf d, none, some d)
                | .object f, .permanent eo | .object f, .battle eo =>
                  let ro := findTriggerEventObj post eo
                  (post.evalTriggerPred src srcCtrl ro f.pred, some ro, none)
                | .playerOrObject pf _, .player d =>
                  (post.stillInGame d && post.matchTriggerPlayerFilter src srcCtrl pf d, none, some d)
                | .playerOrObject _ f, .permanent eo | .playerOrObject _ f, .battle eo =>
                  let ro := findTriggerEventObj post eo
                  (post.evalTriggerPred src srcCtrl ro f.pred, some ro, none)
                | _, _ => (false, none, none)
              if recOk then
                matched := matched.push (eIdx, dmgSrc, recObj?, recPl?, pkt.amount)
      | _ => pure ()
    if matched.isEmpty then return #[]
    match grouping with
    | .oncePerBatch =>
      let mut total : Nat := 0
      let mut srcObjs : Array GameObject := #[]
      for (_, ds, _, _, amt) in matched do
        total := total + amt
        if !srcObjs.any (·.id == ds.id) then srcObjs := srcObjs.push ds
      let (eIdx0, _, _, pl0?, _) := matched[0]!
      return #[{
        eventIdx := eIdx0
        cause := srcObjs[0]?
        causeIds := srcObjs.map (·.id)
        causeController := pl0?
        lastKnownPower := some (Int.ofNat total) }]
    | .perPlayerInBatch =>
      let mut players : Array PlayerId := #[]
      let mut out : Array TriggerMatchPayload := #[]
      for (_, _, _, pl?, _) in matched do
        if let some d := pl? then
          if !players.contains d then
            players := players.push d
            let grp := matched.filter (fun (_, _, _, p?, _) => p? == some d)
            let tot := grp.foldl (fun a (_, _, _, _, amt) => a + amt) 0
            let (eIdx0, ds0, _, _, _) := grp[0]!
            out := out.push {
              eventIdx := eIdx0, cause := some ds0, causeController := some d,
              lastKnownPower := some (Int.ofNat tot), groupPlayer? := some d }
      return out
    | .perSourceInBatch =>
      -- When source is wildcard (`creatureYouControlDealtDamage`, She-Hulk), group by
      -- damaged permanent; otherwise group by damage source.
      let byRecipient := srcPred == .anyObject
      let mut seen : Array ObjectId := #[]
      let mut out : Array TriggerMatchPayload := #[]
      for (eIdx, ds, ro?, pl?, _) in matched do
        let keyObj := if byRecipient then ro?.getD ds else ds
        if !seen.contains keyObj.id then
          seen := seen.push keyObj.id
          let tot := matched.foldl (fun a (_, ds', ro'?, _, amt) =>
            let k' := if byRecipient then (ro'?.getD ds').id else ds'.id
            if k' == keyObj.id then a + amt else a) 0
          out := out.push {
            eventIdx := eIdx,
            cause := if byRecipient then none else some keyObj,
            causeController := pl?,
            lastKnownPower := some (Int.ofNat tot), groupSourceId? := some keyObj.id }
      return out
    | _ =>
      return matched.map fun (eIdx, ds, _, pl?, amt) =>
        { eventIdx := eIdx, cause := some ds, causeController := pl?,
          lastKnownPower := some (Int.ofNat amt), groupSourceId? := some ds.id }
  | .gainLife who =>
    let mut hits : Array TriggerMatchPayload := #[]
    for eIdx in [0:batch.size] do
      match batch[eIdx]!.change with
      | .rules (.life (.gained p amount)) =>
        if amount > 0 && post.matchTriggerPlayerFilter src srcCtrl who p then
          hits := hits.push {
            eventIdx := eIdx, causeController := some p,
            lastKnownPower := some (Int.ofNat amount), groupPlayer? := some p }
      | _ => pure ()
    return hits
  | .loseLife who =>
    let mut hits : Array TriggerMatchPayload := #[]
    for eIdx in [0:batch.size] do
      match batch[eIdx]!.change with
      | .rules (.life (.lost p amount _ _)) =>
        if amount > 0 && post.matchTriggerPlayerFilter src srcCtrl who p then
          hits := hits.push {
            eventIdx := eIdx, causeController := some p,
            lastKnownPower := some (Int.ofNat amount), groupPlayer? := some p }
      | _ => pure ()
    return hits
  | _ => return #[]

/-- Extract `(actor, causeObj?, isAbility, activeTargets, permTargets)` from a
targeting event in `batch` (CR 601.2i / 602.2b / 603.3d / 707.10c). -/
private def extractTargetingInfo (pre : GameSnapshot) (post : Game) (e : GameEvent) :
    Option (PlayerId × Option GameObject × Bool × Array Target × Array GameObject) :=
  match e.change with
  | .rules (.cast (.spellCast spellSnap caster _)) =>
    if spellSnap.name.isEmpty && !spellSnap.faceDown then none
    else
      let castObj := findTriggerEventObj post spellSnap
      let targets := ((post.stackEntry? castObj.id).map (·.targets)).getD #[]
      some (caster, some castObj, false, targets, uniquePermTargetsOn post targets)
  | .rules (.cast (.abilityActivated abilityId _ ctrl (.nonMana ..))) =>
    let targets := ((post.stackEntry? abilityId).map (·.targets)).getD #[]
    some (ctrl, post.findObject? abilityId, true, targets, uniquePermTargetsOn post targets)
  | .rules (.cast (.targeted objId rawTargets ..)) =>
    if post.proposedSpell.any (·.spellId == objId) || rawTargets.isEmpty then none
    else
      match post.findObject? objId, post.stackEntry? objId with
      | some obj, some se =>
        let ctrl := se.controller
        let prevEntry? := pre.stackEntry? objId
        let prevTargets := (prevEntry?.map (·.targets)).getD #[]
        let isAbility := obj.abilityEffect.isSome || obj.triggeredAbility.isSome
        if obj.isCopy then
          let newTgts := se.targets.filter (!prevTargets.contains ·)
          let prevPermIds := (uniquePermTargetsOn post prevTargets).map (·.id)
          let newlyTargeted := (uniquePermTargetsOn post se.targets).filter (fun o => !prevPermIds.contains o.id)
          some (ctrl, some obj, isAbility, newTgts, newlyTargeted)
        else if isAbility then
          let spec :=
            ((obj.abilityEffect.map (·.targets)).orElse (fun _ =>
              obj.triggeredAbility.map (·.targetSpec))).getD .none
          let totalSlots :=
            if spec.isMultiSlot then spec.totalPositions else 0
          let prevDone :=
            prevEntry?.any fun pe =>
              pe.targetsAnnounced && !pe.targets.isEmpty &&
                pe.targets.size + pe.skippedOptionalSlots.size ≥ totalSlots
          if !prevDone && se.targets.size + se.skippedOptionalSlots.size ≥ totalSlots then
            some (ctrl, some obj, true, se.targets, uniquePermTargetsOn post se.targets)
          else if prevDone then
            let newTgts := se.targets.filter (!prevTargets.contains ·)
            let prevPermIds := (uniquePermTargetsOn post prevTargets).map (·.id)
            let newlyTargeted := (uniquePermTargetsOn post se.targets).filter (fun o => !prevPermIds.contains o.id)
            some (ctrl, some obj, true, newTgts, newlyTargeted)
          else none
        else if post.wasCast objId || !prevTargets.isEmpty then
          let newTgts := se.targets.filter (!prevTargets.contains ·)
          let prevPermIds := (uniquePermTargetsOn post prevTargets).map (·.id)
          let newlyTargeted := (uniquePermTargetsOn post se.targets).filter (fun o => !prevPermIds.contains o.id)
          some (ctrl, some obj, false, newTgts, newlyTargeted)
        else none
      | _, _ => none
  | _ => none

/-- Pattern family 5: cast spell, activate ability, and becomes-target triggers
(CR 601.2i / 602 / 603.2 / 605.1b). -/
@[noinline] private def matchCastAndTargetPattern (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (src : GameObject) (srcCtrl : PlayerId)
    (pat : TriggerPattern) (limit : TriggerLimit) : Array TriggerMatchPayload := Id.run do
  let mut hits : Array TriggerMatchPayload := #[]
  for eIdx in [0:batch.size] do
    let e := batch[eIdx]!
    match pat with
    | .castSpell caster spellPred fromZ? manaSpent? mustBePrepared nthFilter? targets? =>
      match e.change with
      | .rules (.cast (.spellCast spellSnap casterP evFrom)) =>
        if !(spellSnap.name.isEmpty && !spellSnap.faceDown) &&
            post.matchTriggerPlayerFilter src srcCtrl caster casterP then
          let castObj := findTriggerEventObj post spellSnap
          if !GameEvent.isUncastStackCopy post.events castObj.id &&
              post.evalTriggerPred src srcCtrl castObj spellPred then
            let fromOk :=
              fromZ?.all fun zk =>
                evFrom.kind == zk || (zk == .hand && post.castFromHand castObj.id)
            let manaOk :=
              manaSpent?.all fun mp =>
                post.evalStaticCastPred src (.manaSpentMatches mp .triggerSubject) (some castObj)
            let prepOk := !mustBePrepared || post.isPreparedSpell castObj.id
            let effNth? :=
              nthFilter?.orElse fun _ =>
                match limit with | .nthEachTurn n => some n | _ => none
            let nthOk :=
              match effNth? with
              | none => true
              | some n =>
                if spellPred == .anyObject then post.loggedSpellsCast casterP == n
                else if spellPred == .not (.hasType .creature) then
                  post.loggedNoncreatureSpells casterP == n
                else
                  let cnt := post.events.foldl (fun acc ev =>
                    if ev.turn != post.turnNumber then acc
                    else match ev.change with
                      | .rules (.cast (.spellCast eo q _)) =>
                        if q == casterP &&
                            post.evalTriggerPred src srcCtrl (lkiEventObjectAsGameObject eo) spellPred then
                          acc + 1
                        else acc
                      | _ => acc) 0
                  cnt == n
            let tgtOk :=
              targets?.all fun rf =>
                let tgts := ((post.stackEntry? castObj.id).map (·.targets)).getD #[]
                tgts.any (targetMatchesRecipient post src srcCtrl · rf)
            if fromOk && manaOk && prepOk && nthOk && tgtOk then
              let lkp := if post.isCreature castObj then some (Int.ofNat spellSnap.manaValue) else none
              hits := hits.push {
                eventIdx := eIdx, cause := some castObj, causeController := some casterP,
                lastKnownPower := lkp, groupPlayer? := some casterP,
                groupSourceId? := some castObj.id }
      | _ => pure ()
    | .activateAbility activator sourcePred kind =>
      match e.change with
      | .rules (.cast (.abilityActivated _ sourceSnap ctrl actKind)) =>
        if post.matchTriggerPlayerFilter src srcCtrl activator ctrl then
          let actSrc := (sourceSnap.id.bind post.findLiveSourceObject?).getD (damageSourceObjectFromLki sourceSnap)
          let (kindOk, lkp) : Bool × Option Int :=
            match kind, actKind with
            | .any, _ => (true, none)
            | .manaAbility, .mana .. => (true, none)
            | .nonMana, .nonMana .. => (true, none)
            | .loyalty minRem, .nonMana (some k) .. =>
              let removed := if k < 0 then (-k).toNat else 0
              (removed ≥ minRem, if minRem > 0 then some (Int.ofNat removed) else none)
            | _, _ => (false, none)
          if kindOk && post.evalTriggerPred src srcCtrl actSrc sourcePred then
            hits := hits.push {
              eventIdx := eIdx, cause := some actSrc, causeController := some ctrl,
              lastKnownPower := lkp, groupPlayer? := some ctrl,
              groupSourceId? := some actSrc.id }
      | _ => pure ()
    | .becomesTarget subjFilter byCtrl srcKind =>
      match extractTargetingInfo pre post e with
      | some (actor, causeObj?, isAbility, activeTgts, permTgts) =>
        let kindOk :=
          match srcKind with
          | .spellOrAbility => true
          | .spell => !isAbility
          | .ability => isAbility
        if kindOk && post.matchTriggerPlayerFilter src srcCtrl byCtrl actor then
          match subjFilter with
          | .playerOrPermanent =>
            let isPlayerOrPerm (t : Target) : Bool :=
              match t with
              | .player pid => post.stillInGame pid
              | .permanent oid => (post.findObject? oid).any (·.isOnBattlefield)
              | _ => false
            if activeTgts.any isPlayerOrPerm then
              hits := hits.push {
                eventIdx := eIdx, cause := causeObj?, causeController := some actor,
                groupPlayer? := some actor }
          | .object pred =>
            for o in permTgts do
              if post.evalTriggerPred src srcCtrl o pred then
                hits := hits.push {
                  eventIdx := eIdx, cause := causeObj?, causeController := some actor,
                  groupSourceId? := some o.id }
      | none => pure ()
    | _ => pure ()
  return hits

/-- Pattern family 6: player actions, step beginnings, stack-object resolutions,
and ability-triggers-ability (CR 500 / 603.1 / 603.3b / 603.10f). -/
@[noinline] private def matchStepAndMiscPattern (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (src : GameObject) (srcCtrl : PlayerId)
    (pat : TriggerPattern) : Array TriggerMatchPayload := Id.run do
  let mut hits : Array TriggerMatchPayload := #[]
  for eIdx in [0:batch.size] do
    let e := batch[eIdx]!
    match pat, e.change with
    | .playerAction who .scry, .rules (.player (.scried p _ _ lookedAt _)) =>
      if post.matchTriggerPlayerFilter src srcCtrl who p then
        hits := hits.push {
          eventIdx := eIdx, causeController := some p,
          lastKnownPower := some (Int.ofNat lookedAt), groupPlayer? := some p }
    | .playerAction who .surveil, .rules (.player (.surveilled p _ _ _ _)) =>
      if post.matchTriggerPlayerFilter src srcCtrl who p then
        hits := hits.push { eventIdx := eIdx, causeController := some p, groupPlayer? := some p }
    | .playerAction who .proliferate, .rules (.player (.proliferated p _ _)) =>
      if post.matchTriggerPlayerFilter src srcCtrl who p then
        hits := hits.push { eventIdx := eIdx, causeController := some p, groupPlayer? := some p }
    | .playerAction who .ringTempts, .rules (.player (.ringTempted p _ _)) =>
      if post.matchTriggerPlayerFilter src srcCtrl who p then
        hits := hits.push { eventIdx := eIdx, causeController := some p, groupPlayer? := some p }
    | .playerAction who .chooseRingBearer, .rules (.player (.ringTempted p (some _) _)) =>
      if post.matchTriggerPlayerFilter src srcCtrl who p then
        hits := hits.push { eventIdx := eIdx, causeController := some p, groupPlayer? := some p }
    | .playerAction who .manaAdded, .rules (.player (.manaAdded p units)) =>
      if !units.isEmpty && post.matchTriggerPlayerFilter src srcCtrl who p then
        hits := hits.push { eventIdx := eIdx, causeController := some p, groupPlayer? := some p }
    | .playerAction who .losesGame, .rules (.player (.lost p _)) =>
      -- CR 603.10f: look-back on `pre` where the losing player is still in the game.
      if pre.matchTriggerPlayerFilter src srcCtrl who p then
        hits := hits.push { eventIdx := eIdx, causeController := some p, groupPlayer? := some p }
    | .stepBegins step whoseTurn, .rules (.turn (.stepBegan evStep ap)) =>
      if evStep == step then
        let seatOk : Bool :=
          match step with
          | .upkeep | .draw | .precombatMain => post.isSharedTurnFirstSeat
          | .beginningOfCombat =>
            let isExtraCombat :=
              (post.events.reverse.findSome? fun ev =>
                match ev.change with
                | .rules (.turn (.phaseEnded .combat)) => some true
                | .rules (.turn (.turnBegan _ _)) => some false
                | _ => none).getD false
            post.isSharedTurnFirstSeat || isExtraCombat
          | .end => post.isSharedTurnFinalSeat
          | _ => true
        if seatOk then
          let ownerOk : Bool :=
            match whoseTurn with
            | .player pf =>
              (post.teamMembers ap).any fun m =>
                post.stillInGame m && post.matchTriggerPlayerFilter src srcCtrl pf m
            | .controllerOf oe =>
              let objs := post.evalStaticObjsFull src srcCtrl oe
              objs.any fun host =>
                (post.teamMembers ap).any fun m => post.stillInGame m && post.controlledBy host m
          if ownerOk then
            hits := hits.push { eventIdx := eIdx, causeController := some ap, groupPlayer? := some ap }
    | .stackObjectResolves pred finalSagaOnly, .rules (.stackObject (.resolved obj nth _ _)) =>
      if (!finalSagaOnly || (nth == 0 && obj.types.isEmpty && obj.hasSubtype .saga)) &&
          post.evalTriggerPred src srcCtrl (lkiEventObjectAsGameObject obj) pred then
        hits := hits.push {
          eventIdx := eIdx, cause := some (lkiEventObjectAsGameObject obj),
          causeController := obj.controller, groupSourceId? := obj.id }
    | .abilityTriggers sourcePred, .rules (.triggerQueue (.triggered srcSnap _ _ _)) =>
      let tSrc := findTriggerEventObj post srcSnap
      if post.evalTriggerPred src srcCtrl tSrc sourcePred then
        hits := hits.push {
          eventIdx := eIdx, cause := some tSrc, causeController := srcSnap.controller,
          groupSourceId? := some tSrc.id }
    | _, _ => pure ()
  return hits

/-- Dispatch one atomic (non-`.or`, non-`.whenCond`) `TriggerPattern` over `batch`,
applying `ab.grouping` for families that do not self-aggregate. -/
@[noinline] private def matchAtomicPattern (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (board : Game) (src : GameObject) (srcCtrl : PlayerId)
    (ab : TriggeredAbility) (pat : TriggerPattern)
    (controlLostList : Array (GameObject × PlayerId)) : Array TriggerMatchPayload :=
  match pat with
  | .zoneChange .. | .createTokens .. | .sacrifice ..
  | .drawCard .. | .discard .. | .spellCountered .. =>
    applyBatchGrouping ab.grouping
      (matchZoneAndResourcePattern pre post batch board src srcCtrl ab.grouping pat ab.limit)
  | .becomesTapped .. | .becomesUntapped .. | .phasesOut ..
  | .becomesUnattached .. | .controlLost .. | .putCounters .. =>
    applyBatchGrouping ab.grouping
      (matchPermanentStatePattern pre post batch board src srcCtrl ab pat controlLostList)
  | .attacks .. | .blocks .. | .becomesBlocked .. =>
    -- `.attacks` already implements `.perPlayerInBatch` / `.oncePerBatch` / `.perOccurrence`.
    match pat with
    | .attacks .. => matchCombatPattern post batch src srcCtrl ab.grouping pat
    | _ => applyBatchGrouping ab.grouping (matchCombatPattern post batch src srcCtrl ab.grouping pat)
  | .damageDealt .. | .gainLife .. | .loseLife .. =>
    -- `.damageDealt` already implements `.oncePerBatch` / `.perPlayerInBatch` / `.perSourceInBatch` with summed amounts.
    match pat with
    | .damageDealt .. => matchDamageAndLifePattern pre post batch src srcCtrl ab.grouping pat
    | _ => applyBatchGrouping ab.grouping (matchDamageAndLifePattern pre post batch src srcCtrl ab.grouping pat)
  | .castSpell .. | .activateAbility .. | .becomesTarget .. =>
    applyBatchGrouping ab.grouping
      (matchCastAndTargetPattern pre post batch src srcCtrl pat ab.limit)
  | .playerAction .. | .stepBegins .. | .stackObjectResolves .. | .abilityTriggers .. =>
    applyBatchGrouping ab.grouping
      (matchStepAndMiscPattern pre post batch src srcCtrl pat)
  | .whenCond .. | .or .. => #[]

/-- Queue one matched trigger onto `(waiting, firedSources)`, checking CR 800.4d,
CR 603.2 `whenCond?`, CR 603.4 `interveningIf?`, CR 603.2h per-turn caps,
CR 603.2d `extraTriggerCopies`, and Windcrag Siege Mardu attack doubling. -/
@[noinline] private def queueTriggerAb (post : Game) (board : Game) (controller : PlayerId)
    (source : GameObject) (ab : TriggeredAbility) (matchedPat : TriggerPattern)
    (whenConds : Array Condition := #[])
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) (causeController : Option PlayerId := none)
    (eventCause : Option EventCause := none) (causeIds : Array ObjectId := #[])
    (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
    Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
  if !post.stillInGame controller then (w, fs)
  else if !whenConds.all (board.evalTriggerCond controller (some source) cause ·) then (w, fs)
  else if !board.triggerConditionHolds controller ab cause (some source) then (w, fs)
  else if ab.onceEachTurn &&
      (post.loggedTriggeredThisTurn source.id ab ||
        fs.any (fun (sid, a) => sid == source.id && a == ab)) then (w, fs)
  else if ab.optionalOnceEachTurn && post.optionalOnceUsedThisTurn source.id then (w, fs)
  else
    let fs := if ab.onceEachTurn then fs.push (source.id, ab) else fs
    let mardu :=
      if matchedPat.isAttackTrigger && source.isOnBattlefield &&
          (board.permanentsOf controller).any (fun o =>
            (board.staticAbilities o).any (fun sa =>
              sa.anyReplacement fun _ sp =>
                match sp with
                | .asEntersChoose (.namedAnchors opts) => opts.contains "Mardu"
                | _ => false) &&
              o.status.chosenAnchor == some "Mardu") then 1 else 0
    let curSource :=
      if source.isLkiSnapshot || board.findObject? source.id == some source then source
      else
        ((post.findObject? source.id).filter fun o =>
          !(o.zone == .battlefield && o.status.phasedOut && !source.status.phasedOut)).getD source
    let copies := board.extraTriggerCopies controller source + 1 + mardu
    let wt : WaitingTrigger :=
      { controller, source := curSource, ability := ab, pattern := matchedPat,
        lastKnownPower, lastKnownToughness,
        causeId := cause.map (·.id), causeIds, cause, causeController,
        checked := true, eventCause }
    (w ++ Array.replicate copies wt, fs)

/-- Built-in keyword, rule, reflexive, and delayed triggers that are not printed
entries in `CardDef.triggeredAbilities` (Monarch CR 726, Ward CR 702.21,
Cascade CR 702.85, Extort CR 702.101, Photon Blast Barrage copy-self, Bolg
reflexive sacrifice CR 603.12, and `post.delayedTriggers` CR 603.7). -/
@[noinline] private def matchBuiltinAndDelayedTriggers (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (mask : BatchEventMask)
    (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
    Array WaitingTrigger × Array (ObjectId × TriggeredAbility) := Id.run do
  let mut waiting := w
  let mut firedSources := fs
  let queueWardsFor (actor : PlayerId) (stackObj : GameObject) (perms : Array GameObject)
      (w : Array WaitingTrigger) (fs : Array (ObjectId × TriggeredAbility)) :
      Array WaitingTrigger × Array (ObjectId × TriggeredAbility) :=
    perms.foldl (fun (w, fs) o =>
      match post.controllerOf o with
      | some c =>
        if o.isOnBattlefield && c != actor && !post.areTeammates c actor then
          (post.wardCostsOn o).foldl (fun (w, fs) cost =>
            let ab := TriggeredAbility.onWard cost
            queueTriggerAb post post c o ab ab.pattern
              (cause := some stackObj) (causeController := some actor) (w := w) (fs := fs)) (w, fs)
        else (w, fs)
      | none => (w, fs)) (w, fs)
  -- Inherent monarch combat-damage trigger (CR 726.2–3 / 113.8 / 800.4a,d).
  if mask.hasDamage then
    if let some monarchPl := post.players.find? (fun pl => pl.isMonarch && post.stillInGame pl.id) then
      let attackers : Array (Option GameObject × Option ObjectId × PlayerId) :=
        batch.foldl (fun acc e =>
          match e.change with
          | .rules (.damage (.dealt pkts)) =>
            pkts.foldl (fun acc pkt =>
              if pkt.combat && pkt.amount > 0 && pkt.recipient == .player monarchPl.id then
                let srcPost? := pkt.source.id.bind post.findObject?
                let srcPre? := pkt.source.id.bind pre.findObject?
                let srcObj? : Option GameObject :=
                  match srcPost? with
                  | some so => if so.isOnBattlefield then some so else srcPre?.orElse (fun _ => some so)
                  | none => srcPre?
                let wasCreature :=
                  pkt.source.creature ||
                    (pkt.source.types.isEmpty &&
                      match srcPost?, srcPre? with
                      | some so, _ =>
                        if so.isOnBattlefield then post.isCreature so else srcPre?.any pre.isCreature
                      | none, some so => pre.isCreature so
                      | none, none => false)
                let ctrl? : Option PlayerId :=
                  pkt.source.controller.orElse fun _ =>
                    match srcPost? with
                    | some so =>
                      if so.isOnBattlefield then post.controllerOf so else srcPre?.bind pre.controllerOf
                    | none => srcPre?.bind pre.controllerOf
                match wasCreature, ctrl? with
                | true, some attCtrl =>
                  let sid? := (srcObj?.map (·.id)).orElse (fun _ => pkt.source.id)
                  if sid?.isSome && acc.any (fun (_, prevSid?, _) => prevSid? == sid?) then acc
                  else acc.push (srcObj?, sid?, attCtrl)
                | _, _ => acc
              else acc) acc
          | _ => acc) #[]
      if !attackers.isEmpty then
        let src : GameObject :=
          { printed := { name := "The monarch", types := #[] }
            id := noSourceSentinelId, owner := monarchPl.id,
            controller := some monarchPl.id, zone := .command }
        let ab : TriggeredAbility :=
          TriggeredAbility.ofPattern .combatDamageToYou
            (.player (.setStatus (.triggerPlayer .controllerOfSubject) .monarch))
        for (srcObj?, sid?, attCtrl) in attackers do
          waiting := waiting.push
            { controller := monarchPl.id, source := src, ability := ab,
              pattern := .combatDamageToYou,
              causeId := sid?, cause := srcObj?, causeController := some attCtrl,
              checked := true }
  for e in batch do
    match e.change with
    | .rules (.zone (.moved before _ .battlefield toZ .sacrifice _ _ _)) =>
      if toZ != .battlefield && !before.phasedOut then
        match pre.pending with
        | .maySacrificeAnotherBolg _ bolgId =>
          let beforeObj := findTriggerEventObj pre before
          let lkp : Option Int := some (pre.snapshotPower beforeObj)
          match (post.findObject? bolgId).map (post, ·) |>.orElse (fun _ => (pre.findObject? bolgId).map (pre, ·)) with
          | some (bolgBoard, bolg) =>
            if let some c := bolgBoard.controllerOf bolg then
              let ab : TriggeredAbility :=
                TriggeredAbility.mkTrigger .youSacrificeOtherCreature
                  { targets := .anotherCreature
                    body := .bind ⟨0⟩
                      (Instruction.dealDamage (.targetSlot 0) (.objectStat .power .triggerSubject)
                        .this { trackExcess := true })
                      (Instruction.ifThen (.cmp .gt (.stepMetric .excessDamage ⟨0⟩) (.const 0))
                        (Instruction.amass (.stepMetric .excessDamage ⟨0⟩) .goblin)) }
                  (word := .when)
              let (w, fs) :=
                queueTriggerAb post pre c bolg ab ab.pattern (lastKnownPower := lkp)
                  (w := waiting) (fs := firedSources)
              waiting := w; firedSources := fs
          | none => pure ()
        | _ => pure ()
    | .rules (.turn (.stepBegan step _)) =>
      match step with
      | .upkeep =>
        if post.isSharedTurnFirstSeat then
          for dt in post.delayedTriggers do
            if post.stillInGame dt.controller then
              match dt.kind with
              | .eaglesBirds n =>
                let src := dt.source.getD
                  { printed := { name := "The Eagles Are Coming!", types := #[.sorcery] }
                    id := noSourceSentinelId, owner := dt.controller,
                    controller := some dt.controller, zone := .exile }
                let ab : TriggeredAbility :=
                  TriggeredAbility.mkTrigger .stepEachUpkeep
                    { body := Instruction.createTokensFixed .birdSoldier n }
                waiting := waiting.push
                  { controller := dt.controller, source := src, ability := ab,
                    pattern := .stepEachUpkeep, eventCause := some dt.cause,
                    delayedTrigger := some (dt.kind, dt.cause), checked := true }
              | _ => pure ()
      | .end =>
        if post.isSharedTurnFinalSeat then
          -- Inherent monarch end-step draw trigger (CR 726.2 / 113.8 / 805.4).
          if let some monarchPl := post.players.find? (fun pl => pl.isMonarch && post.stillInGame pl.id) then
            if post.isOnActiveTeam monarchPl.id then
              let src : GameObject :=
                { printed := { name := "The monarch", types := #[] }
                  id := noSourceSentinelId, owner := monarchPl.id,
                  controller := some monarchPl.id, zone := .command }
              let ab : TriggeredAbility :=
                TriggeredAbility.ofPattern .stepYourEndStep
                  (Instruction.drawFixed 1 .you)
              waiting := waiting.push
                { controller := monarchPl.id, source := src, ability := ab,
                  pattern := .stepYourEndStep, checked := true }
          for dt in post.delayedTriggers do
            if post.stillInGame dt.controller then
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
                    id := noSourceSentinelId, owner := dt.controller,
                    controller := some dt.controller, zone := .exile }
                let ab : TriggeredAbility :=
                  TriggeredAbility.mkTrigger .stepEachEndStep { body := .noop }
                waiting := waiting.push
                  { controller := dt.controller, source := src, ability := ab,
                    pattern := .stepEachEndStep, eventCause := some dt.cause,
                    delayedTrigger := some (dt.kind, dt.cause), checked := true }
              | _ => pure ()
      | .endOfCombat =>
        for dt in post.delayedTriggers do
          if post.stillInGame dt.controller then
            match dt.kind with
            | .endOfCombatExile oid | .endOfCombatSacrifice oid =>
              let obj? := post.findObject? oid
              let src := (dt.source.orElse (fun _ => obj?)).getD
                { printed := { name := "Delayed Trigger", types := #[] }
                  id := noSourceSentinelId, owner := dt.controller,
                  controller := some dt.controller, zone := .exile }
              let pat : TriggerPattern := .stepBegins .endOfCombat (.player .any)
              let ab : TriggeredAbility := TriggeredAbility.mkTrigger pat { body := .noop }
              waiting := waiting.push
                { controller := dt.controller, source := src, ability := ab,
                  pattern := pat, eventCause := some dt.cause,
                  delayedTrigger := some (dt.kind, dt.cause), checked := true }
            | _ => pure ()
      | _ => pure ()
    | .rules (.combat (.attackersDeclared activePlayer decls)) =>
      let attackers := (decls.filterMap (·.1.id)).filterMap post.findObject?
      if !attackers.isEmpty then
        for m in post.teamMembers activePlayer do
          if post.stillInGame m && attackers.any (post.controlledBy · m) then
            for dt in post.delayedTriggers do
              if dt.kind == .attackPumpPerPlains && dt.controller == m && post.stillInGame dt.controller then
                let src := dt.source.getD
                  { printed := { name := "Roads Go Ever, Ever On", types := #[.enchantment], subtypes := #["Saga"] }
                    id := noSourceSentinelId, owner := m, controller := some m, zone := .graveyard m }
                let plainsCount :=
                  ValueExpr.count (.inZones .battlefield (.all #[.hasSubtype (.literal .plains), .controlledBy .you]))
                let ab : TriggeredAbility :=
                  TriggeredAbility.mkTrigger .youAttack
                    { targets := .creatureYouControl
                      body := Instruction.pump (.target 0) plainsCount plainsCount }
                    (grouping := .oncePerBatch)
                waiting := waiting.push
                  { controller := m, source := src,
                    ability := ab, pattern := .youAttack,
                    eventCause := some dt.cause,
                    delayedTrigger := some (dt.kind, dt.cause), checked := true }
    | .rules (.cast (.spellCast spellSnap caster _)) =>
      if !(spellSnap.name.isEmpty && !spellSnap.faceDown) then
        let castObj := findTriggerEventObj post spellSnap
        let targets := ((post.stackEntry? castObj.id).map (·.targets)).getD #[]
        let uniquePerm := uniquePermTargetsOn post targets
        -- Cascade (CR 702.85a–b)
        for _ in [0:KeywordAbility.cascadeCount (post.currentKeywords castObj)] do
          let (w, fs) :=
            queueTriggerAb post post caster castObj .onCastCascade .thisCast
              (w := waiting) (fs := firedSources)
          waiting := w; firedSources := fs
        -- Ward (CR 702.21a)
        let (w, fs) := queueWardsFor caster castObj uniquePerm waiting firedSources
        waiting := w; firedSources := fs
        -- Delayed spell-copy triggers (Way of the Cryomancer & Loki Laufeyson)
        let isUncastCopy := GameEvent.isUncastStackCopy post.events castObj.id
        let mvCast := spellSnap.manaValue
        if !isUncastCopy && post.isInstantOrSorcery castObj then
          for dt in post.delayedTriggers do
            if dt.controller == caster && post.stillInGame dt.controller then
              match dt.kind with
              | .copyNextInstantSorceryThisTurn =>
                let src := dt.source.getD
                  { printed := { name := "Way of the Cryomancer", types := #[.sorcery] }
                    id := noSourceSentinelId, owner := dt.controller,
                    controller := some dt.controller, zone := .exile }
                let ab : TriggeredAbility :=
                  TriggeredAbility.mkTrigger .youCastInstantOrSorcery
                    { body := .stack (.copyStackObject .triggerSubject (.const 1) true) }
                waiting := waiting.push
                  { controller := dt.controller, source := src, ability := ab,
                    pattern := .youCastInstantOrSorcery,
                    cause := some castObj, causeId := some castObj.id,
                    eventCause := some dt.cause,
                    delayedTrigger := some (dt.kind, dt.cause), checked := true }
              | .lokiCopyNextInstantSorceryThisTurn srcId? fallbackPw =>
                let lokiPw : Int :=
                  match srcId? with
                  | some lid =>
                    match post.findObject? lid with
                    | some o =>
                      if o.isOnBattlefield then post.power o
                      else ((post.lastKnownBefore? lid).bind (·.power)).getD fallbackPw
                    | none => ((post.lastKnownBefore? lid).bind (·.power)).getD fallbackPw
                  | none => fallbackPw
                if (mvCast : Int) ≤ lokiPw then
                  let src := (srcId?.bind post.findObject?).orElse (fun _ => dt.source) |>.getD
                    { printed := { name := "Loki Laufeyson", types := #[.creature] }
                      id := srcId?.getD noSourceSentinelId, owner := dt.controller,
                      controller := some dt.controller, zone := .exile }
                  let ab : TriggeredAbility :=
                    TriggeredAbility.mkTrigger .youCastInstantOrSorcery
                      { body := .stack (.copyStackObject .triggerSubject (.const 1) true) }
                  waiting := waiting.push
                    { controller := dt.controller, source := src, ability := ab,
                      pattern := .youCastInstantOrSorcery,
                      cause := some castObj, causeId := some castObj.id,
                      eventCause := some dt.cause,
                      delayedTrigger := some (dt.kind, dt.cause), checked := true }
              | _ => pure ()
        -- Extort (CR 702.101a–b)
        for o in post.permanentsOf caster do
          let extortCnt := KeywordAbility.countSimple (post.currentKeywords o) .extort
          if extortCnt > 0 then
            let extortAbs := (KeywordAbility.expand (.simple .extort)).triggeredAbilities
            for _ in [0:extortCnt] do
              for extortAb in extortAbs do
                let (w, fs) :=
                  queueTriggerAb post post caster o extortAb .youCastSpell
                    (w := waiting) (fs := firedSources)
                waiting := w; firedSources := fs
    | .rules (.cast (.abilityActivated abilityId _ ctrl (.nonMana ..))) =>
      let targets := ((post.stackEntry? abilityId).map (·.targets)).getD #[]
      if let some abObj := post.findObject? abilityId then
        let (w, fs) := queueWardsFor ctrl abObj (uniquePermTargetsOn post targets) waiting firedSources
        waiting := w; firedSources := fs
    | .rules (.cast (.targeted ..)) =>
      if let some (actor, some obj, _, _, permTgts) := extractTargetingInfo pre post e then
        let (w, fs) := queueWardsFor actor obj permTgts waiting firedSources
        waiting := w; firedSources := fs
    | _ => pure ()
  return (waiting, firedSources)

/-- Collect candidate `(source, controller, boardForSrc, wasDiscardedFromHand)` tuples
for one pass (`lookBackPass = true` on `pre`, `false` on `post`). -/
@[noinline] private def collectTriggerCandidates (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) (lookBackPass : Bool) :
    Array (GameObject × PlayerId × Game × Bool) := Id.run do
  let board : Game := if lookBackPass then pre else post
  let mut out : Array (GameObject × PlayerId × Game × Bool) := #[]
  let mut seen : Array ObjectId := #[]
  let addCand (o : GameObject) (ctrl : PlayerId) (b : Game) (fromDisc : Bool := false)
      (acc : Array (GameObject × PlayerId × Game × Bool)) (s : Array ObjectId) :=
    if !post.stillInGame ctrl || s.contains o.id then (acc, s)
    else (acc.push (o, ctrl, b, fromDisc), s.push o.id)
  -- 1. Live battlefield permanents + emblems/commanders + active non-battlefield zones
  for o in board.objects do
    match o.zone with
    | .battlefield =>
      if !o.status.phasedOut then
        if let some ctrl := board.controllerOf o then
          let (o', s') := addCand o ctrl board false out seen
          out := o'; seen := s'
    | .command =>
      let isEmblem := (board.baseCard o).types.isEmpty
      if isEmblem then
        if let some ctrl := board.controllerOf o then
          let (o', s') := addCand o ctrl board false out seen
          out := o'; seen := s'
      else if (board.triggeredAbilities o).any (·.activeZones.contains .command) then
        let (o', s') := addCand o o.owner board false out seen
        out := o'; seen := s'
    | .stack =>
      if (board.triggeredAbilities o).any (·.activeZones.contains .stack) then
        let ctrl := ((board.stackEntry? o.id).map (·.controller)).orElse (fun _ => o.controller) |>.getD o.owner
        let (o', s') := addCand o ctrl board false out seen
        out := o'; seen := s'
    | .graveyard p =>
      if (board.triggeredAbilities o).any (·.activeZones.contains .graveyard) then
        let (o', s') := addCand o p board false out seen
        out := o'; seen := s'
    | .exile =>
      if (board.triggeredAbilities o).any (·.activeZones.contains .exile) then
        let ctrl := o.controller.getD o.owner
        let (o', s') := addCand o ctrl board false out seen
        out := o'; seen := s'
    | .hand p =>
      if (board.triggeredAbilities o).any (·.activeZones.contains .hand) then
        let (o', s') := addCand o p board false out seen
        out := o'; seen := s'
    | .library _ | .ante | .outside _ => pure ()
  -- 2. Ephemeral batch snapshots for objects that changed zones during `batch`
  if lookBackPass then
    for e in batch do
      match e.change with
      | .rules (.zone (.moved before _ .battlefield toZ ..)) =>
        if toZ != .battlefield && !before.phasedOut then
          let bObj := findTriggerEventObj pre before
          let ctrl := (before.controller.orElse (fun _ => pre.controllerOf bObj)).getD before.owner
          let (o', s') := addCand bObj ctrl pre false out seen
          out := o'; seen := s'
      | .rules (.zone (.moved before _ .stack toZ .counter _ _ _)) =>
        if toZ != .stack then
          let bObj := findTriggerEventObj pre before
          let ctrl :=
            (before.controller.orElse (fun _ =>
              (pre.stackEntry? bObj.id).map (·.controller))).orElse
              (fun _ => pre.controllerOf bObj) |>.getD before.owner
          if (pre.triggeredAbilities bObj).any (·.activeZones.contains .stack) then
            let (o', s') := addCand bObj ctrl pre false out seen
            out := o'; seen := s'
      | .rules (.zone (.ceasedToExist snap)) =>
        if snap.zone == .battlefield && !snap.phasedOut then
          let bObj := findTriggerEventObj pre snap
          let ctrl := (snap.controller.orElse (fun _ => pre.controllerOf bObj)).getD snap.owner
          let (o', s') := addCand bObj ctrl pre false out seen
          out := o'; seen := s'
      | _ => pure ()
  else
    for eIdx in [0:batch.size] do
      let e := batch[eIdx]!
      for (eo, _, n, _) in e.countersPutInEvent do
        if n > 0 && eo.zone == .battlefield && !eo.phasedOut && !eo.faceDown && isFullEventSnapshot eo then
          let obj := damageSourceObjectFromLki eo
          let ctrl := eo.controller.getD eo.owner
          let (o', s') := addCand obj ctrl post false out seen
          out := o'; seen := s'
      match e.change with
      | .rules (.zone (.created obj ctrl)) =>
        if obj.zone == .battlefield && !obj.phasedOut then
          let enterCtrl := obj.controller.getD ctrl
          let entered := findTriggerEventObj post { obj with controller := some enterCtrl }
          let (o', s') := addCand entered enterCtrl post false out seen
          out := o'; seen := s'
      | .rules (.zone (.moved _ after fromZ toZ verb _ _ _)) =>
        if fromZ != .battlefield && toZ == .battlefield && !after.phasedOut then
          let entered := findTriggerEventObj post after
          let p := (after.controller.orElse (fun _ => post.controllerOf entered)).getD entered.owner
          let (o', s') := addCand entered p post false out seen
          out := o'; seen := s'
        match fromZ with
        | .hand handP =>
          if toZ != .hand handP && verb == .discard then
            let afterObj := findTriggerEventObj post after
            if (post.triggeredAbilities afterObj).any (·.activeZones.contains .hand) then
              -- Allow discarded-from-hand card even if already seen in graveyard (with `fromDisc := true`)
              out := out.push (afterObj, handP, post, true)
        | _ => pure ()
      | .rules (.damage (.dealt pkts)) =>
        for pkt in pkts do
          if pkt.amount > 0 then
            let ds := resolveTriggerDamageSrc pre post pkt.source
            let dsCtrl := pkt.source.controller.orElse (fun _ => post.controllerOf ds) |>.getD ds.owner
            let dsBoard := if (post.findObject? ds.id).any (·.isOnBattlefield) then post else pre
            let (o', s') := addCand ds dsCtrl dsBoard false out seen
            out := o'; seen := s'
            match pkt.recipient with
            | .permanent recSnap =>
              let ro := findTriggerEventObj post recSnap
              let roCtrl := (post.controllerOf ro).orElse (fun _ => recSnap.controller) |>.getD ro.owner
              let (o', s') := addCand ro roCtrl post false out seen
              out := o'; seen := s'
            | _ => pure ()
      | .rules (.permanent (.tapped obj _)) =>
        if !obj.phasedOut then
          let tObj := findTriggerEventObj post obj
          -- CR 603.2e / 400.7: `becomesTapped` is NOT a look-back trigger; if the tapped permanent
          -- also left the battlefield in the same batch (taking a new ObjectId so `post.findObject?`
          -- is `none` while `pre.findObject?` was `some`), its own trigger is absent on `post`.
          let stillLiveOrSynthetic :=
            match obj.id with
            | none => true
            | some oid =>
              match post.findObject? oid with
              | some live => live.isOnBattlefield
              | none => (pre.findObject? oid).isNone
          if stillLiveOrSynthetic then
            if let some p := (post.controllerOf tObj).orElse (fun _ => obj.controller) then
              let (o', s') := addCand tObj p post false out seen
              out := o'; seen := s'
          -- Equipment attached to `tObj` on `pre` that unattached/left AFTER the tap in `batch`
          let postLiveEqs := (post.attachmentsOf tObj).filter (·.isOnBattlefield)
          let detachedBeforeTap (eqId : ObjectId) : Bool :=
            (batch.extract 0 eIdx).any fun prevEv =>
              match prevEv.change with
              | .rules (.permanent (.unattached att _)) => att.id == some eqId
              | .rules (.permanent (.attached att newHost _)) =>
                att.id == some eqId && newHost != tObj.id
              | .rules (.permanent (.phasedOut b _)) => b.id == some eqId
              | .rules (.zone (.moved b _ .battlefield toZ ..)) =>
                b.id == some eqId && toZ != .battlefield
              | .rules (.zone (.ceasedToExist b)) => b.id == some eqId
              | _ => false
          for eq in (pre.attachmentsOf tObj).filter (·.isOnBattlefield) do
            if !postLiveEqs.any (·.id == eq.id) && !detachedBeforeTap eq.id && pre.isEquipment eq then
              if let some eqCtrl := pre.controllerOf eq then
                let (o', s') := addCand eq eqCtrl pre false out seen
                out := o'; seen := s'
      | _ => pure ()
  return out

/-- Per-`(source, occurrenceIndex, ability)` deduplication state shared across
both the CR 603.10a–f look-back pass (`pre`) and the non-look-back pass (`post`)
so `.or` disjunctions whose branches disagree on `usesLookBack` still honor
CR 603.2c single-event deduplication and CR 700.1 `BatchGrouping` (`oncePerBatch`,
`perPlayerInBatch`, `perSourceInBatch`). -/
private structure TriggerDedupState where
  matchedEventIdxs : Array Nat := #[]
  firedOnce : Bool := false
  firedPlayers : Array PlayerId := #[]
  firedSources : Array ObjectId := #[]
deriving Inhabited

/-- Match all triggered abilities over a committed batch of simultaneous rules
events (CR 603.2 / 603.2c / 603.10 / 603.10a–f / 700.1 / 715.2b). Look-back
disjuncts (`TriggerPattern.usesLookBack`) consult `pre`; all other disjuncts
consult `post` (CR 603.10). -/
def matchTriggers (pre : GameSnapshot) (post : Game)
    (batch : Array GameEvent) : Array WaitingTrigger :=
  if batch.isEmpty then #[]
  else Id.run do
    -- Detect CR 603.10d control losses once across `pre.battlefield`.
    let controlLostList : Array (GameObject × PlayerId) :=
      pre.battlefield.filterMap fun o =>
        match pre.controllerOf o with
        | some oldCtrl =>
          match post.findObject? o.id with
          | some cur =>
            if cur.isOnBattlefield && post.controllerOf cur != some oldCtrl then
              some (o, oldCtrl)
            else none
          | none => none
        | none => none
    let mask := BatchEventMask.ofBatch batch (!controlLostList.isEmpty)
    let mut waiting : Array WaitingTrigger := #[]
    let mut firedSources : Array (ObjectId × TriggeredAbility) := #[]
    let mut dedupStates : Array ((ObjectId × Nat × TriggeredAbility) × TriggerDedupState) := #[]
    let runPass (lookBackPass : Bool)
        (w0 : Array WaitingTrigger)
        (fs0 : Array (ObjectId × TriggeredAbility))
        (ds0 : Array ((ObjectId × Nat × TriggeredAbility) × TriggerDedupState)) :
        Array WaitingTrigger × Array (ObjectId × TriggeredAbility) ×
          Array ((ObjectId × Nat × TriggeredAbility) × TriggerDedupState) := Id.run do
      let mut w := w0
      let mut fs := fs0
      let mut ds := ds0
      let cands := collectTriggerCandidates pre post batch lookBackPass
      for (src, ctrl, srcBoard, fromDisc) in cands do
        let baseAbs := srcBoard.triggeredAbilities src
        let abs :=
          if !lookBackPass && mask.hasCast && src.isOnBattlefield then
            baseAbs ++ srcBoard.prowessTriggers src
          else baseAbs
        if !abs.isEmpty then
          let isEmblem := src.zone == .command && (srcBoard.baseCard src).types.isEmpty
          let srcZoneKind : ZoneKind := if isEmblem then .battlefield else src.zone.kind
          let mut seenAbCounts : Array (TriggeredAbility × Nat) := #[]
          for ab in abs do
            let mut occIdx : Nat := 0
            match seenAbCounts.findIdx? (fun (a, _) => a == ab) with
            | some idx =>
              let (_, c) := seenAbCounts[idx]!
              seenAbCounts := seenAbCounts.set! idx (ab, c + 1)
              occIdx := c
            | none =>
              seenAbCounts := seenAbCounts.push (ab, 1)
            -- Path of Ancestry's mana-spent cast trigger is evaluated by `Casting.lean`
            -- via `ancestryManaSpentOn` (CR 106.6 / 608.2h).
            if !ab.isManaSpentCastScry then
              let zoneOk :=
                if fromDisc then ab.activeZones.contains .hand
                else ab.activeZones.contains srcZoneKind
              if zoneOk then
                let disjuncts := ab.pattern.flattenDisjuncts
                let isMultiDisj := disjuncts.size > 1
                let key : ObjectId × Nat × TriggeredAbility := (src.id, occIdx, ab)
                let mut st : TriggerDedupState :=
                  if !isMultiDisj then {}
                  else
                    match ds.find? (fun (k, _) => k == key) with
                    | some (_, s) => s
                    | none => {}
                let mut stDirty := false
                for (atomicPat, whenConds) in disjuncts do
                  if atomicPat.usesLookBack == lookBackPass && patternCouldMatchMask mask atomicPat then
                    let hits :=
                      matchAtomicPattern pre post batch srcBoard src ctrl ab atomicPat controlLostList
                    let mut disjMatchedIdxs : Array Nat := #[]
                    let mut disjPlayers : Array PlayerId := #[]
                    let mut disjSources : Array ObjectId := #[]
                    let mut disjFired := false
                    for h in hits do
                      let hitPlayer? := h.groupPlayer?.orElse (fun _ => h.causeController)
                      let hitSource? := h.groupSourceId?.orElse (fun _ => h.cause.map (·.id))
                      let dupForOr :=
                        if !isMultiDisj then false
                        else
                          match ab.grouping with
                          | .oncePerBatch => st.firedOnce
                          | .perPlayerInBatch =>
                            match hitPlayer? with
                            | some pid => st.firedPlayers.contains pid
                            | none => st.matchedEventIdxs.contains h.eventIdx && h.overrideAbility.isNone
                          | .perSourceInBatch =>
                            match hitSource? with
                            | some sid => st.firedSources.contains sid
                            | none => st.matchedEventIdxs.contains h.eventIdx && h.overrideAbility.isNone
                          | .perOccurrence | .counterThreshold .. =>
                            st.matchedEventIdxs.contains h.eventIdx && h.overrideAbility.isNone
                      if !dupForOr then
                        let abToQueue := h.overrideAbility.getD ab
                        let prevLen := w.size
                        let (w', fs') :=
                          queueTriggerAb post srcBoard ctrl src abToQueue atomicPat whenConds
                            (lastKnownPower := h.lastKnownPower)
                            (lastKnownToughness := h.lastKnownToughness)
                            (cause := h.cause)
                            (causeController := h.causeController)
                            (eventCause := h.eventCause)
                            (causeIds := h.causeIds)
                            (w := w) (fs := fs)
                        w := w'; fs := fs'
                        if w.size > prevLen then
                          if !disjMatchedIdxs.contains h.eventIdx then
                            disjMatchedIdxs := disjMatchedIdxs.push h.eventIdx
                          if let some pid := hitPlayer? then
                            if !disjPlayers.contains pid then
                              disjPlayers := disjPlayers.push pid
                          if let some sid := hitSource? then
                            if !disjSources.contains sid then
                              disjSources := disjSources.push sid
                          disjFired := true
                    if disjFired && isMultiDisj then
                      let mut idxs := st.matchedEventIdxs
                      for idx in disjMatchedIdxs do
                        if !idxs.contains idx then idxs := idxs.push idx
                      let mut pls := st.firedPlayers
                      for pid in disjPlayers do
                        if !pls.contains pid then pls := pls.push pid
                      let mut srcs := st.firedSources
                      for sid in disjSources do
                        if !srcs.contains sid then srcs := srcs.push sid
                      st := {
                        matchedEventIdxs := idxs
                        firedOnce := true
                        firedPlayers := pls
                        firedSources := srcs
                      }
                      stDirty := true
                if stDirty && isMultiDisj then
                  match ds.findIdx? (fun (k, _) => k == key) with
                  | some idx => ds := ds.set! idx (key, st)
                  | none => ds := ds.push (key, st)
      return (w, fs, ds)
    -- Pass A: CR 603.10a–f look-back disjuncts evaluated against `pre`.
    let (wA, fsA, dsA) := runPass true waiting firedSources dedupStates
    waiting := wA; firedSources := fsA; dedupStates := dsA
    -- Pass B: Non-look-back disjuncts evaluated against `post`.
    let (wB, fsB, _) := runPass false waiting firedSources dedupStates
    waiting := wB; firedSources := fsB
    -- Built-in keyword, rule, reflexive, and delayed triggers.
    let (wC, _) := matchBuiltinAndDelayedTriggers pre post batch mask waiting firedSources
    return wC

/-- Record a `TriggerQueueEvent.triggered` rules event stamped with `origin` as
both its payload `origin` and envelope `batch` without re-entering `closeBatch`,
advancing `nextBatchId` past `origin` so `BatchId`s are never reused (CR 603.2). -/
def recordTriggeredWithOrigin (g : Game) (source : EventObject) (controller : PlayerId)
    (ability : TriggeredAbility) (origin : BatchId) : Game :=
  let ev := (GameEvent.triggered g.turnNumber source controller ability origin).withBatch origin
  let g :=
    { g with
      events := g.events.push ev
      nextBatchId := max g.nextBatchId (origin.raw + 1) }
  g.applyChange ev.change

/-- Close an outermost rules-event batch: evaluate `matchTriggers pre g batchEvents`,
record `TriggerQueueEvent.triggered` for each triggered ability, and enqueue the
resulting `WaitingTrigger`s (CR 603.2 / 603.2c / 603.3 / 603.10). -/
def closeBatch (g : Game) (pre : GameSnapshot) (batchId : BatchId)
    (batchEvents : Array GameEvent) : Game :=
  if batchEvents.isEmpty then g
  else
    let pushInBatch (g : Game) (ev : GameEvent) : Game :=
      let (ev, nextBatch) :=
        match ev with
        | .rules .. => (ev.withBatch batchId, max g.nextBatchId (batchId.raw + 1))
        | .engine .. => (ev, g.nextBatchId)
      ({ g with events := g.events.push ev, nextBatchId := nextBatch }).applyChange ev.change
    let g :=
      g.players.foldl (fun g pl =>
        let p := pl.id
        let g :=
          if !g.hasEnduringStory p && g.controlsStoried p && g.storiedPermanentCount p ≥ 3 then
            let g := pushInBatch g (GameEvent.gainedDesignation g.turnNumber p .enduringStory
              (cause := some (.gameRule .staticAbility)))
            pushInBatch g (GameEvent.engine g.turnNumber
              (.logMsg s!"{(g.player p).name} has an enduring story"))
          else g
        if !g.hasCitysBlessing p && g.controlsAscend p && g.permanentCount p ≥ 10 then
          let g := pushInBatch g (GameEvent.gainedDesignation g.turnNumber p .citysBlessing
            (cause := some (.gameRule .staticAbility)))
          pushInBatch g (GameEvent.engine g.turnNumber
            (.logMsg s!"{(g.player p).name} has the city's blessing"))
        else g) g
    let g :=
      g.players.foldl (fun g pl =>
        match pl.ringBearerId with
        | none => g
        | some rid =>
          match g.findObject? rid with
          | none =>
            let snap := { (g.lastKnownBefore? rid).getD { id := some rid } with
              controller := some pl.id, ringBearer := true }
            pushInBatch g (GameEvent.designation g.turnNumber snap .ringBearer false
              (cause := .gameRule .staticAbility))
          | some o =>
            if o.isBattlefieldObject && g.controlledBy o pl.id then g
            else
              pushInBatch g (GameEvent.designation g.turnNumber
                { g.snapshot o with controller := some pl.id, ringBearer := true }
                .ringBearer false (cause := .gameRule .staticAbility))) g
    let wts :=
      (matchTriggers pre g batchEvents).filter (fun wt =>
        g.stillInGame wt.controller)
    if wts.isEmpty then g
    else
      let firedDelayed := wts.filterMap (fun wt =>
        match wt.delayedTrigger with
        | some (k, c) => if k.isOneShot then some (wt.controller, k, c) else none
        | none => none)
      let g :=
        firedDelayed.foldl (fun acc (ctrl, k, c) =>
          match acc.delayedTriggers.find? (fun dt =>
              dt.controller == ctrl && dt.kind == k && dt.cause == c) with
          | some dt => pushInBatch acc (GameEvent.delayedTriggerConsumed acc.turnNumber dt)
          | none => acc) g
      let preWaiting := g.waitingTriggers
      let (g, toEnqueue, _) := wts.foldl
        (fun (acc, q, coalesced) wt =>
          let key := (wt.source.id, wt.ability)
          let isSelfDealtDamage (t : WaitingTrigger) : Bool :=
            (t.pattern == .thisDealtDamage || t.pattern == .thisDealtNoncombatDamage) &&
              t.ability.grouping == .oncePerBatch
          let alreadyInPre :=
            isSelfDealtDamage wt &&
              preWaiting.any (fun t =>
                t.source.id == wt.source.id && t.ability == wt.ability &&
                  isSelfDealtDamage t)
          if alreadyInPre then
            if coalesced.contains key then
              (acc, q, coalesced)
            else
              let amt := wt.lastKnownPower.getD 0
              let wt' := acc.waitingTriggers.map (fun t =>
                if t.source.id == wt.source.id && t.ability == wt.ability &&
                    isSelfDealtDamage t then
                  { t with lastKnownPower := some (t.lastKnownPower.getD 0 + amt) }
                else t)
              let acc := pushInBatch acc (GameEvent.engine acc.turnNumber (.waitingTriggers wt'))
              (acc, q, coalesced.push key)
          else
            let srcSnap : EventObject :=
              if wt.source.id == noSourceSentinelId then
                { (acc.snapshot wt.source) with
                  id := none
                  controller := wt.source.controller.orElse (fun _ => some wt.controller) }
              else
                match acc.findLiveSourceObject? wt.source.id with
                | some cur => acc.snapshot cur
                | none => (acc.lastKnownBefore? wt.source.id).getD (acc.snapshot wt.source)
            let acc :=
              acc.recordTriggeredWithOrigin srcSnap wt.controller wt.ability batchId
            (acc, q.push wt, coalesced))
        (g, #[], (#[] : Array (ObjectId × TriggeredAbility)))
      if toEnqueue.isEmpty then g else g.enqueueWaitingTriggers toEnqueue

/-- Record a reflexive triggered ability when its embedded action occurs during
resolution (CR 603.12 / 603.3c–d): allocates a fresh `origin : BatchId`, records
`TriggerQueueEvent.triggered`, and enqueues `wt` onto `g.waitingTriggers`.
Skipped if `wt.controller` has already lost or left the game (CR 800.4d). -/
def recordReflexiveTrigger (g : Game) (wt : WaitingTrigger) : Game :=
  if !g.stillInGame wt.controller then g
  else
    let origin : BatchId :=
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
    let g := g.recordTriggeredWithOrigin srcSnap wt.controller wt.ability origin
    g.enqueueWaitingTriggers #[wt]

/-- Resolve `cause` within an active batch `batchCause?`, sharing the batch's
minted `EffectId` across all one-shot events in the batch (CR 610). -/
def resolveCauseInBatch (g : Game) (batchCause? : Option EventCause) :
    EventCause → EventCause × Option EffectId × Option EventCause
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
  match e with
  | .engine .. =>
    let g := { g with events := g.events.push e }
    (g.applyChange e.change, e)
  | .rules t r rawCause _ =>
    let (cause', bumpId?, nextBatchCause?) := g.resolveCauseInBatch batchCause? rawCause
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
    let e' : GameEvent := .rules t r' cause' (some batchId)
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

/-- Add and process an `EngineChange` on the current turn. -/
def change (g : Game) (c : EngineChange) : Game :=
  g.record (GameEvent.engine g.turnNumber c)

/-- Append `next` after the currently stored `g.pendingReplacement` (if any), so
multi-step operations resume remaining work once `Pending.chooseReplacement` finishes. -/
def chainPendingReplacement (g : Game) (next : PendingReplacement) : Game :=
  let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
  match g.pendingReplacement with
  | some first => g.change (.pendingReplacement (some (.seq first next)))
  | none => g.change (.pendingReplacement (some next))

/-- Replay a single recorded `GameEvent` envelope onto `g` without minting new
object/effect/batch ids or re-evaluating `closeBatch` triggers (CR 603.2). -/
def replayEvent (g : Game) (e : GameEvent) : Game :=
  let g := { g with events := g.events.push e }
  let g := g.applyChange e.change
  match e with
  | .engine .. => g
  | .rules _ r cause batch =>
    let batchBump :=
      match batch with
      | some b => b.raw + 1
      | none => 0
    let extraBatch :=
      match r with
      | .triggerQueue (.triggered _ _ _ origin) => origin.raw + 1
      | _ => 0
    let nextBatch := max g.nextBatchId (max batchBump extraBatch)
    let nextEff :=
      match cause.oneShotEffectId? with
      | some eid => max g.nextEffectId (eid.raw + 1)
      | none => g.nextEffectId
    let curBatch :=
      match g.currentBatch with
      | some (bid, prevCause?) =>
        if batch == some bid then
          let (_, _, nextBatchCause?) := g.resolveCauseInBatch prevCause? cause
          some (bid, nextBatchCause?)
        else some (bid, prevCause?)
      | none => none
    { g with
      nextBatchId := nextBatch
      nextEffectId := nextEff
      currentBatch := curBatch }

/-- Deterministically reconstruct a `Game` from its recorded `GameEvent` stream,
starting from `init` (`({} : Game)` by default, matching `Start.startWithRng`). -/
def replayEvents (es : Array GameEvent) (init : Game := {}) : Game :=
  es.foldl Game.replayEvent init

/-- Close a synchronous (non-paused) outermost rules-event batch `batchId` that
started at `startIdx`, reconstructing its pre-batch `GameSnapshot` from the
transient `openBatch*` fields without emitting extra engine events. -/
private def finishOpenBatchSync (g : Game) (batchId : BatchId) (startIdx : Nat)
    (suppressInteractive : Bool := false) : Game :=
  let pre : GameSnapshot :=
    { g with
      objects := g.openBatchObjects
      players := g.openBatchPlayers
      activeEffects := g.openBatchEffects
      pending := g.openBatchPending
      stack := g.openBatchStack
      openBatchSuppressInteractive := false
      events := g.events.extract 0 (min startIdx g.events.size) }
  let g2 :=
    { g with
      currentBatch := none
      openBatchObjects := #[]
      openBatchPlayers := #[]
      openBatchEffects := #[]
      openBatchPending := .none
      openBatchStack := #[]
      openBatchSuppressInteractive := false }
  let slice := g2.events.extract (min startIdx g2.events.size) g2.events.size
  let batchEvents := slice.filter (fun ev =>
    match ev.change with
    | .rules _ => ev.batch == some batchId
    | .engine _ => false)
  if suppressInteractive || g2.over || g2.suppressInteractiveReplay || batchEvents.isEmpty then g2
  else g2.closeBatch pre batchId batchEvents

/-- Close a paused outermost rules-event batch `batchId` that started at `startIdx`,
clearing the journaled `pauseBatch` state via `EngineChange.clearPausedBatch` and
evaluating batch-level triggers once (CR 603.2c). -/
def finishOpenBatch (g : Game) (batchId : BatchId) (startIdx : Nat) : Game :=
  let pre : GameSnapshot :=
    { g with
      objects := g.openBatchObjects
      players := g.openBatchPlayers
      activeEffects := g.openBatchEffects
      pending := g.openBatchPending
      stack := g.openBatchStack
      openBatchSuppressInteractive := false
      events := g.events.extract 0 (min startIdx g.events.size) }
  let g2 := g.change .clearPausedBatch
  let slice := g2.events.extract (min startIdx g2.events.size) g2.events.size
  let batchEvents := slice.filter (fun ev =>
    match ev.change with
    | .rules _ => ev.batch == some batchId
    | .engine _ => false)
  if g2.over || g2.suppressInteractiveReplay || batchEvents.isEmpty then g2
  else g2.closeBatch pre batchId batchEvents

/-- Core batch runner (without `Movement`'s deferred `linkedExile` flush): run `f`
inside a simultaneous rules-event batch (CR 603.2c / 608.2c / 704.3).
If a batch is already active on `g`, `f` joins the enclosing batch; otherwise a
new `BatchId` is opened (advancing `nextBatchId` only if an event uses `batchId`
or the batch pauses) and triggers are evaluated once when `f` completes (or
after `Pending.chooseReplacement` finishes if `f` pauses for a replacement choice). -/
def withBatchCoreReturn {α : Type} (g : Game) (cause : Option EventCause := none)
    (f : Game → Game × α) (suppressInteractive : Bool := false) : Game × α :=
  let isPausePending : Pending → Bool
    | .chooseReplacement .. | .chooseLegend .. => true
    | _ => false
  let quiet0 := suppressInteractive || g.openBatchSuppressInteractive || g.over || g.suppressInteractiveReplay
  match g.currentBatch with
  | some (batchId, prevCause?) =>
    let mergedCause? := prevCause?.orElse (fun _ => cause)
    let wasPaused := isPausePending g.pending
    let (g1, res) := f
      { g with
        currentBatch := some (batchId, mergedCause?)
        openBatchSuppressInteractive := quiet0 }
    let g2 :=
      match g1.currentBatch with
      | none =>
        { g1 with openBatchSuppressInteractive := false }
      | some _ =>
        let nowPaused := isPausePending g1.pending
        let innerOpenedPause :=
          (!wasPaused && nowPaused) || (g.pendingReplacement.isNone && g1.pendingReplacement.isSome)
        let innerEndCause? := (g1.currentBatch.map Prod.snd).join
        let targetCause? : Option EventCause :=
          if innerOpenedPause then innerEndCause?
          else if prevCause?.isNone && cause.isSome then none
          else innerEndCause?
        let replayedPausedBatch? : Option (BatchId × Option EventCause) := Id.run do
          let mut pauseIdx? : Option (Nat × BatchId × Option EventCause) := none
          let mut i := g1.events.size
          while i > 0 do
            i := i - 1
            match g1.events[i]!.change with
            | .engine .clearPausedBatch => return none
            | .engine (.pauseBatch bid c ..) =>
              pauseIdx? := some (i, bid, c)
              break
            | _ => pure ()
          match pauseIdx? with
          | none => return none
          | some (pIdx, bid0, c0) =>
            let mut cur : BatchId × Option EventCause := (bid0, c0)
            for j in [pIdx + 1 : g1.events.size] do
              match g1.events[j]! with
              | .engine _ (.setPausedBatchCause c') _ =>
                cur := (cur.1, c')
              | .rules _ _ evCause evBatch =>
                if evBatch == some cur.1 then
                  let (_, _, nextC?) := g1.resolveCauseInBatch cur.2 evCause
                  cur := (cur.1, nextC?)
              | _ => pure ()
            return some cur
        let g2Core :=
          match replayedPausedBatch? with
          | some (pBid, pCause?) =>
            if pBid == batchId && pCause? != targetCause? then
              g1.change (.setPausedBatchCause targetCause?)
            else
              { g1 with currentBatch := some (batchId, targetCause?) }
          | none =>
            { g1 with currentBatch := some (batchId, targetCause?) }
        { g2Core with openBatchSuppressInteractive := g.openBatchSuppressInteractive }
    (g2, res)
  | none =>
    let batchId : BatchId := ⟨g.nextBatchId⟩
    let startIdx := g.events.size
    let preObjs := g.objects
    let prePls := g.players
    let preEffs := g.activeEffects
    let prePend := g.pending
    let preStk := g.stack
    let g0 :=
      { g with
        currentBatch := some (batchId, cause)
        openBatchObjects := preObjs
        openBatchPlayers := prePls
        openBatchEffects := preEffs
        openBatchPending := prePend
        openBatchStack := preStk
        openBatchSuppressInteractive := quiet0 }
    let (g1, res) := f g0
    let noInteractive := quiet0 || g1.over || g1.suppressInteractiveReplay
    let keepOpen :=
      !noInteractive &&
        match g1.pending with
        | .chooseReplacement .. | .chooseLegend .. => true
        | _ => g1.pendingReplacement.isSome
    if keepOpen then
      let batchCause? := (g1.currentBatch.map Prod.snd).join
      let g2 := g1.change (.pauseBatch batchId batchCause? preObjs prePls preEffs prePend preStk)
      (g2.chainPendingReplacement (.closeBatch batchId startIdx), res)
    else
      (g1.finishOpenBatchSync batchId startIdx (suppressInteractive := noInteractive), res)

/-- Core batch runner (without `Movement`'s deferred `linkedExile` flush). -/
def withBatchCore (g : Game) (cause : Option EventCause := none) (f : Game → Game)
    (suppressInteractive : Bool := false) : Game :=
  (g.withBatchCoreReturn cause (fun g => (f g, ())) (suppressInteractive := suppressInteractive)).1

/-- Bracket a single mana ability or cost action executed during a spell/ability
proposal with `EngineChange.beginProposalAction` / `endProposalAction` so
`reverseToProposalCheckpoint?` reverses or retains the entire action as a unit (CR 734.1). -/
def withProposalAction (g : Game) (kind : ProposalActionKind) (f : Game → Game) : Game :=
  if g.proposalCheckpoint.isNone then f g
  else
    let g0 := g.change (.beginProposalAction kind)
    let g1 := f g0
    if g1.proposalCheckpoint.isNone || (g.proposedSpell.isSome && g1.proposedSpell.isNone) then
      g1
    else if let .chooseReplacement .. := g1.pending then
      g1.chainPendingReplacement .endProposalAction
    else
      g1.change .endProposalAction

/-- Monadic `Except` variant of `withProposalAction`: emits `beginProposalAction` /
`endProposalAction` around `f` when `g.proposalCheckpoint.isSome`, propagating `.error` untouched. -/
def withProposalActionM {ε : Type} (g : Game) (kind : ProposalActionKind)
    (f : Game → Except ε Game) : Except ε Game := do
  if g.proposalCheckpoint.isNone then f g
  else
    let g0 := g.change (.beginProposalAction kind)
    let g1 ← f g0
    if g1.proposalCheckpoint.isNone || (g.proposedSpell.isSome && g1.proposedSpell.isNone) then
      return g1
    else if let .chooseReplacement .. := g1.pending then
      return g1.chainPendingReplacement .endProposalAction
    else
      return g1.change .endProposalAction

/-- Forward reference to `Casting.runPostCastCleanup` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_run_post_cast_cleanup"]
opaque runPostCastCleanupFwd (g : Game) : Game := g

/-- Forward reference to `Decisions.resumePendingReplacement` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_resume_pending_replacement"]
opaque resumePendingReplacementFwd (g : Game) (pr : PendingReplacement)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game := g

/-- Forward reference to `Movement.flushQueuedLinkedExile` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_flush_queued_linked_exile"]
opaque flushQueuedLinkedExileFwd (g : Game) (suppressInteractive : Bool := false) : Game := g

/-- Forward reference to `Leaving.reconcilePostReplayDepartures` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_reconcile_post_replay_departures"]
opaque reconcilePostReplayDeparturesFwd (g : Game) (suppressInteractive : Bool := false) : Game := g

/-- Forward reference to `Decisions.finishAndGrantPriority` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_finish_and_grant_priority"]
opaque finishAndGrantPriorityFwd (g : Game) (prio : PlayerId) : Game := g

/-- Forward reference to `Decisions.anyContinuationGrantsPriority` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_any_continuation_grants_priority"]
opaque anyContinuationGrantsPriorityFwd (g : Game) : Bool := false

/-- Forward reference to `Decisions.anyPostPromptContinuationGrantsPriority` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_any_post_prompt_continuation_grants_priority"]
opaque anyPostPromptContinuationGrantsPriorityFwd (g : Game) : Bool := false

/-- Forward reference to `Decisions.anyContinuationSettlesControlFlow` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_any_continuation_settles_control_flow"]
opaque anyContinuationSettlesControlFlowFwd (g : Game) : Bool := false

/-- Forward reference to `Decisions.anyPostPromptContinuationSettlesControlFlow` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_any_post_prompt_continuation_settles_control_flow"]
opaque anyPostPromptContinuationSettlesControlFlowFwd (g : Game) : Bool := false

/-- Forward reference to `Decisions.hasImplicitPriorityContinuation` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_has_implicit_priority_continuation"]
opaque hasImplicitPriorityContinuationFwd (g : Game) : Bool := false

/-- Forward reference to `Decisions.hasImplicitPendingPriorityContinuation` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_has_implicit_pending_priority_continuation"]
opaque hasImplicitPendingPriorityContinuationFwd (g : Game) : Bool := false

/-- Forward reference to `Decisions.hasPostPromptImplicitPendingPriorityContinuation` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_has_post_prompt_implicit_pending_priority_continuation"]
opaque hasPostPromptImplicitPendingPriorityContinuationFwd (g : Game) : Bool := false

/-- Forward reference to `Decisions.continuationUsesImplicitPendingPriorityExport` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_continuation_uses_implicit_pending_priority"]
opaque continuationUsesImplicitPendingPriorityFwd (g : Game) (pr : PendingReplacement) : Bool := false

/-- Forward reference to `Decisions.drainPendingContinuations` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_drain_pending_continuations"]
opaque drainPendingContinuationsFwd (g : Game) : Game := g

/-- Drain `g.pendingReplacement` locally while `!g.over && g.pending == .none &&
g.afterRandom == .none`, without touching `triggerSequenceRest` or
`outerPendingReplacements` (CR 603.2c / 616.1 / 734.1). -/
partial def drainLocalPendingReplacement (g : Game) : Game :=
  if g.over || g.pending != .none || g.afterRandom != .none then g
  else
    match g.pendingReplacement with
    | some cont =>
      let g := Id.run do
        let mut g := g.change (.pendingReplacement none)
        while g.continuations.back? == some {} do
          g := g.change .popContinuationFrame
        return g
      let g := g.resumePendingReplacementFwd cont false
      g.drainLocalPendingReplacement
    | none => g

/-- Reattach a detached `outerCont?` after an interactive choice completes:
when an active interpreter wait (`currentInterpWait?`) is waiting to resume in
`drainPendingContinuations` (CR 608.2c), push `outer` onto
`outerPendingReplacements` so the interpreter resumes *before* `outer` runs;
otherwise chain `outer` into `pendingReplacement`. -/
def reattachOuterCont (g : Game) (outerCont? : Option PendingReplacement) : Game :=
  match outerCont? with
  | none => g
  | some outer =>
    if g.currentInterpWait?.isSome then
      let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
      g.change (.pushOuterPendingReplacement outer)
    else
      g.chainPendingReplacement outer

/-- Chain a detached proposal-completion `outer` continuation, preserving CR 117.3c
priority for `prio` in `pendingPriority` whenever `grantPriority` holds,
`!hadOuterReplacement`, `!openCont`, `outer` is non-priority or relies on
implicit `pendingPriority` (`!outer.endsWithPriorityGrant || continuationUsesImplicitPendingPriorityFwd`),
and `g.pendingPriority` is not yet set, before appending `.finishResolutionChoice`
(when `!hadOuterReplacement`). -/
def chainProposalOuterCont (g : Game) (prio : PlayerId)
    (outer : PendingReplacement) (grantPriority : Bool := true)
    (hadOuterReplacement : Bool := false) (openCont : Bool := false) : Game :=
  let wrapped :=
    if hadOuterReplacement then outer
    else outer.ensureEndsWithFinishResolutionChoice
  let g :=
    if !g.over && grantPriority && !hadOuterReplacement && !openCont &&
        (!outer.endsWithPriorityGrant || g.continuationUsesImplicitPendingPriorityFwd outer) &&
        g.pendingPriority.isNone then
      g.change (.pendingPriority (some (g.priorityInstead prio)))
    else g
  g.chainPendingReplacement wrapped

/-- When a proposal-completion tail (`completeTurnFaceUp`, `finishPostLoyaltyActivated`,
`becomeActivated`, `.finishBecomeCast`, `SacrificeDiscard`) has queued continuations
(`pendingReplacement`, `outerPendingReplacements`, or `currentInterpWait?`), preserve
CR 117.3c priority for `prio` in `pendingPriority` when no explicit priority recipient
is queued and chain `.finishResolutionChoice` if no continuation settles control flow. -/
def chainFinishChoicePreservingPriority (g : Game) (prio : PlayerId) : Game :=
  if g.over then g
  else
    let openCont := g.anyContinuationSettlesControlFlowFwd
    let g :=
      if (!openCont || g.hasImplicitPendingPriorityContinuationFwd) &&
          g.pendingPriority.isNone then
        g.change (.pendingPriority (some (g.priorityInstead prio)))
      else g
    if openCont then g
    else g.chainPendingReplacement .finishResolutionChoice

def isProposalReplayPaused (g : Game) : Bool :=
  match g.pending with
  | .chooseReplacement .. | .chooseLegend .. => true
  | _ => false

private def resolveProposalRevId (m : Array (ObjectId × ObjectId)) (oid : ObjectId) : ObjectId :=
  match m.findSomeRev? (fun (afterId, origId) =>
      if afterId == oid then some origId else none) with
  | some origId => origId
  | none => oid

private def resolveProposalEffId (m : Array (EffectId × EffectId)) (eid : EffectId) : EffectId :=
  match m.findSomeRev? (fun (rawEid, actualEid) =>
      if rawEid == eid then some actualEid else none) with
  | some actualEid => actualEid
  | none => eid

private def remapProposalAttackTarget (ro : ObjectId → ObjectId) : AttackTarget → AttackTarget
  | .player p => .player p
  | .planeswalker pw => .planeswalker (ro pw)
  | .battle b => .battle (ro b)

private def remapProposalTarget (ro : ObjectId → ObjectId) : Target → Target
  | .player p => .player p
  | .permanent id => .permanent (ro id)
  | .card id => .card (ro id)

private def remapProposalStatus (ro : ObjectId → ObjectId) (s : Status) : Status :=
  { s with
    attackingTarget := s.attackingTarget.map (remapProposalAttackTarget ro)
    blocking := s.blocking.map ro
    phasedWith := s.phasedWith.map ro }

private def remapProposalPlayPerm (ro : ObjectId → ObjectId) (p : PlayPermission) : PlayPermission :=
  { p with prepareSource := p.prepareSource.map ro }

private def remapProposalGameObjNoId (ro : ObjectId → ObjectId) (o : GameObject) : GameObject :=
  { o with
    status := remapProposalStatus ro o.status
    sourceId := o.sourceId.map ro
    attachedTo := o.attachedTo.map ro
    linkedExile := o.linkedExile.map ro
    leaveTriggerExile := o.leaveTriggerExile.map ro
    triggerCauseId := o.triggerCauseId.map ro
    triggerCauseStatus := o.triggerCauseStatus.map (remapProposalStatus ro)
    triggerCauseIds := o.triggerCauseIds.map ro
    exiledBy := o.exiledBy.map ro }

private def remapProposalGameObj (ro : ObjectId → ObjectId) (o : GameObject) : GameObject :=
  { remapProposalGameObjNoId ro o with id := ro o.id }

private def remapProposalEventObjNoId (ro : ObjectId → ObjectId) (eo : EventObject) : EventObject :=
  { eo with
    blockingIds := eo.blockingIds.map ro
    attachedTo := eo.attachedTo.map ro
    attackingTarget := eo.attackingTarget.map (remapProposalAttackTarget ro) }

private def remapProposalEventObj (ro : ObjectId → ObjectId) (eo : EventObject) : EventObject :=
  { remapProposalEventObjNoId ro eo with id := eo.id.map ro }

private def remapProposalRepEffKind (ro : ObjectId → ObjectId) :
    ReplacementEffectKind → ReplacementEffectKind
  | .entersUntappedBehold bid sub => .entersUntappedBehold (ro bid) sub
  | .entersAsCopyCreatureUntilEot tid => .entersAsCopyCreatureUntilEot (ro tid)
  | .asEntersAttachAura hid => .asEntersAttachAura (ro hid)
  | k => k

private def remapProposalRepId (ro : ObjectId → ObjectId) (r : ReplacementId) : ReplacementId :=
  { r with
    kind := remapProposalRepEffKind ro r.kind
    object := r.object.map ro
    grantor := r.grantor.map ro }

private def remapProposalRepKind (ro : ObjectId → ObjectId) : ReplacementKind → ReplacementKind
  | .entersTappedSelf oid => .entersTappedSelf (ro oid)
  | .entersUntappedPayLife oid l => .entersUntappedPayLife (ro oid) l
  | .entersTappedDeclinePayLife oid => .entersTappedDeclinePayLife (ro oid)
  | .entersUntappedBehold oid bid s => .entersUntappedBehold (ro oid) (ro bid) s
  | .entersTappedDeclineBehold oid => .entersTappedDeclineBehold (ro oid)
  | .asEntersChooseColor oid c => .asEntersChooseColor (ro oid) c
  | .asEntersChooseCreatureType oid s => .asEntersChooseCreatureType (ro oid) s
  | .asEntersChooseOdd oid o => .asEntersChooseOdd (ro oid) o
  | .asEntersChooseCardName oid n => .asEntersChooseCardName (ro oid) n
  | .asEntersChooseCardType oid t => .asEntersChooseCardType (ro oid) t
  | .asEntersChooseAnchor oid a => .asEntersChooseAnchor (ro oid) a
  | .entersWithCountersSelf oid k a => .entersWithCountersSelf (ro oid) k a
  | .entersUnderControl oid c => .entersUnderControl (oid.map ro) c
  | .entersAsCopy oid t => .entersAsCopy (oid.map ro) t
  | .entersAsCopyCreatureUntilEot oid tid => .entersAsCopyCreatureUntilEot (ro oid) (ro tid)
  | .declineEntersAsCopy oid => .declineEntersAsCopy (ro oid)
  | .entersBackFaceUp oid => .entersBackFaceUp (oid.map ro)
  | .asEntersAttachAura oid hid => .asEntersAttachAura (ro oid) (ro hid)
  | .entersWithExtraCounters oid k a => .entersWithExtraCounters (oid.map ro) k a
  | .modifyCountersPut oid k a m => .modifyCountersPut (oid.map ro) k a m
  | .exileInsteadOfStackLeave oid => .exileInsteadOfStackLeave (oid.map ro)
  | .exileInsteadOfGraveyard oid w => .exileInsteadOfGraveyard (oid.map ro) w
  | .shieldCounterDestroy oid => .shieldCounterDestroy (ro oid)
  | .addNoncombatDamage src b => .addNoncombatDamage (src.map ro) b
  | .multiplyDamage src f => .multiplyDamage (src.map ro) f
  | .stunCounterUntap oid => .stunCounterUntap (ro oid)
  | k => k

private def remapProposalPrevKind (ro : ObjectId → ObjectId) : PreventionKind → PreventionKind
  | .preventAllDamageToPermanent tid => .preventAllDamageToPermanent (ro tid)
  | .preventAllDamageFromSource sid => .preventAllDamageFromSource (ro sid)
  | .protectionPreventDamage pid sid => .protectionPreventDamage (ro pid) (ro sid)
  | .shieldCounterPreventDamage oid => .shieldCounterPreventDamage (ro oid)
  | k => k

private def remapProposalDuration (ro : ObjectId → ObjectId) : EffectDuration → EffectDuration
  | .whileSourceOnBattlefield s => .whileSourceOnBattlefield (ro s)
  | .untilSourceLeaves s => .untilSourceLeaves (ro s)
  | .whileSourceHasCounter s k => .whileSourceHasCounter (ro s) k
  | .whileInZone o z => .whileInZone (ro o) z
  | d => d

private def remapProposalScope (ro : ObjectId → ObjectId) : ObjectScope → ObjectScope
  | .objects ids => .objects (ids.map ro)
  | s => s

private def remapProposalGameRule (ro : ObjectId → ObjectId) : GameRule → GameRule
  | .cantUntap o s => .cantUntap (ro o) (ro s)
  | .cantBeBlockedByPlayer o p => .cantBeBlockedByPlayer (ro o) p
  | .cantBeBlockedExceptByHaste o => .cantBeBlockedExceptByHaste (ro o)
  | .cantBlock o => .cantBlock (ro o)
  | .uncounterable o => .uncounterable (ro o)
  | .commandEmblem o => .commandEmblem (ro o)
  | r => r

private def remapProposalPlayPermSpec (ro : ObjectId → ObjectId) :
    PlayPermissionSpec → PlayPermissionSpec
  | .playFromExile o perm => .playFromExile (ro o) (remapProposalPlayPerm ro perm)
  | .flashback o => .flashback (ro o)
  | .colorlessGrant o c => .colorlessGrant (ro o) (ro c)

private def remapProposalEffSpec (ro : ObjectId → ObjectId) :
    ContinuousEffectSpec → ContinuousEffectSpec
  | .layered sc e d => .layered (remapProposalScope ro sc) e (remapProposalDuration ro d)
  | .playerRule p (.protectionFrom q srcId? ctrl?) d =>
    .playerRule p (.protectionFrom q (srcId?.map ro) ctrl?) (remapProposalDuration ro d)
  | .playerRule p (.hexproof from? srcId? ctrl?) d =>
    .playerRule p (.hexproof from? (srcId?.map ro) ctrl?) (remapProposalDuration ro d)
  | .playerRule p r d => .playerRule p r (remapProposalDuration ro d)
  | .gameRule r d => .gameRule (remapProposalGameRule ro r) (remapProposalDuration ro d)
  | .replacement r d =>
    .replacement
      { r with
        id := remapProposalRepId ro r.id
        source := r.source.map ro
        kind := remapProposalRepKind ro r.kind }
      (remapProposalDuration ro d)
  | .prevention r d =>
    .prevention
      { r with
        id := remapProposalRepId ro r.id
        source := r.source.map ro
        kind := remapProposalPrevKind ro r.kind }
      (remapProposalDuration ro d)
  | .permission p r d => .permission p (remapProposalPlayPermSpec ro r) (remapProposalDuration ro d)

private def remapProposalCause (ro : ObjectId → ObjectId) (re : EffectId → EffectId) :
    EventCause → EventCause
  | .costPayment k p fo => .costPayment k p (fo.map ro)
  | .oneShotEffect eid src ctrl => .oneShotEffect (eid.map re) (src.map ro) ctrl
  | .replaced rep orig => .replaced (remapProposalRepId ro rep) (remapProposalCause ro re orig)
  | c => c

private def remapProposalDelayedKind (ro : ObjectId → ObjectId) :
    DelayedTriggerKind → DelayedTriggerKind
  | .endStepReturn oid => .endStepReturn (ro oid)
  | .endStepExile oid => .endStepExile (ro oid)
  | .endStepSacrifice oid => .endStepSacrifice (ro oid)
  | .endOfCombatExile oid => .endOfCombatExile (ro oid)
  | .endOfCombatSacrifice oid => .endOfCombatSacrifice (ro oid)
  | .endStepGraveReturn oid c => .endStepGraveReturn (ro oid) c
  | .lokiCopyNextInstantSorceryThisTurn sid fp =>
    .lokiCopyNextInstantSorceryThisTurn (sid.map ro) fp
  | k => k

private def remapProposalStackEntry (ro : ObjectId → ObjectId) (re : EffectId → EffectId)
    (se : StackEntry) : StackEntry :=
  { se with
    objectId := ro se.objectId
    targets := se.targets.map (remapProposalTarget ro)
    delayedTrigger := se.delayedTrigger.map (fun (k, c) =>
      (remapProposalDelayedKind ro k, remapProposalCause ro re c)) }

private def remapProposalObjectChange (ro : ObjectId → ObjectId) : ObjectChange → ObjectChange
  | .linkedExile v => .linkedExile (v.map ro)
  | .pushLinkedExile id => .pushLinkedExile (ro id)
  | .leaveTriggerExile v => .leaveTriggerExile (v.map ro)
  | .pushLeaveTriggerExile id => .pushLeaveTriggerExile (ro id)
  | .exiledBy v => .exiledBy (v.map ro)
  | oc => oc

private def remapProposalStepOutcome (ro : ObjectId → ObjectId) (o : StepOutcome) : StepOutcome :=
  { o with objects := o.objects.map ro }

private def remapProposalInterpCont (ro : ObjectId → ObjectId) (re : EffectId → EffectId) :
    InterpCont → InterpCont
  | .bindClose v idx eid body extra? =>
    .bindClose v idx (re eid) body (extra?.map (remapProposalStepOutcome ro))
  | .forEachObjectRest v ids body => .forEachObjectRest v (ids.map ro) body
  | .afterPutToBattlefield fid fge mods c =>
    .afterPutToBattlefield (ro fid) fge mods (remapProposalCause ro re c)
  | .afterExileReturnBriefly dstP fid nm ret c =>
    .afterExileReturnBriefly dstP (ro fid) nm ret (remapProposalCause ro re c)
  | .afterReturnTappedEndStepExile dstP fid nm c =>
    .afterReturnTappedEndStepExile dstP (ro fid) nm (remapProposalCause ro re c)
  | .logIfCountersIncreased tid bef msg => .logIfCountersIncreased (ro tid) bef msg
  | .applyAggregatedLifelink idx c => .applyAggregatedLifelink idx (remapProposalCause ro re c)
  | .exploreAfterLandMove ctrl cid ow nm => .exploreAfterLandMove ctrl (ro cid) ow nm
  | .exploreOfferGraveyard ctrl cid => .exploreOfferGraveyard ctrl (ro cid)
  | .afterRevealUntil p rest sh dack c =>
    .afterRevealUntil p (rest.map ro) sh (dack.map ro) (remapProposalCause ro re c)
  | .afterDistinctSearchMove p rem c =>
    .afterDistinctSearchMove p (rem.map ro) (remapProposalCause ro re c)
  | .afterMillOfferPermanentOrGainLife p ids life =>
    .afterMillOfferPermanentOrGainLife p (ids.map ro) life
  | .afterDrawAddPlusOnesForDiscards p tid? => .afterDrawAddPlusOnesForDiscards p (tid?.map ro)
  | .afterTokensEnter idx p mods c => .afterTokensEnter idx p mods (remapProposalCause ro re c)
  | .worldsCollectPlayers ev rest ch => .worldsCollectPlayers ev rest (ch.map ro)
  | .worldsAfterPut ev vc => .worldsAfterPut ev (vc.map (fun (id, p, nm) => (ro id, p, nm)))
  | .afterMoveLoop rem dest verb mods c fi? =>
    .afterMoveLoop (rem.map ro) dest verb mods (remapProposalCause ro re c) fi?
  | .afterDamagePermanentsLoop rem amt nm src? opp idx c =>
    .afterDamagePermanentsLoop (rem.map ro) amt nm (src?.map (remapProposalEventObj ro)) opp idx
      (remapProposalCause ro re c)
  | .afterDividedDamageLoop rem nm src? idx c =>
    .afterDividedDamageLoop (rem.map (fun (si, t, n) => (si, remapProposalTarget ro t, n))) nm
      (src?.map (remapProposalEventObj ro)) idx (remapProposalCause ro re c)
  | .afterMixedDamageLoop rem nm src? idx c te acc pe? =>
    .afterMixedDamageLoop (rem.map (fun (t, n) => (remapProposalTarget ro t, n))) nm
      (src?.map (remapProposalEventObj ro)) idx (remapProposalCause ro re c) te acc
      (pe?.map (fun (oid, lethal, pIdx) => (ro oid, lethal, pIdx)))
  | .afterCounterOpLoop rem mode c fi? =>
    .afterCounterOpLoop (rem.map ro) mode (remapProposalCause ro re c) fi?
  | .afterCopyAndCastExileLoop rem ex gp c pf? fi? =>
    .afterCopyAndCastExileLoop (rem.map ro) (ex.map ro) gp (remapProposalCause ro re c)
      (pf?.map (fun (id, nm) => (ro id, nm))) fi?
  | .afterMoveCountersPut tid rem c =>
    .afterMoveCountersPut (ro tid) rem (remapProposalCause ro re c)
  | k => k

private def remapProposalInterpState (ro : ObjectId → ObjectId) (re : EffectId → EffectId)
    (st : InterpState) : InterpState :=
  { st with
    ctx := { st.ctx with
      sourceId := st.ctx.sourceId.map ro
      sourceSnapshot := st.ctx.sourceSnapshot.map (remapProposalEventObj ro)
      targets := st.ctx.targets.map (remapProposalTarget ro)
      targetSlots := st.ctx.targetSlots.map (·.map (remapProposalTarget ro))
      triggerSubjectId := st.ctx.triggerSubjectId.map ro
      triggerSubjectIds := st.ctx.triggerSubjectIds.map ro
      triggerSubjectSnapshot := st.ctx.triggerSubjectSnapshot.map (remapProposalEventObj ro)
      oneShotEffectId := re st.ctx.oneShotEffectId }
    stack := st.stack.map (remapProposalInterpCont ro re) }

private def remapProposalContinuationChange (ro : ObjectId → ObjectId) (re : EffectId → EffectId) :
    ContinuationChange → ContinuationChange
  | .recentTokenIds v => .recentTokenIds (v.map ro)
  | .pendingFreeCopies v => .pendingFreeCopies (v.map (fun (p, ids, a, b) => (p, ids.map ro, a, b)))
  | .pendingMayCastFromExile v => .pendingMayCastFromExile (v.map (fun (p, ids, n) => (p, ids.map ro, n)))
  | .postCastCleanup v => .postCastCleanup (v.map fun
      | .cascadeBottom c id os => .cascadeBottom c (ro id) (os.map ro)
      | .grimaBottom vic id os => .grimaBottom vic (ro id) (os.map ro)
      | .copyCeaseToExist cid => .copyCeaseToExist (ro cid)
      | .lookedBottom c id os => .lookedBottom c (ro id) (os.map ro))
  | .conniveSource v => .conniveSource (v.map ro)
  | .stagedAttackTokenBatches v => .stagedAttackTokenBatches (v.map (fun b =>
      { b with
        attackingTarget := b.attackingTarget.map (remapProposalAttackTarget ro)
        cause := b.cause.map (remapProposalCause ro re) }))
  | .stashedCause v => .stashedCause (v.map (remapProposalCause ro re))
  | .resolvingSpell v => .resolvingSpell (v.map ro)
  | .resolvingAbility v => .resolvingAbility (v.map ro)
  | .afterRandom v => .afterRandom (match v with
      | .revealRandomCreatureThenBottom c rev => .revealRandomCreatureThenBottom c (rev.map ro)
      | .putOnTop p ids => .putOnTop p (ids.map ro)
      | .beholdUntap p lid sub => .beholdUntap p (ro lid) sub
      | ar => ar)
  | .resolutionFinish v => .resolutionFinish (v.map fun
      | .ability oid snap ctrl sid sc =>
        .ability (ro oid) (remapProposalEventObj ro snap) ctrl (sid.map ro) sc
      | .spell se snap fg =>
        .spell (remapProposalStackEntry ro re se) (remapProposalEventObj ro snap) fg)
  | .pendingResolvedEvent v => .pendingResolvedEvent (v.map (fun (eo, p, c) =>
      (remapProposalEventObj ro eo, p, remapProposalCause ro re c)))
  | .stepEnv v => .stepEnv (v.map (fun (vid, o) => (vid, remapProposalStepOutcome ro o)))
  | .bindStepOutcome vid o => .bindStepOutcome vid (remapProposalStepOutcome ro o)
  | .interpWait? v => .interpWait? (v.map (remapProposalInterpState ro re))
  | cc => cc

private def skipProposalActionScaffolding : GameEvent → Bool
  | .rules _ (.triggerQueue (.triggered ..)) _ _
  | .rules _ (.delayedTrigger (.consumed ..)) _ _ => true
  | .engine _ c =>
    match c with
    | .enqueueWaitingTriggers _ | .waitingTriggers _
    | .queueLinkedExile _ | .clearQueuedLinkedExile
    | .beginProposalAction _ | .endProposalAction
    | .proposedSpell _ | .proposal _ | .proposalChanges _
    | .saveProposalCheckpoint | .clearProposalCheckpoint
    | .pending _ | .continuation (.pendingReplacement _)
    | .continuation (.pushOuterPendingReplacement _) | .continuation .popOuterPendingReplacement
    | .pushContinuationFrame _ | .popContinuationFrame
    | .pauseBatch .. | .setPausedBatchCause _ | .clearPausedBatch
    | .replacementOrder _ => true
    | _ => false
  | _ => false

/-- Replay `remainingStream` (a suffix of `fullKeptStream`) in per-batch groups,
draining local non-paused `pendingReplacement` continuations immediately after
each `runBatch` and stopping only when `Pending.chooseReplacement` or
`Pending.chooseLegend` opens, chaining any remaining slice via
`PendingReplacement.continueCheckpointReplay` (CR 603.2c / 610.3 / 616.1 /
734.1–734.2 / 800.4a). -/
@[noinline] private def replayKeptStreamStepEvent
    (fullKeptStream : Array (Bool × GameEvent))
    (revMap : Array (ObjectId × ObjectId))
    (minPostCkptEffId : Nat)
    (effectiveOrigNextEffs : Array Nat)
    (fullIdx : Nat) (fromAction : Bool)
    (st : Game × Array (ObjectId × ObjectId) × Array (EffectId × EffectId) × Array ObjectId)
    (ev : GameEvent) :
    Game × Array (ObjectId × ObjectId) × Array (EffectId × EffectId) × Array ObjectId :=
  let isLibZone : Zone → Bool
    | .library _ => true
    | _ => false
  let inLibraryObjs (objs : Array GameObject) (cid : ObjectId) : Bool :=
    (objs.find? (·.id == cid)).any (fun o => isLibZone o.zone)
  let effObjId? : ContinuousEffectSpec → Option ObjectId
    | .layered (.objects #[id]) _ _ => some id
    | .permission _ (.playFromExile id _) _
    | .permission _ (.flashback id) _
    | .permission _ (.colorlessGrant id _) _ => some id
    | .gameRule (.cantUntap id _) _
    | .gameRule (.cantBeBlockedByPlayer id _) _
    | .gameRule (.cantBeBlockedExceptByHaste id) _
    | .gameRule (.cantBlock id) _
    | .gameRule (.uncounterable id) _
    | .gameRule (.commandEmblem id) _ => some id
    | .replacement r _ => r.id.object
    | .prevention p _ => p.id.object
    | _ => none
  let cleanupRemappedLeavingId (origId : ObjectId) (cause : EventCause) (g0 : Game) : Game :=
    let g0 := g0.objects.foldl (fun acc a =>
      if a.attachedTo == some origId then
        acc.record (GameEvent.unattached acc.turnNumber (acc.snapshot a) origId
          (cause := .gameRule .unattachOnHostLeave))
      else acc) g0
    let (g0, prepCopyId?) : Game × Option ObjectId :=
      match g0.preparedCopyOf? origId with
      | some c =>
        let g1 := g0.record (GameEvent.ceasedToExist g0.turnNumber (g0.snapshot c)
          (cause := .stateBased .copyOutsideStackOrBf))
        (g1, some c.id)
      | none => (g0, none)
    g0.activeEffects.foldl (fun acc (eid, eff) =>
      let tied :=
        effObjId? eff == some origId ||
          (prepCopyId?.isSome && effObjId? eff == prepCopyId?) ||
          (match eff.duration with
           | .whileInZone wid _
           | .whileSourceOnBattlefield wid
           | .untilSourceLeaves wid
           | .whileSourceHasCounter wid _ => wid == origId
           | _ => false) ||
          (match eff with
           | .gameRule (.cantUntap _ src) _ => src == origId
           | .permission _ (.playFromExile _ perm) _ => perm.prepareSource == some origId
           | .layered (.objects ids) _ _ =>
             ids.contains origId && ids.all (fun id => id == origId || (acc.findObject? id).isNone)
           | _ => false)
      if tied then acc.record (GameEvent.effectExpired acc.turnNumber eid eff (cause := cause))
      else acc) g0
  let roWith (lm : Array (ObjectId × ObjectId)) (g0 : Game) (oid : ObjectId) : ObjectId :=
    let r1 := resolveProposalRevId revMap oid
    let r2 := resolveProposalRevId lm r1
    if r1 != oid then
      let f := g0.followMoved r2
      if f != r2 && (g0.findObject? f).isSome then f else r2
    else r2
  let mintObjId (gCur : Game) (lm : Array (ObjectId × ObjectId)) (oid : ObjectId) :
      ObjectId × Array (ObjectId × ObjectId) :=
    if oid.raw < gCur.nextObjectId || gCur.objects.any (·.id == oid) then
      let freshId : ObjectId := ⟨gCur.nextObjectId⟩
      let r1 := resolveProposalRevId revMap oid
      (freshId, if freshId == oid then lm else lm.push (r1, freshId))
    else
      (oid, lm)
  let ensurePostCkptEffId (g0 : Game) (effRev : Array (EffectId × EffectId)) (rawEid : EffectId) :
      EffectId × Array (EffectId × EffectId) :=
    if rawEid.raw < minPostCkptEffId then
      (resolveProposalEffId effRev rawEid, effRev)
    else
      match effRev.findSomeRev? (fun (src, dst) => if src == rawEid then some dst else none) with
      | some dst => (dst, effRev)
      | none =>
        let minFree := effRev.foldl (fun acc (_, dst) => max acc (dst.raw + 1)) g0.nextEffectId
        let actualEid : EffectId :=
          if rawEid.raw < minFree || g0.activeEffects.any (·.1 == rawEid) then
            ⟨minFree⟩
          else rawEid
        (actualEid, effRev.push (rawEid, actualEid))
  let rec ensureRulesCause (ro : ObjectId → ObjectId) (g0 : Game)
      (effRev : Array (EffectId × EffectId)) :
      EventCause → EventCause × Array (EffectId × EffectId)
    | .costPayment k p fo => (.costPayment k p (fo.map ro), effRev)
    | .oneShotEffect (some rawEid) src ctrl =>
      let (actualEid, effRev1) := ensurePostCkptEffId g0 effRev rawEid
      (.oneShotEffect (some actualEid) (src.map ro) ctrl, effRev1)
    | .oneShotEffect none src ctrl => (.oneShotEffect none (src.map ro) ctrl, effRev)
    | .replaced rep orig =>
      let (orig', effRev1) := ensureRulesCause ro g0 effRev orig
      (.replaced (remapProposalRepId ro rep) orig', effRev1)
    | c => (c, effRev)
  let rec ensurePayloadCause (ro : ObjectId → ObjectId) (g0 : Game)
      (effRev : Array (EffectId × EffectId)) :
      EventCause → Game × EventCause × Array (EffectId × EffectId)
    | .costPayment k p fo => (g0, .costPayment k p (fo.map ro), effRev)
    | .oneShotEffect (some rawEid) src ctrl =>
      let (actualEid, effRev1) := ensurePostCkptEffId g0 effRev rawEid
      let g1 :=
        if actualEid.raw >= g0.nextEffectId then
          g0.record (.engine g0.turnNumber (.nextEffectId (actualEid.raw + 1)))
        else g0
      (g1, .oneShotEffect (some actualEid) (src.map ro) ctrl, effRev1)
    | .oneShotEffect none src ctrl => (g0, .oneShotEffect none (src.map ro) ctrl, effRev)
    | .replaced rep orig =>
      let (g1, orig', effRev1) := ensurePayloadCause ro g0 effRev orig
      (g1, .replaced (remapProposalRepId ro rep) orig', effRev1)
    | c => (g0, c, effRev)
  let ensureStackEntry (ro : ObjectId → ObjectId) (g0 : Game)
      (effRev : Array (EffectId × EffectId)) (se : StackEntry) :
      Game × StackEntry × Array (EffectId × EffectId) :=
    let (g1, dt', effRev1) :=
      match se.delayedTrigger with
      | some (k, c) =>
        let (g', c', e') := ensurePayloadCause ro g0 effRev c
        (g', some (remapProposalDelayedKind ro k, c'), e')
      | none => (g0, none, effRev)
    (g1,
      { se with
        objectId := ro se.objectId
        targets := se.targets.map (remapProposalTarget ro)
        delayedTrigger := dt' },
      effRev1)
  let ensureStackTriggerSpec (ro : ObjectId → ObjectId) (g0 : Game)
      (effRev : Array (EffectId × EffectId)) (sp : StackTriggerSpec) :
      Game × StackTriggerSpec × Array (EffectId × EffectId) :=
    let (g1, dt', effRev1) :=
      match sp.delayedTrigger with
      | some (k, c) =>
        let (g', c', e') := ensurePayloadCause ro g0 effRev c
        (g', some (remapProposalDelayedKind ro k, c'), e')
      | none => (g0, none, effRev)
    (g1,
      { sp with
        sourceId := sp.sourceId.map ro
        delayedTrigger := dt'
        triggerCauseId := sp.triggerCauseId.map ro
        triggerCauseIds := sp.triggerCauseIds.map ro
        triggerCauseStatus := sp.triggerCauseStatus.map (remapProposalStatus ro) },
      effRev1)
  let ensureDelayedTrigger (ro : ObjectId → ObjectId) (g0 : Game)
      (effRev : Array (EffectId × EffectId)) (dt : DelayedTrigger) :
      Game × DelayedTrigger × Array (EffectId × EffectId) :=
    let (g1, c', effRev1) := ensurePayloadCause ro g0 effRev dt.cause
    (g1,
      { dt with
        source := dt.source.map (remapProposalGameObj ro)
        kind := remapProposalDelayedKind ro dt.kind
        cause := c' },
      effRev1)
  let ensureContinuationChange (ro : ObjectId → ObjectId) (re : EffectId → EffectId)
      (g0 : Game) (effRev : Array (EffectId × EffectId)) :
      ContinuationChange → Game × ContinuationChange × Array (EffectId × EffectId)
    | .stagedAttackTokenBatches v => Id.run do
      let mut gCur := g0
      let mut eCur := effRev
      let mut out := #[]
      for b in v do
        let (g1, c', e1) :=
          match b.cause with
          | some c =>
            let (g', c1, e') := ensurePayloadCause ro gCur eCur c
            (g', some c1, e')
          | none => (gCur, none, eCur)
        gCur := g1
        eCur := e1
        out := out.push
          { b with
            attackingTarget := b.attackingTarget.map (remapProposalAttackTarget ro)
            cause := c' }
      return (gCur, .stagedAttackTokenBatches out, eCur)
    | .stashedCause (some c) =>
      let (g1, c', effRev1) := ensurePayloadCause ro g0 effRev c
      (g1, .stashedCause (some c'), effRev1)
    | .resolutionFinish (some (.spell se snap fg)) =>
      let (g1, se', effRev1) := ensureStackEntry ro g0 effRev se
      (g1, .resolutionFinish (some (.spell se' (remapProposalEventObj ro snap) fg)), effRev1)
    | .pendingResolvedEvent (some (eo, p, c)) =>
      let (g1, c', effRev1) := ensurePayloadCause ro g0 effRev c
      (g1, .pendingResolvedEvent (some (remapProposalEventObj ro eo, p, c')), effRev1)
    | cc => (g0, remapProposalContinuationChange ro re cc, effRev)
  let stepEvent (fullIdx : Nat) (fromAction : Bool)
      (st : Game × Array (ObjectId × ObjectId) × Array (EffectId × EffectId) × Array ObjectId)
      (ev : GameEvent) :
      Game × Array (ObjectId × ObjectId) × Array (EffectId × EffectId) × Array ObjectId :=
    let (gCur, liveMap, effRev, matIds) := st
    if skipProposalActionScaffolding ev then st
    else
      let ro := roWith liveMap gCur
      let re := resolveProposalEffId effRev
      let queueUnreturnedLinked (curLiveMap : Array (ObjectId × ObjectId))
          (before : EventObject) (fromZ toZ : Zone) (rawSourceOnBattlefield : Bool)
          (g0 : Game) : Game :=
        if fromZ != .battlefield || toZ == .battlefield then g0
        else
          match before.id.bind g0.findObject? with
          | none => g0
          | some old =>
            let roCur := roWith curLiveMap g0
            let unret :=
              old.linkedExile.filter fun lid =>
                (g0.findObject? lid).any (·.zone == .exile) &&
                  !fullKeptStream.any fun (_, kev) =>
                    match kev with
                    | .rules _ (.zone (.moved lb _ .exile ..)) _ _ =>
                      lb.id.map roCur == some lid
                    | .rules _ (.zone (.ceasedToExist lo)) _ kb =>
                      (kb == ev.batch ||
                        (rawSourceOnBattlefield && lo.zone == .exile && lo.id == some lid)) &&
                        lo.id.map roCur == some lid
                    | _ => false
            if unret.isEmpty then g0 else g0.change (.queueLinkedExile unret)
      match ev with
      | .engine t (.materializeObject obj libPos) _ =>
        let objDeparted :=
          obj.zone != .ante &&
            ((gCur.player obj.owner).leftTheGame ||
              ((obj.zone == .stack || obj.zone == .battlefield) &&
                obj.controller.any (fun c => (gCur.player c).leftTheGame)))
        if objDeparted then st
        else
          let matIds' := if matIds.contains obj.id then matIds else matIds.push obj.id
          let objNoId := remapProposalGameObjNoId ro obj
          let (freshId, liveMap') := mintObjId gCur liveMap obj.id
          let obj' := { objNoId with id := freshId }
          (gCur.record (.engine t (.materializeObject obj' libPos)), liveMap', effRev, matIds')
      | .engine t (.nextEffectId v) _ =>
        let origNext := effectiveOrigNextEffs.getD fullIdx minPostCkptEffId
        if v > origNext then
          let rawEid : EffectId := ⟨v - 1⟩
          let (actualEid, effRev1) := ensurePostCkptEffId gCur effRev rawEid
          let nextV := max gCur.nextEffectId (actualEid.raw + 1)
          (gCur.record (.engine t (.nextEffectId nextV)), liveMap, effRev1, matIds)
        else
          let nextRulesCid? : Option EffectId := Id.run do
            for j in [fullIdx + 1 : fullKeptStream.size] do
              match fullKeptStream[j]!.2 with
              | .rules _ _ nextCause _ => return nextCause.oneShotEffectId?
              | _ => pure ()
            return none
          match nextRulesCid? with
          | some cid =>
            let (actualCid, effRev1) := ensurePostCkptEffId gCur effRev cid
            let nextV := max gCur.nextEffectId (actualCid.raw + 1)
            (gCur.record (.engine t (.nextEffectId nextV)), liveMap, effRev1, matIds)
          | none =>
            (gCur.record (.engine t (.nextEffectId (max gCur.nextEffectId v))), liveMap, effRev, matIds)
      | .engine t (.removeStackEntry oid) _ =>
        let origId := ro oid
        let gNext :=
          if gCur.stack.any (·.objectId == origId) then
            gCur.record (.engine t (.removeStackEntry origId))
          else gCur
        (gNext, liveMap, effRev, matIds)
      | .engine t (.pushStack se) _ =>
        let objId' := ro se.objectId
        if !((gCur.findObject? objId').any (·.zone == .stack) &&
            !(gCur.player se.controller).leftTheGame) then
          st
        else
          let (gCur1, se', effRev1) := ensureStackEntry ro gCur effRev se
          (gCur1.record (.engine t (.pushStack se')), liveMap, effRev1, matIds)
      | .engine t (.stackEntry oid sc) _ =>
        (gCur.record (.engine t (.stackEntry (ro oid) sc)), liveMap, effRev, matIds)
      | .engine t (.object oid oc) _ =>
        (gCur.record (.engine t (.object (ro oid) (remapProposalObjectChange ro oc))), liveMap, effRev, matIds)
      | .engine t (.continuation cc) _ =>
        let (gCur1, cc', effRev1) := ensureContinuationChange ro re gCur effRev cc
        (gCur1.record (.engine t (.continuation cc')), liveMap, effRev1, matIds)
      | .engine t (.pendingBlockerAssignments asgns) _ =>
        let asgns' := asgns.map (fun a =>
          { a with
            source := ro a.source
            toCreatures := a.toCreatures.map (fun (cid, d) => (ro cid, d)) })
        (gCur.record (.engine t (.pendingBlockerAssignments asgns')), liveMap, effRev, matIds)
      | .engine t (.priority nextP) _ =>
        let gNext :=
          if fromAction || (gCur.player gCur.priority).leftTheGame then
            let nextP' :=
              if (gCur.player nextP).leftTheGame && !gCur.livingPlayers.isEmpty then
                gCur.nextLiving nextP
              else nextP
            gCur.record (.engine t (.priority nextP'))
          else gCur
        (gNext, liveMap, effRev, matIds)
      | .engine t (.pendingPriority (some nextP)) _ =>
        let gNext :=
          if fromAction || gCur.pendingPriority.any (fun q => (gCur.player q).leftTheGame) then
            let nextP' :=
              if (gCur.player nextP).leftTheGame && !gCur.livingPlayers.isEmpty then
                gCur.nextLiving nextP
              else nextP
            gCur.record (.engine t (.pendingPriority (some nextP')))
          else gCur
        (gNext, liveMap, effRev, matIds)
      | .rules t (.zone (.moved before after fromZ toZ verb actor entersWith libPos)) cause batch =>
        let beforeBase := remapProposalEventObjNoId ro before
        let (b', remapped, hasLiveOrig) :=
          match beforeBase.id with
          | some bid =>
            let origId := ro bid
            let followed := gCur.followMoved origId
            let resolvedObj? :=
              (if followed != origId then gCur.findObject? followed else none).orElse
                (fun _ => gCur.findObject? origId)
            match resolvedObj? with
            | some origObj =>
              let liveId := origObj.id
              let bRemap :=
                if liveId == bid && origObj.zone == beforeBase.zone then beforeBase
                else { beforeBase with id := some liveId, zone := origObj.zone }
              (bRemap, liveId != bid, true)
            | none =>
              (if origId == bid then beforeBase else { beforeBase with id := some origId },
                origId != bid, false)
          | none => (beforeBase, false, true)
        if !fromAction && before.id.isSome && !hasLiveOrig then
          st
        else
          let destDeparted : Bool :=
            match toZ with
            | .outside _ => false
            | .library p | .hand p | .graveyard p =>
              (gCur.player p).leftTheGame || (gCur.player after.owner).leftTheGame
            | .battlefield | .stack =>
              (gCur.player after.owner).leftTheGame ||
                after.controller.any (fun c => (gCur.player c).leftTheGame)
            | .exile | .command | .ante =>
              (gCur.player after.owner).leftTheGame
          if destDeparted then
            st
          else
            let rawSourceOnBattlefield := fromZ == .battlefield
            let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
            let afterBase := remapProposalEventObjNoId ro after
            let (after', liveMap') :=
              if after.id == before.id then
                let lm1 :=
                  match before.id, b'.id with
                  | some bid, some liveId =>
                    let r1 := resolveProposalRevId revMap bid
                    if liveId != resolveProposalRevId liveMap r1 then
                      liveMap.push (r1, liveId)
                    else liveMap
                  | _, _ => liveMap
                ({ afterBase with id := b'.id }, lm1)
              else
                match after.id with
                | some rawAfterId =>
                  let (freshAfterId, lm1) := mintObjId gCur liveMap rawAfterId
                  ({ afterBase with id := some freshAfterId }, lm1)
                | none => (afterBase, liveMap)
            let fromZ' := if hasLiveOrig && before.id.isSome then b'.zone else fromZ
            let gCur := queueUnreturnedLinked liveMap' b' fromZ' toZ rawSourceOnBattlefield gCur
            let gCur :=
              match b'.id with
              | some oid =>
                if remapped && hasLiveOrig && fromZ' != toZ then
                  cleanupRemappedLeavingId oid cause' gCur
                else gCur
              | none => gCur
            let gNext :=
              gCur.record (.rules t (.zone (.moved b' after' fromZ' toZ verb actor entersWith libPos)) cause' batch)
            (gNext, liveMap', effRev1, matIds)
      | .rules t (.zone (.created obj ctrl)) cause batch =>
        if (gCur.player obj.owner).leftTheGame || (gCur.player ctrl).leftTheGame ||
            obj.controller.any (fun c => (gCur.player c).leftTheGame) then
          st
        else
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          let objBase := remapProposalEventObjNoId ro obj
          let (obj', liveMap') :=
            match obj.id with
            | some rawId =>
              let (freshId, lm1) := mintObjId gCur liveMap rawId
              ({ objBase with id := some freshId }, lm1)
            | none => (objBase, liveMap)
          (gCur.record (.rules t (.zone (.created obj' ctrl)) cause' batch), liveMap', effRev1, matIds)
      | .rules t (.zone (.ceasedToExist obj)) cause batch =>
        let objBase := remapProposalEventObjNoId ro obj
        match objBase.id with
        | none =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.zone (.ceasedToExist objBase)) cause' batch), liveMap, effRev1, matIds)
        | some oid =>
          let rawSourceOnBattlefield := obj.zone == .battlefield
          let origId := ro oid
          let followed := gCur.followMoved origId
          let resolvedObj? :=
            (if followed != origId then gCur.findObject? followed else none).orElse
              (fun _ => gCur.findObject? origId)
          match resolvedObj? with
          | none =>
            if fromAction then
              let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
              (gCur.record (.rules t (.zone (.ceasedToExist { objBase with id := some origId })) cause' batch),
                liveMap, effRev1, matIds)
            else st
          | some origObj =>
            let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
            let liveId := origObj.id
            let obj' :=
              if liveId == oid && origObj.zone == objBase.zone then objBase
              else { objBase with id := some liveId, zone := origObj.zone }
            let gCur := queueUnreturnedLinked liveMap obj' origObj.zone (.outside origObj.owner) rawSourceOnBattlefield gCur
            let gCur :=
              if liveId == oid then gCur
              else cleanupRemappedLeavingId liveId cause' gCur
            (gCur.record (.rules t (.zone (.ceasedToExist obj')) cause' batch), liveMap, effRev1, matIds)
      | .rules t (.player (.shuffled p newOrder)) cause batch =>
        let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
        let mappedOrder := newOrder.map ro
        let curLib := (gCur.player p).library
        let kept := mappedOrder.filter curLib.contains
        let missing := curLib.filter (!kept.contains ·)
        (gCur.record (.rules t (.player (.shuffled p (kept ++ missing))) cause' batch), liveMap, effRev1, matIds)
      | .rules t (.player (.revealed p cardIds)) cause batch =>
        let mappedIds := cardIds.map ro
        let validIds :=
          if fromAction then mappedIds.filter (fun cid => (gCur.findObject? cid).isSome)
          else mappedIds.filter (inLibraryObjs gCur.objects ·)
        if validIds.isEmpty then st
        else
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.player (.revealed p validIds)) cause' batch), liveMap, effRev1, matIds)
      | .rules t (.player (.lookedAt p cardIds)) cause batch =>
        let mappedIds := cardIds.map ro
        let validIds :=
          if fromAction then mappedIds.filter (fun cid => (gCur.findObject? cid).isSome)
          else mappedIds.filter (inLibraryObjs gCur.objects ·)
        if validIds.isEmpty then st
        else
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.player (.lookedAt p validIds)) cause' batch), liveMap, effRev1, matIds)
      | .rules t (.player (.becameMonarch heir prev)) cause batch =>
        if (gCur.player heir).leftTheGame && gCur.livingPlayers.isEmpty then st
        else
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          let gNext :=
            if (gCur.player heir).leftTheGame then
              let heir' :=
                if gCur.stillInGame gCur.activePlayer && gCur.activePlayer != heir then
                  gCur.activePlayer
                else if !gCur.isSharedTurnFinalSeat then
                  gCur.nextLiving gCur.activePlayer
                else
                  gCur.nextLiving heir
              gCur.record (.rules t (.player (.becameMonarch heir' prev)) cause' batch)
            else
              gCur.record (.rules t (.player (.becameMonarch heir prev)) cause' batch)
          (gNext, liveMap, effRev1, matIds)
      | .rules t (.player pe) cause batch =>
        let skipManaAdded :=
          match pe with
          | .manaAdded p _ => (gCur.player p).leftTheGame
          | _ => false
        if skipManaAdded then st
        else
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          let pe' : PlayerEvent :=
            match pe with
            | .manaAdded p units =>
              .manaAdded p (units.map (fun u => { u with source := u.source.map ro }))
            | .manaSpent p units fo =>
              .manaSpent p (units.map (fun u => { u with source := u.source.map ro })) (fo.map ro)
            | .manaEmptied p units kept =>
              .manaEmptied p (units.map (fun u => { u with source := u.source.map ro })) kept
            | .scried p top bottom l a => .scried p (top.map ro) (bottom.map ro) l a
            | .surveilled p top gy l a => .surveilled p (top.map ro) (gy.map ro) l a
            | .searched p lo found => .searched p lo (found.map ro)
            | .proliferated p perms pls => .proliferated p (perms.map ro) pls
            | .ringTempted p bearer stage => .ringTempted p (bearer.map ro) stage
            | .optionalOnceActed p src => .optionalOnceActed p (ro src)
            | other => other
          (gCur.record (.rules t (.player pe') cause' batch), liveMap, effRev1, matIds)
      | .rules t (.permanent (.unattached att fromHost)) cause batch =>
        let att' := remapProposalEventObj ro att
        let fromHost' := ro fromHost
        if att'.id.isNone || (att'.id.bind gCur.findObject?).any (·.attachedTo == some fromHost') then
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.permanent (.unattached att' fromHost')) cause' batch), liveMap, effRev1, matIds)
        else st
      | .rules t (.permanent pe) cause batch =>
        let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
        let pe' : PermanentEvent :=
          match pe with
          | .tapped eo d => .tapped (remapProposalEventObj ro eo) d
          | .untapped eo => .untapped (remapProposalEventObj ro eo)
          | .phasedOut eo i => .phasedOut (remapProposalEventObj ro eo) i
          | .phasedIn eo i => .phasedIn (remapProposalEventObj ro eo) i
          | .transformed eo b => .transformed (remapProposalEventObj ro eo) b
          | .turnedFaceUp eo => .turnedFaceUp (remapProposalEventObj ro eo)
          | .turnedFaceDown eo => .turnedFaceDown (remapProposalEventObj ro eo)
          | .counters (.object eo) k d a => .counters (.object (remapProposalEventObj ro eo)) k d a
          | .counters (.player p) k d a => .counters (.player p) k d a
          | .attached att host prev => .attached (remapProposalEventObj ro att) (ro host) (prev.map ro)
          | .unattached att fh => .unattached (remapProposalEventObj ro att) (ro fh)
          | .designation eo d v => .designation (remapProposalEventObj ro eo) d v
        (gCur.record (.rules t (.permanent pe') cause' batch), liveMap, effRev1, matIds)
      | .rules t (.damage de) cause batch =>
        let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
        let remapRecp : DamageRecipient → DamageRecipient
          | .permanent eo => .permanent (remapProposalEventObj ro eo)
          | .battle eo => .battle (remapProposalEventObj ro eo)
          | .player p => .player p
        let de' : DamageEvent :=
          match de with
          | .dealt pkts =>
            .dealt (pkts.map (fun pkt =>
              { pkt with
                source := remapProposalEventObj ro pkt.source
                recipient := remapRecp pkt.recipient }))
          | .marked oid amt => .marked (ro oid) amt
          | .markedCleared oids => .markedCleared (oids.map ro)
          | .prevented src recp amt =>
            .prevented (remapProposalEventObj ro src) (remapRecp recp) amt
        (gCur.record (.rules t (.damage de') cause' batch), liveMap, effRev1, matIds)
      | .rules t (.cast ce) cause batch =>
        match ce with
        | .abilityActivated ability source player kind =>
          if (gCur.player player).leftTheGame then st
          else
            let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
            let source' := remapProposalEventObj ro source
            let (ability', liveMap') :=
              match kind with
              | .nonMana .. =>
                if !matIds.contains ability then
                  mintObjId gCur liveMap ability
                else
                  (ro ability, liveMap)
              | .mana .. => (ro ability, liveMap)
            (gCur.record (.rules t (.cast (.abilityActivated ability' source' player kind)) cause' batch),
              liveMap', effRev1, matIds)
        | .proposed obj p fz way =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.cast (.proposed (ro obj) p fz way)) cause' batch), liveMap, effRev1, matIds)
        | .announced obj modes x costs =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          let costs' := costs.map fun
            | .teamwork ids => .teamwork (ids.map ro)
            | .behold id => .behold (ro id)
            | .sacrifice id => .sacrifice (ro id)
            | .discard id => .discard (ro id)
            | .sneak ret atk => .sneak (ro ret) (atk.map (remapProposalAttackTarget ro))
            | c => c
          (gCur.record (.rules t (.cast (.announced (ro obj) modes x costs')) cause' batch), liveMap, effRev1, matIds)
        | .targeted obj tgts div sk =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.cast (.targeted (ro obj) (tgts.map (remapProposalTarget ro)) div sk)) cause' batch),
            liveMap, effRev1, matIds)
        | .spellCast eo p fz =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.cast (.spellCast (remapProposalEventObj ro eo) p fz)) cause' batch),
            liveMap, effRev1, matIds)
      | .rules t (.triggerQueue tqe) cause batch =>
        match tqe with
        | .putOnStack stackObj source ctrl spec =>
          if (gCur.player ctrl).leftTheGame then st
          else
            let source' := remapProposalEventObj ro source
            let (gCur1, spec', effRev1) := ensureStackTriggerSpec ro gCur effRev spec
            let (cause', effRev2) := ensureRulesCause ro gCur1 effRev1 cause
            let (freshStackObj, liveMap') := mintObjId gCur1 liveMap stackObj
            (gCur1.record (.rules t (.triggerQueue (.putOnStack freshStackObj source' ctrl spec')) cause' batch),
              liveMap', effRev2, matIds)
        | .triggered src ctrl ab orig =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.triggerQueue (.triggered (remapProposalEventObj ro src) ctrl ab orig)) cause' batch),
            liveMap, effRev1, matIds)
        | .modeChosen src mode lt =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.triggerQueue (.modeChosen (ro src) mode lt)) cause' batch),
            liveMap, effRev1, matIds)
      | .rules t (.stackObject soe) cause batch =>
        match soe with
        | .copied original copy ctrl =>
          if (gCur.player ctrl).leftTheGame then st
          else
            let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
            let original' := ro original
            let copyBase := remapProposalEventObjNoId ro copy
            let (copy', liveMap') :=
              match copy.id with
              | some rawCopyId =>
                let (freshCopyId, lm1) := mintObjId gCur liveMap rawCopyId
                ({ copyBase with id := some freshCopyId }, lm1)
              | none => (copyBase, liveMap)
            (gCur.record (.rules t (.stackObject (.copied original' copy' ctrl)) cause' batch),
              liveMap', effRev1, matIds)
        | .resolved eo nth sid ab =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.stackObject (.resolved (remapProposalEventObj ro eo) nth (sid.map ro) ab)) cause' batch),
            liveMap, effRev1, matIds)
        | .removedOnResolution eo =>
          let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
          (gCur.record (.rules t (.stackObject (.removedOnResolution (remapProposalEventObj ro eo))) cause' batch),
            liveMap, effRev1, matIds)
      | .rules t (.combat cbe) cause batch =>
        let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
        let cbe' : CombatEvent :=
          match cbe with
          | .attackersDeclared p decls =>
            .attackersDeclared p (decls.map (fun (eo, atgt) =>
              (remapProposalEventObj ro eo, remapProposalAttackTarget ro atgt)))
          | .becameAttacking eo atgt =>
            .becameAttacking (remapProposalEventObj ro eo) (remapProposalAttackTarget ro atgt)
          | .blockersDeclared p decls =>
            .blockersDeclared p (decls.map (fun (eo, aid) => (remapProposalEventObj ro eo, ro aid)))
          | .becameBlocked eo blks =>
            .becameBlocked (remapProposalEventObj ro eo) (blks.map ro)
          | .remainedUnblocked eo => .remainedUnblocked (remapProposalEventObj ro eo)
          | .damageAssigned fs fa asgns =>
            .damageAssigned fs fa (asgns.map (fun a =>
              { a with
                source := ro a.source
                toCreatures := a.toCreatures.map (fun (cid, d) => (ro cid, d)) }))
          | .removedFromCombat eo => .removedFromCombat (remapProposalEventObj ro eo)
        (gCur.record (.rules t (.combat cbe') cause' batch), liveMap, effRev1, matIds)
      | .rules t (.continuousEffect cee) cause batch =>
        let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
        let re1 := resolveProposalEffId effRev1
        match cee with
        | .created eid spec =>
          let spec' := remapProposalEffSpec ro spec
          let (freshEid, effRev2) := ensurePostCkptEffId gCur effRev1 eid
          (gCur.record (.rules t (.continuousEffect (.created freshEid spec')) cause' batch),
            liveMap, effRev2, matIds)
        | .expired eid spec? =>
          let spec?' := spec?.map (remapProposalEffSpec ro)
          (gCur.record (.rules t (.continuousEffect (.expired (re1 eid) spec?')) cause' batch),
            liveMap, effRev1, matIds)
      | .rules t (.delayedTrigger dte) cause batch =>
        match dte with
        | .created dt =>
          if (gCur.player dt.controller).leftTheGame then st
          else
            let (gCur1, dt', effRev1) := ensureDelayedTrigger ro gCur effRev dt
            let (cause', effRev2) := ensureRulesCause ro gCur1 effRev1 cause
            (gCur1.record (.rules t (.delayedTrigger (.created dt')) cause' batch),
              liveMap, effRev2, matIds)
        | .consumed dt =>
          let (gCur1, dt', effRev1) := ensureDelayedTrigger ro gCur effRev dt
          let (cause', effRev2) := ensureRulesCause ro gCur1 effRev1 cause
          (gCur1.record (.rules t (.delayedTrigger (.consumed dt')) cause' batch),
            liveMap, effRev2, matIds)
        | .expired dt =>
          let (gCur1, dt', effRev1) := ensureDelayedTrigger ro gCur effRev dt
          let (cause', effRev2) := ensureRulesCause ro gCur1 effRev1 cause
          (gCur1.record (.rules t (.delayedTrigger (.expired dt')) cause' batch),
            liveMap, effRev2, matIds)
      | .rules t r cause batch =>
        let (cause', effRev1) := ensureRulesCause ro gCur effRev cause
        (gCur.record (.rules t r cause' batch), liveMap, effRev1, matIds)
      | _ =>
        (gCur.record ev, liveMap, effRev, matIds)
  stepEvent fullIdx fromAction st ev

/-- Shared core for CR 734.1 / 734.2 kept-stream replay (`restoreProposalCheckpointWith`
and `PendingReplacement.continueCheckpointReplay`). Replays `remainingStream`,
draining local non-paused `pendingReplacement` continuations immediately after
each `runBatch` and stopping only when `Pending.chooseReplacement` or
`Pending.chooseLegend` opens, chaining any remaining slice via
`PendingReplacement.continueCheckpointReplay` (CR 603.2c / 610.3 / 616.1 /
734.1–734.2 / 800.4a). -/
def replayKeptStreamCore (g : Game)
    (remainingStream fullKeptStream : Array (Bool × GameEvent))
    (revMap : Array (ObjectId × ObjectId))
    (liveObjMap : Array (ObjectId × ObjectId) := #[])
    (effRevMap : Array (EffectId × EffectId) := #[])
    (minPostCkptEffId : Nat := 0)
    (suppressInteractive : Bool := false)
    (keptOrigNextEffs : Array Nat := #[])
    (runBatch : Game → (Game → Game) → Game := fun g0 f => g0.withBatchCore none f) : Game := Id.run do
  let stepOrigNextEff (cur : Nat) (ev : GameEvent) : Nat :=
    match ev with
    | .engine _ (.nextEffectId v) _ => v
    | .rules _ r cause _ =>
      let cur1 :=
        match r with
        | .continuousEffect (.created eid _)
        | .continuousEffect (.expired eid _) => max cur (eid.raw + 1)
        | _ => cur
      match cause.oneShotEffectId? with
      | some eid => max cur1 (eid.raw + 1)
      | none => cur1
    | _ => cur
  let effectiveOrigNextEffs : Array Nat :=
    if keptOrigNextEffs.size >= fullKeptStream.size then keptOrigNextEffs
    else Id.run do
      let mut arr : Array Nat := #[]
      let mut cur : Nat := minPostCkptEffId
      for (_, kev) in fullKeptStream do
        arr := arr.push cur
        cur := stepOrigNextEff cur kev
      return arr
  let stepEvent := replayKeptStreamStepEvent fullKeptStream revMap minPostCkptEffId effectiveOrigNextEffs
  let prefixLen := fullKeptStream.size - min remainingStream.size fullKeptStream.size
  let mut materializedIds : Array ObjectId := Id.run do
    let mut ids : Array ObjectId := #[]
    for i in [0:prefixLen] do
      if let (_, .engine _ (.materializeObject obj _) _) := fullKeptStream[i]! then
        if !ids.contains obj.id then
          ids := ids.push obj.id
    return ids
  let mut mutLiveMap := liveObjMap
  let mut mutEffMap := effRevMap
  let mut gAcc := g
  let mut idx := 0
  while idx < remainingStream.size do
    if isProposalReplayPaused gAcc then
      break
    let fullIdx0 := prefixLen + idx
    let (fromAct0, ev0) := remainingStream[idx]!
    match ev0 with
    | .engine .. =>
      let (gNext, l1, e1, m1) :=
        stepEvent fullIdx0 fromAct0 (gAcc, mutLiveMap, mutEffMap, materializedIds) ev0
      gAcc := gNext
      mutLiveMap := l1
      mutEffMap := e1
      materializedIds := m1
      idx := idx + 1
    | .rules _ _ _ none =>
      let l0 := mutLiveMap
      let e0 := mutEffMap
      let m0 := materializedIds
      let (l1, e1, m1) :=
        (gAcc.withBatchCoreReturn none
          (fun g0 =>
            let (g1, l', e', m') := stepEvent fullIdx0 fromAct0 (g0, l0, e0, m0) ev0
            (g1, (l', e', m')))
          (suppressInteractive := true)).2
      gAcc := runBatch gAcc (fun g0 => (stepEvent fullIdx0 fromAct0 (g0, l0, e0, m0) ev0).1)
      mutLiveMap := l1
      mutEffMap := e1
      materializedIds := m1
      if !(suppressInteractive || gAcc.over || gAcc.suppressInteractiveReplay) then
        gAcc := gAcc.drainLocalPendingReplacement
      idx := idx + 1
    | .rules _ _ _ (some bid) =>
      let mut grp : Array (Nat × Bool × GameEvent) := #[(fullIdx0, fromAct0, ev0)]
      idx := idx + 1
      while idx < remainingStream.size do
        let fullIdxCur := prefixLen + idx
        let (fa, nextEv) := remainingStream[idx]!
        match nextEv with
        | .rules _ _ _ (some bid2) =>
          if bid2 == bid then
            grp := grp.push (fullIdxCur, fa, nextEv)
            idx := idx + 1
          else break
        | .rules _ _ _ none => break
        | .engine .. =>
          -- Keep interleaved log/engine changes inside the batch if the next rules event has `some bid`.
          let nextRulesMatches : Bool := Id.run do
            let mut j := idx + 1
            while j < remainingStream.size do
              match remainingStream[j]!.2 with
              | .engine .. => j := j + 1
              | .rules _ _ _ (some bid2) => return bid2 == bid
              | .rules _ _ _ none => return false
            return false
          if nextRulesMatches then
            grp := grp.push (fullIdxCur, fa, nextEv)
            idx := idx + 1
          else break
      let l0 := mutLiveMap
      let e0 := mutEffMap
      let m0 := materializedIds
      let grpSnap := grp
      let (l1, e1, m1) :=
        (gAcc.withBatchCoreReturn none
          (fun g0 =>
            let (g1, l', e', m') :=
              grpSnap.foldl (fun st (fi, fa, e) => stepEvent fi fa st e) (g0, l0, e0, m0)
            (g1, (l', e', m')))
          (suppressInteractive := true)).2
      gAcc := runBatch gAcc (fun g0 =>
        (grpSnap.foldl (fun st (fi, fa, e) => stepEvent fi fa st e) (g0, l0, e0, m0)).1)
      mutLiveMap := l1
      mutEffMap := e1
      materializedIds := m1
      if !(suppressInteractive || gAcc.over || gAcc.suppressInteractiveReplay) then
        gAcc := gAcc.drainLocalPendingReplacement
  if isProposalReplayPaused gAcc &&
      (idx < remainingStream.size || gAcc.players.any (·.leftTheGame)) then
    let remSlice := remainingStream.extract idx remainingStream.size
    gAcc := gAcc.chainPendingReplacement
      (.continueCheckpointReplay remSlice fullKeptStream revMap mutLiveMap mutEffMap
        minPostCkptEffId
        (suppressInteractive || gAcc.over || gAcc.suppressInteractiveReplay)
        effectiveOrigNextEffs)
  return gAcc

private inductive ProposalSliceUnit where
  | action (idx : Nat) (kind : ProposalActionKind) (events : Array GameEvent)
  | standalone (idx : Nat) (event : GameEvent)

/-- Restore `g` to its saved `proposalCheckpoint`, then reapply whole CR 734.1
irreversible mana abilities and cost actions from the undone proposal slice
(actions that moved cards to a library, moved cards from a library to any zone
other than `.stack`, shuffled a library, revealed cards from a library, or
reordered library cards via scry/surveil, plus upstream mana abilities whose
FIFO mana paid for an unreversed mana ability), as well as any unbracketed
irreversible library events (CR 734.1–734.2). -/
def reverseToProposalCheckpointCore? (g : Game)
    (runBatch : Game → (Game → Game) → Game := fun g0 f => g0.withBatchCore none f)
    (flushLinked : Game → Game := id) :
    Except String Game := do
  let some ckpt := g.proposalCheckpoint
    | throw "No proposal checkpoint to reverse (CR 734.1)"
  pure <| Id.run do
  let slice := g.events.extract (min ckpt.eventsSize g.events.size) g.events.size
  let isLibZone : Zone → Bool
    | .library _ => true
    | _ => false
  let setInLib (ids : Array ObjectId) (oid : ObjectId) (inLib : Bool) : Array ObjectId :=
    if inLib then
      if ids.contains oid then ids else ids.push oid
    else
      ids.filter (· != oid)
  let resolveRevId := resolveProposalRevId
  -- 1. Partition `slice` into outermost bracketed proposal actions and standalone
  --    events, keeping mid-proposal player departures outside `depth > 0` `.action`
  --    brackets so a concession during a paused cost/mana replacement prompt stays
  --    irreversible without retaining the proposer's unfinished cost action
  --    (CR 104.3a / 610.3 / 734.1 / 800.4a).
  let firstDepIdx? : Option Nat := slice.findIdx? fun ev =>
    match ev with
    | .rules _ (.player (.lost ..)) _ _
    | .rules _ (.player (.leftGame ..)) _ _
    | .rules _ (.player (.gameEnded ..)) _ _ => true
    | _ => false
  let isProposalResumeEvent : GameEvent → Bool
    | .engine _ (.beginProposalAction _)
    | .engine _ .endProposalAction
    | .engine _ (.proposal _)
    | .engine _ (.proposalChanges _)
    | .engine _ (.proposedSpell (some _))
    | .engine _ (.stackEntry ..)
    | .rules _ (.cast _) _ _
    | .rules _ _ (.costPayment ..) _
    | .rules _ (.player (.manaAdded ..)) _ _
    | .rules _ (.player (.manaSpent ..)) _ _ => true
    | _ => false
  let isProposalPromptPending : Pending → Bool
    | .none | .chooseReplacement .. | .chooseLegend ..
    | .resolveRandom (.orderInto ..) => false
    | _ => true
  let (units, depStIdxs) : Array ProposalSliceUnit × Array Nat := Id.run do
    let mut out : Array ProposalSliceUnit := #[]
    let mut depSt : Array Nat := #[]
    let mut depth : Nat := 0
    let mut curActIdx : Nat := 0
    let mut curKind : ProposalActionKind := .costAction
    let mut curEvs : Array GameEvent := #[]
    let mut nextStIdx : Nat := 0
    let depTriggerBatches : Array BatchId := Id.run do
      let mut bs : Array BatchId := #[]
      let mut curPaused : Option BatchId := ckpt.currentBatch.map Prod.fst
      for sEv in slice do
        match sEv with
        | .engine _ (.pauseBatch pb ..) _ =>
          curPaused := some pb
        | .engine _ .clearPausedBatch _ =>
          curPaused := none
        | .rules _ (.player (.leftGame ..)) _ (some b) =>
          if !bs.contains b then bs := bs.push b
        | .rules _ (.player (.lost _ reason)) _ (some b) =>
          if reason != .conceded && curPaused != some b && !bs.contains b then
            bs := bs.push b
        | .rules _ (.player (.gameEnded ..)) _ (some b) =>
          if curPaused != some b && !bs.contains b then
            bs := bs.push b
        | _ => pure ()
      return bs
    let mut nonDepBatches : Array BatchId :=
      match ckpt.currentBatch with
      | some (b, _) => if depTriggerBatches.contains b then #[] else #[b]
      | none => #[]
    let mut inDepSpan : Bool := false
    let mut depOuterDepth : Nat := 0
    let mut pendingDepPlayers : Array PlayerId := #[]
    let mut gameEndedInDep : Bool := false
    let mut depReplacementPending : Bool := false
    let mut depPausedBatch? : Option BatchId := none
    for idx in [0:slice.size] do
      let ev := slice[idx]!
      if firstDepIdx?.any (idx ≥ ·) then
        match ev with
        | .rules _ (.player (.lost p ..)) _ _ =>
          inDepSpan := true
          if !pendingDepPlayers.contains p then
            pendingDepPlayers := pendingDepPlayers.push p
        | .rules _ (.player (.leftGame p)) _ _ =>
          inDepSpan := true
          pendingDepPlayers := pendingDepPlayers.filter (· != p)
        | .rules _ (.player (.gameEnded ..)) _ _ =>
          inDepSpan := true
          gameEndedInDep := true
          pendingDepPlayers := #[]
        | .engine _ (.removeStackEntry _) =>
          inDepSpan := true
        | _ => pure ()
        let blockedByDepRep :=
          depPausedBatch?.isSome ||
            (depReplacementPending &&
              match ev with
              | .rules _ _ (.costPayment ..) _ => true
              | _ => false)
        if inDepSpan && depOuterDepth == 0 && pendingDepPlayers.isEmpty && !gameEndedInDep &&
            !blockedByDepRep && isProposalResumeEvent ev then
          inDepSpan := false
          depReplacementPending := false
      if inDepSpan then
        if depth > 0 && !curEvs.isEmpty then
          out := out.push (.action curActIdx curKind curEvs)
          curEvs := #[]
        out := out.push (.standalone nextStIdx ev)
        depSt := depSt.push nextStIdx
        nextStIdx := nextStIdx + 1
        match ev with
        | .engine _ (.pauseBatch bid ..) =>
          if !nonDepBatches.contains bid then
            depPausedBatch? := some bid
        | .engine _ .clearPausedBatch =>
          depPausedBatch? := none
        | .engine _ (.continuation (.pushOuterPendingReplacement _)) =>
          depOuterDepth := depOuterDepth + 1
        | .engine _ (.continuation .popOuterPendingReplacement) =>
          if depOuterDepth > 0 then
            depOuterDepth := depOuterDepth - 1
          if depOuterDepth == 0 && pendingDepPlayers.isEmpty && !gameEndedInDep &&
              !depReplacementPending && depPausedBatch?.isNone then
            inDepSpan := false
        | .engine _ (.pending p) =>
          match p with
          | .chooseReplacement .. | .chooseLegend .. =>
            depReplacementPending := true
          | _ =>
            depReplacementPending := false
            if depOuterDepth == 0 && pendingDepPlayers.isEmpty && !gameEndedInDep &&
                depPausedBatch?.isNone && isProposalPromptPending p then
              inDepSpan := false
        | _ => pure ()
      else
        if let some b := ev.batch then
          if !depTriggerBatches.contains b && !nonDepBatches.contains b then
            nonDepBatches := nonDepBatches.push b
        match ev with
        | .engine _ (.pauseBatch b ..) =>
          if !depTriggerBatches.contains b && !nonDepBatches.contains b then
            nonDepBatches := nonDepBatches.push b
        | _ => pure ()
        match ev.change with
        | .engine (.beginProposalAction kind) =>
          if depth == 0 then
            curKind := kind
            curEvs := #[]
          depth := depth + 1
        | .engine .endProposalAction =>
          if depth > 0 then
            depth := depth - 1
            if depth == 0 then
              out := out.push (.action curActIdx curKind curEvs)
              curActIdx := curActIdx + 1
              curEvs := #[]
        | _ =>
          if depth > 0 then
            curEvs := curEvs.push ev
          else
            out := out.push (.standalone nextStIdx ev)
            nextStIdx := nextStIdx + 1
    if depth > 0 && !curEvs.isEmpty then
      out := out.push (.action curActIdx curKind curEvs)
    return (out, depSt)
  -- 2. Chronological simulation of `liveLibIds` and FIFO tagged mana pools to
  --    identify library-irreversible actions/events and upstream mana dependencies.
  let mut liveLibIds : Array ObjectId :=
    ckpt.objects.foldl (fun acc o =>
      if isLibZone o.zone then acc.push o.id else acc) #[]
  let mut pools : Array (Array (ManaUnit × Option Nat)) :=
    ckpt.players.map (fun pl => pl.manaPool.units.map (·, none))
  let mut actionKinds : Array (Nat × ProposalActionKind) := #[]
  let mut irrevActs : Array Nat := #[]
  let mut irrevStIdxs : Array Nat := depStIdxs
  let mut deps : Array (Nat × Nat) := #[]
  let markIrrev (act? : Option Nat) (stIdx? : Option Nat)
      (ia : Array Nat) (ist : Array Nat) : Array Nat × Array Nat :=
    match act?, stIdx? with
    | some a, _ => (if ia.contains a then ia else ia.push a, ist)
    | none, some s => (ia, if ist.contains s then ist else ist.push s)
    | none, none => (ia, ist)
  for u in units do
    let (act?, st?, evs) : Option Nat × Option Nat × Array GameEvent :=
      match u with
      | .action idx _ es => (some idx, none, es)
      | .standalone idx ev => (none, some idx, #[ev])
    if let .action idx kind _ := u then
      if !actionKinds.any (·.1 == idx) then
        actionKinds := actionKinds.push (idx, kind)
    for ev in evs do
      match ev with
      | .rules _ (.zone (.moved before after _ (.library _) ..)) _ _ =>
        if let some bid := before.id then
          liveLibIds := setInLib liveLibIds bid false
        if let some aid := after.id.orElse (fun _ => before.id) then
          liveLibIds := setInLib liveLibIds aid true
        let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
        irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.zone (.moved before after (.library _) toZone ..)) _ _ =>
        if let some bid := before.id then
          liveLibIds := setInLib liveLibIds bid false
        if let some aid := after.id then
          liveLibIds := setInLib liveLibIds aid false
        if toZone != .stack then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.zone (.moved before after ..)) _ _ =>
        if let some bid := before.id then
          liveLibIds := setInLib liveLibIds bid false
        if let some aid := after.id then
          liveLibIds := setInLib liveLibIds aid false
      | .rules _ (.zone (.created obj _)) _ _ =>
        if let some oid := obj.id then
          liveLibIds := setInLib liveLibIds oid false
      | .rules _ (.zone (.ceasedToExist obj)) cause _ =>
        if let some oid := obj.id then
          liveLibIds := setInLib liveLibIds oid false
        if act?.isNone &&
            (cause == .gameRule .triggeredAbility || cause == .gameRule .noLegalMode) &&
            !obj.id.any (fun oid => g.proposedSpell.any (·.spellId == oid)) then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .engine _ (.materializeObject obj _) =>
        liveLibIds := setInLib liveLibIds obj.id (isLibZone obj.zone)
      | .rules _ (.cast (.targeted oid ..)) _ _
      | .rules _ (.cast (.announced oid ..)) _ _
      | .engine _ (.stackEntry oid _)
      | .engine _ (.object oid (.abilityEffect _)) =>
        if act?.isNone && !g.proposedSpell.any (·.spellId == oid) then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.triggerQueue (.modeChosen ..)) _ _ =>
        if act?.isNone then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.player (.shuffled ..)) _ _ =>
        let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
        irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.player (.scried _ top bottom ..)) _ _ =>
        if !top.isEmpty || !bottom.isEmpty then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.player (.surveilled _ top gy ..)) _ _ =>
        if !top.isEmpty || !gy.isEmpty then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.player (.revealed _ cardIds)) _ _ =>
        if !(cardIds.filter liveLibIds.contains).isEmpty then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.player (.lookedAt _ cardIds)) _ _ =>
        if !(cardIds.filter liveLibIds.contains).isEmpty then
          let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
          irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.player (.searched ..)) _ _
      | .rules _ (.player (.drawFromEmptyAttempted _)) _ _ =>
        let (ia, ist) := markIrrev act? st? irrevActs irrevStIdxs
        irrevActs := ia; irrevStIdxs := ist
      | .rules _ (.player (.manaAdded p added)) _ _ =>
        if h : p.idx < pools.size then
          let curPool := pools[p.idx]
          pools := pools.set! p.idx (curPool ++ added.map (·, act?))
      | .rules _ (.player (.manaSpent p spent _)) _ _ =>
        if h : p.idx < pools.size then
          let mut curPool := pools[p.idx]
          for mu in spent do
            match curPool.findIdx? (fun (u', _) => u' == mu) with
            | some k =>
              let (_, prodAct?) := curPool[k]!
              curPool := curPool.eraseIdx! k
              match act?, prodAct? with
              | some cAct, some pAct =>
                if cAct != pAct && !deps.contains (cAct, pAct) then
                  deps := deps.push (cAct, pAct)
              | _, _ => pure ()
            | none =>
              match act?, mu.source with
              | some cAct, some srcId =>
                for (pAct, pKind) in actionKinds do
                  if pAct < cAct && pKind == .manaAbility (some srcId) && !deps.contains (cAct, pAct) then
                    deps := deps.push (cAct, pAct)
              | _, _ => pure ()
          pools := pools.set! p.idx curPool
      | .rules _ (.player (.manaEmptied p _ keptColorless)) _ _ =>
        if h : p.idx < pools.size then
          let curPool := pools[p.idx]
          let nextPool :=
            if keptColorless then
              curPool.map (fun (u', tag) => ({ u' with mana := .colorless }, tag))
            else #[]
          pools := pools.set! p.idx nextPool
      | _ => pure ()
  -- Transitively close `irrevActs` over upstream mana dependencies.
  let mut changed := true
  while changed do
    changed := false
    for (cAct, pAct) in deps do
      if irrevActs.contains cAct && !irrevActs.contains pAct then
        irrevActs := irrevActs.push pAct
        changed := true
  -- 3. Build `revIdMap` from `ZoneEvent.moved` in REVERSED units only so any
  --    kept move or departure referencing a post-proposal `ObjectId` remaps cleanly.
  let stepOrigNextEff (cur : Nat) (ev : GameEvent) : Nat :=
    match ev with
    | .engine _ (.nextEffectId v) _ => v
    | .rules _ r cause _ =>
      let cur1 :=
        match r with
        | .continuousEffect (.created eid _)
        | .continuousEffect (.expired eid _) => max cur (eid.raw + 1)
        | _ => cur
      match cause.oneShotEffectId? with
      | some eid => max cur1 (eid.raw + 1)
      | none => cur1
    | _ => cur
  let mut revIdMap : Array (ObjectId × ObjectId) := #[]
  let mut keptStream : Array (Bool × GameEvent) := #[]
  let mut keptOrigNextEffs : Array Nat := #[]
  let mut origNextEff : Nat := ckpt.nextEffectId
  for u in units do
    let isKept :=
      match u with
      | .action idx _ _ => irrevActs.contains idx
      | .standalone idx _ => irrevStIdxs.contains idx
    let evs := match u with | .action _ _ es => es | .standalone _ ev => #[ev]
    let fromAct := match u with | .action .. => true | .standalone .. => false
    for ev in evs do
      if isKept && !skipProposalActionScaffolding ev then
        keptStream := keptStream.push (fromAct, ev)
        keptOrigNextEffs := keptOrigNextEffs.push origNextEff
      else if !isKept then
        match ev with
        | .rules _ (.zone (.moved before after ..)) _ _ =>
          match before.id, after.id with
          | some bid, some aid => revIdMap := revIdMap.push (aid, resolveRevId revIdMap bid)
          | _, _ => pure ()
        | _ => pure ()
      origNextEff := stepOrigNextEff origNextEff ev
  let finalRevMap := revIdMap
  let finalKeptStream := keptStream
  let finalKeptOrigNextEffs := keptOrigNextEffs
  let wasGameOver := g.over
  let wasSuppressed := g.suppressInteractiveReplay
  let quietReplay := wasGameOver || wasSuppressed
  let mut gAcc := g.restoreProposalCheckpoint ckpt
  let needsIsolation :=
    !keptStream.isEmpty ||
      (!quietReplay && !gAcc.over && !gAcc.suppressInteractiveReplay && gAcc.postCastCleanup.isSome &&
        (gAcc.pending != .none || gAcc.currentBatch.isSome || gAcc.pendingReplacement.isSome))
  if !needsIsolation then
    return gAcc
  let findPausedCloseFor? (target : BatchId) : PendingReplacement → Option Nat :=
    let rec go : PendingReplacement → Option Nat
      | .closeBatch b s => if b == target then some s else none
      | .seq a b => go a <|> go b
      | _ => none
    go
  let findEarliestIdx (g0 : Game) (target : BatchId) : Nat := Id.run do
    for i in [0:g0.events.size] do
      match g0.events[i]! with
      | .engine _ (.pauseBatch bid ..) _ =>
        if bid == target then return i
      | e =>
        if e.batch == some target then return i
    return g0.events.size
  let ckptPausedBatch? :=
    match gAcc.currentBatch with
    | some (origBid, origCause) =>
      let wasDiscard := gAcc.discardBatch.map Prod.fst == some origBid
      let origStartIdx :=
        if wasDiscard then
          (gAcc.discardBatch.map Prod.snd).getD 0
        else
          ((gAcc.pendingReplacement.bind (findPausedCloseFor? origBid)).orElse
            (fun _ => gAcc.outerPendingReplacements.findSomeRev? (findPausedCloseFor? origBid)))
            |>.getD (findEarliestIdx gAcc origBid)
      some (origBid, origStartIdx, wasDiscard, origCause, gAcc.openBatchObjects,
        gAcc.openBatchPlayers, gAcc.openBatchEffects, gAcc.openBatchPending, gAcc.openBatchStack)
    | none => none
  let ckptQueuedLinkedExile := gAcc.queuedLinkedExile
  let ckptPending := gAcc.pending
  let ckptCont? := gAcc.pendingReplacement
  if ckptPausedBatch?.isSome then
    gAcc := gAcc.change .clearPausedBatch
  if !ckptQueuedLinkedExile.isEmpty then
    gAcc := gAcc.change .clearQueuedLinkedExile
  if ckptPending != .none then
    gAcc := gAcc.change (.pending .none)
  if ckptCont?.isSome then
    gAcc := gAcc.change (.pendingReplacement none)
  if !keptStream.isEmpty then
    gAcc := gAcc.replayKeptStreamCore keptStream finalKeptStream finalRevMap
      (minPostCkptEffId := ckpt.nextEffectId)
      (suppressInteractive := quietReplay)
      (keptOrigNextEffs := finalKeptOrigNextEffs)
      (runBatch := if quietReplay then
        (fun g0 f =>
          (g0.withBatchCore none f (suppressInteractive := true)).flushQueuedLinkedExileFwd
            (suppressInteractive := true))
      else runBatch)
    if !wasGameOver && !isProposalReplayPaused gAcc && gAcc.players.any (·.leftTheGame) then
      gAcc := gAcc.reconcilePostReplayDeparturesFwd (suppressInteractive := quietReplay)
  if wasGameOver || gAcc.over then
    if !isProposalReplayPaused gAcc && ckptPausedBatch?.isNone && !ckptQueuedLinkedExile.isEmpty then
      gAcc := gAcc.change (.queueLinkedExile ckptQueuedLinkedExile)
    return gAcc
  let preReplayDeparted := g.playersDepartedSinceCheckpoint ckpt
  let ckptDeparted := gAcc.playersDepartedSinceCheckpoint ckpt preReplayDeparted
  let nowSuppressed := wasSuppressed || gAcc.suppressInteractiveReplay
  if isProposalReplayPaused gAcc then
    let deferredCleanup? := if gAcc.over || nowSuppressed then none else gAcc.postCastCleanup
    if deferredCleanup?.isSome then
      gAcc := gAcc.change (.postCastCleanup none)
    if let some cleanup := deferredCleanup? then
      gAcc := gAcc.chainPendingReplacement (.runPostCastCleanup cleanup)
    match ckptPausedBatch? with
    | some (origBid, origStartIdx, wasDiscard, origCause, origObjs, origPls, origEffs, origPend, origStk) =>
      gAcc := gAcc.chainPendingReplacement
        (.restorePausedBatch origBid origStartIdx wasDiscard origCause
          origObjs origPls origEffs origPend origStk false ckptQueuedLinkedExile)
    | none =>
      if !ckptQueuedLinkedExile.isEmpty then
        gAcc := gAcc.chainPendingReplacement (.finishLinkedExileMove ckptQueuedLinkedExile none)
    if !gAcc.over && ckptPending != .none then
      gAcc := gAcc.chainPendingReplacement (.restorePending ckptPending false none ckptDeparted none)
    if !gAcc.over then
      if let some origCont := ckptCont? then
        gAcc := gAcc.chainPendingReplacement origCont
    return gAcc
  if ckptPausedBatch?.isNone && !ckptQueuedLinkedExile.isEmpty then
    gAcc := gAcc.change (.queueLinkedExile ckptQueuedLinkedExile)
    if nowSuppressed then
      gAcc := gAcc.flushQueuedLinkedExileFwd (suppressInteractive := true)
    else
      gAcc := (flushLinked gAcc).drainLocalPendingReplacement
  if gAcc.over then
    return gAcc
  let ckptDeparted := gAcc.playersDepartedSinceCheckpoint ckpt ckptDeparted
  let nowSuppressed := nowSuppressed || gAcc.suppressInteractiveReplay
  if isProposalReplayPaused gAcc then
    let deferredCleanup? := if gAcc.over || nowSuppressed then none else gAcc.postCastCleanup
    if deferredCleanup?.isSome then
      gAcc := gAcc.change (.postCastCleanup none)
    if let some cleanup := deferredCleanup? then
      gAcc := gAcc.chainPendingReplacement (.runPostCastCleanup cleanup)
    if !gAcc.over && ckptPending != .none then
      gAcc := gAcc.chainPendingReplacement (.restorePending ckptPending false none ckptDeparted none)
    if !gAcc.over then
      if let some origCont := ckptCont? then
        gAcc := gAcc.chainPendingReplacement origCont
    return gAcc
  if !nowSuppressed && !gAcc.over then
    gAcc := gAcc.runPostCastCleanupFwd.drainLocalPendingReplacement
  if gAcc.over then
    return gAcc
  let ckptDeparted := gAcc.playersDepartedSinceCheckpoint ckpt ckptDeparted
  if gAcc.pending != .none || gAcc.afterRandom != .none || isProposalReplayPaused gAcc then
    match ckptPausedBatch? with
    | some (origBid, origStartIdx, wasDiscard, origCause, origObjs, origPls, origEffs, origPend, origStk) =>
      gAcc := gAcc.chainPendingReplacement
        (.restorePausedBatch origBid origStartIdx wasDiscard origCause
          origObjs origPls origEffs origPend origStk false ckptQueuedLinkedExile)
    | none => pure ()
    if !gAcc.over && ckptPending != .none then
      gAcc := gAcc.chainPendingReplacement (.restorePending ckptPending false none ckptDeparted none)
    if !gAcc.over then
      if let some origCont := ckptCont? then
        gAcc := gAcc.chainPendingReplacement origCont
    return gAcc
  match ckptPausedBatch? with
  | some (origBid, _, _, origCause, origObjs, origPls, origEffs, origPend, origStk) =>
    gAcc := gAcc.change (.pauseBatch origBid origCause origObjs origPls origEffs origPend origStk)
    if !ckptQueuedLinkedExile.isEmpty then
      gAcc := gAcc.change (.queueLinkedExile ckptQueuedLinkedExile)
  | none => pure ()
  if !gAcc.over && ckptPending != .none then
    if !ckptDeparted.isEmpty then
      gAcc := gAcc.chainPendingReplacement (.restorePending ckptPending false none ckptDeparted none)
    else
      gAcc := gAcc.change (.pending ckptPending)
  if !gAcc.over then
    if let some origCont := ckptCont? then
      gAcc := gAcc.chainPendingReplacement origCont
  return gAcc

/-- Commit a batch of simultaneous rules events with explicit per-event causes
under a single `BatchId`, then evaluate batch-level triggers once (CR 603.2c / 704.3). -/
def commitBatchWithCauses (g : Game) (events : Array (EventCause × RulesEvent)) : Game :=
  if events.isEmpty then g
  else
    g.withBatchCore none (fun g =>
      events.foldl (fun acc (cause, r) =>
        acc.record (GameEvent.rules acc.turnNumber r cause)) g)

/-- Commit a batch of simultaneous rules events sharing `cause` and a single
`BatchId` (CR 608.2c / 610). Resolves `g.resolveOneShotCause cause` once so every
event of a one-shot instruction shares one `EffectId` and one `BatchId`. -/
def commitBatch (g : Game) (cause : EventCause) (events : Array RulesEvent) : Game :=
  if events.isEmpty then g
  else
    let (cause', _) := g.resolveOneShotCause cause
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

/-- Ensure a `ContinuationFrame` exists for continuation-scoped scratch fields
without fabricating a `resolvingContext`, popping it if no pending choice or
`afterRandom` continuation remains open. -/
def withContinuationFrame (g : Game) (f : Game → Game) : Game :=
  if !g.continuations.isEmpty then f g
  else
    let prevDepth := g.continuations.size
    let g := f (g.change (.pushContinuationFrame {}))
    if g.pending != .none || g.afterRandom != .none then g
    else if g.continuations.size > prevDepth then g.change .popContinuationFrame
    else g

/-- Resolving one-shot cause for a player action when an active batch or
resolving spell/ability is present (`none` on a quiet board so non-resolving
helpers do not allocate an `EffectId`; CR 610.1). -/
def resolvingOneShotCause (g : Game) (p : PlayerId)
    (source : Option ObjectId := none) : Option EventCause :=
  match g.currentBatch with
  | some (_, some (.oneShotEffect bid bsrc bctrl)) =>
    some (.oneShotEffect bid (bsrc.orElse (fun _ => source)) (bctrl.orElse (fun _ => some p)))
  | some (_, some bc) => some bc
  | _ =>
    match g.currentResolvingContext? with
    | some (s, c) =>
      some (.oneShotEffect none (source.orElse (fun _ => s)) (c.orElse (fun _ => some p)))
    | none => none

/-- Resolving one-shot cause when a spell or ability is actively resolving,
or `defaultCause` on a quiet board so non-resolving helpers never consume an
`EffectId` (CR 610.1). -/
def resolvingOrRuleCause (g : Game) (p : PlayerId)
    (source : Option ObjectId := none)
    (defaultCause : EventCause := .gameRule .spellCast) : EventCause :=
  (g.resolvingOneShotCause p source).getD defaultCause

/-- Record `PlayerEvent.manaAdded` for `units` on `p` (skipping empty arrays; CR 106.4). -/
def addManaUnits (g : Game) (p : PlayerId) (units : Array ManaUnit)
    (cause : Option EventCause := none) : Game :=
  if !g.stillInGame p || units.isEmpty then g
  else
    let units :=
      units.map fun u =>
        let isTreasureSrc : Bool :=
          u.fromTreasure ||
            match u.source with
            | some srcId =>
              match g.findObject? srcId with
              | some src =>
                if src.isOnBattlefield then g.hasSubtype src .treasure
                else GameEvent.isTreasureSourceInLog g.events srcId
              | none => GameEvent.isTreasureSourceInLog g.events srcId
            | none => false
        { u with fromTreasure := isTreasureSrc }
    let c := cause.orElse (fun _ => g.resolvingOneShotCause p (units[0]?.bind (·.source)))
    g.record (GameEvent.manaAdded g.turnNumber p units (cause := c))

/-- Record `PlayerEvent.manaAdded` for `n` mana of type `t` on `p` (CR 106.4 / 106.6). -/
def addMana (g : Game) (p : PlayerId) (t : ManaType) (n : Nat := 1)
    (source : Option ObjectId := none)
    (restriction : Option ManaSpendRestriction := none)
    (riders : Array SpellRiderSpec := #[])
    (cause : Option EventCause := none)
    (fromTreasure : Bool := false) : Game :=
  if n == 0 then g
  else
    let units := Array.replicate n { mana := t, source, restriction, riders, fromTreasure }
    g.addManaUnits p units (cause := cause.orElse (fun _ => g.resolvingOneShotCause p source))

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

/-- Record and apply the creation of a delayed triggered ability (CR 603.7). -/
def registerDelayedTrigger (g : Game) (dt : DelayedTrigger) : Game :=
  if !g.stillInGame dt.controller then g
  else g.record (GameEvent.delayedTriggerCreated g.turnNumber dt)

/-- Add and process a sequence of `EngineChange`s on the current turn. -/
def changes (g : Game) (cs : Array EngineChange) : Game :=
  cs.foldl Game.change g

/-- Remove any `ReplacementId`s that were applied during an event from
`g.replacementOrder` so player preferences apply only to the current event
and do not stick across subsequent events (CR 616.1). -/
def consumeReplacementOrder (g : Game) (applied : Array ReplacementId) : Game :=
  if g.replacementOrder.isEmpty || applied.isEmpty then g
  else
    let next := g.replacementOrder.filter fun prefId =>
      !applied.contains prefId &&
        !(prefId.counterKind.isNone &&
          applied.any (fun cid => { cid with counterKind := none } == prefId))
    if next == g.replacementOrder then g
    else g.change (.replacementOrder next)

/-- Open `Pending.chooseReplacement` for `chooser` over `choices` and stash
`cont` in `g.pendingReplacement` so `Action.chooseReplacement` can resume the
event once the player chooses (CR 616.1). -/
def promptChooseReplacement (g : Game) (chooser : PlayerId)
    (choices : Array ReplacementId) (cont : PendingReplacement)
    (suppressInteractive : Bool := false) : Game :=
  if suppressInteractive || g.openBatchSuppressInteractive || g.over || g.suppressInteractiveReplay then
    g
  else
    let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
    g.changes #[
      .pending (.chooseReplacement chooser choices),
      .pendingReplacement (some cont)
    ]

/-- Add and process a `PlayerChange` for `p`. -/
def changePlayer (g : Game) (p : PlayerId) (c : PlayerChange) : Game :=
  g.change (.player p c)

/-- Add and process a `ProposalChange` on the current proposed spell or ability. -/
def changeProposal (g : Game) (c : ProposalChange) : Game :=
  g.change (.proposal c)

/-- Add and process multiple `ProposalChange`s on the current proposed spell or ability. -/
def changeProposals (g : Game) (cs : Array ProposalChange) : Game :=
  g.change (.proposalChanges cs)

def logMsg (g : Game) (msg : String) : Game :=
  g.change (.logMsg msg)

/-- Update `lastKnownPower` / `lastKnownToughness` on the `StackEntry` for `objectId`. -/
def setStackEntryLastKnown (g : Game) (objectId : ObjectId)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none) : Game :=
  if g.stack.any (·.objectId == objectId) &&
      (lastKnownPower.isSome || lastKnownToughness.isSome) then
    g.change (.stackEntry objectId (.lastKnownPT lastKnownPower lastKnownToughness))
  else g

/-- The object a continuous effect applies to (or the source for an object-scoped
permission/rule). `none` for effects on players or the whole game. -/
def effectObject? : ContinuousEffectSpec → Option ObjectId
  | .layered (.objects #[id]) _ _ => some id
  | .permission _ (.playFromExile id _) _
  | .permission _ (.flashback id) _
  | .permission _ (.colorlessGrant id _) _ => some id
  | .gameRule (.cantUntap id _) _
  | .gameRule (.cantBeBlockedByPlayer id _) _
  | .gameRule (.cantBeBlockedExceptByHaste id) _
  | .gameRule (.cantBlock id) _
  | .gameRule (.uncounterable id) _
  | .gameRule (.commandEmblem id) _ => some id
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

/-- Whether `id` is currently being attacked as a planeswalker or battle. -/
def isBeingAttacked (g : Game) (id : ObjectId) : Bool :=
  g.objects.any (fun x =>
    x.isOnBattlefield && x.status.attacking &&
      (x.status.attackingTarget == some (.planeswalker id) ||
       x.status.attackingTarget == some (.battle id)))

/-- Whether `id` was removed from combat during the current combat phase (CR 506.4). -/
def removedFromCombatThisCombat (g : Game) (id : ObjectId) : Bool :=
  Id.run do
    let mut idx := g.events.size
    while idx > 0 do
      idx := idx - 1
      let ev := g.events[idx]!
      match ev.change with
      | .rules (.turn (.stepBegan .beginningOfCombat _))
      | .rules (.turn (.phaseBegan .combat))
      | .rules (.turn (.turnBegan _ _)) =>
        return false
      | .rules (.combat (.removedFromCombat snap)) =>
        if snap.id == some id then return true
      | _ => pure ()
    return false

/-- Remove `o` from combat (CR 506.4). -/
def removeFromCombat (g : Game) (o : GameObject) (cause : Option EventCause := none) : Game :=
  if o.status.attacking || !o.status.blocking.isEmpty || o.status.blocked ||
      g.isBeingAttacked o.id then
    g.record (GameEvent.removedFromCombat g.turnNumber (g.snapshot o)
      (cause := g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o)))
  else g

/-- Remove any battlefield permanent from combat whose controller changed
between `pre` and `post` (CR 506.4). -/
def removeFromCombatOnControlChange (pre post : Game)
    (cause : Option EventCause := none) : Game :=
  post.battlefield.foldl (fun acc o =>
    let preObj := (pre.findObject? o.id).getD o
    if pre.controllerOf preObj != post.controllerOf o then
      match acc.findObject? o.id with
      | some cur => acc.removeFromCombat cur (cause := cause)
      | none => acc
    else acc) post

/-- Forward reference to `Leaving.reconcileControlAfterTransition` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_reconcile_control_after_transition"]
opaque reconcileControlAfterTransitionFwd (pre post : Game)
    (cause : Option EventCause := none) (deferPlayFromExileLogs : Bool := false)
    (fromEventIdx? : Option Nat := none) : Game := post

/-- Forward reference to `Leaving.coDepartingIdsExport` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_co_departing_ids"]
opaque coDepartingIdsFwd (g : Game) (seedIds : Array ObjectId) : Array ObjectId := seedIds

/-- Record and apply the creation of a continuous effect (CR 611). Assigns a
fresh unique `EffectId` from `g.nextEffectId`; Layers 1–7d derive characteristics
purely from `g.activeEffects` without imperative mutations on creation. -/
def createEffect (g : Game) (eff : ContinuousEffect)
    (cause : Option EventCause := none) (reconcileControl : Bool := true) : Game :=
  let batchCause? := (g.currentBatch.map Prod.snd).join
  let (g, effCause) : Game × EventCause :=
    match cause with
    | some c =>
      match c with
      | .oneShotEffect (some cid) _ _ =>
        if g.nextEffectId ≤ cid.raw then
          (g.change (.nextEffectId (cid.raw + 1)), c)
        else (g, c)
      | .oneShotEffect none _ _ =>
        let (c', bumpId?, _) := g.resolveCauseInBatch batchCause? c
        match bumpId? with
        | some cid => (g.change (.nextEffectId (max g.nextEffectId (cid.raw + 1))), c')
        | none => (g, c')
      | _ => (g, c)
    | none =>
      match batchCause? with
      | some (.oneShotEffect (some bid) bsrc bctrl) =>
        (g, .oneShotEffect (some bid) bsrc bctrl)
      | some (.oneShotEffect none bsrc bctrl) =>
        let (c', bumpId?, _) := g.resolveCauseInBatch batchCause? (.oneShotEffect none bsrc bctrl)
        match bumpId? with
        | some cid => (g.change (.nextEffectId (max g.nextEffectId (cid.raw + 1))), c')
        | none => (g, c')
      | some bc =>
        (g, bc)
      | none =>
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          g.allocDelayedCause ctrl src
        | none => (g, .gameRule .continuousEffect)
  let pre := g
  let eid : EffectId := ⟨g.nextEffectId⟩
  let g := g.record (GameEvent.effectCreated g.turnNumber eid eff (cause := effCause))
  match eff with
  | .layered _ (.control _) _ | .layered _ (.copy _) _ =>
    if reconcileControl then
      reconcileControlAfterTransitionFwd pre g (cause := some effCause)
    else g
  | _ => g

/-- Players currently tied for most life. -/
def playersWithMostLife (g : Game) : Array PlayerId :=
  let living := g.livingPlayers
  match living[0]? with
  | none => #[]
  | some first =>
    let best := living.foldl (fun acc pl => max acc pl.life) first.life
    living.filter (fun pl => pl.life == best) |>.map (·.id)

/-- The Black Gate: check most life as the ability resolves, then those
creatures (including later ones) cannot block the target this turn. -/
def applyBlackGateUnblockable (g : Game) (attackerId : ObjectId)
    (chosen : PlayerId) : Game :=
  if !(g.playersWithMostLife).contains chosen then
    g.logMsg "The chosen player does not have the most life. The ability does nothing."
  else
    match g.findObject? attackerId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      if !o.isOnBattlefield then
        g.logMsg "The target is no longer legal"
      else
        let (g, effCause) : Game × EventCause :=
          match g.currentResolvingContext? with
          | some (src, ctrl) => g.allocDelayedCause ctrl src
          | none => (g, .gameRule .continuousEffect)
        let g := g.createEffect (.cantBeBlockedByPlayerUntilEot attackerId chosen) (cause := some effCause)
        g.logMsg
          s!"{g.name o} can't be blocked by creatures {(g.player chosen).name} controls this turn"

/-- Record and apply the creation of multiple continuous effects in order (CR 611),
reconciling control transitions once across the entire batch. -/
def createEffects (g : Game) (effs : Array ContinuousEffect)
    (cause : Option EventCause := none) : Game :=
  if effs.isEmpty then g
  else
    let batchCause? := (g.currentBatch.map Prod.snd).join
    let (g, cause) : Game × Option EventCause :=
      match cause, batchCause?, g.currentResolvingContext? with
      | none, some (.oneShotEffect (some bid) bsrc bctrl), _ =>
        (g, some (.oneShotEffect (some bid) bsrc bctrl))
      | none, some (.oneShotEffect none bsrc bctrl), _ =>
        let (c', bumpId?, _) := g.resolveCauseInBatch batchCause? (.oneShotEffect none bsrc bctrl)
        match bumpId? with
        | some cid => (g.change (.nextEffectId (max g.nextEffectId (cid.raw + 1))), some c')
        | none => (g, some c')
      | none, some bc, _ =>
        (g, some bc)
      | none, none, some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause ctrl src
        (g, some c)
      | some (.oneShotEffect none src ctrl), _, _ =>
        let (c', bumpId?, _) := g.resolveCauseInBatch batchCause? (.oneShotEffect none src ctrl)
        match bumpId? with
        | some cid => (g.change (.nextEffectId (max g.nextEffectId (cid.raw + 1))), some c')
        | none => (g, some c')
      | _, _, _ => (g, cause)
    let needsReconcile := effs.any fun
      | .layered _ (.control _) _ | .layered _ (.copy _) _ => true
      | _ => false
    let applyAll (g : Game) : Game :=
      let pre := g
      let g := effs.foldl (fun acc e => acc.createEffect e (cause := cause) (reconcileControl := false)) g
      if needsReconcile then
        let recCause := cause.getD (.gameRule .continuousEffect)
        reconcileControlAfterTransitionFwd pre g (cause := some recCause)
      else g
    if effs.size > 1 then (g.withBatchCore cause applyAll).flushQueuedLinkedExileFwd
    else (applyAll g).flushQueuedLinkedExileFwd

/-- Whether continuous effect `e` expires when object `oid` leaves zone `z`
(with `coLeavingIds` simultaneously leaving or ceasing to exist, CR 400.7 / 611). -/
def effectExpiresWithLeavingObj (g : Game) (oid : ObjectId) (z : Zone)
    (coLeavingIds : Array ObjectId := #[]) (e : ContinuousEffect) : Bool :=
  effectObject? e == some oid ||
    (match e.duration with
     | .whileInZone did dz => did == oid && (z == dz || !(g.findObject? did).any (·.zone == dz))
     | .whileSourceOnBattlefield s | .untilSourceLeaves s | .whileSourceHasCounter s _ =>
       z == .command && s == oid
     | _ => false) ||
    match e with
    | .layered (.objects ids) _ _ =>
      ids.contains oid &&
        ids.all (fun xid => xid == oid || coLeavingIds.contains xid || (g.findObject? xid).isNone)
    | _ => false

/-- Expand `seedIds` transitively across active `.gameRule (.commandEmblem childId)`
effects that expire when an emblem in the set ceases to exist in `.command` (CR 114.5 / 611.2a). -/
def expandTransitiveCommandEmblems (g : Game) (seedIds : Array ObjectId) : Array ObjectId := Id.run do
  let mut result : Array ObjectId := #[]
  for id in seedIds do
    if !result.contains id then
      result := result.push id
  let mut changed := true
  while changed do
    changed := false
    for (_, s) in g.activeEffects do
      match s with
      | .gameRule (.commandEmblem childId) _ =>
        if !result.contains childId &&
            result.any (fun pid => g.effectExpiresWithLeavingObj pid .command result s) then
          result := result.push childId
          changed := true
      | _ => pure ()
  return result

/-- Collect every battlefield target affected by an expiring `.control`
continuous effect (singleton `.objects #[id]`, multi-target `.objects ids`, or
any scoped `ObjectScope`) along with its `pre`-state `GameObject` snapshot. -/
private def collectControlTargets (pre g : Game) (eid : EffectId) (e : ContinuousEffect)
    (targets : Array (ObjectId × GameObject))
    (excludeId? : Option ObjectId := none) : Array (ObjectId × GameObject) :=
  match e with
  | .layered (.objects ids) (.control _) _ =>
    ids.foldl (fun acc tid =>
      if excludeId? == some tid || acc.any (·.1 == tid) then acc
      else
        match g.findObject? tid with
        | some o =>
          if o.zone == .battlefield then
            acc.push (tid, (pre.findObject? tid).getD o)
          else acc
        | none => acc) targets
  | .layered _ (.control _) _ =>
    g.objects.foldl (fun acc o =>
      if o.zone != .battlefield || excludeId? == some o.id || acc.any (·.1 == o.id) then acc
      else
        let preObj := (pre.findObject? o.id).getD o
        if (pre.appliedControlEffectIds preObj).contains eid then acc.push (o.id, preObj)
        else acc) targets
  | _ => targets

/-- Whether `oid` had a `.playFromExile` permission expire and a matching
`"{cardName} can no longer be played from exile"` log emitted for `oid` itself
in `events[startIdx .. endIdx)` with no subsequent re-creation of a
`.playFromExile` permission for `oid` (CR 611.2). When multiple distinct
exiled objects have `.playFromExile` expirations, disambiguates logs by
checking which expired object(s) were unplayable at each log's event index so
one card's log never suppresses a second distinct same-named card. -/
private def hasPlayFromExileLoggedInSlice (g : Game) (oid : ObjectId)
    (cardName : String) (startIdx endIdx : Nat) : Bool := Id.run do
  let events := g.events
  let targetMsg := s!"{cardName} can no longer be played from exile"
  let hi := min endIdx events.size
  let mut sawExpiry := false
  let mut sawLogAfterExpiry := false
  for i in [startIdx:hi] do
    match events[i]! with
    | .rules _ (.continuousEffect (.expired _ (some (.permission _ (.playFromExile oid' perm) _)))) _ _ =>
      if oid' == oid && !perm.fromAdventure && !perm.whileExiled then
        sawExpiry := true
    | .rules _ (.continuousEffect (.created _ (.permission _ (.playFromExile oid' _) _))) _ _ =>
      if oid' == oid then
        sawExpiry := false
        sawLogAfterExpiry := false
    | .engine _ (.logMsg m) _ =>
      if sawExpiry && m == targetMsg then
        sawLogAfterExpiry := true
    | _ => pure ()
  if !sawLogAfterExpiry then
    return false
  let mut allExpired : Array ObjectId := #[]
  for i in [0:hi] do
    match events[i]! with
    | .rules _ (.continuousEffect (.expired _ (some (.permission _ (.playFromExile oid' perm) _)))) _ _ =>
      if !perm.fromAdventure && !perm.whileExiled && !allExpired.contains oid' then
        allExpired := allExpired.push oid'
    | _ => pure ()
  if allExpired.size ≤ 1 then
    return true
  let isPlayableAt (st : Game) (cid : ObjectId) : Bool :=
    (st.findObject? cid).any fun o =>
      o.zone == .exile &&
        (!(st.activePlayPermissions o).isEmpty ||
          st.livingPlayers.any (fun pl => st.mayCastExiledBySource pl.id o))
  let isUnplayableAt (st : Game) (cid : ObjectId) : Bool :=
    (st.findObject? cid).any fun o =>
      o.zone == .exile && st.name o == cardName &&
        (st.activePlayPermissions o).isEmpty &&
        !st.livingPlayers.any (fun pl => st.mayCastExiledBySource pl.id o)
  let matchesCardName (st : Game) (cid : ObjectId) : Bool :=
    (st.findObject? cid).any (fun o => st.name o == cardName) ||
      (g.findObject? cid).any (fun o => g.name o == cardName)
  let interpWaitHasFromIdxAtMost (expIdx : Nat) (w : InterpState) : Bool :=
    w.stack.any fun
      | .afterMoveLoop _ _ _ _ _ (some fi)
      | .afterCounterOpLoop _ _ _ (some fi)
      | .afterCopyAndCastExileLoop _ _ _ _ _ (some fi)
      | .afterDamagePermanentsLoop _ _ _ _ _ fi _
      | .afterDividedDamageLoop _ _ _ fi _
      | .afterMixedDamageLoop _ _ _ fi _ _ _ _ => fi ≤ expIdx
      | _ => false
  let rec contHasFromIdxAtMost (expIdx : Nat) : PendingReplacement → Bool
    | .seq a b => contHasFromIdxAtMost expIdx a || contHasFromIdxAtMost expIdx b
    | .continueInterpreter w => interpWaitHasFromIdxAtMost expIdx w
    | .leavePlayersWhoLost _ _ _ _ (some fi)
    | .endControlExileLoop _ _ _ _ (some fi) false
    | .finishConcede _ _ _ _ _ _ _ (some fi)
    | .concedePlayersLoop _ _ _ _ _ _ _ _ _ _ (some fi)
    | .moveSimultaneousToGraveyard _ _ _ false (some fi)
    | .moveCardsToGraveyardLoop _ _ (some fi)
    | .sacrificePermanentsLoop _ _ _ _ _ (some fi)
    | .destroyPermanentsLoop _ _ _ _ _ _ _ (some fi)
    | .exilePermanentsLoop _ _ _ _ (some fi)
    | .flickerLoop _ _ _ _ _ _ _ _ _ _ (some fi) false
    | .untapStepPermanents _ (some fi)
    | .untapPermanentsLoop _ _ _ _ (some fi)
    | .payCostPickItems _ _ _ _ _ (some fi)
    | .finishActivationExtraCosts _ _ _ _ _ _ _ _ _ _ _ (some fi)
    | .finishActivateManaAbilityPicks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (some fi) _
    | .dealFightDamage _ _ _ _ false (some fi)
    | .markDamageOn _ _ _ _ _ _ _ _ false _ (some fi)
    | .millCardsLoop _ _ _ _ _ _ (some fi) false
    | .putToBattlefieldLoop _ _ _ _ _ _ _ _ _ _ _ (some fi)
    | .finishLinkedExileMove _ _ _ _ (some fi)
    | .returnLinkedExileLoop _ _ _ _ _ (some fi)
    | .commitEnteringAttackItems _ _ _ _ _ (some fi)
    | .finishEnteringAttackCards _ _ (some fi)
    | .dealAssignedCombatDamage _ (some fi)
    | .dealDamageToEachCreatureMatching _ _ _ _ _ _ _ (some fi) _
    | .placeSearchedBatch _ _ _ _ _ _ (some fi)
    | .placeSearchedGraveyardLoop _ _ _ (some fi)
    | .surveilMoveLoop _ _ _ (some fi)
    | .finishSurveilPostMove _ _ _ _ _ (some fi)
    | .finishPostStep (.finishSurveilHandMove _ _ _ _ _ (some fi))
    | .finishPostStep (.damageUpToOneAndPlayerLoop _ _ _ _ _ _ _ (some fi))
    | .finishPostStep (.exileZemoBoastCards _ _ _ (some fi))
    | .finishPostStep (.exileSearchedLinkedLoop _ _ _ _ _ (some fi))
    | .finishPostStep (.exileTopPlayIfYouControlSubtypeLoop _ _ _ _ _ (some fi))
    | .finishPostStep (.exileTopMayCastUpToLoop _ _ _ _ _ _ _ (some fi))
    | .finishPostStep (.resolveCascadeLoop _ _ _ _ _ (some fi))
    | .finishPostStep (.exileUntilInstantOrSorceryLoop _ _ _ _ _ _ (some fi))
    | .finishPostStep (.moveIdsInOrderLoop _ _ _ _ _ _ (some fi))
    | .finishPostStep (.millOpponentsOnly _ _ _ (some fi))
    | .finishPostStep (.returnOwnedCreaturesLoop _ _ _ _ _ _ (some fi))
    | .finishPostStep (.placeSearchedHandLoop _ _ _ _ (some fi))
    | .finishPostStep (.applyRiddlesToHandLoop _ _ _ (some fi))
    | .finishPostStep (.exileCardsLoop _ _ (some fi))
    | .finishPostStep (.returnToHandLoop _ _ (some fi))
    | .finishPostStep (.discardCleanupIds _ _ _ (some fi))
    | .finishPostStep (.discardHandIdsLoop _ _ _ _ (some fi))
    | .finishPostStep (.discardMultiHandIdsLoop _ _ _ (some fi))
    | .finishPostStep (.chooseCardsToHandLoop _ _ _ _ (some fi))
    | .finishPostStep (.movePublicCardsToHandLoop _ _ _ _ _ _ _ (some fi))
    | .finishPostStep (.exileOpponentLibrariesLoop _ _ _ _ _ (some fi))
    | .finishPostStep (.revealPutCreaturesStep _ _ _ _ _ (some fi))
    | .finishPostStep (.exileTopForPlayLoop _ _ _ _ _ _ (some fi))
    | .finishPostStep (.emitExpiredPlayFromExileFrom fi)
    | .checkSBA (some fi) => fi ≤ expIdx
    | _ => false
  let frameQueues (x : ObjectId) (expIdx : Nat) (f : ContinuationFrame) : Bool :=
    f.pendingReplacement.any (fun c =>
      c.containsDeferredPlayFromExile x || contHasFromIdxAtMost expIdx c) ||
    f.outerPendingReplacements.any (fun c =>
      c.containsDeferredPlayFromExile x || contHasFromIdxAtMost expIdx c) ||
    f.interpWait?.any (interpWaitHasFromIdxAtMost expIdx)
  let mut pending : Array ObjectId := #[]
  let mut loggedInSlice : Array ObjectId := #[]
  -- Each entry `(inSlice, elig)` records an ambiguous log emitted at `i` (`inSlice = i ≥ startIdx`)
  -- with eligible pending same-named unplayable cards `elig`.
  let mut ambigEvents : Array (Bool × Array ObjectId) := #[]
  let mut lastPreStartExpIdx : Array (ObjectId × Nat) := #[]
  let mut curG? : Option Game := none
  let mut curIdx : Nat := 0
  let advanceCurG (targetIdx : Nat) (curGOpt : Option Game) (cIdx : Nat) : Game :=
    match curGOpt with
    | none => Game.replayEvents (events.extract 0 targetIdx)
    | some prev => (events.extract cIdx targetIdx).foldl Game.replayEvent prev
  let gameWithObjAt (idx : Nat) (replayed : Game) (x : ObjectId) : Game :=
    if replayed.players.size ≥ g.players.size && (replayed.findObject? x).isSome then replayed
    else g.mkHistoricalGameAt idx
  let dropFromAmbig (evts : Array (Bool × Array ObjectId)) (x : ObjectId) :
      Array (Bool × Array ObjectId) := Id.run do
    let mut consumed := false
    let mut out : Array (Bool × Array ObjectId) := #[]
    for (inS, grp) in evts do
      if !consumed && grp.contains x then
        consumed := true
      else
        let grp' := grp.filter (· != x)
        if !grp'.isEmpty then
          out := out.push (inS, grp')
    return out
  let resolveSaturated (pendIn : Array ObjectId) (loggedIn : Array ObjectId)
      (lastPreIn : Array (ObjectId × Nat)) (evtsIn : Array (Bool × Array ObjectId)) :
      Array ObjectId × Array ObjectId × Array (ObjectId × Nat) × Array (Bool × Array ObjectId) := Id.run do
    let mut pend := pendIn
    let mut logged := loggedIn
    let mut lastPre := lastPreIn
    let mut evts := evtsIn.filterMap fun (inS, grp) =>
      let grp' := grp.filter (pend.contains ·)
      if grp'.isEmpty then none else some (inS, grp')
    let mut changed := true
    while changed && !evts.isEmpty do
      changed := false
      if let some idx := evts.findIdx? (fun (_, grp) => grp.size == 1) then
        let (inS, grp) := evts[idx]!
        let x := grp[0]!
        if inS && !logged.contains x then
          logged := logged.push x
        pend := pend.filter (· != x)
        lastPre := lastPre.filter (·.1 != x)
        let mut nextEvts : Array (Bool × Array ObjectId) := #[]
        for j in [0:evts.size] do
          if j != idx then
            let (inS', g') := evts[j]!
            let g'' := g'.filter (· != x)
            if !g''.isEmpty then
              nextEvts := nextEvts.push (inS', g'')
        evts := nextEvts
        changed := true
      else
        -- Compute a maximum bipartite matching between `evts` (left, `0..nL-1`) and
        -- `pend` (right, `0..nR-1`) via augmenting-path BFS (respecting pre-slice vs
        -- in-slice preference), then extract the unique maximal Hall-tight (saturated)
        -- subset `T_R = R \ ReachR` via Dulmage-Mendelsohn alternating-path reachability
        -- from unmatched right vertices `U_R`. Unresolved events in `ReachL` are retained
        -- with `T_R` removed rather than dropped.
        let nL := evts.size
        let nR := pend.size
        let adj : Array (Array Nat) := evts.map fun (inS, grp) => Id.run do
          let mut pref : Array Nat := #[]
          let mut rest : Array Nat := #[]
          for r in [0:nR] do
            let x := pend[r]!
            if grp.contains x then
              let isPre := lastPre.any (·.1 == x)
              if (!inS && isPre) || (inS && !isPre) then
                pref := pref.push r
              else
                rest := rest.push r
          return pref ++ rest
        let mut matchL : Array (Option Nat) := Array.replicate nL none
        let mut matchR : Array (Option Nat) := Array.replicate nR none
        let orderL : Array Nat := Id.run do
          let mut preL : Array Nat := #[]
          let mut inL : Array Nat := #[]
          for e in [0:nL] do
            if !evts[e]!.1 then preL := preL.push e else inL := inL.push e
          return preL ++ inL
        for startE in orderL do
          let mut visitedR : Array Bool := Array.replicate nR false
          let mut parentR : Array (Option Nat) := Array.replicate nR none
          let mut queueL : Array Nat := #[startE]
          let mut qHead : Nat := 0
          let mut foundR? : Option Nat := none
          while qHead < queueL.size && foundR?.isNone do
            let u := queueL[qHead]!
            qHead := qHead + 1
            for r in adj[u]! do
              if !visitedR[r]! then
                visitedR := visitedR.set! r true
                parentR := parentR.set! r (some u)
                match matchR[r]! with
                | none =>
                  foundR? := some r
                  break
                | some prevL =>
                  queueL := queueL.push prevL
          if let some targetR := foundR? then
            let mut curR? : Option Nat := some targetR
            for _ in [0:nR + 1] do
              match curR? with
              | none => break
              | some r =>
                match parentR[r]! with
                | none => break
                | some u =>
                  let nextR? := matchL[u]!
                  matchL := matchL.set! u (some r)
                  matchR := matchR.set! r (some u)
                  curR? := nextR?
        let mut reachR : Array Bool := Array.replicate nR false
        let mut reachL : Array Bool := Array.replicate nL false
        let mut qR : Array Nat := #[]
        for r in [0:nR] do
          if matchR[r]!.isNone then
            reachR := reachR.set! r true
            qR := qR.push r
        let mut qRHead : Nat := 0
        while qRHead < qR.size do
          let r := qR[qRHead]!
          qRHead := qRHead + 1
          for u in [0:nL] do
            if !reachL[u]! && adj[u]!.contains r then
              reachL := reachL.set! u true
              if let some r' := matchL[u]! then
                if !reachR[r']! then
                  reachR := reachR.set! r' true
                  qR := qR.push r'
        let mut resolvedIds : Array ObjectId := #[]
        for r in [0:nR] do
          if !reachR[r]! then
            let x := pend[r]!
            resolvedIds := resolvedIds.push x
            if let some u := matchR[r]! then
              if evts[u]!.1 && !logged.contains x then
                logged := logged.push x
        if !resolvedIds.isEmpty then
          pend := pend.filter (fun x => !resolvedIds.contains x)
          lastPre := lastPre.filter (fun (x, _) => !resolvedIds.contains x)
          let mut nextEvts : Array (Bool × Array ObjectId) := #[]
          for j in [0:nL] do
            if reachL[j]! then
              let (inS', g') := evts[j]!
              let g'' := g'.filter (fun x => !resolvedIds.contains x)
              if !g''.isEmpty then
                nextEvts := nextEvts.push (inS', g'')
          evts := nextEvts
          changed := true
    return (pend, logged, lastPre, evts)
  for i in [0:hi] do
    if i == startIdx && startIdx > 0 && !pending.isEmpty then
      let stAtStart := advanceCurG startIdx curG? curIdx
      curG? := some stAtStart
      curIdx := startIdx
      let mut toPrune : Array ObjectId := #[]
      for x in pending do
        match lastPreStartExpIdx.find? (·.1 == x) with
        | some (_, expIdx) =>
          let isQueued :=
            stAtStart.currentBatch.isSome ||
              stAtStart.continuations.any (frameQueues x expIdx)
          if !isQueued then
            let shouldPrune :=
              if !isUnplayableAt (gameWithObjAt startIdx stAtStart x) x then true
              else
                let batchEnd : Nat := Id.run do
                  match events[expIdx]!.batch with
                  | some bid =>
                    let mut k := expIdx + 1
                    let mut lastInBatch := expIdx + 1
                    while k < startIdx do
                      match events[k]!.batch with
                      | some b =>
                        if b == bid then
                          lastInBatch := k + 1
                          k := k + 1
                        else break
                      | none =>
                        match events[k]!.change with
                        | .engine _ => k := k + 1
                        | _ => break
                    return lastInBatch
                  | none =>
                    let mut k := expIdx + 1
                    let mut lastInAction := expIdx + 1
                    while k < startIdx do
                      let ev := events[k]!
                      if ev.batch.isSome then break
                      match ev.change with
                      | .engine (.priority _)
                      | .rules (.turn (.turnBegan _ _))
                      | .rules (.turn (.phaseBegan _))
                      | .rules (.turn (.stepBegan _))
                      | .rules (.turn (.stepEnded _))
                      | .rules (.turn (.phaseEnded _))
                      | .rules (.turn (.turnEnded _))
                      | .rules (.cast _) => break
                      | .engine (.logMsg m) =>
                        if m == targetMsg then break
                        k := k + 1
                      | .engine _ => k := k + 1
                      | .rules _ =>
                        lastInAction := k + 1
                        k := k + 1
                    return lastInAction
                let stAfterExp := Game.replayEvents (events.extract 0 batchEnd)
                !isUnplayableAt (gameWithObjAt batchEnd stAfterExp x) x
            if shouldPrune then
              toPrune := toPrune.push x
        | none => pure ()
      for x in toPrune do
        pending := pending.filter (· != x)
        lastPreStartExpIdx := lastPreStartExpIdx.filter (·.1 != x)
        ambigEvents := dropFromAmbig ambigEvents x
    match events[i]! with
    | .rules _ (.continuousEffect (.expired _ (some (.permission _ (.playFromExile oid' perm) _)))) _ _ =>
      if !perm.fromAdventure && !perm.whileExiled then
        let stBefore := advanceCurG i curG? curIdx
        curG? := some stBefore
        curIdx := i
        let stCheck := gameWithObjAt i stBefore oid'
        let inExileNow := (stCheck.findObject? oid').any (·.zone == .exile)
        let hadPlayable :=
          if !inExileNow then false
          else if isPlayableAt stCheck oid' then true
          else
            let preIdx : Nat := Id.run do
              match events[i]!.batch with
              | some bid =>
                let mut k := i
                let mut firstInBatch := i
                while k > 0 do
                  match events[k - 1]!.batch with
                  | some b =>
                    if b == bid then
                      firstInBatch := k - 1
                      k := k - 1
                    else break
                  | none =>
                    match events[k - 1]!.change with
                    | .engine _ => k := k - 1
                    | _ => break
                return firstInBatch
              | none =>
                let mut k := i
                let mut firstInAction := i
                while k > 0 do
                  let ev := events[k - 1]!
                  if ev.batch.isSome then break
                  match ev.change with
                  | .engine (.priority _)
                  | .rules (.turn (.turnBegan _ _))
                  | .rules (.turn (.phaseBegan _))
                  | .rules (.turn (.stepBegan _))
                  | .rules (.turn (.stepEnded _))
                  | .rules (.turn (.phaseEnded _))
                  | .rules (.turn (.turnEnded _))
                  | .rules (.cast _) => break
                  | .rules (.continuousEffect (.created _ (.permission _ (.playFromExile oid'' _) _))) =>
                    if oid'' == oid' then break
                    else
                      firstInAction := k - 1
                      k := k - 1
                  | .rules (.zone (.moved _ after _ .exile _ _ _ _)) =>
                    if after.id == some oid' then break
                    else
                      firstInAction := k - 1
                      k := k - 1
                  | .rules (.zone (.created eo _)) =>
                    if eo.id == some oid' && eo.zone == .exile then break
                    else
                      firstInAction := k - 1
                      k := k - 1
                  | .engine (.logMsg m) =>
                    if m == targetMsg then break
                    k := k - 1
                  | .engine _ => k := k - 1
                  | .rules _ =>
                    firstInAction := k - 1
                    k := k - 1
                return firstInAction
            if preIdx < i then
              let stPreRaw := Game.replayEvents (events.extract 0 preIdx)
              isPlayableAt (gameWithObjAt preIdx stPreRaw oid') oid'
            else false
        if hadPlayable then
          if !pending.contains oid' && (i < startIdx || !loggedInSlice.contains oid') then
            pending := pending.push oid'
          if i < startIdx then
            lastPreStartExpIdx := (lastPreStartExpIdx.filter (·.1 != oid')).push (oid', i)
    | .rules _ (.continuousEffect (.created _ (.permission _ (.playFromExile oid' _) _))) _ _ =>
      pending := pending.filter (· != oid')
      loggedInSlice := loggedInSlice.filter (· != oid')
      lastPreStartExpIdx := lastPreStartExpIdx.filter (·.1 != oid')
      ambigEvents := dropFromAmbig ambigEvents oid'
    | .rules _ (.zone (.moved before _ .exile _ _ _ _ _)) _ _ =>
      if let some oid' := before.id then
        pending := pending.filter (· != oid')
        lastPreStartExpIdx := lastPreStartExpIdx.filter (·.1 != oid')
        ambigEvents := dropFromAmbig ambigEvents oid'
    | .rules _ (.zone (.ceasedToExist snap)) _ _ =>
      if let some oid' := snap.id then
        pending := pending.filter (· != oid')
        lastPreStartExpIdx := lastPreStartExpIdx.filter (·.1 != oid')
        ambigEvents := dropFromAmbig ambigEvents oid'
    | .engine _ (.logMsg m) _ =>
      if m == targetMsg && !pending.isEmpty then
        let curG := advanceCurG i curG? curIdx
        curG? := some curG
        curIdx := i
        let useReplayForElig :=
          curG.players.size ≥ g.players.size &&
            pending.all (fun x => (curG.findObject? x).isSome)
        let evalG := if useReplayForElig then curG else g.mkHistoricalGameAt i
        let elig0 := pending.filter (isUnplayableAt evalG)
        let elig :=
          if !elig0.isEmpty then elig0
          else
            let histG := if useReplayForElig then g.mkHistoricalGameAt i else evalG
            let eligHist := pending.filter (isUnplayableAt histG)
            if !eligHist.isEmpty then eligHist
            else pending.filter (matchesCardName histG)
        if elig.size == 1 then
          let x := elig[0]!
          if i ≥ startIdx && !loggedInSlice.contains x then
            loggedInSlice := loggedInSlice.push x
          pending := pending.filter (· != x)
          lastPreStartExpIdx := lastPreStartExpIdx.filter (·.1 != x)
          let (p', l', lp', ae') := resolveSaturated pending loggedInSlice lastPreStartExpIdx ambigEvents
          pending := p'
          loggedInSlice := l'
          lastPreStartExpIdx := lp'
          ambigEvents := ae'
        else if elig.size ≥ 2 then
          let nextAmbig := ambigEvents.push (i ≥ startIdx, elig)
          let (p', l', lp', ae') := resolveSaturated pending loggedInSlice lastPreStartExpIdx nextAmbig
          pending := p'
          loggedInSlice := l'
          lastPreStartExpIdx := lp'
          ambigEvents := ae'
    | _ => pure ()
  return loggedInSlice.contains oid

/-- Emit `"{name} can no longer be played from exile"` for each exiled card in
`ids` that now has neither an active play permission nor a living
`mayCastExiledBySource` source, skipping cards already logged since
`startEventIdx` (CR 611.2). -/
def logExpiredPlayFromExileIds (g : Game) (ids : Array ObjectId)
    (startEventIdx : Nat := 0) : Game :=
  (ids.foldl (fun (acc, seen) oid =>
    if seen.contains oid then (acc, seen)
    else
      let seen' := seen.push oid
      match acc.findObject? oid with
      | some o =>
        if o.zone == .exile &&
            (acc.activePlayPermissions o).isEmpty &&
            !acc.livingPlayers.any (fun pl => acc.mayCastExiledBySource pl.id o) &&
            !hasPlayFromExileLoggedInSlice acc oid (acc.name o) startEventIdx acc.events.size then
          (acc.logMsg s!"{acc.name o} can no longer be played from exile", seen')
        else (acc, seen')
      | none => (acc, seen')) (g, #[])).1

private def countPfeLeaves : PendingReplacement → Nat
  | .seq a b => countPfeLeaves a + countPfeLeaves b
  | _ => 1

private def insertPfeAfterLeafIdx (pr postStep : PendingReplacement) (targetIdx : Nat) :
    PendingReplacement :=
  match pr with
  | .seq a b =>
    let nA := countPfeLeaves a
    if targetIdx < nA then
      .seq (insertPfeAfterLeafIdx a postStep targetIdx) b
    else
      .seq a (insertPfeAfterLeafIdx b postStep (targetIdx - nA))
  | leaf => .seq leaf postStep

/-- Walk one continuation slot's `PendingReplacement` tree in exact runtime execution order
for `emitExpiredPlayFromExileLogs` placement:
- `.restorePending .none false _ _ none` is a transparent no-op;
- `.restorePending .none true _ _ none` pops and immediately walks the next unpopped outer
  on the same frame (`outers[nextOut - 1]`) ahead of any suffix in the parent `.seq`;
- `.receivePriority _` / `.finishResolutionChoice` stops walking the current tree (and any
  enclosing `.restorePending .none true` suffix) and returns `hitPrio := true` so remaining
  unpopped outers on the same frame still drain before stopping prior to lower frames;
- any other defer-boundary leaf (including all 14 proposal-pause `.restorePending` payloads
  and all non-priority CR 734.1 proposal-reversing leaves) halts the walk immediately. -/
private def walkPfeSlot (fi : Nat) (outers : Array PendingReplacement)
    (oi? : Option Nat) (pr : PendingReplacement) (nextOuter : Nat)
    (lastNonBoundary? : Option (Nat × Option Nat × Nat)) :
    Nat → Nat × Option (Nat × Option Nat × Nat) × Bool × Bool
  | 0 => (nextOuter, lastNonBoundary?, true, false)
  | fuel' + 1 =>
    let rec go (sub : PendingReplacement) (leafBase nextOut : Nat)
        (lastNb? : Option (Nat × Option Nat × Nat))
        (stopped hitPrio stopTree : Bool) :
        Nat × Nat × Option (Nat × Option Nat × Nat) × Bool × Bool × Bool :=
      if stopped || stopTree then
        (leafBase + countPfeLeaves sub, nextOut, lastNb?, stopped, hitPrio, stopTree)
      else
        match sub with
        | .seq a b =>
          let (baseA, nextOutA, lastNbA, stoppedA, hitPrioA, stopTreeA) :=
            go a leafBase nextOut lastNb? false hitPrio false
          go b baseA nextOutA lastNbA stoppedA hitPrioA stopTreeA
        | .restorePending .none false _ _ none =>
          (leafBase + 1, nextOut, lastNb?, false, hitPrio, false)
        | .restorePending .none true _ _ none =>
          if nextOut > 0 then
            let poppedOi := nextOut - 1
            match outers[poppedOi]? with
            | some poppedPr =>
              let (nextOut', lastNb', stopped', hitPrio') :=
                walkPfeSlot fi outers (some poppedOi) poppedPr poppedOi
                  lastNb? fuel'
              (leafBase + 1, nextOut', lastNb', stopped', hitPrio || hitPrio', stopped' || hitPrio')
            | none =>
              (leafBase + 1, poppedOi, lastNb?, false, hitPrio, false)
          else
            (leafBase + 1, nextOut, lastNb?, false, hitPrio, false)
        | leaf =>
          let isBarePrio : Bool :=
            match leaf with
            | .receivePriority _ | .finishResolutionChoice => true
            | _ => false
          if isBarePrio then
            (leafBase + 1, nextOut, lastNb?, false, true, true)
          else if leaf.isPlayFromExileDeferBoundaryLeaf then
            (leafBase + 1, nextOut, lastNb?, true, hitPrio, true)
          else
            (leafBase + 1, nextOut, some (fi, oi?, leafBase), false, hitPrio, false)
    let (_, nextOutEnd, lastNbEnd, stoppedEnd, hitPrioEnd, _) :=
      go pr 0 nextOuter lastNonBoundary? false false false
    (nextOutEnd, lastNbEnd, stoppedEnd, hitPrioEnd)

/-- True when `g.events[fromEventIdx..]` contains any non-adventure,
non-`whileExiled` `.playFromExile` continuous-effect expiration event that
could require a play-from-exile expiry log (CR 611.2b). -/
def hasExpiredPlayFromExileEventSince (g : Game) (fromEventIdx : Nat) : Bool :=
  let n := g.events.size
  let start := min fromEventIdx n
  Id.run do
    for i in [start:n] do
      match g.events[i]! with
      | .rules _ (.continuousEffect (.expired _ (some (.permission _ (.playFromExile _ perm) _)))) _ _ =>
        if !perm.fromAdventure && !perm.whileExiled then
          return true
      | _ => pure ()
    return false

/-- Emit deferred `"{name} can no longer be played from exile"` logs once all
simultaneously expiring continuous effects in a transition starting at `pre`
have ended, checking `hadPlayable` on `pre` and post-expiry permissions /
`mayCastExiledBySource` on `g` (CR 611.2). When `g` is currently paused on a
CR 616.1 / 704.5j choice (such as a paused `endControlExileLoop` that has not
yet exiled a `mayCastExiledBySource` source, across any frame of
`g.continuations`), cards that are still playable before that loop finishes are
deferred via `.finishPostStep (.logExpiredPlayFromExile _ _)`, placed in
execution order immediately ahead of any priority-granting, mutating-then-priority,
or proposal-reversing boundary leaf so expiry logs emit before
`PriorityEvent.received` and are never dropped on CR 734.1 proposal reversal. -/
def emitExpiredPlayFromExileLogs (pre g : Game) (fromEventIdx : Nat) : Game :=
  if !g.hasExpiredPlayFromExileEventSince fromEventIdx then g
  else
  let slice := g.events.extract fromEventIdx g.events.size
  let checkStartIdx := min pre.events.size fromEventIdx
  let expiredOids : Array ObjectId :=
    slice.foldl (fun acc ev =>
      match ev with
      | .rules _ (.continuousEffect (.expired _ (some (.permission _ (.playFromExile oid perm) _)))) _ _ =>
        if perm.fromAdventure || perm.whileExiled || acc.contains oid then acc
        else acc.push oid
      | _ => acc) #[]
  let paused :=
    match g.pending with
    | .chooseReplacement .. | .chooseLegend .. => true
    | _ => g.continuations.any fun f =>
      f.pendingReplacement.isSome || !f.outerPendingReplacements.isEmpty
  let alreadyDeferred (oid : ObjectId) : Bool :=
    g.continuations.any fun f =>
      f.pendingReplacement.any (·.containsDeferredPlayFromExile oid) ||
        f.outerPendingReplacements.any (·.containsDeferredPlayFromExile oid)
  let (gOut, deferredIds) :=
    expiredOids.foldl (fun (acc, deferred) oid =>
      let hadPlayable :=
        (pre.findObject? oid).any fun o =>
          o.zone == .exile &&
            (!(pre.activePlayPermissions o).isEmpty ||
              pre.livingPlayers.any (fun pl => pre.mayCastExiledBySource pl.id o))
      match acc.findObject? oid with
      | some o =>
        if o.zone == .exile && hadPlayable &&
            !hasPlayFromExileLoggedInSlice acc oid (acc.name o) checkStartIdx acc.events.size then
          if (acc.activePlayPermissions o).isEmpty &&
              !acc.livingPlayers.any (fun pl => acc.mayCastExiledBySource pl.id o) then
            (acc.logMsg s!"{acc.name o} can no longer be played from exile", deferred)
          else if paused && !alreadyDeferred oid then
            (acc, if deferred.contains oid then deferred else deferred.push oid)
          else (acc, deferred)
        else (acc, deferred)
      | none => (acc, deferred)) (g, #[])
  if deferredIds.isEmpty then gOut
  else
    let deferCont : PendingReplacement :=
      .finishPostStep (.logExpiredPlayFromExile deferredIds checkStartIdx)
    let targetUpdate? : Option (Nat × Option Nat × PendingReplacement) := Id.run do
      let nFrames := gOut.continuations.size
      if nFrames == 0 then return none
      let mut lastNonBoundary? : Option (Nat × Option Nat × Nat) := none
      let mut firstSlot? : Option (Nat × Option Nat × PendingReplacement) := none
      let mut fallbackFrame? : Option Nat := none
      let mut stopped := false
      let mut sawFramePriority := false
      for step in [0:nFrames] do
        if stopped || sawFramePriority then
          break
        let fi := nFrames - 1 - step
        let fr := gOut.continuations[fi]!
        if step > 0 && fr.afterRandom != .none then
          stopped := true
          break
        let interpActive : Bool :=
          fr.interpWait?.isSome &&
            !(gOut.proposedSpell.isNone && (fr.pendingMayCastFromExile.isSome || fr.pendingFreeCopies.isSome))
        let hasMidBarrier : Bool := fr.afterRandom != .none || interpActive
        let outers := fr.outerPendingReplacements
        let mut nextOuter := outers.size
        let popFuel := outers.size + 2
        if let some pr := fr.pendingReplacement then
          if firstSlot?.isNone then
            firstSlot? := some (fi, none, pr)
          let (no', lnb', st', hitPrio') :=
            walkPfeSlot fi outers none pr nextOuter lastNonBoundary? popFuel
          nextOuter := no'
          lastNonBoundary? := lnb'
          stopped := st'
          sawFramePriority := sawFramePriority || hitPrio'
        if !stopped && hasMidBarrier then
          if fallbackFrame?.isNone then
            fallbackFrame? := some fi
          stopped := true
        while !stopped && nextOuter > 0 do
          let oi := nextOuter - 1
          nextOuter := oi
          match outers[oi]? with
          | some opr =>
            if firstSlot?.isNone then
              firstSlot? := some (fi, some oi, opr)
            let (no', lnb', st', hitPrio') :=
              walkPfeSlot fi outers (some oi) opr nextOuter lastNonBoundary? popFuel
            nextOuter := no'
            lastNonBoundary? := lnb'
            stopped := st'
            sawFramePriority := sawFramePriority || hitPrio'
          | none => pure ()
        let frameStopsDescent : Bool :=
          fr.resolutionFinish.isSome ||
            fr.pendingMayCastFromExile.isSome ||
            fr.pendingFreeCopies.isSome ||
            fr.afterRandom != .none ||
            fr.interpWait?.isSome
        if !stopped && frameStopsDescent then
          if fallbackFrame?.isNone then
            fallbackFrame? := some fi
          stopped := true
      match lastNonBoundary? with
      | some (tFi, tOi?, leafIdx) =>
        let fr := gOut.continuations[tFi]!
        let origPr? : Option PendingReplacement :=
          match tOi? with
          | none => fr.pendingReplacement
          | some oi => fr.outerPendingReplacements[oi]?
        match origPr? with
        | some origPr => return some (tFi, tOi?, insertPfeAfterLeafIdx origPr deferCont leafIdx)
        | none => return none
      | none =>
        match firstSlot? with
        | some (tFi, tOi?, firstPr) =>
          return some (tFi, tOi?, .seq deferCont firstPr)
        | none =>
          match fallbackFrame? with
          | some tFi => return some (tFi, none, deferCont)
          | none => return none
    match targetUpdate? with
    | none =>
      gOut.chainPendingReplacement deferCont
    | some (targetFi, targetOi?, newPr) =>
      let nFrames := gOut.continuations.size
      if targetFi == nFrames - 1 then
        match targetOi? with
        | none =>
          gOut.change (.pendingReplacement (some newPr))
        | some idx =>
          let outers := gOut.outerPendingReplacements
          let cs : Array EngineChange := Id.run do
            let popCount := outers.size - idx
            let mut cs : Array EngineChange := #[]
            for _ in [0:popCount] do
              cs := cs.push .popOuterPendingReplacement
            cs := cs.push (.pushOuterPendingReplacement newPr)
            for k in [idx + 1 : outers.size] do
              cs := cs.push (.pushOuterPendingReplacement outers[k]!)
            return cs
          gOut.changes cs
      else
        let origFrame := gOut.continuations[targetFi]!
        let updatedFrame : ContinuationFrame :=
          match targetOi? with
          | none => { origFrame with pendingReplacement := some newPr }
          | some idx =>
            { origFrame with
              outerPendingReplacements := origFrame.outerPendingReplacements.set! idx newPr }
        let cs : Array EngineChange := Id.run do
          let popCount := nFrames - targetFi
          let mut cs : Array EngineChange := #[]
          for _ in [0:popCount] do
            cs := cs.push .popContinuationFrame
          cs := cs.push (.pushContinuationFrame updatedFrame)
          for k in [targetFi + 1 : nFrames] do
            cs := cs.push (.pushContinuationFrame gOut.continuations[k]!)
          return cs
        gOut.changes cs

/-- Like `emitExpiredPlayFromExileLogs`, but constructs the pre-transition `Game`
lazily via `mkPre ()` only when `g.events[fromEventIdx..]` actually contains an
eligible `.playFromExile` continuous-effect expiration event. -/
def emitExpiredPlayFromExileLogsLazy (mkPre : Unit → Game) (g : Game) (fromEventIdx : Nat) : Game :=
  if !g.hasExpiredPlayFromExileEventSince fromEventIdx then g
  else emitExpiredPlayFromExileLogs (mkPre ()) g fromEventIdx

mutual

/-- Record and apply the expiration of the active continuous effect recorded
under `eid` (CR 611), using the payload stored when it was created. An id that
is not active records nothing; Layers 1–7d derive remaining characteristics
purely from `g.activeEffects`. -/
partial def expireEffectById (g : Game) (eid : EffectId)
    (cause : Option EventCause := none) (reconcileControl : Bool := true)
    (preState? : Option Game := none) (suppressEmblemLog : Bool := false)
    (suppressReturnLog : Bool := false) (skipLogIds : Array ObjectId := #[])
    (deferPlayFromExileLogs : Bool := false) : Game :=
  match g.activeEffect? eid with
  | none => g
  | some eff =>
    let pre := preState?.getD g
    let expCause :=
      g.resolveOptionalCause cause (defaultCause := .gameRule .continuousEffect)
    match eff with
    | .gameRule (.commandEmblem id) _ =>
      match g.findObject? id with
      | some old =>
        if old.zone == .command then
          let allEmbIds := expandTransitiveCommandEmblems g #[old.id]
          let effSkipLogIds : Array ObjectId :=
            if reconcileControl then
              (coDepartingIdsFwd pre allEmbIds).foldl
                (fun acc cid => if acc.contains cid then acc else acc.push cid) skipLogIds
            else skipLogIds
          let childEmbNames : Array String :=
            (allEmbIds.filter (· != old.id)).filterMap fun cid =>
              match g.findObject? cid with
              | some co =>
                if co.zone == .command then
                  some (pre.name ((pre.findObject? cid).getD co))
                else none
              | none => none
          let embName := pre.name ((pre.findObject? id).getD old)
          let embCause := g.resolveOptionalCause cause (defaultCause := .gameRule .leavingZone)
          let fromIdx := g.events.size
          let snap :=
            { (pre.snapshot ((pre.findObject? id).getD old)) with
              id := some old.id
              zone := old.zone }
          let g := g.record (GameEvent.ceasedToExist g.turnNumber snap (cause := embCause))
          let leaving := g.activeEffects.filter (fun (_, e) =>
            effectExpiresWithLeavingObj g old.id .command allEmbIds e)
          let allLeaving := g.activeEffects.filter (fun (_, e) =>
            allEmbIds.any (fun embId => effectExpiresWithLeavingObj g embId .command allEmbIds e))
          let controlSingles : Array (ObjectId × GameObject) :=
            if suppressReturnLog then #[]
            else
              allLeaving.foldl (fun targets (cEid, e) =>
                collectControlTargets pre g cEid e targets) #[]
          let g :=
            restoreCopiesWhere g
              (fun acc cEid _ _ =>
                match acc.activeEffect? cEid with
                | some ce =>
                  allEmbIds.any (fun embId => effectExpiresWithLeavingObj acc embId .command allEmbIds ce)
                | none => false)
              (cause := some embCause) (reconcileControl := false) (skipLogIds := effSkipLogIds)
              (preState? := some pre) (deferPlayFromExileLogs := true)
          let g := leaving.foldl (fun acc (mEid, _) =>
            let mCause := if mEid == eid then some expCause else some embCause
            expireEffectById acc mEid (cause := mCause) (reconcileControl := false)
              (preState? := some pre) (suppressEmblemLog := true)
              (suppressReturnLog := true) (skipLogIds := effSkipLogIds)
              (deferPlayFromExileLogs := true)) g
          let g :=
            if (g.activeEffect? eid).isSome then
              g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := expCause))
            else g
          let g :=
            if suppressEmblemLog then g
            else
              childEmbNames.foldl (fun acc cName => acc.logMsg s!"{cName} ends")
                (g.logMsg s!"{embName} ends")
          let g :=
            if suppressReturnLog then g
            else
              controlSingles.foldl (fun acc (cid, o) =>
                if effSkipLogIds.contains cid then acc
                else
                  match acc.findObject? cid with
                  | none => acc
                  | some cur =>
                    let prevCtrl := pre.controllerOf ((pre.findObject? cid).getD o)
                    let curCtrl := acc.controllerOf cur
                    if curCtrl == prevCtrl then acc
                    else
                      let objName := acc.name cur
                      let p := (cur.defaultController.orElse (fun _ => cur.controller)).getD cur.owner
                      let othersRemain := !(acc.appliedControlEffectIds cur).isEmpty
                      if othersRemain then
                        match curCtrl with
                        | some q =>
                          if (acc.player q).leftTheGame then acc
                          else acc.logMsg s!"{objName} returns to {(acc.player q).name}'s control"
                        | none => acc
                      else if (acc.player p).leftTheGame then acc
                      else acc.logMsg s!"{objName} returns to {(acc.player p).name}'s control") g
          let g :=
            if reconcileControl then
              reconcileControlAfterTransitionFwd pre g (cause := some embCause)
                (deferPlayFromExileLogs := true) (fromEventIdx? := some fromIdx)
            else g
          if deferPlayFromExileLogs then g else emitExpiredPlayFromExileLogs pre g fromIdx
        else
          g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := expCause))
      | none =>
        g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := expCause))
    | _ =>
      let fromIdx := g.events.size
      let g := g.record (GameEvent.effectExpired g.turnNumber eid eff (cause := expCause))
      match eff with
      | .layered _ (.control _) _ =>
        if reconcileControl then
          reconcileControlAfterTransitionFwd pre g (cause := some expCause)
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
        else g
      | .layered _ (.copy _) _ =>
        if reconcileControl then
          reconcileControlAfterTransitionFwd pre g (cause := some expCause)
            (deferPlayFromExileLogs := deferPlayFromExileLogs)
        else g
      | .permission _ (.playFromExile _ _) _ =>
        if deferPlayFromExileLogs then g else emitExpiredPlayFromExileLogs pre g fromIdx
      | _ => g

/-- End every active copy effect matching `sel`, each under its own `EffectId`,
restoring the original printed card on battlefield objects (CR 707).
Does not cause the permanent to enter or leave the battlefield. -/
partial def restoreCopiesWhere (g : Game)
    (sel : Game → EffectId → Option GameObject → EffectDuration → Bool)
    (cause : Option EventCause := none)
    (reconcileControl : Bool := true)
    (suppressLog : Bool := false)
    (skipLogIds : Array ObjectId := #[])
    (preState? : Option Game := none)
    (deferPlayFromExileLogs : Bool := false) : Game :=
  let preRef := preState?.getD g
  let expEids : Array EffectId :=
    g.activeEffects.foldl (fun acc (eid, e) =>
      match e with
      | .layered (.objects ids) (.copy _) d =>
        let bfObjs := ids.filterMap (fun id => (g.findObject? id).filter (fun o => o.zone == .battlefield))
        if bfObjs.any (fun o => sel g eid (some o) d) || sel g eid none d then
          acc.push eid
        else acc
      | .layered _ (.copy _) d =>
        if g.battlefield.any (fun o => sel g eid (some o) d) || sel g eid none d then
          acc.push eid
        else acc
      | _ => acc) #[]
  if expEids.isEmpty then g
  else
    let candLogs : Array (ObjectId × CardDef) :=
      if suppressLog then #[]
      else
        let objCandIds : Array ObjectId :=
          g.activeEffects.foldl (fun idsAcc (eid, e) =>
            if !expEids.contains eid then idsAcc
            else
              match e with
              | .layered (.objects ids) (.copy _) _ =>
                ids.foldl (fun a id =>
                  if a.contains id || skipLogIds.contains id then a
                  else if (g.findObject? id).any (fun o => o.zone == .battlefield) then a.push id
                  else a) idsAcc
              | _ => idsAcc) #[]
        let candIds : Array ObjectId :=
          g.objects.foldl (fun a o =>
            if o.zone != .battlefield || a.contains o.id || skipLogIds.contains o.id then a
            else a.push o.id) objCandIds
        let preLiveG : Game := { preRef with activeEffects := g.activeEffects }
        let postLiveG : Game :=
          { preRef with activeEffects := g.activeEffects.filter (fun (eid, _) => !expEids.contains eid) }
        candIds.filterMap fun oid =>
          let preObj? := (preRef.findObject? oid).orElse (fun _ => g.findObject? oid)
          match preObj? with
          | none => none
          | some preObj =>
            let preChain := preLiveG.activeLayer1CopyChain preObj
            match preChain.back? with
            | some (topEid, topCard) =>
              let postTopEid? := (postLiveG.activeLayer1CopyChain preObj).back?.map Prod.fst
              if postTopEid? != some topEid then some (oid, topCard) else none
            | none => none
    let acc :=
      expEids.foldl (fun acc2 eid =>
        expireEffectById acc2 eid (cause := cause) (reconcileControl := false)
          (preState? := some preRef) (skipLogIds := skipLogIds)
          (deferPlayFromExileLogs := deferPlayFromExileLogs)) g
    let effSkipLogIds : Array ObjectId :=
      if reconcileControl && acc.players.any (·.leftTheGame) then
        (coDepartingIdsFwd acc #[]).foldl
          (fun a cid => if a.contains cid then a else a.push cid) skipLogIds
      else skipLogIds
    let acc :=
      candLogs.foldl (fun acc2 (oid, topCard) =>
        if effSkipLogIds.contains oid then acc2
        else
          match (acc2.findObject? oid).filter (fun cur => cur.zone == .battlefield) with
          | some cur =>
            let restName := acc2.name cur
            acc2.logMsg s!"{restName} is no longer a copy of {topCard.name}"
          | none => acc2) acc
    if reconcileControl then
      let expCause := acc.resolveOptionalCause cause (defaultCause := .gameRule .continuousEffect)
      reconcileControlAfterTransitionFwd preRef acc (cause := some expCause)
        (deferPlayFromExileLogs := deferPlayFromExileLogs)
    else acc

end

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
    (cause : Option EventCause := none) (reconcileControl : Bool := true)
    (preState? : Option Game := none) (suppressEmblemLog : Bool := false)
    (suppressReturnLog : Bool := false) (skipLogIds : Array ObjectId := #[])
    (deferPlayFromExileLogs : Bool := false) : Game :=
  let pre := preState?.getD g
  let fromIdx := g.events.size
  let matching := g.activeEffects.filter (fun (_, e) => pred e)
  let gAfter :=
    matching.foldl (fun acc (eid, _) =>
      acc.expireEffectById eid (cause := cause) (reconcileControl := reconcileControl)
        (preState? := some pre) (suppressEmblemLog := suppressEmblemLog)
        (suppressReturnLog := suppressReturnLog) (skipLogIds := skipLogIds)
        (deferPlayFromExileLogs := true)) g
  if deferPlayFromExileLogs then gAfter
  else emitExpiredPlayFromExileLogs pre gAfter fromIdx

/-- Record and apply the expiration of every active continuous effect equal to
`eff`, e.g. when their shared duration ends (CR 611). -/
def expireAll (g : Game) (eff : ContinuousEffect)
    (cause : Option EventCause := none) : Game :=
  g.expireMatching (· == eff) (cause := cause)

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
      | some (src, ctrl) => some (.oneShotEffect none src ctrl)
      | none => some (.gameRule .impending)
  match g.findObject? id with
  | none => g
  | some o =>
    if o.zone != .battlefield || !(g.baseCard o).impending.isSome then g
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

/-- Record `CombatEvent.becameAttacking` for `id` targeting `target` (defaulting
to `id`'s opponent) when a legal attack target exists (CR 508.4 / 810.7). -/
def markAttacking (g : Game) (id : ObjectId) (target : Option AttackTarget := none)
    (cause : Option EventCause := some (.turnBased .declareAttackers)) : Game :=
  match g.findObject? id with
  | some o =>
    let ctrl := (g.controllerOf o).getD g.activePlayer
    let tgt? : Option AttackTarget :=
      match target with
      | some (.player p) =>
        if g.stillInGame p then some (.player p)
        else (g.defaultAttackOpponent? ctrl).map .player
      | some (.planeswalker pwId) =>
        if (g.findObject? pwId).any (fun pw => pw.isOnBattlefield && g.isPlaneswalker pw) then
          some (.planeswalker pwId)
        else (g.defaultAttackOpponent? ctrl).map .player
      | some (.battle bId) =>
        if (g.findObject? bId).any (·.isOnBattlefield) then some (.battle bId)
        else (g.defaultAttackOpponent? ctrl).map .player
      | none =>
        (g.defaultAttackOpponent? ctrl).map .player
    match tgt? with
    | none => g
    | some tgt =>
      let effCause :=
        g.resolveOptionalCause cause (fallbackSrc := some id)
          (defaultCause := .turnBased .declareAttackers)
      g.record (GameEvent.becameAttacking g.turnNumber (g.snapshot o) tgt (cause := effCause))
  | none => g

/-- Record `CombatEvent.blockersDeclared` for `id` blocking `attackers` (CR 509.1g). -/
def markBlocking (g : Game) (id : ObjectId) (attackers : Array ObjectId)
    (cause : Option EventCause := some (.turnBased .declareBlockers)) : Game :=
  match g.findObject? id with
  | some o =>
    let p := (g.controllerOf o).getD o.owner
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
ceases to exist (CR 400.7, CR 611), each under its own `EffectId`. -/
def expireEffectsOnLeavingObject (g : Game) (o : GameObject)
    (cause : Option EventCause := some (.gameRule .leavingZone))
    (reconcileControl : Bool := true)
    (preState? : Option Game := none) (suppressEmblemLog : Bool := false)
    (suppressReturnLog : Bool := false) (skipLogIds : Array ObjectId := #[])
    (coLeavingIds : Array ObjectId := #[])
    (deferPlayFromExileLogs : Bool := false) : Game :=
  g.expireMatching (fun e => g.effectExpiresWithLeavingObj o.id o.zone coLeavingIds e)
    (cause := cause) (reconcileControl := reconcileControl)
    (preState? := preState?) (suppressEmblemLog := suppressEmblemLog)
    (suppressReturnLog := suppressReturnLog) (skipLogIds := skipLogIds)
    (deferPlayFromExileLogs := deferPlayFromExileLogs)

/-- Route `.whileInZone old.id old.zone` (and optionally `.whileSource* old.id`
when `includeWhileSource` is true, plus transitive command emblems and
multi-target/scoped `.control`) `.copy` and `.control` expirations through a
single `restoreCopiesWhere` and a single `pre -> post` control-return log pass
before `expireEffectsOnLeavingObject` (CR 114.5 / 400.7 / 611.2 / 613.7 / 707.2). -/
def expireLeavingObjectEffectsWithLogs (g : Game) (old : GameObject)
    (cause : Option EventCause := some (.gameRule .leavingZone))
    (preState? : Option Game := none) (suppressEmblemLog : Bool := false)
    (suppressReturnLog : Bool := false) (skipLogIds : Array ObjectId := #[])
    (coLeavingIds : Array ObjectId := #[])
    (includeWhileSource : Bool := false) : Game :=
  let pre := preState?.getD g
  let matchesWhileSrc (d : EffectDuration) : Bool :=
    includeWhileSource && old.zone == .battlefield &&
      match d with
      | .whileSourceOnBattlefield src | .untilSourceLeaves src | .whileSourceHasCounter src _ =>
        src == old.id
      | _ => false
  let baseLeavingIds : Array ObjectId :=
    if coLeavingIds.isEmpty then #[old.id]
    else if coLeavingIds.contains old.id then coLeavingIds
    else coLeavingIds.push old.id
  let zoneOfLeaving (lid : ObjectId) : Zone :=
    if lid == old.id then old.zone
    else
      (pre.findObject? lid).map (·.zone)
        |>.orElse (fun _ => (g.findObject? lid).map (·.zone))
        |>.getD old.zone
  let seedEmbIds : Array ObjectId :=
    let initCmds := baseLeavingIds.filter (fun lid => zoneOfLeaving lid == .command)
    g.activeEffects.foldl (fun acc (_, e) =>
      match e with
      | .gameRule (.commandEmblem embId) d =>
        if !acc.contains embId &&
            (matchesWhileSrc d ||
              baseLeavingIds.any (fun lid =>
                g.effectExpiresWithLeavingObj lid (zoneOfLeaving lid) baseLeavingIds e)) then
          acc.push embId
        else acc
      | _ => acc) initCmds
  let embIds := g.expandTransitiveCommandEmblems seedEmbIds
  let liveEmbIds : Array ObjectId :=
    embIds.filter (fun embId => embId != old.id && (g.findObject? embId).any (·.zone == .command))
  let leavingIds : Array ObjectId :=
    embIds.foldl (fun acc id => if acc.contains id then acc else acc.push id) baseLeavingIds
  let expiresForOld (acc : Game) (ce : ContinuousEffect) : Bool :=
    matchesWhileSrc ce.duration ||
      baseLeavingIds.any (fun lid => acc.effectExpiresWithLeavingObj lid (zoneOfLeaving lid) leavingIds ce) ||
      embIds.any (fun eid => acc.effectExpiresWithLeavingObj eid .command leavingIds ce)
  let controlTargets : Array (ObjectId × GameObject) :=
    if suppressReturnLog then #[]
    else
      g.activeEffects.foldl (fun targets (eid, e) =>
        if !expiresForOld g e then targets
        else collectControlTargets pre g eid e targets (excludeId? := some old.id)) #[]
  let bfsCommandEmblems : Array (EffectId × ObjectId) :=
    liveEmbIds.foldl (fun acc embId =>
      g.activeEffects.foldl (fun a (eid, s) =>
        match s with
        | .gameRule (.commandEmblem eidEmb) _ =>
          if eidEmb == embId && !a.any (·.1 == eid) then a.push (eid, embId) else a
        | _ => a) acc) #[]
  let directWhileSrcEmblems : Array (EffectId × ObjectId) :=
    if !includeWhileSource || old.zone != .battlefield then #[]
    else
      g.activeEffects.foldl (fun acc (eid, s) =>
        match s with
        | .gameRule (.commandEmblem embId) d =>
          if matchesWhileSrc d && !liveEmbIds.contains embId && !acc.any (·.1 == eid) then
            acc.push (eid, embId)
          else acc
        | _ => acc) #[]
  let g :=
    g.restoreCopiesWhere
      (fun acc cEid _ _ =>
        match acc.activeEffect? cEid with
        | some ce => expiresForOld acc ce
        | none => false)
      (cause := cause) (reconcileControl := false)
      (skipLogIds := skipLogIds) (preState? := some pre)
      (deferPlayFromExileLogs := true)
  let g :=
    (bfsCommandEmblems ++ directWhileSrcEmblems).foldl (fun acc (eid, _) =>
      acc.expireEffectById eid (cause := cause) (reconcileControl := false)
        (preState? := some pre) (suppressEmblemLog := suppressEmblemLog)
        (suppressReturnLog := true) (skipLogIds := skipLogIds)
        (deferPlayFromExileLogs := true)) g
  let g := g.expireEffectsOnLeavingObject old (cause := cause) (reconcileControl := false)
    (preState? := some pre) (suppressEmblemLog := suppressEmblemLog)
    (suppressReturnLog := true) (skipLogIds := skipLogIds)
    (coLeavingIds := leavingIds) (deferPlayFromExileLogs := true)
  let g :=
    if includeWhileSource && old.zone == .battlefield then
      g.expireMatching (fun s => matchesWhileSrc s.duration)
        (cause := cause) (reconcileControl := false)
        (preState? := some pre) (suppressEmblemLog := suppressEmblemLog)
        (suppressReturnLog := true) (skipLogIds := skipLogIds)
        (deferPlayFromExileLogs := true)
    else g
  if suppressReturnLog then g
  else
    controlTargets.foldl (fun acc (tid, o) =>
      if skipLogIds.contains tid then acc
      else
        match acc.findObject? tid with
        | none => acc
        | some cur =>
          if !cur.isBattlefieldObject then acc
          else
            let prevCtrl := pre.controllerOf ((pre.findObject? tid).getD o)
            let curCtrl := acc.controllerOf cur
            if curCtrl == prevCtrl then acc
            else
              let objName := acc.name cur
              let p := (cur.defaultController.orElse (fun _ => cur.controller)).getD cur.owner
              let othersRemain := !(acc.appliedControlEffectIds cur).isEmpty
              if othersRemain then
                match curCtrl with
                | some q =>
                  if (acc.player q).leftTheGame then acc
                  else acc.logMsg s!"{objName} returns to {(acc.player q).name}'s control"
                | none => acc
              else if (acc.player p).leftTheGame then
                acc
              else
                acc.logMsg s!"{objName} returns to {(acc.player p).name}'s control") g

/-- Remove `eid` from a live `sid`'s `leaveTriggerExile` and `linkedExile`
metadata lists once `eid` has been consumed by a linked ability (CR 607.2a). -/
def pruneLinkedExileId (g : Game) (sid eid : ObjectId) : Game :=
  match g.findObject? sid with
  | none => g
  | some src =>
    let g :=
      if src.leaveTriggerExile.contains eid then
        g.changeObject sid (.leaveTriggerExile (src.leaveTriggerExile.filter (· != eid)))
      else g
    let src := g.object! sid
    if src.linkedExile.contains eid then
      g.changeObject sid (.linkedExile (src.linkedExile.filter (· != eid)))
    else g

/-- Record that combat damage was dealt to `p`. -/
def noteCombatDamageTo (g : Game) (p : PlayerId) (source : EventObject)
    (cause : Option EventCause := none) : Game :=
  let effCause :=
    g.resolveOptionalCause cause (fallbackSrc := source.id)
      (defaultCause := .turnBased (.assignCombatDamage false))
  g.record (GameEvent.damagedPlayer g.turnNumber source p 1 true (cause := effCause))

/-- Restore copy effects that last until end of turn (including
`.untilEndOfNextTurnOf` on the active team's final shared-turn seat once that
shared turn has begun, CR 514.2 / 611.2a / 805.4 / 810.2). -/
def restoreCopiesUntilEot (g : Game) (reconcileControl : Bool := true)
    (skipLogIds : Array ObjectId := #[])
    (deferPlayFromExileLogs : Bool := false) : Game :=
  g.restoreCopiesWhere (fun acc eid _ d =>
    d == .untilEndOfTurn ||
      match d with
      | .untilEndOfNextTurnOf q =>
        (q == acc.activePlayer || acc.areTeammates q acc.activePlayer) &&
          acc.isSharedTurnFinalSeat && acc.hasTurnBegunSince eid q
      | _ => false)
    (cause := some (.turnBased .cleanupClear))
    (reconcileControl := reconcileControl)
    (skipLogIds := skipLogIds)
    (deferPlayFromExileLogs := deferPlayFromExileLogs)

/-- Restore copy effects that last until `p`'s next turn (or also
`.untilEndOfNextTurnOf p` — and any dead teammate `q` when `p`'s entire shared
team has left/lost — when `departed` is true under CR 800.4m / 805.2). -/
def restoreCopiesUntilNextTurn (g : Game) (p : PlayerId) (departed : Bool := false)
    (reconcileControl : Bool := true)
    (skipLogIds : Array ObjectId := #[])
    (deferPlayFromExileLogs : Bool := false) : Game :=
  g.restoreCopiesWhere (fun acc _ _ d =>
    let deadTeamTeammate (q : PlayerId) : Bool :=
      departed && !(acc.teamMembers p).any acc.stillInGame && acc.areTeammates q p
    match d with
    | .untilNextTurnOf q =>
      q == p || (!departed && acc.areTeammates q p) || deadTeamTeammate q
    | .untilEndOfNextTurnOf q =>
      departed && (q == p || deadTeamTeammate q)
    | _ => false)
    (cause := some (.turnBased .expireAtStepBegin))
    (reconcileControl := reconcileControl)
    (skipLogIds := skipLogIds)
    (deferPlayFromExileLogs := deferPlayFromExileLogs)

/-- Restore copy effects that last until `srcId` leaves the battlefield. -/
def restoreCopiesUntilSourceLeaves (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.gameRule .leavingZone))
    (suppressLog : Bool := false)
    (skipLogIds : Array ObjectId := #[])
    (preState? : Option Game := none) : Game :=
  g.restoreCopiesWhere (fun _ _ _ d =>
    match d with
    | .untilSourceLeaves s | .whileSourceOnBattlefield s | .whileSourceHasCounter s _ => s == srcId
    | _ => false)
    (cause := cause) (reconcileControl := false) (suppressLog := suppressLog)
    (skipLogIds := skipLogIds) (preState? := preState?)

/-- End the control-changing effects that last until `srcId` leaves, each under
its own `EffectId` (Super Hero Civil War; MSH 143). Other control-changing
effects on the same permanent keep applying (CR 613.7). -/
def restoreControlUntilSourceLeaves (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.gameRule .leavingZone))
    (preState? : Option Game := none)
    (reconcileControl : Bool := true)
    (suppressReturnLog : Bool := false)
    (skipLogIds : Array ObjectId := #[])
    (extraSingleTargets : Array (ObjectId × GameObject) := #[])
    (forceReconcile : Bool := false)
    (deferPlayFromExileLogs : Bool := false) : Game :=
  let preRef := preState?.getD g
  let (matchingEids, controlTargets) :=
    g.activeEffects.foldl (fun (eids, targets) (eid, e) =>
      match e with
      | .layered _ (.control _) (.whileSourceOnBattlefield s)
      | .layered _ (.control _) (.untilSourceLeaves s)
      | .layered _ (.control _) (.whileSourceHasCounter s _) =>
        if s != srcId then (eids, targets)
        else
          let targets' :=
            if suppressReturnLog then targets
            else collectControlTargets preRef g eid e targets
          (eids.push eid, targets')
      | _ => (eids, targets)) (#[], extraSingleTargets)
  if matchingEids.isEmpty && !forceReconcile && controlTargets.isEmpty then g
  else
    let resolvedCause := g.resolveOptionalCause cause (defaultCause := .gameRule .leavingZone)
    let g :=
      matchingEids.foldl (fun acc eid =>
        acc.expireEffectById eid (cause := cause) (reconcileControl := false)
          (preState? := some preRef)) g
    let effSkipLogIds : Array ObjectId :=
      if reconcileControl then
        (coDepartingIdsFwd g #[]).foldl
          (fun acc cid => if acc.contains cid then acc else acc.push cid) skipLogIds
      else skipLogIds
    let g :=
      if suppressReturnLog then g
      else
        controlTargets.foldl (fun acc (id, o) =>
          if effSkipLogIds.contains id then acc
          else
            match acc.findObject? id with
            | none => acc
            | some cur =>
              if !cur.isBattlefieldObject then acc
              else
                let prevCtrl := preRef.controllerOf ((preRef.findObject? id).getD o)
                let curCtrl := acc.controllerOf cur
                if curCtrl == prevCtrl then acc
                else
                  let objName := acc.name cur
                  let p := (cur.defaultController.orElse (fun _ => cur.controller)).getD cur.owner
                  let othersRemain := !(acc.appliedControlEffectIds cur).isEmpty
                  if othersRemain then
                    match curCtrl with
                    | some q =>
                      if (acc.player q).leftTheGame then acc
                      else acc.logMsg s!"{objName} returns to {(acc.player q).name}'s control"
                    | none => acc
                  else if (acc.player p).leftTheGame then
                    acc
                  else
                    acc.logMsg s!"{objName} returns to {(acc.player p).name}'s control") g
    if reconcileControl then
      reconcileControlAfterTransitionFwd preRef g (cause := some resolvedCause)
        (deferPlayFromExileLogs := deferPlayFromExileLogs)
    else g

/-- Expire all continuous effects that last for as long as `srcId` remains on
the battlefield or until `srcId` leaves the battlefield (CR 611.2a / 611.2b),
each under its own `EffectId`. -/
def expireWhileSourceEffects (g : Game) (srcId : ObjectId)
    (cause : Option EventCause := some (.gameRule .leavingZone))
    (preState? : Option Game := none)
    (reconcileControl : Bool := true)
    (suppressReturnLog : Bool := false)
    (skipLogIds : Array ObjectId := #[])
    (suppressEmblemLog : Bool := false)
    (deferPlayFromExileLogs : Bool := false) : Game :=
  let preRef := preState?.getD g
  let fromIdx := g.events.size
  let effSkipLogIds : Array ObjectId :=
    (coDepartingIdsFwd g #[srcId]).foldl
      (fun acc cid => if acc.contains cid then acc else acc.push cid) skipLogIds
  let matchesSrcDuration (d : EffectDuration) : Bool :=
    match d with
    | .whileSourceOnBattlefield src | .untilSourceLeaves src | .whileSourceHasCounter src _ =>
      src == srcId
    | _ => false
  let seedEmbIds : Array ObjectId :=
    g.activeEffects.foldl (fun acc (_, s) =>
      match s with
      | .gameRule (.commandEmblem embId) d =>
        if matchesSrcDuration d && !acc.contains embId then acc.push embId else acc
      | _ => acc) #[]
  let allEmbCands := g.expandTransitiveCommandEmblems seedEmbIds
  let emblemIds : Array ObjectId :=
    allEmbCands.filter (fun embId => (g.findObject? embId).any (·.zone == .command))
  let bfsCommandEmblems : Array (EffectId × ObjectId) :=
    emblemIds.foldl (fun acc embId =>
      g.activeEffects.foldl (fun a (eid, s) =>
        match s with
        | .gameRule (.commandEmblem eidEmb) _ =>
          if eidEmb == embId && !a.any (·.1 == eid) then a.push (eid, embId) else a
        | _ => a) acc) #[]
  let directCommandEmblems : Array (EffectId × ObjectId) :=
    g.activeEffects.foldl (fun acc (eid, s) =>
      match s with
      | .gameRule (.commandEmblem embId) d =>
        if matchesSrcDuration d && !emblemIds.contains embId && !acc.any (·.1 == eid) then
          acc.push (eid, embId)
        else acc
      | _ => acc) #[]
  let commandEmblemEntries : Array (EffectId × ObjectId) := bfsCommandEmblems ++ directCommandEmblems
  let expiresWithEmblem (embId : ObjectId) (e : ContinuousEffect) : Bool :=
    g.effectExpiresWithLeavingObj embId .command emblemIds e
  let (hadEmbControl, embControlTargets) :=
    if emblemIds.isEmpty then (false, #[])
    else
      g.activeEffects.foldl (fun (hadC, targets) (eid, e) =>
        if !emblemIds.any (expiresWithEmblem · e) then (hadC, targets)
        else
          match e with
          | .layered _ (.control _) _ =>
            let targets' :=
              if suppressReturnLog then targets
              else collectControlTargets preRef g eid e targets
            (true, targets')
          | _ => (hadC, targets)) (false, #[])
  let hadDirectControl : Bool :=
    g.activeEffects.any fun (_, e) =>
      match e with
      | .layered _ (.control _) d => matchesSrcDuration d
      | _ => false
  let preCopyEvents := g.events.size
  let g :=
    g.restoreCopiesWhere
      (fun acc eid _ d =>
        matchesSrcDuration d ||
          (!emblemIds.isEmpty &&
            match acc.activeEffect? eid with
            | some e => emblemIds.any (acc.effectExpiresWithLeavingObj · .command emblemIds e)
            | none => false))
      (cause := cause) (reconcileControl := false) (suppressLog := false)
      (skipLogIds := effSkipLogIds) (preState? := some preRef)
      (deferPlayFromExileLogs := true)
  let expiredAnyCopy := g.events.size > preCopyEvents
  let g :=
    commandEmblemEntries.foldl (fun acc (eid, _) =>
      acc.expireEffectById eid (cause := cause) (reconcileControl := false)
        (preState? := some preRef) (suppressEmblemLog := suppressEmblemLog)
        (suppressReturnLog := true) (skipLogIds := effSkipLogIds)
        (deferPlayFromExileLogs := true)) g
  let g := g.restoreControlUntilSourceLeaves srcId (cause := cause) (preState? := some preRef)
    (reconcileControl := false) (suppressReturnLog := suppressReturnLog)
    (skipLogIds := effSkipLogIds) (extraSingleTargets := embControlTargets)
    (forceReconcile := hadEmbControl)
  let g := g.expireMatching (fun s => matchesSrcDuration s.duration)
    (cause := cause) (preState? := some preRef) (reconcileControl := false)
    (suppressEmblemLog := suppressEmblemLog) (deferPlayFromExileLogs := true)
  let g :=
    if (!commandEmblemEntries.isEmpty || expiredAnyCopy || hadEmbControl || hadDirectControl) &&
        reconcileControl then
      let resolvedCause := g.resolveOptionalCause cause (defaultCause := .gameRule .leavingZone)
      reconcileControlAfterTransitionFwd preRef g (cause := some resolvedCause)
        (deferPlayFromExileLogs := true) (fromEventIdx? := some fromIdx)
    else g
  if deferPlayFromExileLogs then g else emitExpiredPlayFromExileLogs preRef g fromIdx

/-- Last player-controlling effect wins (MSH 259). The controlled player
remains the active player on their turn (MSH 300) and still controls their
permanents (MSH 358). `onNextTurn` makes the control start on the controlled
player's next turn they actually take. -/
def setPlayerControl (g : Game) (you them : PlayerId) (onNextTurn : Bool := false) : Game :=
  if !g.stillInGame you || !g.stillInGame them then g
  else
    let g :=
      g.createEffect (.playerControl you them onNextTurn)
        |>.logMsg
          s!"{(g.player you).name} controls {(g.player them).name} during their next turn"
    match g.players.find? (fun pl => g.areTeammates them pl.id) with
    | some mate =>
      if mate.id == you then g
      else
        g.logMsg
          s!"{(g.player you).name} also controls {mate.name} (Two-Headed Giant team)"
    | none => g

/-- Record putting `n` counters of `kind` on `id` via `PermanentEvent.counters`
(CR 122.1). Does nothing when `n == 0`. -/
def recordPutCounters (g : Game) (id : ObjectId) (kind : CounterKind) (n : Nat)
    (byPlayer : Option PlayerId := none) (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.recordPutCounters id kind n byPlayer cause)
  else
    match g.findObject? id with
    | none => g
    | some o =>
      let putter := byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
      let (n', applied, cause', choice?, _) :=
        g.replaceCountersPutChoice o kind n (putter := putter) (cause := cause)
      match choice? with
      | some (chooser, choices) =>
        g.promptChooseReplacement chooser choices
          (.recordPutCounters id kind n byPlayer cause)
      | none =>
        let g := g.consumeReplacementOrder applied
        if n' == 0 then g
        else
          let pre := g
          let wasZeroOnBf := o.isOnBattlefield && o.status.counterCount kind == 0
          let hasWhileCounterCtrlOrCopy :=
            wasZeroOnBf &&
              g.activeEffects.any (fun (_, e) =>
                match e with
                | .layered _ (.control _) (.whileSourceHasCounter s k)
                | .layered _ (.copy _) (.whileSourceHasCounter s k) => s == id && k == kind
                | _ => false)
          let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := putter)
          let g := g.record (GameEvent.counters g.turnNumber putter (g.snapshot o) kind n' (cause := finalCause))
          let g := if kind == .time then g.syncImpendingNotACreature id (cause := some finalCause) else g
          if hasWhileCounterCtrlOrCopy then
            reconcileControlAfterTransitionFwd pre g (cause := some finalCause)
          else g

/-- Put all non-+1/+1 counters from `«from»` (with `extra` added to each
non-zero counter kind) onto `id`, emitting one `PermanentEvent.counters` put
per non-zero counter kind in a single batch (CR 122.1). -/
def putCountersExceptPlusOne (g : Game) (id : ObjectId) («from» : Status)
    (extra : Nat := 0) (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  let bag := «from».toCounterBag.filter (fun (k, n) => k != .plusOnePlusOne && n > 0)
  if bag.isEmpty then g
  else
    (g.withBatchCore cause fun g => Id.run do
      let mut g := g
      for (kind, cnt) in bag do
        if let .chooseReplacement .. := g.pending then
          g := g.chainPendingReplacement (.recordPutCounters id kind (cnt + extra) byPlayer cause)
        else
          g := g.recordPutCounters id kind (cnt + extra) (byPlayer := byPlayer) (cause := cause)
      return g).flushQueuedLinkedExileFwd

/-- Begin a `ResolutionChoice` for `p`, opening a `ContinuationFrame` if none is active. -/
def beginResolutionChoice (g : Game) (p : PlayerId) (choice : ResolutionChoice) (msg : String := "") : Game :=
  let g :=
    if g.continuations.isEmpty then g.change (.pushContinuationFrame {})
    else g
  let g := g.change (.pending (.resolutionChoice p choice))
  if msg.isEmpty then g else g.logMsg msg

/-- Append departed player `p` to any `.restorePending`, `.leavePlayersWhoLost`,
`.finishConcede`, or `.concedePlayersLoop` continuation in `g.pendingReplacement`
or `g.outerPendingReplacements` so `.restorePending` re-runs
`redirectPendingAfterLeave` after the replacement pause finishes (CR 616.1 / 800.4). -/
def appendDepartedToContinuations (g : Game) (p : PlayerId) : Game :=
  let g :=
    match g.pendingReplacement with
    | some cont =>
      let cont' := cont.appendDeparted p
      if cont' != cont then g.change (.pendingReplacement (some cont')) else g
    | none => g
  let outers := g.outerPendingReplacements
  let outers' := outers.map (·.appendDeparted p)
  if outers' == outers then g
  else
    let g := (List.range outers.size).foldl (fun acc _ => acc.change .popOuterPendingReplacement) g
    outers'.foldl (fun acc c => acc.change (.pushOuterPendingReplacement c)) g

def appendDepartedManyToContinuations (g : Game) (dep : Array PlayerId) : Game :=
  dep.foldl (fun acc p => acc.appendDepartedToContinuations p) g

end Game
end Mtg.Engine
