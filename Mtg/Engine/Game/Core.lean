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
  players : Array Player
  objects : Array GameObject
  stack : Array StackEntry := #[]
  activePlayer : PlayerId := ⟨0⟩
  priority : PlayerId := ⟨0⟩
  step : Step := .untap
  turnNumber : Nat := 1
  startingPlayer : PlayerId := ⟨0⟩
  isFirstTurn : Bool := true
  pending : Pending := .none
  nextObjectId : Nat := 0
  timestamp : Nat := 0
  rng : Rng := Rng.ofSeed 1
  /-- When true, random events become `Pending.resolveRandom` instead of
  using `rng`. -/
  norandom : Bool := false
  /-- Continuation after a `--norandom` result is applied. -/
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
  /-- A creature went to a graveyard from the battlefield this turn
  (used by cost reductions such as Dreaded Bat-Cloud). Cleared as the turn ends. -/
  creatureDiedThisTurn : Bool := false
  /-- Spell or ability proposed and waiting for mana abilities / payment
  (CR 601.2f–h / 602.2b). -/
  proposedSpell : Option ProposedSpell := none
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
  /-- It is night (CR 702.145). Used by Nick Fury / daybound (MSH 191). -/
  isNight : Bool := false
  /-- Draw these cards after the current scry finishes (e.g. Hithlain Knots). -/
  pendingDrawAfterScry : Option (PlayerId × Nat) := none
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
  /-- Player most recently dealt combat damage by a creature whose
  combat-damage trigger is resolving (Cavern-Hoard Dragon). -/
  lastCombatDamagePlayer : Option PlayerId := none
  /-- True while a spell is being cast from the top of a library
  (Elven Chorus cannot show the new top until that finishes). -/
  castingFromTop : Bool := false
  /-- Creature cards that went from the battlefield to a graveyard this turn
  (Supper for Spiders). Cleared as the turn ends. -/
  battlefieldCreaturesToGyThisTurn : Array ObjectId := #[]
  /-- Most recent life loss amount, for “mills that many” triggers. -/
  lastLifeLost : Option (PlayerId × Nat) := none
  /-- Most recent noncombat damage marked on a permanent. -/
  lastNoncombatDamage : Option (ObjectId × Nat) := none
  /-- Cards in exile that return at the beginning of the next end step
  (Roll-Roll-Roll-Roll and similar delayed blinks). -/
  delayedEndStepReturns : Array ObjectId := #[]
  /-- Source of the current connive action, if any (MSH / CR 701.47). -/
  conniveSource : Option ObjectId := none
  /-- Most recent creature that became tapped (Captain America, Living Legend). -/
  lastBecameTapped : Option ObjectId := none
  /-- Extra combat phases still to begin after the current combat (Hulk enrage). -/
  additionalCombatPhases : Nat := 0
  /-- Enrage triggers that will grant an additional combat when they resolve. -/
  enrageGrantsAdditionalCombat : Nat := 0
  /-- The Sensational She-Hulk chose to deal damage this turn (MSH 95 / 142). -/
  sheHulkDamageUsedThisTurn : Bool := false
  /-- A pending MSH reflexive trigger: (controller, source, kind tag).
  Kind is `0` grant-indestructible, `1` deal-2, `2` Hawkeye modes (paid count
  in `pendingMshReflexivePaid`). -/
  pendingMshReflexive : Option (PlayerId × Option ObjectId × Nat) := none
  /-- Times Hawkeye paid for Trick Arrows (0–3). -/
  pendingMshReflexivePaid : Nat := 0
  /-- Player-controlling effect: (you, the player you control). Last created
  wins (MSH 259). -/
  playerControl : Option (PlayerId × PlayerId) := none
  /-- If the controlled player skips their next turn, control applies to the
  next turn they actually take (MSH 221). -/
  controlOnNextTakenTurn : Bool := false
  /-- Loki delayed copy: (controller, Loki's id if still known, last-known
  power). Compared at cast time (MSH 109). -/
  pendingLokiCopy : Option (PlayerId × Option ObjectId × Int) := none
  /-- Extort triggers waiting for a pay/don't-pay decision (MSH 371). -/
  pendingExtort : Nat := 0
  /-- Controller of the pending extort trigger. -/
  pendingExtortController : Option PlayerId := none
  /-- Until EOT, this player's creatures with toughness greater than power
  assign combat damage equal to toughness (The Kingpin of Crime; MSH 287). -/
  assignCombatDamageEqualToughness : Option PlayerId := none
  /-- Most recent attacking creature that died (new GY object id; Ares). -/
  lastDiedAttacker : Option ObjectId := none
  /-- World War Hulk chapter I: the next red or green creature spell this
  player casts this turn may be cast without paying its mana cost (MSH 343). -/
  pendingFreeRGCreature : Option PlayerId := none
  /-- Cards exiled to pay the current Zemo boast activation (MSH 227). -/
  zemoBoastExiles : Array ObjectId := #[]
  /-- Remaining discards for Thirst for Knowledge (MSH 344). An artifact
  card finishes the requirement early. -/
  thirstDiscardsLeft : Nat := 0
  /-- Remaining discards for a required multi-card discard such as “discard
  two cards”. Unlike `thirstDiscardsLeft`, an artifact does not end this
  early. -/
  pendingDiscardsLeft : Nat := 0
  /-- Ward payments still to announce after the current one (CR 702.21). -/
  wardQueue : Array WardObligation := #[]
deriving Repr, Inhabited

namespace Game

def logMsg (g : Game) (msg : String) : Game :=
  { g with log := g.log.push msg }

def over (g : Game) : Bool := g.result.isSome

def player (g : Game) (p : PlayerId) : Player :=
  g.players[p.idx]!

def setPlayer (g : Game) (pl : Player) : Game :=
  { g with players := g.players.set! pl.id.idx pl }

def modifyPlayer (g : Game) (p : PlayerId) (f : Player → Player) : Game :=
  g.setPlayer (f (g.player p))

/-- Set `p`'s life total and log `msg`. -/
def setLife (g : Game) (p : PlayerId) (life : Int) (msg : String) : Game :=
  if (g.player p).lifeLocked && life != (g.player p).life then
    g.logMsg s!"{(g.player p).name}'s life total can't change"
  else
    g.setPlayer { (g.player p) with life := life } |>.logMsg msg

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
      copyRestore := none
      copyUntilEot := false
      copyUntilNextTurn := false
      copyUntilSourceLeaves := none }
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
    { g with playerControl := some (you, them), controlOnNextTakenTurn := false }
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

end Game
end Mtg.Engine
