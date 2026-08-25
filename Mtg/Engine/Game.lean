import Mtg.Engine.Card
import Mtg.Engine.Deck
import Mtg.Engine.Mana
import Mtg.Engine.Rng
import Mtg.Engine.Rules
import Mtg.Engine.Turn
import Mtg.Engine.Zone

/-!
# Game state and rules engine

Encodes starting a game (CR 103), including the London mulligan (CR 103.5),
ending a game (CR 104), priority (CR 117), playing lands (CR 116.2a / 305),
casting the spells we model (CR 601), including choosing modes (CR 601.2b),
announcing targets (CR 601.2c), and activating mana abilities while paying
(CR 601.2g), activating non-mana abilities of permanents (CR 602), including
modal abilities (CR 700.2) and destroying permanents (CR 701.7), static
abilities that grant trample or pump an enchanted creature (CR 604), Aura
spells (CR 303.4), flash (CR 702.8), scry (CR 701.20),
attack triggers (CR 508.2 / 603), becomes-blocked triggers (CR 509.5c / 603),
enters triggers (CR 603.6a), combat (CR 506–510, including CR 510.1c), cleanup
(CR 514.3), and the state-based actions we implement (CR 704.5).
-/

namespace Mtg.Engine

/-- A target chosen while casting a spell (CR 115). -/
inductive Target where
  | player (id : PlayerId)
  | permanent (id : ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Permanent status (CR 110.5). Extra fields track combat and EOT pumps. -/
structure Status where
  tapped : Bool := false
  damage : Int := 0
  summoningSick : Bool := true
  pumpPower : Int := 0
  pumpToughness : Int := 0
  attacking : Bool := false
  blocking : Option ObjectId := none
  /-- Set when this attacker becomes blocked (CR 509.1h). Remains true even if
  every blocking creature leaves combat. -/
  blocked : Bool := false
  /-- Non-mana activations this turn, for “only once each turn”. -/
  activationsThisTurn : Nat := 0
deriving Repr, Inhabited, BEq

/-- Permission to play a card from exile (CR 701.14), e.g. Snowslope Hunter. -/
structure PlayPermission where
  /-- The player who may play the card. -/
  player : PlayerId
  /-- Remaining endings of `player`'s turns before the permission expires.
  Granted as 2 during that player's turn so it lasts until the end of their
  next turn. -/
  turnEndsRemaining : Nat
deriving Repr, Inhabited, BEq

/-- An object currently in the game (CR 109). -/
structure GameObject where
  id : ObjectId
  printed : CardDef
  owner : PlayerId
  controller : Option PlayerId := none
  zone : Zone
  status : Status := {}
  timestamp : Nat := 0
  /-- Present when this object is an activated ability on the stack (CR 602.2a). -/
  abilityEffect : Option AbilityEffect := none
  /-- Present when this object is a triggered ability on the stack (CR 603.3). -/
  triggeredAbility : Option TriggeredAbility := none
  /-- Source of an activated or triggered ability on the stack (CR 113.7). -/
  sourceId : Option ObjectId := none
  /-- Set while this card may be played from exile. -/
  playPermission : Option PlayPermission := none
  /-- Object this Aura is attached to (CR 303.4). -/
  attachedTo : Option ObjectId := none
deriving Repr, Inhabited

namespace GameObject

def name (o : GameObject) : String := o.printed.name

def power (o : GameObject) : Int :=
  (o.printed.power.getD 0) + o.status.pumpPower

def toughness (o : GameObject) : Int :=
  (o.printed.toughness.getD 0) + o.status.pumpToughness

def isOnBattlefield (o : GameObject) : Bool := o.zone == .battlefield

def controlledBy (o : GameObject) (p : PlayerId) : Bool :=
  o.controller == some p

def hasSubtype (o : GameObject) (s : String) : Bool :=
  o.printed.subtypes.any (· == s)

/-- Colorless nonland permanent (e.g. a legal Goblin Cratermaker destroy target). -/
def isColorlessNonland (o : GameObject) : Bool :=
  o.isOnBattlefield && !o.printed.isLand && o.printed.colors.isColorless

/-- Whether `{T}` in an activation cost is currently payable (CR 302.6). -/
def canPayTapCost (o : GameObject) : Bool :=
  !o.status.tapped &&
  !(o.printed.isCreature && o.status.summoningSick && !o.printed.keywords.haste)

end GameObject

/-- A spell or ability on the stack (CR 405). Last array element is the top. -/
structure StackEntry where
  objectId : ObjectId
  controller : PlayerId
  targets : Array Target
deriving Repr, Inhabited

/-- Whether a proposed payment is for a spell (CR 601) or an activated ability (CR 602). -/
inductive ProposalKind where
  | spell
  | activatedAbility
deriving DecidableEq, Repr, Inhabited, BEq

/-- Snapshot of a spell or activated ability whose total cost is being paid
(CR 601.2f–h / 602.2b). Used to reverse an illegal action (CR 733.1). -/
structure ProposedSpell where
  caster : PlayerId
  cost : ManaCost
  spellId : ObjectId
  original : GameObject
  handBefore : Array ObjectId
  stackBefore : Array StackEntry
  manaBefore : ManaPool
  tapped : Array ObjectId := #[]
  kind : ProposalKind := .spell
  /-- Source permanent of an activated ability; unused for spells. -/
  sourceId : Option ObjectId := none
  tapSource : Bool := false
  sacrificeSource : Bool := false
  /-- After mana is paid, the player must sacrifice another creature or artifact. -/
  needsSacrificeOther : Bool := false
  /-- Modes of a modal activated ability, announced at CR 601.2b. -/
  abilityModes : Array AbilityEffect := #[]
deriving Repr, Inhabited

/-- Choice that must be made before priority proceeds. -/
inductive Pending where
  | none
  | declareAttackers
  | declareBlockers
  /-- The player may activate mana abilities before paying (CR 601.2g). -/
  | activateManaAbilities (caster : PlayerId)
  /-- The player must announce targets for the proposed spell (CR 601.2c). -/
  | chooseTargets (caster : PlayerId)
  /-- The player must choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (caster : PlayerId)
  /-- After `pay`, choose another creature or artifact to sacrifice. -/
  | sacrificePermanent (player : PlayerId) (sourceId : ObjectId)
  /-- This player declares whether they will take a mulligan (CR 103.5). -/
  | declareMulligan (player : PlayerId)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- This player is looking at the top `count` cards of their library (CR 701.20). -/
  | scry (player : PlayerId) (count : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

inductive GameResult where
  | won (player : PlayerId)
  | draw
deriving DecidableEq, Repr, BEq

structure Player where
  id : PlayerId
  name : String
  life : Int := 20
  startingLife : Int := 20
  maxHandSize : Nat := 7
  /-- Cards drawn as the game begins (CR 103.5); normally seven. -/
  startingHandSize : Nat := 7
  manaPool : ManaPool := {}
  landsPlayedThisTurn : Nat := 0
  poison : Nat := 0
  lost : Bool := false
  drewFromEmpty : Bool := false
  /-- Completed London mulligans this game (CR 103.5). -/
  mulligansTaken : Nat := 0
  /-- Set once this player declines further mulligans (CR 103.5). -/
  keptOpeningHand : Bool := false
  library : Array ObjectId := #[]
  hand : Array ObjectId := #[]
  graveyard : Array ObjectId := #[]
deriving Repr, Inhabited

/-- A seat at the table before objects are created. -/
structure Seat where
  name : String
  deck : Array CardDef
deriving Repr, Inhabited

structure StartConfig where
  seats : Array Seat
  format : Format := .constructed
  seed : UInt64 := 20260807
  /-- Index into `seats`. `none` means the RNG chooses. -/
  startingPlayer : Option Nat := none

inductive Action where
  | pass
  | playLand (id : ObjectId)
  | tapForMana (id : ObjectId) (mana : ManaType)
  | cast (id : ObjectId)
  /-- Announce a target for the proposed spell (CR 601.2c). -/
  | target (t : Target)
  /-- Choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (idx : Nat)
  /-- Activate a non-mana activated ability of a permanent (CR 602). -/
  | activate (id : ObjectId) (abilityIdx : Nat)
  /-- Pay the locked-in cost of a proposed spell or ability (CR 601.2h / 602.2b). -/
  | pay
  /-- After `pay`, sacrifice another creature or artifact to finish activating. -/
  | sacrifice (id : ObjectId)
  | declareAttackers (ids : Array ObjectId)
  | declareBlockers (assignments : Array (ObjectId × ObjectId))
  /-- Keep this hand as the opening hand (CR 103.5). -/
  | keep
  /-- Declare a London mulligan; it is taken after every remaining player has
  declared (CR 103.5). -/
  | takeMulligan
  /-- Put these cards on the bottom after a mulligan, first listed = new bottom. -/
  | putOnBottom (ids : Array ObjectId)
  /-- Finish scrying: `top` (last = new top) go on top of the library in that
  order; `bottom` (first = new bottom) go to the bottom (CR 701.20). -/
  | scry (top : Array ObjectId) (bottom : Array ObjectId)
  | concede
deriving Repr

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
  result : Option GameResult := none
  log : Array String := #[]
  format : Format := .constructed
  consecutivePasses : Nat := 0
  /-- Set when CR 514.3a grants priority during the current cleanup step. -/
  cleanupGivesPriority : Bool := false
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

def livingPlayers (g : Game) : Array Player :=
  g.players.filter (fun pl => !pl.lost)

def opponent (g : Game) (p : PlayerId) : PlayerId :=
  let living := g.livingPlayers
  if living.size == 2 then
    if living[0]!.id == p then living[1]!.id else living[0]!.id
  else
    PlayerId.mk ((p.idx + 1) % g.players.size)

def nextLiving (g : Game) (p : PlayerId) : PlayerId :=
  let n := g.players.size
  Id.run do
    for k in [1:n+1] do
      let q : PlayerId := ⟨(p.idx + k) % n⟩
      if !(g.player q).lost then
        return q
    return p

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

def allocId (g : Game) : Game × ObjectId :=
  ({ g with nextObjectId := g.nextObjectId + 1 }, ⟨g.nextObjectId⟩)

def bumpTime (g : Game) : Game × Nat :=
  ({ g with timestamp := g.timestamp + 1 }, g.timestamp)

/-- Remove an id from a zone list. -/
def stripId (ids : Array ObjectId) (id : ObjectId) : Array ObjectId :=
  ids.filter (fun x => x != id)

def removeFromZoneList (g : Game) (id : ObjectId) (z : Zone) : Game :=
  match z with
  | .library p => g.modifyPlayer p (fun pl => { pl with library := stripId pl.library id })
  | .hand p => g.modifyPlayer p (fun pl => { pl with hand := stripId pl.hand id })
  | .graveyard p => g.modifyPlayer p (fun pl => { pl with graveyard := stripId pl.graveyard id })
  | .stack => { g with stack := g.stack.filter (fun e => e.objectId != id) }
  | _ => g

/-- Move an object to a new zone, assigning a new object identity (CR 400.7).
Auras attached to a permanent that leaves the battlefield become unattached
and remain on the battlefield (CR 400.7d). -/
def unattachFrom (g : Game) (hostId : ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.attachedTo == some hostId then
        g := g.setObject { o with attachedTo := none }
        g := g.logMsg s!"{o.name} becomes unattached"
    return g

def move (g : Game) (id : ObjectId) (dest : Zone) (controller : Option PlayerId := none) :
    Game × ObjectId :=
  let old := g.object! id
  let g :=
    if old.zone == .battlefield then g.unattachFrom id else g
  let g := g.removeFromZoneList id old.zone
  let (g, newId) := g.allocId
  let (g, ts) := g.bumpTime
  let fresh : GameObject := {
    id := newId
    printed := old.printed
    owner := old.owner
    controller := controller
    zone := dest
    status := {}
    timestamp := ts
  }
  let g := { g with objects := g.objects.filter (fun o => o.id != id) |>.push fresh }
  let g :=
    match dest with
    | .library p => g.modifyPlayer p (fun pl => { pl with library := pl.library.push newId })
    | .hand p => g.modifyPlayer p (fun pl => { pl with hand := pl.hand.push newId })
    | .graveyard p => g.modifyPlayer p (fun pl => { pl with graveyard := pl.graveyard.push newId })
    | _ => g
  (g, newId)

def emptyManaPools (g : Game) : Game :=
  Id.run do
    let mut g := g
    for pl in g.players do
      if !pl.manaPool.isEmpty then
        g := g.logMsg s!"{pl.name} empties mana pool ({pl.manaPool})"
        g := g.setPlayer { pl with manaPool := ManaPool.empty }
    return g

/-- Draw `n` cards for `p` (CR 121). -/
def draw (g : Game) (p : PlayerId) (n : Nat := 1) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let pl := g.player p
      if pl.library.isEmpty then
        g := g.setPlayer { pl with drewFromEmpty := true }
        g := g.logMsg s!"{pl.name} tries to draw from an empty library"
        return g
      else
        let top := pl.library.back!
        let cardName := (g.object! top).name
        let rest := pl.library.pop
        g := g.setPlayer { pl with library := rest }
        let (g', _) := g.move top (.hand p) none
        g := g'.logMsg s!"{pl.name} draws {cardName}"
    return g

def shuffleLibrary (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  let (rng, lib) := g.rng.shuffle pl.library
  { g with rng := rng } |>.setPlayer { pl with library := lib }
   |>.logMsg s!"{pl.name} shuffles their library"

def canAttack (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.printed.isCreature &&
  o.controlledBy g.activePlayer &&
  !o.status.tapped && !o.printed.keywords.defender &&
  (!o.status.summoningSick || o.printed.keywords.haste)

def canBlock (g : Game) (blocker attacker : GameObject) : Bool :=
  let defender := g.opponent g.activePlayer
  blocker.isOnBattlefield && blocker.printed.isCreature &&
  blocker.controlledBy defender && !blocker.status.tapped &&
  attacker.status.attacking &&
  (!attacker.printed.keywords.flying ||
    blocker.printed.keywords.flying || blocker.printed.keywords.reach)

/-- Whether `src` currently grants trample to `target` (CR 604.2). -/
def grantsTrampleTo (src target : GameObject) : Bool :=
  src.id != target.id &&
  src.isOnBattlefield &&
  target.isOnBattlefield &&
  src.controller == target.controller &&
  src.controller.isSome &&
  target.printed.isCreature &&
  src.printed.staticAbilities.any (fun ab =>
    match ab with
    | .otherCreaturesHaveTrample subtypes =>
      subtypes.any target.hasSubtype
    | .enchantedCreatureGets _ _ => false)

/-- Whether `o` has trample, printed or granted (CR 702.19, 604.2). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  o.printed.keywords.trample ||
  (o.isOnBattlefield && g.battlefield.any (fun src => grantsTrampleTo src o))

/-- Keywords including those granted by static abilities. -/
def effectiveKeywords (g : Game) (o : GameObject) : Keywords :=
  { o.printed.keywords with trample := g.hasTrample o }

/-- Continuous +P/+T this Aura currently grants its host (CR 613.3c). -/
def auraStatBonus (aura : GameObject) : Int × Int :=
  aura.printed.staticAbilities.foldl
    (fun acc ab =>
      match ab with
      | .enchantedCreatureGets p t => (acc.1 + p, acc.2 + t)
      | .otherCreaturesHaveTrample _ => acc)
    (0, 0)

/-- Static power/toughness from Auras attached to `o`. -/
def attachedStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    g.battlefield.foldl
      (fun acc aura =>
        if aura.attachedTo == some o.id then
          let b := auraStatBonus aura
          (acc.1 + b.1, acc.2 + b.2)
        else acc)
      (0, 0)

/-- Current power, including until-end-of-turn pumps and Aura bonuses (CR 208.2). -/
def power (g : Game) (o : GameObject) : Int :=
  o.power + (g.attachedStatBonus o).1

/-- Current toughness, including until-end-of-turn pumps and Aura bonuses (CR 208.2). -/
def toughness (g : Game) (o : GameObject) : Int :=
  o.toughness + (g.attachedStatBonus o).2

/-- Greatest power among creatures `p` controls; `0` if they control none. -/
def greatestPowerAmongCreatures (g : Game) (p : PlayerId) : Int :=
  let creatures := g.permanentsOf p |>.filter (·.printed.isCreature)
  if creatures.isEmpty then 0
  else creatures.foldl (fun acc o => max acc (g.power o)) (g.power creatures[0]!)

/-- Creatures currently blocking `attackerId`. -/
def blockersOf (g : Game) (attackerId : ObjectId) : Array GameObject :=
  g.battlefield.filter (fun b => b.status.blocking == some attackerId)

/-- Perform applicable state-based actions (CR 704.3). The `Bool` is `true` if
any state-based action was performed (used by CR 514.3a). -/
partial def checkSBACounted (g : Game) : Game × Bool :=
  if g.over then (g, false)
  else
    Id.run do
      let mut g := g
      let mut changed := false
      -- Players losing (CR 704.5a–c).
      for pl in g.players do
        if !pl.lost then
          if pl.life ≤ 0 then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (life total {pl.life})"
            changed := true
          else if pl.drewFromEmpty then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (drew from empty library)"
            changed := true
          else if pl.poison ≥ 10 then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (poison)"
            changed := true
      -- Creatures with 0 toughness or lethal damage (CR 704.5f–g).
      for o in g.battlefield do
        if o.printed.isCreature then
          let t := g.toughness o
          if t ≤ 0 then
            g := g.logMsg s!"{o.name} dies (toughness {t})"
            let (g', _) := g.move o.id (.graveyard o.owner) none
            g := g'
            changed := true
          else if o.status.damage ≥ t then
            g := g.logMsg s!"{o.name} dies from lethal damage"
            let (g', _) := g.move o.id (.graveyard o.owner) none
            g := g'
            changed := true
          else if o.printed.keywords.deathtouch && o.status.damage > 0 then
            -- Simplified: any damage from a deathtouch source is tracked as
            -- ordinary damage; full 704.5h tracking is future work.
            pure ()
      -- Unattached or illegally attached Auras (CR 704.5n).
      for o in g.battlefield do
        if o.printed.isAura then
          let legal :=
            match o.attachedTo.bind g.findObject? with
            | some host => host.isOnBattlefield && host.printed.isCreature
            | none => false
          if !legal then
            g := g.logMsg s!"{o.name} is put into its owner's graveyard (CR 704.5n)"
            let (g', _) := g.move o.id (.graveyard o.owner) none
            g := g'
            changed := true
      let living := g.livingPlayers
      if living.size == 0 then
        g := { g with result := some .draw }
        g := g.logMsg "The game is a draw"
        return (g, true)
      else if living.size == 1 then
        let w := living[0]!
        g := { g with result := some (.won w.id) }
        g := g.logMsg s!"{w.name} wins the game"
        return (g, true)
      if changed then
        let (g', _) := checkSBACounted g
        return (g', true)
      return (g, false)

def checkSBA (g : Game) : Game :=
  (g.checkSBACounted).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3, 514.3a).
Attack, becomes-blocked, and enters triggers are put on the stack as their
events happen (CR 508.2, 509.5c, 603.6a). -/
def hasWaitingTriggers (_g : Game) : Bool :=
  false

/-- CR 103.8a: in a two-player game the starting player skips the draw step
of their first turn. -/
def skipsFirstDraw (g : Game) : Bool :=
  g.isFirstTurn && g.players.size == 2 && g.activePlayer == g.startingPlayer

/-- Whether a player currently receives priority (CR 117.3a, 502.4, 514.3,
103.8a / 500.11). A skipped draw step grants none. -/
def playersReceivePriority (g : Game) : Bool :=
  if g.step == .cleanup then g.cleanupGivesPriority
  else if g.step == .draw && g.skipsFirstDraw then false
  else g.step.playersReceivePriority

def receivePriority (g : Game) (p : PlayerId) : Game :=
  let g := g.checkSBA
  if g.over then g
  else { g with priority := p, consecutivePasses := 0 }

def asSorcery? (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.stack.isEmpty &&
  g.step.isMainPhase && g.activePlayer == p && g.priority == p

def hasPriority (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.priority == p && g.playersReceivePriority

/-- Lands remaining this turn (CR 305.3 / 116.2a). -/
def canPlayLand (g : Game) (p : PlayerId) : Bool :=
  g.asSorcery? p && (g.player p).landsPlayedThisTurn == 0

/-- Whether `p` may play `o` from exile under a granted permission (CR 701.14). -/
def mayPlayFromExile (_g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
  match o.playPermission with
  | some perm => perm.player == p && perm.turnEndsRemaining > 0
  | none => false

/-- Cards in exile that `p` currently may play. -/
def exiledPlayable (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => g.mayPlayFromExile p o)

/-- Whether `p` may play `o` from hand or from exile under a permission. -/
def mayPlay (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  (g.player p).hand.contains o.id || g.mayPlayFromExile p o

def playZoneError (g : Game) (p : PlayerId) (o : GameObject) : String :=
  if o.zone == .exile && !g.mayPlayFromExile p o then
    "You may not play that card from exile"
  else
    "That card is not in your hand"

def playLand (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.canPlayLand p then
    throw "Can't play a land now (CR 116.2a / 305.3)"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if !card.printed.isLand then
    throw s!"{card.name} is not a land"
  let (g, newId) := g.move id .battlefield (some p)
  let g := g.modifyPlayer p (fun pl => { pl with landsPlayedThisTurn := pl.landsPlayedThisTurn + 1 })
  let g := g.logMsg s!"{(g.player p).name} plays {card.name}"
  -- Permanents enter untapped (CR 110.5b); lands have no summoning sickness.
  let o := g.object! newId
  let g := g.setObject { o with status := { o.status with summoningSick := false } }
  return g.receivePriority p

def manaSources (g : Game) (p : PlayerId) : Array (GameObject × Array ManaType) :=
  g.permanentsOf p |>.filterMap (fun o =>
    let types := o.printed.manaAbilities
    if types.isEmpty || o.status.tapped then none
    else if o.printed.isCreature && o.status.summoningSick && !o.printed.keywords.haste then none
    else some (o, types))

/-- A player may activate mana abilities with priority, or while paying a
spell they are casting (CR 605.3a / 601.2g). -/
def canActivateManaAbility (g : Game) (p : PlayerId) : Bool :=
  if g.over then false
  else if g.hasPriority p then true
  else
    match g.pending with
    | .activateManaAbilities caster => caster == p
    | _ => false

def tapForMana (g : Game) (p : PlayerId) (id : ObjectId) (mana : ManaType) : Except String Game := do
  if !g.canActivateManaAbility p then
    throw "You can't activate a mana ability now (CR 605.3a)"
  let o := g.object! id
  if !o.controlledBy p || !o.isOnBattlefield then
    throw "You don't control that permanent"
  if o.status.tapped then
    throw s!"{o.name} is already tapped"
  if o.printed.isCreature && o.status.summoningSick && !o.printed.keywords.haste then
    throw s!"{o.name} has summoning sickness (CR 302.6)"
  if !o.printed.manaAbilities.contains mana then
    throw s!"{o.name} cannot produce {mana}"
  let g := g.setObject { o with status := { o.status with tapped := true } }
  let g := g.modifyPlayer p (fun pl => { pl with manaPool := pl.manaPool.add mana })
  let g := g.logMsg s!"{g.player p |>.name} taps {o.name} for {mana}"
  let g :=
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some { prop with tapped := prop.tapped.push id } }
    | none => g
  -- Mana abilities don't use the stack (CR 605.3b).
  return { g with consecutivePasses := 0 }

/-- Mana in `p`'s pool plus one mana from each of their untapped sources. -/
def availableMana (g : Game) (p : PlayerId) : ManaPool :=
  (g.manaSources p).foldl
    (fun pool (_, types) =>
      match types[0]? with
      | some t => pool.add t
      | none => pool)
    (g.player p).manaPool

def legalTargets (g : Game) (_caster : PlayerId) (effect : SpellEffect) : Array Target :=
  match effect with
  | .dealDamage _ =>
    let players := g.livingPlayers.map (fun pl => Target.player pl.id)
    let creatures := g.battlefield.filter (·.printed.isCreature) |>.map (fun o => Target.permanent o.id)
    players ++ creatures
  | .pump _ _ =>
    g.battlefield.filter (·.printed.isCreature) |>.map (fun o => Target.permanent o.id)

/-- Legal targets for an Aura spell with “Enchant creature” (CR 303.4). -/
def legalAuraTargets (g : Game) : Array Target :=
  g.battlefield.filter (·.printed.isCreature) |>.map (fun o => Target.permanent o.id)

/-- Legal targets for beginning to cast `o` (CR 115.1, 303.4, 601.2c). -/
def legalSpellTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  match o.printed.spellEffect with
  | some e => g.legalTargets p e
  | none => if o.printed.isAura then g.legalAuraTargets else #[]

/-- Legal targets for an activated-ability effect (CR 115.1 / 601.2c). -/
def legalAbilityTargets (g : Game) (_p : PlayerId) : AbilityEffect → Array Target
  | .dealDamageToTargetCreature _ =>
    g.battlefield.filter (·.printed.isCreature) |>.map (fun o => Target.permanent o.id)
  | .destroyTargetColorlessNonland =>
    g.battlefield.filter (·.isColorlessNonland) |>.map (fun o => Target.permanent o.id)
  | .searchBasicLandTapped | .exileTopPlayUntilEndOfNextTurn => #[]

/-- Legal targets for the object currently being announced (spell or ability). -/
def legalProposedTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  match o.abilityEffect with
  | some e => g.legalAbilityTargets p e
  | none => g.legalSpellTargets p o

/-- Whether `e` currently has a legal target, or does not require one. -/
def modeIsChoosable (g : Game) (p : PlayerId) (e : AbilityEffect) : Bool :=
  !e.requiresTarget || !(g.legalAbilityTargets p e).isEmpty

/-- Default object or player to announce as a target (CR 601.2c). Damage spells
prefer the opponent; creature damage prefers an opposing creature; destroy
prefers an opposing colorless nonland; pumps and Auras prefer a creature the
caster controls. -/
def defaultTarget (g : Game) (p : PlayerId) (obj : GameObject) : Option Target :=
  let legal := g.legalProposedTargets p obj
  let preferred : Option Target :=
    match obj.abilityEffect, obj.printed.spellEffect with
    | some (.dealDamageToTargetCreature _), _ =>
      (g.permanentsOf (g.opponent p)).filter (·.printed.isCreature) |>.back?
        |>.map (fun c => Target.permanent c.id)
    | some .destroyTargetColorlessNonland, _ =>
      (g.permanentsOf (g.opponent p)).filter (·.isColorlessNonland) |>.back?
        |>.map (fun c => Target.permanent c.id)
    | _, some (.dealDamage _) => some (Target.player (g.opponent p))
    | _, some (.pump _ _) | _, none =>
      (g.permanentsOf p).filter (·.printed.isCreature) |>.back?
        |>.map (fun c => Target.permanent c.id)
  match preferred with
  | some t => if legal.contains t then some t else legal[0]?
  | none => legal[0]?

/-- Default mode index for a modal activated ability (CR 601.2b). Prefers
dealing damage to an opposing creature, then destroying a colorless nonland. -/
def defaultAbilityMode (g : Game) (p : PlayerId) (modes : Array AbilityEffect) : Option Nat :=
  let choosable : Array (Nat × AbilityEffect) :=
    Id.run do
      let mut acc : Array (Nat × AbilityEffect) := #[]
      for i in [0:modes.size] do
        let e := modes[i]!
        if g.modeIsChoosable p e then
          acc := acc.push (i, e)
      return acc
  let findKind (pred : AbilityEffect → Bool) : Option Nat :=
    (choosable.find? (fun (_, e) => pred e)).map (·.1)
  let damageIdx :=
    findKind (fun e => match e with | .dealDamageToTargetCreature _ => true | _ => false)
  let destroyIdx :=
    findKind (fun e => match e with | .destroyTargetColorlessNonland => true | _ => false)
  let oppHasCreature :=
    (g.permanentsOf (g.opponent p)).any (·.printed.isCreature)
  let hasColorless := g.battlefield.any (·.isColorlessNonland)
  if oppHasCreature then
    damageIdx <|> destroyIdx <|> choosable[0]?.map (·.1)
  else if hasColorless then
    destroyIdx <|> damageIdx <|> choosable[0]?.map (·.1)
  else
    choosable[0]?.map (·.1)

def targetLogName (g : Game) : Target → String
  | .player pid => (g.player pid).name
  | .permanent oid =>
    match g.findObject? oid with
    | some o => o.name
    | none => toString oid

/-- Whether `p` may begin to cast `o` (CR 601.3). Having enough mana in the
pool is not required; mana abilities are activated at CR 601.2g. -/
def canCast (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  !o.printed.isLand &&
  g.mayPlay p o &&
  g.hasPriority p &&
  (if o.printed.hasSorcerySpeed then g.asSorcery? p else true) &&
  if o.printed.requiresTarget then !(g.legalSpellTargets p o |>.isEmpty)
  else o.printed.isPermanentCard

def payCost (g : Game) (p : PlayerId) (cost : ManaCost) : Except String Game := do
  let pl := g.player p
  match pl.manaPool.pay? cost with
  | none => throw s!"{pl.name} cannot pay {cost}"
  | some pool =>
    return g.setPlayer { pl with manaPool := pool }

/-- Undo a proposed spell or ability that could not be paid (CR 601.2 / 602.2 / 733.1). -/
def reverseProposedSpell (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    Id.run do
      let mut g := g
      let name := (g.player prop.caster).name
      let objects := g.objects.filter (fun o => o.id != prop.spellId)
      let objects :=
        match prop.kind with
        | .spell => objects.push prop.original
        | .activatedAbility => objects
      g := { g with
        objects := objects
        stack := prop.stackBefore
        pending := .none
        proposedSpell := none }
      g := g.modifyPlayer prop.caster (fun pl =>
        { pl with hand := prop.handBefore, manaPool := prop.manaBefore })
      for id in prop.tapped do
        if let some o := g.findObject? id then
          g := g.setObject { o with status := { o.status with tapped := false } }
      let reversed :=
        match prop.kind with
        | .spell => "the casting is reversed (CR 601.2 / 733.1)"
        | .activatedAbility => "the activation is reversed (CR 602.2 / 733.1)"
      g := g.logMsg s!"{name} cannot pay {prop.cost}; {reversed}"
      -- The player who had priority retains it (CR 733.2).
      return { g with priority := prop.caster, consecutivePasses := 0 }

def becomeCast (g : Game) (p : PlayerId) (cardName : String) : Game :=
  g.logMsg s!"{(g.player p).name} casts {cardName}" |>.receivePriority p

/-- Continue after CR 601.2c: activate mana abilities (601.2g) or finish casting. -/
def afterTargetsChosen (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    if prop.cost.includesManaPayment then
      { g with pending := .activateManaAbilities prop.caster }
        |>.logMsg s!"{(g.player prop.caster).name} may activate mana abilities (CR 601.2g)"
    else
      let name := (g.object! prop.spellId).name
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      g.becomeCast prop.caster name

/-- Write `targets` onto the stack entry for the proposed spell. -/
def setProposedTargets (g : Game) (targets : Array Target) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    match g.stack.findIdx? (fun e => e.objectId == prop.spellId) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with targets := targets } }

def becomeActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId := none) : Game :=
  let g :=
    match sourceId with
    | none => g
    | some sid =>
      match g.findObject? sid with
      | some src =>
        g.setObject { src with status := { src.status with
          activationsThisTurn := src.status.activationsThisTurn + 1 } }
      | none => g
  g.logMsg s!"{(g.player p).name} activates {sourceName}" |>.receivePriority p

/-- Permanents `p` may sacrifice to pay “sacrifice another creature or artifact”. -/
def sacrificeCreatureOrArtifactChoices (g : Game) (p : PlayerId) (sourceId : ObjectId) :
    Array GameObject :=
  g.permanentsOf p |>.filter (fun o =>
    o.id != sourceId && (o.printed.isCreature || o.printed.isArtifact))

/-- Whether `sac` is a legal “another creature or artifact” sacrifice for `sourceId`. -/
def canSacrificeAsCreatureOrArtifact (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (sac : GameObject) : Bool :=
  (g.sacrificeCreatureOrArtifactChoices p sourceId).any (·.id == sac.id)

/-- Whether the source of a proposed activated ability can still pay tap/sacrifice. -/
def sourceStillPayable (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.sourceId with
  | none => true
  | some sid =>
    match g.findObject? sid with
    | none => false
    | some src =>
      src.isOnBattlefield && src.controlledBy prop.caster &&
      (!prop.tapSource || !src.status.tapped)

/-- Pay `{T}` and/or sacrifice the source as part of an activation cost (CR 601.2h). -/
def payActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (tapSource sacrificeSource : Bool) : Except String Game := do
  let some src := g.findObject? sourceId | throw "The source is no longer in play"
  if !src.isOnBattlefield then
    throw "The source is no longer on the battlefield"
  if !src.controlledBy p then
    throw "You don't control that permanent"
  let mut g := g
  if tapSource then
    let src := g.object! sourceId
    if src.status.tapped then
      throw s!"{src.name} is already tapped"
    g := g.setObject { src with status := { src.status with tapped := true } }
  if sacrificeSource then
    let src := g.object! sourceId
    g := g.logMsg s!"{(g.player p).name} sacrifices {src.name}"
    let (g', _) := g.move sourceId (.graveyard src.owner) none
    g := g'
  return g

/-- Pay the locked-in cost (CR 601.2h / 602.2b). Abilities that still need
another creature or artifact sacrificed wait for the `sacrifice` action. -/
def finishProposedSpell (g : Game) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell or ability is waiting to be paid for"
  if !(g.player prop.caster).manaPool.canPay prop.cost || !g.sourceStillPayable prop then
    return g.reverseProposedSpell
  if prop.needsSacrificeOther then
    match prop.sourceId with
    | none => return g.reverseProposedSpell
    | some sid =>
      if (g.sacrificeCreatureOrArtifactChoices prop.caster sid).isEmpty then
        return g.reverseProposedSpell
  let g ← g.payCost prop.caster prop.cost
  let g ←
    match prop.sourceId with
    | some sid =>
      g.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
    | none => pure g
  match prop.kind, prop.needsSacrificeOther, prop.sourceId with
  | .spell, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeCast prop.caster (g.object! prop.spellId).name
  | .activatedAbility, true, some sid =>
    let g := { g with
      pending := .sacrificePermanent prop.caster sid
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice another creature or artifact"
  | .activatedAbility, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeActivated prop.caster prop.original.name prop.sourceId

def castSpell (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  let pl := g.player p
  if card.printed.isLand then
    throw "Lands are played, not cast (CR 305)"
  if card.printed.hasSorcerySpeed && !g.asSorcery? p then
    throw s!"{card.name} has sorcery speed"
  if card.printed.requiresTarget && (g.legalSpellTargets p card).isEmpty then
    throw s!"{card.name} requires a target"
  -- CR 601.2a: propose the spell by moving it onto the stack. Targets are
  -- announced at CR 601.2c; mana is not required yet (CR 601.2g).
  let cost := card.printed.manaCost
  let original := card
  let handBefore := pl.hand
  let stackBefore := g.stack
  let manaBefore := pl.manaPool
  let (g, newId) := g.move id .stack (some p)
  let entry : StackEntry := { objectId := newId, controller := p, targets := #[] }
  let g := { g with stack := g.stack.push entry, consecutivePasses := 0 }
  let needsTarget := original.printed.requiresTarget
  if !needsTarget && !cost.includesManaPayment then
    return g.becomeCast p original.name
  let prop : ProposedSpell := {
    caster := p
    cost := cost
    spellId := newId
    original := original
    handBefore := handBefore
    stackBefore := stackBefore
    manaBefore := manaBefore
  }
  let g := g.logMsg s!"{pl.name} begins casting {original.name}"
  if needsTarget then
    let g := { g with pending := .chooseTargets p, proposedSpell := some prop }
    return g.logMsg s!"{pl.name} must choose a target (CR 601.2c)"
  let g := { g with pending := .activateManaAbilities p, proposedSpell := some prop }
  return g.logMsg s!"{pl.name} may activate mana abilities (CR 601.2g)"

/-- Announce the chosen target for the proposed spell (CR 601.2c). -/
def announceTarget (g : Game) (p : PlayerId) (t : Target) : Except String Game := do
  match g.pending with
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some prop := g.proposedSpell | throw "No spell is waiting for a target (CR 601.2c)"
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    if !(g.legalProposedTargets p spell).contains t then
      throw "Illegal target (CR 601.2c)"
    let g := g.setProposedTargets #[t]
    let g := g.logMsg
      s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
    return g.afterTargetsChosen
  | _ => throw "Not time to choose targets (CR 601.2c)"

/-- Announce the chosen mode for a modal activated ability (CR 601.2b / 700.2). -/
def announceMode (g : Game) (p : PlayerId) (idx : Nat) : Except String Game := do
  match g.pending with
  | .chooseMode caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a mode (CR 601.2b)"
    let some prop := g.proposedSpell | throw "No ability is waiting for a mode (CR 601.2b)"
    let some chosen := prop.abilityModes[idx]?
      | throw "No such mode (CR 601.2b)"
    if !g.modeIsChoosable p chosen then
      throw "That mode requires a target (CR 700.2d)"
    let some obj := g.findObject? prop.spellId | throw "The ability left the stack"
    let g := g.setObject { obj with abilityEffect := some chosen }
    let g := g.logMsg
      s!"{(g.player p).name} chooses a mode: {chosen.toNotation} (CR 601.2b)"
    if chosen.requiresTarget then
      let g := { g with pending := .chooseTargets p }
      return g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
    return g.afterTargetsChosen
  | _ => throw "Not time to choose a mode (CR 601.2b)"

/-- Whether `p` may begin activating `ab` of permanent `o` (CR 602.3). Having
enough mana in the pool is not required; mana abilities are activated at
CR 601.2g. -/
def canActivate (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) : Bool :=
  o.isOnBattlefield &&
  o.controlledBy p &&
  g.hasPriority p &&
  (if ab.onlyAsSorcery then g.asSorcery? p else true) &&
  (if ab.onlyDuringYourTurn then g.activePlayer == p else true) &&
  (if ab.onceEachTurn then o.status.activationsThisTurn == 0 else true) &&
  (if ab.cost.tap then o.canPayTapCost else true) &&
  (if ab.cost.sacrificeAnotherCreatureOrArtifact then
    !(g.sacrificeCreatureOrArtifactChoices p o.id).isEmpty
   else true) &&
  (ab.allModes.any (g.modeIsChoosable p))

def activateAbility (g : Game) (p : PlayerId) (id : ObjectId) (abilityIdx : Nat) :
    Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let some o := g.findObject? id | throw "no such object"
  if !o.isOnBattlefield then
    throw s!"{o.name} is not on the battlefield"
  if !o.controlledBy p then
    throw "You don't control that permanent"
  if o.printed.activatedAbilities.isEmpty then
    throw s!"{o.name} has no activated ability"
  let some ab := o.printed.activatedAbilities[abilityIdx]?
    | throw s!"{o.name} has no such activated ability"
  if ab.onlyAsSorcery && !g.asSorcery? p then
    throw s!"{o.name}'s ability can be activated only as a sorcery"
  if ab.onlyDuringYourTurn && g.activePlayer != p then
    throw s!"{o.name}'s ability can be activated only during your turn"
  if ab.onceEachTurn && o.status.activationsThisTurn != 0 then
    throw s!"{o.name}'s ability can be activated only once each turn"
  if ab.cost.tap && o.status.tapped then
    throw s!"{o.name} is already tapped"
  if ab.cost.tap && o.printed.isCreature && o.status.summoningSick && !o.printed.keywords.haste then
    throw s!"{o.name} has summoning sickness (CR 302.6)"
  if ab.cost.sacrificeAnotherCreatureOrArtifact &&
      (g.sacrificeCreatureOrArtifactChoices p id).isEmpty then
    throw s!"{o.name}'s ability requires sacrificing another creature or artifact"
  if !ab.allModes.any (g.modeIsChoosable p) then
    throw s!"{o.name}'s ability requires a target"
  let pl := g.player p
  let stackBefore := g.stack
  let manaBefore := pl.manaPool
  let (g, newId) := g.allocId
  let (g, ts) := g.bumpTime
  let abilityObj : GameObject := {
    id := newId
    printed := {
      name := s!"{o.name}'s ability"
      types := #[]
      oracleText := o.printed.oracleText
    }
    owner := o.owner
    controller := some p
    zone := .stack
    timestamp := ts
    abilityEffect := if ab.isModal then none else some ab.effect
    sourceId := some id
  }
  let entry : StackEntry := { objectId := newId, controller := p, targets := #[] }
  let g := { g with
    objects := g.objects.push abilityObj
    stack := g.stack.push entry
    consecutivePasses := 0 }
  let g := g.logMsg s!"{pl.name} begins activating {o.name}"
  if !ab.isModal && !ab.effect.requiresTarget &&
      !ab.cost.mana.includesManaPayment && !ab.cost.sacrificeAnotherCreatureOrArtifact then
    let g ← g.payActivationExtraCosts p id ab.cost.tap ab.cost.sacrificeSource
    return g.becomeActivated p o.name (some id)
  let prop : ProposedSpell := {
    caster := p
    cost := ab.cost.mana
    spellId := newId
    original := o
    handBefore := pl.hand
    stackBefore := stackBefore
    manaBefore := manaBefore
    kind := .activatedAbility
    sourceId := some id
    tapSource := ab.cost.tap
    sacrificeSource := ab.cost.sacrificeSource
    needsSacrificeOther := ab.cost.sacrificeAnotherCreatureOrArtifact
    abilityModes := ab.allModes
  }
  if ab.isModal then
    let g := { g with pending := .chooseMode p, proposedSpell := some prop }
    return g.logMsg s!"{pl.name} must choose a mode (CR 601.2b)"
  if ab.effect.requiresTarget then
    let g := { g with pending := .chooseTargets p, proposedSpell := some prop }
    return g.logMsg s!"{pl.name} must choose a target (CR 601.2c)"
  let g := { g with pending := .activateManaAbilities p, proposedSpell := some prop }
  return g.logMsg s!"{pl.name} may activate mana abilities (CR 601.2g)"

/-- After mana is paid, sacrifice another creature or artifact (CR 601.2h). -/
def sacrificeForActivation (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .sacrificePermanent caster sourceId =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeAsCreatureOrArtifact p sourceId sac then
      throw s!"Can't sacrifice {sac.name}"
    let g := g.logMsg s!"{(g.player p).name} sacrifices {sac.name}"
    let (g, _) := g.move id (.graveyard sac.owner) none
    let sourceName :=
      match g.proposedSpell with
      | some prop => prop.original.name
      | none => (g.object! sourceId).name
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeActivated p sourceName (some sourceId)
  | _ => throw "Not time to sacrifice a permanent"

def applyEffect (g : Game) (_controller : PlayerId) (effect : SpellEffect)
    (targets : Array Target) : Game :=
  match effect, targets[0]? with
  | .dealDamage n, some (Target.player pid) =>
    let pl := g.player pid
    let g := g.setPlayer { pl with life := pl.life - n }
    g.logMsg s!"{pl.name} is dealt {n} damage ({g.player pid |>.life} life)"
  | .dealDamage n, some (Target.permanent oid) =>
    match g.findObject? oid with
    | none => g.logMsg "The target is no longer in play"
    | some o =>
      let g := g.setObject { o with status := { o.status with damage := o.status.damage + n } }
      g.logMsg s!"{o.name} is dealt {n} damage"
  | .pump pw tw, some (Target.permanent oid) =>
    match g.findObject? oid with
    | none => g.logMsg "The target is no longer in play"
    | some o =>
      let g := g.setObject { o with
        status := { o.status with pumpPower := o.status.pumpPower + pw, pumpToughness := o.status.pumpToughness + tw } }
      g.logMsg s!"{o.name} gets +{pw}/+{tw} until end of turn"
  | _, _ => g

/-- Search `p`'s library for a basic land card, put it onto the battlefield
tapped, then shuffle (CR 701.19). Picks the first matching card in library
order (bottom first). -/
def resolveSearchBasicLandTapped (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  let found := pl.library.find? (fun id =>
    match g.findObject? id with
    | some o => isBasicLandCard o.printed
    | none => false)
  let g :=
    match found with
    | none =>
      g.logMsg s!"{pl.name} searches their library and finds no basic land card"
    | some landId =>
      let landName := (g.object! landId).name
      let (g, newId) := g.move landId .battlefield (some p)
      let o := g.object! newId
      let g := g.setObject { o with
        status := { o.status with tapped := true, summoningSick := false } }
      g.logMsg s!"{pl.name} puts {landName} onto the battlefield tapped"
  g.shuffleLibrary p

/-- Exile the top card of `p`'s library and grant permission to play it until
the end of that player's next turn (CR 701.14). -/
def resolveExileTopPlayUntilEndOfNextTurn (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    g.logMsg s!"{pl.name} has no cards in their library to exile"
  else
    let top := pl.library.back!
    let cardName := (g.object! top).name
    let (g, newId) := g.move top .exile none
    let o := g.object! newId
    let g := g.setObject { o with
      playPermission := some { player := p, turnEndsRemaining := 2 } }
    g.logMsg
      s!"{pl.name} exiles {cardName} and may play it until the end of their next turn"

/-- Log why a targeted ability failed to affect its announced target (CR 608.2b). -/
def illegalAbilityTarget (g : Game) : Target → Game
  | Target.player _ => g.logMsg "The target is no longer legal"
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o =>
      if o.isOnBattlefield then g.logMsg "The target is no longer legal"
      else g.logMsg "The target is no longer in play"
    | none => g.logMsg "The target is no longer in play"

def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : AbilityEffect)
    (targets : Array Target) : Game :=
  match effect with
  | .searchBasicLandTapped => g.resolveSearchBasicLandTapped controller
  | .exileTopPlayUntilEndOfNextTurn => g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .dealDamageToTargetCreature n =>
    match targets[0]? with
    | none => g
    | some t =>
      if (g.legalAbilityTargets controller effect).contains t then
        g.applyEffect controller (.dealDamage n) targets
      else
        g.illegalAbilityTarget t
  | .destroyTargetColorlessNonland =>
    match targets[0]? with
    | none => g
    | some t =>
      if (g.legalAbilityTargets controller effect).contains t then
        match t with
        | Target.permanent oid =>
          let o := g.object! oid
          let (g, _) := g.move oid (.graveyard o.owner) none
          g.logMsg s!"{o.name} is destroyed"
        | Target.player _ => g.logMsg "The target is no longer legal"
      else
        g.illegalAbilityTarget t

/-- Top `count` cards of `p`'s library (last = current top). -/
def scryLookedIds (g : Game) (p : PlayerId) (count : Nat) : Array ObjectId :=
  let lib := (g.player p).library
  let n := min count lib.size
  lib.extract (lib.size - n) lib.size

/-- Start scrying `n` as a keyword action during resolution (CR 701.20). -/
def beginScry (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  let count := min n pl.library.size
  if count == 0 then
    g.logMsg s!"{pl.name} scries {n} (no cards to look at)"
  else
    { g with pending := .scry p count }.logMsg s!"{pl.name} scries {n}"

/-- Resolve a triggered ability (CR 608). `sourceId` is the object that generated it. -/
def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) : Game :=
  match ab with
  | .onAttackPumpByGreatestPower =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let x := g.greatestPowerAmongCreatures controller
        g.applyEffect controller (.pump x 0) #[Target.permanent o.id]
      else
        g.logMsg s!"{o.name} is no longer on the battlefield"
    | none =>
      g.logMsg "The triggered ability's source is no longer in play"
  | .onBecomesBlockedDeal1ToBlockers =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let blockers := g.blockersOf o.id
        if blockers.isEmpty then
          g.logMsg s!"there are no creatures blocking {o.name}"
        else
          Id.run do
            let mut g := g
            for b in blockers do
              let bNow := g.object! b.id
              g := g.setObject { bNow with
                status := { bNow.status with damage := bNow.status.damage + 1 } }
              g := g.logMsg s!"{o.name} deals 1 damage to {bNow.name}"
            return g
      else
        g.logMsg s!"{o.name} is no longer on the battlefield"
    | none =>
      g.logMsg "The triggered ability's source is no longer in play"
  | .onEnterScry n =>
    g.beginScry controller n

/-- Put a triggered ability of `source` onto the stack (CR 603.3). -/
def putTriggeredAbilityOnStack (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String) : Game :=
  let (g, newId) := g.allocId
  let (g, ts) := g.bumpTime
  let abilityObj : GameObject := {
    id := newId
    printed := {
      name := s!"{source.name}'s ability"
      types := #[]
      oracleText := source.printed.oracleText
    }
    owner := source.owner
    controller := some controller
    zone := .stack
    timestamp := ts
    triggeredAbility := some ab
    sourceId := some source.id
  }
  let entry : StackEntry := { objectId := newId, controller := controller, targets := #[] }
  let g := { g with
    objects := g.objects.push abilityObj
    stack := g.stack.push entry
    consecutivePasses := 0 }
  g.logMsg s!"{source.name}'s {event} is put on the stack"

/-- Put attack-triggered abilities of `attackerIds` onto the stack (CR 508.2). -/
def putAttackTriggersOnStack (g : Game) (p : PlayerId) (attackerIds : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for id in attackerIds do
      let o := g.object! id
      for ab in o.printed.triggeredAbilities do
        if ab.triggersWhenAttacking then
          g := g.putTriggeredAbilityOnStack p o ab "attack trigger"
    return g

/-- Put becomes-blocked triggers for unique attackers in `assignments` (CR 509.5c). -/
def putBlockedTriggersOnStack (g : Game) (assignments : Array (ObjectId × ObjectId)) : Game :=
  Id.run do
    let mut g := g
    let mut seen : Array ObjectId := #[]
    for (_, attackerId) in assignments do
      if !seen.contains attackerId then
        seen := seen.push attackerId
        let o := g.object! attackerId
        match o.controller with
        | none => pure ()
        | some p =>
          for ab in o.printed.triggeredAbilities do
            if ab.triggersWhenBecomesBlocked then
              g := g.putTriggeredAbilityOnStack p o ab "becomes-blocked trigger"
    return g

/-- Put enters-the-battlefield triggers of `o` onto the stack (CR 603.6a). -/
def putEnterTriggersOnStack (g : Game) (o : GameObject) : Game :=
  match o.controller with
  | none => g
  | some p =>
    Id.run do
      let mut g := g
      for ab in o.printed.triggeredAbilities do
        if ab.triggersWhenEntering then
          g := g.putTriggeredAbilityOnStack p o ab "enters trigger"
      return g

/-- Whether `host` is a legal Enchant-creature attachment (CR 303.4). -/
def isLegalAuraHost (host : GameObject) : Bool :=
  host.isOnBattlefield && host.printed.isCreature

/-- Resolve an Aura spell, attaching it or putting it into the graveyard (CR 303.4, 608.3a). -/
def resolveAuraSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let toGraveyard (g : Game) : Game :=
    let (g, _) := g.move obj.id (.graveyard obj.owner) none
    g.logMsg s!"{obj.name} goes to the graveyard (illegal Aura target)"
  match entry.targets[0]? with
  | some (Target.permanent hostId) =>
    match g.findObject? hostId with
    | some host =>
      if isLegalAuraHost host then
        let (g, newId) := g.move obj.id .battlefield (some entry.controller)
        let o := g.object! newId
        let g := g.setObject { o with attachedTo := some host.id }
        let g := g.logMsg s!"{o.name} enters the battlefield attached to {host.name}"
        g.putEnterTriggersOnStack (g.object! newId)
      else
        toGraveyard g
    | none => toGraveyard g
  | _ => toGraveyard g

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    let g := { g with stack := g.stack.pop }
    match g.findObject? entry.objectId with
    | none => g.logMsg "The spell left the stack unexpectedly"
    | some obj =>
      if let some e := obj.abilityEffect then
        let g := g.applyAbilityEffect entry.controller e entry.targets
        -- CR 608.2m: after resolution the ability ceases to exist.
        { g with objects := g.objects.filter (fun o => o.id != obj.id) }
      else if let some t := obj.triggeredAbility then
        let g := g.applyTriggeredAbility entry.controller t obj.sourceId
        { g with objects := g.objects.filter (fun o => o.id != obj.id) }
      else
        let g :=
          if let some e := obj.printed.spellEffect then
            g.applyEffect entry.controller e entry.targets
          else g
        if obj.printed.isAura then
          g.resolveAuraSpell entry obj
        else if obj.printed.isPermanentCard && !obj.printed.isLand then
          let (g, newId) := g.move obj.id .battlefield (some entry.controller)
          let o := g.object! newId
          let sick := o.printed.isCreature && !o.printed.keywords.haste
          let g := g.setObject { o with status := { o.status with summoningSick := sick } }
          let g := g.logMsg s!"{o.name} enters the battlefield"
          g.putEnterTriggersOnStack (g.object! newId)
        else
          let owner := obj.owner
          let (g, _) := g.move obj.id (.graveyard owner) none
          g.logMsg s!"{obj.name} goes to the graveyard"

def declareAttackers (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  if g.pending != .declareAttackers || g.activePlayer != p then
    throw "Not time to declare attackers"
  let mut g := g
  for id in ids do
    let o := g.object! id
    if !g.canAttack o then
      throw s!"{o.name} cannot attack"
    g := g.setObject { o with status := { o.status with attacking := true, tapped := true } }
    g := g.logMsg s!"{g.player p |>.name} attacks with {o.name}"
  if ids.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not attack"
  g := g.putAttackTriggersOnStack p ids
  return { g with pending := .none } |>.receivePriority p

def declareBlockers (g : Game) (p : PlayerId) (assignments : Array (ObjectId × ObjectId)) :
    Except String Game := do
  if g.pending != .declareBlockers then
    throw "Not time to declare blockers"
  if p != g.opponent g.activePlayer then
    throw "Only the defending player declares blockers"
  let mut g := g
  for (blockerId, attackerId) in assignments do
    let b := g.object! blockerId
    let a := g.object! attackerId
    if !g.canBlock b a then
      throw s!"{b.name} cannot block {a.name}"
    g := g.setObject { b with status := { b.status with blocking := some attackerId } }
    let aNow := g.object! attackerId
    g := g.setObject { aNow with status := { aNow.status with blocked := true } }
    g := g.logMsg s!"{b.name} blocks {a.name}"
  if assignments.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not block"
  g := g.putBlockedTriggersOnStack assignments
  return { g with pending := .none } |>.receivePriority g.activePlayer

def combatDamage (g : Game) : Game :=
  Id.run do
    let mut g := g
    let attackers := g.battlefield.filter (·.status.attacking)
    for a in attackers do
      let blockers := g.blockersOf a.id
      if blockers.isEmpty then
        if a.status.blocked && !g.hasTrample a then
          -- CR 510.1c: a blocked creature with no remaining blockers assigns none.
          g := g.logMsg
            s!"{a.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
        else
          let defn := g.opponent g.activePlayer
          let dmg := max (g.power a) 0
          if dmg > 0 then
            let pl := g.player defn
            g := g.setPlayer { pl with life := pl.life - dmg }
            -- Blocked with trample and no remaining blockers: all damage to the
            -- player (CR 702.19d). Unblocked creatures deal combat damage.
            if a.status.blocked then
              g := g.logMsg
                s!"{a.name} tramples for {dmg} to {pl.name} ({(g.player defn).life} life)"
            else
              g := g.logMsg
                s!"{a.name} deals {dmg} combat damage to {pl.name} ({(g.player defn).life} life)"
      else
        -- All combat damage from the attacker is assigned to the first blocker;
        -- leftover trample damage goes to the defending player.
        let b := blockers[0]!
        let dmg := max (g.power a) 0
        let lethal := max (g.toughness b) 0
        let trampling := g.hasTrample a
        let toBlocker := if trampling then min dmg lethal else dmg
        let toPlayer := if trampling then dmg - toBlocker else 0
        g := g.setObject { b with status := { b.status with damage := b.status.damage + toBlocker } }
        g := g.logMsg s!"{a.name} deals {toBlocker} combat damage to {b.name}"
        if toPlayer > 0 then
          let defn := g.opponent g.activePlayer
          let pl := g.player defn
          g := g.setPlayer { pl with life := pl.life - toPlayer }
          g := g.logMsg s!"{a.name} tramples for {toPlayer} to {pl.name} ({(g.player defn).life} life)"
        let back := max (g.power b) 0
        if back > 0 then
          let aNow := g.object! a.id
          g := g.setObject { aNow with status := { aNow.status with damage := aNow.status.damage + back } }
          g := g.logMsg s!"{b.name} deals {back} combat damage to {a.name}"
    return g

def clearCombat (g : Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.status.attacking || o.status.blocking.isSome || o.status.blocked then
        g := g.setObject { o with
          status := { o.status with attacking := false, blocking := none, blocked := false } }
    return g

def clearEOT (g : Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.status.damage != 0 || o.status.pumpPower != 0 || o.status.pumpToughness != 0 then
        g := g.setObject { o with
          status := { o.status with damage := 0, pumpPower := 0, pumpToughness := 0 } }
    return g

/-- Discard down to maximum hand size (CR 514.1). This turn-based action does
not use the stack; the engine discards from the back of the hand array. -/
def discardToMaxHandSize (g : Game) : Game :=
  let pl := g.player g.activePlayer
  let extra := pl.hand.size - pl.maxHandSize
  if extra == 0 then g
  else
    Id.run do
      let mut g := g
      for _ in [0:extra] do
        let pl := g.player g.activePlayer
        if let some last := pl.hand.back? then
          let card := g.object! last
          let (g', _) := g.move last (.graveyard pl.id) none
          g := g'.logMsg s!"{pl.name} discards {card.name} (cleanup)"
      return g

/-- Clear “once each turn” activation counts as a turn ends. -/
def clearTurnActivations (g : Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.status.activationsThisTurn != 0 then
        g := g.setObject { o with status := { o.status with activationsThisTurn := 0 } }
    return g

/-- Expire or decrement play-from-exile permissions as `endingPlayer`'s turn ends. -/
def expirePlayPermissions (g : Game) (endingPlayer : PlayerId) : Game :=
  Id.run do
    let mut g := g
    for o in g.objects do
      match o.playPermission with
      | none => pure ()
      | some perm =>
        if perm.player == endingPlayer then
          if perm.turnEndsRemaining ≤ 1 then
            g := g.setObject { o with playPermission := none }
            if o.zone == .exile then
              g := g.logMsg s!"{o.name} can no longer be played from exile"
          else
            g := g.setObject { o with
              playPermission := some { perm with
                turnEndsRemaining := perm.turnEndsRemaining - 1 } }
    return g

/-- Advance to the next living player's turn after a cleanup step ends. -/
def startNextTurn (g : Game) : Game :=
  let ending := g.activePlayer
  let g := g.expirePlayPermissions ending |>.clearTurnActivations
  let nxt := g.nextLiving ending
  let g := { g with
    activePlayer := nxt
    turnNumber := g.turnNumber + 1
    isFirstTurn := false
    cleanupGivesPriority := false }
  g.logMsg s!"It is now {g.player nxt |>.name}'s turn {g.turnNumber}"

/-- `partial` because a silent cleanup (CR 514.3) immediately begins the next
turn, and a skipped draw step (CR 103.8a / 500.11) immediately begins
precombat main; both re-enter `beginStep`. -/
partial def beginStep (g : Game) (st : Step) : Game :=
  let g := { g with
    step := st
    pending := .none
    consecutivePasses := 0
    cleanupGivesPriority := false
    proposedSpell := none }
  let g := g.logMsg s!"— Turn {g.turnNumber}, {g.player g.activePlayer |>.name}: {st} —"
  match st with
  | .untap =>
    Id.run do
      let mut g := g
      let ap := g.activePlayer
      let apName := (g.player ap).name
      g := g.modifyPlayer ap (fun pl => { pl with landsPlayedThisTurn := 0 })
      for o in g.permanentsOf ap do
        -- CR 502.2: the active player untaps their permanents. Logging each
        -- previously tapped permanent makes the battlefield status change
        -- visible in the demo before the zone reprint.
        if o.status.tapped then
          g := g.logMsg s!"{apName} untaps {o.name}"
        g := g.setObject { o with status := { o.status with tapped := false, summoningSick := false } }
      -- No priority (CR 502.4). Immediately continue.
      return g
  | .draw =>
    if g.skipsFirstDraw then
      -- CR 103.8a / 500.11 / 614.10: to skip a step is to proceed past it as
      -- though it didn't exist. Nothing happens during it — no turn-based
      -- draw, and no player receives priority.
      g.logMsg s!"{g.player g.activePlayer |>.name} skips their first draw step (CR 103.8a)"
        |>.beginStep .precombatMain
    else
      g.draw g.activePlayer |>.receivePriority g.activePlayer
  | .declareAttackers =>
    { g with pending := .declareAttackers }
  | .declareBlockers =>
    if (g.battlefield.filter (·.status.attacking)).isEmpty then
      g.logMsg "No attackers; skipping declare blockers and combat damage (CR 508.8)"
    else
      { g with pending := .declareBlockers }
  | .combatDamage =>
    if (g.battlefield.filter (·.status.attacking)).isEmpty then
      g
    else
      g.combatDamage |>.receivePriority g.activePlayer
  | .cleanup =>
    -- Combatants leave combat; then CR 514.1–514.3.
    let g := g.clearCombat
    let g := g.discardToMaxHandSize
    let g := g.clearEOT
    -- CR 514.3 / 514.3a / 704.3: normally no priority. If state-based actions
    -- would be performed or triggered abilities are waiting, perform them,
    -- put the triggers on the stack, and the active player receives priority.
    let (g, sba) := g.checkSBACounted
    if g.over then g
    else if sba || g.hasWaitingTriggers then
      let g := { g with cleanupGivesPriority := true }
      let g := g.logMsg "Players receive priority during cleanup (CR 514.3a)"
      g.receivePriority g.activePlayer
    else
      -- The cleanup step ends (CR 500.3) and the turn ends.
      let g := g.emptyManaPools
      (g.startNextTurn).beginStep .untap |>.beginStep .upkeep
  | _ =>
    g.receivePriority g.activePlayer

def beginTurn (g : Game) : Game :=
  -- No player receives priority during untap (CR 502.4).
  (g.beginStep .untap).beginStep .upkeep

/-- Advance after both players pass with an empty stack (CR 500.2). -/
def advanceStep (g : Game) : Game :=
  let g := g.emptyManaPools
  match g.step.next? with
  | some st =>
    -- Skip declare blockers / combat damage when no attackers.
    let attackers := g.battlefield.filter (·.status.attacking)
    if g.step == .declareAttackers && attackers.isEmpty then
      g.beginStep .endOfCombat
    else if g.step == .declareBlockers && attackers.isEmpty then
      g.beginStep .endOfCombat
    else
      g.beginStep st
  | none =>
    -- Leaving cleanup. If CR 514.3a granted priority this step, another
    -- cleanup step begins; otherwise the turn ends (CR 514.3 / 500.3).
    if g.cleanupGivesPriority then
      g.beginStep .cleanup
    else
      g.startNextTurn |>.beginTurn

/-- Pay the proposed spell or ability (CR 601.2h / 602.2b). If the cost
cannot be paid, the action is reversed (CR 733.1). -/
def pay (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .activateManaAbilities caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may pay (CR 601.2h)"
    g.finishProposedSpell
  | .chooseTargets _ =>
    throw "Choose a target first (CR 601.2c)"
  | .chooseMode _ =>
    throw "Choose a mode first (CR 601.2b)"
  | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"

def pass (g : Game) (p : PlayerId) : Except String Game := do
  if g.over then
    throw "The game is over"
  if g.pending != .none then
    throw "A required choice is still pending"
  if !g.playersReceivePriority then
    throw "No player receives priority right now (CR 117.3a / 514.3)"
  if g.priority != p then
    throw "You don't have priority"
  let g := g.logMsg s!"{g.player p |>.name} passes priority"
  let g := { g with consecutivePasses := g.consecutivePasses + 1 }
  if g.consecutivePasses ≥ g.livingPlayers.size then
    if !g.stack.isEmpty then
      let g := g.resolveTop
      if g.pending != .none then
        return g
      return g.receivePriority g.activePlayer
    else
      return g.advanceStep
  else
    return { g with priority := g.nextLiving p }

def concede (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  let g := g.setPlayer { pl with lost := true }
  let g := g.logMsg s!"{pl.name} concedes (CR 104.3a)"
  g.checkSBA

/-- True while players are still keeping or taking mulligans (CR 103.5). -/
def openingHandsPending (g : Game) : Bool :=
  match g.pending with
  | .declareMulligan _ | .putOnBottom _ _ => true
  | _ => false

/-- Players who have not yet kept an opening hand, in turn order from the
starting player (CR 103.5). -/
def playersStillDecidingMulligan (g : Game) : Array PlayerId :=
  let n := g.players.size
  Id.run do
    let mut acc : Array PlayerId := #[]
    for k in [0:n] do
      let q : PlayerId := ⟨(g.startingPlayer.idx + k) % n⟩
      let pl := g.player q
      if !pl.lost && !pl.keptOpeningHand then
        acc := acc.push q
    return acc

def promptMulligan (g : Game) (p : PlayerId) : Game :=
  { g with pending := .declareMulligan p }
    |>.logMsg s!"{g.player p |>.name} may keep or take a mulligan (CR 103.5)"

def promptBottom (g : Game) (p : PlayerId) : Game :=
  let n := (g.player p).mulligansTaken
  let cards := if n == 1 then "1 card" else s!"{n} cards"
  { g with pending := .putOnBottom p n }
    |>.logMsg s!"{g.player p |>.name} puts {cards} on the bottom of their library (CR 103.5)"

/-- After every remaining player has kept, the starting player takes their
first turn (CR 103.8). -/
def finishOpeningHands (g : Game) : Game :=
  let g := { g with
    pending := .none
    mulliganToDeclare := #[]
    willMulligan := #[]
    mulliganToBottom := #[] }
  let g := g.logMsg s!"{g.player g.startingPlayer |>.name} takes the first turn"
  g.beginTurn

/-- Start (or restart) a CR 103.5 round: eligible players declare in turn
order. When nobody remains, the game begins. -/
def beginMulliganRound (g : Game) : Game :=
  if g.over then g
  else
    let remaining := g.playersStillDecidingMulligan
    if remaining.isEmpty then
      g.finishOpeningHands
    else
      promptMulligan
        { g with
          mulliganToDeclare := remaining
          willMulligan := #[]
          mulliganToBottom := #[] }
        remaining[0]!

/-- Shuffle the cards in `p`'s hand back into their library (CR 103.5). -/
def returnHandToLibrary (g : Game) (p : PlayerId) : Game :=
  Id.run do
    let mut g := g
    let ids := (g.player p).hand
    for id in ids do
      let (g', _) := g.move id (.library p)
      g := g'
    return g

/-- A player may mulligan until that mulligan would leave a zero-card opening
hand, after which they may not take further mulligans (CR 103.5). -/
def canTakeMulligan (g : Game) (p : PlayerId) : Bool :=
  let pl := g.player p
  !g.over && !pl.keptOpeningHand && pl.mulligansTaken < pl.startingHandSize

/-- Perform one already-declared mulligan: shuffle, then draw a new starting
hand (CR 103.5). Bottoming is a later choice. -/
def executeOneMulligan (g : Game) (p : PlayerId) : Game :=
  let n := (g.player p).mulligansTaken + 1
  let size := (g.player p).startingHandSize
  let g := g.modifyPlayer p (fun pl => { pl with mulligansTaken := n })
  let g := g.logMsg s!"{g.player p |>.name} takes a mulligan ({n})"
  let g := g.returnHandToLibrary p
  let g := g.shuffleLibrary p
  g.draw p size

/-- After every remaining player has declared, those who chose to mulligan
do so at the same time (CR 103.5). -/
def resolveDeclaredMulligans (g : Game) : Game :=
  if g.willMulligan.isEmpty then
    g.beginMulliganRound
  else
    let order := g.playersStillDecidingMulligan.filter (fun p => g.willMulligan.contains p)
    let g := g.logMsg
      "Players who chose to mulligan do so at the same time (CR 103.5)"
    let g :=
      Id.run do
        let mut g := g
        for p in order do
          g := g.executeOneMulligan p
        return g
    if order.isEmpty then
      g.beginMulliganRound
    else
      promptBottom { g with willMulligan := #[], mulliganToBottom := order } order[0]!

/-- After `who` has declared keep or mulligan, the next declarer in this round
acts. When the round's declarations are complete, pending mulligans are taken
together. -/
def afterDeclaration (g : Game) (who : PlayerId) : Game :=
  if g.over then g
  else
    let rest := g.mulliganToDeclare.filter (fun q => q != who)
    let g := { g with mulliganToDeclare := rest }
    if rest.isEmpty then
      g.resolveDeclaredMulligans
    else
      g.promptMulligan rest[0]!

/-- After `who` has put cards on the bottom, the next such player acts, or a
new declaration round begins. -/
def afterBottom (g : Game) (who : PlayerId) : Game :=
  if g.over then g
  else
    let rest := g.mulliganToBottom.filter (fun q => q != who)
    let g := { g with mulliganToBottom := rest }
    if rest.isEmpty then
      g.beginMulliganRound
    else
      g.promptBottom rest[0]!

def uniqueObjectIds (ids : Array ObjectId) : Bool :=
  Id.run do
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        return false
      seen := seen.push id
    return true

def isPermutation (a b : Array ObjectId) : Bool :=
  a.size == b.size && uniqueObjectIds a && a.all (fun x => b.contains x)

/-- Finish scrying: put `bottom` on the bottom (first = new bottom) and `top`
on top (last = new top) of the library, each pile in the given order (CR 701.20). -/
def finishScry (g : Game) (p : PlayerId) (top bottom : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .scry q count =>
    if p != q then
      throw s!"Only {(g.player q).name} may scry"
    if !uniqueObjectIds (top ++ bottom) then
      throw "Duplicate card"
    let looked := g.scryLookedIds p count
    if !isPermutation (top ++ bottom) looked then
      throw "Scry must rearrange the cards you looked at (CR 701.20)"
    let pl := g.player p
    let lower := pl.library.extract 0 (pl.library.size - count)
    let mut g := g
    for id in bottom do
      g := g.logMsg
        s!"{(g.player p).name} puts {(g.object! id).name} on the bottom of their library"
    if top != looked then
      for id in top do
        g := g.logMsg
          s!"{(g.player p).name} puts {(g.object! id).name} on top of their library"
    g := g.setPlayer { (g.player p) with library := bottom ++ lower ++ top }
    g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to scry (CR 701.20)"

def keepOpeningHand (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    let g := g.modifyPlayer p (fun pl => { pl with keptOpeningHand := true })
    let g := g.logMsg
      s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterDeclaration p
  | _ => throw "Not time to keep an opening hand (CR 103.5)"

/-- Record that this player will mulligan. The mulligan itself is taken only
after every remaining player has declared (CR 103.5). -/
def takeMulligan (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    if (g.player p).keptOpeningHand then
      throw "You already kept your opening hand (CR 103.5)"
    if !g.canTakeMulligan p then
      throw "A player may not take further mulligans after their opening hand would be zero cards (CR 103.5)"
    let g := { g with willMulligan := g.willMulligan.push p }
    let g := g.logMsg s!"{g.player p |>.name} will take a mulligan (CR 103.5)"
    return g.afterDeclaration p
  | _ => throw "Not time to take a mulligan (CR 103.5)"

/-- Place the listed cards on the bottom of `p`'s library. The first listed
card becomes the new bottom; later cards sit above it. -/
def putCardsOnBottom (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .putOnBottom q n =>
    if p != q then
      throw "Only the player who took a mulligan may put cards on the bottom (CR 103.5)"
    if ids.size != n then
      throw s!"Put exactly {n} card(s) on the bottom of your library (CR 103.5)"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let pl := g.player p
    for id in ids do
      if (g.findObject? id).isNone then
        throw "no such object"
      if !pl.hand.contains id then
        throw "That card is not in your hand"
    let mut g := g
    let mut newBottom : Array ObjectId := #[]
    for id in ids do
      let card := g.object! id
      let ownerName := (g.player p).name
      let (g', newId) := g.move id (.library p)
      g := g'
      newBottom := newBottom.push newId
      g := g.logMsg s!"{ownerName} puts {card.name} on the bottom of their library"
    let plNow := g.player p
    let without := newBottom.foldl (fun lib id => stripId lib id) plNow.library
    g := g.setPlayer { plNow with library := newBottom ++ without }
    -- After a mulligan to zero, the player may not take further mulligans.
    if !g.canTakeMulligan p then
      g := g.modifyPlayer p (fun pl => { pl with keptOpeningHand := true })
      g := g.logMsg
        s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterBottom p
  | _ => throw "Not time to put cards on the bottom (CR 103.5)"

def apply (g : Game) (p : PlayerId) : Action → Except String Game
  | .pass => g.pass p
  | .playLand id => g.playLand p id
  | .tapForMana id m => g.tapForMana p id m
  | .cast id => g.castSpell p id
  | .target t => g.announceTarget p t
  | .chooseMode idx => g.announceMode p idx
  | .activate id idx => g.activateAbility p id idx
  | .pay => g.pay p
  | .sacrifice id => g.sacrificeForActivation p id
  | .declareAttackers ids => g.declareAttackers p ids
  | .declareBlockers as => g.declareBlockers p as
  | .keep => g.keepOpeningHand p
  | .takeMulligan => g.takeMulligan p
  | .putOnBottom ids => g.putCardsOnBottom p ids
  | .scry top bottom => g.finishScry p top bottom
  | .concede => return g.concede p

def handObjects (g : Game) (p : PlayerId) : Array GameObject :=
  (g.player p).hand.filterMap (fun id => g.findObject? id)

/-- Who must act next? -/
def actor (g : Game) : Option PlayerId :=
  if g.over then none
  else
    match g.pending with
    | .declareAttackers => some g.activePlayer
    | .declareBlockers => some (g.opponent g.activePlayer)
    | .activateManaAbilities caster => some caster
    | .chooseTargets p => some p
    | .chooseMode p => some p
    | .sacrificePermanent p _ => some p
    | .declareMulligan p => some p
    | .putOnBottom p _ => some p
    | .scry p _ => some p
    | .none =>
      if g.playersReceivePriority then some g.priority else none

end Game

namespace Start

def materializeSeat (g : Game) (seatIdx : Nat) (seat : Seat) : Except String Game := do
  if seat.deck.isEmpty then
    throw s!"{seat.name} has an empty deck"
  match validateDeck g.format seat.deck with
  | .error e => throw s!"{seat.name}: {e}"
  | .ok _ => pure ()
  let pid : PlayerId := ⟨seatIdx⟩
  let player : Player := {
    id := pid
    name := seat.name
    life := 20
    startingLife := 20
  }
  let g := { g with players := g.players.push player }
  return Id.run do
    let mut g := g
    for card in seat.deck do
      let (g', id) := g.allocId
      let (g', ts) := g'.bumpTime
      let obj : GameObject := {
        id := id
        printed := card
        owner := pid
        zone := .library pid
        timestamp := ts
      }
      g := { g' with objects := g'.objects.push obj }
      g := g.modifyPlayer pid (fun pl => { pl with library := pl.library.push id })
    return g

def start (cfg : StartConfig) : Except String Game := do
  if cfg.seats.size < 2 then
    throw "A game needs at least two players (CR 100.1)"
  let mut g : Game := { players := #[], objects := #[], rng := Rng.ofSeed cfg.seed, format := cfg.format }
  for i in [0:cfg.seats.size] do
    g ← materializeSeat g i cfg.seats[i]!
  -- Determine starting player (CR 103.1).
  let (g', startIdx) :=
    match cfg.startingPlayer with
    | some i => (g, i % g.players.size)
    | none =>
      let (rng, r) := g.rng.next
      ({ g with rng := rng }, r.toNat % g.players.size)
  g := g'
  let sp : PlayerId := ⟨startIdx⟩
  g := { g with startingPlayer := sp, activePlayer := sp, priority := sp }
  g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
  g := g.logMsg s!"Starting player: {g.player sp |>.name}"
  for pl in g.players do
    g := g.shuffleLibrary pl.id
  -- Starting life (CR 103.4) already 20. Draw opening hands, then mulligan
  -- (CR 103.5). The first turn begins after every player has kept.
  for pl in g.players do
    g := g.draw pl.id (g.player pl.id).startingHandSize
  return g.beginMulliganRound

end Start

#guard Format.constructed.minDeckSize == 60

end Mtg.Engine
