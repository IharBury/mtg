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
casting the spells we model (CR 601), including choosing modes of modal spells
and abilities (CR 601.2b / 700.2), announcing targets (CR 601.2c), dividing
damage among those targets (CR 601.2d), additional costs such as sacrificing
an artifact or creature (CR 601.2f / 601.2h), and activating mana abilities while
paying (CR 601.2g), activating non-mana abilities of permanents (CR 602),
including destroying permanents (CR 701.7), equip (CR 702.6), and lasting
type-changing animations (CR 205.1a / 611.2a), static abilities that grant
trample, pump an enchanted or equipped creature, set power and toughness
equal to lands you control, or restrict blocking unless you control certain
creature types (CR 604 / 208.2a / 613.3 / 509.1b), until-end-of-turn
layer-7b base P/T setting (CR 613.3b), Aura spells (CR 303.4),
Equipment (CR 301.5), flash (CR 702.8), hexproof (CR 702.11), scry (CR 701.20),
discard (CR 701.9), destroy (CR 701.8), +1/+1 counters (CR 122), until-end-of-turn
keyword grants, attack triggers (CR 508.2 / 603), including copying this
creature's P/T onto another creature you control or giving another creature
+2/+0 and trample, becomes-blocked triggers
(CR 509.5c / 603), enters triggers (CR 603.6a), including damage divided as
you choose when a creature enters or attacks (CR 601.2d), landfall triggers that target (CR 603.3d / 601.2c),
dies triggers that deal damage equal to last-known power (CR 700.4 / 113.7a),
cast triggers that deal damage to each opponent when you cast an instant or
sorcery (CR 601.2i / 603.3),
activated pumps that last until end of turn and activated abilities that
put +1/+1 counters on the source (CR 602 / 611.2a / 122),
adventurer cards including casting an Adventure and later the permanent
(CR 715), combat (CR 506–510, including combat damage assignment under
CR 510.1c–d), cleanup (CR 514.3), and the state-based actions we implement
(CR 704.5).
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
  /-- Attacking creatures this creature is blocking (CR 509.1a / 510.1d). -/
  blocking : Array ObjectId := #[]
  /-- Set when this attacker becomes blocked (CR 509.1h). Remains true even if
  every blocking creature leaves combat. -/
  blocked : Bool := false
  /-- Non-mana activations this turn, for “only once each turn”. -/
  activationsThisTurn : Nat := 0
  /-- +1/+1 counters (CR 122.1). These do not wear off in cleanup. -/
  plusOnePlusOne : Nat := 0
  /-- Granted until end of turn (cleared in cleanup, CR 514.3). -/
  untilEotTrample : Bool := false
  untilEotHexproof : Bool := false
  /-- Until-end-of-turn layer-7b setting of base power (e.g. Galion). -/
  setBasePower : Option Int := none
  /-- Until-end-of-turn layer-7b setting of base toughness (e.g. Galion). -/
  setBaseToughness : Option Int := none
  /-- This permanent is a creature in addition to its other types (CR 205.1a).
  Lasting effects such as Beorn's Hospitality's activation do not end. -/
  additionalCreature : Bool := false
  /-- Subtypes granted by a lasting type-changing effect. -/
  additionalSubtypes : Array String := #[]
  /-- Static abilities granted by a lasting effect (CR 611.2a). -/
  grantedStaticAbilities : Array StaticAbility := #[]
deriving Repr, Inhabited, BEq

/-- Permission to play a card from exile (CR 701.14 / 715.3d). -/
structure PlayPermission where
  /-- The player who may play the card. -/
  player : PlayerId
  /-- Remaining endings of `player`'s turns before the permission expires.
  Granted as 2 during that player's turn so it lasts until the end of their
  next turn. Ignored when `fromAdventure` is true. -/
  turnEndsRemaining : Nat
  /-- CR 715.3d permission from resolving an Adventure: lasts while the card
  remains exiled, and the card cannot be recast as an Adventure this way. -/
  fromAdventure : Bool := false
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
  /-- Last known power of a trigger source (CR 113.7a / 608.2g). -/
  lastKnownPower : Option Int := none
  /-- Last known toughness of a trigger source (CR 113.7a / 608.2g). -/
  lastKnownToughness : Option Int := none
  /-- Set while this card may be played from exile. -/
  playPermission : Option PlayPermission := none
  /-- Object this Aura or Equipment is attached to (CR 303.4 / 301.5). -/
  attachedTo : Option ObjectId := none
  /-- Normal characteristics of an adventurer card, set while the spell is on
  the stack as an Adventure (CR 715.3b). -/
  adventurerCard : Option CardDef := none
deriving Repr, Inhabited

/-- How one attacking or blocking creature assigns its combat damage (CR 510.1). -/
structure CreatureCombatAssignment where
  source : ObjectId
  /-- Damage assigned to creatures blocking it (CR 510.1c) or that it is
  blocking (CR 510.1d). -/
  toCreatures : Array (ObjectId × Int) := #[]
  /-- Leftover assigned to the defending player (unblocked or trample). -/
  toPlayer : Int := 0
deriving Repr, Inhabited, BEq

namespace GameObject

def name (o : GameObject) : String := o.printed.name

/-- Current card types, including a lasting “becomes a creature” effect. -/
def types (o : GameObject) : Array CardType :=
  if o.status.additionalCreature && !o.printed.types.any (· == .creature) then
    o.printed.types.push .creature
  else
    o.printed.types

/-- Current subtypes, including those granted by a lasting type-changing effect. -/
def subtypes (o : GameObject) : Array Subtype :=
  let extra := o.status.additionalSubtypes.filter (fun s => !o.printed.subtypes.any (· == s))
  o.printed.subtypes ++ extra

/-- Type line from current types and subtypes (CR 205.1a). -/
def typeLine (o : GameObject) : String :=
  let super := String.intercalate " " (o.printed.supertypes.toList.map toString)
  let types := String.intercalate " " (o.types.toList.map toString)
  let sub := String.intercalate " " o.subtypes.toList
  let head :=
    if super.isEmpty then types else s!"{super} {types}"
  if sub.isEmpty then head else s!"{head} — {sub}"

/-- Printed power/toughness plus until-EOT pumps and +1/+1 counters. Layer-7b
setting effects such as “equal to the number of lands you control” or an
until-end-of-turn base P/T set are applied in `Game.power` / `Game.toughness`. -/
def power (o : GameObject) : Int :=
  (o.printed.power.getD 0) + o.status.pumpPower + (o.status.plusOnePlusOne : Int)

def toughness (o : GameObject) : Int :=
  (o.printed.toughness.getD 0) + o.status.pumpToughness + (o.status.plusOnePlusOne : Int)

def isOnBattlefield (o : GameObject) : Bool := o.zone == .battlefield

def controlledBy (o : GameObject) (p : PlayerId) : Bool :=
  o.controller == some p

/-- Whether this object is currently a creature (CR 205.1a / 302). -/
def isCreature (o : GameObject) : Bool :=
  o.printed.isCreature || o.status.additionalCreature

/-- True while this spell is on the stack as an Adventure (CR 715.3b). -/
def isAdventureSpell (o : GameObject) : Bool :=
  o.adventurerCard.isSome

def hasSubtype (o : GameObject) (s : String) : Bool :=
  o.subtypes.any (· == s)

/-- Printed static abilities plus those granted by a lasting effect. -/
def staticAbilities (o : GameObject) : Array StaticAbility :=
  o.printed.staticAbilities ++ o.status.grantedStaticAbilities

/-- Colorless nonland permanent (e.g. a legal Goblin Cratermaker destroy target). -/
def isColorlessNonland (o : GameObject) : Bool :=
  o.isOnBattlefield && !o.printed.isLand && o.printed.colors.isColorless

/-- Whether `{T}` in an activation cost is currently payable (CR 302.6). -/
def canPayTapCost (o : GameObject) : Bool :=
  !o.status.tapped &&
  !(o.isCreature && o.status.summoningSick && !o.printed.keywords.haste)

end GameObject

/-- A dies trigger waiting to be put onto the stack after state-based actions
(CR 603.3, 700.4). `source` is a snapshot of the creature as it last existed
on the battlefield. -/
structure WaitingDeathTrigger where
  controller : PlayerId
  source : GameObject
  ability : TriggeredAbility
  lastKnownPower : Int
deriving Repr, Inhabited

/-- A spell or ability on the stack (CR 405). Last array element is the top. -/
structure StackEntry where
  objectId : ObjectId
  controller : PlayerId
  targets : Array Target
  /-- Damage assigned to each target of a “divided as you choose” effect
  (CR 601.2d). Parallel to `targets`. -/
  dividedDamage : Array Nat := #[]
  /-- Set once targets (including choosing zero) have been announced
  (CR 603.3d / 601.2c). -/
  targetsAnnounced : Bool := false
  /-- Chosen mode index for a modal spell (CR 700.2). -/
  chosenMode : Option Nat := none
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
  /-- After mana is paid, the player must sacrifice an artifact or creature
  (another, when this is an activated ability). -/
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
  /-- The player must choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (caster : PlayerId)
  /-- The player must announce targets for the proposed spell (CR 601.2c). -/
  | chooseTargets (caster : PlayerId)
  /-- After `pay`, choose an artifact or creature to sacrifice
  (another, when paying an activated ability). -/
  | sacrificePermanent (player : PlayerId) (sourceId : ObjectId)
  /-- This player declares whether they will take a mulligan (CR 103.5). -/
  | declareMulligan (player : PlayerId)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- This player is looking at the top `count` cards of their library (CR 701.20). -/
  | scry (player : PlayerId) (count : Nat)
  /-- This player may discard a card; if they do, they draw `drawCount` (CR 701.9). -/
  | mayDiscardDraw (player : PlayerId) (drawCount : Nat)
  /-- The player announces how attacking (`forAttackers`) or blocking creatures
  assign combat damage (CR 510.1c–d). -/
  | assignCombatDamage (player : PlayerId) (forAttackers : Bool)
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
  /-- Cast this adventurer card as its Adventure (CR 715.3). -/
  | castAdventure (id : ObjectId)
  /-- Choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (idx : Nat)
  /-- Announce a target for the proposed spell (CR 601.2c). For a divided-
  damage ability, assigns all remaining damage to this target (CR 601.2d). -/
  | target (t : Target)
  /-- Assign `n` damage to target `t` of a “divided as you choose” effect
  (CR 601.2d). -/
  | divideDamage (t : Target) (n : Nat)
  /-- Activate a non-mana activated ability of a permanent (CR 602). -/
  | activate (id : ObjectId) (abilityIdx : Nat)
  /-- Pay the locked-in cost of a proposed spell or ability (CR 601.2h / 602.2b). -/
  | pay
  /-- After `pay`, sacrifice an artifact or creature to finish paying
  (CR 601.2h / 602.2b). -/
  | sacrifice (id : ObjectId)
  | declareAttackers (ids : Array ObjectId)
  | declareBlockers (assignments : Array (ObjectId × ObjectId))
  /-- Announce combat damage assignment (CR 510.1). Omitted sources use a
  legal default; listed sources must divide their power among legal creature
  recipients (and leftover to the defending player only with trample). -/
  | assignCombatDamage (assignments : Array CreatureCombatAssignment)
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
  /-- Discard this card from hand; if a pending “may discard, then draw” is
  waiting, draw afterward (CR 701.9). -/
  | discard (id : ObjectId)
  /-- Decline an optional “you may discard a card”, or choose no target for an
  “up to one” trigger (CR 608.2d / 601.2c). -/
  | decline
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
  /-- Combat damage assigned this step and not yet dealt (CR 510.1 / 510.2). -/
  assignedCombatDamage : Array CreatureCombatAssignment := #[]
  /-- Dies triggers waiting to be put onto the stack (CR 603.3 / 700.4). -/
  waitingDeathTriggers : Array WaitingDeathTrigger := #[]
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
Auras and Equipment attached to a permanent that leaves the battlefield
become unattached and remain on the battlefield (CR 701.3d). -/
def unattachFrom (g : Game) (hostId : ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.attachedTo == some hostId then
        g := g.setObject { o with attachedTo := none }
        g := g.logMsg s!"{o.name} becomes unattached"
    return g

/-- Power of `o` as last known information, including pumps, counters, land-count
setting effects, until-EOT base setting, and attached bonuses (CR 113.7a / 208.2).
Computed before `o` leaves the battlefield. -/
def snapshotPower (g : Game) (o : GameObject) : Int :=
  let attached : Int :=
    if !o.isOnBattlefield then 0
    else
      g.battlefield.foldl
        (fun acc aura =>
          if aura.attachedTo == some o.id then
            acc +
              aura.staticAbilities.foldl
                (fun n ab =>
                  match ab with
                  | .enchantedCreatureGets p _ | .equippedCreatureGets p _ => n + p
                  | .otherCreaturesHaveTrample _ | .powerToughnessEqualLandsYouControl
                  | .cantBlockUnlessYouControl _ => n)
                (0 : Int)
          else acc)
        (0 : Int)
  let setByLands :=
    o.staticAbilities.any (fun ab =>
      match ab with
      | .powerToughnessEqualLandsYouControl => true
      | .otherCreaturesHaveTrample _ | .enchantedCreatureGets _ _
      | .equippedCreatureGets _ _ | .cantBlockUnlessYouControl _ => false)
  let base :=
    match o.status.setBasePower with
    | some n => n
    | none =>
      if o.isOnBattlefield && setByLands then
        match o.controller with
        | some p => Int.ofNat ((g.permanentsOf p).filter (·.printed.isLand) |>.size)
        | none => 0
      else
        o.printed.power.getD 0
  base + o.status.pumpPower + (o.status.plusOnePlusOne : Int) + attached

/-- Toughness of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotToughness (g : Game) (o : GameObject) : Int :=
  let attached : Int :=
    if !o.isOnBattlefield then 0
    else
      g.battlefield.foldl
        (fun acc aura =>
          if aura.attachedTo == some o.id then
            acc +
              aura.staticAbilities.foldl
                (fun n ab =>
                  match ab with
                  | .enchantedCreatureGets _ t | .equippedCreatureGets _ t => n + t
                  | .otherCreaturesHaveTrample _ | .powerToughnessEqualLandsYouControl
                  | .cantBlockUnlessYouControl _ => n)
                (0 : Int)
          else acc)
        (0 : Int)
  let setByLands :=
    o.staticAbilities.any (fun ab =>
      match ab with
      | .powerToughnessEqualLandsYouControl => true
      | .otherCreaturesHaveTrample _ | .enchantedCreatureGets _ _
      | .equippedCreatureGets _ _ | .cantBlockUnlessYouControl _ => false)
  let base :=
    match o.status.setBaseToughness with
    | some n => n
    | none =>
      if o.isOnBattlefield && setByLands then
        match o.controller with
        | some p => Int.ofNat ((g.permanentsOf p).filter (·.printed.isLand) |>.size)
        | none => 0
      else
        o.printed.toughness.getD 0
  base + o.status.pumpToughness + (o.status.plusOnePlusOne : Int) + attached

/-- Dies triggers of a creature leaving the battlefield for a graveyard
(CR 700.4 / 603.6c). -/
def dyingTriggers (g : Game) (old : GameObject) (dest : Zone) : Array WaitingDeathTrigger :=
  if old.zone == .battlefield && old.isCreature then
    match dest, old.controller with
    | .graveyard _, some p =>
      old.printed.triggeredAbilities.filterMap (fun ab =>
        if ab.triggersWhenDying then
          some {
            controller := p
            source := old
            ability := ab
            lastKnownPower := g.snapshotPower old
          }
        else (none : Option WaitingDeathTrigger))
    | _, _ => (#[] : Array WaitingDeathTrigger)
  else (#[] : Array WaitingDeathTrigger)

def move (g : Game) (id : ObjectId) (dest : Zone) (controller : Option PlayerId := none) :
    Game × ObjectId :=
  let old := g.object! id
  let dying := g.dyingTriggers old dest
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
  let g : Game :=
    { g with objects := g.objects.filter (fun (o : GameObject) => o.id != id) |>.push fresh }
  let g :=
    match dest with
    | .library p => g.modifyPlayer p (fun pl => { pl with library := pl.library.push newId })
    | .hand p => g.modifyPlayer p (fun pl => { pl with hand := pl.hand.push newId })
    | .graveyard p => g.modifyPlayer p (fun pl => { pl with graveyard := pl.graveyard.push newId })
    | _ => g
  let g := { g with waitingDeathTriggers := g.waitingDeathTriggers ++ dying }
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
  o.isOnBattlefield && o.isCreature &&
  o.controlledBy g.activePlayer &&
  !o.status.tapped && !o.printed.keywords.defender &&
  (!o.status.summoningSick || o.printed.keywords.haste)

/-- Whether `p` currently controls a permanent with any of these subtypes. -/
def controlsAnySubtype (g : Game) (p : PlayerId) (subtypes : Array String) : Bool :=
  (g.permanentsOf p).any (fun o => subtypes.any o.hasSubtype)

/-- Whether `blocker`'s static abilities currently allow it to be declared as
a blocker (CR 509.1b). Checked only when declaring blockers. -/
def mayDeclareAsBlocker (g : Game) (blocker : GameObject) : Bool :=
  blocker.staticAbilities.all (fun ab =>
    match ab with
    | .cantBlockUnlessYouControl subtypes =>
      match blocker.controller with
      | none => false
      | some p => g.controlsAnySubtype p subtypes
    | .otherCreaturesHaveTrample _ | .enchantedCreatureGets _ _
    | .equippedCreatureGets _ _ | .powerToughnessEqualLandsYouControl => true)

/-- Whether `o` has flying, printed or granted (CR 702.9). -/
def hasFlying (_g : Game) (o : GameObject) : Bool :=
  o.printed.keywords.flying

def canBlock (g : Game) (blocker attacker : GameObject) : Bool :=
  let defender := g.opponent g.activePlayer
  blocker.isOnBattlefield && blocker.isCreature &&
  blocker.controlledBy defender && !blocker.status.tapped &&
  blocker.status.blocking.isEmpty &&
  g.mayDeclareAsBlocker blocker &&
  attacker.status.attacking &&
  (!g.hasFlying attacker ||
    g.hasFlying blocker || blocker.printed.keywords.reach)

/-- Whether `src` currently grants trample to `target` (CR 604.2). -/
def grantsTrampleTo (src target : GameObject) : Bool :=
  src.id != target.id &&
  src.isOnBattlefield &&
  target.isOnBattlefield &&
  src.controller == target.controller &&
  src.controller.isSome &&
  target.isCreature &&
  src.staticAbilities.any (fun ab =>
    match ab with
    | .otherCreaturesHaveTrample subtypes =>
      subtypes.any target.hasSubtype
    | .enchantedCreatureGets _ _ | .equippedCreatureGets _ _
    | .powerToughnessEqualLandsYouControl | .cantBlockUnlessYouControl _ => false)

/-- Whether `o` has hexproof, printed or granted until end of turn (CR 702.11). -/
def hasHexproof (_g : Game) (o : GameObject) : Bool :=
  o.printed.keywords.hexproof ||
  (o.isOnBattlefield && o.status.untilEotHexproof)

/-- Whether `o` has trample, printed, granted until end of turn, or granted by
a static ability (CR 702.19, 604.2). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  o.printed.keywords.trample ||
  (o.isOnBattlefield && o.status.untilEotTrample) ||
  (o.isOnBattlefield && g.battlefield.any (fun src => grantsTrampleTo src o))

/-- Keywords including those granted by static abilities and until-EOT effects. -/
def effectiveKeywords (g : Game) (o : GameObject) : Keywords :=
  { o.printed.keywords with
    flying := g.hasFlying o
    hexproof := g.hasHexproof o
    trample := g.hasTrample o }

/-- Continuous +P/+T this Aura or Equipment currently grants its host (CR 613.3c). -/
def auraStatBonus (aura : GameObject) : Int × Int :=
  aura.staticAbilities.foldl
    (fun acc ab =>
      match ab with
      | .enchantedCreatureGets p t | .equippedCreatureGets p t => (acc.1 + p, acc.2 + t)
      | .otherCreaturesHaveTrample _ | .powerToughnessEqualLandsYouControl
      | .cantBlockUnlessYouControl _ => acc)
    (0, 0)

/-- Lands `p` currently controls (CR 305.1). -/
def landsYouControl (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (·.printed.isLand) |>.size

/-- Whether `o` currently has a “P/T equal to lands you control” ability. -/
def hasLandsYouControlPT (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any (fun ab =>
    match ab with
    | .powerToughnessEqualLandsYouControl => true
    | .otherCreaturesHaveTrample _ | .enchantedCreatureGets _ _
    | .equippedCreatureGets _ _ | .cantBlockUnlessYouControl _ => false)

/-- Characteristic power before pumps, counters, and attached bonuses: an
until-EOT layer-7b set, else lands you control when that CDA applies, else
printed power (CR 208.2a / 613.3). -/
def basePower (g : Game) (o : GameObject) : Int :=
  if o.isOnBattlefield then
    match o.status.setBasePower with
    | some n => n
    | none =>
      if g.hasLandsYouControlPT o then
        match o.controller with
        | some p => Int.ofNat (g.landsYouControl p)
        | none => 0
      else
        o.printed.power.getD 0
  else
    o.printed.power.getD 0

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def baseToughness (g : Game) (o : GameObject) : Int :=
  if o.isOnBattlefield then
    match o.status.setBaseToughness with
    | some n => n
    | none =>
      if g.hasLandsYouControlPT o then
        match o.controller with
        | some p => Int.ofNat (g.landsYouControl p)
        | none => 0
      else
        o.printed.toughness.getD 0
  else
    o.printed.toughness.getD 0

/-- Static power/toughness from Auras and Equipment attached to `o`. -/
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

/-- Current power, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, and attached bonuses (CR 208.2). -/
def power (g : Game) (o : GameObject) : Int :=
  g.basePower o + o.status.pumpPower + (o.status.plusOnePlusOne : Int) +
    (g.attachedStatBonus o).1

/-- Current toughness, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, and attached bonuses (CR 208.2). -/
def toughness (g : Game) (o : GameObject) : Int :=
  g.baseToughness o + o.status.pumpToughness + (o.status.plusOnePlusOne : Int) +
    (g.attachedStatBonus o).2

/-- Greatest power among creatures `p` controls; `0` if they control none. -/
def greatestPowerAmongCreatures (g : Game) (p : PlayerId) : Int :=
  let creatures := g.permanentsOf p |>.filter (·.isCreature)
  if creatures.isEmpty then 0
  else creatures.foldl (fun acc o => max acc (g.power o)) (g.power creatures[0]!)

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

/-- Combat damage already assigned to `id` in `asgns`. -/
def damageAssignedTo (asgns : Array CreatureCombatAssignment) (id : ObjectId) : Int :=
  asgns.foldl
    (fun acc a =>
      acc + a.toCreatures.foldl (fun n (tid, amt) => if tid == id then n + amt else n) 0)
    0

/-- Remaining lethal for trample (CR 702.19b): toughness minus marked damage
and damage already assigned this step. -/
def lethalRemaining (g : Game) (o : GameObject) (already : Array CreatureCombatAssignment) :
    Int :=
  max (g.toughness o - o.status.damage - damageAssignedTo already o.id) 0

/-- Creatures that assign combat damage in the current half of CR 510.1. -/
def creaturesAssigningCombatDamage (g : Game) (forAttackers : Bool) : Array GameObject :=
  if forAttackers then
    g.battlefield.filter (·.status.attacking)
  else
    g.battlefield.filter (fun o => !o.status.blocking.isEmpty)

/-- Legal creature recipients for `source`'s combat damage (CR 510.1c–d). -/
def legalCombatDamageRecipients (g : Game) (source : GameObject) (forAttackers : Bool) :
    Array GameObject :=
  if forAttackers then g.blockersOf source.id else g.creaturesBlockedBy source

/-- True when a creature this player controls has two or more creature
recipients, so the controller must divide combat damage (CR 510.1c–d). -/
def needsCombatDamageChoice (g : Game) (forAttackers : Bool) : Bool :=
  (g.creaturesAssigningCombatDamage forAttackers).any (fun o =>
    (g.legalCombatDamageRecipients o forAttackers).size ≥ 2 && max (g.power o) 0 > 0)

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
        if o.isCreature then
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
      -- Unattached or illegally attached Auras (CR 704.5m).
      for o in g.battlefield do
        if o.printed.isAura then
          let legal :=
            match o.attachedTo.bind g.findObject? with
            | some host => host.isOnBattlefield && host.isCreature
            | none => false
          if !legal then
            g := g.logMsg s!"{o.name} is put into its owner's graveyard (CR 704.5n)"
            let (g', _) := g.move o.id (.graveyard o.owner) none
            g := g'
            changed := true
      -- Illegally attached Equipment (CR 704.5n). Unattached Equipment stays.
      for o in g.battlefield do
        if o.printed.isEquipment then
          let legal :=
            match o.attachedTo.bind g.findObject? with
            | some host => host.isOnBattlefield && host.printed.isCreature
            | none => true
          if !legal then
            g := g.setObject { o with attachedTo := none }
            g := g.logMsg s!"{o.name} becomes unattached (CR 704.5n)"
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
Attack, becomes-blocked, enters, and cast triggers are put on the stack as
their events happen (CR 508.2, 509.5c, 603.6a, 601.2i). Dies triggers wait
until a player would receive priority (CR 603.3 / 700.4). -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingDeathTriggers.isEmpty

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

def asSorcery? (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.stack.isEmpty &&
  g.step.isMainPhase && g.activePlayer == p && g.priority == p

def hasPriority (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.priority == p && g.playersReceivePriority

/-- Lands remaining this turn (CR 305.3 / 116.2a). -/
def canPlayLand (g : Game) (p : PlayerId) : Bool :=
  g.asSorcery? p && (g.player p).landsPlayedThisTurn == 0

/-- Whether `p` may play `o` from exile under a granted permission (CR 701.14 / 715.3d). -/
def mayPlayFromExile (_g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
  match o.playPermission with
  | some perm =>
    perm.player == p && (perm.fromAdventure || perm.turnEndsRemaining > 0)
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

/-- Whether `caster` may target `o` (CR 115.1, 702.11b). -/
def canBeTargetedBy (g : Game) (caster : PlayerId) (o : GameObject) : Bool :=
  !g.hasHexproof o || o.controlledBy caster

/-- Battlefield creatures matching `pred` that `caster` may target. -/
def legalCreatureTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  g.battlefield.filter (fun o =>
    o.isCreature && pred o && g.canBeTargetedBy caster o)
  |>.map (fun o => Target.permanent o.id)

/-- Legal targets for a triggered ability (CR 603.3d / 601.2c). `sourceId` is
the object that generated the ability, used to exclude “another” creature. -/
def legalTriggerTargets (g : Game) (p : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none) : Array Target :=
  match ab with
  | .onLandYouControlEntersPlusOnePlusOne =>
    g.legalCreatureTargets p (fun o => o.controlledBy p)
  | .onAttackSetOtherBasePT | .onAttackOtherGets2AndTrample =>
    g.legalCreatureTargets p (fun o => o.controlledBy p && some o.id != sourceId)
  | .onEnterDealDividedDamage _ _ | .onEnterOrAttackDealDividedDamage _ _ =>
    g.livingPlayers.map (fun pl => Target.player pl.id) ++
      g.legalCreatureTargets p (fun _ => true)
  | .onDiesDealDamageEqualToPowerToOppCreature =>
    g.legalCreatureTargets p (fun o => o.controlledBy (g.opponent p))
  | .onAttackPumpByGreatestPower | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _
  | .onEnterMayDiscardDraw _ | .onCastInstantOrSorceryDealDamageToEachOpponent _ =>
    #[]

/-- Damage already assigned on a “divided as you choose” stack entry (CR 601.2d). -/
def assignedDividedDamage (e : StackEntry) : Nat :=
  e.dividedDamage.foldl (· + ·) 0

/-- Whether this stacked triggered ability still needs targets or a damage
division announced (CR 603.3d / 601.2d). -/
def triggerStillNeedsTargets (e : StackEntry) : TriggeredAbility → Bool
  | .onEnterDealDividedDamage amount _ | .onEnterOrAttackDealDividedDamage amount _ =>
    assignedDividedDamage e < amount
  | .onAttackSetOtherBasePT =>
    !e.targetsAnnounced
  | ab => ab.requiresTarget && e.targets.isEmpty

/-- Stack entry for a triggered ability that still needs targets announced
(CR 603.3d). Oldest first so targets are chosen in the order abilities were
put on the stack. -/
def triggerNeedingTargets (g : Game) : Option StackEntry :=
  g.stack.find? (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      match o.triggeredAbility with
      | some ab => triggerStillNeedsTargets e ab
      | none => false
    | none => false)

/-- Put a triggered ability of `source` onto the stack (CR 603.3). -/
def putTriggeredAbilityOnStack (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
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
    lastKnownPower := lastKnownPower
    lastKnownToughness := lastKnownToughness
  }
  let entry : StackEntry := { objectId := newId, controller := controller, targets := #[] }
  let g := { g with
    objects := g.objects.push abilityObj
    stack := g.stack.push entry
    consecutivePasses := 0 }
  g.logMsg s!"{source.name}'s {event} is put on the stack"

/-- If a stacked triggered ability still needs targets, prompt its controller
(CR 603.3d / 601.2c). -/
def promptTriggerTargetsIfNeeded (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some e =>
    if g.pending == .chooseTargets e.controller then g
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

/-- Put queued dies triggers onto the stack (CR 603.3 / 700.4). Abilities that
require a target and have none are removed (CR 603.3d). -/
def putWaitingDeathTriggers (g : Game) : Game :=
  if g.waitingDeathTriggers.isEmpty then g
  else
    Id.run do
      let waiting := g.waitingDeathTriggers
      let mut g := { g with waitingDeathTriggers := #[] }
      for wt in waiting do
        if wt.ability.requiresTarget && !wt.ability.allowsZeroTargets &&
            (g.legalTriggerTargets wt.controller wt.ability (some wt.source.id)).isEmpty then
          g := g.logMsg
            s!"{wt.source.name}'s dies trigger is removed from the stack (no legal target) (CR 603.3d)"
        else
          g := g.putTriggeredAbilityOnStack wt.controller wt.source wt.ability "dies trigger"
            (some wt.lastKnownPower)
      return g.promptTriggerTargetsIfNeeded

def receivePriority (g : Game) (p : PlayerId) : Game :=
  let g := g.checkSBA
  if g.over then g
  else
    let g := g.putWaitingDeathTriggers
    if g.over || g.pending != .none then g
    else { g with priority := p, consecutivePasses := 0 }

/-- Put enters-the-battlefield triggers of `o` onto the stack (CR 603.6a).
Abilities that require a target and have none are removed (CR 603.3d). -/
def putEnterTriggersOnStack (g : Game) (o : GameObject) : Game :=
  match o.controller with
  | none => g
  | some p =>
    Id.run do
      let mut g := g
      for ab in o.printed.triggeredAbilities do
        if ab.triggersWhenEntering then
          if ab.requiresTarget && !ab.allowsZeroTargets &&
              (g.legalTriggerTargets p ab (some o.id)).isEmpty then
            g := g.logMsg
              s!"{o.name}'s enters trigger is removed from the stack (no legal target) (CR 603.3d)"
          else
            g := g.putTriggeredAbilityOnStack p o ab "enters trigger"
      return g.promptTriggerTargetsIfNeeded

/-- Put “whenever a land you control enters” triggers onto the stack (CR 603.6a).
Abilities that require a target and have none are removed (CR 603.3d). -/
def putLandYouControlEntersTriggers (g : Game) (land : GameObject) : Game :=
  if !land.printed.isLand then g
  else
    match land.controller with
    | none => g
    | some landController =>
      Id.run do
        let mut g := g
        for o in g.battlefield do
          if o.controlledBy landController then
            for ab in o.printed.triggeredAbilities do
              if ab.triggersWhenLandYouControlEnters then
                if ab.requiresTarget && !ab.allowsZeroTargets &&
                    (g.legalTriggerTargets landController ab (some o.id)).isEmpty then
                  g := g.logMsg
                    s!"{o.name}'s landfall trigger is removed from the stack (no legal target) (CR 603.3d)"
                else
                  g := g.putTriggeredAbilityOnStack landController o ab "landfall trigger"
        return g.promptTriggerTargetsIfNeeded

/-- Put “whenever you cast an instant or sorcery” triggers onto the stack
(CR 601.2i / 603.3). -/
def putCastTriggersOnStack (g : Game) (caster : PlayerId) (spell : GameObject) : Game :=
  if !spell.printed.isInstantOrSorcery then g
  else
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.controlledBy caster then
          for ab in o.printed.triggeredAbilities do
            if ab.triggersWhenYouCastInstantOrSorcery then
              g := g.putTriggeredAbilityOnStack caster o ab "cast trigger"
      return g

/-- After a land enters, put its enters triggers and landfall triggers. -/
def afterLandEnters (g : Game) (land : GameObject) : Game :=
  let g := g.putEnterTriggersOnStack land
  g.putLandYouControlEntersTriggers (g.object! land.id)

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
  let g := g.afterLandEnters (g.object! newId)
  if g.pending != .none then
    return g
  return g.receivePriority p

def manaSources (g : Game) (p : PlayerId) : Array (GameObject × Array ManaType) :=
  g.permanentsOf p |>.filterMap (fun o =>
    let types := o.printed.manaAbilities
    if types.isEmpty || o.status.tapped then none
    else if o.isCreature && o.status.summoningSick && !o.printed.keywords.haste then none
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
  if o.isCreature && o.status.summoningSick && !o.printed.keywords.haste then
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

def legalTargets (g : Game) (caster : PlayerId) (effect : SpellEffect) : Array Target :=
  match effect with
  | .dealDamage _ =>
    let players := g.livingPlayers.map (fun pl => Target.player pl.id)
    players ++ g.legalCreatureTargets caster (fun _ => true)
  | .dealDamageToCreature _ =>
    g.legalCreatureTargets caster (fun _ => true)
  | .pump _ _ =>
    g.legalCreatureTargets caster (fun _ => true)
  | .destroyCreatureWithFlying =>
    g.legalCreatureTargets caster (fun o => g.hasFlying o)
  | .plusOnePlusOneTrampleHexproof =>
    g.legalCreatureTargets caster (fun o => o.controlledBy caster)

/-- Legal targets for an Aura spell with “Enchant creature” (CR 303.4). -/
def legalAuraTargets (g : Game) (caster : PlayerId) : Array Target :=
  g.legalCreatureTargets caster (fun _ => true)

/-- Chosen mode of `o` if it is a modal spell on the stack (CR 700.2). -/
def chosenModeOf (g : Game) (o : GameObject) : Option Nat :=
  match g.stack.find? (fun e => e.objectId == o.id) with
  | some e => e.chosenMode
  | none => none

/-- Spell effect after a modal choice, if one has been announced (CR 700.2). -/
def currentSpellEffect (g : Game) (o : GameObject) : Option SpellEffect :=
  if o.printed.isModal then
    match g.chosenModeOf o with
    | some i => o.printed.spellModes[i]?
    | none => none
  else
    o.printed.spellEffect

/-- Legal targets for beginning to cast `o`, or for the chosen mode (CR 115.1, 303.4, 601.2c). -/
def legalSpellTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  if o.printed.isModal && (g.chosenModeOf o).isNone then
    o.printed.spellModes.foldl (fun acc e => acc ++ g.legalTargets p e) #[]
  else
    match g.currentSpellEffect o with
    | some e => g.legalTargets p e
    | none => if o.printed.isAura then g.legalAuraTargets p else #[]

/-- Legal mode indices for a modal spell (CR 700.2d). -/
def legalModes (g : Game) (p : PlayerId) (o : GameObject) : Array Nat :=
  if !o.printed.isModal then #[]
  else
    Id.run do
      let mut acc : Array Nat := #[]
      for i in [0:o.printed.spellModes.size] do
        if !(g.legalTargets p o.printed.spellModes[i]!).isEmpty then
          acc := acc.push i
      return acc

/-- Default mode: destroy an opponent's flyer if that mode is legal, else the
first legal mode. -/
def defaultMode (g : Game) (p : PlayerId) (spell : GameObject) : Option Nat :=
  let legal := g.legalModes p spell
  let destroyIdx := legal.find? (fun i =>
    match spell.printed.spellModes[i]? with
    | some .destroyCreatureWithFlying => true
    | _ => false)
  match destroyIdx with
  | some i => some i
  | none => legal[0]?

/-- Legal targets for an activated-ability effect (CR 115.1 / 601.2c / 702.11b). -/
def legalAbilityTargets (g : Game) (p : PlayerId) : AbilityEffect → Array Target
  | .dealDamageToTargetCreature _ =>
    g.legalCreatureTargets p (fun _ => true)
  | .destroyTargetColorlessNonland =>
    g.battlefield.filter (fun o => o.isColorlessNonland && g.canBeTargetedBy p o)
      |>.map (fun o => Target.permanent o.id)
  | .attachToTargetCreatureYouControl =>
    g.legalCreatureTargets p (fun o => o.controlledBy p)
  | .searchBasicLandTapped | .exileTopPlayUntilEndOfNextTurn
  | .becomeBearCreatureWithLandsPT | .sourceGets _ _ | .putPlusOnePlusOneOnSource _ => #[]

/-- The spell, activated ability, or triggered ability currently waiting for
targets (CR 601.2c / 603.3d). -/
def objectAwaitingTargets (g : Game) : Option GameObject :=
  match g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some o => some o
  | none => g.triggerNeedingTargets.bind (fun e => g.findObject? e.objectId)

/-- True while announcing a “divided as you choose” damage trigger (CR 601.2d). -/
def announcingDividedDamage (g : Game) : Bool :=
  match g.objectAwaitingTargets with
  | some o => (o.triggeredAbility.bind TriggeredAbility.dividedDamage?).isSome
  | none => false

/-- The stack entry for `objectId`, if that object is on the stack. -/
def stackEntry? (g : Game) (objectId : ObjectId) : Option StackEntry :=
  g.stack.find? (fun e => e.objectId == objectId)

/-- Legal targets for the object currently being announced (spell or ability).
Already-chosen targets of a divided-damage trigger are excluded (CR 115.3). -/
def legalProposedTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  let raw :=
    match o.abilityEffect with
    | some e => g.legalAbilityTargets p e
    | none =>
      match o.triggeredAbility with
      | some t => g.legalTriggerTargets p t o.sourceId
      | none => g.legalSpellTargets p o
  match o.triggeredAbility.bind TriggeredAbility.dividedDamage?, g.stackEntry? o.id with
  | some _, some e =>
    raw.filter (fun t => !e.targets.contains t)
  | _, _ => raw

/-- Whether `e` currently has a legal target, or does not require one. -/
def modeIsChoosable (g : Game) (p : PlayerId) (e : AbilityEffect) : Bool :=
  !e.requiresTarget || !(g.legalAbilityTargets p e).isEmpty

/-- Default object or player to announce as a target (CR 601.2c). Damage spells
and divided-damage enters or attack triggers prefer the opponent; creature-damage abilities
and dies triggers prefer an opposing creature; destroy-flying prefers an opponent's flyer;
destroy-colorless prefers an opposing colorless nonland; pumps, the +1/+1-counter
mode, Equip, landfall, Galion's and Oliphaunt's attack triggers, and Auras prefer a creature the
caster controls. -/
def defaultTarget (g : Game) (p : PlayerId) (obj : GameObject) : Option Target :=
  let legal := g.legalProposedTargets p obj
  let preferred : Option Target :=
    match obj.triggeredAbility, obj.abilityEffect, g.currentSpellEffect obj with
    | some (.onEnterDealDividedDamage _ _), _, _
    | some (.onEnterOrAttackDealDividedDamage _ _), _, _ =>
      some (Target.player (g.opponent p))
    | some .onDiesDealDamageEqualToPowerToOppCreature, _, _ =>
      (g.permanentsOf (g.opponent p)).filter (fun o =>
        o.isCreature && g.canBeTargetedBy p o)
      |>.back?.map (fun c => Target.permanent c.id)
    | some .onAttackSetOtherBasePT, _, _
    | some .onAttackOtherGets2AndTrample, _, _ =>
      (g.permanentsOf p).filter (fun o =>
        o.isCreature && some o.id != obj.sourceId)
      |>.back?.map (fun c => Target.permanent c.id)
    | _, some (.dealDamageToTargetCreature _), _ =>
      (g.permanentsOf (g.opponent p)).filter (fun o =>
        o.isCreature && g.canBeTargetedBy p o)
      |>.back?.map (fun c => Target.permanent c.id)
    | _, some .destroyTargetColorlessNonland, _ =>
      (g.permanentsOf (g.opponent p)).filter (fun o =>
        o.isColorlessNonland && g.canBeTargetedBy p o)
      |>.back?.map (fun c => Target.permanent c.id)
    | _, some .attachToTargetCreatureYouControl, _ =>
      (g.permanentsOf p).filter (·.printed.isCreature) |>.back?
        |>.map (fun c => Target.permanent c.id)
    | _, _, some (.dealDamage _) => some (Target.player (g.opponent p))
    | _, _, some (.dealDamageToCreature _) =>
      (g.permanentsOf (g.opponent p)).filter (fun o =>
        o.isCreature && g.canBeTargetedBy p o)
      |>.back?.map (fun c => Target.permanent c.id)
    | _, _, some .destroyCreatureWithFlying =>
      (g.permanentsOf (g.opponent p)).filter (fun o =>
        o.isCreature && g.hasFlying o && g.canBeTargetedBy p o)
      |>.back?.map (fun c => Target.permanent c.id)
    | _, _, some (.pump _ _) | _, _, some .plusOnePlusOneTrampleHexproof | _, _, none =>
      (g.permanentsOf p).filter (·.isCreature) |>.back?
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
    (g.permanentsOf (g.opponent p)).any (·.isCreature)
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
pool is not required; mana abilities are activated at CR 601.2g. Additional
non-mana costs such as sacrificing a permanent must still be payable. -/
def canCast (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  !o.printed.isLand &&
  g.mayPlay p o &&
  g.hasPriority p &&
  (if o.printed.hasSorcerySpeed then g.asSorcery? p else true) &&
  (if o.printed.additionalCostSacrificeArtifactOrCreature then
    (g.permanentsOf p).any (fun perm =>
      perm.id != o.id && (perm.isCreature || perm.printed.isArtifact))
   else true) &&
  if o.printed.requiresTarget then !(g.legalSpellTargets p o |>.isEmpty)
  else o.printed.isPermanentCard

/-- True when the CR 715.3d exile permission forbids recasting as an Adventure. -/
def adventureExileForbidsRecast (_g : Game) (o : GameObject) : Bool :=
  match o.playPermission with
  | some perm => perm.fromAdventure
  | none => false

/-- Legal targets for beginning to cast card `c` (from hand or as an Adventure). -/
def legalCastTargets (g : Game) (p : PlayerId) (c : CardDef) : Array Target :=
  if c.isModal then
    c.spellModes.foldl (fun acc e => acc ++ g.legalTargets p e) #[]
  else
    match c.spellEffect with
    | some e => g.legalTargets p e
    | none => if c.isAura then g.legalAuraTargets p else #[]

/-- Whether `p` may begin to cast `o` as an Adventure (CR 715.3). -/
def canCastAdventure (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  match o.printed.adventure with
  | none => false
  | some adv =>
    let face := adv.toCardDef
    !g.adventureExileForbidsRecast o &&
    g.mayPlay p o &&
    g.hasPriority p &&
    (if face.hasSorcerySpeed then g.asSorcery? p else true) &&
    if face.requiresTarget then !(g.legalCastTargets p face).isEmpty
    else true

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

def becomeCast (g : Game) (p : PlayerId) (spell : GameObject) : Game :=
  let g := g.logMsg s!"{(g.player p).name} casts {spell.name}"
  let g := g.putCastTriggersOnStack p spell
  g.receivePriority p

/-- Continue after CR 601.2c: activate mana abilities (601.2g) or finish casting. -/
def afterTargetsChosen (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    if prop.cost.includesManaPayment || prop.needsSacrificeOther then
      { g with pending := .activateManaAbilities prop.caster }
        |>.logMsg s!"{(g.player prop.caster).name} may activate mana abilities (CR 601.2g)"
    else
      let spell := g.object! prop.spellId
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      g.becomeCast prop.caster spell

/-- Write `targets` (and optional damage division) onto the stack entry. -/
def setStackEntryTargets (g : Game) (objectId : ObjectId) (targets : Array Target)
    (dividedDamage : Array Nat := #[]) : Game :=
  match g.stack.findIdx? (fun e => e.objectId == objectId) with
  | none => g
  | some i =>
    { g with stack := g.stack.set! i { g.stack[i]! with
        targets := targets, dividedDamage := dividedDamage, targetsAnnounced := true } }

/-- Write `targets` onto the stack entry for the proposed spell. -/
def setProposedTargets (g : Game) (targets : Array Target) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop => g.setStackEntryTargets prop.spellId targets

/-- Record the chosen mode on the proposed spell's stack entry (CR 700.2). -/
def setProposedMode (g : Game) (mode : Nat) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    match g.stack.findIdx? (fun e => e.objectId == prop.spellId) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with chosenMode := some mode } }

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
    o.id != sourceId && (o.isCreature || o.printed.isArtifact))

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

/-- Pay the locked-in cost (CR 601.2h / 602.2b). Spells and abilities that still
need an artifact or creature sacrificed wait for the `sacrifice` action. -/
def finishProposedSpell (g : Game) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell or ability is waiting to be paid for"
  if !(g.player prop.caster).manaPool.canPay prop.cost || !g.sourceStillPayable prop then
    return g.reverseProposedSpell
  if prop.needsSacrificeOther then
    let excludeId := prop.sourceId.getD prop.spellId
    if (g.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
      return g.reverseProposedSpell
  let g ← g.payCost prop.caster prop.cost
  let g ←
    match prop.kind, prop.sourceId with
    | .activatedAbility, some sid =>
      g.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
    | _, _ => pure g
  match prop.kind, prop.needsSacrificeOther, prop.sourceId with
  | .spell, true, _ =>
    let g := { g with
      pending := .sacrificePermanent prop.caster prop.spellId
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
  | .spell, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeCast prop.caster (g.object! prop.spellId)
  | .activatedAbility, true, some sid =>
    let g := { g with
      pending := .sacrificePermanent prop.caster sid
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice another creature or artifact"
  | .activatedAbility, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeActivated prop.caster prop.original.name prop.sourceId

def castSpell (g : Game) (p : PlayerId) (id : ObjectId) (asAdventure : Bool := false) :
    Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if asAdventure then
    if card.printed.adventure.isNone then
      throw s!"{card.name} has no Adventure"
    if g.adventureExileForbidsRecast card then
      throw "You may not cast that card as an Adventure this way (CR 715.3d)"
  let face :=
    match asAdventure, card.printed.adventure with
    | true, some adv => adv.toCardDef
    | _, _ => card.printed
  let pl := g.player p
  if face.isLand then
    throw "Lands are played, not cast (CR 305)"
  if face.hasSorcerySpeed && !g.asSorcery? p then
    throw s!"{face.name} has sorcery speed"
  if (face.requiresTarget || face.isModal) &&
      (g.legalCastTargets p face).isEmpty then
    throw s!"{face.name} requires a target"
  if face.additionalCostSacrificeArtifactOrCreature &&
      (g.sacrificeCreatureOrArtifactChoices p id).isEmpty then
    throw s!"{face.name} requires sacrificing an artifact or creature"
  -- CR 601.2a: propose the spell by moving it onto the stack. Modes are
  -- announced at CR 601.2b, targets at CR 601.2c; mana is not required yet
  -- (CR 601.2g). CR 715.3: an adventurer card may be cast as its Adventure.
  let cost := face.manaCost
  let original := card
  let handBefore := pl.hand
  let stackBefore := g.stack
  let manaBefore := pl.manaPool
  let (g, newId) := g.move id .stack (some p)
  let g :=
    if asAdventure then
      let o := g.object! newId
      g.setObject { o with printed := face, adventurerCard := some original.printed }
    else g
  let entry : StackEntry := { objectId := newId, controller := p, targets := #[] }
  let g := { g with stack := g.stack.push entry, consecutivePasses := 0 }
  let needsMode := face.isModal
  let needsTarget := face.requiresTarget && !needsMode
  let needsSacrifice := face.additionalCostSacrificeArtifactOrCreature
  if !needsMode && !needsTarget && !cost.includesManaPayment && !needsSacrifice then
    return g.becomeCast p (g.object! newId)
  let prop : ProposedSpell := {
    caster := p
    cost := cost
    spellId := newId
    original := original
    handBefore := handBefore
    stackBefore := stackBefore
    manaBefore := manaBefore
    needsSacrificeOther := needsSacrifice
  }
  let g := g.logMsg s!"{pl.name} begins casting {face.name}"
  if needsMode then
    let g := { g with pending := .chooseMode p, proposedSpell := some prop }
    return g.logMsg s!"{pl.name} must choose a mode (CR 601.2b / 700.2)"
  if needsTarget then
    let g := { g with pending := .chooseTargets p, proposedSpell := some prop }
    return g.logMsg s!"{pl.name} must choose a target (CR 601.2c)"
  let g := { g with pending := .activateManaAbilities p, proposedSpell := some prop }
  return g.logMsg s!"{pl.name} may activate mana abilities (CR 601.2g)"

/-- Announce the chosen mode for a modal spell or activated ability
(CR 601.2b / 700.2). -/
def announceMode (g : Game) (p : PlayerId) (mode : Nat) : Except String Game := do
  match g.pending with
  | .chooseMode caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a mode (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell or ability is waiting for a mode (CR 601.2b)"
    match prop.kind with
    | .activatedAbility =>
      let some chosen := prop.abilityModes[mode]?
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
    | .spell =>
      let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
      if !spell.printed.isModal then
        throw "That spell is not modal (CR 700.2)"
      let some effect := spell.printed.spellModes[mode]? | throw "No such mode (CR 700.2)"
      if (g.legalTargets p effect).isEmpty then
        throw "That mode has no legal target (CR 700.2d)"
      let g := g.setProposedMode mode
      let g := g.logMsg
        s!"{(g.player p).name} chooses mode {mode + 1} ({effect.toNotation}) (CR 601.2b)"
      let g := { g with pending := .chooseTargets p }
      return g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
  | _ => throw "Not time to choose a mode (CR 601.2b)"

/-- After a trigger's targets (and any damage division) are fully announced,
prompt the next trigger that needs targets or give priority. -/
def afterTriggerTargetsChosen (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some _ =>
    promptTriggerTargetsIfNeeded { g with pending := .none }
  | none =>
    receivePriority { g with pending := .none } g.activePlayer

/-- Announce the chosen target for a proposed spell or a triggered ability
(CR 601.2c / 603.3d). `amount?` is the damage assigned to this target of a
divided-damage ability; omitted means all remaining damage (CR 601.2d). -/
def announceTarget (g : Game) (p : PlayerId) (t : Target) (amount? : Option Nat := none) :
    Except String Game := do
  match g.pending with
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    if !(g.legalProposedTargets p obj).contains t then
      throw "Illegal target (CR 601.2c)"
    match obj.triggeredAbility.bind TriggeredAbility.dividedDamage? with
    | some (total, maxTargets) =>
      let some e := g.stackEntry? obj.id | throw "The ability left the stack"
      let already := assignedDividedDamage e
      let remaining := total - already
      if remaining == 0 then
        throw "All damage has already been divided (CR 601.2d)"
      let n := amount?.getD remaining
      if n == 0 then
        throw "Each target must be dealt at least 1 damage (CR 601.2d)"
      if n > remaining then
        throw s!"Only {remaining} damage remains to divide (CR 601.2d)"
      let used := e.targets.size + 1
      if used > maxTargets then
        throw s!"Cannot choose more than {maxTargets} targets (CR 601.2d)"
      let leftover := remaining - n
      if leftover > 0 && used == maxTargets then
        throw
          s!"Must assign all remaining damage among at most {maxTargets} targets (CR 601.2d)"
      let g := g.setStackEntryTargets obj.id (e.targets.push t) (e.dividedDamage.push n)
      let g := g.logMsg
        s!"{(g.player p).name} chooses {g.targetLogName t} to be dealt {n} damage (CR 601.2d)"
      if leftover == 0 then
        return g.afterTriggerTargetsChosen
      return { g with pending := .chooseTargets p }
    | none =>
      if amount?.isSome then
        throw "That spell or ability does not divide damage (CR 601.2d)"
      let g := g.setStackEntryTargets obj.id #[t]
      let g := g.logMsg
        s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
      if g.proposedSpell.isSome then
        return g.afterTargetsChosen
      return g.afterTriggerTargetsChosen
  | _ => throw "Not time to choose targets (CR 601.2c)"

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
  if ab.cost.tap && o.isCreature && o.status.summoningSick && !o.printed.keywords.haste then
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

/-- After mana is paid, sacrifice an artifact or creature (CR 601.2h / 602.2b). -/
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
    match g.proposedSpell with
    | some prop =>
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      match prop.kind with
      | .spell => return g.becomeCast prop.caster (g.object! prop.spellId)
      | .activatedAbility =>
        return g.becomeActivated p prop.original.name prop.sourceId
    | none =>
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      return g.becomeActivated p (g.object! sourceId).name (some sourceId)
  | _ => throw "Not time to sacrifice a permanent"

def applyEffect (g : Game) (controller : PlayerId) (effect : SpellEffect)
    (targets : Array Target) : Game :=
  let illegal : Game := g.logMsg "The target is illegal"
  match effect, targets[0]? with
  | .dealDamage n, some (Target.player pid) =>
    if !(g.legalTargets controller (.dealDamage n)).contains (Target.player pid) then
      illegal
    else
      let pl := g.player pid
      let g := g.setPlayer { pl with life := pl.life - n }
      g.logMsg s!"{pl.name} is dealt {n} damage ({g.player pid |>.life} life)"
  | .dealDamage n, some (Target.permanent oid) =>
    match g.findObject? oid with
    | none => g.logMsg "The target is no longer in play"
    | some o =>
      if !(g.legalTargets controller (.dealDamage n)).contains (Target.permanent oid) then
        illegal
      else
        let g := g.setObject { o with status := { o.status with damage := o.status.damage + n } }
        g.logMsg s!"{o.name} is dealt {n} damage"
  | .pump pw tw, some (Target.permanent oid) =>
    match g.findObject? oid with
    | none => g.logMsg "The target is no longer in play"
    | some o =>
      if !(g.legalTargets controller (.pump pw tw)).contains (Target.permanent oid) then
        illegal
      else
        let g := g.setObject { o with
          status := { o.status with pumpPower := o.status.pumpPower + pw, pumpToughness := o.status.pumpToughness + tw } }
        g.logMsg s!"{o.name} gets +{pw}/+{tw} until end of turn"
  | .destroyCreatureWithFlying, some (Target.permanent oid) =>
    match g.findObject? oid with
    | none => g.logMsg "The target is no longer in play"
    | some o =>
      if !(g.legalTargets controller .destroyCreatureWithFlying).contains
          (Target.permanent oid) then
        illegal
      else
        let g := g.logMsg s!"{o.name} is destroyed"
        let (g, _) := g.move oid (.graveyard o.owner) none
        g
  | .plusOnePlusOneTrampleHexproof, some (Target.permanent oid) =>
    match g.findObject? oid with
    | none => g.logMsg "The target is no longer in play"
    | some o =>
      if !(g.legalTargets controller .plusOnePlusOneTrampleHexproof).contains
          (Target.permanent oid) then
        illegal
      else
        let g := g.setObject { o with
          status := { o.status with
            plusOnePlusOne := o.status.plusOnePlusOne + 1
            untilEotTrample := true
            untilEotHexproof := true } }
        g.logMsg
          s!"{o.name} gets a +1/+1 counter and gains trample and hexproof until end of turn"
  | .dealDamageToCreature n, some (Target.permanent oid) =>
    match g.findObject? oid with
    | none => g.logMsg "The target is no longer in play"
    | some o =>
      if !(g.legalTargets controller (.dealDamageToCreature n)).contains
          (Target.permanent oid) then
        illegal
      else
        let g := g.setObject { o with status := { o.status with damage := o.status.damage + n } }
        g.logMsg s!"{o.name} is dealt {n} damage"
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
      let g := g.logMsg s!"{pl.name} puts {landName} onto the battlefield tapped"
      g.afterLandEnters (g.object! newId)
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
    (targets : Array Target) (sourceId : Option ObjectId := none) : Game :=
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
  | .attachToTargetCreatureYouControl =>
    match targets[0]? with
    | none => g
    | some t =>
      if (g.legalAbilityTargets controller effect).contains t then
        match t, sourceId.bind g.findObject? with
        | Target.permanent hostId, some src =>
          if !src.isOnBattlefield then
            g.logMsg s!"{src.name} is no longer on the battlefield"
          else
            let host := g.object! hostId
            if src.attachedTo == some host.id then
              g.logMsg s!"{src.name} is already attached to {host.name}"
            else
              let (g, ts) := g.bumpTime
              let src := g.object! src.id
              let g := g.setObject { src with attachedTo := some host.id, timestamp := ts }
              g.logMsg s!"{src.name} attaches to {host.name}"
        | Target.permanent _, none =>
          g.logMsg "The Equipment is no longer in play"
        | Target.player _, _ => g.logMsg "The target is no longer legal"
      else
        g.illegalAbilityTarget t
  | .becomeBearCreatureWithLandsPT =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let subtypes :=
          if o.hasSubtype "Bear" then o.status.additionalSubtypes
          else o.status.additionalSubtypes.push "Bear"
        let granted :=
          if g.hasLandsYouControlPT o then o.status.grantedStaticAbilities
          else o.status.grantedStaticAbilities.push .powerToughnessEqualLandsYouControl
        let g := g.setObject { o with
          status := { o.status with
            additionalCreature := true
            additionalSubtypes := subtypes
            grantedStaticAbilities := granted } }
        g.logMsg
          s!"{o.name} becomes a Bear creature. Its power and toughness are each equal to the number of lands you control"
      else
        g.logMsg s!"{o.name} is no longer on the battlefield"
    | none =>
      g.logMsg "The ability's source is no longer in play"
  | .sourceGets pw tw =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let g := g.setObject { o with
          status := { o.status with
            pumpPower := o.status.pumpPower + pw
            pumpToughness := o.status.pumpToughness + tw } }
        g.logMsg s!"{o.name} gets +{pw}/+{tw} until end of turn"
      else
        g.logMsg s!"{o.name} is no longer on the battlefield"
    | none =>
      g.logMsg "The ability's source is no longer in play"
  | .putPlusOnePlusOneOnSource n =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let g := g.setObject { o with
          status := { o.status with
            plusOnePlusOne := o.status.plusOnePlusOne + n } }
        g.logMsg s!"{o.name} gets {AbilityEffect.plusOnePlusOneCountersPhrase n}"
      else
        g.logMsg s!"{o.name} is no longer on the battlefield"
    | none =>
      g.logMsg "The ability's source is no longer in play"

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

/-- Start an optional “discard a card. If you do, draw `n`” (CR 701.9 / 608.2d). -/
def beginMayDiscardDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  if pl.hand.isEmpty then
    g.logMsg s!"{pl.name} has no card to discard"
  else
    { g with pending := .mayDiscardDraw p n }.logMsg
      s!"{pl.name} may discard a card. If they do, they draw {n}"

/-- Resolve a triggered ability (CR 608). `sourceId` is the object that generated it. -/
def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (dividedDamage : Array Nat := #[]) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (sourceName : String := "This creature") : Game :=
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
  | .onAttackSetOtherBasePT =>
    match targets[0]? with
    | none =>
      g.logMsg "No target was chosen"
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer in play"
      | some o =>
        if (g.legalTriggerTargets controller ab sourceId).contains (Target.permanent oid) then
          let (pw, tw) :=
            match sourceId.bind g.findObject? with
            | some src =>
              if src.isOnBattlefield then (g.power src, g.toughness src)
              else (lastKnownPower.getD 0, lastKnownToughness.getD 0)
            | none => (lastKnownPower.getD 0, lastKnownToughness.getD 0)
          let g := g.setObject { o with
            status := { o.status with
              setBasePower := some pw
              setBaseToughness := some tw } }
          g.logMsg
            s!"{o.name}'s base power and toughness become {pw}/{tw} until end of turn"
        else if o.isOnBattlefield then
          g.logMsg "The target is no longer legal"
        else
          g.logMsg "The target is no longer in play"
    | some (Target.player _) =>
      g.logMsg "The target is no longer legal"
  | .onAttackOtherGets2AndTrample =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer in play"
      | some o =>
        if (g.legalTriggerTargets controller ab sourceId).contains (Target.permanent oid) then
          let g := g.setObject { o with
            status := { o.status with
              pumpPower := o.status.pumpPower + 2
              untilEotTrample := true } }
          g.logMsg s!"{o.name} gets +2/+0 and gains trample until end of turn"
        else if o.isOnBattlefield then
          g.logMsg "The target is no longer legal"
        else
          g.logMsg "The target is no longer in play"
    | _ => g.logMsg "The target is no longer legal"
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
  | .onEnterMayDiscardDraw n =>
    g.beginMayDiscardDraw controller n
  | .onLandYouControlEntersPlusOnePlusOne =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer in play"
      | some o =>
        if (g.legalTriggerTargets controller ab sourceId).contains (Target.permanent oid) then
          let g := g.setObject { o with
            status := { o.status with plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
          g.logMsg s!"{o.name} gets a +1/+1 counter"
        else if o.isOnBattlefield then
          g.logMsg "The target is no longer legal"
        else
          g.logMsg "The target is no longer in play"
    | _ => g.logMsg "The target is no longer legal"
  | .onEnterDealDividedDamage _ _ | .onEnterOrAttackDealDividedDamage _ _ =>
    Id.run do
      let mut g := g
      for i in [0:targets.size] do
        let t := targets[i]!
        let n := dividedDamage[i]?.getD 0
        if n > 0 then
          g := g.applyEffect controller (.dealDamage n) #[t]
      return g
  | .onDiesDealDamageEqualToPowerToOppCreature =>
    let n := (lastKnownPower.getD 0).toNat
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer in play"
      | some o =>
        if (g.legalTriggerTargets controller ab sourceId).contains (Target.permanent oid) then
          let g := g.setObject { o with
            status := { o.status with damage := o.status.damage + (n : Int) } }
          g.logMsg s!"{sourceName} deals {n} damage to {o.name}"
        else if o.isOnBattlefield then
          g.logMsg "The target is no longer legal"
        else
          g.logMsg "The target is no longer in play"
    | _ => g.logMsg "The target is no longer legal"
  | .onCastInstantOrSorceryDealDamageToEachOpponent n =>
    Id.run do
      let mut g := g
      for pl in g.livingPlayers do
        if pl.id != controller then
          g := g.applyEffect controller (.dealDamage n) #[Target.player pl.id]
      return g

/-- Put attack-triggered abilities of `attackerIds` onto the stack (CR 508.2). -/
def putAttackTriggersOnStack (g : Game) (p : PlayerId) (attackerIds : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for id in attackerIds do
      let o := g.object! id
      for ab in o.printed.triggeredAbilities do
        if ab.triggersWhenAttacking then
          if ab.requiresTarget && !ab.allowsZeroTargets &&
              (g.legalTriggerTargets p ab (some o.id)).isEmpty then
            g := g.logMsg
              s!"{o.name}'s attack trigger is removed from the stack (no legal target) (CR 603.3d)"
          else
            g := g.putTriggeredAbilityOnStack p o ab "attack trigger"
              (some (g.snapshotPower o)) (some (g.snapshotToughness o))
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

/-- Whether `host` is a legal Enchant-creature attachment (CR 303.4). -/
def isLegalAuraHost (host : GameObject) : Bool :=
  host.isOnBattlefield && host.isCreature

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

/-- Resolve an Adventure: apply its effect, then exile the card and grant
permission to cast the permanent (CR 715.3d). -/
def resolveAdventureSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let orig := obj.adventurerCard.getD obj.printed
  let g := g.setObject { obj with printed := orig, adventurerCard := none }
  let obj := g.object! obj.id
  let (g, newId) := g.move obj.id .exile none
  let o := g.object! newId
  let g := g.setObject { o with
    playPermission := some {
      player := entry.controller
      turnEndsRemaining := 0
      fromAdventure := true } }
  g.logMsg
    s!"{o.name} is exiled. {(g.player entry.controller).name} may cast it for as long as it remains exiled (CR 715.3d)"

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    let g := { g with stack := g.stack.pop }
    match g.findObject? entry.objectId with
    | none => g.logMsg "The spell left the stack unexpectedly"
    | some obj =>
      if let some e := obj.abilityEffect then
        let g := g.applyAbilityEffect entry.controller e entry.targets obj.sourceId
        -- CR 608.2m: after resolution the ability ceases to exist.
        { g with objects := g.objects.filter (fun o => o.id != obj.id) }
      else if let some t := obj.triggeredAbility then
        let srcName := obj.printed.name.replace "'s ability" ""
        let g := g.applyTriggeredAbility entry.controller t obj.sourceId
          entry.targets entry.dividedDamage obj.lastKnownPower obj.lastKnownToughness srcName
        { g with objects := g.objects.filter (fun o => o.id != obj.id) }
      else
        let g :=
          let effect? :=
            if obj.printed.isModal then
              match entry.chosenMode with
              | some i => obj.printed.spellModes[i]?
              | none => none
            else
              obj.printed.spellEffect
          match effect? with
          | some e => g.applyEffect entry.controller e entry.targets
          | none => g
        if obj.isAdventureSpell then
          g.resolveAdventureSpell entry (g.object! obj.id)
        else if obj.printed.isAura then
          g.resolveAuraSpell entry obj
        else if obj.printed.isPermanentCard && !obj.printed.isLand then
          let (g, newId) := g.move obj.id .battlefield (some entry.controller)
          let o := g.object! newId
          let sick := !o.printed.keywords.haste
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
  g := { g with pending := .none }
  g := g.promptTriggerTargetsIfNeeded
  if g.pending != .none then
    return g
  return g.receivePriority p

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
    g := g.setObject { b with status := { b.status with blocking := #[attackerId] } }
    let aNow := g.object! attackerId
    g := g.setObject { aNow with status := { aNow.status with blocked := true } }
    g := g.logMsg s!"{b.name} blocks {a.name}"
  if assignments.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not block"
  g := g.putBlockedTriggersOnStack assignments
  return { g with pending := .none } |>.receivePriority g.activePlayer

/-- Sum of combat damage this assignment sends to creatures. -/
def creatureDamageTotal (asgn : CreatureCombatAssignment) : Int :=
  asgn.toCreatures.foldl (fun acc (_, n) => acc + n) 0

/-- A legal default assignment for `source` (CR 510.1c–d, 702.19).
Without trample, all damage goes to the first remaining recipient — one
legal division under 510.1c/d. With trample, lethal is assigned to each
blocker before leftover goes to the defending player. -/
def defaultCombatAssignment (g : Game) (source : GameObject) (forAttackers : Bool)
    (already : Array CreatureCombatAssignment) : CreatureCombatAssignment :=
  let dmg := max (g.power source) 0
  if forAttackers then
    let blockers := g.blockersOf source.id
    if blockers.isEmpty then
      if source.status.blocked && !g.hasTrample source then
        { source := source.id }
      else
        { source := source.id, toPlayer := dmg }
    else if g.hasTrample source then
      Id.run do
        let mut remaining := dmg
        let mut toCreatures : Array (ObjectId × Int) := #[]
        let mut already := already
        for b in blockers do
          let need := g.lethalRemaining b already
          let amt := min remaining need
          toCreatures := toCreatures.push (b.id, amt)
          already := already.push { source := source.id, toCreatures := #[(b.id, amt)] }
          remaining := remaining - amt
        return { source := source.id, toCreatures := toCreatures, toPlayer := remaining }
    else
      { source := source.id, toCreatures := #[(blockers[0]!.id, dmg)] }
  else
    let targets := g.creaturesBlockedBy source
    if targets.isEmpty then { source := source.id }
    else { source := source.id, toCreatures := #[(targets[0]!.id, dmg)] }

/-- Fill in a default for every assigning creature not listed in `listed`. -/
def completeCombatAssignments (g : Game) (forAttackers : Bool)
    (listed : Array CreatureCombatAssignment) : Except String (Array CreatureCombatAssignment) := do
  let mut acc : Array CreatureCombatAssignment := #[]
  let mut seen : Array ObjectId := #[]
  let assigning := g.creaturesAssigningCombatDamage forAttackers
  for a in listed do
    if seen.contains a.source then
      throw "Duplicate combat damage source"
    if !assigning.any (fun o => o.id == a.source) then
      throw "That creature does not assign combat damage now"
    seen := seen.push a.source
    acc := acc.push a
  for o in assigning do
    if !seen.contains o.id then
      let asgn := g.defaultCombatAssignment o forAttackers acc
      acc := acc.push asgn
      seen := seen.push o.id
  return acc

/-- Check one creature's assignment against CR 510.1a–d and trample (702.19b).
`batch` is the complete assignment for this half of 510.1, so lethal can
include damage from other creatures (CR 510.1e / 702.19b). -/
def checkCombatAssignment (g : Game) (asgn : CreatureCombatAssignment) (forAttackers : Bool)
    (batch : Array CreatureCombatAssignment) : Except String Unit := do
  let some src := g.findObject? asgn.source | throw "no such object"
  if !src.isOnBattlefield then
    throw s!"{src.name} is not on the battlefield"
  let dmg := max (g.power src) 0
  if asgn.toPlayer < 0 || asgn.toCreatures.any (fun (_, n) => n < 0) then
    throw "Combat damage amounts cannot be negative"
  let mut seenTargets : Array ObjectId := #[]
  for (tid, _) in asgn.toCreatures do
    if seenTargets.contains tid then
      throw "Duplicate combat damage recipient"
    seenTargets := seenTargets.push tid
  let recipients := g.legalCombatDamageRecipients src forAttackers
  for (tid, _) in asgn.toCreatures do
    if !recipients.any (fun r => r.id == tid) then
      if forAttackers then
        throw s!"{src.name} must assign combat damage to the creatures blocking it (CR 510.1c)"
      else
        throw s!"{src.name} must assign combat damage to the creatures it's blocking (CR 510.1d)"
  let toCreatures := creatureDamageTotal asgn
  if forAttackers then
    if !src.status.attacking then
      throw s!"{src.name} is not attacking"
    if recipients.isEmpty then
      if asgn.toCreatures.size != 0 then
        throw s!"{src.name} has no blocking creatures to assign combat damage to"
      if src.status.blocked && !g.hasTrample src then
        if asgn.toPlayer != 0 then
          throw s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
      else if asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
    else
      if toCreatures + asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
      if asgn.toPlayer > 0 then
        if !g.hasTrample src then
          throw s!"{src.name} cannot assign combat damage to the defending player"
        if recipients.any (fun b => g.lethalRemaining b batch > 0) then
          throw s!"{src.name} must assign lethal damage to each blocking creature before trampling (CR 702.19b)"
  else
    if src.status.blocking.isEmpty then
      throw s!"{src.name} is not blocking"
    if asgn.toPlayer != 0 then
      throw s!"{src.name} assigns combat damage to the creatures it's blocking (CR 510.1d)"
    if recipients.isEmpty then
      if toCreatures != 0 then
        throw s!"{src.name} is not blocking any creatures and assigns no combat damage (CR 510.1d)"
    else if toCreatures != dmg then
      throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"

/-- CR 510.1e: the total assignment is legal only if every creature complies. -/
def checkCombatAssignmentBatch (g : Game) (forAttackers : Bool)
    (batch : Array CreatureCombatAssignment) : Except String Unit := do
  for a in batch do
    let _ ← checkCombatAssignment g a forAttackers batch
  let expected := (g.creaturesAssigningCombatDamage forAttackers).map (·.id)
  if batch.size != expected.size || !expected.all (fun id => batch.any (·.source == id)) then
    throw "Every attacking or blocking creature must assign combat damage (CR 510.1)"

/-- Apply assigned combat damage simultaneously (CR 510.2). -/
def dealAssignedCombatDamage (g : Game) : Game :=
  Id.run do
    let mut g := g
    let defn := g.opponent g.activePlayer
    for asgn in g.assignedCombatDamage do
      let src := g.object! asgn.source
      let recipients :=
        if src.status.attacking then g.blockersOf src.id else g.creaturesBlockedBy src
      if src.status.attacking && src.status.blocked && recipients.isEmpty &&
          asgn.toPlayer == 0 then
        g := g.logMsg
          s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
      else if !src.status.blocking.isEmpty && recipients.isEmpty then
        g := g.logMsg
          s!"{src.name} is not blocking any creatures and assigns no combat damage (CR 510.1d)"
      for (tid, amt) in asgn.toCreatures do
        if amt > 0 then
          let t := g.object! tid
          g := g.setObject { t with status := { t.status with damage := t.status.damage + amt } }
          g := g.logMsg s!"{src.name} deals {amt} combat damage to {t.name}"
      if asgn.toPlayer > 0 then
        let pl := g.player defn
        g := g.setPlayer { pl with life := pl.life - asgn.toPlayer }
        if src.status.blocked then
          g := g.logMsg
            s!"{src.name} tramples for {asgn.toPlayer} to {pl.name} ({(g.player defn).life} life)"
        else
          g := g.logMsg
            s!"{src.name} deals {asgn.toPlayer} combat damage to {pl.name} ({(g.player defn).life} life)"
    g := { g with assignedCombatDamage := #[], pending := .none }
    return g.receivePriority g.activePlayer

/-- Record a legal assignment batch and append it for later dealing. -/
def storeCombatAssignments (g : Game) (forAttackers : Bool)
    (listed : Array CreatureCombatAssignment) : Except String Game := do
  let batch ← g.completeCombatAssignments forAttackers listed
  let _ ← checkCombatAssignmentBatch g forAttackers batch
  return { g with assignedCombatDamage := g.assignedCombatDamage ++ batch }

/-- After attackers have assigned, the defending player assigns (CR 510.1d)
or damage is dealt if they have no division to announce. -/
def finishAttackerCombatAssignment (g : Game) : Game :=
  let defender := g.opponent g.activePlayer
  if g.needsCombatDamageChoice false then
    { g with pending := .assignCombatDamage defender false }
      |>.logMsg s!"{(g.player defender).name} assigns combat damage (CR 510.1d)"
  else
    match g.storeCombatAssignments false #[] with
    | .ok g' => g'.dealAssignedCombatDamage
    | .error e => g.logMsg s!"Combat damage assignment failed: {e}"

/-- Start CR 510.1: the active player assigns attacking creatures first. -/
def beginCombatDamageAssignment (g : Game) : Game :=
  let g := { g with assignedCombatDamage := #[], pending := .none }
  if g.needsCombatDamageChoice true then
    { g with pending := .assignCombatDamage g.activePlayer true }
      |>.logMsg s!"{(g.player g.activePlayer).name} assigns combat damage (CR 510.1c)"
  else
    match g.storeCombatAssignments true #[] with
    | .ok g' => g'.finishAttackerCombatAssignment
    | .error e => g.logMsg s!"Combat damage assignment failed: {e}"

/-- Assign and deal combat damage (CR 510.1–510.2). -/
def combatDamage (g : Game) : Game :=
  g.beginCombatDamageAssignment

/-- Announce how attacking or blocking creatures assign combat damage (CR 510.1). -/
def announceCombatDamage (g : Game) (p : PlayerId)
    (listed : Array CreatureCombatAssignment) : Except String Game := do
  match g.pending with
  | .assignCombatDamage q forAttackers =>
    if p != q then
      throw s!"Only {(g.player q).name} may assign combat damage (CR 510.1)"
    let g ← g.storeCombatAssignments forAttackers listed
    if forAttackers then
      return g.finishAttackerCombatAssignment
    else
      return g.dealAssignedCombatDamage
  | _ => throw "Not time to assign combat damage (CR 510.1)"

def clearCombat (g : Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.status.attacking || !o.status.blocking.isEmpty || o.status.blocked then
        g := g.setObject { o with
          status := { o.status with attacking := false, blocking := #[], blocked := false } }
    return g

def clearEOT (g : Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.status.damage != 0 || o.status.pumpPower != 0 || o.status.pumpToughness != 0 ||
          o.status.untilEotTrample || o.status.untilEotHexproof ||
          o.status.setBasePower.isSome || o.status.setBaseToughness.isSome then
        g := g.setObject { o with
          status := { o.status with
            damage := 0, pumpPower := 0, pumpToughness := 0
            untilEotTrample := false, untilEotHexproof := false
            setBasePower := none, setBaseToughness := none } }
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
        if perm.fromAdventure then
          pure ()
        else if perm.player == endingPlayer then
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
      g.beginCombatDamageAssignment
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
  | .chooseMode _ =>
    throw "Choose a mode first (CR 601.2b)"
  | .chooseTargets _ =>
    throw "Choose a target first (CR 601.2c)"
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

/-- Discard `id` from hand; if this finishes a pending “may discard, then draw”,
draw that many cards (CR 701.9). -/
def discardForDraw (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .mayDiscardDraw q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard"
    let pl := g.player p
    if !pl.hand.contains id then
      throw "That card is not in your hand"
    let some card := g.findObject? id | throw "no such object"
    let g := g.logMsg s!"{(g.player p).name} discards {card.name}"
    let (g, _) := g.move id (.graveyard card.owner) none
    let g := g.draw p n
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to discard a card (CR 701.9)"

/-- Decline an optional discard (CR 608.2d) or choose no target for an
“up to one” trigger (CR 601.2c / 115.1c). -/
def decline (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayDiscardDraw q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to discard"
    let g := g.logMsg s!"{(g.player p).name} declines to discard a card"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    match obj.triggeredAbility with
    | some ab =>
      if !ab.allowsZeroTargets then
        throw "That ability requires a target (CR 601.2c)"
      let g := g.setStackEntryTargets obj.id #[]
      let g := g.logMsg
        s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
      return g.afterTriggerTargetsChosen
    | none =>
      throw "That spell requires a target (CR 601.2c)"
  | _ => throw "Not time to decline"

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
  | .castAdventure id => g.castSpell p id true
  | .chooseMode idx => g.announceMode p idx
  | .target t => g.announceTarget p t
  | .divideDamage t n => g.announceTarget p t (some n)
  | .activate id idx => g.activateAbility p id idx
  | .pay => g.pay p
  | .sacrifice id => g.sacrificeForActivation p id
  | .declareAttackers ids => g.declareAttackers p ids
  | .declareBlockers as => g.declareBlockers p as
  | .assignCombatDamage asgns => g.announceCombatDamage p asgns
  | .keep => g.keepOpeningHand p
  | .takeMulligan => g.takeMulligan p
  | .putOnBottom ids => g.putCardsOnBottom p ids
  | .scry top bottom => g.finishScry p top bottom
  | .discard id => g.discardForDraw p id
  | .decline => g.decline p
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
    | .chooseMode p => some p
    | .chooseTargets p => some p
    | .sacrificePermanent p _ => some p
    | .declareMulligan p => some p
    | .putOnBottom p _ => some p
    | .scry p _ => some p
    | .mayDiscardDraw p _ => some p
    | .assignCombatDamage p _ => some p
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
