import Mtg.Engine.Card
import Mtg.Engine.Deck
import Mtg.Engine.Mana
import Mtg.Engine.Rng
import Mtg.Engine.Rules
import Mtg.Engine.Turn
import Mtg.Engine.Zone

/-!
# Game state and rules engine

Encodes starting a game (CR 103), ending a game (CR 104), priority (CR 117),
playing lands (CR 116.2a / 305), casting the spells we model (CR 601),
combat (CR 506–510), and the state-based actions we implement (CR 704.5).
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

end GameObject

/-- A spell or ability on the stack (CR 405). Last array element is the top. -/
structure StackEntry where
  objectId : ObjectId
  controller : PlayerId
  targets : Array Target
deriving Repr, Inhabited

/-- Choice that must be made before priority proceeds. -/
inductive Pending where
  | none
  | declareAttackers
  | declareBlockers
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
  manaPool : ManaPool := {}
  landsPlayedThisTurn : Nat := 0
  poison : Nat := 0
  lost : Bool := false
  drewFromEmpty : Bool := false
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
  | cast (id : ObjectId) (target : Option Target)
  | declareAttackers (ids : Array ObjectId)
  | declareBlockers (assignments : Array (ObjectId × ObjectId))
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

/-- Move an object to a new zone, assigning a new object identity (CR 400.7). -/
def move (g : Game) (id : ObjectId) (dest : Zone) (controller : Option PlayerId := none) :
    Game × ObjectId :=
  let old := g.object! id
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

partial def checkSBA (g : Game) : Game :=
  if g.over then g
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
          let t := o.toughness
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
      let living := g.livingPlayers
      if living.size == 0 then
        g := { g with result := some .draw }
        g := g.logMsg "The game is a draw"
        return g
      else if living.size == 1 then
        let w := living[0]!
        g := { g with result := some (.won w.id) }
        g := g.logMsg s!"{w.name} wins the game"
        return g
      if changed then
        return checkSBA g
      return g

def receivePriority (g : Game) (p : PlayerId) : Game :=
  let g := g.checkSBA
  if g.over then g
  else { g with priority := p, consecutivePasses := 0 }

def asSorcery? (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.stack.isEmpty &&
  g.step.isMainPhase && g.activePlayer == p && g.priority == p

def hasPriority (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.priority == p && g.step.playersReceivePriority

/-- Lands remaining this turn (CR 305.3 / 116.2a). -/
def canPlayLand (g : Game) (p : PlayerId) : Bool :=
  g.asSorcery? p && (g.player p).landsPlayedThisTurn == 0

def playLand (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.canPlayLand p then
    throw "Can't play a land now (CR 116.2a / 305.3)"
  let pl := g.player p
  if !pl.hand.contains id then
    throw "That card is not in your hand"
  let card := g.object! id
  if !card.printed.isLand then
    throw s!"{card.name} is not a land"
  let (g, newId) := g.move id .battlefield (some p)
  let g := g.modifyPlayer p (fun pl => { pl with landsPlayedThisTurn := pl.landsPlayedThisTurn + 1 })
  let g := g.logMsg s!"{pl.name} plays {card.name}"
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

def tapForMana (g : Game) (p : PlayerId) (id : ObjectId) (mana : ManaType) : Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
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
  -- Mana abilities don't use the stack; the same player keeps priority (CR 605).
  return { g with consecutivePasses := 0 }

def legalTargets (g : Game) (_caster : PlayerId) (effect : SpellEffect) : Array Target :=
  match effect with
  | .dealDamage _ =>
    let players := g.livingPlayers.map (fun pl => Target.player pl.id)
    let creatures := g.battlefield.filter (·.printed.isCreature) |>.map (fun o => Target.permanent o.id)
    players ++ creatures
  | .pump _ _ =>
    g.battlefield.filter (·.printed.isCreature) |>.map (fun o => Target.permanent o.id)

def canCast (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  let pl := g.player p
  pl.hand.contains o.id &&
  g.hasPriority p &&
  (if o.printed.hasSorcerySpeed then g.asSorcery? p else true) &&
  (pl.manaPool.canPay o.printed.manaCost ||
    -- Allow the caller to tap mana first; `canCast` is used after tapping in the AI.
    pl.manaPool.canPay o.printed.manaCost) &&
  match o.printed.spellEffect with
  | some e => !(g.legalTargets p e |>.isEmpty)
  | none => o.printed.isPermanentCard

def payCost (g : Game) (p : PlayerId) (cost : ManaCost) : Except String Game := do
  let pl := g.player p
  match pl.manaPool.pay? cost with
  | none => throw s!"{pl.name} cannot pay {cost}"
  | some pool =>
    return g.setPlayer { pl with manaPool := pool }

def castSpell (g : Game) (p : PlayerId) (id : ObjectId) (target : Option Target) :
    Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let pl := g.player p
  if !pl.hand.contains id then
    throw "That card is not in your hand"
  let card := g.object! id
  if card.printed.isLand then
    throw "Lands are played, not cast (CR 305)"
  if card.printed.hasSorcerySpeed && !g.asSorcery? p then
    throw s!"{card.name} has sorcery speed"
  if card.printed.spellEffect.isSome && target.isNone then
    throw s!"{card.name} requires a target"
  if let some e := card.printed.spellEffect then
    if let some t := target then
      if !(g.legalTargets p e).contains t then
        throw "Illegal target"
  let g ← g.payCost p card.printed.manaCost
  let (g, newId) := g.move id .stack (some p)
  let entry : StackEntry := { objectId := newId, controller := p, targets := target.toArray }
  let g := { g with stack := g.stack.push entry, consecutivePasses := 0 }
  let g := g.logMsg s!"{pl.name} casts {card.name}"
  return g.receivePriority p

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

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    let g := { g with stack := g.stack.pop }
    match g.findObject? entry.objectId with
    | none => g.logMsg "The spell left the stack unexpectedly"
    | some spell =>
      let g :=
        if let some e := spell.printed.spellEffect then
          g.applyEffect entry.controller e entry.targets
        else g
      if spell.printed.isPermanentCard && !spell.printed.isLand then
        let (g, newId) := g.move spell.id .battlefield (some entry.controller)
        let o := g.object! newId
        let sick := o.printed.isCreature && !o.printed.keywords.haste
        let g := g.setObject { o with status := { o.status with summoningSick := sick } }
        g.logMsg s!"{o.name} enters the battlefield"
      else
        let owner := spell.owner
        let (g, _) := g.move spell.id (.graveyard owner) none
        g.logMsg s!"{spell.name} goes to the graveyard"

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
    g := g.logMsg s!"{b.name} blocks {a.name}"
  if assignments.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not block"
  return { g with pending := .none } |>.receivePriority g.activePlayer

def combatDamage (g : Game) : Game :=
  Id.run do
    let mut g := g
    let attackers := g.battlefield.filter (·.status.attacking)
    for a in attackers do
      let blockers := g.battlefield.filter (fun b => b.status.blocking == some a.id)
      if blockers.isEmpty then
        let defn := g.opponent g.activePlayer
        let dmg := max a.power 0
        if dmg > 0 then
          let pl := g.player defn
          g := g.setPlayer { pl with life := pl.life - dmg }
          g := g.logMsg s!"{a.name} deals {dmg} combat damage to {pl.name}"
      else
        -- All combat damage from the attacker is assigned to the first blocker;
        -- leftover trample damage goes to the defending player.
        let b := blockers[0]!
        let dmg := max a.power 0
        let lethal := max b.toughness 0
        let toBlocker := if a.printed.keywords.trample then min dmg lethal else dmg
        let toPlayer := if a.printed.keywords.trample then dmg - toBlocker else 0
        g := g.setObject { b with status := { b.status with damage := b.status.damage + toBlocker } }
        g := g.logMsg s!"{a.name} deals {toBlocker} combat damage to {b.name}"
        if toPlayer > 0 then
          let defn := g.opponent g.activePlayer
          let pl := g.player defn
          g := g.setPlayer { pl with life := pl.life - toPlayer }
          g := g.logMsg s!"{a.name} tramples for {toPlayer} to {pl.name}"
        let back := max b.power 0
        if back > 0 then
          let aNow := g.object! a.id
          g := g.setObject { aNow with status := { aNow.status with damage := aNow.status.damage + back } }
          g := g.logMsg s!"{b.name} deals {back} combat damage to {a.name}"
    return g

def clearCombat (g : Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.status.attacking || o.status.blocking.isSome then
        g := g.setObject { o with status := { o.status with attacking := false, blocking := none } }
    return g

def clearEOT (g : Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.status.damage != 0 || o.status.pumpPower != 0 || o.status.pumpToughness != 0 then
        g := g.setObject { o with
          status := { o.status with damage := 0, pumpPower := 0, pumpToughness := 0 } }
    return g

def beginStep (g : Game) (st : Step) : Game :=
  let g := { g with step := st, pending := .none, consecutivePasses := 0 }
  let g := g.logMsg s!"— Turn {g.turnNumber}, {g.player g.activePlayer |>.name}: {st} —"
  match st with
  | .untap =>
    Id.run do
      let mut g := g
      let ap := g.activePlayer
      g := g.modifyPlayer ap (fun pl => { pl with landsPlayedThisTurn := 0 })
      for o in g.permanentsOf ap do
        g := g.setObject { o with status := { o.status with tapped := false, summoningSick := false } }
      -- No priority (CR 502.4). Immediately continue.
      return g
  | .draw =>
    if g.isFirstTurn && g.players.size == 2 && g.activePlayer == g.startingPlayer then
      g.logMsg s!"{g.player g.activePlayer |>.name} skips their first draw step (CR 103.8a)"
        |>.receivePriority g.activePlayer
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
    let g := g.clearCombat |>.clearEOT
    -- Discard down to maximum hand size (CR 514.1).
    let pl := g.player g.activePlayer
    let extra := pl.hand.size - pl.maxHandSize
    let g :=
      if extra > 0 then
        Id.run do
          let mut g := g
          for _ in [0:extra] do
            let pl := g.player g.activePlayer
            if let some last := pl.hand.back? then
              let card := g.object! last
              let (g', _) := g.move last (.graveyard pl.id) none
              g := g'.logMsg s!"{pl.name} discards {card.name} (cleanup)"
          return g
      else g
    g.receivePriority g.activePlayer
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
    -- Next player's turn.
    let nxt := g.nextLiving g.activePlayer
    let g := { g with
      activePlayer := nxt
      turnNumber := g.turnNumber + 1
      isFirstTurn := false }
    let g := g.logMsg s!"It is now {g.player nxt |>.name}'s turn {g.turnNumber}"
    g.beginTurn

def pass (g : Game) (p : PlayerId) : Except String Game := do
  if g.over then
    throw "The game is over"
  if g.pending != .none then
    throw "A required choice is still pending"
  if g.priority != p then
    throw "You don't have priority"
  let g := g.logMsg s!"{g.player p |>.name} passes priority"
  let g := { g with consecutivePasses := g.consecutivePasses + 1 }
  if g.consecutivePasses ≥ g.livingPlayers.size then
    if !g.stack.isEmpty then
      let g := g.resolveTop
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

def apply (g : Game) (p : PlayerId) : Action → Except String Game
  | .pass => g.pass p
  | .playLand id => g.playLand p id
  | .tapForMana id m => g.tapForMana p id m
  | .cast id t => g.castSpell p id t
  | .declareAttackers ids => g.declareAttackers p ids
  | .declareBlockers as => g.declareBlockers p as
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
    | .none =>
      if g.step.playersReceivePriority then some g.priority else none

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
  -- Starting life (CR 103.4) already 20. Draw opening hands (CR 103.5).
  for pl in g.players do
    g := g.draw pl.id 7
    g := g.logMsg s!"{pl.name} keeps their opening hand of {(g.player pl.id).hand.size}"
  g := g.logMsg s!"{g.player sp |>.name} takes the first turn"
  return g.beginTurn

end Start

#guard Format.constructed.minDeckSize == 60

end Mtg.Engine
