import Mtg.Engine.Game.Pending

/-!
# Players, actions, and setup (CR 102 / 103)

`GameResult`, `Player` — life, zones, mulligan bookkeeping, designations,
and per-turn flags — `Seat` and `StartConfig` for starting a game, and
the `Action` interface players use to act.
-/

namespace Mtg.Engine

/-- One unit of mana in a mana pool or mana event, with its type, producing
source, and spending restriction (CR 106.1 / 106.6). -/
structure ManaUnit where
  mana : ManaType
  source : Option ObjectId := none
  restriction : Option ManaRestriction := none
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaPool

/-- Add one `ManaUnit` to `p` (CR 106.4 / 106.6). -/
def addUnit (p : ManaPool) (u : ManaUnit) : ManaPool :=
  match u.restriction.getD .none with
  | .none => p.add u.mana
  | .elf => p.add u.mana (elfRestricted := true)
  | .instantOrSorcery => p.add u.mana (instRestricted := true)
  | .hero => p.add u.mana (heroRestricted := true)
  | .villain => p.add u.mana (villainRestricted := true)
  | .cantNonartifact => p.add u.mana (cantNonartifact := true)
  | .creatureSource => p.add u.mana (creatureRestricted := true)
  | .fra fu => p.add u.mana (fra := some fu)

/-- Add `units` to `p` in order (CR 106.4 / 106.6). -/
def addUnits (p : ManaPool) (units : Array ManaUnit) : ManaPool :=
  units.foldl addUnit p

/-- Remove one `ManaUnit` from `p` (CR 106.4 / 106.6). -/
def removeUnit (p : ManaPool) (u : ManaUnit) : ManaPool :=
  let t := u.mana
  if p.get t == 0 then p
  else
    let p := p.set t (p.get t - 1)
    match u.restriction.getD .none with
    | .none => p
    | .elf => p.setElf t (p.getElf t - 1)
    | .instantOrSorcery => p.setInst t (p.getInst t - 1)
    | .hero => p.setHero t (p.getHero t - 1)
    | .villain => p.setVillain t (p.getVillain t - 1)
    | .cantNonartifact =>
      if t == .colorless then { p with cantNonartifact := p.cantNonartifact - 1 }
      else if t == .colored .blue then { p with cantNonartifactBlue := p.cantNonartifactBlue - 1 }
      else p
    | .creatureSource => p.setCreature t (p.getCreature t - 1)
    | .fra fu =>
      match p.fraRestricted.findIdx? (fun (t', fu') => t' == t && fu' == fu) with
      | some i => { p with fraRestricted := p.fraRestricted.eraseIdx! i }
      | none => p

/-- Remove `units` from `p` in order (CR 106.4 / 106.6). -/
def removeUnits (p : ManaPool) (units : Array ManaUnit) : ManaPool :=
  units.foldl removeUnit p

/-- Enumerate all mana units currently in `p` (CR 106.4). -/
def toUnits (p : ManaPool) : Array ManaUnit :=
  let colors : List Color := [.white, .blue, .black, .red, .green]
  let coloredUnits :=
    colors.foldl (fun acc c =>
      let t := ManaType.colored c
      let acc := acc ++ Array.replicate (p.unrestricted t) { mana := t }
      let acc := acc ++ Array.replicate (p.getElf t) { mana := t, restriction := some .elf }
      let acc := acc ++ Array.replicate (p.getInst t) { mana := t, restriction := some .instantOrSorcery }
      let acc := acc ++ Array.replicate (p.getHero t) { mana := t, restriction := some .hero }
      let acc := acc ++ Array.replicate (p.getVillain t) { mana := t, restriction := some .villain }
      let acc := acc ++ Array.replicate (p.getCreature t) { mana := t, restriction := some .creatureSource }
      if c == .blue then
        acc ++ Array.replicate p.cantNonartifactBlue { mana := t, restriction := some .cantNonartifact }
      else acc) (#[] : Array ManaUnit)
  let colorlessUnits :=
    Array.replicate (p.unrestricted .colorless) { mana := .colorless } ++
      Array.replicate p.cantNonartifact { mana := .colorless, restriction := some .cantNonartifact }
  let fraUnits :=
    p.fraRestricted.map (fun (t, fu) => ({ mana := t, restriction := some (.fra fu) } : ManaUnit))
  coloredUnits ++ colorlessUnits ++ fraUnits

/-- Try to spend one mana of the given type, returning the updated pool and the
`ManaUnit` spent (CR 106.6). -/
def spendOneUnit? (p : ManaPool) (t : ManaType) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) :
    Option (ManaPool × ManaUnit) :=
  if p.get t == 0 then none
  else if let some i := p.fraRestricted.findIdx? (fun (t', u) => t' == t && u.allows spend) then
    let (_, u) := p.fraRestricted[i]!
    some ({ p.set t (p.get t - 1) with fraRestricted := p.fraRestricted.eraseIdx! i },
      { mana := t, restriction := some (.fra u) })
  else if allowHeroRestricted && p.getHero t > 0 then
    some (p.set t (p.get t - 1) |>.setHero t (p.getHero t - 1),
      { mana := t, restriction := some .hero })
  else if allowVillainRestricted && p.getVillain t > 0 then
    some (p.set t (p.get t - 1) |>.setVillain t (p.getVillain t - 1),
      { mana := t, restriction := some .villain })
  else if allowCreatureRestricted && p.getCreature t > 0 then
    some (p.set t (p.get t - 1) |>.setCreature t (p.getCreature t - 1),
      { mana := t, restriction := some .creatureSource })
  else if allowElfRestricted && p.getElf t > 0 then
    some (p.set t (p.get t - 1) |>.setElf t (p.getElf t - 1),
      { mana := t, restriction := some .elf })
  else if allowInstRestricted && p.getInst t > 0 then
    some (p.set t (p.get t - 1) |>.setInst t (p.getInst t - 1),
      { mana := t, restriction := some .instantOrSorcery })
  else if allowCantNonartifact && t == .colorless && p.cantNonartifact > 0 then
    some ({ p.set t (p.get t - 1) with cantNonartifact := p.cantNonartifact - 1 },
      { mana := t, restriction := some .cantNonartifact })
  else if allowCantNonartifact && t == .colored .blue && p.cantNonartifactBlue > 0 then
    some ({ p.set t (p.get t - 1) with cantNonartifactBlue := p.cantNonartifactBlue - 1 },
      { mana := t, restriction := some .cantNonartifact })
  else if p.unrestricted t > 0 then
    some (p.set t (p.get t - 1), { mana := t })
  else none

/-- Spend one mana of any type, returning the updated pool and the `ManaUnit`
spent. Restricted Elf mana is spent first when allowed, then
instant/sorcery-restricted mana, then colorless, then WUBRG (CR 106.6). -/
def spendAnyUnit? (p : ManaPool) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) :
    Option (ManaPool × ManaUnit) :=
  let colored : List ManaType :=
    [.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]
  let order : List ManaType := [.colorless] ++ colored
  Id.run do
    if let some (t, _) := p.fraRestricted.find? (fun (_, u) => u.allows spend) then
      if let some res := p.spendOneUnit? t (spend := spend) then
        return some res
    if allowElfRestricted then
      for t in colored do
        if p.getElf t > 0 then
          if let some res := p.spendOneUnit? t true then
            return some res
    if allowInstRestricted then
      for t in colored do
        if p.getInst t > 0 then
          if let some res := p.spendOneUnit? t false true then
            return some res
    if allowHeroRestricted then
      for t in colored do
        if p.getHero t > 0 then
          if let some res := p.spendOneUnit? t false false true then
            return some res
    if allowVillainRestricted then
      for t in colored do
        if p.getVillain t > 0 then
          if let some res := p.spendOneUnit? t false false false true then
            return some res
    if allowCreatureRestricted then
      for t in colored do
        if p.getCreature t > 0 then
          if let some res :=
              p.spendOneUnit? t false false false false false true then
            return some res
    for t in order do
      if let some res := p.spendOneUnit? t allowElfRestricted allowInstRestricted
          allowHeroRestricted allowVillainRestricted allowCantNonartifact
          allowCreatureRestricted spend then
        return some res
    return none

/-- Pay a mana cost, requiring colored/colorless symbols first, then generic
(CR 202), returning the updated pool and the `ManaUnit`s spent. -/
def payUnits? (p : ManaPool) (cost : ManaCost) (allowElfRestricted : Bool := false)
    (allowInstRestricted : Bool := false) (allowHeroRestricted : Bool := false)
    (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {}) :
    Option (ManaPool × Array ManaUnit) :=
  Id.run do
    let mut pool := p
    let mut units : Array ManaUnit := #[]
    let mut unpaidTwobrid : Nat := 0
    for s in cost.symbols do
      match s with
      | .colored c =>
        match pool.spendOneUnit? (.colored c) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some (p', u) => pool := p'; units := units.push u
        | none => return none
      | .colorless =>
        match pool.spendOneUnit? .colorless allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some (p', u) => pool := p'; units := units.push u
        | none => return none
      | .hybrid a b =>
        match pool.spendOneUnit? (.colored a) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some (p', u) => pool := p'; units := units.push u
        | none =>
          match pool.spendOneUnit? (.colored b) allowElfRestricted allowInstRestricted
              allowHeroRestricted allowVillainRestricted allowCantNonartifact
              allowCreatureRestricted spend with
          | some (p', u) => pool := p'; units := units.push u
          | none => return none
      | .twobrid c =>
        match pool.spendOneUnit? (.colored c) allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some (p', u) => pool := p'; units := units.push u
        | none => unpaidTwobrid := unpaidTwobrid + 1
      | .generic _ | .x => pure ()
    for _ in [0:unpaidTwobrid] do
      for _ in [0:2] do
        match pool.spendAnyUnit? allowElfRestricted allowInstRestricted
            allowHeroRestricted allowVillainRestricted allowCantNonartifact
            allowCreatureRestricted spend with
        | some (p', u) => pool := p'; units := units.push u
        | none => return none
    for s in cost.symbols do
      match s with
      | .generic n =>
        for _ in [0:n] do
          match pool.spendAnyUnit? allowElfRestricted allowInstRestricted
              allowHeroRestricted allowVillainRestricted allowCantNonartifact
              allowCreatureRestricted spend with
          | some (p', u) => pool := p'; units := units.push u
          | none => return none
      | _ => pure ()
    return some (pool, units)

end ManaPool

inductive GameResult where
  | won (player : PlayerId)
  | draw
deriving DecidableEq, Repr, Inhabited, BEq

structure Player where
  id : PlayerId
  name : String
  life : Int := 20
  startingLife : Int := 20
  maxHandSize : Option Nat := some 7
  /-- Cards drawn as the game begins (CR 103.5); normally seven. -/
  startingHandSize : Nat := 7
  manaPool : ManaPool := {}
  poison : Nat := 0
  /-- Non-poison counters on this player (CR 122.1). -/
  counters : Array (CounterKind × Nat) := #[]
  lost : Bool := false
  /-- CR 800.4a has already been performed for this player. -/
  leftTheGame : Bool := false
  /-- Completed London mulligans this game (CR 103.5). The first may not
  count toward bottoming or the zero-card limit (CR 103.5c). -/
  mulligansTaken : Nat := 0
  /-- Set once this player declines further mulligans (CR 103.5). -/
  keptOpeningHand : Bool := false
  library : Array ObjectId := #[]
  hand : Array ObjectId := #[]
  graveyard : Array ObjectId := #[]
  /-- Storied: enduring story for the rest of the game. -/
  enduringStory : Bool := false
  /-- Number of The Ring emblem abilities gained (0 = no emblem). Max 4. -/
  theRingAbilities : Nat := 0
  /-- Current Ring-bearer, if any. -/
  ringBearerId : Option ObjectId := none
  /-- Ascend: the city's blessing for the rest of the game. -/
  citysBlessing : Bool := false
  /-- True when this player has a commander (Commander / Oathbreaker). -/
  hasCommander : Bool := false
  /-- Combined color identity of this player's commander(s). Empty when they
  have no commander or the commander is colorless (CR 903.4). -/
  commanderColorIdentity : ColorSet := {}
  /-- Sideboard cards not yet brought into play as objects outside the game
  (CR 400.11b). -/
  sideboard : Array CardDef := #[]
  /-- Two-Headed Giant teammate (MSH 57 / 236). -/
  teammate : Option PlayerId := none
  /-- This player is the monarch (CR 722). -/
  isMonarch : Bool := false
  /-- Creature types of this player's commander, for Path of Ancestry. -/
  commanderCreatureTypes : Array CardSubtype := #[]
deriving Repr, Inhabited, BEq

namespace Player

/-- Number of counters of `kind` on `pl` (CR 122.1). -/
def counterCount (pl : Player) (kind : CounterKind) : Nat :=
  match kind with
  | .poison => pl.poison
  | _ =>
    match pl.counters.find? (·.1 == kind) with
    | some (_, n) => n
    | none => 0

end Player

/-- A seat at the table before objects are created. -/
structure Seat where
  name : String
  deck : Array CardDef
  /-- Cards outside the game the player may use, such as a sideboard
  (CR 400.11b). -/
  sideboard : Array CardDef := #[]
deriving Repr, Inhabited

structure StartConfig where
  seats : Array Seat
  format : Format := .constructed
  /-- CR 903.12 Brawl option. The first mulligan is free (CR 103.5c / 903.12g). -/
  brawl : Bool := false
  seed : UInt64 := 20260807
  /-- Index into `seats`. `none` means the RNG chooses. -/
  startingPlayer : Option Nat := none
  /-- When true, never shuffle or roll; leave a `Pending.resolveRandom`. -/
  norandom : Bool := false

inductive Action where
  | pass
  | playLand (id : ObjectId)
  | tapForMana (id : ObjectId) (mana : ManaType)
  /-- Activate mana ability `idx` of `id` (CR 605.3), adding exactly `mana`
  and paying costs that need chosen objects with `costIds`, in order. -/
  | activateManaAbility (id : ObjectId) (idx : Nat) (mana : Array ManaType)
      (costIds : Array ObjectId := #[])
  | cast (id : ObjectId)
  /-- Cast this adventurer card as its Adventure (CR 715.3). -/
  | castAdventure (id : ObjectId)
  /-- Cast this card for its sneak cost, returning the unblocked attacker
  `attackerId` you control to hand as part of the cost (MSH sneak). -/
  | castWithSneak (id attackerId : ObjectId)
  /-- Choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (idx : Nat)
  /-- Announce a value for `{X}` (CR 107.3a / 601.2b). -/
  | chooseX (n : Nat)
  /-- Announce a target for the current instance of the word “target”
  (CR 601.2c). For a divided-damage ability, assigns all remaining damage
  to this one target (CR 601.2d). For “one or two target creatures”, this
  chooses exactly that one creature. -/
  | target (t : Target)
  /-- Announce every target of one instance of the word “target” together
  (CR 601.2c), e.g. both creatures of “one or two target creatures”. -/
  | targets (ts : Array Target)
  /-- Announce every target of one instance of the word “target” on a
  “divided as you choose” effect, together with the damage assigned to each
  (CR 601.2c / 601.2d). -/
  | divideDamage (assignments : Array (Target × Nat))
  /-- Activate a non-mana activated ability of a permanent (CR 602). -/
  | activate (id : ObjectId) (abilityIdx : Nat)
  /-- Pay the locked-in cost of a proposed spell or ability (CR 601.2h / 602.2b). -/
  | pay
  /-- After `pay`, sacrifice an artifact or creature to finish paying
  (CR 601.2h / 602.2b), a creature a resolved trigger requires, or a creature
  as a resolving effect. -/
  | sacrifice (id : ObjectId)
  /-- Choose to pay extra generic mana rather than the non-mana option
  (sacrifice or discard) as an additional cost (CR 601.2b). `true` pays
  the generic alternative; `false` sacrifices or discards. -/
  | chooseAdditionalCost (payGeneric : Bool)
  /-- `defender` is the destination when `each` is omitted or an entry is
  `none`. `each[i]` is the player `ids[i]` attacks (CR 508.1).
  `planeswalkers[i]`, when set, is the planeswalker `ids[i]` attacks instead
  (CR 506.3 / 508.1b). -/
  | declareAttackers (ids : Array ObjectId) (defender : Option PlayerId := none)
      (each : Array (Option PlayerId) := #[])
      (planeswalkers : Array (Option ObjectId) := #[])
  | declareBlockers (assignments : Array (ObjectId × ObjectId))
  /-- Announce combat damage assignment (CR 510.1). Omitted sources use a
  legal default; listed sources must divide their power among legal creature
  recipients (and leftover to the defending player only with trample). -/
  | assignCombatDamage (assignments : Array CreatureCombatAssignment)
  /-- Keep this hand as the opening hand (CR 103.5). -/
  | keep
  /-- Choose which legendary permanent to keep under the legend rule (CR 704.5j). -/
  | keepLegend (id : ObjectId)
  /-- Put waiting triggered abilities on the stack in this source order
  (first listed is put first, so it is farthest from the top) (CR 603.3b). -/
  | stackTriggers (ids : Array ObjectId)
  /-- Declare a London mulligan; it is taken after every remaining player has
  declared (CR 103.5). -/
  | takeMulligan
  /-- Put these cards on the bottom after a mulligan, first listed = new bottom. -/
  | putOnBottom (ids : Array ObjectId)
  /-- Finish scrying: `top` (last = new top) go on top of the library in that
  order; `bottom` (first = new bottom) go to the bottom (CR 701.20). -/
  | scry (top : Array ObjectId) (bottom : Array ObjectId)
  /-- Finish surveilling: `top` (last = new top) go on top of the library in
  that order; `graveyard` go to the graveyard in that order (CR 701.25). -/
  | surveil (top : Array ObjectId) (graveyard : Array ObjectId)
  /-- Discard this card from hand; if a pending “may discard, then draw” is
  waiting, draw afterward (CR 701.9). -/
  | discard (id : ObjectId)
  /-- Decline an optional “you may discard a card”, or choose no target for an
  “up to one” trigger (CR 608.2d / 601.2c). -/
  | decline
  /-- Agree to an optional action offered while an effect resolves. -/
  | accept
  /-- Have the entering Villain connive (Baron Strucker; MSH 422). -/
  | haveVillainConnive
  /-- Pay a pending generic-mana “you may pay” or “unless pays” cost. -/
  | payGeneric
  /-- Put the pending card on top of its owner's library. -/
  | chooseTop
  /-- Put the pending card on the bottom of its owner's library. -/
  | chooseBottom
  /-- Attach this Equipment, or tap these Humans. -/
  | choosePermanents (ids : Array ObjectId)
  /-- Pay (`true`) or decline (`false`) the optional kicker cost. -/
  | announceKicker (kick : Bool)
  /-- Promise a gift to this opponent, or `none` to decline. -/
  | announceGift (to : Option PlayerId)
  /-- Pay (`true`) or decline (`false`) the optional teamwork cost. -/
  | announceTeamwork (pay : Bool)
  /-- Choose this creature as your Ring-bearer, or `none` if you control none. -/
  | chooseRingBearer (id : Option ObjectId)
  | concede
  /-- Supply the order or chosen object for a pending random event
  (`--norandom`). An empty list keeps the current order of a shuffle. -/
  | supplyOrder (ids : Array ObjectId)
  /-- Supply an index for a pending `chooseIndex` random event (`--norandom`). -/
  | supplyIndex (i : Nat)
  /-- Name a card (CR 201.3), e.g. for Meddling Mage. -/
  | chooseName (name : String)
  /-- Choose which applicable replacement or prevention effect to apply next (CR 616.1). -/
  | chooseReplacement (id : ReplacementId)
deriving Repr

end Mtg.Engine
