import Mtg.Engine.Game.CombatAssignment

/-!
# State-based actions (CR 704)

APNAP order (CR 101.4), the legend rule and its choice prompt
(CR 704.5j), and the state-based-action sweep `checkSBA` (CR 704.5).
-/

namespace Mtg.Engine
namespace Game

/-- Alias of `apnapPlayers` (CR 101.4). -/
def apnapOrder (g : Game) : Array PlayerId :=
  g.apnapPlayers

/-- Legendary permanents `p` currently controls. -/
def legendaryPermanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (g.treatedAsLegendary)

/-- First legend-rule group that needs a choice (CR 704.5j / 201.2a): two or
more legendary permanents with the same name controlled by the same player,
taking players in APNAP order. When `onlyIds` is supplied, restricts candidate
permanents to those present at the start of the SBA pass (CR 704.3). -/
def firstLegendRuleChoice? (g : Game)
    (onlyIds : Option (Array ObjectId) := none) :
    Option (PlayerId × String × Array ObjectId) :=
  Id.run do
    for p in g.apnapPlayers.filter (fun p => !g.legendRuleOffThisTurn p) do
      let legs := (g.legendaryPermanentsOf p).filter (fun o =>
        match onlyIds with
        | some ids => ids.contains o.id
        | none => true)
      let mut seen : Array String := #[]
      for o in legs do
        let nm := g.name o
        if !seen.contains nm then
          seen := seen.push nm
          let group := legs.filter (fun x => g.name x == nm)
          if group.size ≥ 2 then
            return some (p, nm, group.map (·.id))
    return none

/-- True while a player must choose which legendary permanent to keep. -/
def legendChoicePending? (g : Game) : Bool :=
  match g.pending with
  | .chooseLegend .. => true
  | _ => false

/-- True when `controller` controls a permanent saying planeswalkers they
control aren't put into graveyards for having 0 loyalty (Sanctum Lurker). -/
def planeswalkersSurviveZeroLoyalty (g : Game) (controller : Option PlayerId) : Bool :=
  match controller with
  | none => false
  | some p =>
    (g.permanentsOf p).any (fun o =>
      (g.staticAbilities o).any (fun
        | .planeswalkersSurviveZeroLoyalty => true
        | _ => false))

/-- Default legend-rule choice: the copy that entered most recently. -/
def defaultLegendToKeep (g : Game) (ids : Array ObjectId) : ObjectId :=
  ids.foldl (fun best id =>
    match g.findObject? best, g.findObject? id with
    | some a, some b => if b.timestamp ≥ a.timestamp then id else best
    | _, some _ => id
    | _, none => best) (ids[0]!)

/-- Execute the remaining permanent-removal and unattachment actions of a
single CR 704.3 state-based action pass inside the currently open batch using
conditions captured at the start of the pass (`stage` 0 = dying creatures,
1 = 0-loyalty planeswalkers + legend rule + tokens/copies outside valid zones,
2 = final-chapter Sagas, 3 = illegal Auras + illegal Equipment/creature
attachments), chaining `.finishSbaSweep` if a graveyard move pauses on
`Pending.chooseReplacement`. -/
def finishSbaSweep (g : Game) (moves : Array SbaGraveyardMove)
    (preBf : Array GameObject) (stage : Nat)
    (pwMoves : Array SbaGraveyardMove := #[])
    (sagaMoves : Array SbaGraveyardMove := #[])
    (tokensOutsideBf : Array ObjectId := #[])
    (copiesOutside : Array ObjectId := #[])
    (illegalAuras : Array ObjectId := #[])
    (illegalEquips : Array (ObjectId × ObjectId) := #[])
    (illegalCreatureAtts : Array (ObjectId × ObjectId) := #[])
    (changedIn : Bool := false) :
    Game × (Bool × Bool) := Id.run do
  let mut g := g
  let mut changed := changedIn
  if stage == 0 then
    for i in [0:moves.size] do
      let m := moves[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := moves.extract (i + 1) moves.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 0
              pwMoves sagaMoves tokensOutsideBf copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts), (true, true))
      | none => pure ()
    g := g.change .sbaChecked
  if stage <= 1 then
    -- Planeswalkers with 0 loyalty captured at start of pass (CR 704.5i).
    let pwList : Array SbaGraveyardMove := if stage == 1 then moves else pwMoves
    for i in [0:pwList.size] do
      let m := pwList[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := pwList.extract (i + 1) pwList.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 1
              #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts), (true, true))
      | none => pure ()
    -- Legend rule (CR 704.5j): pause so the controller chooses one to keep,
    -- chaining the rest of this SBA pass so `keepLegend` finishes the pass in
    -- the same batch before Pass 2 runs (CR 704.3 / 603.2c).
    match g.firstLegendRuleChoice? (some (preBf.map (·.id))) with
    | some (p, name, ids) =>
      g := g.change (.pending (.chooseLegend p name ids))
      g := g.logMsg
        s!"{(g.player p).name} chooses which {name} to keep (legend rule, CR 704.5j)"
      g := g.chainPendingReplacement (.finishSbaSweep #[] preBf 1
        #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
        illegalEquips illegalCreatureAtts)
      return (g, (true, true))
    | none => pure ()
    -- Tokens in zones other than the battlefield at start of pass cease to exist (CR 704.5d).
    for tid in tokensOutsideBf do
      match g.findObject? tid with
      | some o =>
        if o.printed.isToken && o.zone != .battlefield then
          g := g.ceaseToExist o.id (cause := some (.stateBased .tokenOutsideBattlefield))
          g := g.logMsg s!"{o.name} ceases to exist (token left the battlefield)"
          changed := true
      | none => pure ()
    -- Non-token copies outside stack and battlefield at start of pass cease to exist (CR 704.5e).
    for cid in copiesOutside do
      match g.findObject? cid with
      | some o =>
        if o.isCopy && !o.printed.isToken && o.zone != .stack && o.zone != .battlefield then
          g := g.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))
          g := g.logMsg s!"{o.name} ceases to exist (copy outside stack or battlefield, CR 704.5e)"
          changed := true
      | none => pure ()
  if stage <= 2 then
    -- Saga with lore at or past its final chapter and no chapter on the
    -- stack captured at start of pass is sacrificed (CR 714.4 / 704.5s).
    let sagaList : Array SbaGraveyardMove := if stage == 2 then moves else sagaMoves
    for i in [0:sagaList.size] do
      let m := sagaList[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := sagaList.extract (i + 1) sagaList.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 2
              #[] #[] #[] #[] illegalAuras illegalEquips illegalCreatureAtts), (true, true))
      | none => pure ()
  if stage <= 3 then
    -- Unattached or illegally attached Auras captured at start of pass (CR 704.5m).
    let auraList : Array SbaGraveyardMove :=
      if stage == 3 then moves
      else
        illegalAuras.filterMap (fun aid =>
          match g.findObject? aid with
          | some o =>
            if o.isOnBattlefield then
              some {
                objectId := o.id
                reason := s!"{g.name o} is put into its owner's graveyard (CR 704.5m)"
                sba := .illegalAura
              }
            else none
          | none => none)
    for i in [0:auraList.size] do
      let m := auraList[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := auraList.extract (i + 1) auraList.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 3
              #[] #[] #[] #[] #[] illegalEquips illegalCreatureAtts), (true, true))
      | none => pure ()
  -- Illegally attached Equipment captured at start of pass (CR 704.5n / 702.16d).
  for (eqId, hostId) in illegalEquips do
    match g.findObject? eqId with
    | some o =>
      if o.isOnBattlefield && o.attachedTo == some hostId then
        g := g.record (GameEvent.unattached g.turnNumber (g.snapshot o) hostId
          (cause := .stateBased .illegalEquipmentOrFortification))
        g := g.logMsg s!"{g.name o} becomes unattached (CR 704.5n)"
        changed := true
    | none => pure ()
  -- Creatures, battles, or non-Aura/non-Equipment permanents attached to an object (CR 704.5p).
  for (attId, hostId) in illegalCreatureAtts do
    match g.findObject? attId with
    | some o =>
      if o.isOnBattlefield && o.attachedTo == some hostId then
        g := g.record (GameEvent.unattached g.turnNumber (g.snapshot o) hostId
          (cause := .stateBased .illegalCreatureAttachment))
        g := g.logMsg s!"{g.name o} becomes unattached (CR 704.5p)"
        changed := true
    | none => pure ()
  match g.decideGameIfFinished with
  | some finished => return (finished, (true, true))
  | none => return (g, (changed, false))

/-- Perform applicable state-based actions (CR 704.3). The `Bool` is `true` if
any state-based action was performed (used by CR 514.3a). If a legend-rule
choice is required (CR 704.5j), the check pauses: that SBA is not finished,
so CR 704.3 does not yet repeat, put triggers on the stack, or grant
priority. `keepLegend` resumes the loop. -/
partial def checkSBACounted (g : Game) : Game × Bool :=
  if g.over then (g, false)
  else
    let (g, (changed, paused)) := g.withBatchReturn none fun g => Id.run do
      let mut g := g
      let mut changed := false
      -- Players losing (CR 704.5a–c). They leave after this SBA pass
      -- if the game continues (CR 800.4 / 800.4a).
      for pl in g.players do
        if !pl.lost then
          let shielded :=
            (g.permanentsOf pl.id).any (fun o =>
              (g.baseCard o).cantLoseGame && g.retainsPrintedAbilities o) ||
              (g.objects.filter (fun o =>
                o.zone == .command && g.controlledBy o pl.id)).any (fun o =>
                  (g.baseCard o).cantLoseGame && g.retainsPrintedAbilities o)
          if shielded then
            pure ()
          else if pl.life ≤ 0 then
            g := g.record (GameEvent.playerLost g.turnNumber pl.id .lifeZeroOrLess
              (cause := some (.stateBased .lifeZeroOrLess)))
            g := g.logMsg s!"{pl.name} loses the game (life total {pl.life})"
            changed := true
          else if g.drewFromEmpty pl.id then
            g := g.record (GameEvent.playerLost g.turnNumber pl.id .decked
              (cause := some (.stateBased .drewFromEmpty)))
            g := g.logMsg s!"{pl.name} loses the game (drew from empty library)"
            changed := true
          else if pl.poison ≥ 10 then
            g := g.record (GameEvent.playerLost g.turnNumber pl.id .poison
              (cause := some (.stateBased .tenPoison)))
            g := g.logMsg s!"{pl.name} loses the game (poison)"
            changed := true
      match g.decideGameIfFinished with
      | some finished => return (finished, (true, true))
      | none => pure ()
      -- Waiting for a legend-rule choice: do not apply further SBAs until
      -- the player keeps one copy (CR 704.5j). Drop a stale prompt if the
      -- group is no longer two or more.
      match g.pending with
      | .chooseReplacement _ _ =>
        return (g, (changed, true))
      | .chooseLegend p name ids =>
        let still := ids.filter (fun id =>
          match g.findObject? id with
          | some o =>
            o.isOnBattlefield && g.controlledBy o p && g.treatedAsLegendary o && g.name o == name
          | none => false)
        if still.size ≥ 2 then
          return (g, (changed, true))
        else
          g := g.change (.pending .none)
      | _ => pure ()
      -- Capture all applicable CR 704.5 state-based actions simultaneously
      -- against the start-of-pass state BEFORE applying CR 704.5q counter
      -- annihilation so simultaneous 0-toughness death LKI retains its
      -- pre-annihilation counters and Pass 1 does not sweep newly dead tokens
      -- or newly unattached Auras/Equipment until Pass 2 (CR 704.3 / 704.8).
      let preBf := g.battlefield
      let victims : Array SbaGraveyardMove :=
        preBf.filterMap (fun o =>
          if !g.isCreature o then none
          else
            let t := g.toughness o
            if t ≤ 0 then
              some {
                objectId := o.id
                reason := s!"{o.name} dies (toughness {t})"
                verb := some .put
                sba := .zeroOrLessToughness
              }
            else if o.status.damage ≥ t && !g.hasIndestructible o then
              some {
                objectId := o.id
                reason := s!"{o.name} dies from lethal damage"
                verb := some .destroy
                sba := .lethalDamage
              }
            else if g.deathtouchDealtSinceLastSba o.id && !g.hasIndestructible o then
              some {
                objectId := o.id
                reason := s!"{o.name} dies from deathtouch"
                verb := some .destroy
                sba := .deathtouchDamage
              }
            else none)
      let pwMoves : Array SbaGraveyardMove :=
        preBf.filterMap (fun o =>
          if g.isPlaneswalker o && o.status.loyaltyCounters == 0 &&
              !g.planeswalkersSurviveZeroLoyalty (g.controllerOf o) then
            some {
              objectId := o.id
              reason := s!"{g.name o} is put into its owner's graveyard (0 loyalty, CR 704.5i)"
              sba := .zeroLoyalty
            }
          else none)
      let tokensOutsideBf : Array ObjectId :=
        g.objects.filterMap (fun o =>
          if o.printed.isToken && o.zone != .battlefield then some o.id else none)
      let copiesOutside : Array ObjectId :=
        g.objects.filterMap (fun o =>
          if o.isCopy && !o.printed.isToken && o.zone != .stack && o.zone != .battlefield then
            some o.id
          else none)
      let sagaMoves : Array SbaGraveyardMove :=
        preBf.filterMap (fun o =>
          match (g.baseCard o).saga, g.controllerOf o with
          | some sdef, some ctrl =>
            if o.status.lore ≥ sdef.finalChapterNumber && sdef.finalChapterNumber > 0 &&
                !g.sagaChapterPending o.id then
              some {
                objectId := o.id
                reason := s!"{g.name o} is sacrificed (CR 714.4)"
                verb := some .sacrifice
                actor := some ctrl
                sba := .sagaFinalChapter
              }
            else none
          | _, _ => none)
      let illegalAuras : Array ObjectId :=
        preBf.filterMap (fun o =>
          if !g.isAura o then none
          else
            let legal :=
              match o.attachedTo.bind g.findObject? with
              | some host => g.auraObjCanEnchant host o
              | none => false
            if !legal then some o.id else none)
      let illegalEquips : Array (ObjectId × ObjectId) :=
        preBf.filterMap (fun o =>
          if !g.isEquipment o then none
          else
            match o.attachedTo with
            | none => none
            | some hostId =>
              let legal :=
                match g.findObject? hostId with
                | some host =>
                  host.isOnBattlefield && g.isCreature host && !g.frcProtectedFrom host o
                | none => false
              if !legal then some (o.id, hostId) else none)
      let illegalCreatureAtts : Array (ObjectId × ObjectId) :=
        preBf.filterMap (fun o =>
          match o.attachedTo with
          | none => none
          | some hostId =>
            if g.isCreature o || g.isBattle o || (!g.isAura o && !g.isEquipment o) then
              some (o.id, hostId)
            else none)
      -- CR 704.5q: +1/+1 and -1/-1 counters on one permanent are removed in
      -- pairs.
      for o in preBf do
        let k := Nat.min o.status.plusOnePlusOne o.status.minusOneMinusOne
        if k > 0 then
          let cause := EventCause.stateBased .counterAnnihilation
          g := g.record (GameEvent.counters g.turnNumber none (g.snapshot o) .plusOnePlusOne k true
            (cause := cause))
          g := g.record (GameEvent.counters g.turnNumber none (g.snapshot (g.object! o.id)) .minusOneMinusOne k true
            (cause := cause))
          g := g.logMsg s!"{k} +1/+1 and -1/-1 counter pair(s) are removed from {o.name}"
          changed := true
      return g.finishSbaSweep victims preBf 0 pwMoves sagaMoves tokensOutsideBf
        copiesOutside illegalAuras illegalEquips illegalCreatureAtts
        (changedIn := changed)
    match g.pending with
    | .chooseReplacement .. | .chooseLegend .. =>
      (g.chainPendingReplacement .checkSBA, true)
    | _ =>
      if paused then (g, changed)
      else if changed then
        let (g', _) := checkSBACounted g
        (g', true)
      else (g, false)

/-- Repeat `checkSBACounted` and `leavePlayersWhoLost` until neither performs an
action or the game ends / pauses on a pending choice (CR 704.3 / 800.4a). -/
partial def checkSBACountedWithLeaves (g : Game) : Game × Bool :=
  let (g, didSba) := g.checkSBACounted
  if g.over || g.pending != .none then (g, didSba)
  else
    let leftBefore := (g.players.filter (·.leftTheGame)).size
    let g := g.leavePlayersWhoLost
    let anyLeft := (g.players.filter (·.leftTheGame)).size > leftBefore
    if g.over || g.pending != .none then (g, didSba || anyLeft)
    else if anyLeft then
      let (g', didMore) := g.checkSBACountedWithLeaves
      (g', didSba || anyLeft || didMore)
    else (g, didSba)

def checkSBA (g : Game) : Game :=
  (g.checkSBACountedWithLeaves).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3 / 603.3b,
514.3a). All triggered abilities wait until a player would receive priority. -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingTriggers.isEmpty

end Game
end Mtg.Engine
