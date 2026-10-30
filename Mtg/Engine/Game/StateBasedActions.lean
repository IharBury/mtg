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
taking players in APNAP order. -/
def firstLegendRuleChoice? (g : Game) : Option (PlayerId × String × Array ObjectId) :=
  Id.run do
    for p in g.apnapPlayers.filter (fun p => !g.legendRuleOffThisTurn p) do
      let legs := g.legendaryPermanentsOf p
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

/-- Execute the remaining permanent-removal stages of a single CR 704.3
state-based action check inside the currently open batch (`stage` 0 = dying
creatures, 1 = 0-loyalty planeswalkers, 2 = final-chapter Sagas, 3 = illegal
Auras), chaining `.finishSbaSweep` if a graveyard move pauses on
`Pending.chooseReplacement`. -/
def finishSbaSweep (g : Game) (moves : Array SbaGraveyardMove)
    (preBf : Array GameObject) (stage : Nat) (changedIn : Bool := false) :
    Game × (Bool × Bool) := Id.run do
  let mut g := g
  let mut changed := changedIn
  if stage == 0 then
    for i in [0:moves.size] do
      let m := moves[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield && g.isCreature o then
          g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
            (preBattlefield := some preBf)
            (cause := some (.stateBased m.sba))
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := moves.extract (i + 1) moves.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 0), (true, true))
      | none => pure ()
    g := g.change .sbaChecked
  if stage <= 1 then
    -- Planeswalkers with 0 loyalty (CR 704.5i), unless their controller
    -- controls Sanctum Lurker (ruling 778).
    let pwList : Array SbaGraveyardMove :=
      if stage == 1 then moves
      else
        g.battlefield.filterMap (fun o =>
          if g.isPlaneswalker o && o.status.loyaltyCounters == 0 &&
              !g.planeswalkersSurviveZeroLoyalty (g.controllerOf o) then
            some {
              objectId := o.id
              reason := s!"{g.name o} is put into its owner's graveyard (0 loyalty, CR 704.5i)"
              sba := .zeroLoyalty
            }
          else none)
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
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 1), (true, true))
      | none => pure ()
    -- Legend rule (CR 704.5j): pause so the controller chooses one to keep.
    match g.firstLegendRuleChoice? with
    | some (p, name, ids) =>
      g := g.change (.pending (.chooseLegend p name ids))
      g := g.logMsg
        s!"{(g.player p).name} chooses which {name} to keep (legend rule, CR 704.5j)"
      return (g, (true, true))
    | none => pure ()
    -- Tokens in zones other than the battlefield cease to exist (CR 704.5d).
    for o in g.objects do
      if o.printed.isToken && o.zone != .battlefield then
        g := g.ceaseToExist o.id (cause := some (.stateBased .tokenOutsideBattlefield))
        g := g.logMsg s!"{o.name} ceases to exist (token left the battlefield)"
        changed := true
  if stage <= 2 then
    -- Saga with lore at or past its final chapter and no chapter on the
    -- stack is sacrificed (CR 714.4 / 704.5s).
    let sagaList : Array SbaGraveyardMove :=
      if stage == 2 then moves
      else
        g.battlefield.filterMap (fun o =>
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
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 2), (true, true))
      | none => pure ()
  if stage <= 3 then
    -- Unattached or illegally attached Auras (CR 704.5m).
    let auraList : Array SbaGraveyardMove :=
      if stage == 3 then moves
      else
        g.battlefield.filterMap (fun o =>
          if !g.isAura o then none
          else
            let legal :=
              match o.attachedTo.bind g.findObject? with
              | some host => g.auraObjCanEnchant host o
              | none => false
            if !legal then
              some {
                objectId := o.id
                reason := s!"{g.name o} is put into its owner's graveyard (CR 704.5n)"
                sba := .illegalAura
              }
            else none)
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
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf 3), (true, true))
      | none => pure ()
  -- Illegally attached Equipment (CR 704.5n). Unattached Equipment stays.
  for o in g.battlefield do
    if g.isEquipment o then
      let legal :=
        match o.attachedTo.bind g.findObject? with
        | some host => host.isOnBattlefield && g.isCreature host
        | none => true
      if !legal then
        let hostId := o.attachedTo.getD ⟨0⟩
        g := g.record (GameEvent.unattached g.turnNumber (g.snapshot o) hostId
          (cause := .stateBased .illegalEquipmentOrFortification))
        g := g.logMsg s!"{g.name o} becomes unattached (CR 704.5n)"
        changed := true
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
      -- CR 704.5q: +1/+1 and -1/-1 counters on one permanent are removed in
      -- pairs.
      for o in g.battlefield do
        let k := Nat.min o.status.plusOnePlusOne o.status.minusOneMinusOne
        if k > 0 then
          let cause := EventCause.stateBased .counterAnnihilation
          g := g.record (GameEvent.counters g.turnNumber none (g.snapshot o) .plusOnePlusOne k true
            (cause := cause))
          g := g.record (GameEvent.counters g.turnNumber none (g.snapshot (g.object! o.id)) .minusOneMinusOne k true
            (cause := cause))
          g := g.logMsg s!"{k} +1/+1 and -1/-1 counter pair(s) are removed from {o.name}"
          changed := true
      -- Creatures with 0 toughness or lethal damage (CR 704.5f–h).
      -- Snapshot the battlefield before moving dying creatures so a
      -- simultaneous death of Head of the Hunt still exiles opposing creatures (CR 614.6).
      let preBf := g.battlefield
      let victims : Array SbaGraveyardMove :=
        g.battlefield.filterMap (fun o =>
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
      return g.finishSbaSweep victims preBf 0 (changedIn := changed)
    if let .chooseReplacement .. := g.pending then
      (g.chainPendingReplacement .checkSBA, true)
    else if paused then (g, changed)
    else if changed then
      let (g', _) := checkSBACounted g
      (g', true)
    else (g, false)

def checkSBA (g : Game) : Game :=
  let g := (g.checkSBACounted).1
  if g.over || g.pending != .none then g
  else
    let g := g.leavePlayersWhoLost
    if g.over || g.pending != .none then g
    else (g.checkSBACounted).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3 / 603.3b,
514.3a). All triggered abilities wait until a player would receive priority. -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingTriggers.isEmpty

end Game
end Mtg.Engine
