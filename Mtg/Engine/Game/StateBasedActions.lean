import Mtg.Engine.Game.Leaving

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

/-- All legend-rule groups that need a choice (CR 704.5j / 201.2a): two or
more legendary permanents with the same name controlled by the same player,
taking players in APNAP order. When `onlyIds` is supplied, restricts candidate
permanents to those present at the start of the SBA pass (CR 704.3). -/
def legendRuleGroups (g : Game)
    (onlyIds : Option (Array ObjectId) := none) :
    Array (PlayerId × String × Array ObjectId) :=
  Id.run do
    let mut out : Array (PlayerId × String × Array ObjectId) := #[]
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
            out := out.push (p, nm, group.map (·.id))
    return out

/-- First legend-rule group that needs a choice (CR 704.5j / 201.2a): two or
more legendary permanents with the same name controlled by the same player,
taking players in APNAP order. When `onlyIds` is supplied, restricts candidate
permanents to those present at the start of the SBA pass (CR 704.3). -/
def firstLegendRuleChoice? (g : Game)
    (onlyIds : Option (Array ObjectId) := none) :
    Option (PlayerId × String × Array ObjectId) :=
  (g.legendRuleGroups onlyIds)[0]?

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

/-- Reconstruct the pre-batch board state when `o.id` already existed on the
battlefield at the start of an enclosing simultaneous batch (CR 608.2c / 701.8b). -/
private def preBatchDestroyCheck (g : Game) (o : GameObject) : Game × GameObject :=
  if g.currentBatch.isSome && !g.openBatchObjects.isEmpty then
    let preG : Game :=
      { g with
        objects := g.openBatchObjects
        players := g.openBatchPlayers
        activeEffects := g.openBatchEffects
        stack := g.openBatchStack }
    match preG.findObject? o.id with
    | some preO =>
      if preO.isOnBattlefield then (preG, preO) else (g, o)
    | none => (g, o)
  else (g, o)

/-- Destroy a permanent (CR 701.8). Indestructible permanents aren't destroyed
(CR 702.12b). A shield counter replaces destruction with removing a
shield counter via the CR 616.1 replacement loop (CR 122.1c / 614.6). If it
would die this turn under an exile replacement, `move` sends it to exile instead
of the graveyard (CR 614.1). -/
def destroyPermanent (g : Game) (o : GameObject)
    (cause : Option EventCause := none)
    (preBattlefield : Option (Array GameObject) := none)
    (reason : Option String := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.destroyPermanent o.id cause preBattlefield reason)
  else
  let (checkG, checkO) := g.preBatchDestroyCheck o
  if checkG.hasIndestructible checkO then
    g.logMsg s!"{g.name o} is indestructible and isn't destroyed"
  else
  let ctrl := g.controllerOf o
  let affected := ctrl.getD o.owner
  let mutSpecs : Array ReplacementSpec := Id.run do
    let mut s : Array ReplacementSpec := #[]
    if o.status.shield > 0 then
      s := s.push {
        id := { kind := .shieldCounterDestroy, object := some o.id }
        source := some o.id
        controller := ctrl
        affectedPlayer := affected
        kind := .shieldCounterDestroy o.id
      }
    for (_, eff) in g.activeEffects do
      match eff with
      | .replacement spec d =>
        if g.durationActive d then
          match spec.kind with
          | .shieldCounterDestroy tid =>
            if tid == o.id && o.status.shield > 0 then
              s := s.push { spec with affectedPlayer := affected }
          | _ => pure ()
      | _ => pure ()
    return s
  let candidates := mutSpecs.map (fun s => (ReplacementOrPrevention.replacement s).toCandidate)
  match g.selectNextReplacementStep candidates #[] with
  | .needChoice chooser choices _ =>
    g.promptChooseReplacement chooser choices (.destroyPermanent o.id cause preBattlefield reason)
  | .chosen chosen _ =>
    let g := g.consumeReplacementOrder #[chosen.id]
    let cause' := g.wrapReplacedCause chosen.id cause ctrl
    let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := ctrl)
    let oName := g.name o
    let g := g.record (GameEvent.counters g.turnNumber ctrl (g.snapshot o) .shield 1 true (cause := finalCause))
    g.logMsg s!"A shield counter is removed from {oName} instead of destroying it"
  | .none =>
    g.moveToOwnerGraveyard o (reason.getD s!"{g.name o} is destroyed") (verb := some .destroy)
      (preBattlefield := preBattlefield) (cause := cause)

/-- Execute the remaining permanent-removal and unattachment actions of a
single CR 704.3 state-based action pass inside the currently open batch using
conditions captured at the start of the pass (`.dyingCreatures` = dying creatures,
`.planeswalkersAndLegend` = 0-loyalty planeswalkers + legend rule + tokens/copies
outside valid zones, `.finalChapterSagas` = final-chapter Sagas,
`.illegalAttachments` = illegal Auras + illegal Equipment/creature attachments),
chaining `.finishSbaSweep` if a graveyard move pauses on
`Pending.chooseReplacement`. -/
def finishSbaSweep (g : Game) (moves : Array SbaGraveyardMove)
    (preBf : Array GameObject) (stage : SbaSweepStage)
    (pwMoves : Array SbaGraveyardMove := #[])
    (sagaMoves : Array SbaGraveyardMove := #[])
    (tokensOutsideBf : Array ObjectId := #[])
    (copiesOutside : Array ObjectId := #[])
    (illegalAuras : Array ObjectId := #[])
    (illegalEquips : Array (ObjectId × ObjectId) := #[])
    (illegalCreatureAtts : Array (ObjectId × ObjectId) := #[])
    (legendGroups : Array (PlayerId × String × Array ObjectId) := #[])
    (changedIn : Bool := false) :
    Game × (Bool × Bool) := Id.run do
  let mut g := g
  let mut changed := changedIn
  if stage == .dyingCreatures then
    for i in [0:moves.size] do
      let m := moves[i]!
      match g.findObject? m.objectId with
      | some o =>
        if o.isOnBattlefield then
          if m.verb == some .destroy then
            g := g.destroyPermanent o (cause := some (.stateBased m.sba))
              (preBattlefield := some preBf) (reason := some m.reason)
          else
            g := g.moveToOwnerGraveyard o m.reason (verb := m.verb) (actor := m.actor)
              (preBattlefield := some preBf)
              (cause := some (.stateBased m.sba))
          changed := true
          if let .chooseReplacement _ _ := g.pending then
            let rem := moves.extract (i + 1) moves.size
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .dyingCreatures
              pwMoves sagaMoves tokensOutsideBf copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts legendGroups), (true, true))
      | none => pure ()
    g := g.change .sbaChecked
  if stage == .dyingCreatures || stage == .planeswalkersAndLegend then
    -- Planeswalkers with 0 loyalty captured at start of pass (CR 704.5i).
    let pwList : Array SbaGraveyardMove :=
      if stage == .planeswalkersAndLegend then moves else pwMoves
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
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .planeswalkersAndLegend
              #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
              illegalEquips illegalCreatureAtts legendGroups), (true, true))
      | none => pure ()
    -- Legend rule (CR 704.5j): groups captured at the start of the pass before
    -- `playerLost`, CR 704.5q counter annihilation, `dyingCreatures`, and `pwMoves`
    -- (CR 704.3 / 704.8 / 800.4a). Pause so a living controller chooses one to
    -- keep, chaining the rest of this SBA pass so `keepLegend` finishes the pass
    -- in the same batch before Pass 2 runs (CR 704.3 / 603.2c).
    for gi in [0:legendGroups.size] do
      let (p, name, rawIds) := legendGroups[gi]!
      let ids := rawIds.filter (fun id => (g.findObject? id).any GameObject.isOnBattlefield)
      if ids.size ≥ 2 then
        let restGroups := legendGroups.extract (gi + 1) legendGroups.size
        if !(g.player p).lost then
          g := g.change (.pending (.chooseLegend p name ids))
          g := g.logMsg
            s!"{(g.player p).name} chooses which {name} to keep (legend rule, CR 704.5j)"
          g := g.chainPendingReplacement (.finishSbaSweep #[] preBf .planeswalkersAndLegend
            #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
            illegalEquips illegalCreatureAtts restGroups)
          return (g, (true, true))
        else
          let keptId := g.defaultLegendToKeep ids
          let others := ids.filter (· != keptId)
          if let some kept := g.findObject? keptId then
            g := g.logMsg s!"{(g.player p).name} keeps {g.name kept} (legend rule, CR 704.5j)"
          for oi in [0:others.size] do
            let other := others[oi]!
            match g.findObject? other with
            | some o =>
              if o.isOnBattlefield then
                g := g.moveToOwnerGraveyard o
                  s!"{g.name o} is put into its owner's graveyard (legend rule, CR 704.5j)"
                  (preBattlefield := some preBf)
                  (cause := some (.stateBased .legendRule))
                changed := true
                if let .chooseReplacement _ _ := g.pending then
                  let remOthers := others.extract (oi + 1) others.size
                  let tail := PendingReplacement.finishSbaSweep #[] preBf .planeswalkersAndLegend
                    #[] sagaMoves tokensOutsideBf copiesOutside illegalAuras
                    illegalEquips illegalCreatureAtts restGroups
                  let cont :=
                    if remOthers.isEmpty then tail
                    else .seq (.moveSimultaneousToGraveyard remOthers (some preBf) (some (.stateBased .legendRule))) tail
                  return (g.chainPendingReplacement cont, (true, true))
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
    -- Non-token copies outside stack and battlefield at start of pass cease to exist (CR 704.5e;
    -- FRA ruling 736 exempts a prepared creature's associated spell copy in exile).
    for cid in copiesOutside do
      match g.findObject? cid with
      | some o =>
        if o.isCopy && !o.printed.isToken && o.zone != .stack && o.zone != .battlefield &&
            !(o.zone == .exile && ((g.playPermission o).bind (·.prepareSource)).isSome) then
          g := g.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))
          g := g.logMsg s!"{o.name} ceases to exist (copy outside stack or battlefield, CR 704.5e)"
          changed := true
      | none => pure ()
  if stage != .illegalAttachments then
    -- Saga with lore at or past its final chapter and no chapter on the
    -- stack captured at start of pass is sacrificed (CR 714.4 / 704.5s).
    let sagaList : Array SbaGraveyardMove :=
      if stage == .finalChapterSagas then moves else sagaMoves
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
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .finalChapterSagas
              #[] #[] #[] #[] illegalAuras illegalEquips illegalCreatureAtts), (true, true))
      | none => pure ()
  do
    -- Unattached or illegally attached Auras captured at start of pass (CR 704.5m).
    let auraList : Array SbaGraveyardMove :=
      if stage == .illegalAttachments then moves
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
            return (g.chainPendingReplacement (.finishSbaSweep rem preBf .illegalAttachments
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
  if g.over || g.sbaPaused then (g, false)
  else
    let (g, (changed, _paused)) := g.withBatchReturn none fun g => Id.run do
      let mut g := g
      let mut changed := false
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
            o.isOnBattlefield && !(g.player p).lost &&
              (if g.currentBatch.isSome then true
               else g.controlledBy o p && g.treatedAsLegendary o && g.name o == name)
          | none => false)
        if still.size ≥ 2 then
          return (g, (changed, true))
        else
          g := g.change (.pending .none)
      | _ => pure ()
      -- Capture all applicable CR 704.5 state-based actions simultaneously
      -- against the start-of-pass state BEFORE recording `GameEvent.playerLost`
      -- or applying CR 704.5q counter annihilation so a player losing in this
      -- pass does not alter battlefield control or continuous effects mid-pass
      -- (CR 704.3 / 800.4a), simultaneous 0-toughness death LKI retains its
      -- pre-annihilation counters, and Pass 1 does not sweep newly dead tokens
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
      let legendGroups : Array (PlayerId × String × Array ObjectId) :=
        g.legendRuleGroups (some (preBf.map (·.id)))
      let tokensOutsideBf : Array ObjectId :=
        g.objects.filterMap (fun o =>
          if o.printed.isToken && o.zone != .battlefield then some o.id else none)
      let copiesOutside : Array ObjectId :=
        g.objects.filterMap (fun o =>
          if o.isCopy && !o.printed.isToken && o.zone != .stack && o.zone != .battlefield &&
              !(o.zone == .exile && ((g.playPermission o).bind (·.prepareSource)).isSome) then
            some o.id
          else none)
      let sagaMoves : Array SbaGraveyardMove :=
        preBf.filterMap (fun o =>
          if g.hasSubtype o .saga && g.retainsPrintedAbilities o then
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
            | _, _ => none
          else none)
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
      -- Players losing (CR 704.5a–c / 704.6a–b / 810.8a,c,d / 810.11). They
      -- leave after this SBA pass if the game continues (CR 800.4 / 800.4a).
      let hasCantLose (g : Game) (pid : PlayerId) : Bool :=
        (g.permanentsOf pid).any (fun o =>
          (g.baseCard o).cantLoseGame && g.retainsPrintedAbilities o) ||
        (g.objects.filter (fun o =>
          o.zone == .command && g.controlledBy o pid)).any (fun o =>
            (g.baseCard o).cantLoseGame && g.retainsPrintedAbilities o)
      for pl in g.players do
        let curPl := g.player pl.id
        if !curPl.lost then
          let shielded :=
            hasCantLose g pl.id ||
              g.livingPlayers.any (fun mate =>
                g.areTeammates pl.id mate.id && hasCantLose g mate.id)
          if shielded then
            pure ()
          else
            let team := g.teamMembers pl.id
            let poisonThreshold :=
              if team.size ≤ 1 then 10 else 10 + 5 * (team.size - 1)
            let poisonLoss := g.teamPoison pl.id ≥ poisonThreshold
            let loss? : Option (LossReason × StateBasedAction) :=
              if curPl.life ≤ 0 then some (.lifeZeroOrLess, .lifeZeroOrLess)
              else if g.drewFromEmpty pl.id then some (.decked, .drewFromEmpty)
              else if poisonLoss then some (.poison, .tenPoison)
              else none
            match loss? with
            | none => pure ()
            | some (lossReason, sbaKind) =>
              g := g.record (GameEvent.playerLost g.turnNumber pl.id lossReason
                (cause := some (.stateBased sbaKind)))
              let detail :=
                match lossReason with
                | .lifeZeroOrLess => s!"life total {curPl.life}"
                | .decked => "drew from empty library"
                | .poison => "poison"
                | _ => "state-based action"
              g := g.logMsg s!"{curPl.name} loses the game ({detail})"
              for mate in g.players do
                if mate.id != pl.id && !(g.player mate.id).lost && g.areTeammates pl.id mate.id then
                  g := g.record (GameEvent.playerLost g.turnNumber mate.id lossReason
                    (cause := some (.stateBased sbaKind)))
                  g := g.logMsg s!"{mate.name} loses the game (teammate lost; CR 810.8a)"
              changed := true
      match g.decideGameIfFinished with
      | some finished => return (finished, (true, true))
      | none => pure ()
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
      return g.finishSbaSweep victims preBf .dyingCreatures pwMoves sagaMoves tokensOutsideBf
        copiesOutside illegalAuras illegalEquips illegalCreatureAtts legendGroups
        (changedIn := changed)
    match g.pending with
    | .chooseReplacement .. | .chooseLegend .. =>
      (g.chainPendingReplacement .checkSBA, true)
    | _ =>
      (g, changed)

/-- Repeat `checkSBACounted` and `leavePlayersWhoLost` until neither performs an
action or the game ends / pauses on a pending choice (CR 704.3 / 800.4a). -/
partial def checkSBACountedWithLeaves (g : Game) : Game × Bool :=
  let (g, didSba) := g.checkSBACounted
  if g.over || g.pending != .none then (g, didSba)
  else
    let leftBefore := (g.players.filter (·.leftTheGame)).size
    let g := g.leavePlayersWhoLost
    let anyLeft := (g.players.filter (·.leftTheGame)).size > leftBefore
    if g.over then (g, didSba || anyLeft)
    else if g.sbaPaused then (g.chainPendingReplacement .checkSBA, true)
    else if g.pending != .none then (g, didSba || anyLeft)
    else if didSba || anyLeft then
      let (g', didMore) := g.checkSBACountedWithLeaves
      (g', didSba || anyLeft || didMore)
    else (g, false)

def checkSBA (g : Game) : Game :=
  (g.checkSBACountedWithLeaves).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3 / 603.3b,
514.3a). All triggered abilities wait until a player would receive priority. -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingTriggers.isEmpty

end Game
end Mtg.Engine
