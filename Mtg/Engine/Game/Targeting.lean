import Mtg.Engine.Game.Timing

/-!
# Legal targets (CR 115)

Hexproof- and protection-aware target legality driven by unified `TargetSpec` /
`TargetSlot` / `TargetDomain` evaluated through `EvalExpr`: legal permanent,
graveyard-card, stack-spell, stack-ability, player, and multi-slot targets,
group constraints (`GroupTargetConstraint`), and `"for each opponent"` slot
expansion (CR 115.1, 115.3–5, 601.2c, 603.3d, 702.11, 702.16).
-/

namespace Mtg.Engine
namespace Game

/-- Whether `caster` may target `o` (CR 115.1, 702.11b, 702.16b, 810.5). -/
def canBeTargetedBy (g : Game) (caster : PlayerId) (o : GameObject)
    (sourceId : Option ObjectId := none) : Bool :=
  let srcBlocked :=
    match g.targetingSourceObject? sourceId with
    | some src => g.protectedFrom o src
    | none => false
  (!g.hasHexproof o || g.controlledBy o caster ||
      (g.controllerOf o).any (g.areTeammates · caster)) && !srcBlocked

/-- Player targets `caster` may choose. A player with hexproof or protection is
not a legal target when prohibited (CR 702.11c / 702.16b). -/
def legalPlayerTargets (g : Game) (caster : PlayerId) (ps : Array Player)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.playerTargets (ps.filter (fun pl => g.playerCanBeTargetedBy caster pl.id sourceId))

/-- Battlefield permanents matching `pred` that `caster` may target. -/
def legalPermanentTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.battlefield.filter (fun o => pred o && g.canBeTargetedBy caster o sourceId)
    |>.map (fun o => Target.permanent o.id)

/-- Cards in `p`'s graveyard matching `pred` (CR 404 / 115.1). Hexproof does
not apply off the battlefield (CR 702.11b). -/
def legalGraveyardCardTargets (g : Game) (p : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  (g.player p).graveyard.filterMap (fun id =>
    match g.findObject? id with
    | some o => if pred o then some (Target.card o.id) else none
    | none => none)

/-- Spells on the stack matching `pred` (not activated or triggered abilities). -/
def stackSpells (g : Game) (pred : GameObject → Bool := fun _ => true) : Array GameObject :=
  g.stack.filterMap (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      if o.abilityEffect.isNone && o.triggeredAbility.isNone && pred o then some o
      else none
    | none => none)

/-- Legal spell-on-the-stack targets matching `pred` (CR 115.1 / 115.5). -/
def legalStackSpellTargets (g : Game) (pred : GameObject → Bool)
    (excludeId : Option ObjectId := none) : Array Target :=
  let selfId := excludeId.orElse (fun _ => g.proposedSpell.map (·.spellId))
  g.stackSpells (fun o => some o.id != selfId && pred o) |>.map (fun o => Target.card o.id)

/-- Whether this target is a spell on the stack that `p` controls. -/
def isOwnStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o => o.zone == .stack && g.controlledBy o p)
  | _ => false

/-- Whether this target is a spell on the stack an opponent of `p` controls. -/
def isOppStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o =>
      o.zone == .stack && (g.livingOpponents p).any (fun pl => g.controlledBy o pl.id))
  | _ => false

/-- Whether `o` has card type `t`, counting type-changing effects on
permanents. -/
def objectHasCardType (g : Game) (o : GameObject) (t : CardType) : Bool :=
  g.hasType o t

/-- Whether the spell being cast or resolved paid its teamwork cost (CR 601.2 / 608.2 / 707.10).
Checks an active `proposedSpell` first (including mid-resolution casts), then an
active spell-copy retargeting prompt (`.newTargetsForCopies` / `.newTargetsForCopySlot`,
MSH Ruling 365), then `resolvingSpell`. -/
def spellPaidTeamwork (g : Game) : Bool :=
  match g.proposedSpell with
  | some prop => prop.teamworkPaid || g.teamworkPaid prop.spellId
  | none =>
    let copyTargetId? : Option ObjectId :=
      match g.pending with
      | .resolutionChoice _ (.newTargetsForCopies copies)
      | .resolutionChoice _ (.newTargetsForCopySlot copies ..) => copies[0]?
      | _ => none
    match copyTargetId?.orElse (fun _ => g.resolvingSpell) with
    | some id => g.teamworkPaid id
    | none => false

/-! ### Unified `TargetDomain` / `TargetSlot` / `TargetSpec` Evaluation (CR 115) -/

private def pushUniqueTarget (acc : Array Target) (t : Target) : Array Target :=
  if acc.contains t then acc else acc.push t

/-- Resolve conditional domain relaxation (`altDomainIf?`, e.g. Teamwork
relaxation during CR 601.2b–c, copy retargeting, or resolution). -/
def effectiveSlotDomain (g : Game) (caster : PlayerId) (slot : TargetSlot)
    (sourceId : Option ObjectId := none) : TargetDomain :=
  match slot.altDomainIf? with
  | none => slot.domain
  | some (cond, altDomain) =>
    let copyTargetId? : Option ObjectId :=
      match g.pending with
      | .resolutionChoice _ (.newTargetsForCopies copies)
      | .resolutionChoice _ (.newTargetsForCopySlot copies ..) => copies[0]?
      | _ => none
    let effSource :=
      sourceId.orElse fun _ =>
        (g.proposedSpell.map (·.spellId)).orElse fun _ =>
          copyTargetId?.orElse fun _ => g.resolvingSpell
    let env : EvalEnv := { controller := caster, sourceId := effSource }
    if EvalExpr.evalCondition g env cond then altDomain else slot.domain

/-- Legal targets matching a `TargetDomain` (CR 115.1 / 115.4 / 115.5 / 702.11 / 702.16).
`sourceId` identifies the source object for `"another"` and protection (CR 702.16b);
`stackSelfId` identifies the stack spell, ability, or copy whose targets are being
checked so it cannot target itself under CR 115.5. -/
partial def legalTargetsForDomain (g : Game) (caster : PlayerId) (domain : TargetDomain)
    (sourceId : Option ObjectId := none)
    (stackSelfId : Option ObjectId := none) : Array Target :=
  let env : EvalEnv := { controller := caster, sourceId }
  let selfStackId : Option ObjectId :=
    stackSelfId.orElse fun _ =>
      let stackSource? := sourceId.bind fun sid =>
        match g.findObject? sid with
        | some o => if o.zone == .stack then some o.id else none
        | none => none
      stackSource?.orElse fun _ =>
        match g.proposedSpell with
        | some prop =>
          if sourceId.isNone || prop.sourceId == sourceId then some prop.spellId else none
        | none => none
  match domain with
  | .player pf =>
    let ps := g.livingPlayers.filter fun pl =>
      EvalExpr.matchesPlayerFilter g env pf pl.id
    g.legalPlayerTargets caster ps sourceId
  | .anyTarget rp =>
    -- CR 115.4: "any target" is a creature, planeswalker, battle, or player.
    match rp with
    | .any =>
      g.legalPlayerTargets caster g.livingPlayers sourceId ++
        g.legalPermanentTargets caster (fun o =>
          o.isOnBattlefield && (g.isCreature o || g.isPlaneswalker o || g.isBattle o)) sourceId
    | .otherThan ref =>
      let excludeIds := EvalExpr.resolveRefIds g env ref
      g.legalPlayerTargets caster g.livingPlayers sourceId ++
        g.legalPermanentTargets caster (fun o =>
          o.isOnBattlefield && !excludeIds.contains o.id &&
            (g.isCreature o || g.isPlaneswalker o || g.isBattle o)) sourceId
    | .filtered objPred pf =>
      let ps := g.livingPlayers.filter fun pl =>
        EvalExpr.matchesPlayerFilter g env pf pl.id
      g.legalPlayerTargets caster ps sourceId ++
        g.legalPermanentTargets caster (fun o =>
          o.isOnBattlefield && (g.isCreature o || g.isPlaneswalker o || g.isBattle o) &&
            EvalExpr.evalObjectPred g env (.live o) objPred) sourceId
  | .stackAbility ctrl srcPred =>
    g.stack.filterMap fun e =>
      match g.findObject? e.objectId with
      | none => none
      | some o =>
        if o.zone == .stack && some o.id != selfStackId &&
            (o.abilityEffect.isSome || o.triggeredAbility.isSome) &&
            (g.controllerOf o).any (EvalExpr.matchesPlayerFilter g env ctrl) then
          match o.sourceId.bind g.damageSourceById? with
          | some src =>
            if EvalExpr.evalObjectPred g env (.live src) srcPred then some (Target.card o.id)
            else none
          | none => none
        else none
  | .object zs pred =>
    let ownerOk (o : GameObject) : Bool :=
      match zs.owner with
      | .any => true
      | .matching pf => EvalExpr.matchesPlayerFilter g env pf o.owner
      | .ofPlayer pe => (EvalExpr.evalPlayer g env pe).contains o.owner
    let matchingOwners : Array PlayerId :=
      match zs.owner with
      | .any => g.livingPlayers.map (·.id)
      | .matching pf =>
        (g.livingPlayers.filter fun pl => EvalExpr.matchesPlayerFilter g env pf pl.id).map (·.id)
      | .ofPlayer pe => EvalExpr.evalPlayer g env pe
    let collectZone (zk : ZoneKind) : Array Target :=
      match zk with
      | .battlefield =>
        g.legalPermanentTargets caster (fun o =>
          o.isOnBattlefield && ownerOk o && EvalExpr.evalObjectPred g env (.live o) pred) sourceId
      | .stack =>
        g.stack.filterMap fun e =>
          match g.findObject? e.objectId with
          | some o =>
            if o.zone == .stack && some o.id != selfStackId && ownerOk o &&
                EvalExpr.evalObjectPred g env (.live o) pred then
              some (Target.card o.id)
            else none
          | none => none
      | .graveyard =>
        matchingOwners.foldl (fun acc pid =>
          acc ++ g.legalGraveyardCardTargets pid (fun o =>
            EvalExpr.evalObjectPred g env (.live o) pred)) #[]
      | .hand =>
        matchingOwners.foldl (fun acc pid =>
          acc ++ (g.player pid).hand.filterMap fun id =>
            match g.findObject? id with
            | some o => if EvalExpr.evalObjectPred g env (.live o) pred then some (Target.card o.id) else none
            | none => none) #[]
      | .library =>
        matchingOwners.foldl (fun acc pid =>
          acc ++ (g.player pid).library.filterMap fun id =>
            match g.findObject? id with
            | some o => if EvalExpr.evalObjectPred g env (.live o) pred then some (Target.card o.id) else none
            | none => none) #[]
      | .exile =>
        g.objects.filterMap fun o =>
          if o.zone == .exile && ownerOk o && EvalExpr.evalObjectPred g env (.live o) pred then
            some (Target.card o.id)
          else none
      | .command =>
        g.objects.filterMap fun o =>
          if o.zone == .command && ownerOk o && EvalExpr.evalObjectPred g env (.live o) pred then
            some (Target.card o.id)
          else none
      | .ante | .outside => #[]
    zs.zones.foldl (fun acc zk =>
      (collectZone zk).foldl pushUniqueTarget acc) #[]
  | .anyOf ds =>
    ds.foldl (fun acc d =>
      (g.legalTargetsForDomain caster d sourceId stackSelfId).foldl pushUniqueTarget acc) #[]

/-- Legal single-target candidates for one `TargetSlot`, accounting for
conditional domain overrides (`altDomainIf?`). -/
def legalTargetsForSlot (g : Game) (caster : PlayerId) (slot : TargetSlot)
    (sourceId : Option ObjectId := none)
    (stackSelfId : Option ObjectId := none) : Array Target :=
  g.legalTargetsForDomain caster (g.effectiveSlotDomain caster slot sourceId) sourceId stackSelfId

private def targetObject? (g : Game) : Target → Option GameObject
  | .permanent oid | .card oid => g.findObject? oid
  | .player _ => none

private def targetManaValue (g : Game) (t : Target) : Nat :=
  ((g.targetObject? t).map g.objectManaValue).getD 0

private def canAssignDistinctCardTypes : List (Array CardType) → Array CardType → Bool
  | [], _ => true
  | ts :: rest, used =>
    ts.any fun ty => !used.contains ty && canAssignDistinctCardTypes rest (used.push ty)

/-- Whether a tuple of chosen targets jointly satisfies `gc` (CR 115.3 / 205.2 / 601.2c).
Monotone under adding targets to a partial tuple, so it can be used both for
complete-tuple validation and for backtracking pruning. -/
def satisfiesGroupConstraint (g : Game) (caster : PlayerId) (sourceId : Option ObjectId)
    (gc : GroupTargetConstraint) (targets : Array Target) : Bool :=
  if targets.isEmpty then true
  else
    match gc with
    | .totalManaValueAtMost capExpr =>
      let env : EvalEnv := { controller := caster, sourceId }
      let capVal := EvalExpr.evalValue g env capExpr
      let cap : Nat := if capVal < 0 then 0 else capVal.toNat
      let total := targets.foldl (fun acc t => acc + g.targetManaValue t) 0
      total ≤ cap
    | .shareCharacteristic char =>
      let objs := targets.filterMap g.targetObject?
      if objs.size != targets.size then false
      else
        match char with
        | .color =>
          Color.all.any fun c => objs.all fun o => (g.colors o).contains c
        | .cardType =>
          match objs[0]? with
          | none => true
          | some o0 => (g.types o0).any fun ty => objs.all fun o => (g.types o).contains ty
        | .creatureType =>
          match objs[0]? with
          | none => true
          | some o0 =>
            ((g.subtypes o0).filter CardSubtype.isCreatureType).any fun s =>
              objs.all fun o => (g.subtypes o).contains s
        | .subtype =>
          match objs[0]? with
          | none => true
          | some o0 => (g.subtypes o0).any fun s => objs.all fun o => (g.subtypes o).contains s
        | .name =>
          -- CR 201.2a: nameless face-down permanents have no name and never share a name.
          match objs[0]? with
          | none => true
          | some o0 =>
            let nm := g.name o0
            !nm.isEmpty && objs.all fun o => g.name o == nm
    | .distinctControllers =>
      let ctrls : Array PlayerId := targets.filterMap fun t =>
        match t with
        | .player p => some p
        | .permanent oid | .card oid =>
          (g.findObject? oid).map fun o => (g.controllerOf o).getD o.owner
      ctrls.size == targets.size && ctrls.toList.eraseDups.length == ctrls.size
    | .distinctNames =>
      -- CR 201.2a: nameless face-down permanents have no name and never share a name.
      let named := targets.filterMap fun t =>
        match g.targetObject? t with
        | some o =>
          let nm := g.name o
          if nm.isEmpty then none else some nm
        | none => none
      named.toList.eraseDups.length == named.size
    | .distinctCardTypes =>
      let typeSets : Array (Array CardType) := targets.map fun t =>
        match g.targetObject? t with
        | some o => g.types o
        | none => #[]
      canAssignDistinctCardTypes typeSets.toList #[]

/-- Backtracking solver for a partial or complete flat-position assignment over
`spec` honoring CR 115.3 pairwise distinctness (`spec.distinctPosGroups`) and all
intra- and cross-slot `GroupTargetConstraint`s (`spec.constraintPosGroups`).
Optional positions (`spec.isOptionalPos pos`) may remain unassigned (CR 115.1c). -/
def findValidAssignment (g : Game) (caster : PlayerId) (sourceId : Option ObjectId)
    (spec : TargetSpec) :
    List (Nat × Array Target) → Array (Nat × Target) → Option (Array (Nat × Target))
  | [], chosen => some chosen
  | (pos, part) :: rest, chosen =>
    let distinctGrps := spec.distinctPosGroups
    let constraintGrps := spec.constraintPosGroups
    let compatible (t : Target) : Bool :=
      chosen.all (fun (j, u) =>
        !(u == t && distinctGrps.any (fun grp => grp.contains pos && grp.contains j))) &&
      constraintGrps.all (fun (gc, grp) =>
        if !grp.contains pos then true
        else
          let inGrp := (chosen.filter fun (j, _) => grp.contains j).map (·.2)
          g.satisfiesGroupConstraint caster sourceId gc (inGrp.push t))
    let fromPick :=
      part.findSome? fun t =>
        if compatible t then
          g.findValidAssignment caster sourceId spec rest (chosen.push (pos, t))
        else none
    match fromPick with
    | some ans => some ans
    | none =>
      if spec.isOptionalPos pos then
        g.findValidAssignment caster sourceId spec rest chosen
      else none

/-- Whether required flat positions `rest` of `spec` can each be given a target
from their candidate list, extending `chosen`, while satisfying CR 115.3
distinctness and every `GroupTargetConstraint` (CR 115.1c / 601.2c). -/
def slotAssignmentExists (g : Game) (caster : PlayerId) (sourceId : Option ObjectId)
    (spec : TargetSpec) (rest : List (Nat × Array Target))
    (chosen : Array (Nat × Target)) : Bool :=
  (g.findValidAssignment caster sourceId spec rest chosen).isSome

/-- Find `count` distinct legal targets in `candidates` satisfying an optional
`GroupTargetConstraint` (used by the demonstration agent for constrained
multi-target `"target"` words like `twoNonlandsSharingType`). -/
def findValidTargetsForCount (g : Game) (caster : PlayerId) (sourceId : Option ObjectId)
    (candidates : Array Target) (count : Nat)
    (gc? : Option GroupTargetConstraint) : Option (Array Target) :=
  let rec go (need : Nat) (startIdx : Nat) (picked : Array Target) : Option (Array Target) :=
    match need with
    | 0 => some picked
    | k + 1 =>
      Id.run do
        for idx in [startIdx:candidates.size] do
          let t := candidates[idx]!
          if !picked.contains t then
            let next := picked.push t
            let ok :=
              match gc? with
              | some gc => g.satisfiesGroupConstraint caster sourceId gc next
              | none => true
            if ok then
              if let some ans := go k (idx + 1) next then
                return some ans
        return none
  go count 0 #[]

/-- Expand any `forEach?` slot (`"for each opponent, ..."` / `"for each player, ..."`)
into one concrete per-seat `TargetSlot` per matching player (CR 601.2c / 602.2b).
When `stackObjId` has a recorded `CastEvent.proposed` / `TriggerQueueEvent.putOnStack`,
preserves players who were in the game at announcement so mid-stack departures do
not shift slot indices. -/
def expandForEachSpec (g : Game) (p : PlayerId) (spec : TargetSpec)
    (allowsZero : Bool := false) (stackObjId : Option ObjectId := none) : TargetSpec :=
  if !spec.slots.any (·.forEach?.isSome) then spec
  else
    let propIdx? :=
      stackObjId.bind fun oid =>
        let rootId := GameEvent.rootCopiedSpellId g.events oid
        g.events.findIdx? fun ev =>
          match ev.change with
          | .rules (.cast (.proposed sid ..))
          | .rules (.triggerQueue (.putOnStack sid ..)) => sid == rootId
          | _ => false
    let inGameAtAnnouncement (pl : Player) : Bool :=
      match propIdx? with
      | some idx =>
        let later := g.events.extract (idx + 1) g.events.size
        g.stillInGame pl.id || later.any fun ev =>
          match ev.change with
          | .rules (.player (.lost q _)) | .rules (.player (.leftGame q)) => q == pl.id
          | _ => false
      | none => g.stillInGame pl.id
    Id.run do
      let mut outSlots : Array TargetSlot := #[]
      let mut slotMap : Array (Array Nat) := #[]
      for slot in spec.slots do
        let startIdx := outSlots.size
        match slot.forEach? with
        | some pf =>
          let matchesForEach (pl : Player) : Bool :=
            inGameAtAnnouncement pl &&
              (match pf.relation with
               | .anyPlayer => true
               | .you => pl.id == p
               | .opponent => pl.id != p && !g.areTeammates p pl.id
               | .teammate => pl.id != p && g.areTeammates p pl.id) &&
              (pf.pred == .any || EvalExpr.evalPlayerPred g { controller := p } pl.id pf.pred)
          let matched := g.players.filter matchesForEach
          let count :=
            if allowsZero then CountRange.ofBounds 0 (max 1 slot.count.maxCount)
            else slot.count
          for pl in matched do
            outSlots := outSlots.push { slot with
              domain := slot.domain.substituteForEach pf (.seat pl.id.idx)
              count
              forEach? := none }
        | none =>
          outSlots := outSlots.push slot
        let endIdx := outSlots.size
        slotMap := slotMap.push ((List.range (endIdx - startIdx)).toArray.map (· + startIdx))
      let outCross := spec.crossSlotConstraints.filterMap fun c =>
        let mapped := c.slots.foldl (fun acc si => acc ++ (slotMap[si]?.getD #[])) #[]
        if mapped.size > 1 then some { c with slots := mapped } else none
      return { slots := outSlots, crossSlotConstraints := outCross }

/-- Legal targets for a unified `TargetSpec` (CR 115.1 / 115.3 / 115.5 / 601.2c / 603.3d).
Returns `#[]` when required slots cannot all be filled simultaneously while
respecting CR 115.3 distinctness and `GroupTargetConstraint`s. -/
@[export mtg_game_legal_targets_for_spec]
def legalTargetsForSpec (g : Game) (caster : PlayerId) (spec : TargetSpec)
    (sourceId : Option ObjectId := none)
    (stackSelfId : Option ObjectId := none) : Array Target :=
  let spec := g.expandForEachSpec caster spec (stackObjId := stackSelfId)
  match spec.slots.toList with
  | [] => #[]
  | [slot] =>
    let raw := g.legalTargetsForSlot caster slot sourceId stackSelfId
    let cands :=
      match slot.groupConstraint? with
      | some gc => raw.filter fun t => g.satisfiesGroupConstraint caster sourceId gc #[t]
      | none => raw
    let minReq := slot.minCount
    if minReq <= 1 then
      if minReq == 0 || !cands.isEmpty then cands else #[]
    else
      let indexed := (List.range minReq).map fun pos => (pos, cands)
      if g.slotAssignmentExists caster sourceId spec indexed #[] then cands else #[]
  | _ =>
    let slotCands : Array (Array Target) :=
      spec.slots.map fun s =>
        let raw := g.legalTargetsForSlot caster s sourceId stackSelfId
        match s.groupConstraint? with
        | some gc => raw.filter fun t => g.satisfiesGroupConstraint caster sourceId gc #[t]
        | none => raw
    let totalPos := spec.totalPositions
    let indexed := (List.range totalPos).map fun pos =>
      (pos, slotCands[spec.slotIndexOfPos pos]!)
    if g.slotAssignmentExists caster sourceId spec indexed #[] then
      slotCands.foldl (· ++ ·) #[]
    else #[]

/-- Expand `"for each opponent, ..."` and `"for each player, ..."` (`forEach?`)
slots on `e` into one concrete per-seat `TargetSlot` per matching player
(CR 601.2c / 602.2b). -/
def expandEachOpponentEffect (g : Game) (p : PlayerId) (e : Effect)
    (stackObjId : Option ObjectId := none) : Effect :=
  if !e.targets.slots.any (·.forEach?.isSome) then e
  else
    let expandedSpec := g.expandForEachSpec p e.targets e.allowsZeroTargets stackObjId
    { e with targets := expandedSpec }

/-- Whether enough distinct legal targets exist for `e` (CR 115.3 / 115.5 / 601.2c):
delegates directly to `legalTargetsForSpec` over `e.effectiveTargetSpec` after
expanding `forEach?` slots. -/
def effectHasEnoughTargets (g : Game) (p : PlayerId) (e : Effect)
    (sourceId : Option ObjectId := none)
    (stackSelfId : Option ObjectId := none) : Bool :=
  let e := g.expandEachOpponentEffect p e stackSelfId
  let spec := e.effectiveTargetSpec
  if spec.isEmpty || e.allowsZeroTargets || spec.allowsZero then true
  else !(g.legalTargetsForSpec p spec sourceId stackSelfId).isEmpty

/-- Legal targets for a triggered ability (CR 603.3d / 601.2c). `sourceId` is
the object that generated the ability, used to exclude “another” creature. -/
def legalTriggerTargets (g : Game) (p : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none)
    (stackSelfId : Option ObjectId := none) : Array Target :=
  g.legalTargetsForSpec p ab.targetSpec sourceId stackSelfId

end Game
end Mtg.Engine
