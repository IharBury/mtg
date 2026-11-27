import Mtg.Engine.Game.Entering

/-!
# Activation costs (CR 601.2h / 602.2b)

Paying life (CR 118.3b), the source's own costs ({T}, sacrificing or
discarding it, counters), and costs paid with objects the player chooses:
sacrificing, discarding, exiling, or tapping them.
-/

namespace Mtg.Engine
namespace Game

/-- Forward reference to `Decisions.reverseProposedSpell` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_reverse_proposed_spell"]
private opaque reverseProposedSpellFwd (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none)
    (alwaysGrantPriority : Bool := false)
    (skipDepartureReconcile : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game := g

/-- Forward reference to `ManaAbilities.canTapForPlainMana` (resolved at link time via `@[export]`). -/
@[extern "mtg_game_can_tap_for_plain_mana"]
private opaque canTapForPlainManaFwd (g : Game) (p : PlayerId) (o : GameObject) : Bool := false

/-- Remove an indestructible counter as a cost (ruling 357). -/
def payRemoveIndestructibleCounter (g : Game) (o : GameObject)
    (forObject : Option ObjectId := none)
    (deferPlayFromExileLogs : Bool := false) : Except String Game := do
  if o.status.indestructibleCounters == 0 then
    throw s!"{g.name o} has no indestructible counter"
  let oName := g.name o
  let ctrl := g.controllerOf o
  let p := ctrl.getD o.owner
  let g := g.recordRemoveCounters o.id .indestructible 1 (byPlayer := ctrl) (noActor := ctrl.isNone)
    (cause := some (.costPayment .removeCounters p forObject))
    (deferPlayFromExileLogs := deferPlayFromExileLogs)
  return g.logMsg s!"{oName} loses an indestructible counter"

/-- Pay `n` life as a cost (CR 118.3b / 119.4 / 119.8). Payment of life is not damage. -/
def payLifeCost (g : Game) (p : PlayerId) (n : Nat)
    (forObject : Option ObjectId := none)
    (cause : Option EventCause := some (.costPayment .life p forObject)) : Except String Game := do
  if n == 0 then
    return g
  let pl := g.player p
  if pl.life < (n : Int) then
    throw s!"{pl.name} cannot pay {n} life"
  if g.lifeLocked p || g.lifeCantChange p then
    throw s!"{pl.name} cannot pay {n} life (life total can't change)"
  let effCause :=
    g.resolveOptionalCause cause (fallbackCtrl := some p)
      (defaultCause := .costPayment .life p forObject)
  return (g.record (GameEvent.life g.turnNumber p n false false false
    (cause := effCause))).logMsg
    s!"{pl.name} pays {n} life ({pl.life - (n : Int)} life)"

/-- Default order for paying a cost with permanents: tokens first, then the
lowest mana value. -/
def cheapestFirst (g : Game) (cands : Array GameObject) : Array GameObject :=
  let key (x : GameObject) : Nat := (if x.printed.isToken then 0 else 1000) + g.objectManaValue x
  cands.qsort (fun a b => key a < key b)

private def unreplacedCostCause : EventCause → EventCause
  | .replaced _ orig => unreplacedCostCause orig
  | other => other

/-- Whether `sid` was already sacrificed from the battlefield as a cost for
`forObject` (CR 601.2h). -/
def sourceSacrificedForCost (g : Game) (sid : ObjectId) (forObject : Option ObjectId)
    (sinceIdx : Nat := 0) : Bool :=
  match forObject with
  | none => false
  | some fid =>
    let slice := g.events.extract (min sinceIdx g.events.size) g.events.size
    slice.any fun
      | .rules _ (.zone (.moved before _ .battlefield _ ..)) cause _ =>
        before.id == some sid &&
          match unreplacedCostCause cause with
          | .costPayment .sacrifice _ (some f) => f == fid
          | _ => false
      | _ => false

/-- Whether `sid` was already discarded from its owner's hand as a cost for
`forObject` (CR 601.2h). -/
def sourceDiscardedFromHandForCost (g : Game) (sid : ObjectId) (forObject : Option ObjectId)
    (sinceIdx : Nat := 0) : Bool :=
  match forObject with
  | none => false
  | some fid =>
    let slice := g.events.extract (min sinceIdx g.events.size) g.events.size
    slice.any fun
      | .rules _ (.zone (.moved before _ (.hand _) _ ..)) cause _ =>
        before.id == some sid &&
          match unreplacedCostCause cause with
          | .costPayment .discard _ (some f) => f == fid
          | _ => false
      | _ => false

/-- Whether `sid` was already tapped to pay `{T}` for `forObject` (CR 601.2h). -/
def sourceTappedForCost (g : Game) (sid : ObjectId) (forObject : Option ObjectId)
    (sinceIdx : Nat := 0) : Bool :=
  match forObject with
  | none => false
  | some fid =>
    let slice := g.events.extract (min sinceIdx g.events.size) g.events.size
    slice.any fun
      | .rules _ (.permanent (.tapped snap _)) cause _ =>
        snap.id == some sid &&
          match unreplacedCostCause cause with
          | .costPayment .tap _ (some f) => f == fid
          | _ => false
      | _ => false

/-- Whether `sid` already paid a counter cost of `costKind` (and optional
`counterKind?`) for `forObject` (CR 601.2h). -/
def sourceCounterCostPaidFor (g : Game) (sid : ObjectId) (forObject : Option ObjectId)
    (costKind : CostKind) (counterKind? : Option CounterKind := none)
    (sinceIdx : Nat := 0) : Bool :=
  match forObject with
  | none => false
  | some fid =>
    let slice := g.events.extract (min sinceIdx g.events.size) g.events.size
    slice.any fun
      | .rules _ (.permanent (.counters (.object snap) ck ..)) cause _ =>
        snap.id == some sid && counterKind?.all (· == ck) &&
          match unreplacedCostCause cause with
          | .costPayment k _ (some f) => k == costKind && f == fid
          | _ => false
      | _ => false

/-- Whether `sid` left the battlefield after `sinceIdx` as part of a cost paid
by `p` (e.g. sacrificing or exiling `sid` to a CR 601.2g mana ability). -/
def sourceRemovedByCostSince (g : Game) (p : PlayerId) (sid : ObjectId)
    (sinceIdx : Nat := 0) : Bool :=
  let slice := g.events.extract (min sinceIdx g.events.size) g.events.size
  slice.any fun
    | .rules _ (.zone (.moved before _ .battlefield _ ..)) cause _ =>
      before.id == some sid &&
        match unreplacedCostCause cause with
        | .costPayment .sacrifice q _ | .costPayment .exile q _ => q == p
        | _ => false
    | _ => false

/-- Whether `prop` still requires its `sourceId` to remain on the battlefield
for an unpaid battlefield-source cost (CR 601.2g / 601.2h / 602.2b). -/
def proposedNeedsBattlefieldSource (g : Game) (prop : ProposedSpell)
    (sinceIdx : Nat := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size) : Bool :=
  match prop.sourceId with
  | none => false
  | some sid =>
    if prop.kind == .turnFaceUp then true
    else if prop.kind != .activatedAbility then false
    else
      let forObj := some prop.spellId
      (prop.tapSource && !g.sourceTappedForCost sid forObj sinceIdx) ||
        ((prop.sacrificeSource || prop.activation.any (·.cost.sacrificeSource)) &&
          !g.sourceSacrificedForCost sid forObj sinceIdx) ||
        prop.activation.any (·.cost.exileSourceFromBattlefield) ||
        (prop.activation.any (·.cost.isLoyalty) && !prop.loyaltyPaid &&
          !g.sourceCounterCostPaidFor sid forObj .loyalty (some .loyalty) sinceIdx) ||
        (prop.removePlusOneX &&
          !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .plusOnePlusOne) sinceIdx) ||
        (prop.activation.any (·.cost.removeStoryCounter) &&
          !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .story) sinceIdx) ||
        (prop.activation.any (·.cost.removeIndestructibleCounter) &&
          !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .indestructible) sinceIdx) ||
        (prop.activation.any (fun a =>
          (a.cost.putStunCounterOnSource &&
            !g.sourceCounterCostPaidFor sid forObj .putCounters (some .stun) sinceIdx) ||
          (a.cost.sacrificeEquipmentAttachedToSource && g.pending == .activateManaAbilities prop.caster)))

/-- Whether `prop` still has activation costs remaining to be paid after a
CR 601.2h chosen-object cost step (`.crew`, `.zemoBoast`, or `CostPick`). -/
def propHasRemainingExtraCosts (g : Game) (prop : ProposedSpell)
    (remainingPicks : Array CostPick := (prop.activation.map costPicksOf).getD #[])
    (sinceIdx : Nat := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size) : Bool :=
  prop.kind != .activatedAbility ||
    prop.sourceId.isNone ||
    !remainingPicks.isEmpty ||
    prop.needsSacrificeOther ||
    prop.payLife > 0 ||
    prop.discardSource ||
    g.proposedNeedsBattlefieldSource prop sinceIdx ||
    prop.activation.any (fun a =>
      a.isFromGraveyard || a.isFromHand || a.cost.removeAnyNumberPlusOne)

private def matchingCounterCount (o : GameObject) (kind? : Option CounterKind) : Nat :=
  match kind? with
  | some k => o.status.counterCount k
  | none => o.status.toCounterBag.foldl (fun acc (_, n) => acc + n) 0

private partial def costItemAllowsObject (g : Game) (p : PlayerId) (sourceId : Option ObjectId)
    (item : CostItem) (o : GameObject)
    (tapSource sacrificeOrExileSource discardOrExileHandSource : Bool) : Bool :=
  let perm := o.isOnBattlefield && g.controlledBy o p
  let inHand := o.owner == p && o.zone == .hand p && isDiscardableCard o
  let other := sourceId.all (o.id != ·)
  let env : EvalEnv := { controller := p, sourceId }
  match item with
  | .sacrifice _ (.filter pred) =>
    perm && !g.cantSacrificeObject p o && (!sacrificeOrExileSource || other) && EvalExpr.evalObjectPred g env (.live o) pred
  | .discard _ .hand =>
    inHand && (!discardOrExileHandSource || other)
  | .discard _ (.matching pred) =>
    inHand && (!discardOrExileHandSource || other) && EvalExpr.evalObjectPred g env (.live o) pred
  | .exile _ zones (.filter pred) _ =>
    let inZone :=
      (zones.zones.contains .graveyard && o.owner == p && o.zone == .graveyard p && isDiscardableCard o) ||
      (zones.zones.contains .hand && inHand && (!discardOrExileHandSource || other)) ||
      (zones.zones.contains .battlefield && perm && (!sacrificeOrExileSource || other))
    inZone && EvalExpr.evalObjectPred g env (.live o) pred
  | .putOnLibrary _ zones (.filter pred) _ =>
    let inZone :=
      (zones.zones.contains .graveyard && o.owner == p && o.zone == .graveyard p && isDiscardableCard o) ||
      (zones.zones.contains .hand && inHand && (!discardOrExileHandSource || other)) ||
      (zones.zones.contains .battlefield && perm && (!sacrificeOrExileSource || other))
    inZone && EvalExpr.evalObjectPred g env (.live o) pred
  | .removeCounters _ kind? (.filter pred) =>
    perm && EvalExpr.evalObjectPred g env (.live o) pred && matchingCounterCount o kind? > 0
  | .tapObjects _ pred =>
    perm && (!tapSource || other) && !o.status.tapped && EvalExpr.evalObjectPred g env (.live o) pred
  | .returnToHand _ (.filter pred) =>
    perm && (!sacrificeOrExileSource || other) && EvalExpr.evalObjectPred g env (.live o) pred
  | .or choices =>
    choices.any fun c =>
      c.items.any fun sub =>
        costItemAllowsObject g p sourceId sub o tapSource sacrificeOrExileSource discardOrExileHandSource
  | _ => false

/-- Whether `o` can pay `pick` for `p`'s ability of `sourceId`. -/
def costPickAllows (g : Game) (p : PlayerId) (sourceId : Option ObjectId) (pick : CostPick)
    (o : GameObject)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false) : Bool :=
  let perm := o.isOnBattlefield && g.controlledBy o p
  let canSac := perm && !g.cantSacrificeObject p o
  let inHand := o.owner == p && o.zone == .hand p && isDiscardableCard o
  let other := sourceId.all (o.id != ·)
  let artifact := g.isArtifact o
  match pick with
  | .sacrificeAnotherCreature => canSac && other && g.isCreature o
  | .sacrificeAnotherSubtype t => canSac && other && g.hasSubtype o t

  | .sacrificeArtifact => canSac && (!sacrificeOrExileSource || other) && artifact
  | .sacrificeLegendaryArtifact =>
    canSac && (!sacrificeOrExileSource || other) && artifact && g.isLegendary o
  | .sacrificeArtifactOrCreature =>
    canSac && (!sacrificeOrExileSource || other) && (artifact || g.isCreature o)
  | .sacrificeAnotherArtifact => canSac && other && artifact
  | .sacrificeAnotherCreatureOrArtifact =>
    canSac && other && (g.isCreature o || artifact)
  | .sacrificeAnotherCreatureOrPlaneswalker =>
    canSac && other && (g.isCreature o || g.isPlaneswalker o)
  | .sacrificeArtifactOrLand =>
    canSac && (!sacrificeOrExileSource || other) && (artifact || g.isLand o)
  | .sacrificeEquipmentAttachedToSource =>
    canSac && (!sacrificeOrExileSource || other) && g.isEquipment o &&
      sourceId.isSome && o.attachedTo == sourceId
  | .sacrificeArtifactOrDiscardNonland =>
    (canSac && (!sacrificeOrExileSource || other) && artifact) ||
      (inHand && (!discardOrExileHandSource || other) && !g.isLand o)
  | .discardACard => inHand && (!discardOrExileHandSource || other)
  | .discardNonland => inHand && (!discardOrExileHandSource || other) && !g.isLand o
  | .discardLegendaryCard => inHand && (!discardOrExileHandSource || other) && g.isLegendary o
  | .discardLegendarySameName =>
    inHand && (!discardOrExileHandSource || other) && g.isLegendary o &&
      (g.permanentsOf p).any (fun x => g.isLegendary x && g.name x == g.name o)
  | .exileAnotherCreatureCardFromGraveyard =>
    other && o.owner == p && o.zone == .graveyard p && isDiscardableCard o && g.isCreature o
  | .tapUntappedCreature => perm && (!tapSource || other) && g.isCreature o && !o.status.tapped
  | .tapTwoUntappedArtifacts => perm && (!tapSource || other) && artifact && !o.status.tapped
  | .custom item =>
    costItemAllowsObject g p sourceId item o tapSource sacrificeOrExileSource discardOrExileHandSource

/-- Objects that can pay `pick`, in a default order (tokens and cheaper
permanents first, preferring non-mana permanents for tap picks). -/
def costPickCandidates (g : Game) (p : PlayerId) (sourceId : Option ObjectId) (pick : CostPick)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false) :
    Array ObjectId :=
  let pl := g.player p
  let zoneCards (ids : Array ObjectId) := ids.filterMap g.findObject?
  let pool := g.cheapestFirst (g.permanentsOf p) ++ zoneCards pl.hand ++ zoneCards pl.graveyard
  let allowed := pool.filter (g.costPickAllows p sourceId pick
    (tapSource := tapSource)
    (sacrificeOrExileSource := sacrificeOrExileSource)
    (discardOrExileHandSource := discardOrExileHandSource))
  let isTapPick : Bool :=
    match pick with
    | .tapUntappedCreature | .tapTwoUntappedArtifacts | .custom (.tapObjects ..) => true
    | _ => false
  let ordered :=
    if isTapPick then
      let (nonMana, manaSrcs) := allowed.partition (fun o => !canTapForPlainManaFwd g p o)
      nonMana ++ manaSrcs
    else allowed
  ordered.map (·.id)

private partial def assignDisjointPicks (g : Game) (p : PlayerId) (sourceId : Option ObjectId)
    (picks : Array CostPick) (tapSource sacrificeOrExileSource discardOrExileHandSource : Bool)
    (idx : Nat) (used : Array ObjectId) (preTappedIds : Array ObjectId := #[])
    (sacReservedIds : Array ObjectId := #[]) :
    Option (Array ObjectId) :=
  if idx ≥ picks.size then some #[]
  else
    let pick := picks[idx]!
    let isTapPick : Bool :=
      match pick with
      | .tapUntappedCreature | .tapTwoUntappedArtifacts | .custom (.tapObjects ..) => true
      | _ => false
    let isBfSacPick : Bool :=
      match pick with
      | .tapUntappedCreature | .tapTwoUntappedArtifacts
      | .discardACard | .discardNonland | .discardLegendaryCard | .discardLegendarySameName
      | .exileAnotherCreatureCardFromGraveyard
      | .custom (.tapObjects ..) | .custom (.discard ..) | .custom (.removeCounters ..) => false
      | .custom (.exile _ zones _ _) => zones.zones.contains .battlefield
      | _ => true
    let laterSacAttachedEquip :=
      isBfSacPick && (picks.extract (idx + 1) picks.size).contains .sacrificeEquipmentAttachedToSource
    let baseCands :=
      (g.costPickCandidates p sourceId pick
        (tapSource := tapSource)
        (sacrificeOrExileSource := sacrificeOrExileSource || laterSacAttachedEquip)
        (discardOrExileHandSource := discardOrExileHandSource)).filter fun cid =>
          !used.contains cid && !(isTapPick && preTappedIds.contains cid) &&
            !(isBfSacPick && sacReservedIds.contains cid)
    let cands : Array ObjectId :=
      match pick with
      | .custom (.removeCounters _ kind? _) =>
        baseCands.foldl (fun acc cid =>
          match g.findObject? cid with
          | some o => acc ++ Array.replicate (matchingCounterCount o kind?) cid
          | none => acc) #[]
      | _ => baseCands
    if cands.size < pick.count then none
    else if idx + 1 == picks.size then
      some (cands.extract 0 pick.count)
    else
      let rec chooseK (start left : Nat) (picked : Array ObjectId) : Option (Array ObjectId) :=
        if left == 0 then
          if (assignDisjointPicks g p sourceId picks tapSource sacrificeOrExileSource
                discardOrExileHandSource (idx + 1) (used ++ picked) preTappedIds sacReservedIds).isSome then
            some picked
          else none
        else if start + left > cands.size then none
        else
          match chooseK (start + 1) (left - 1) (picked.push cands[start]!) with
          | some chosen => some chosen
          | none => chooseK (start + 1) left picked
      chooseK 0 pick.count #[]

/-- First valid candidate slice for `picks[0]` (in `cheapestFirst` order) that
leaves the remaining `picks` payable with distinct objects (CR 602.2b / 118.10). -/
def firstPayableCostPickSlice? (g : Game) (p : PlayerId) (sourceId : Option ObjectId)
    (picks : Array CostPick)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false)
    (used : Array ObjectId := #[])
    (preTappedIds : Array ObjectId := #[])
    (sacReservedIds : Array ObjectId := #[]) : Option (Array ObjectId) :=
  if picks.isEmpty then none
  else
    assignDisjointPicks g p sourceId picks tapSource sacrificeOrExileSource
      discardOrExileHandSource 0 used preTappedIds sacReservedIds

/-- Whether every pick can be paid by different objects, accounting for whether
`sourceId` itself is separately tapped, sacrificed/exiled, or discarded/exiled
from hand (CR 602.2b / 118.3 / 118.10). -/
def costPicksPayable (g : Game) (p : PlayerId) (sourceId : Option ObjectId) (picks : Array CostPick)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false)
    (used : Array ObjectId := #[])
    (preTappedIds : Array ObjectId := #[])
    (sacReservedIds : Array ObjectId := #[]) :
    Bool :=
  (assignDisjointPicks g p sourceId picks tapSource sacrificeOrExileSource
    discardOrExileHandSource 0 used preTappedIds sacReservedIds).isSome

/-- Append `CostPick.sacrificeAnotherCreatureOrArtifact` when `needsSacrificeOther`
holds so disjointness is checked across all non-mana object picks (CR 118.10 / 602.2b). -/
def costPicksWithSacrificeOther (picks : Array CostPick) (needsSacrificeOther : Bool) :
    Array CostPick :=
  if needsSacrificeOther then picks.push .sacrificeAnotherCreatureOrArtifact else picks

/-- Whether a `.tapObjects (.totalPowerAtLeast ..)` cost item excludes the
source permanent itself (`.otherThan .this`, CR 702.122a). -/
def crewExcludesSelf (c : CostSpec) : Bool :=
  c.items.any fun
    | .tapObjects (.totalPowerAtLeast _) pred =>
      match pred with
      | .all ps => ps.contains (.otherThan .this)
      | .otherThan .this => true
      | _ => false
    | _ => false

/-- Find a subset of untapped creatures `p` controls (excluding `vehicleId` when
`excludeSelf || tapSource`) with total power at least `crewN` whose tapping
still leaves `allPicks` payable (CR 118.10 / 602.2b / 702.122a). -/
partial def firstPayableCrewSelection? (g : Game) (p : PlayerId) (vehicleId : ObjectId)
    (crewN : Nat) (allPicks : Array CostPick)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false)
    (orderedCands? : Option (Array GameObject) := none)
    (disjointFromAllPicks : Bool := false)
    (preTappedIds : Array ObjectId := #[])
    (used : Array ObjectId := #[])
    (sacReservedIds : Array ObjectId := #[])
    (excludeSelf : Bool := true) : Option (Array ObjectId) :=
  let exclSelf := excludeSelf || tapSource
  let cands :=
    (orderedCands?.getD
      ((g.creaturesControlledBy p).filter (fun c => (!exclSelf || c.id != vehicleId) && !c.status.tapped))).filter
      (fun c =>
        (!exclSelf || c.id != vehicleId) && !c.status.tapped &&
          !used.contains c.id && !preTappedIds.contains c.id)
  let okAfterCrew (picked : Array ObjectId) : Bool :=
    if allPicks.isEmpty then true
    else
      g.costPicksPayable p (some vehicleId) allPicks
        (tapSource := tapSource)
        (sacrificeOrExileSource := sacrificeOrExileSource)
        (discardOrExileHandSource := discardOrExileHandSource)
        (used := if disjointFromAllPicks then used ++ picked else used)
        (preTappedIds := preTappedIds ++ picked)
        (sacReservedIds := sacReservedIds)
  if crewN == 0 then
    if okAfterCrew #[] then some #[] else none
  else
    let sufPow : Array Nat := Id.run do
      let mut out := Array.replicate (cands.size + 1) 0
      let mut i := cands.size
      while i > 0 do
        i := i - 1
        out := out.set! i (out[i + 1]! + (g.power cands[i]!).toNat)
      return out
    let rec search (idx : Nat) (curPow : Nat) (picked : Array ObjectId) : Option (Array ObjectId) :=
      if curPow ≥ crewN then
        if okAfterCrew picked then some picked else none
      else if idx ≥ cands.size || curPow + sufPow[idx]! < crewN then
        none
      else
        let c := cands[idx]!
        let pwr := (g.power c).toNat
        if pwr == 0 then
          search (idx + 1) curPow picked
        else
          match search (idx + 1) (curPow + pwr) (picked.push c.id) with
          | some res => some res
          | none => search (idx + 1) curPow picked
    search 0 0 #[]

/-- Pay one or more already-validated `ids` for `pick` on `abilityId` / `sourceId`,
chaining `.payCostPickItems` if an earlier move or sacrifice pauses on
`Pending.chooseReplacement` (`pick.count >= 2`), and returning whether every
item in `ids` was paid or queued across a replacement pause. -/
def payCostPickItemsChecked (g : Game) (p : PlayerId) (abilityId sourceId : Option ObjectId)
    (pick : CostPick) (ids : Array ObjectId)
    (outerToRestore? : Option PendingReplacement := none)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (fromEventIdx? : Option Nat := none) : Game × Bool :=
  let deferPfe := ids.size > 1 || fromEventIdx?.isSome
  let loopFromIdx := fromEventIdx?.getD g.events.size
  if let .chooseReplacement .. := g.pending then
    (g.chainPendingReplacement
      (.payCostPickItems p abilityId sourceId pick ids (if deferPfe then some loopFromIdx else none)), true)
  else
    let preLoop :=
      match fromEventIdx? with
      | some idx => g.mkHistoricalGameAt idx
      | none => g
    let finishDeferredPfe (g0 : Game) : Game :=
      if deferPfe then emitExpiredPlayFromExileLogs preLoop g0 loopFromIdx else g0
    let abortOrNoop (g0 : Game) : Game :=
      if !g0.hasActiveManaProposalCheckpoint && g0.proposedSpell.isSome then
        let g1 :=
          match outerToRestore? with
          | some outer => g0.chainPendingReplacement outer
          | none => g0
        g1.reverseProposedSpellFwd (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      else finishDeferredPfe g0
    let itemPayable (g0 : Game) (id : ObjectId) : Bool :=
      match g0.findObject? id with
      | some o => g0.costPickAllows p sourceId pick o
      | none => false
    if g.over || !g.stillInGame p || !ids.all (itemPayable g) then
      (abortOrNoop g, false)
    else
      let forObj : Option ObjectId := abilityId
      let run (g : Game) : Game × Bool := Id.run do
        let name := (g.player p).name
        let mut g := g
        for i in [0:ids.size] do
          if g.over || !g.stillInGame p then
            return (if g.currentBatch.isNone then abortOrNoop g else g, false)
          let id := ids[i]!
          match g.findObject? id with
          | none =>
            return (if g.currentBatch.isNone then abortOrNoop g else g, false)
          | some o =>
            if !g.costPickAllows p sourceId pick o then
              return (if g.currentBatch.isNone then abortOrNoop g else g, false)
            match pick with
            | .tapUntappedCreature | .tapTwoUntappedArtifacts | .custom (.tapObjects ..) =>
              let records :=
                g.isCreature o && (
                  (abilityId.bind g.findObject?).any (fun ab =>
                    ab.abilityEffect.any (fun e => Effect.usesCostPaidObjects e.body)) ||
                  (g.proposedSpell.bind (·.activation)).any (·.cost.bindVar?.isSome))
              let pw := g.power o
              let oName := g.name o
              g := (g.becomeTapped o (cause := some (.costPayment .tap p forObj))).logMsg
                s!"{name} taps {oName} to pay a cost"
              if records then
                if let some aid := abilityId then
                  if (g.findObject? aid).isSome then
                    g := g.setStackEntryLastKnown aid (lastKnownPower := some pw)
            | .custom (.putOnLibrary _ _ _ pos) =>
              let oName := g.name o
              g := (g.move id (.library o.owner) none (cause := some (.costPayment .putOnLibrary p forObj))
                (libraryPosition := pos) (deferPlayFromExileLogs := deferPfe)).1
              g := g.logMsg s!"{name} puts {oName} on the library to pay a cost"
            | .exileAnotherCreatureCardFromGraveyard | .custom (.exile ..) =>
              let msg :=
                if o.zone == .graveyard o.owner then s!"{name} exiles {g.name o} from their graveyard"
                else s!"{name} exiles {g.name o}"
              g := (g.move id .exile none (cause := some (.costPayment .exile p forObj))
                (deferPlayFromExileLogs := deferPfe)).1
              if let .chooseReplacement .. := g.pending then
                g := g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id msg))
              else if (g.followMovedToZone? id (· == .exile)).isSome then
                g := g.logMsg msg
            | .custom (.returnToHand ..) =>
              let oName := g.name o
              g := (g.move id (.hand o.owner) none (cause := some (.costPayment .returnToHand p forObj))
                (deferPlayFromExileLogs := deferPfe)).1
              g := g.logMsg s!"{name} returns {oName} to its owner's hand"
            | .custom (.removeCounters _ kind? _) =>
              let chosenKind? : Option CounterKind :=
                match kind? with
                | some k => if o.status.counterCount k > 0 then some k else none
                | none => (o.status.toCounterBag.find? (fun (_, n) => n > 0)).map Prod.fst
              match chosenKind? with
              | some k =>
                let oName := g.name o
                g := g.recordRemoveCounters id k 1 (byPlayer := some p)
                  (cause := some (.costPayment .removeCounters p forObj))
                  (deferPlayFromExileLogs := deferPfe)
                g := g.logMsg s!"{name} removes {k.countersPhrase 1} from {oName} to pay a cost"
              | none =>
                return (if g.currentBatch.isNone then abortOrNoop g else g, false)
            | _ =>
              if o.isOnBattlefield then
                let records :=
                  g.isCreature o && (
                    (abilityId.bind g.findObject?).any (fun ab =>
                      ab.abilityEffect.any (fun e => Effect.usesCostPaidObjects e.body)) ||
                    (g.proposedSpell.bind (·.activation)).any (·.cost.bindVar?.isSome))
                let pw := g.power o
                let oName := g.name o
                g := g.sacrificeToGraveyard o s!"{name} sacrifices {oName}"
                  (cause := some (.costPayment .sacrifice p forObj))
                  (deferPlayFromExileLogs := deferPfe)
                if records then
                  if let .chooseReplacement .. := g.pending then
                    g := g.chainPendingReplacement
                      (.finishPostStep (.recordCostSacrificedPower abilityId id pw))
                  else if !(g.findObject? id).any (·.isOnBattlefield) then
                    if let some aid := abilityId then
                      if (g.findObject? aid).isSome then
                        g := g.setStackEntryLastKnown aid (lastKnownPower := some pw)
              else
                let msg := s!"{name} discards {g.name o}"
                let owner := o.owner
                g := (g.move id (.graveyard owner) none (verb := some .discard) (actor := some p)
                  (cause := some (.costPayment .discard p forObj))
                  (deferPlayFromExileLogs := deferPfe)).1
                -- CR 614.6 / 701.9a: log the discard only once the card reaches
                -- its owner's graveyard.
                if let .chooseReplacement .. := g.pending then
                  g := g.chainPendingReplacement
                    (.finishPostStep (.logDiscardIfInGraveyard id owner msg))
                else if (g.followMovedToZone? id (· == .graveyard owner)).isSome then
                  g := g.logMsg msg
            if let .chooseReplacement .. := g.pending then
              let rem := ids.extract (i + 1) ids.size
              if !rem.isEmpty || deferPfe then
                g := g.chainPendingReplacement
                  (.payCostPickItems p abilityId sourceId pick rem (if deferPfe then some loopFromIdx else none))
              return (g, true)
        return (finishDeferredPfe g, true)
      match pick with
      | .tapTwoUntappedArtifacts | .custom (.tapObjects ..) =>
        if g.currentBatch.isSome || ids.size ≤ 1 then run g
        else
          let (gAfter, ok) := g.withBatchReturn (some (.costPayment .tap p forObj)) run
          if !ok && gAfter.currentBatch.isNone then (abortOrNoop gAfter, false)
          else (gAfter, ok)
      | _ => run g

/-- Pay one or more already-validated `ids` for `pick` on `abilityId` / `sourceId`,
chaining `.payCostPickItems` if an earlier move or sacrifice pauses on
`Pending.chooseReplacement` (`pick.count >= 2`). -/
def payCostPickItems (g : Game) (p : PlayerId) (abilityId sourceId : Option ObjectId)
    (pick : CostPick) (ids : Array ObjectId)
    (outerToRestore? : Option PendingReplacement := none)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none)
    (fromEventIdx? : Option Nat := none) : Game :=
  (g.payCostPickItemsChecked p abilityId sourceId pick ids
    (outerToRestore? := outerToRestore?)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)
    (fromEventIdx? := fromEventIdx?)).1

/-- Pay a combined net loyalty delta `k` on `o` (CR 606.3 / 606.4 / 606.5 / 606.6 / 118.11). -/
def payLoyaltyDelta (g : Game) (p : PlayerId) (o : GameObject) (k : Int)
    (forObject : Option ObjectId := none) : Game :=
  let oName := g.name o
  let markPaid (g : Game) : Game :=
    if g.proposedSpell.isSome then g.changeProposal (.loyaltyPaid true) else g
  if k > 0 then
    g.withProposalAction .costAction fun g =>
      let g := markPaid g
      g.putCountersDeferredLog o.id .loyalty k.natAbs (some p) .countArePutOn
        (cause := some (.costPayment .loyalty p forObject))
  else if k < 0 then
    let g := g.withProposalAction .costAction fun g =>
      let g := markPaid g
      g.recordRemoveCounters o.id .loyalty k.natAbs (byPlayer := some p)
        (cause := some (.costPayment .loyalty p forObject))
    g.logMsg s!"{-k} loyalty counter(s) are removed from {oName}"
  else
    g.withProposalAction .costAction fun g =>
      markPaid g

/-- Pay a single loyalty cost symbol on `o` (CR 606.3 / 606.4 / 118.11). -/
def payLoyaltyCost (g : Game) (p : PlayerId) (o : GameObject) (sym : LoyaltySymbol)
    (forObject : Option ObjectId := none) : Game :=
  let chosenX := ((forObject.bind g.findObject?).bind (·.chosenX)).getD 0
  g.payLoyaltyDelta p o (sym.netDelta chosenX) (forObject := forObject)

/-- Pay `pick` with `ids` for the ability `abilityId` of `sourceId`
(CR 601.2h). The power of a creature sacrificed for an ability that refers
to it is recorded on the ability (Tom, Bert, and William). -/
def payCostPick (g : Game) (p : PlayerId) (abilityId sourceId : Option ObjectId) (pick : CostPick)
    (ids : Array ObjectId)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false)
    (callerOuter? : Option PendingReplacement := none)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Except String Game :=
  g.withProposalActionM .costAction fun g => do
  let allowsMultiplicity : Bool :=
    match pick with
    | .custom (.removeCounters ..) => true
    | _ => false
  if ids.size != pick.count || (!allowsMultiplicity && ids.toList.eraseDups.length != ids.size) then
    throw s!"Choose {pick.count} to {pick.phrase}"
  for id in ids do
    let some o := g.findObject? id | throw "no such object"
    if !g.costPickAllows p sourceId pick o
        (tapSource := tapSource)
        (sacrificeOrExileSource := sacrificeOrExileSource)
        (discardOrExileHandSource := discardOrExileHandSource) then
      throw s!"{g.name o} can't be used to {pick.phrase}"
  if let .custom (.removeCounters _ kind? _) := pick then
    for id in ids.toList.eraseDups do
      let needed := (ids.filter (· == id)).size
      let some o := g.findObject? id | throw "no such object"
      if matchingCounterCount o kind? < needed then
        throw s!"{g.name o} doesn't have {needed} counter(s) to remove"
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let hadProp := g.proposedSpell.isSome
  let outer? := g.pendingReplacement
  let outerForAbort? := outer?.orElse (fun _ => callerOuter?)
  let abortMissingSource (g0 : Game) : Game :=
    if !g0.hasActiveManaProposalCheckpoint && g0.proposedSpell.isSome then
      let g1 :=
        match outerForAbort? with
        | some outer => g0.chainPendingReplacement outer
        | none => g0
      g1.reverseProposedSpellFwd (resumeContinuation := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
    else
      match outer? with
      | some outer => g0.chainPendingReplacement outer
      | none => g0
  let requireLiveSource (g0 : Game) (sid : ObjectId) : Option GameObject :=
    match g0.findObject? sid with
    | some cur => if cur.isOnBattlefield && g0.controlledBy cur p then some cur else none
    | none => none
  let mut g := if outer?.isSome then g.change (.pendingReplacement none) else g
  let isBfSacPick : Bool :=
    match pick with
    | .tapUntappedCreature | .tapTwoUntappedArtifacts
    | .custom (.tapObjects ..) | .custom (.removeCounters ..)
    | .exileAnotherCreatureCardFromGraveyard => false
    | _ => true
  if !sacrificeOrExileSource && isBfSacPick then
    if let some sid := sourceId then
      if ids.contains sid then
        if let some src := g.findObject? sid then
          if src.isOnBattlefield then
            let effTap :=
              tapSource ||
                g.proposedSpell.any (fun prop =>
                  prop.sourceId == some sid &&
                    (abilityId.isNone || abilityId == some prop.spellId) && prop.tapSource)
            let effAb? :=
              g.proposedSpell.bind fun prop =>
                if prop.sourceId == some sid &&
                    (abilityId.isNone || abilityId == some prop.spellId) then
                  prop.activation
                else none
            let effX := (abilityId.bind g.findObject? |>.bind (·.chosenX)).getD 0
            let effRemovePlusOnes :=
              if g.proposedSpell.any (fun prop =>
                  prop.sourceId == some sid &&
                    (abilityId.isNone || abilityId == some prop.spellId) && prop.removePlusOneX) then
                effX
              else 0
            let forObj := abilityId <|> some sid
            let tapNeeded := effTap && !g.sourceTappedForCost sid forObj sinceIdx
            if !g.controlledBy src p then
              throw "You don't control that permanent"
            if tapNeeded && src.status.tapped then
              throw s!"{g.name src} is already tapped"
            if let some a := effAb? then
              if a.cost.removeStoryCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .story) sinceIdx &&
                  src.status.story == 0 then
                throw s!"{g.name src} has no story counter"
              if a.cost.removeIndestructibleCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .indestructible) sinceIdx &&
                  src.status.indestructibleCounters == 0 then
                throw s!"{g.name src} has no indestructible counter"
              if a.cost.removeAnyNumberPlusOne &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .plusOnePlusOne) sinceIdx &&
                  src.status.plusOnePlusOne < effRemovePlusOnes then
                throw s!"{g.name src} doesn't have {effRemovePlusOnes} +1/+1 counters"
              if let some k := a.cost.netLoyaltyDelta effX then
                let loyaltyAlreadyPaid :=
                  g.proposedSpell.any (·.loyaltyPaid) ||
                    g.sourceCounterCostPaidFor sid forObj .loyalty (some .loyalty) sinceIdx
                if !loyaltyAlreadyPaid then
                  if g.loyaltyActivatedThisTurn src.id then
                    throw s!"{g.name src}'s loyalty ability was already activated this turn (CR 606.3)"
                  if k < 0 && (src.status.loyaltyCounters : Int) < -k then
                    throw s!"{g.name src} doesn't have {-k} loyalty counters to remove (CR 606.4)"
            if tapNeeded then
              let some curSrc := requireLiveSource g sid | return abortMissingSource g
              if curSrc.status.tapped then return abortMissingSource g
              g := g.becomeTapped curSrc (cause := some (.costPayment .tap p forObj))
            if let some a := effAb? then
              let preCounters := g
              let costFromIdx := g.events.size
              let mut removedAnyCounter := false
              let needIndestRem :=
                a.cost.removeIndestructibleCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .indestructible) sinceIdx
              let needPlusRem? : Option Nat :=
                if a.cost.removeAnyNumberPlusOne &&
                    !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .plusOnePlusOne) sinceIdx then
                  some effRemovePlusOnes
                else none
              let loyDelta? := a.cost.netLoyaltyDelta effX
              let needStun :=
                a.cost.putStunCounterOnSource &&
                  !g.sourceCounterCostPaidFor sid forObj .putCounters (some .stun) sinceIdx
              if a.cost.removeStoryCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters (some .story) sinceIdx then
                let some curSrc := requireLiveSource g sid | return abortMissingSource g
                if curSrc.status.story == 0 then return abortMissingSource g
                let srcName := g.name curSrc
                g := g.recordRemoveCounters sid .story 1 (byPlayer := some p)
                  (cause := some (.costPayment .removeCounters p forObj)) (deferPlayFromExileLogs := true)
                g := g.logMsg s!"{(g.player p).name} removes a story counter from {srcName}"
                removedAnyCounter := true
                if g.sbaPaused then
                  g := g.chainPendingReplacement
                    (.finishActivationExtraCosts p sid forObj false false .removeCounters sinceIdx
                      needIndestRem needPlusRem? loyDelta? needStun (some costFromIdx))
                  g := g.chainPendingReplacement
                    (.payCostPickItems p abilityId sourceId pick ids)
                  return match outer? with
                    | some outer => g.chainPendingReplacement outer
                    | none => g
              if needIndestRem then
                let some curSrc := requireLiveSource g sid | return abortMissingSource g
                if curSrc.status.indestructibleCounters == 0 then return abortMissingSource g
                g := (← g.payRemoveIndestructibleCounter curSrc forObj (deferPlayFromExileLogs := true))
                removedAnyCounter := true
                if g.sbaPaused then
                  g := g.chainPendingReplacement
                    (.finishActivationExtraCosts p sid forObj false false .removeCounters sinceIdx
                      false needPlusRem? loyDelta? needStun (some costFromIdx))
                  g := g.chainPendingReplacement
                    (.payCostPickItems p abilityId sourceId pick ids)
                  return match outer? with
                    | some outer => g.chainPendingReplacement outer
                    | none => g
              if needPlusRem?.isSome then
                let some curSrc := requireLiveSource g sid | return abortMissingSource g
                if curSrc.status.plusOnePlusOne < effRemovePlusOnes then return abortMissingSource g
                let srcName := g.name curSrc
                let g' :=
                  if effRemovePlusOnes > 0 then
                    g.recordRemoveCounters sid .plusOnePlusOne effRemovePlusOnes (byPlayer := some p)
                      (cause := some (.costPayment .removeCounters p forObj)) (deferPlayFromExileLogs := true)
                  else g
                g := g'.logMsg
                  s!"{(g.player p).name} removes {effRemovePlusOnes} +1/+1 counters from {srcName}"
                if effRemovePlusOnes > 0 then
                  removedAnyCounter := true
                if g.sbaPaused then
                  g := g.chainPendingReplacement
                    (.finishActivationExtraCosts p sid forObj false false .removeCounters sinceIdx
                      false none loyDelta? needStun (some costFromIdx))
                  g := g.chainPendingReplacement
                    (.payCostPickItems p abilityId sourceId pick ids)
                  return match outer? with
                    | some outer => g.chainPendingReplacement outer
                    | none => g
              if removedAnyCounter then
                g := emitExpiredPlayFromExileLogs preCounters g costFromIdx
              if let some k := loyDelta? then
                let loyaltyAlreadyPaid :=
                  g.proposedSpell.any (·.loyaltyPaid) ||
                    g.sourceCounterCostPaidFor sid forObj .loyalty (some .loyalty) sinceIdx
                if !loyaltyAlreadyPaid then
                  let some curSrc := requireLiveSource g sid | return abortMissingSource g
                  if g.loyaltyActivatedThisTurn curSrc.id then return abortMissingSource g
                  if k < 0 && (curSrc.status.loyaltyCounters : Int) < -k then
                    return abortMissingSource g
                  g := g.payLoyaltyDelta p curSrc k (forObject := forObj)
                  if let .chooseReplacement .. := g.pending then
                    if a.cost.putStunCounterOnSource &&
                        !g.sourceCounterCostPaidFor sid forObj .putCounters (some .stun) sinceIdx then
                      g := g.chainPendingReplacement
                        (.finishActivationExtraCosts p sid forObj false false .stunAndSacrifice sinceIdx)
                    g := g.chainPendingReplacement
                      (.payCostPickItems p abilityId sourceId pick ids)
                    return match outer? with
                      | some outer => g.chainPendingReplacement outer
                      | none => g
              if a.cost.putStunCounterOnSource &&
                  !g.sourceCounterCostPaidFor sid forObj .putCounters (some .stun) sinceIdx then
                let some _ := requireLiveSource g sid | return abortMissingSource g
                g := g.putCountersDeferredLog sid .stun 1 (some p) (.playerPutsOn p)
                  (cause := some (.costPayment .putCounters p forObj))
                if let .chooseReplacement .. := g.pending then
                  g := g.chainPendingReplacement
                    (.payCostPickItems p abilityId sourceId pick ids)
                  return match outer? with
                    | some outer => g.chainPendingReplacement outer
                    | none => g
  g := g.payCostPickItems p abilityId sourceId pick ids (outerToRestore? := outerForAbort?)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)
  if hadProp && g.proposedSpell.isNone then
    return g
  return match outer? with
    | some outer => g.chainPendingReplacement outer
    | none => g

/-- Finish the remaining steps of `payActivationExtraCosts` after an earlier
counter or sacrifice step paused on `Pending.chooseReplacement` or `sbaPaused`. -/
def finishActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (forObject : Option ObjectId) (sacrificeSource exileSource : Bool)
    (stage : ActivationExtraCostStage := .sacrificeAndExile)
    (sinceIdx : Nat := 0)
    (removeIndestructible : Bool := false)
    (removePlusOnes : Option Nat := none)
    (loyaltyDelta : Option Int := none)
    (putStun : Bool := false)
    (fromEventIdx? : Option Nat := none)
    (outerToRestore? : Option PendingReplacement := none)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game := Id.run do
  if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
    return g.chainPendingReplacement
      (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage sinceIdx
        removeIndestructible removePlusOnes loyaltyDelta putStun fromEventIdx?)
  let abortOrNoop (g0 : Game) : Game :=
    if !g0.hasActiveManaProposalCheckpoint && g0.proposedSpell.isSome then
      let g1 :=
        match outerToRestore? with
        | some outer => g0.chainPendingReplacement outer
        | none => g0
      g1.reverseProposedSpellFwd (resumeContinuation := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
    else g0
  if g.over || !g.stillInGame p then
    return abortOrNoop g
  let mut g := g
  if stage == .removeCounters then
    let costFromIdx := fromEventIdx?.getD g.events.size
    let preCounters :=
      match fromEventIdx? with
      | some idx => g.mkHistoricalGameAt idx
      | none => g
    if removeIndestructible &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .indestructible) sinceIdx then
      match g.findObject? sourceId with
      | some src =>
        if !src.isOnBattlefield || !g.controlledBy src p || src.status.indestructibleCounters == 0 then
          return abortOrNoop g
        let srcName := g.name src
        g := g.recordRemoveCounters sourceId .indestructible 1 (byPlayer := some p)
          (cause := some (.costPayment .removeCounters p forObject)) (deferPlayFromExileLogs := true)
        g := g.logMsg s!"{srcName} loses an indestructible counter"
        if g.sbaPaused then
          return g.chainPendingReplacement
            (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
              .removeCounters sinceIdx false removePlusOnes loyaltyDelta putStun (some costFromIdx))
      | none =>
        return abortOrNoop g
    if g.over || !g.stillInGame p then
      return abortOrNoop g
    if let some cnt := removePlusOnes then
      if !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .plusOnePlusOne) sinceIdx then
        match g.findObject? sourceId with
        | some src =>
          if !src.isOnBattlefield || !g.controlledBy src p || src.status.plusOnePlusOne < cnt then
            return abortOrNoop g
          let srcName := g.name src
          if cnt > 0 then
            g := g.recordRemoveCounters sourceId .plusOnePlusOne cnt (byPlayer := some p)
              (cause := some (.costPayment .removeCounters p forObject)) (deferPlayFromExileLogs := true)
          g := g.logMsg s!"{(g.player p).name} removes {cnt} +1/+1 counters from {srcName}"
          if g.sbaPaused then
            return g.chainPendingReplacement
              (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
                .removeCounters sinceIdx false none loyaltyDelta putStun (some costFromIdx))
        | none =>
          return abortOrNoop g
    g := emitExpiredPlayFromExileLogs preCounters g costFromIdx
    if g.over || !g.stillInGame p then
      return abortOrNoop g
    if let some k := loyaltyDelta then
      let loyaltyAlreadyPaid :=
        g.proposedSpell.any (·.loyaltyPaid) ||
          g.sourceCounterCostPaidFor sourceId forObject .loyalty (some .loyalty) sinceIdx
      if !loyaltyAlreadyPaid then
        match g.findObject? sourceId with
        | some src =>
          if !src.isOnBattlefield || !g.controlledBy src p ||
              g.loyaltyActivatedThisTurn src.id ||
              (k < 0 && (src.status.loyaltyCounters : Int) < -k) then
            return abortOrNoop g
          g := g.payLoyaltyDelta p src k (forObject := forObject)
          if let .chooseReplacement .. := g.pending then
            let needsStun :=
              putStun && !g.sourceCounterCostPaidFor sourceId forObject .putCounters (some .stun) sinceIdx
            if needsStun then
              g := g.chainPendingReplacement
                (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
                  .stunAndSacrifice sinceIdx)
            else if sacrificeSource || exileSource then
              g := g.chainPendingReplacement
                (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
                  .sacrificeAndExile sinceIdx)
            return g
        | none =>
          return abortOrNoop g
  if g.over || !g.stillInGame p then
    return abortOrNoop g
  if stage == .stunAndSacrifice || (stage == .removeCounters && putStun) then
    if !g.sourceCounterCostPaidFor sourceId forObject .putCounters (some .stun) sinceIdx then
      match g.findObject? sourceId with
      | some src =>
        if !src.isOnBattlefield || !g.controlledBy src p then
          return abortOrNoop g
        g := g.putCountersDeferredLog sourceId .stun 1 (some p) (.playerPutsOn p)
          (cause := some (.costPayment .putCounters p forObject))
        if let .chooseReplacement .. := g.pending then
          if sacrificeSource || exileSource then
            g := g.chainPendingReplacement
              (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
                .sacrificeAndExile sinceIdx)
          return g
      | none =>
        return abortOrNoop g
  if g.over || !g.stillInGame p then
    return abortOrNoop g
  if (stage == .removeCounters || stage == .stunAndSacrifice || stage == .sacrificeAndExile) && sacrificeSource then
    match g.findObject? sourceId with
    | some src =>
      if !src.isOnBattlefield || !g.controlledBy src p then
        return abortOrNoop g
      g := g.sacrificeToGraveyard src
        s!"{(g.player p).name} sacrifices {g.name src}"
        (cause := some (.costPayment .sacrifice p forObject))
      if let .chooseReplacement .. := g.pending then
        if exileSource then
          g := g.chainPendingReplacement
            (.finishActivationExtraCosts p sourceId forObject false exileSource .exileOnly sinceIdx)
        return g
    | none =>
      return abortOrNoop g
  if g.over || !g.stillInGame p then
    return abortOrNoop g
  if exileSource then
    match g.findObject? sourceId with
    | some src =>
      if !src.isOnBattlefield || !g.controlledBy src p then
        return if !sacrificeSource then abortOrNoop g else g
      let msg := s!"{(g.player p).name} exiles {g.name src}"
      g := (g.move sourceId .exile none
        (cause := some (.costPayment .exile p forObject))).1
      if let .chooseReplacement .. := g.pending then
        g := g.chainPendingReplacement
          (.finishPostStep (.logExiledIfInExile sourceId msg))
      else if (g.followMovedToZone? sourceId (· == .exile)).isSome then
        g := g.logMsg msg
    | none =>
      return if !sacrificeSource then abortOrNoop g else g
  return g

/-- Pay `{T}`, life, discard, and/or sacrifice the source, and the source's
counter costs, as part of an activation cost (CR 601.2h / 118.3b / 702.29).
Costs paid with chosen objects are paid by `payCostPick`. -/
def payActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (tapSource sacrificeSource : Bool) (payLife : Nat := 0)
    (discardSource : Bool := false)
    (ab : Option ActivatedAbility := none) (removePlusOnes : Nat := 0)
    (forObject? : Option ObjectId := none)
    (callerOuter? : Option PendingReplacement := none)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) :
    Except String Game :=
  g.withProposalActionM .costAction fun g => do
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let hadProp := g.proposedSpell.isSome
  let forObject := forObject? <|> g.proposedSpell.map (·.spellId) <|> some sourceId
  let exileSource := ab.any (·.cost.exileSourceFromBattlefield)
  let sacrificeOrExileSource :=
    sacrificeSource || exileSource || ab.any (·.cost.sacrificeSource)
  let rawFromGy := ab.any (·.isFromGraveyard)
  let rawFromHand := discardSource || ab.any (·.isFromHand)
  let needsBfSource :=
    tapSource || sacrificeOrExileSource || removePlusOnes > 0 || ab.any (·.needsBattlefieldSource)
  if (rawFromGy && rawFromHand) || ((rawFromGy || rawFromHand) && needsBfSource) then
    throw "Ability cost cannot be paid from that zone"
  let hasUnpaidBfSourceCost : Bool :=
    (tapSource && !g.sourceTappedForCost sourceId forObject sinceIdx) ||
      (sacrificeOrExileSource && !g.sourceSacrificedForCost sourceId forObject sinceIdx) ||
      exileSource ||
      (ab.any (·.cost.isLoyalty) &&
        !(g.proposedSpell.any (·.loyaltyPaid) ||
          g.sourceCounterCostPaidFor sourceId forObject .loyalty (some .loyalty) sinceIdx)) ||
      ((removePlusOnes > 0 || ab.any (·.cost.removeAnyNumberPlusOne)) &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .plusOnePlusOne) sinceIdx) ||
      (ab.any (·.cost.removeStoryCounter) &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .story) sinceIdx) ||
      (ab.any (·.cost.removeIndestructibleCounter) &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .indestructible) sinceIdx) ||
      (ab.any (fun a =>
        a.cost.putStunCounterOnSource &&
          !g.sourceCounterCostPaidFor sourceId forObject .putCounters (some .stun) sinceIdx))
  let alreadySacrificedForCost :=
    !sacrificeOrExileSource && !discardSource && !rawFromGy && !rawFromHand &&
      (g.sourceSacrificedForCost sourceId forObject sinceIdx ||
        (!hasUnpaidBfSourceCost && g.sourceRemovedByCostSince p sourceId sinceIdx))
  let alreadyDiscardedFromHandForCost :=
    !sacrificeOrExileSource && !discardSource && !rawFromGy && !needsBfSource &&
      ab.any (·.isFromHand) &&
      !ab.any (·.cost.exileSourceFromHand) &&
      g.sourceDiscardedFromHandForCost sourceId forObject sinceIdx
  let some src := g.findObject? sourceId | do
    if alreadySacrificedForCost || alreadyDiscardedFromHandForCost then
      if !g.canPayLife p payLife then
        throw s!"{(g.player p).name} cannot pay {payLife} life"
      return (← g.payLifeCost p payLife (forObject := forObject))
    throw "The source is no longer in play"
  if ab.any (·.cost.exileSourceFromHand) then
    if !(src.zone == .hand src.owner && src.owner == p && isDiscardableCard src) then
      throw s!"{g.name src} is not in your hand"
    let g ← g.payLifeCost p payLife (forObject := forObject)
    let outer? := g.pendingReplacement
    let g := if outer?.isSome then g.change (.pendingReplacement none) else g
    let msg := s!"{(g.player p).name} exiles {g.name src} from their hand"
    let g := (g.move sourceId .exile none (cause := some (.costPayment .exile p forObject))).1
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile sourceId msg))
      else if (g.followMovedToZone? sourceId (· == .exile)).isSome then
        g.logMsg msg
      else g
    return match outer? with | some outer => g.chainPendingReplacement outer | none => g
  if discardSource then
    if !(src.zone == .hand src.owner && src.owner == p && isDiscardableCard src) then
      throw s!"{g.name src} is not in your hand"
    let g ← g.payLifeCost p payLife (forObject := forObject)
    let some src := g.findObject? sourceId | do
      if !g.hasActiveManaProposalCheckpoint && g.proposedSpell.isSome then
        let g1 :=
          match callerOuter? with
          | some outer => g.chainPendingReplacement outer
          | none => g
        return g1.reverseProposedSpellFwd (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      else
        return g
    let outer? := g.pendingReplacement
    let g := if outer?.isSome then g.change (.pendingReplacement none) else g
    let msg := s!"{(g.player p).name} discards {g.name src}"
    let costKind : CostKind := if ab.any (·.isCycling) then .cycle else .discard
    let (g, _) := g.move sourceId (.graveyard src.owner) none (verb := some .discard)
      (actor := some p) (cause := some (.costPayment costKind p forObject))
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.logDiscardIfInGraveyard sourceId src.owner msg))
      else if (g.followMovedToZone? sourceId (· == .graveyard src.owner)).isSome then
        g.logMsg msg
      else g
    return match outer? with | some outer => g.chainPendingReplacement outer | none => g
  let fromGraveyardAb := rawFromGy && !rawFromHand && !needsBfSource
  if fromGraveyardAb then
    if !(src.zone == .graveyard src.owner && src.owner == p && isDiscardableCard src) then
      throw s!"{g.name src} is not in your graveyard"
    let g ← g.payLifeCost p payLife (forObject := forObject)
    if ab.any (·.cost.exileSourceFromGraveyard) then
      let outer? := g.pendingReplacement
      let g := if outer?.isSome then g.change (.pendingReplacement none) else g
      let msg := s!"{(g.player p).name} exiles {g.name src} from their graveyard"
      let g := (g.move sourceId .exile none (cause := some (.costPayment .exile p forObject))).1
      let g :=
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile sourceId msg))
        else if (g.followMovedToZone? sourceId (· == .exile)).isSome then
          g.logMsg msg
        else g
      return match outer? with | some outer => g.chainPendingReplacement outer | none => g
    return g
  let fromHandAb :=
    !discardSource && !ab.any (·.cost.exileSourceFromHand) &&
      ab.any (·.isFromHand) && !rawFromGy && !needsBfSource
  if fromHandAb && !alreadyDiscardedFromHandForCost then
    if !(src.zone == .hand src.owner && src.owner == p && isDiscardableCard src) then
      throw s!"{g.name src} is not in your hand"
    if !g.canPayLife p payLife then
      throw s!"{(g.player p).name} cannot pay {payLife} life"
    return (← g.payLifeCost p payLife (forObject := forObject))
  if !src.isOnBattlefield then
    if alreadySacrificedForCost || alreadyDiscardedFromHandForCost then
      if !g.canPayLife p payLife then
        throw s!"{(g.player p).name} cannot pay {payLife} life"
      return (← g.payLifeCost p payLife (forObject := forObject))
    throw "The source is no longer on the battlefield"
  if !g.controlledBy src p && !alreadySacrificedForCost then
    throw "You don't control that permanent"
  let tapNeeded := tapSource && !g.sourceTappedForCost sourceId forObject sinceIdx
  if tapNeeded && src.status.tapped then
    throw s!"{g.name src} is already tapped"
  if !g.canPayLife p payLife then
    throw s!"{(g.player p).name} cannot pay {payLife} life"
  let chosenX := ((forObject.bind g.findObject?).bind (·.chosenX)).getD 0
  if let some a := ab then
    if a.cost.removeStoryCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .story) sinceIdx &&
        src.status.story == 0 then
      throw s!"{g.name src} has no story counter"
    if a.cost.removeIndestructibleCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .indestructible) sinceIdx &&
        src.status.indestructibleCounters == 0 then
      throw s!"{g.name src} has no indestructible counter"
    if a.cost.removeAnyNumberPlusOne &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .plusOnePlusOne) sinceIdx &&
        src.status.plusOnePlusOne < removePlusOnes then
      throw s!"{g.name src} doesn't have {removePlusOnes} +1/+1 counters"
    if let some k := a.cost.netLoyaltyDelta chosenX then
      let loyaltyAlreadyPaid :=
        g.proposedSpell.any (·.loyaltyPaid) ||
          g.sourceCounterCostPaidFor sourceId forObject .loyalty (some .loyalty) sinceIdx
      if !loyaltyAlreadyPaid then
        if g.loyaltyActivatedThisTurn src.id then
          throw s!"{g.name src}'s loyalty ability was already activated this turn (CR 606.3)"
        if k < 0 && (src.status.loyaltyCounters : Int) < -k then
          throw s!"{g.name src} doesn't have {-k} loyalty counters to remove (CR 606.4)"
  let outer? := g.pendingReplacement
  let outerForAbort? := outer?.orElse (fun _ => callerOuter?)
  let abortMissingSource (g0 : Game) : Game :=
    if !g0.hasActiveManaProposalCheckpoint && g0.proposedSpell.isSome then
      let g1 :=
        match outerForAbort? with
        | some outer => g0.chainPendingReplacement outer
        | none => g0
      g1.reverseProposedSpellFwd (resumeContinuation := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
    else
      match outer? with
      | some outer => g0.chainPendingReplacement outer
      | none => g0
  let requireLiveSource (g0 : Game) : Option GameObject :=
    match g0.findObject? sourceId with
    | some cur => if cur.isOnBattlefield && g0.controlledBy cur p then some cur else none
    | none => none
  let mut g := if outer?.isSome then g.change (.pendingReplacement none) else g
  if tapNeeded then
    let some curSrc := requireLiveSource g | return abortMissingSource g
    if curSrc.status.tapped then return abortMissingSource g
    g := g.becomeTapped curSrc (cause := some (.costPayment .tap p forObject))
  g := (← g.payLifeCost p payLife (forObject := forObject))
  match ab with
  | some a =>
    let preCounters := g
    let costFromIdx := g.events.size
    let mut removedAnyCounter := false
    let needIndestRem :=
      a.cost.removeIndestructibleCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .indestructible) sinceIdx
    let needPlusRem? : Option Nat :=
      if a.cost.removeAnyNumberPlusOne &&
          !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .plusOnePlusOne) sinceIdx then
        some removePlusOnes
      else none
    let loyDelta? := a.cost.netLoyaltyDelta chosenX
    let needStun :=
      a.cost.putStunCounterOnSource &&
        !g.sourceCounterCostPaidFor sourceId forObject .putCounters (some .stun) sinceIdx
    if a.cost.removeStoryCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters (some .story) sinceIdx then
      let some curSrc := requireLiveSource g | return abortMissingSource g
      if curSrc.status.story == 0 then return abortMissingSource g
      let srcName := g.name curSrc
      g := g.recordRemoveCounters sourceId .story 1 (byPlayer := some p)
        (cause := some (.costPayment .removeCounters p forObject)) (deferPlayFromExileLogs := true)
      g := g.logMsg s!"{(g.player p).name} removes a story counter from {srcName}"
      removedAnyCounter := true
      if g.sbaPaused then
        g := g.chainPendingReplacement
          (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
            .removeCounters sinceIdx needIndestRem needPlusRem? loyDelta? needStun (some costFromIdx))
        if let some outer := outer? then
          g := g.chainPendingReplacement outer
        return g
    if needIndestRem then
      let some curSrc := requireLiveSource g | return abortMissingSource g
      if curSrc.status.indestructibleCounters == 0 then return abortMissingSource g
      g := (← g.payRemoveIndestructibleCounter curSrc forObject (deferPlayFromExileLogs := true))
      removedAnyCounter := true
      if g.sbaPaused then
        g := g.chainPendingReplacement
          (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
            .removeCounters sinceIdx false needPlusRem? loyDelta? needStun (some costFromIdx))
        if let some outer := outer? then
          g := g.chainPendingReplacement outer
        return g
    if needPlusRem?.isSome then
      let some curSrc := requireLiveSource g | return abortMissingSource g
      if curSrc.status.plusOnePlusOne < removePlusOnes then return abortMissingSource g
      let srcName := g.name curSrc
      let g' :=
        if removePlusOnes > 0 then
          g.recordRemoveCounters sourceId .plusOnePlusOne removePlusOnes (byPlayer := some p)
            (cause := some (.costPayment .removeCounters p forObject)) (deferPlayFromExileLogs := true)
        else g
      g := g'.logMsg
        s!"{(g.player p).name} removes {removePlusOnes} +1/+1 counters from {srcName}"
      if removePlusOnes > 0 then
        removedAnyCounter := true
      if g.sbaPaused then
        g := g.chainPendingReplacement
          (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
            .removeCounters sinceIdx false none loyDelta? needStun (some costFromIdx))
        if let some outer := outer? then
          g := g.chainPendingReplacement outer
        return g
    if removedAnyCounter then
      g := emitExpiredPlayFromExileLogs preCounters g costFromIdx
    if let some k := loyDelta? then
      let loyaltyAlreadyPaid :=
        g.proposedSpell.any (·.loyaltyPaid) ||
          g.sourceCounterCostPaidFor sourceId forObject .loyalty (some .loyalty) sinceIdx
      if !loyaltyAlreadyPaid then
        let some curSrc := requireLiveSource g | return abortMissingSource g
        if g.loyaltyActivatedThisTurn curSrc.id then return abortMissingSource g
        if k < 0 && (curSrc.status.loyaltyCounters : Int) < -k then
          return abortMissingSource g
        g := g.payLoyaltyDelta p curSrc k (forObject := forObject)
        if let .chooseReplacement .. := g.pending then
          let needsStun :=
            a.cost.putStunCounterOnSource &&
              !g.sourceCounterCostPaidFor sourceId forObject .putCounters (some .stun) sinceIdx
          if needsStun then
            g := g.chainPendingReplacement
              (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
                .stunAndSacrifice sinceIdx)
          else if sacrificeSource || exileSource then
            g := g.chainPendingReplacement
              (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
                .sacrificeAndExile sinceIdx)
          if let some outer := outer? then
            g := g.chainPendingReplacement outer
          return g
    if a.cost.putStunCounterOnSource &&
        !g.sourceCounterCostPaidFor sourceId forObject .putCounters (some .stun) sinceIdx then
      let some _ := requireLiveSource g | return abortMissingSource g
      g := g.putCountersDeferredLog sourceId .stun 1 (some p) (.playerPutsOn p)
        (cause := some (.costPayment .putCounters p forObject))
      if let .chooseReplacement .. := g.pending then
        if sacrificeSource || exileSource then
          g := g.chainPendingReplacement
            (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
              .sacrificeAndExile sinceIdx)
        if let some outer := outer? then
          g := g.chainPendingReplacement outer
        return g
  | none => pure ()
  g := g.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
    .sacrificeAndExile (sinceIdx := sinceIdx) (outerToRestore? := outerForAbort?)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)
  if hadProp && g.proposedSpell.isNone then
    return g
  if let some outer := outer? then
    g := g.chainPendingReplacement outer
  return g

/-- Colored mana symbols of `col` among `ids` for Zemo's boast, counting hybrid
symbols that include `col` (MSH 128 / CR 612.2). -/
def zemoBoastBlackSymbols (g : Game) (ids : Array ObjectId) (col : Color := .black) : Nat :=
  ids.foldl (fun n id =>
    match g.findObject? id with
    | some o => n + (g.baseCard o).manaCost.symbolsIncludingColor col
    | none => n) 0

/-- True when `ids` are `col` cards in `p`'s graveyard whose mana costs have
fifteen or more `col` mana symbols, including `{col/x}` hybrids (MSH 128 / CR 612.2). -/
def canPayZemoBoast (g : Game) (p : PlayerId) (ids : Array ObjectId) (col : Color := .black) : Bool :=
  !ids.isEmpty &&
    ids.all (fun id =>
      match g.findObject? id with
      | some o =>
        o.zone == .graveyard p && isDiscardableCard o && (g.colors o).contains col
      | none => false) &&
    g.zemoBoastBlackSymbols ids col >= 15

/-- True when a boast ability of `o` may be activated (MSH / CR 702.142). -/
def canActivateBoast (g : Game) (o : GameObject) : Bool :=
  (g.activatedAbilitiesOf o).any ActivatedAbility.isBoast &&
    g.declaredAsAttackerThisTurn o.id && !g.boastUsedThisTurn o.id

/-- Mark a boast activation used for the turn. -/
def markBoastUsed (g : Game) (o : GameObject) : Game :=
  match g.findObject? o.id with
  | some o =>
    let ctrl := (g.controllerOf o).getD o.owner
    let oName := g.name o
    (g.record (GameEvent.abilityActivated g.turnNumber o.id (g.snapshot o) ctrl
      (.nonMana none false false true))).logMsg
      s!"{oName}'s boast ability is activated"
  | none => g

end Game
end Mtg.Engine
