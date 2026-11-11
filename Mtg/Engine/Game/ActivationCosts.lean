import Mtg.Engine.Game.Entering

/-!
# Activation costs (CR 601.2h / 602.2b)

Paying life (CR 118.3b), the source's own costs ({T}, sacrificing or
discarding it, counters), and costs paid with objects the player chooses:
sacrificing, discarding, exiling, or tapping them.
-/

namespace Mtg.Engine
namespace Game

/-- Remove an indestructible counter as a cost (ruling 357). -/
def payRemoveIndestructibleCounter (g : Game) (o : GameObject)
    (forObject : Option ObjectId := none) : Except String Game := do
  if o.status.indestructibleCounters == 0 then
    throw s!"{g.name o} has no indestructible counter"
  let oName := g.name o
  let ctrl := g.controllerOf o
  let p := ctrl.getD o.owner
  let g := g.recordRemoveCounters o.id .indestructible 1 (byPlayer := ctrl) (noActor := ctrl.isNone)
    (cause := some (.costPayment .removeCounters p forObject))
  return g.logMsg s!"{oName} loses an indestructible counter"

/-- Whether `p` can pay `n` life (CR 119.4 / 119.8 / 800.4a). Paying 0 life is always legal for a player in the game. -/
def canPayLife (g : Game) (p : PlayerId) (n : Nat) : Bool :=
  g.stillInGame p &&
    (n == 0 || ((g.player p).life ≥ (n : Int) && !g.lifeLocked p && !g.lifeCantChange p))

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
def sourceSacrificedForCost (g : Game) (sid : ObjectId) (forObject : Option ObjectId) : Bool :=
  match forObject with
  | none => false
  | some fid =>
    fid != sid &&
      g.events.any fun
        | .rules _ (.zone (.moved before _ .battlefield _ ..)) cause _ =>
          before.id == some sid &&
            match unreplacedCostCause cause with
            | .costPayment .sacrifice _ (some f) => f == fid
            | _ => false
        | _ => false

/-- Whether `sid` was already tapped to pay `{T}` for `forObject` (CR 601.2h). -/
def sourceTappedForCost (g : Game) (sid : ObjectId) (forObject : Option ObjectId) : Bool :=
  match forObject with
  | none => false
  | some fid =>
    fid != sid &&
      g.events.any fun
        | .rules _ (.permanent (.tapped snap _)) cause _ =>
          snap.id == some sid &&
            match unreplacedCostCause cause with
            | .costPayment .tap _ (some f) => f == fid
            | _ => false
        | _ => false

/-- Whether `sid` already paid a counter cost of `costKind` for `forObject`
(CR 601.2h). -/
def sourceCounterCostPaidFor (g : Game) (sid : ObjectId) (forObject : Option ObjectId)
    (costKind : CostKind) : Bool :=
  match forObject with
  | none => false
  | some fid =>
    fid != sid &&
      g.events.any fun
        | .rules _ (.permanent (.counters (.object snap) ..)) cause _ =>
          snap.id == some sid &&
            match unreplacedCostCause cause with
            | .costPayment k _ (some f) => k == costKind && f == fid
            | _ => false
        | _ => false

/-- Whether `o` can pay `pick` for `p`'s ability of `sourceId`. -/
def costPickAllows (g : Game) (p : PlayerId) (sourceId : Option ObjectId) (pick : CostPick)
    (o : GameObject)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false) : Bool :=
  let perm := o.isOnBattlefield && g.controlledBy o p
  let inHand := o.owner == p && o.zone == .hand p
  let other := sourceId.all (o.id != ·)
  let artifact := g.isArtifact o
  match pick with
  | .sacrificeAnotherCreature => perm && other && g.isCreature o
  | .sacrificeAnotherSubtype t => perm && other && g.hasSubtype o t

  | .sacrificeArtifact => perm && (!sacrificeOrExileSource || other) && artifact
  | .sacrificeLegendaryArtifact =>
    perm && (!sacrificeOrExileSource || other) && artifact && g.isLegendary o
  | .sacrificeArtifactOrCreature =>
    perm && (!sacrificeOrExileSource || other) && (artifact || g.isCreature o)
  | .sacrificeAnotherArtifact => perm && other && artifact
  | .sacrificeAnotherCreatureOrPlaneswalker =>
    perm && other && (g.isCreature o || g.isPlaneswalker o)
  | .sacrificeArtifactOrLand =>
    perm && (!sacrificeOrExileSource || other) && (artifact || g.isLand o)
  | .sacrificeEquipmentAttachedToSource =>
    perm && (!sacrificeOrExileSource || other) && g.isEquipment o &&
      sourceId.isSome && o.attachedTo == sourceId
  | .sacrificeArtifactOrDiscardNonland =>
    (perm && (!sacrificeOrExileSource || other) && artifact) ||
      (inHand && (!discardOrExileHandSource || other) && !g.isLand o)
  | .discardACard => inHand && (!discardOrExileHandSource || other)
  | .discardNonland => inHand && (!discardOrExileHandSource || other) && !g.isLand o
  | .discardLegendaryCard => inHand && (!discardOrExileHandSource || other) && g.isLegendary o
  | .discardLegendarySameName =>
    inHand && (!discardOrExileHandSource || other) && g.isLegendary o &&
      (g.permanentsOf p).any (fun x => g.isLegendary x && g.name x == g.name o)
  | .exileAnotherCreatureCardFromGraveyard =>
    other && o.owner == p && o.zone == .graveyard p && g.isCreature o
  | .tapUntappedCreature => perm && (!tapSource || other) && g.isCreature o && !o.status.tapped
  | .tapTwoUntappedArtifacts => perm && (!tapSource || other) && artifact && !o.status.tapped

/-- Objects that can pay `pick`, in a default order (tokens and cheaper
permanents first). -/
def costPickCandidates (g : Game) (p : PlayerId) (sourceId : Option ObjectId) (pick : CostPick)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false) :
    Array ObjectId :=
  let pl := g.player p
  let zoneCards (ids : Array ObjectId) := ids.filterMap g.findObject?
  let pool := g.cheapestFirst (g.permanentsOf p) ++ zoneCards pl.hand ++ zoneCards pl.graveyard
  (pool.filter (g.costPickAllows p sourceId pick
    (tapSource := tapSource)
    (sacrificeOrExileSource := sacrificeOrExileSource)
    (discardOrExileHandSource := discardOrExileHandSource))).map (·.id)

private partial def assignDisjointPicks (g : Game) (p : PlayerId) (sourceId : Option ObjectId)
    (picks : Array CostPick) (tapSource sacrificeOrExileSource discardOrExileHandSource : Bool)
    (idx : Nat) (used : Array ObjectId) : Option (Array ObjectId) :=
  if idx ≥ picks.size then some #[]
  else
    let pick := picks[idx]!
    let cands :=
      (g.costPickCandidates p sourceId pick
        (tapSource := tapSource)
        (sacrificeOrExileSource := sacrificeOrExileSource)
        (discardOrExileHandSource := discardOrExileHandSource)).filter (!used.contains ·)
    if cands.size < pick.count then none
    else if idx + 1 == picks.size then
      some (cands.extract 0 pick.count)
    else
      let rec chooseK (start left : Nat) (picked : Array ObjectId) : Option (Array ObjectId) :=
        if left == 0 then
          if (assignDisjointPicks g p sourceId picks tapSource sacrificeOrExileSource
                discardOrExileHandSource (idx + 1) (used ++ picked)).isSome then
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
    (discardOrExileHandSource : Bool := false) : Option (Array ObjectId) :=
  if picks.isEmpty then none
  else
    assignDisjointPicks g p sourceId picks tapSource sacrificeOrExileSource
      discardOrExileHandSource 0 #[]

/-- Whether every pick can be paid by different objects, accounting for whether
`sourceId` itself is separately tapped, sacrificed/exiled, or discarded/exiled
from hand (CR 602.2b / 118.3 / 118.10). -/
def costPicksPayable (g : Game) (p : PlayerId) (sourceId : Option ObjectId) (picks : Array CostPick)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false) :
    Bool :=
  (assignDisjointPicks g p sourceId picks tapSource sacrificeOrExileSource
    discardOrExileHandSource 0 #[]).isSome

/-- Pay one or more already-validated `ids` for `pick` on `abilityId` / `sourceId`,
chaining `.payCostPickItems` if an earlier move or sacrifice pauses on
`Pending.chooseReplacement` (`pick.count >= 2`). -/
def payCostPickItems (g : Game) (p : PlayerId) (abilityId sourceId : Option ObjectId)
    (pick : CostPick) (ids : Array ObjectId) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.payCostPickItems p abilityId sourceId pick ids)
  else
    let forObj : Option ObjectId := abilityId
    let run (g : Game) : Game := Id.run do
      let name := (g.player p).name
      let mut g := g
      for i in [0:ids.size] do
        let id := ids[i]!
        if let some o := g.findObject? id then
          match pick with
          | .tapUntappedCreature | .tapTwoUntappedArtifacts =>
            let oName := g.name o
            g := (g.becomeTapped o (cause := some (.costPayment .tap p forObj))).logMsg
              s!"{name} taps {oName} to pay a cost"
          | .exileAnotherCreatureCardFromGraveyard =>
            let msg := s!"{name} exiles {g.name o} from their graveyard"
            g := (g.move id .exile none (cause := some (.costPayment .exile p forObj))).1
            if let .chooseReplacement .. := g.pending then
              g := g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id msg))
            else if (g.followMovedToZone? id (· == .exile)).isSome then
              g := g.logMsg msg
          | _ =>
            if o.isOnBattlefield then
              let records :=
                g.isCreature o && (abilityId.bind g.findObject?).any (fun ab =>
                  (ab.abilityEffect.map (·.resolution)) ==
                    some (.sequence [.drawEqualToLastKnownPower, .discard (.cards 1)]))
              let pw := g.power o
              let oName := g.name o
              g := g.sacrificeToGraveyard o s!"{name} sacrifices {oName}"
                (cause := some (.costPayment .sacrifice p forObj))
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
                (cause := some (.costPayment .discard p forObj))).1
              -- CR 614.6 / 701.9a: log the discard only once the card reaches
              -- its owner's graveyard.
              if let .chooseReplacement .. := g.pending then
                g := g.chainPendingReplacement
                  (.finishPostStep (.logDiscardIfInGraveyard id owner msg))
              else if (g.followMovedToZone? id (· == .graveyard owner)).isSome then
                g := g.logMsg msg
          if let .chooseReplacement .. := g.pending then
            let rem := ids.extract (i + 1) ids.size
            if !rem.isEmpty then
              g := g.chainPendingReplacement (.payCostPickItems p abilityId sourceId pick rem)
            return g
      return g
    match pick with
    | .tapTwoUntappedArtifacts =>
      if g.currentBatch.isSome || ids.size ≤ 1 then run g
      else g.withBatch (some (.costPayment .tap p forObj)) run
    | _ => run g

/-- Pay `pick` with `ids` for the ability `abilityId` of `sourceId`
(CR 601.2h). The power of a creature sacrificed for an ability that refers
to it is recorded on the ability (Tom, Bert, and William). -/
def payCostPick (g : Game) (p : PlayerId) (abilityId sourceId : Option ObjectId) (pick : CostPick)
    (ids : Array ObjectId)
    (tapSource : Bool := false)
    (sacrificeOrExileSource : Bool := false)
    (discardOrExileHandSource : Bool := false) : Except String Game :=
  g.withProposalActionM .costAction fun g => do
  if ids.size != pick.count || ids.toList.eraseDups.length != ids.size then
    throw s!"Choose {pick.count} to {pick.phrase}"
  for id in ids do
    let some o := g.findObject? id | throw "no such object"
    if !g.costPickAllows p sourceId pick o
        (tapSource := tapSource)
        (sacrificeOrExileSource := sacrificeOrExileSource)
        (discardOrExileHandSource := discardOrExileHandSource) then
      throw s!"{g.name o} can't be used to {pick.phrase}"
  let outer? := g.pendingReplacement
  let mut g := if outer?.isSome then g.change (.pendingReplacement none) else g
  let isBfSacPick : Bool :=
    match pick with
    | .tapUntappedCreature | .tapTwoUntappedArtifacts
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
            let tapNeeded := effTap && !g.sourceTappedForCost sid forObj
            if !g.controlledBy src p then
              throw "You don't control that permanent"
            if tapNeeded && src.status.tapped then
              throw s!"{g.name src} is already tapped"
            if let some a := effAb? then
              if a.cost.removeStoryCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters &&
                  src.status.story == 0 then
                throw s!"{g.name src} has no story counter"
              if a.cost.removeIndestructibleCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters &&
                  src.status.indestructibleCounters == 0 then
                throw s!"{g.name src} has no indestructible counter"
              if a.cost.removeAnyNumberPlusOne &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters &&
                  src.status.plusOnePlusOne < effRemovePlusOnes then
                throw s!"{g.name src} doesn't have {effRemovePlusOnes} +1/+1 counters"
              if let some sym := a.cost.loyalty then
                let k := if sym == LoyaltySymbol.minusX then -(effX : Int) else sym.counters.getD 0
                if !g.sourceCounterCostPaidFor sid forObj .loyalty &&
                    k < 0 && (src.status.loyaltyCounters : Int) < -k then
                  throw s!"{g.name src} doesn't have {-k} loyalty counters to remove (CR 606.4)"
            if tapNeeded then
              g := g.becomeTapped (g.object! sid) (cause := some (.costPayment .tap p forObj))
            if let some a := effAb? then
              if a.cost.removeStoryCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters then
                let curSrc := g.object! sid
                let srcName := g.name curSrc
                g := g.recordRemoveCounters sid .story 1 (byPlayer := some p)
                  (cause := some (.costPayment .removeCounters p forObj))
                g := g.logMsg s!"{(g.player p).name} removes a story counter from {srcName}"
              if a.cost.removeIndestructibleCounter &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters then
                g := (← g.payRemoveIndestructibleCounter (g.object! sid) forObj)
              if a.cost.removeAnyNumberPlusOne &&
                  !g.sourceCounterCostPaidFor sid forObj .removeCounters then
                let curSrc := g.object! sid
                let srcName := g.name curSrc
                let g' :=
                  if effRemovePlusOnes > 0 then
                    g.recordRemoveCounters sid .plusOnePlusOne effRemovePlusOnes (byPlayer := some p)
                      (cause := some (.costPayment .removeCounters p forObj))
                  else g
                g := g'.logMsg
                  s!"{(g.player p).name} removes {effRemovePlusOnes} +1/+1 counters from {srcName}"
              if let some sym := a.cost.loyalty then
                if !g.sourceCounterCostPaidFor sid forObj .loyalty then
                  let k := if sym == LoyaltySymbol.minusX then -(effX : Int) else sym.counters.getD 0
                  let srcName := g.name (g.object! sid)
                  if k > 0 then
                    g := g.putCountersDeferredLog sid .loyalty k.natAbs (some p) .countArePutOn
                      (cause := some (.costPayment .loyalty p forObj))
                  else if k < 0 then
                    g := (g.recordRemoveCounters sid .loyalty k.natAbs (byPlayer := some p)
                      (cause := some (.costPayment .loyalty p forObj))).logMsg
                      s!"{-k} loyalty counter(s) are removed from {srcName}"
              if a.cost.putStunCounterOnSource &&
                  !g.sourceCounterCostPaidFor sid forObj .putCounters then
                g := g.putCountersDeferredLog sid .stun 1 (some p) (.playerPutsOn p)
                  (cause := some (.costPayment .putCounters p forObj))
  g := g.payCostPickItems p abilityId sourceId pick ids
  return match outer? with
    | some outer => g.chainPendingReplacement outer
    | none => g

/-- Finish the remaining steps of `payActivationExtraCosts` after an earlier
counter or sacrifice step paused on `Pending.chooseReplacement`. -/
def finishActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (forObject : Option ObjectId) (sacrificeSource exileSource : Bool)
    (stage : ActivationExtraCostStage := .sacrificeAndExile) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource stage)
  let mut g := g
  if stage == .sacrificeAndExile && sacrificeSource then
    if let some src := g.findObject? sourceId then
      g := g.sacrificeToGraveyard src
        s!"{(g.player p).name} sacrifices {g.name src}"
        (cause := some (.costPayment .sacrifice p forObject))
      if let .chooseReplacement .. := g.pending then
        if exileSource then
          g := g.chainPendingReplacement
            (.finishActivationExtraCosts p sourceId forObject false exileSource .exileOnly)
        return g
  if exileSource then
    if let some src := g.findObject? sourceId then
      if src.isOnBattlefield then
        let msg := s!"{(g.player p).name} exiles {g.name src}"
        g := (g.move sourceId .exile none
          (cause := some (.costPayment .exile p forObject))).1
        if let .chooseReplacement .. := g.pending then
          g := g.chainPendingReplacement
            (.finishPostStep (.logExiledIfInExile sourceId msg))
        else if (g.followMovedToZone? sourceId (· == .exile)).isSome then
          g := g.logMsg msg
  return g

/-- Pay `{T}`, life, discard, and/or sacrifice the source, and the source's
counter costs, as part of an activation cost (CR 601.2h / 118.3b / 702.29).
Costs paid with chosen objects are paid by `payCostPick`. -/
def payActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (tapSource sacrificeSource : Bool) (payLife : Nat := 0)
    (discardSource : Bool := false)
    (ab : Option ActivatedAbility := none) (removePlusOnes : Nat := 0)
    (forObject? : Option ObjectId := none) :
    Except String Game :=
  g.withProposalActionM .costAction fun g => do
  let forObject := forObject? <|> g.proposedSpell.map (·.spellId) <|> some sourceId
  let exileSource := ab.any (·.cost.fra == .exileSource)
  let sacrificeOrExileSource :=
    sacrificeSource || exileSource || ab.any (·.cost.sacrificeSource)
  let alreadySacrificedForCost :=
    !sacrificeOrExileSource && !discardSource &&
      !ab.any (fun a =>
        a.activateFromGraveyard || a.activateFromHand || a.cost.fra == .exileSourceFromHand) &&
      g.sourceSacrificedForCost sourceId forObject
  let some src := g.findObject? sourceId | do
    if alreadySacrificedForCost then
      if !g.canPayLife p payLife then
        throw s!"{(g.player p).name} cannot pay {payLife} life"
      return (← g.payLifeCost p payLife (forObject := forObject))
    throw "The source is no longer in play"
  if ab.any (·.cost.fra == .exileSourceFromHand) then
    if !(src.zone == .hand src.owner && src.owner == p) then
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
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{g.name src} is not in your hand"
    let g ← g.payLifeCost p payLife (forObject := forObject)
    let src := g.object! sourceId
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
  let fromGraveyard :=
    ab.any (·.activateFromGraveyard) &&
      src.zone == .graveyard src.owner && src.owner == p &&
      !ab.any (·.cost.loyalty.isSome)
  if fromGraveyard && !tapSource && !sacrificeSource then
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
  if !src.isOnBattlefield then
    if alreadySacrificedForCost then
      if !g.canPayLife p payLife then
        throw s!"{(g.player p).name} cannot pay {payLife} life"
      return (← g.payLifeCost p payLife (forObject := forObject))
    throw "The source is no longer on the battlefield"
  if !g.controlledBy src p then
    throw "You don't control that permanent"
  let tapNeeded := tapSource && !g.sourceTappedForCost sourceId forObject
  if tapNeeded && src.status.tapped then
    throw s!"{g.name src} is already tapped"
  if !g.canPayLife p payLife then
    throw s!"{(g.player p).name} cannot pay {payLife} life"
  if let some a := ab then
    if a.cost.removeStoryCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters &&
        src.status.story == 0 then
      throw s!"{g.name src} has no story counter"
    if a.cost.removeIndestructibleCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters &&
        src.status.indestructibleCounters == 0 then
      throw s!"{g.name src} has no indestructible counter"
    if a.cost.removeAnyNumberPlusOne &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters &&
        src.status.plusOnePlusOne < removePlusOnes then
      throw s!"{g.name src} doesn't have {removePlusOnes} +1/+1 counters"
  let outer? := g.pendingReplacement
  let mut g := if outer?.isSome then g.change (.pendingReplacement none) else g
  if tapNeeded then
    g := g.becomeTapped (g.object! sourceId) (cause := some (.costPayment .tap p forObject))
  g := (← g.payLifeCost p payLife (forObject := forObject))
  match ab with
  | some a =>
    if a.cost.removeStoryCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters then
      let src := g.object! sourceId
      let srcName := g.name src
      g := g.recordRemoveCounters sourceId .story 1 (byPlayer := some p)
        (cause := some (.costPayment .removeCounters p forObject))
      g := g.logMsg s!"{(g.player p).name} removes a story counter from {srcName}"
    if a.cost.removeIndestructibleCounter &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters then
      g := (← g.payRemoveIndestructibleCounter (g.object! sourceId) forObject)
    if a.cost.removeAnyNumberPlusOne &&
        !g.sourceCounterCostPaidFor sourceId forObject .removeCounters then
      let src := g.object! sourceId
      let srcName := g.name src
      let g' :=
        if removePlusOnes > 0 then
          g.recordRemoveCounters sourceId .plusOnePlusOne removePlusOnes (byPlayer := some p)
            (cause := some (.costPayment .removeCounters p forObject))
        else g
      g := g'.logMsg
        s!"{(g.player p).name} removes {removePlusOnes} +1/+1 counters from {srcName}"
    if a.cost.putStunCounterOnSource &&
        !g.sourceCounterCostPaidFor sourceId forObject .putCounters then
      g := g.putCountersDeferredLog sourceId .stun 1 (some p) (.playerPutsOn p)
        (cause := some (.costPayment .putCounters p forObject))
      if let .chooseReplacement .. := g.pending then
        if sacrificeSource || exileSource then
          g := g.chainPendingReplacement
            (.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
              .sacrificeAndExile)
        if let some outer := outer? then
          g := g.chainPendingReplacement outer
        return g
  | none => pure ()
  g := g.finishActivationExtraCosts p sourceId forObject sacrificeSource exileSource
    .sacrificeAndExile
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
        o.zone == .graveyard p && (g.colors o).contains col
      | none => false) &&
    g.zemoBoastBlackSymbols ids col >= 15

/-- True when a boast ability of `o` may be activated (MSH / CR 702.142). -/
def canActivateBoast (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (· == .boast) &&
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
