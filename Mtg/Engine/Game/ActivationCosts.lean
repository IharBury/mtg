import Mtg.Engine.Game.SpellTargets

/-!
# Activation costs (CR 601.2h / 602.2b)

Paying life (CR 118.3b), the source's own costs ({T}, sacrificing or
discarding it, counters), and costs paid with objects the player chooses:
sacrificing, discarding, exiling, or tapping them.
-/

namespace Mtg.Engine
namespace Game

/-- Remove an indestructible counter as a cost (ruling 357). -/
def payRemoveIndestructibleCounter (g : Game) (o : GameObject) : Except String Game := do
  if o.status.indestructibleCounters == 0 then
    throw s!"{o.name} has no indestructible counter"
  let g := g.setObject { o with status :=
    { o.status with indestructibleCounters := o.status.indestructibleCounters - 1 } }
  return g.logMsg s!"{o.name} loses an indestructible counter"

/-- Whether `p` can pay `n` life (CR 119.4). Paying 0 life is always legal. -/
def canPayLife (g : Game) (p : PlayerId) (n : Nat) : Bool :=
  n == 0 || (g.player p).life ≥ (n : Int)

/-- Pay `n` life as a cost (CR 118.3b / 119.4). Payment of life is not damage. -/
def payLifeCost (g : Game) (p : PlayerId) (n : Nat) : Except String Game := do
  if n == 0 then
    return g
  let pl := g.player p
  if pl.life < (n : Int) then
    throw s!"{pl.name} cannot pay {n} life"
  return g.setLife p (pl.life - (n : Int))
    s!"{pl.name} pays {n} life ({pl.life - (n : Int)} life)"

/-- Default order for paying a cost with permanents: tokens first, then the
lowest mana value. -/
def cheapestFirst (g : Game) (cands : Array GameObject) : Array GameObject :=
  let key (x : GameObject) : Nat := (if x.printed.isToken then 0 else 1000) + g.objectManaValue x
  cands.qsort (fun a b => key a < key b)

/-- Parts of `ab`'s cost the player chooses what to pay with (CR 601.2h). -/
def costPicksOf (ab : ActivatedAbility) : Array CostPick :=
  let c := ab.cost
  let fra : Array CostPick :=
    match c.fra with
    | .exileAnotherCreatureCardFromGraveyard => #[.exileAnotherCreatureCardFromGraveyard]
    | .sacrificeAnotherArtifact => #[.sacrificeAnotherArtifact]
    | .sacrificeAnotherCreatureOrPlaneswalker => #[.sacrificeAnotherCreatureOrPlaneswalker]
    | .sacrificeArtifactOrLand => #[.sacrificeArtifactOrLand]
    | .discardLegendaryCard => #[.discardLegendaryCard]
    | .tapTwoUntappedArtifacts => #[.tapTwoUntappedArtifacts]
    | _ => #[]
  (if c.discardACard then #[CostPick.discardACard] else #[]) ++
  (if c.discardLegendarySameName then #[CostPick.discardLegendarySameName] else #[]) ++
  (if c.sacrificeLegendaryArtifact then #[CostPick.sacrificeLegendaryArtifact] else #[]) ++
  (if c.sacrificeArtifact then #[CostPick.sacrificeArtifact] else #[]) ++
  (if c.sacrificeArtifactOrCreature then #[CostPick.sacrificeArtifactOrCreature] else #[]) ++
  (if c.sacrificeArtifactOrDiscardNonland then
    #[CostPick.sacrificeArtifactOrDiscardNonland] else #[]) ++
  (if c.sacrificeEquipmentAttachedToSource then
    #[CostPick.sacrificeEquipmentAttachedToSource] else #[]) ++
  (if c.tapAnUntappedCreatureYouControl then #[CostPick.tapUntappedCreature] else #[]) ++
  (match c.sacrificeAnotherSubtype with
   | some t => #[CostPick.sacrificeAnotherSubtype t]
   | none => #[]) ++ fra

/-- Whether `o` can pay `pick` for `p`'s ability of `sourceId`. -/
def costPickAllows (g : Game) (p : PlayerId) (sourceId : ObjectId) (pick : CostPick)
    (o : GameObject) : Bool :=
  let perm := o.isOnBattlefield && o.controlledBy p
  let inHand := o.owner == p && o.zone == .hand p
  let other := o.id != sourceId
  let artifact := o.types.contains .artifact
  match pick with
  | .sacrificeAnotherSubtype t =>
    perm && other && (if t == "Creature" then o.isCreature else g.hasSubtype o t)
  | .sacrificeArtifact => perm && artifact
  | .sacrificeLegendaryArtifact => perm && artifact && o.isLegendary
  | .sacrificeArtifactOrCreature => perm && (artifact || o.isCreature)
  | .sacrificeAnotherArtifact => perm && other && artifact
  | .sacrificeAnotherCreatureOrPlaneswalker =>
    perm && other && (o.isCreature || o.printed.isPlaneswalker)
  | .sacrificeArtifactOrLand => perm && (artifact || o.printed.isLand)
  | .sacrificeEquipmentAttachedToSource =>
    perm && o.printed.isEquipment && o.attachedTo == some sourceId
  | .sacrificeArtifactOrDiscardNonland =>
    (perm && artifact) || (inHand && !o.printed.isLand)
  | .discardACard => inHand
  | .discardLegendaryCard => inHand && o.isLegendary
  | .discardLegendarySameName =>
    inHand && o.isLegendary &&
      (g.permanentsOf p).any (fun x => x.isLegendary && x.name == o.name)
  | .exileAnotherCreatureCardFromGraveyard =>
    other && o.owner == p && o.zone == .graveyard p && o.printed.isCreature
  | .tapUntappedCreature => perm && o.isCreature && !o.status.tapped
  | .tapTwoUntappedArtifacts => perm && artifact && !o.status.tapped

/-- Objects that can pay `pick`, in a default order (tokens and cheaper
permanents first). -/
def costPickCandidates (g : Game) (p : PlayerId) (sourceId : ObjectId) (pick : CostPick) :
    Array ObjectId :=
  let pl := g.player p
  let zoneCards (ids : Array ObjectId) := ids.filterMap g.findObject?
  let pool := g.cheapestFirst (g.permanentsOf p) ++ zoneCards pl.hand ++ zoneCards pl.graveyard
  (pool.filter (g.costPickAllows p sourceId pick)).map (·.id)

/-- Whether every pick can be paid by different objects, assuming the
source is tapped or sacrificed separately (CR 602.2b). -/
def costPicksPayable (g : Game) (p : PlayerId) (sourceId : ObjectId) (picks : Array CostPick) :
    Bool :=
  let (ok, _) := picks.foldl (fun (acc : Bool × Array ObjectId) pick =>
    let cands := (g.costPickCandidates p sourceId pick).filter (!acc.2.contains ·)
    if cands.size < pick.count then (false, acc.2)
    else (acc.1, acc.2 ++ cands.extract 0 pick.count)) (true, #[])
  ok

/-- Pay `pick` with `ids` for the ability `abilityId` of `sourceId`
(CR 601.2h). The power of a creature sacrificed for an ability that refers
to it is recorded on the ability (Tom, Bert, and William). -/
def payCostPick (g : Game) (p : PlayerId) (abilityId sourceId : ObjectId) (pick : CostPick)
    (ids : Array ObjectId) : Except String Game := do
  if ids.size != pick.count || ids.toList.eraseDups.length != ids.size then
    throw s!"Choose {pick.count} to {pick.phrase}"
  let name := (g.player p).name
  let mut g := g
  for id in ids do
    let some o := g.findObject? id | throw "no such object"
    if !g.costPickAllows p sourceId pick o then
      throw s!"{o.name} can't be used to {pick.phrase}"
    match pick with
    | .tapUntappedCreature | .tapTwoUntappedArtifacts =>
      g := (g.becomeTapped o).logMsg s!"{name} taps {o.name} to pay a cost"
    | .exileAnotherCreatureCardFromGraveyard =>
      g := (g.move id .exile none).1.logMsg s!"{name} exiles {o.name} from their graveyard"
    | _ =>
      if o.isOnBattlefield then
        let records :=
          o.isCreature && (g.findObject? abilityId).any (fun ab =>
            (ab.abilityEffect.map (·.resolution)) == some .drawEqualSacrificedPowerThenDiscard)
        let pw := g.power o
        g := g.sacrificeToGraveyard o s!"{name} sacrifices {o.name}"
        if records then
          if let some ab := g.findObject? abilityId then
            g := g.setObject { ab with lastKnownPower := some pw }
      else
        g := (g.move id (.graveyard o.owner) none).1.logMsg s!"{name} discards {o.name}"
        g := g.modifyPlayer p (fun pl =>
          { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })
  return g

/-- Pay `{T}`, life, discard, and/or sacrifice the source, and the source's
counter costs, as part of an activation cost (CR 601.2h / 118.3b / 702.29).
Costs paid with chosen objects are paid by `payCostPick`. -/
def payActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (tapSource sacrificeSource : Bool) (payLife : Nat := 0)
    (discardSource : Bool := false)
    (ab : Option ActivatedAbility := none) (removePlusOnes : Nat := 0) :
    Except String Game := do
  let some src := g.findObject? sourceId | throw "The source is no longer in play"
  if ab.any (·.cost.fra == .exileSourceFromHand) then
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{src.name} is not in your hand"
    let g ← g.payLifeCost p payLife
    let g := g.logMsg s!"{(g.player p).name} exiles {src.name} from their hand"
    return (g.move sourceId .exile none).1
  if discardSource then
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{src.name} is not in your hand"
    let g ← g.payLifeCost p payLife
    let src := g.object! sourceId
    let g := g.logMsg s!"{(g.player p).name} discards {src.name}"
    let (g, _) := g.move sourceId (.graveyard src.owner) none
    return g
  let fromGraveyard := src.zone == .graveyard src.owner && src.owner == p
  if fromGraveyard && !tapSource && !sacrificeSource then
    let g ← g.payLifeCost p payLife
    if ab.any (·.cost.exileSourceFromGraveyard) then
      let g := g.logMsg s!"{(g.player p).name} exiles {src.name} from their graveyard"
      return (g.move sourceId .exile none).1
    return g
  if !src.isOnBattlefield then
    throw "The source is no longer on the battlefield"
  if !src.controlledBy p then
    throw "You don't control that permanent"
  let mut g := g
  if tapSource then
    let src := g.object! sourceId
    if src.status.tapped then
      throw s!"{src.name} is already tapped"
    g := g.becomeTapped src
  g := (← g.payLifeCost p payLife)
  match ab with
  | some a =>
    if a.cost.removeIndestructibleCounter then
      g := (← g.payRemoveIndestructibleCounter (g.object! sourceId))
    if a.cost.putStunCounterOnSource then
      let src := g.object! sourceId
      g := (g.setObject { src with status := { src.status with stun := src.status.stun + 1 } }).logMsg
        s!"{(g.player p).name} puts a stun counter on {src.name}"
    if a.cost.removeAnyNumberPlusOne then
      let src := g.object! sourceId
      if src.status.plusOnePlusOne < removePlusOnes then
        throw s!"{src.name} doesn't have {removePlusOnes} +1/+1 counters"
      g := (g.setObject { src with status := { src.status with
        plusOnePlusOne := src.status.plusOnePlusOne - removePlusOnes } }).logMsg
        s!"{(g.player p).name} removes {removePlusOnes} +1/+1 counters from {src.name}"
  | none => pure ()
  if sacrificeSource then
    match g.findObject? sourceId with
    | none => pure ()
    | some src =>
      g := g.sacrificeToGraveyard src
        s!"{(g.player p).name} sacrifices {src.name}"
  if ab.any (·.cost.fra == .exileSource) then
    match g.findObject? sourceId with
    | some src =>
      if src.isOnBattlefield then
        g := (g.move sourceId .exile none).1.logMsg s!"{(g.player p).name} exiles {src.name}"
    | none => pure ()
  return g

end Game
end Mtg.Engine
