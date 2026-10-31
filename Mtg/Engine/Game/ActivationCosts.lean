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
  let ctrl := g.controllerOf o
  let p := ctrl.getD o.owner
  let g := g.record (GameEvent.counters g.turnNumber ctrl (g.snapshot o) .indestructible 1 true
    (cause := .costPayment .removeCounters p forObject))
  return g.logMsg s!"{g.name o} loses an indestructible counter"

/-- Whether `p` can pay `n` life (CR 119.4). Paying 0 life is always legal. -/
def canPayLife (g : Game) (p : PlayerId) (n : Nat) : Bool :=
  n == 0 || (g.player p).life ≥ (n : Int)

/-- Pay `n` life as a cost (CR 118.3b / 119.4). Payment of life is not damage. -/
def payLifeCost (g : Game) (p : PlayerId) (n : Nat)
    (forObject : Option ObjectId := none)
    (cause : Option EventCause := some (.costPayment .life p forObject)) : Except String Game := do
  if n == 0 then
    return g
  let pl := g.player p
  if pl.life < (n : Int) then
    throw s!"{pl.name} cannot pay {n} life"
  let effCause :=
    g.resolveOptionalCause cause (fallbackCtrl := some p)
      (defaultCause := .costPayment .life p forObject)
  let g :=
    if g.lifeLocked p || g.lifeCantChange p then
      g.logMsg s!"{pl.name}'s life total can't change"
    else
      (g.record (GameEvent.life g.turnNumber p n false false false
        (cause := effCause))).logMsg
        s!"{pl.name} pays {n} life ({pl.life - (n : Int)} life)"
  return g

/-- Default order for paying a cost with permanents: tokens first, then the
lowest mana value. -/
def cheapestFirst (g : Game) (cands : Array GameObject) : Array GameObject :=
  let key (x : GameObject) : Nat := (if x.printed.isToken then 0 else 1000) + g.objectManaValue x
  cands.qsort (fun a b => key a < key b)

/-- Whether `o` can pay `pick` for `p`'s ability of `sourceId`. -/
def costPickAllows (g : Game) (p : PlayerId) (sourceId : ObjectId) (pick : CostPick)
    (o : GameObject) : Bool :=
  let perm := o.isOnBattlefield && g.controlledBy o p
  let inHand := o.owner == p && o.zone == .hand p
  let other := o.id != sourceId
  let artifact := g.isArtifact o
  match pick with
  | .sacrificeAnotherCreature => perm && other && g.isCreature o
  | .sacrificeAnotherSubtype t => perm && other && g.hasSubtype o t

  | .sacrificeArtifact => perm && artifact
  | .sacrificeLegendaryArtifact => perm && artifact && g.isLegendary o
  | .sacrificeArtifactOrCreature => perm && (artifact || g.isCreature o)
  | .sacrificeAnotherArtifact => perm && other && artifact
  | .sacrificeAnotherCreatureOrPlaneswalker =>
    perm && other && (g.isCreature o || g.isPlaneswalker o)
  | .sacrificeArtifactOrLand => perm && (artifact || g.isLand o)
  | .sacrificeEquipmentAttachedToSource =>
    perm && g.isEquipment o && o.attachedTo == some sourceId
  | .sacrificeArtifactOrDiscardNonland =>
    (perm && artifact) || (inHand && !o.printed.isLand)
  | .discardACard => inHand
  | .discardNonland => inHand && !o.printed.isLand
  | .discardLegendaryCard => inHand && o.isLegendary
  | .discardLegendarySameName =>
    inHand && o.isLegendary &&
      (g.permanentsOf p).any (fun x => g.isLegendary x && g.name x == o.name)
  | .exileAnotherCreatureCardFromGraveyard =>
    other && o.owner == p && o.zone == .graveyard p && o.printed.isCreature
  | .tapUntappedCreature => perm && g.isCreature o && !o.status.tapped
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
    (ids : Array ObjectId) : Except String Game :=
  g.withProposalActionM .costAction fun g => do
  if ids.size != pick.count || ids.toList.eraseDups.length != ids.size then
    throw s!"Choose {pick.count} to {pick.phrase}"
  let name := (g.player p).name
  let mut g := g
  for id in ids do
    let some o := g.findObject? id | throw "no such object"
    if !g.costPickAllows p sourceId pick o then
      throw s!"{g.name o} can't be used to {pick.phrase}"
    match pick with
    | .tapUntappedCreature | .tapTwoUntappedArtifacts =>
      let oName := g.name o
      g := (g.becomeTapped o (cause := some (.costPayment .tap p (some abilityId)))).logMsg
        s!"{name} taps {oName} to pay a cost"
    | .exileAnotherCreatureCardFromGraveyard =>
      g := (g.move id .exile none (cause := some (.costPayment .exile p (some abilityId)))).1.logMsg
        s!"{name} exiles {o.name} from their graveyard"
    | _ =>
      if o.isOnBattlefield then
        let records :=
          g.isCreature o && (g.findObject? abilityId).any (fun ab =>
            (ab.abilityEffect.map (·.resolution)) ==
              some (.sequence [.drawEqualToLastKnownPower, .discard (.cards 1)]))
        let pw := g.power o
        let oName := g.name o
        g := g.sacrificeToGraveyard o s!"{name} sacrifices {oName}"
          (cause := some (.costPayment .sacrifice p (some abilityId)))
        if records then
          if (g.findObject? abilityId).isSome then
            g := g.setStackEntryLastKnown abilityId (lastKnownPower := some pw)
      else
        g := (g.move id (.graveyard o.owner) none
          (cause := some (.costPayment .discard p (some abilityId)))).1.logMsg
          s!"{name} discards {o.name}"
  return g

/-- Pay `{T}`, life, discard, and/or sacrifice the source, and the source's
counter costs, as part of an activation cost (CR 601.2h / 118.3b / 702.29).
Costs paid with chosen objects are paid by `payCostPick`. -/
def payActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (tapSource sacrificeSource : Bool) (payLife : Nat := 0)
    (discardSource : Bool := false)
    (ab : Option ActivatedAbility := none) (removePlusOnes : Nat := 0) :
    Except String Game :=
  g.withProposalActionM .costAction fun g => do
  let some src := g.findObject? sourceId | throw "The source is no longer in play"
  let forObject := g.proposedSpell.map (·.spellId) <|> some sourceId
  if ab.any (·.cost.fra == .exileSourceFromHand) then
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{src.name} is not in your hand"
    let g ← g.payLifeCost p payLife
    let g := g.logMsg s!"{(g.player p).name} exiles {src.name} from their hand"
    return (g.move sourceId .exile none (cause := some (.costPayment .exile p forObject))).1
  if discardSource then
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{src.name} is not in your hand"
    let g ← g.payLifeCost p payLife
    let src := g.object! sourceId
    let g := g.logMsg s!"{(g.player p).name} discards {src.name}"
    let (g, _) := g.move sourceId (.graveyard src.owner) none
      (cause := some (.costPayment .discard p forObject))
    return g
  let fromGraveyard :=
    src.zone == .graveyard src.owner && src.owner == p &&
      !ab.any (·.cost.loyalty.isSome)
  if fromGraveyard && !tapSource && !sacrificeSource then
    let g ← g.payLifeCost p payLife
    if ab.any (·.cost.exileSourceFromGraveyard) then
      let g := g.logMsg s!"{(g.player p).name} exiles {src.name} from their graveyard"
      return (g.move sourceId .exile none (cause := some (.costPayment .exile p forObject))).1
    return g
  if !src.isOnBattlefield then
    throw "The source is no longer on the battlefield"
  if !g.controlledBy src p then
    throw "You don't control that permanent"
  let mut g := g
  if tapSource then
    let src := g.object! sourceId
    if src.status.tapped then
      throw s!"{g.name src} is already tapped"
    g := g.becomeTapped src (cause := some (.costPayment .tap p forObject))
  g := (← g.payLifeCost p payLife)
  match ab with
  | some a =>
    if a.cost.removeStoryCounter then
      let src := g.object! sourceId
      if src.status.story == 0 then
        throw s!"{g.name src} has no story counter"
      let srcName := g.name src
      g := g.record (GameEvent.counters g.turnNumber (some p) (g.snapshot src) .story 1 true
        (cause := .costPayment .removeCounters p forObject))
      g := g.logMsg s!"{(g.player p).name} removes a story counter from {srcName}"
    if a.cost.removeIndestructibleCounter then
      g := (← g.payRemoveIndestructibleCounter (g.object! sourceId) forObject)
    if a.cost.putStunCounterOnSource then
      let src := g.object! sourceId
      let srcName := g.name src
      let n := g.countersYouPut src 1 (putter := some p)
      let g' :=
        if n > 0 then
          g.record (GameEvent.counters g.turnNumber (some p) (g.snapshot src) .stun n
            (cause := .costPayment .putCounters p forObject))
        else g
      g := g'.logMsg s!"{(g.player p).name} puts a stun counter on {srcName}"
    if a.cost.removeAnyNumberPlusOne then
      let src := g.object! sourceId
      let srcName := g.name src
      if src.status.plusOnePlusOne < removePlusOnes then
        throw s!"{srcName} doesn't have {removePlusOnes} +1/+1 counters"
      let g' :=
        if removePlusOnes > 0 then
          g.record (GameEvent.counters g.turnNumber (some p) (g.snapshot src) .plusOnePlusOne removePlusOnes true
            (cause := .costPayment .removeCounters p forObject))
        else g
      g := g'.logMsg
        s!"{(g.player p).name} removes {removePlusOnes} +1/+1 counters from {srcName}"
  | none => pure ()
  if sacrificeSource then
    match g.findObject? sourceId with
    | none => pure ()
    | some src =>
      g := g.sacrificeToGraveyard src
        s!"{(g.player p).name} sacrifices {g.name src}"
        (cause := some (.costPayment .sacrifice p forObject))
  if ab.any (·.cost.fra == .exileSource) then
    match g.findObject? sourceId with
    | some src =>
      if src.isOnBattlefield then
        let srcName := g.name src
        g := (g.move sourceId .exile none
          (cause := some (.costPayment .exile p forObject))).1.logMsg
          s!"{(g.player p).name} exiles {srcName}"
    | none => pure ()
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
