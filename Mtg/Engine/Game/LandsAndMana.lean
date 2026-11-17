import Mtg.Engine.Game.ManaAbilities

/-!
# Playing lands and mana abilities (CR 305 / 605)

Land drops, mana sources and their producible types, tapping for mana
with spending restrictions (CR 106.6), and available-mana calculation.
-/

namespace Mtg.Engine
namespace Game

/-- Record that `p` has used a land play this turn, without putting a land
onto the battlefield. Tests use this when the drop itself is not the action. -/
def recordLandPlayed (g : Game) (p : PlayerId) : Game :=
  let snap : EventObject := { id := some ⟨Nat.pow 2 60⟩, controller := some p, owner := p, zone := .outside p }
  g.record (GameEvent.moved g.turnNumber snap (.outside p) (.outside p)
    (after := some snap) (verb := some .playLand) (actor := some p)
    (cause := .specialAction .playLand p))

/-- Put `id` onto the battlefield as `p`'s land play and run its enters
processing (CR 305.1). -/
def finishPlayLand (g : Game) (p : PlayerId) (id : ObjectId) (tapped : Bool := false) : Game :=
  match g.findObject? id with
  | none => g
  | some card =>
    let (g, newId) := g.putOntoBattlefield id p
      (tapped := tapped)
      (verb := some .playLand) (actor := some p)
      (cause := some (.specialAction .playLand p))
    let g := g.logMsg s!"{(g.player p).name} plays {g.name card}"
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.afterLastPermanentEnters (some id) (isPlayLand := true))
    else
      match g.findObject? newId with
      | some entered =>
        if !entered.isOnBattlefield then g
        else
          let g := if entered.status.tapped then g.logMsg s!"{g.name entered} enters tapped" else g
          g.afterLandEnters entered
      | none => g

def playLand (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.canPlayLand p then
    throw "Can't play a land now (CR 116.2a / 305.3)"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if !g.isLand card then
    throw s!"{g.name card} is not a land"
  let g := g.finishPlayLand p id
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.receivePriority p)
  if g.pending != .none then
    return g
  return g.receivePriority p

def manaSources (g : Game) (p : PlayerId) : Array (GameObject × Array ManaType) :=
  g.permanentsOf p |>.filterMap (fun o =>
    let types := g.manaAbilitiesOf o
    if types.isEmpty || o.status.tapped then none
    else if g.hasSummoningSickness o &&
        !(g.isCreature o && g.activatesAsThoughHaste p) then none
    else some (o, types))

/-- Permanents `p` currently controls with this subtype. -/
def countSubtype (g : Game) (p : PlayerId) (subtype : CardSubtype) : Nat :=
  (g.permanentsOf p).filter (fun o => g.hasSubtype o subtype) |>.size

/-- Greatest mana value among permanents `p` controls matching `pred`. -/
def greatestManaValueAmong (g : Game) (p : PlayerId) (pred : GameObject → Bool) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if pred o then max acc (g.objectManaValue o) else acc) 0

/-- Mana in `p`'s pool plus mana from each of their untapped sources, skipping
any source in `excludeIds` (used when `{T}` or tap-cost picks reserve those
permanents). Each source is counted as its first mana type (green for any color),
with its spending restriction (leaving `.mountainExtraRed` extra `{R}`
unrestricted). -/
def availableManaExceptIds (g : Game) (p : PlayerId) (excludeIds : Array ObjectId) : ManaPool :=
  (g.manaSources p).foldl
    (fun pool (src, types) =>
      if excludeIds.contains src.id then pool
      else
        let green := ManaType.colored .green
        match (if types.size ≥ 5 && types.contains green then some green else types[0]?) with
        | some t => g.addTapManaToPool pool src t
        | none => pool)
    (g.player p).manaPool

/-- Mana in `p`'s pool plus mana from each of their untapped sources, skipping
`exclude` (used when that source's `{T}` is part of an activation cost).
Each source is counted as its first mana type (green for any color), with
its spending restriction. -/
def availableManaExcept (g : Game) (p : PlayerId) (exclude : Option ObjectId) : ManaPool :=
  g.availableManaExceptIds p exclude.toArray

/-- Mana in `p`'s pool plus mana from each of their untapped sources. -/
def availableMana (g : Game) (p : PlayerId) : ManaPool :=
  g.availableManaExceptIds p #[]

/-- Whether `p` currently controls a usable non-plain CR 605 mana ability
(`!isPlainTapManaAbilityDef`, such as Treasures, life/mana filter lands, or
counter-removal mana abilities). When `prop? = some prop`, also requires that
the source is not reserved for `prop`'s non-mana costs and that the ability can
produce mana covering `prop.cost` (or another usable mana ability's mana cost). -/
def hasUsableNonPlainManaAbility (g : Game) (p : PlayerId)
    (prop? : Option ProposedSpell := none) : Bool :=
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let perms := g.permanentsOf p
  let usableAbilityOn (o : GameObject) (d : ManaAbilityDef) (requireNonPlain : Bool) : Bool :=
    (!requireNonPlain || !g.isPlainTapManaAbilityDef p o d) &&
      g.manaAbilityDefUsable p o d &&
      !(d.output.allChoices (fun ts => if ts.size > 1 then #[ts[0]!] else ts)).isEmpty &&
      (!d.tap ||
        (!o.status.tapped &&
          !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)))) &&
      (let effCost := g.manaAbilityEffectiveCost p o d
       !effCost.includesManaPayment ||
         (g.availableManaExcept p (if d.tap then some o.id else none)).canPay effCost
           (allowElfRestricted := g.hasSubtype o .elf)
           (allowInstRestricted := false)
           (allowHeroRestricted := g.hasSubtype o .hero)
           (allowVillainRestricted := g.hasSubtype o .villain)
           (allowCantNonartifact := true)
           (allowCreatureRestricted := g.isCreature o)
           (spend := { abilitySourceSubtypes := g.subtypes o })) &&
      (match prop? with
       | none => true
       | some prop =>
         prop.cost.includesManaPayment &&
         (!d.tap ||
           !((prop.tapSource && prop.sourceId == some o.id &&
               !g.sourceTappedForCost o.id (some prop.spellId) sinceIdx) ||
             prop.teamworkCreatures.contains o.id)) &&
         (!(d.sacrificeSelf || d.exileSelf) ||
           !((prop.sourceId == some o.id && g.proposedNeedsBattlefieldSource prop sinceIdx) ||
             prop.teamworkCreatures.contains o.id ||
             (prop.sneakAttacker == some o.id && !g.sneakPaid prop.spellId))) &&
         (!d.removeStoryCounter ||
           !(prop.sourceId == some o.id && prop.activation.any (·.cost.removeStoryCounter) &&
             !g.sourceCounterCostPaidFor o.id (some prop.spellId) .removeCounters (some .story) sinceIdx &&
             o.status.story ≤ 1)) &&
         (!d.removeIndestructibleCounter ||
           !(prop.sourceId == some o.id && prop.activation.any (·.cost.removeIndestructibleCounter) &&
             !g.sourceCounterCostPaidFor o.id (some prop.spellId) .removeCounters (some .indestructible) sinceIdx &&
             o.status.indestructibleCounters ≤ 1)))
  match prop? with
  | none =>
    perms.any (fun o => (g.manaAbilityDefs o).any (fun d => usableAbilityOn o d true))
  | some prop =>
    if !prop.cost.includesManaPayment then false
    else
      let allowElf := g.proposedAllowsElfRestricted prop
      let allowInst := g.proposedAllowsInstRestricted prop
      let allowHero := g.proposedAllowsHeroRestricted prop
      let allowVillain := g.proposedAllowsVillainRestricted prop
      let allowCantNonart := g.proposedAllowsCantNonartifact prop
      let allowCreat := g.proposedAllowsCreatureRestricted prop
      let spend := g.proposedManaSpend prop
      let otherManaCosts : Array (GameObject × ManaCost) :=
        perms.foldl (fun acc o2 =>
          (g.manaAbilityDefs o2).foldl (fun acc d2 =>
            let eff2 := g.manaAbilityEffectiveCost p o2 d2
            if eff2.includesManaPayment && g.manaAbilityDefUsable p o2 d2 &&
                (!d2.tap ||
                  (!o2.status.tapped &&
                    !(g.hasSummoningSickness o2 && !(g.isCreature o2 && g.activatesAsThoughHaste p)))) then
              acc.push (o2, eff2)
            else acc) acc) #[]
      perms.any fun o =>
        (g.manaAbilityDefs o).any fun d =>
          usableAbilityOn o d true &&
            let dedupForProp (ts : Array ManaType) : Array ManaType :=
              if ts.size ≤ 1 then ts
              else Id.run do
                let mut acc : Array ManaType := #[]
                let mut seenZero := false
                for t in ts do
                  match t with
                  | .colored c =>
                    let req :=
                      prop.cost.symbolsIncludingColor c > 0 ||
                        otherManaCosts.any (fun (o2, c2) => o2.id != o.id && c2.symbolsIncludingColor c > 0)
                    if !req then
                      if !seenZero then
                        seenZero := true
                        acc := acc.push t
                    else
                      acc := acc.push t
                  | .colorless => acc := acc.push t
                return acc
            let extra := if d.tap then g.extraMountainRedFromTap o #[.colorless] else #[]
            (d.output.allChoices dedupForProp).any fun added =>
              let simPool :=
                addRestrictedMana (addRestrictedMana ManaPool.empty added d.restriction) extra .none
              simPool.coveredMana prop.cost allowElf allowInst allowHero allowVillain
                  allowCantNonart allowCreat spend > 0 ||
                otherManaCosts.any (fun (o2, eff2) =>
                  o2.id != o.id &&
                    simPool.coveredMana eff2 (g.hasSubtype o2 .elf) false
                      (g.hasSubtype o2 .hero) (g.hasSubtype o2 .villain) true
                      (g.isCreature o2) { abilitySourceSubtypes := g.subtypes o2 } > 0)

end Game
end Mtg.Engine

