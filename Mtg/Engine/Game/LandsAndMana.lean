import Mtg.Engine.Game.ManaAbilities

/-!
# Playing lands and mana abilities (CR 305 / 605)

Land drops, mana sources and their producible types, tapping for mana
with spending restrictions (CR 106.10), and available-mana calculation.
-/

namespace Mtg.Engine
namespace Game

def playLand (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.canPlayLand p then
    throw "Can't play a land now (CR 116.2a / 305.3)"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if !card.printed.isLand then
    throw s!"{card.name} is not a land"
  let (g, newId) := g.putOntoBattlefield id p
    (tapped := g.entersTapped p card.printed) (summoningSick := false)
  let g := g.modifyPlayer p (fun pl => { pl with landsPlayedThisTurn := pl.landsPlayedThisTurn + 1 })
  let g := g.logMsg s!"{(g.player p).name} plays {card.name}"
  -- Lands have no summoning sickness. `entersTapped` overrides CR 110.5b.
  let g := g.afterLandEnters (g.object! newId)
  if g.pending != .none then
    return g
  return g.receivePriority p

def manaSources (g : Game) (p : PlayerId) : Array (GameObject × Array ManaType) :=
  g.permanentsOf p |>.filterMap (fun o =>
    let types := g.manaAbilitiesOf o
    if types.isEmpty || o.status.tapped then none
    else if o.hasSummoningSickness && !g.hasHaste o &&
        !(o.isCreature && g.activatesAsThoughHaste p) then none
    else some (o, types))

/-- Permanents `p` currently controls with this subtype. -/
def countSubtype (g : Game) (p : PlayerId) (subtype : String) : Nat :=
  (g.permanentsOf p).filter (fun o => g.hasSubtype o subtype) |>.size

/-- Greatest mana value among permanents `p` controls matching `pred`. -/
def greatestManaValueAmong (g : Game) (p : PlayerId) (pred : GameObject → Bool) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if pred o then max acc o.printed.manaValue else acc) 0

/-- Mana in `p`'s pool plus mana from each of their untapped sources, skipping
`exclude` (used when that source's `{T}` is part of an activation cost).
Each source is counted as its first mana type (green for any color), with
its spending restriction. -/
def availableManaExcept (g : Game) (p : PlayerId) (exclude : Option ObjectId) : ManaPool :=
  (g.manaSources p).foldl
    (fun pool (src, types) =>
      if exclude == some src.id then pool
      else
        let green := ManaType.colored .green
        match (if types.size ≥ 5 && types.contains green then some green else types[0]?) with
        | some t =>
          addRestrictedMana pool (Array.replicate (g.manaFromTap src t) t) (g.tapRestrictionOf src t)
        | none => pool)
    (g.player p).manaPool

/-- Mana in `p`'s pool plus mana from each of their untapped sources. -/
def availableMana (g : Game) (p : PlayerId) : ManaPool :=
  g.availableManaExcept p none

end Game
end Mtg.Engine
