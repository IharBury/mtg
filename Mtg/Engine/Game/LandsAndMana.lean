import Mtg.Engine.Game.ManaAbilities

/-!
# Playing lands and mana abilities (CR 305 / 605)

Land drops, mana sources and their producible types, tapping for mana
with spending restrictions (CR 106.10), and available-mana calculation.
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
    let g := g.logMsg s!"{(g.player p).name} plays {card.name}"
    let g := if tapped then g.logMsg s!"{card.name} enters tapped" else g
    g.afterLandEnters (g.object! newId)

def playLand (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.canPlayLand p then
    throw "Can't play a land now (CR 116.2a / 305.3)"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if !card.printed.isLand then
    throw s!"{card.name} is not a land"
  -- The Black Gate: “As it enters, you may pay N life. If you don't, it
  -- enters tapped.” Choose tapped before moving so the arrival event is
  -- recorded with the final tap status (CR 614.1c).
  match card.printed.entersTappedUnlessPayLife with
  | some n =>
    if !card.printed.entersTapped then
      return (g.change (.pending (.fraChoice p (.payLifeOrEnterTapped id n)))).logMsg
        s!"{(g.player p).name} may pay {n} life, or {card.name} enters tapped"
  | none => pure ()
  let g := g.finishPlayLand p id
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
