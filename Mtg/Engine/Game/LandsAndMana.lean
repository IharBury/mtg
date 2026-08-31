import Mtg.Engine.Game.Entering

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
    else if o.hasSummoningSickness then none
    else some (o, types))

/-- Permanents `p` currently controls with this subtype. -/
def countSubtype (g : Game) (p : PlayerId) (subtype : String) : Nat :=
  (g.permanentsOf p).filter (fun o => g.hasSubtype o subtype) |>.size

/-- Greatest mana value among permanents `p` controls matching `pred`. -/
def greatestManaValueAmong (g : Game) (p : PlayerId) (pred : GameObject → Bool) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if pred o then max acc o.printed.manaValue else acc) 0

/-- Colors among legendary creatures and planeswalkers `p` controls (Mox Amber).
Colorless is not a color; a colorless legend contributes nothing. -/
def legendaryManaColors (g : Game) (p : PlayerId) : ColorSet :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.isLegendary && (o.isCreature || o.printed.isPlaneswalker) then
      ColorSet.union acc o.printed.colors
    else acc) ColorSet.empty

/-- Mana added by tapping `o` for `mana` (CR 106.4 / 605.3b). A
`tapAddManaForEach` ability counts permanents the controller currently
controls with the listed subtype. `tapAddAnyColorEqualToPower` adds this
creature's current power (CR 208.2). Mox Amber and Arcane Signet may
produce 0 when no matching color is available. -/
def manaFromTap (g : Game) (o : GameObject) (mana : ManaType) : Nat :=
  if o.printed.tapAddAnyColorEqualToPower then
    match mana with
    | .colored _ => (g.power o).toNat
    | .colorless => 0
  else if o.printed.tapAddAnyColorAmongLegendaries then
    match mana, o.controller with
    | .colored c, some p => if (g.legendaryManaColors p).contains c then 1 else 0
    | _, _ => 0
  else if o.printed.tapAddCommanderIdentity then
    match mana, o.controller with
    | .colored c, some p =>
      let pl := g.player p
      if pl.hasCommander && pl.commanderColorIdentity.contains c then 1 else 0
    | _, _ => 0
  else
    match o.printed.tapAddManaForEach.find? (fun a => a.mana == mana) with
    | some a =>
      match o.controller with
      | some p => g.countSubtype p a.subtype
      | none => 0
    | none => 1

/-- A player may activate mana abilities with priority, or while paying a
spell they are casting (CR 605.3a / 601.2g). -/
def canActivateManaAbility (g : Game) (p : PlayerId) : Bool :=
  if g.over then false
  else if g.hasPriority p then true
  else
    match g.pending with
    | .activateManaAbilities caster => caster == p
    | .mayPayGeneric q _ => q == p
    | .payOrLetCounter q _ _ => q == p
    | .payWard q _ cost =>
      q == p &&
        (match cost with
         | .genericMana _ | .discardOrPay _ => true
         | _ => false)
    | _ => false

def tapForMana (g : Game) (p : PlayerId) (id : ObjectId) (mana : ManaType) : Except String Game := do
  if !g.canActivateManaAbility p then
    throw "You can't activate a mana ability now (CR 605.3a)"
  let o := g.object! id
  if !o.controlledBy p || !o.isOnBattlefield then
    throw "You don't control that permanent"
  if o.status.tapped then
    throw s!"{o.name} is already tapped"
  if (match g.proposedSpell with
      | some prop => prop.tapSource && prop.sourceId == some id
      | none => false) then
    throw s!"{o.name} is needed to pay \{T}"
  if o.hasSummoningSickness then
    throw s!"{o.name} has summoning sickness (CR 302.6)"
  if o.printed.enteredOrBasicAddMana.contains mana &&
      o.printed.requiresEnteredOrBasicAdd &&
      !g.canUseEnteredOrBasicAdd o then
    throw s!"{o.name}'s colored mana ability can be activated only if this land entered this turn or if you control a basic land"
  if !(g.manaAbilitiesOf o).contains mana then
    throw s!"{o.name} cannot produce {mana}"
  let amount := g.manaFromTap o mana
  let elfRestricted := o.printed.tapAddAnyColorEqualToPower
  let instRestricted := o.printed.tapAddAnyColorForInstantOrSorcery
  let cantNonartifact := o.printed.hasSubtype "Vibranium" && mana == .colorless
  let g := g.setObject { o with status := { o.status with tapped := true } }
  let g :=
    if o.printed.tapSacrificeAddAnyColor then
      let o := g.object! o.id
      g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {o.name}"
    else g
  let pool :=
    ManaPool.add (g.player p).manaPool mana amount
      (elfRestricted := elfRestricted)
      (instRestricted := instRestricted)
      (cantNonartifact := cantNonartifact)
  let g := g.modifyPlayer p (fun pl => { pl with manaPool := pool })
  let produced :=
    if amount == 0 then "no mana"
    else if amount == 1 then toString mana
    else s!"{mana} ×{amount}"
  let restrictNote :=
    if elfRestricted then " (Elf spells and abilities)"
    else if instRestricted then " (instant or sorcery spells)"
    else if cantNonartifact then " (not a nonartifact spell)"
    else ""
  let g :=
    if amount == 0 then
      g.logMsg s!"{g.player p |>.name} taps {o.name} but adds no mana"
    else
      g.logMsg s!"{g.player p |>.name} taps {o.name} for {produced}{restrictNote}"
  let g :=
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some { prop with tapped := prop.tapped.push id } }
    | none => g
  -- Mana abilities don't use the stack (CR 605.3b), but they still activate
  -- and can cause Elrond-style triggers.
  let g :=
    if o.isCreature then
      g.putControlledTriggers p .youActivateCreatureAbility
    else g
  return { g with consecutivePasses := 0 }

/-- Mana in `p`'s pool plus mana from each of their untapped sources, skipping
`exclude` (used when that source's `{T}` is part of an activation cost).
Any-color power mana is counted as green Elf-restricted mana for the heuristic. -/
def availableManaExcept (g : Game) (p : PlayerId) (exclude : Option ObjectId) : ManaPool :=
  (g.manaSources p).foldl
    (fun pool (src, types) =>
      if exclude == some src.id then pool
      else if src.printed.tapAddAnyColorEqualToPower then
        let n := g.manaFromTap src (.colored .green)
        pool.add (.colored .green) n (elfRestricted := true)
      else if src.printed.tapAddAnyColorForInstantOrSorcery then
        pool.add (.colored .blue) 1 (instRestricted := true)
      else
        match types[0]? with
        | some t => pool.add t (g.manaFromTap src t)
        | none => pool)
    (g.player p).manaPool

/-- Mana in `p`'s pool plus mana from each of their untapped sources. Any-color
power mana is counted as green Elf-restricted mana for the heuristic. -/
def availableMana (g : Game) (p : PlayerId) : ManaPool :=
  g.availableManaExcept p none

end Game
end Mtg.Engine
