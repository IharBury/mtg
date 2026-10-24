import Mtg.Engine.Game.Keywords

/-!
# Current power and toughness (CR 613.4)

Final power and toughness after characteristic-defining abilities,
layer-7b base setting, lord and attachment bonuses, counters, and pumps,
plus greatest-power queries and blocker lookups.
-/

namespace Mtg.Engine
namespace Game

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def basePower (g : Game) (o : GameObject) : Int :=
  g.characteristicBasePower o

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def baseToughness (g : Game) (o : GameObject) : Int :=
  g.characteristicBaseToughness o

/-- Current power, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def power (g : Game) (o : GameObject) : Int :=
  g.snapshotPower o

/-- Current toughness, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def toughness (g : Game) (o : GameObject) : Int :=
  g.snapshotToughness o

/-- Greatest power among creatures `p` controls; `0` if they control none. -/
def greatestPowerAmongCreatures (g : Game) (p : PlayerId) : Int :=
  let creatures := g.creaturesControlledBy p
  if creatures.isEmpty then 0
  else creatures.foldl (fun acc o => max acc (g.power o)) (g.power creatures[0]!)

/-- Greatest power among attacking creatures `p` controls; `0` if none. -/
def greatestPowerAmongAttacking (g : Game) (p : PlayerId) : Int :=
  let attackers :=
    (g.permanentsOf p).filter (fun o => o.isCreature && o.status.attacking)
  if attackers.isEmpty then 0
  else attackers.foldl (fun acc o => max acc (g.power o)) (g.power attackers[0]!)

/-- Creatures currently blocking `attackerId`. -/
def blockersOf (g : Game) (attackerId : ObjectId) : Array GameObject :=
  g.battlefield.filter (fun b => b.status.blocking.contains attackerId)

/-- Attacking creatures `blocker` is still blocking (CR 510.1d). -/
def creaturesBlockedBy (g : Game) (blocker : GameObject) : Array GameObject :=
  blocker.status.blocking.filterMap (fun id =>
    match g.findObject? id with
    | some a =>
      if a.isOnBattlefield && a.status.attacking then some a else none
    | none => none)

/-- Snapshot `o` as an `EventObject` (CR 113.7a).
Note: `colors`, `manaValue`, `types`, `subtypes`, `power`, `toughness`,
`keywords`, and `staticAbilities` are provisional until the Layer 1–7 pipeline
in Phase 4 (CR 613.1). -/
def snapshot (g : Game) (o : GameObject) : EventObject :=
  let base := o.asEvent
  let extraSubtypes : Array CardSubtype :=
    #[.hero, .villain, .goblin, .orc, .army, .elf, .merfolk].foldl
      (fun acc s => if g.hasSubtype o s && !acc.contains s then acc.push s else acc)
      base.subtypes
  let pw : Option Int :=
    if o.zone == .battlefield then
      if o.isCreature || o.printed.power.isSome then some (g.snapshotPower o) else none
    else
      o.lastKnownPower.orElse (fun _ =>
        if o.isCreature || o.printed.power.isSome then some (g.snapshotPower o) else none)
  let tg : Option Int :=
    if o.zone == .battlefield then
      if o.isCreature || o.printed.toughness.isSome then some (g.snapshotToughness o) else none
    else
      o.lastKnownToughness.orElse (fun _ =>
        if o.isCreature || o.printed.toughness.isSome then some (g.snapshotToughness o) else none)
  let curKw := g.currentKeywords o
  { base with
    subtypes := extraSubtypes
    power := pw
    toughness := tg
    keywords := { curKw with
      haste := g.hasHaste o
      vigilance := g.hasVigilance o
      flying := g.hasFlying o
      menace := g.hasMenace o
      hexproof := g.hasHexproof o
      indestructible := g.hasIndestructible o
      reach := curKw.reach
      trample := g.hasTrample o
      deathtouch := g.hasDeathtouch o
      defender := curKw.defender
      lifelink := g.hasLifelink o
      firstStrike := g.hasFirstStrike o
      doubleStrike := g.hasDoubleStrike o
      shadow := g.hasShadow o } }

end Game
end Mtg.Engine
