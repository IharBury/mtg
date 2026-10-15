import Mtg.Engine.Fixture

/-!
# `TriggerResolution.removeCounters`

A hope counter from the source, and every counter from the enchanted
creature. What is removed, and who loses it, are arguments.
-/

namespace Mtg.Engine.RemoveCountersTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId
    (resolutionOverride := some r)

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def anyObj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.setObject { a with attachedTo := some (pid g host) }

def withHope (g : Game) (name : String) (n : Nat) : Game :=
  let o := obj g name
  g.setObject { o with status := { o.status with hope := n } }

def load (g : Game) (name : String) : Game :=
  let o := obj g name
  g.setObject { o with status := { o.status with
    plusOnePlusOne := 2
    hope := 1
    charge := 2
    stun := 1
    shield := 1
    lore := 3
    keywordCounters := { flying := 1 }
    damage := 4
    pump := (1, 2) } }

def dawn : CardDef := { name := "Dawn", types := #[.enchantment] }
def grasp : CardDef := { name := "Grasp", types := #[.enchantment] }
def bear : CardDef := {
  name := "Bear"
  types := #[.creature]
  power := some 2
  toughness := some 2
}
def foe : CardDef := {
  name := "Foe"
  types := #[.creature]
  power := some 3
  toughness := some 3
}

def hopeFromSource : TriggeredAbility.TriggerResolution :=
  .removeCounters .hope .source

def allFromEnchanted : TriggeredAbility.TriggerResolution :=
  .removeCounters .all .enchanted

def handSize (g : Game) : Nat :=
  (g.player caster).hand.size

def stillLoaded (s : Status) : Bool :=
  s.plusOnePlusOne == 2 && s.hope == 1 && s.charge == 2 && s.stun == 1 &&
    s.shield == 1 && s.lore == 3 && s.keywordCounters.flying == 1 &&
    s.damage == 4 && s.pump == (1, 2)

def stripped (s : Status) : Bool :=
  !Status.hasCounters s && s.damage == 4 && s.pump == (1, 2) &&
    s.plusOnePlusOne == 0 && s.hope == 0 && s.keywordCounters.flying == 0

/- One hope counter leaves the source, and a later step can see that.
None to remove changes nothing except clearing that note. A missing
source, and a source that has left, remove nothing. -/
#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 3
  let g := step g0 hopeFromSource (some (pid g0 "Dawn"))
  (obj g "Dawn").status.hope == 2 && g.removedHopeThisWay &&
    logContains g "Dawn loses a hope counter"

#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 1
  let before := handSize g0
  let g := step g0 (.sequence [hopeFromSource, .«if» .removedHope (.draw (.fixed 1))])
    (some (pid g0 "Dawn"))
  (obj g "Dawn").status.hope == 0 && !g.removedHopeThisWay &&
    handSize g == before + 1

#guard
  let base := addPermanent afterDraw dawn caster caster
  let g0 := { base with removedHopeThisWay := true }
  let g := step g0 hopeFromSource (some (pid g0 "Dawn"))
  (obj g "Dawn").status.hope == 0 && !g.removedHopeThisWay &&
    g.log == g0.log

#guard
  let g0 := addPermanent afterDraw dawn caster caster
  let before := handSize g0
  let g := step g0 (.sequence [hopeFromSource, .«if» .removedHope (.draw (.fixed 1))])
    (some (pid g0 "Dawn"))
  handSize g == before && !g.removedHopeThisWay &&
    !(logContains g "loses a hope counter")

#guard
  let g0 := { afterDraw with removedHopeThisWay := true }
  let g := step g0 hopeFromSource
  !g.removedHopeThisWay && logContains g "no longer in play"

#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 3
  let (g1, newId) := g0.move (pid g0 "Dawn") (.graveyard caster) none
  let g1 := g1.mapObjectStatus (anyObj g1 "Dawn") (fun s => { s with hope := 3 })
  let g := step g1 hopeFromSource (some newId)
  (anyObj g "Dawn").status.hope == 3 && !g.removedHopeThisWay &&
    logContains g "no longer on the battlefield"

/- Every counter leaves the enchanted creature, including an opponent's.
Damage and a pump stay. Nothing enchanted, a missing host, and a missing
source remove nothing. A host that has left still loses its counters.
Removing them does not count as removing a hope counter. -/
#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear") "Bear"
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stripped (obj g "Bear").status && !(obj g "Bear").status.tapped &&
    logContains g "counters are removed from Bear"

#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw foe opp opp) grasp caster caster)
    "Grasp" "Foe") "Foe"
  let g0 := withHope g0 "Grasp" 2
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stripped (obj g "Foe").status && (obj g "Grasp").status.hope == 2 &&
    logContains g "counters are removed from Foe"

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let before := handSize g0
  let g := step g0
    (.sequence [allFromEnchanted, .«if» .removedHope (.draw (.fixed 1))])
    (some (pid g0 "Grasp"))
  handSize g == before && !g.removedHopeThisWay &&
    logContains g "counters are removed from Bear"

#guard
  let g0 := load
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Bear"
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stillLoaded (obj g "Bear").status && g.log == g0.log

#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear") "Bear"
  let aura := obj g0 "Grasp"
  let g0 := g0.setObject { aura with attachedTo := some ⟨99999⟩ }
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stillLoaded (obj g "Bear").status && g.log == g0.log

#guard
  let g0 := load (addPermanent afterDraw bear caster caster) "Bear"
  let g := step g0 allFromEnchanted
  stillLoaded (obj g "Bear").status && g.log == g0.log

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster
  let (g1, bearId) := g0.move (pid g0 "Bear") (.graveyard caster) none
  let g1 := g1.mapObjectStatus (anyObj g1 "Bear") (fun s =>
    { s with plusOnePlusOne := 2, hope := 1, damage := 4, pump := (1, 2) })
  let aura := obj g1 "Grasp"
  let g1 := g1.setObject { aura with attachedTo := some bearId }
  let g := step g1 allFromEnchanted (some (pid g1 "Grasp"))
  let host := anyObj g "Bear"
  !Status.hasCounters host.status && host.status.damage == 4 && host.status.pump == (1, 2) &&
    logContains g "counters are removed from Bear"

/- The other combinations remove nothing, and they leave an earlier note. -/
#guard
  let g0 := load (attach
    (withHope (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
      "Grasp" 2)
    "Grasp" "Bear") "Bear"
  let g0 := { g0 with removedHopeThisWay := true }
  let crossed := step g0 (.removeCounters .hope .enchanted) (some (pid g0 "Grasp"))
  let swapped := step g0 (.removeCounters .all .source) (some (pid g0 "Grasp"))
  crossed.removedHopeThisWay && stillLoaded (obj crossed "Bear").status &&
    (obj crossed "Grasp").status.hope == 2 && crossed.log == g0.log &&
    swapped.removedHopeThisWay && stillLoaded (obj swapped "Bear").status &&
    (obj swapped "Grasp").status.hope == 2 && swapped.log == g0.log

/- Tap, then remove, including when nothing is enchanted. -/
#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear") "Bear"
  let g := g0.applyTriggeredAbility caster .onEnterTapEnchantedRemoveCounters
    (some (pid g0 "Grasp"))
  (obj g "Bear").status.tapped && stripped (obj g "Bear").status

#guard
  let g0 := load
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Bear"
  let g := g0.applyTriggeredAbility caster .onEnterTapEnchantedRemoveCounters
    (some (pid g0 "Grasp"))
  !(obj g "Bear").status.tapped && stillLoaded (obj g "Bear").status &&
    logContains g "Nothing is enchanted"

#guard TriggeredAbility.resolution .onYourEndStepRemoveHopeDrawSac ==
  .sequence [hopeFromSource, .«if» .removedHope (.draw (.fixed 1)),
    .«if» .noHopeOnSource (.sequence [.sacrifice .you .source, .gainLife 4])]
#guard TriggeredAbility.resolution .onEnterTapEnchantedRemoveCounters ==
  .sequence [.tap .enchanted, allFromEnchanted]

#guard TriggeredAbility.resolutionPhrase { resolution := hopeFromSource } ==
  "remove a hope counter from this"
#guard TriggeredAbility.resolutionPhrase { resolution := allFromEnchanted } ==
  "remove all counters from enchanted creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .removeCounters .hope .enchanted } == "remove counters"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .removeCounters .all .source } == "remove counters"
#guard TriggeredAbility.resolutionPhrase
    (SharedTrigger.timing .removeHopeDrawSac) ==
  "remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life"
#guard TriggeredAbility.resolutionPhrase
    (SharedTrigger.timing .tapEnchantedRemoveCounters) ==
  "tap enchanted creature and remove all counters from it"

#guard TriggeredAbility.toNotation .onYourEndStepRemoveHopeDrawSac ==
  "At the beginning of your end step, remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life."
#guard TriggeredAbility.toNotation .onEnterTapEnchantedRemoveCounters ==
  "When this Aura enters, tap enchanted creature and remove all counters from it."

#guard (SharedTrigger.timing .removeHopeDrawSac).resolution ==
  .sequence [hopeFromSource, .«if» .removedHope (.draw (.fixed 1)),
    .«if» .noHopeOnSource (.sequence [.sacrifice .you .source, .gainLife 4])]
#guard (SharedTrigger.timing .tapEnchantedRemoveCounters).resolution ==
  .sequence [.tap .enchanted, allFromEnchanted]

end Mtg.Engine.RemoveCountersTests
