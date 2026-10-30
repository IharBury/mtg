import Mtg.Engine.Fixture

/-!
# `TriggerResolution.removeCounters`

A hope counter from the source, and every counter from the enchanted
creature. What is removed is `TriggerRemoveWhat`. Who loses it is an
`ObjectSelector`. Any other permanent the selector names loses that
counter. A card or an unmade choice loses nothing.
-/

namespace Mtg.Engine.RemoveCountersTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

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
  g.record (GameEvent.attached g.turnNumber a.id (pid g host) (cause := .gameRule .staticAbility))

def withHope (g : Game) (name : String) (n : Nat) : Game :=
  let o := obj g name
  g.recordPutCounters o.id .hope n

def load (g : Game) (name : String) : Game :=
  let o := obj g name
  let g :=
    #[(.plusOnePlusOne, 2), (.hope, 1), (.charge, 2), (.stun, 1),
      (.shield, 1), (.lore, 3), (.flying, 1)].foldl
      (fun acc (k, n) => acc.recordPutCounters o.id k n) g
  (setMarkedDamage g o.id 4).createEffect (.pump o.id 1 2)

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

def stillLoaded (g : Game) (o : GameObject) : Bool :=
  let s := o.status
  s.plusOnePlusOne == 2 && s.hope == 1 && s.charge == 2 && s.stun == 1 &&
    s.shield == 1 && s.lore == 3 && s.keywordCounters.flying == 1 &&
    s.damage == 4 && g.pumpOf o == (1, 2)

def stripped (g : Game) (o : GameObject) : Bool :=
  let s := o.status
  !Status.hasCounters s && s.damage == 4 && g.pumpOf o == (1, 2) &&
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
  let g0 := base.change (.removedHopeThisWay true)
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
  let g0 := afterDraw.change (.removedHopeThisWay true)
  let g := step g0 hopeFromSource
  !g.removedHopeThisWay && logContains g "no longer in play"

#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 3
  let (g1, newId) := g0.move (pid g0 "Dawn") (.graveyard caster) none
  let g1 := g1.recordPutCounters (anyObj g1 "Dawn").id .hope 3
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
  stripped g (obj g "Bear") && !(obj g "Bear").status.tapped &&
    logContains g "counters are removed from Bear"

#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw foe opp opp) grasp caster caster)
    "Grasp" "Foe") "Foe"
  let g0 := withHope g0 "Grasp" 2
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stripped g (obj g "Foe") && (obj g "Grasp").status.hope == 2 &&
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
  stillLoaded g (obj g "Bear") && g.log == g0.log

#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear") "Bear"
  let aura := obj g0 "Grasp"
  let g0 := g0.record (GameEvent.attached g0.turnNumber aura.id ⟨99999⟩ (cause := .gameRule .staticAbility))
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stillLoaded g (obj g "Bear") && g.log == g0.log

#guard
  let g0 := load (addPermanent afterDraw bear caster caster) "Bear"
  let g := step g0 allFromEnchanted
  stillLoaded g (obj g "Bear") && g.log == g0.log

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster
  let (g1, bearId) := g0.move (pid g0 "Bear") (.graveyard caster) none
  let g1 := (setMarkedDamage ((g1.recordPutCounters bearId .plusOnePlusOne 2).recordPutCounters bearId .hope 1) bearId 4).createEffect (.pump bearId 1 2)
  let aura := obj g1 "Grasp"
  let g1 := g1.record (GameEvent.attached g1.turnNumber aura.id bearId (cause := .gameRule .staticAbility))
  let g := step g1 allFromEnchanted (some (pid g1 "Grasp"))
  let host := anyObj g "Bear"
  !Status.hasCounters host.status && host.status.damage == 4 && g.pumpOf host == (1, 2) &&
    logContains g "counters are removed from Bear"

/- Hope from the enchanted creature is removed, and the note records that.
Every counter on the source is removed. Hope from a permanent that was
not announced clears the note and removes nothing. -/
#guard
  let g0 := load (attach
    (withHope (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
      "Grasp" 2)
    "Grasp" "Bear") "Bear"
  let g0 := g0.change (.removedHopeThisWay false)
  let crossed := step g0 (.removeCounters .hope .enchanted) (some (pid g0 "Grasp"))
  crossed.removedHopeThisWay && (obj crossed "Bear").status.hope == 0 &&
    (obj crossed "Bear").status.plusOnePlusOne == 2 &&
    (obj crossed "Grasp").status.hope == 2 &&
    logContains crossed "Bear loses a hope counter"

#guard
  let g0 := load (attach
    (withHope (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
      "Grasp" 2)
    "Grasp" "Bear") "Bear"
  let g0 := g0.change (.removedHopeThisWay true)
  let swapped := step g0 (.removeCounters .all .source) (some (pid g0 "Grasp"))
  swapped.removedHopeThisWay && stillLoaded swapped (obj swapped "Bear") &&
    (obj swapped "Grasp").status.hope == 0 &&
    (obj swapped "Grasp").status.plusOnePlusOne == 0 &&
    logContains swapped "counters are removed from Grasp"

#guard
  let g0 := load (attach
    (withHope (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
      "Grasp" 2)
    "Grasp" "Bear") "Bear"
  let g0 := g0.change (.removedHopeThisWay true)
  let other := step g0 (.removeCounters .hope .target) (some (pid g0 "Grasp"))
  !other.removedHopeThisWay && stillLoaded other (obj other "Bear") &&
    (obj other "Grasp").status.hope == 2 && other.log == g0.log

/- Tap, then remove, including when nothing is enchanted. -/
#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear") "Bear"
  let g := g0.applyTriggeredAbility caster .onEnterTapEnchantedRemoveCounters
    (some (pid g0 "Grasp"))
  (obj g "Bear").status.tapped && stripped g (obj g "Bear")

#guard
  let g0 := load
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Bear"
  let g := g0.applyTriggeredAbility caster .onEnterTapEnchantedRemoveCounters
    (some (pid g0 "Grasp"))
  !(obj g "Bear").status.tapped && stillLoaded g (obj g "Bear") &&
    logContains g "Nothing is enchanted"

#guard TriggeredAbility.resolution .onYourEndStepRemoveHopeDrawSac ==
  .sequence [hopeFromSource, .«if» .removedHope (.draw (.fixed 1)),
    .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]
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
    { resolution := .removeCounters .hope .target } == "remove counters"
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
    .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]
#guard (SharedTrigger.timing .tapEnchantedRemoveCounters).resolution ==
  .sequence [.tap .enchanted, allFromEnchanted]

end Mtg.Engine.RemoveCountersTests
