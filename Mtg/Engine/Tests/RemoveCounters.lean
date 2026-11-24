import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture

/-!
# Unified counter removal instructions (`CounterOp.remove` / `CounterOp.removeAll`)

Removing a hope counter from the source (binding `stepSucceeded` for follow-up
draw/sacrifice) and removing all counters from the enchanted creature execute
through `Interpreter.execPermanent`.
-/

namespace Mtg.Engine.RemoveCountersTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters { body }) sourceId

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
  g.record (GameEvent.attached g.turnNumber (g.snapshot a) (pid g host) (cause := .gameRule .staticAbility))

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
  power := some (.fixed 2)
  toughness := some (.fixed 2)
}
def foe : CardDef := {
  name := "Foe"
  types := #[.creature]
  power := some (.fixed 3)
  toughness := some (.fixed 3)
}

def hopeFromSource : Instruction :=
  .permanent (.modifyCounters (.remove (some .hope) (.exact (.const 1))) .this)

def allFromEnchanted : Instruction :=
  .permanent (.modifyCounters (.remove none .anyNumber) .attachedHost)

def handSize (g : Game) : Nat :=
  (g.player caster).hand.size

def stillLoaded (g : Game) (o : GameObject) : Bool :=
  let s := o.status
  s.plusOnePlusOne == 2 && s.hope == 1 && s.charge == 2 && s.stun == 1 &&
    s.shield == 1 && s.lore == 3 && s.counters.count .flying == 1 &&
    s.damage == 4 && g.pumpOf o == (1, 2)

def stripped (g : Game) (o : GameObject) : Bool :=
  let s := o.status
  !Status.hasCounters s && s.damage == 4 && g.pumpOf o == (1, 2) &&
    s.plusOnePlusOne == 0 && s.hope == 0 && s.counters.count .flying == 0

/- One hope counter leaves the source; binding `stepSucceeded` draws a card only
when a counter was actually removed; removing the last hope counter triggers
sacrifice and +4 life via `onYourEndStepRemoveHopeDrawSac`. -/
#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 3
  let g := step g0 hopeFromSource (some (pid g0 "Dawn"))
  (obj g "Dawn").status.hope == 2

#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 2
  let before := handSize g0
  let g := g0.applyTriggeredAbility caster .onYourEndStepRemoveHopeDrawSac (some (pid g0 "Dawn"))
  (obj g "Dawn").status.hope == 1 && handSize g == before + 1 &&
    (g.player caster).life == (g0.player caster).life

#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 1
  let before := handSize g0
  let life0 := (g0.player caster).life
  let g := g0.applyTriggeredAbility caster .onYourEndStepRemoveHopeDrawSac (some (pid g0 "Dawn"))
  !(g.battlefield.any (·.name == "Dawn")) && handSize g == before + 1 &&
    (g.player caster).life == life0 + 4

#guard
  let g0 := addPermanent afterDraw dawn caster caster
  let before := handSize g0
  let life0 := (g0.player caster).life
  let g := g0.applyTriggeredAbility caster .onYourEndStepRemoveHopeDrawSac (some (pid g0 "Dawn"))
  handSize g == before && !(g.battlefield.any (·.name == "Dawn")) &&
    (g.player caster).life == life0 + 4

#guard
  let g0 := withHope (addPermanent afterDraw dawn caster caster) "Dawn" 3
  let (g1, newId) := g0.move (pid g0 "Dawn") (.graveyard caster) none
  let g1 := g1.recordPutCounters (anyObj g1 "Dawn").id .hope 3
  let g := step g1 hopeFromSource (some newId)
  (anyObj g "Dawn").status.hope == 3

/- Every counter leaves the enchanted creature, including an opponent's.
Damage and a pump stay. Nothing enchanted leaves counters intact. -/
#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear") "Bear"
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stripped g (obj g "Bear") && !(obj g "Bear").status.tapped

#guard
  let g0 := load (attach
    (addPermanent (addPermanent afterDraw foe opp opp) grasp caster caster)
    "Grasp" "Foe") "Foe"
  let g0 := withHope g0 "Grasp" 2
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stripped g (obj g "Foe") && (obj g "Grasp").status.hope == 2

#guard
  let g0 := load
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Bear"
  let g := step g0 allFromEnchanted (some (pid g0 "Grasp"))
  stillLoaded g (obj g "Bear") && g.log == g0.log

#guard
  let g0 := load (addPermanent afterDraw bear caster caster) "Bear"
  let g := step g0 allFromEnchanted
  stillLoaded g (obj g "Bear") && g.log == g0.log

/- Removing hope from the enchanted creature and removing all counters from the source work too. -/
#guard
  let g0 := load (attach
    (withHope (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
      "Grasp" 2)
    "Grasp" "Bear") "Bear"
  let crossed := step g0 (.permanent (.modifyCounters (.remove (some .hope) (.exact (.const 1))) .attachedHost))
    (some (pid g0 "Grasp"))
  let swapped := step g0 (.permanent (.modifyCounters (.remove none .anyNumber) .this))
    (some (pid g0 "Grasp"))
  (obj crossed "Bear").status.hope == 0 &&
    (obj crossed "Bear").status.plusOnePlusOne == 2 &&
    (obj crossed "Grasp").status.hope == 2 &&
    stillLoaded swapped (obj swapped "Bear") &&
    (obj swapped "Grasp").status.hope == 0

/- Tap, then remove all counters from enchanted creature (`onEnterTapEnchantedRemoveCounters`). -/
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
  !(obj g "Bear").status.tapped && stillLoaded g (obj g "Bear")

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation .onYourEndStepRemoveHopeDrawSac ==
  "At the beginning of your end step, remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life."
#guard TriggeredAbility.toNotation .onEnterTapEnchantedRemoveCounters ==
  "When this Aura enters, tap enchanted creature. Remove any number of counter(s) from enchanted creature."

end Mtg.Engine.RemoveCountersTests
