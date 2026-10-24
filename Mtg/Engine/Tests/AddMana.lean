import Mtg.Engine.Fixture

/-!
# `TriggerResolution.addMana`

The printed mana types, and those types once for each charge counter on
the source. How many times is a `NumberSelector`. A source that has left
uses its last-known charge counters. Zero times adds nothing.
-/

namespace Mtg.Engine.AddManaTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩

def plot : CardDef := {
  name := "Charge Plot"
  types := #[.enchantment]
}

def manaOf (g : Game) (t : ManaType) : Nat :=
  (g.player caster).manaPool.get t

def plotOf (g : Game) : GameObject :=
  match g.battlefield.find? (·.name == "Charge Plot") with
  | some o => o
  | none => panic! "missing Charge Plot"

def withCharge (n : Nat) : Game :=
  let g := addPermanent afterDraw plot caster caster
  g.changeStatus (plotOf g).id (.charge n)

def addStep (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId
    (resolutionOverride := some r)

/- The controller adds the printed mana types. -/
#guard
  let g := addStep afterDraw (.addMana #[.colored .red, .colored .red])
  manaOf g (.colored .red) == 2 && manaOf g (.colored .green) == 0 &&
    logContains g "adds mana"

#guard
  let g := addStep afterDraw (.addMana #[.colored .blue, .colorless])
  manaOf g (.colored .blue) == 1 && manaOf g .colorless == 1

/- {G} for each charge counter on the source. Zero counters add nothing. -/
#guard
  let g0 := withCharge 3
  let g := addStep g0
    (.addMana #[.colored .green] .perChargeCounter)
    (some (plotOf g0).id)
  manaOf g (.colored .green) == 3 && logContains g "adds mana"

#guard
  let g0 := withCharge 0
  let g := addStep g0
    (.addMana #[.colored .green] .perChargeCounter)
    (some (plotOf g0).id)
  manaOf g (.colored .green) == 0

/- A source that has left still adds mana for its last-known counters. -/
#guard
  let g0 := withCharge 2
  let sid := (plotOf g0).id
  let (g1, _) := g0.move sid (.graveyard caster) none
  let g := addStep g1
    (.addMana #[.colored .green] .perChargeCounter) (some sid)
  manaOf g (.colored .green) == 2 &&
    (g.findObject? sid).isNone

/- No source and no last-known counters adds no mana. -/
#guard
  let g := addStep afterDraw
    (.addMana #[.colored .green] .perChargeCounter)
  manaOf g (.colored .green) == 0

#guard TriggeredAbility.resolution
    (.onYourFirstMainAddMana #[.colored .red, .colored .red]) ==
  .addMana #[.colored .red, .colored .red]

#guard TriggeredAbility.resolution
    (.onStep (Effect.ofTrigger .addGreenPerChargeCounter)) ==
  .addMana #[.colored .green] .perChargeCounter

#guard TriggeredAbility.toNotation
    (.onYourFirstMainAddMana #[.colored .red, .colored .red]) ==
  "At the beginning of your first main phase, add {R}{R}."

#guard TriggeredAbility.toNotation
    (.onStep (Effect.ofTrigger .addGreenPerChargeCounter)) ==
  "At the beginning of your first main phase, add {G} for each charge counter on this enchantment."

#guard (SharedTrigger.timing .addGreenPerChargeCounter).resolution ==
  .addMana #[.colored .green] .perChargeCounter

/- Adding the types twice repeats them. Zero times adds nothing.
A count of other creatures adds that many. -/
#guard
  let g := addStep afterDraw (.addMana #[.colored .red] (.fixed 2))
  manaOf g (.colored .red) == 2

#guard
  let zero := addStep afterDraw (.addMana #[.colored .red] (.fixed 0))
  let other := addStep afterDraw (.addMana #[.colored .red] .perOtherCreature)
  manaOf zero (.colored .red) == 0 && zero.log.size == afterDraw.log.size &&
    manaOf other (.colored .red) == 0 && other.log.size == afterDraw.log.size

#guard
  let bear : CardDef := {
    name := "Mana Bear"
    types := #[.creature]
    power := some 2
    toughness := some 2
  }
  let g0 := addPermanent afterDraw bear caster caster
  let g := addStep g0 (.addMana #[.colored .red] .perOtherCreature)
  manaOf g (.colored .red) == 1

#guard TriggeredAbility.resolutionPhrase
    { resolution := .addMana #[.colored .red] .perOtherCreature } == "add mana"

end Mtg.Engine.AddManaTests
