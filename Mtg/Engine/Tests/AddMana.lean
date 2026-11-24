import Mtg.Engine.Fixture

/-!
# Unified `PlayerInstr.addMana`

The printed mana types, and those types once for each charge counter on
the source. How many times is a `ValueExpr`. A source that has left
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
  g.recordPutCounters (plotOf g).id .charge n

def addStep (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters { body }) sourceId

def perChargeMana : Instruction :=
  Effect.triggerAddGreenPerChargeCounter.body

def perOtherCreatureRed : Instruction :=
  Instruction.addMana {
    spec := .sequence #[(.colored .red, ValueExpr.count (.inZones .battlefield (.all #[
      .otherThan .this, .hasType .creature, .controlledBy .you])))]
  }

/- The controller adds the printed mana types. -/
#guard
  let g := addStep afterDraw (Instruction.addSimpleMana #[.colored .red, .colored .red])
  manaOf g (.colored .red) == 2 && manaOf g (.colored .green) == 0 &&
    logContains g "adds mana"

#guard
  let g := addStep afterDraw (Instruction.addSimpleMana #[.colored .blue, .colorless])
  manaOf g (.colored .blue) == 1 && manaOf g .colorless == 1

/- {G} for each charge counter on the source. Zero counters add nothing. -/
#guard
  let g0 := withCharge 3
  let g := addStep g0 perChargeMana (some (plotOf g0).id)
  manaOf g (.colored .green) == 3 && logContains g "adds mana"

#guard
  let g0 := withCharge 0
  let g := addStep g0 perChargeMana (some (plotOf g0).id)
  manaOf g (.colored .green) == 0

/- A source that has left still adds mana for its last-known counters. -/
#guard
  let g0 := withCharge 2
  let sid := (plotOf g0).id
  let (g1, _) := g0.move sid (.graveyard caster) none
  let g := addStep g1 perChargeMana (some sid)
  manaOf g (.colored .green) == 2 &&
    (g.findObject? sid).isNone

/- No source and no last-known counters adds no mana. -/
#guard
  let g := addStep afterDraw perChargeMana
  manaOf g (.colored .green) == 0

#guard (TriggeredAbility.onYourFirstMainAddMana #[.colored .red, .colored .red]).effect.body ==
  Instruction.addSimpleMana #[.colored .red, .colored .red]

#guard TriggeredAbility.onYourFirstMainAddGreenPerCharge.effect.body ==
  Effect.triggerAddGreenPerChargeCounter.body

#guard TriggeredAbility.toNotation
    (.onYourFirstMainAddMana #[.colored .red, .colored .red]) ==
  "At the beginning of your first main phase, add {R}{R}."

#guard TriggeredAbility.toNotation .onYourFirstMainAddGreenPerCharge ==
  "At the beginning of your first main phase, add the number of charge counters on this permanent {G}."

/- Adding a type twice repeats it. Zero times adds nothing.
A count of other creatures adds that many. -/
#guard
  let g := addStep afterDraw (Instruction.addMana { spec := .sequence #[(.colored .red, .const 2)] })
  manaOf g (.colored .red) == 2

#guard
  let zero := addStep afterDraw (Instruction.addMana { spec := .sequence #[(.colored .red, .const 0)] })
  let other := addStep afterDraw perOtherCreatureRed
  manaOf zero (.colored .red) == 0 && zero.log.size == afterDraw.log.size &&
    manaOf other (.colored .red) == 0 && other.log.size == afterDraw.log.size

#guard
  let bear : CardDef := {
    name := "Mana Bear"
    types := #[.creature]
    power := some (.fixed 2)
    toughness := some (.fixed 2)
  }
  let g0 := addPermanent afterDraw bear caster caster
  let g := addStep g0 perOtherCreatureRed
  manaOf g (.colored .red) == 1

end Mtg.Engine.AddManaTests
