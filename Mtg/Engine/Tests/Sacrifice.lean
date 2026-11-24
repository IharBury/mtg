import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture
import Mtg.Engine.Game

/-!
# Unified sacrifice instructions (`Instruction.sacrifice` / `Instruction.moveZone ... .sacrifice`)

Source sacrifice, target opponent sacrifices a creature, each player sacrifices
a creature, defending player sacrifices least power, each opponent sacrifices
a nontoken creature, Plan sacrifice, and Bolg's optional sacrifice all execute
through `Game/Interpreter.lean`.
-/

namespace Mtg.Engine.SacrificeTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def relic : CardDef := { name := "Sacrifice Relic", types := #[.artifact] }

def attacker : CardDef := {
  name := "Sacrifice Attacker"
  types := #[.creature]
  power := some (.fixed 3)
  toughness := some (.fixed 3)
}

def fodder : CardDef := {
  name := "Sacrifice Fodder"
  types := #[.creature]
  power := some (.fixed 1)
  toughness := some (.fixed 1)
}

def planCard : CardDef := { name := "The Plan", types := #[.enchantment] }

def stepBody (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .none) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targets := spec, body })
    sourceId targets

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def inGraveyard (g : Game) (owner : PlayerId) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .graveyard owner)

def pid (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def withRelic : Game := addPermanent afterDraw relic caster caster

/- The source is sacrificed. A missing source leaves permanents untouched. -/
#guard
  let g0 := withRelic
  let sid := pid g0 "Sacrifice Relic"
  let g := stepBody g0 (Instruction.sacrifice .this) (some sid)
  !onBoard g "Sacrifice Relic" && inGraveyard g caster "Sacrifice Relic"

#guard
  let g := stepBody withRelic (Instruction.sacrifice .this)
  onBoard g "Sacrifice Relic"

/- Target opponent chooses a creature to sacrifice. Missing target does nothing. -/
#guard
  let g0 := addPermanent afterDraw fodder opp opp
  let g := g0.applyTriggeredAbility caster .onEnterTargetOpponentSacrificesCreature
    none #[Target.player opp]
  match g.pending with
  | .sacrificeCreature p => p == opp && onBoard g "Sacrifice Fodder"
  | _ => false

#guard
  let g := afterDraw.applyTriggeredAbility caster .onEnterTargetOpponentSacrificesCreature
    none #[]
  g.pending == afterDraw.pending

/- Each player sacrifices a creature when someone controls one. -/
#guard
  let g0 := addPermanent afterDraw fodder opp opp
  let g := g0.applyTriggeredAbility caster .onEnterEachPlayerSacrificesCreature none
  match g.pending with
  | .chooseSacrificeCreature p _ _ => p == opp && onBoard g "Sacrifice Fodder"
  | _ => false

#guard
  let g := afterDraw.applyTriggeredAbility caster .onEnterEachPlayerSacrificesCreature none
  match g.pending with
  | .chooseSacrificeCreature .. => false
  | _ => true

/- Defending player sacrifices a least-power creature. Ties prompt a choice. -/
#guard
  let g0 := addPermanent afterDraw fodder opp opp
  let g := g0.applyTriggeredAbility caster .onAttackDefenderSacsLeastPower none
  !onBoard g "Sacrifice Fodder" && inGraveyard g opp "Sacrifice Fodder"

#guard
  let g0 := addPermanent (addPermanent afterDraw attacker caster caster) fodder caster caster
  let sid := pid g0 "Sacrifice Attacker"
  let g0 := g0.markAttacking sid (some (.player caster))
  let g := g0.applyTriggeredAbility caster .onAttackDefenderSacsLeastPower (some sid)
  onBoard g "Sacrifice Attacker" && !onBoard g "Sacrifice Fodder" &&
    inGraveyard g caster "Sacrifice Fodder"

#guard
  let g := afterDraw.applyTriggeredAbility caster .onAttackDefenderSacsLeastPower none
  g.pending == afterDraw.pending

#guard
  let tied : CardDef := { fodder with name := "Tied Fodder" }
  let g0 := addPermanent (addPermanent afterDraw fodder opp opp) tied opp opp
  let g := g0.applyTriggeredAbility caster .onAttackDefenderSacsLeastPower none
  onBoard g "Sacrifice Fodder" && onBoard g "Tied Fodder" &&
    match g.pending with
    | .fraChoice p (.sacrificeLeastPower _) => p == opp
    | _ => false

/- Each opponent chooses a nontoken creature (`deathDeathtouchOppSac`). -/
#guard
  let g := (addPermanent afterDraw fodder opp opp).applyTriggeredAbility caster
    (.onDeath Effect.deathDeathtouchOppSac) none
  onBoard g "Sacrifice Fodder" &&
    match g.pending with
    | .fraChoice p (.sacrificeNontokenEach _ _) => p == opp
    | _ => false

#guard
  let g := afterDraw.applyTriggeredAbility caster (.onDeath Effect.deathDeathtouchOppSac) none
  g.pending == afterDraw.pending

/- Bolg's optional sacrifice of another creature offers the choice when source is present. -/
#guard
  let g0 := addPermanent withRelic fodder caster caster
  let sid := pid g0 "Sacrifice Relic"
  let g := g0.applyTriggeredAbility caster .onEnterBolgMaySacrifice (some sid)
  onBoard g "Sacrifice Relic" && g.pending != .none

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation .onEnterTargetOpponentSacrificesCreature ==
  "When this permanent enters, target opponent sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onEnterEachPlayerSacrificesCreature ==
  "When this permanent enters, each player sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onAttackDefenderSacsLeastPower ==
  "Whenever this creature attacks, defending player sacrifices a creature with the least power among creatures they control."
#guard TriggeredAbility.toNotation .onEnterBolgMaySacrifice ==
  "When this permanent enters, you may sacrifice another creature. When you do, deals damage equal to that permanent's power to another target creature; if the excess damage dealt this way is greater than 0, amass Goblins the excess damage dealt this way."

end Mtg.Engine.SacrificeTests
