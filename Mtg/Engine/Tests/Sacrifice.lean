import Mtg.Engine.Fixture
import Mtg.Engine.Game

/-!
# `TriggerResolution.sacrifice`

Who sacrifices and which permanent are one `ObjectSelector`.
Any other selector sacrifices nothing.
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
  power := some 3
  toughness := some 3
}

def fodder : CardDef := {
  name := "Sacrifice Fodder"
  types := #[.creature]
  power := some 1
  toughness := some 1
}

def planCard : CardDef := { name := "The Plan", types := #[.enchantment] }

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (resolutionOverride := some r)

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def inGraveyard (g : Game) (owner : PlayerId) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .graveyard owner)

def pid (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def withRelic : Game := addPermanent afterDraw relic caster caster

def phrase (r : TriggeredAbility.TriggerResolution) : String :=
  TriggeredAbility.resolutionPhrase { resolution := r }

/- The source is sacrificed. A missing source is reported and the noted
flag stays clear. The controller's wording names that player. Moving the
source as sacrificed uses the same log without a separate player clause.
Noting the sacrifice records it. A note the source does not read, and a
selector that is not a sacrifice, leave the permanent where it is. -/
#guard
  let g0 := withRelic
  let sid := pid g0 "Sacrifice Relic"
  let g := step g0 (.sacrifice .source) (some sid)
  !onBoard g "Sacrifice Relic" && inGraveyard g caster "Sacrifice Relic" &&
    !g.sourceWasSacrificed && logContains g "Sacrifice Relic is sacrificed" &&
    !(logContains g "sacrifices Sacrifice Relic")

#guard
  let g := step (withRelic.change (.sourceWasSacrificed true)) (.sacrifice .source)
  onBoard g "Sacrifice Relic" && g.sourceWasSacrificed &&
    logContains g "The ability's source is no longer in play"

#guard
  let g0 := withRelic
  let g := step g0 (.sacrifice (.sacrificedSource .controllerSacrifices))
    (some (pid g0 "Sacrifice Relic"))
  !onBoard g "Sacrifice Relic" && inGraveyard g caster "Sacrifice Relic" &&
    logContains g "Chandra sacrifices Sacrifice Relic" &&
    !(logContains g "Sacrifice Relic is sacrificed")

#guard
  let g0 := withRelic
  let g := step g0 (.sacrifice (.sacrificedSource .movedAsSacrificed))
    (some (pid g0 "Sacrifice Relic"))
  !onBoard g "Sacrifice Relic" && inGraveyard g caster "Sacrifice Relic" &&
    logContains g "Sacrifice Relic is sacrificed" && !g.sourceWasSacrificed

#guard
  let g0 := withRelic
  let g := step g0 (.sacrifice (.sacrificedSource .isSacrificed) .noted)
    (some (pid g0 "Sacrifice Relic"))
  g.sourceWasSacrificed && !onBoard g "Sacrifice Relic" &&
    logContains g "Sacrifice Relic is sacrificed"

#guard
  let g := step (withRelic.change (.sourceWasSacrificed true))
    (.sacrifice .source .noted)
  !g.sourceWasSacrificed && onBoard g "Sacrifice Relic" &&
    logContains g "The ability's source is no longer in play"

/- The reflexive note still sacrifices by `how`, and records that it did. -/
#guard
  let g0 := withRelic
  let sid := pid g0 "Sacrifice Relic"
  let g := step g0 (.sacrifice (.sacrificedSource .isSacrificed) .forReflexive) (some sid)
  !onBoard g "Sacrifice Relic" && inGraveyard g caster "Sacrifice Relic" &&
    g.planWasSacrificed && !g.sourceWasSacrificed &&
    logContains g "Sacrifice Relic is sacrificed"

#guard
  let g0 := withRelic
  let sid := pid g0 "Sacrifice Relic"
  let g := step g0 (.sacrifice .target) (some sid)
  onBoard g "Sacrifice Relic" && g.log == g0.log && g.pending == g0.pending

/- The announced opponent chooses a creature. No target, or a note this
selector does not read, sacrifices nothing. -/
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
  g.pending == afterDraw.pending && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent afterDraw fodder opp opp
  let g := g0.applyTriggeredAbility caster .onEnterTargetOpponentSacrificesCreature
    none #[Target.player opp]
    (resolutionOverride := some (.sacrifice .opponentChosenCreature .noted))
  onBoard g "Sacrifice Fodder" && g.pending == g0.pending &&
    !(logContains g "must sacrifice")

/- Each player is asked, in turn, when someone controls a creature. -/
#guard
  let g0 := addPermanent afterDraw fodder opp opp
  let g := step g0 (.sacrifice .eachPlayersCreature)
  match g.pending with
  | .chooseSacrificeCreature p _ _ => p == opp && onBoard g "Sacrifice Fodder"
  | _ => false

#guard
  let g := step afterDraw (.sacrifice .eachPlayersCreature)
  (match g.pending with
    | .chooseSacrificeCreature .. => false
    | _ => true) &&
    logContains g "Chandra has no creature to sacrifice" &&
    logContains g "Nissa has no creature to sacrifice"

/- The defending player sacrifices a least-power creature. An attacking
source asks the player it is attacking. Otherwise it asks the opponent.
No creatures there is reported. A tied choice is still a choice. -/
#guard
  let g0 := addPermanent afterDraw fodder opp opp
  let g := step g0 (.sacrifice .leastPower)
  !onBoard g "Sacrifice Fodder" && inGraveyard g opp "Sacrifice Fodder" &&
    logContains g "Nissa sacrifices Sacrifice Fodder (least power)"

#guard
  let g0 := addPermanent (addPermanent afterDraw attacker caster caster) fodder caster caster
  let sid := pid g0 "Sacrifice Attacker"
  let g0 := g0.markAttacking sid (some (.player caster))
  let g := step g0 (.sacrifice .leastPower) (some sid)
  onBoard g "Sacrifice Attacker" && !onBoard g "Sacrifice Fodder" &&
    inGraveyard g caster "Sacrifice Fodder" &&
    logContains g "Chandra sacrifices Sacrifice Fodder (least power)"

#guard
  let g := step afterDraw (.sacrifice .leastPower)
  g.pending == afterDraw.pending &&
    logContains g "Nissa controls no creatures to sacrifice"

#guard
  let tied : CardDef := { fodder with name := "Tied Fodder" }
  let g0 := addPermanent (addPermanent afterDraw fodder opp opp) tied opp opp
  let g := step g0 (.sacrifice .leastPower)
  onBoard g "Sacrifice Fodder" && onBoard g "Tied Fodder" &&
    match g.pending with
    | .fraChoice p (.sacrificeLeastPower _) => p == opp
    | _ => false

/- Each opponent sacrifices a creature that dealt combat damage. None
means that opponent sacrifices nothing. -/
#guard
  let g := step (addPermanent afterDraw fodder opp opp) (.sacrifice .combatDamager)
  g.pending == afterDraw.pending && onBoard g "Sacrifice Fodder" &&
    logContains g "Nissa controls no creature that dealt combat damage this turn"

/- Each opponent chooses a nontoken creature. An opponent with none is skipped. -/
#guard
  let g := step (addPermanent afterDraw fodder opp opp) (.sacrifice .chosenNontokenCreature)
  onBoard g "Sacrifice Fodder" &&
    match g.pending with
    | .fraChoice p (.sacrificeNontokenEach _ _) => p == opp
    | _ => false

#guard
  let g := step afterDraw (.sacrifice .chosenNontokenCreature)
  g.pending == afterDraw.pending && g.log == afterDraw.log

/- The Plan is sacrificed, and the reflexive note records that it was.
A Plan that has left does not. The source note sacrifices it and records
that the source was sacrificed. -/
#guard
  let g0 := addPermanent afterDraw planCard caster caster
  let sid := pid g0 "The Plan"
  let g := step g0 (.sacrifice .plan) (some sid)
  !onBoard g "The Plan" && !g.planWasSacrificed &&
    logContains g "the Plan is completed"

#guard
  let g0 := addPermanent afterDraw planCard caster caster
  let sid := pid g0 "The Plan"
  let g := step g0 (.sacrifice .plan .forReflexive) (some sid)
  !onBoard g "The Plan" && g.planWasSacrificed &&
    logContains g "the Plan is completed"

#guard
  let g0 := addPermanent afterDraw planCard caster caster
  let sid := pid g0 "The Plan"
  let (gGone, _) := g0.move sid (.graveyard caster) none
  let g := step gGone (.sacrifice .plan .forReflexive) (some sid)
  !g.planWasSacrificed &&
    logContains g "is no longer on the battlefield. The reflexive ability doesn't trigger."

#guard
  let g0 := addPermanent afterDraw planCard caster caster
  let sid := pid g0 "The Plan"
  let g := step g0 (.sacrifice .plan .noted) (some sid)
  !onBoard g "The Plan" && inGraveyard g caster "The Plan" &&
    g.sourceWasSacrificed && !g.planWasSacrificed &&
    logContains g "The Plan is sacrificed"

/- Another creature is the Bolg choice. A missing source is reported. -/
#guard
  let g0 := withRelic
  let sid := pid g0 "Sacrifice Relic"
  let g := step g0 (.may (.sacrifice .another) (.sequence [])) (some sid)
  onBoard g "Sacrifice Relic" &&
    match g.pending with
    | .maySacrificeAnotherBolg p id => p == caster && id == sid
    | _ => false

#guard
  let g := step afterDraw (.sacrifice .another)
  g.pending == afterDraw.pending && logContains g "Bolg is no longer in play"

/- Printed phrases stay with the selector that produces them. -/
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .opponent, resolution := .sacrifice .opponentChosenCreature } ==
  "target opponent sacrifices a creature of their choice"
#guard phrase (.sacrifice .eachPlayersCreature) ==
  "each player sacrifices a creature of their choice"
#guard phrase (.sacrifice .leastPower) ==
  "defending player sacrifices a creature with the least power among creatures they control"
#guard phrase (.sacrifice .combatDamager) ==
  "each opponent sacrifices a creature of their choice that dealt combat damage to you this turn"
#guard phrase (.sacrifice .chosenNontokenCreature) ==
  "each opponent sacrifices a nontoken creature of their choice"
#guard phrase (.sacrifice (.sacrificedSource .controllerSacrifices)) ==
  "sacrifice this creature"
#guard phrase (.sacrifice .source) == "sacrifice it"
#guard phrase (.sacrifice (.sacrificedSource .isSacrificed)) == "sacrifice it"
#guard phrase (.sacrifice (.sacrificedSource .movedAsSacrificed)) == "sacrifice it"
#guard phrase (.sacrifice .plan) == "sacrifice it"
#guard phrase (.sacrifice .another) ==
  "sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
#guard phrase (.may (.sacrifice .another) (.sequence [])) ==
  "you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
#guard phrase (.sacrifice .target) == "sacrifice it"

end Mtg.Engine.SacrificeTests
