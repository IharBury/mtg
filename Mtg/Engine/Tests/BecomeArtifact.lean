import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified become-artifact continuous effects

Who becomes an artifact until end of turn is an `ObjectExpr`.
The announced permanent, the source, the enchanted creature, and the target
while the source remains become artifacts. Any other permanent the expression
names becomes an artifact. A non-battlefield card does not.
-/

namespace Mtg.Engine.BecomeArtifactTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def becomeArtifactInstr (obj : ObjectExpr) : Instruction :=
  .installEffect (.applyContinuous .untilEndOfTurn obj
    (.all #[.modifyTypes { types := #[.artifact] }]))

def becomeArtifactAndIndestructibleInstr (obj : ObjectExpr) : Instruction :=
  .installEffect (.applyContinuous .untilEndOfTurn obj
    (.all #[.modifyTypes { types := #[.artifact] }, .grantKeywords #[Keyword.indestructible]]))

def onCreature : TriggeredAbility :=
  TriggeredAbility.mkTrigger .thisEnters {
    targeting := .of .creature
    body := becomeArtifactAndIndestructibleInstr (.target 0)
  }

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .creature) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targeting := .of spec, body })
    sourceId targets

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

def titan : CardDef := creature "Titan" ManaCost.empty #[] 4 4
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def golem : CardDef := {
  name := "Golem"
  types := #[.artifact, .creature]
  power := some 3
  toughness := some 3
}
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def artifacted : Instruction :=
  becomeArtifactInstr (.target 0)

def both : Instruction :=
  becomeArtifactAndIndestructibleInstr (.target 0)

def flagged (g : Game) (name : String) : Bool :=
  g.additionalArtifactUntilEot (obj g name)

def became (g : Game) (name : String) : Bool :=
  let o := obj g name
  flagged g name && g.isCreature o && (g.types o).any (· == .artifact)

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature becomes an artifact in addition to its other
types. An opponent's creature can too. A creature that is already an
artifact keeps both types. A land, a player, a missing target, and a
creature that has left are not affected. -/
#guard
  let g := step board artifacted (targets := #[Target.permanent (pid board "Titan")])
  became g "Titan" && !(obj g "Titan").printed.isArtifact && !flagged g "Bear"

#guard
  let g := step board artifacted (targets := #[Target.permanent (pid board "Bear")])
  became g "Bear" && !flagged g "Titan"

#guard
  let g0 := addPermanent board golem caster caster
  let g := step g0 artifacted (targets := #[Target.permanent (pid g0 "Golem")])
  became g "Golem" && (obj g "Golem").printed.isArtifact && !flagged g "Titan"

#guard
  let g := step board artifacted
  !flagged g "Titan"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 artifacted (targets := #[Target.permanent (pid g0 "Field")])
  !flagged g "Titan" && !g.additionalArtifactUntilEot (obj g "Field") &&
    !(g.types (obj g "Field")).any (· == .artifact)

#guard
  let g := step board artifacted (targets := #[Target.player opp])
  !flagged g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 artifacted (targets := #[Target.permanent newId])
  !g.additionalArtifactUntilEot (anyObj g "Titan")

/- Becoming an artifact and gaining indestructible resolves together. -/
#guard
  let g := step board both (targets := #[Target.permanent (pid board "Titan")])
  became g "Titan" && g.hasIndestructible (obj g "Titan") &&
    !flagged g "Bear" && !g.hasIndestructible (obj g "Bear")

#guard
  let g := board.applyTriggeredAbility caster onCreature none
    #[Target.permanent (pid board "Titan")]
  became g "Titan" && g.hasIndestructible (obj g "Titan")

/- The source becomes an artifact. A missing source, and a source that
has left, do not. Gaining indestructible follows the same recipient. -/
#guard
  let g := step board (becomeArtifactInstr .this) (some (pid board "Titan")) (spec := .none)
  became g "Titan" && !flagged g "Bear"

#guard
  let g := step board (becomeArtifactAndIndestructibleInstr .this)
    (some (pid board "Titan")) (spec := .none)
  became g "Titan" && g.hasIndestructible (obj g "Titan") && !flagged g "Bear"

#guard
  let g := step board (becomeArtifactInstr .this) (spec := .none)
  !flagged g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (becomeArtifactInstr .this) (some newId) (spec := .none)
  !g.additionalArtifactUntilEot (anyObj g "Titan")

/- The enchanted creature becomes an artifact. Nothing enchanted is
silent. An Aura that has left does not affect the creature. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (becomeArtifactInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  became g "Titan"

#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (becomeArtifactAndIndestructibleInstr .attachedHost)
    (some (pid g0 "Grasp")) (spec := .none)
  became g "Titan" && g.hasIndestructible (obj g "Titan")

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (becomeArtifactInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  !flagged g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (becomeArtifactInstr .attachedHost) (some newId) (spec := .none)
  !flagged g "Titan"

#guard
  let g := step board (becomeArtifactInstr .attachedHost) (spec := .none)
  !flagged g "Titan"

/- The target becomes an artifact only while the source remains.
A source that has left is silent. -/
def whileSourceArtifact : Instruction :=
  Instruction.ifThen (.exists .this) artifacted

#guard
  let g := step board whileSourceArtifact
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  became g "Titan" && !flagged g "Bear"

#guard
  let g := step board (Instruction.ifThen (.exists .this) both)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  became g "Titan" && g.hasIndestructible (obj g "Titan") && !flagged g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 whileSourceArtifact
    (some newId) #[Target.permanent (pid g0 "Titan")]
  !flagged g "Titan" && g.log == g0.log

/- Creatures you control become artifacts; hand cards do not. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let handOnly := step g0 (becomeArtifactInstr (.inZones (.handOf .you) .anyObject)) sid (spec := .none)
  let yours := step g0 (becomeArtifactInstr (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))) sid (spec := .none)
  !flagged handOnly "Titan" && !flagged handOnly "Bear" &&
    !handOnly.additionalArtifactUntilEot (obj handOnly "Grasp") &&
    became yours "Titan" && !flagged yours "Bear"

/- Printed phrases stay with the recipient that produces them. -/
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, body := artifacted } ==
  "until end of turn, target creature becomes an artifact in addition to its other types"
#guard TriggeredAbility.resolutionPhrase
    { body := becomeArtifactInstr .this } ==
  "until end of turn, this creature becomes an artifact in addition to its other types"
#guard TriggeredAbility.resolutionPhrase
    { body := becomeArtifactInstr .attachedHost } ==
  "until end of turn, enchanted creature becomes an artifact in addition to its other types"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, body := both } ==
  "until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible"
#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible."

end Mtg.Engine.BecomeArtifactTests
