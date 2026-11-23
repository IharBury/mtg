import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified `PermanentInstr.setDesignation` (`.prepared`)

Who becomes prepared is an `ObjectExpr`.
The announced permanent, the source, the enchanted creature, and the target
while the source remains become prepared. A creature that is already
prepared, or has no prepare spell, does not. Any other permanent the expression
names becomes prepared. A card in hand does not.
-/

namespace Mtg.Engine.BecomePreparedTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def prepareInstr (obj : ObjectExpr) : Instruction :=
  .permanent (.setDesignation obj .prepared true)

def onCreature : TriggeredAbility :=
  TriggeredAbility.mkTrigger .thisEnters { targets := .creature, body := prepareInstr (.target 0) }

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .creature) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targets := spec, body })
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

def markPrepared (g : Game) (name : String) : Game :=
  let o := obj g name
  g.record (GameEvent.designation g.turnNumber (g.snapshot o) .prepared true (cause := .gameRule .staticAbility))

def seed : SubFace := { kind := .prepare, name := "Seed" }

def angel : CardDef := {
  name := "Angel"
  types := #[.creature]
  power := some (.fixed 2)
  toughness := some (.fixed 4)
  subFaces := #[{ seed with kind := .prepare }]
}

def bear : CardDef := {
  name := "Bear"
  types := #[.creature]
  power := some (.fixed 2)
  toughness := some (.fixed 2)
  subFaces := #[{ seed with kind := .prepare }]
}

def plain : CardDef := creature "Plain" ManaCost.empty #[] 1 1
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def prepared : Instruction :=
  prepareInstr (.target 0)

def isPrepared (g : Game) (name : String) : Bool :=
  (obj g name).status.prepared

def seedExiled (g : Game) (host : String) : Bool :=
  let hostId := (obj g host).id
  g.objects.any fun o =>
    o.zone == .exile && o.name == "Seed" &&
      ((g.playPermission o).bind (·.prepareSource)) == some hostId

def board : Game :=
  addPermanent (addPermanent afterDraw angel caster caster) bear opp opp

/- The announced creature becomes prepared. An opponent's creature can too.
A creature that is already prepared, or has no prepare spell, does not.
A land, a player, a missing target, and a creature that has left are not
affected. -/
#guard
  let g := step board prepared (targets := #[Target.permanent (pid board "Angel")])
  isPrepared g "Angel" && !isPrepared g "Bear" && seedExiled g "Angel" &&
    g.objects.size == board.objects.size + 1 &&
    logContains g "Angel becomes prepared. A copy of Seed is exiled"

#guard
  let g := step board prepared (targets := #[Target.permanent (pid board "Bear")])
  isPrepared g "Bear" && !isPrepared g "Angel" && seedExiled g "Bear" &&
    logContains g "Bear becomes prepared. A copy of Seed is exiled"

#guard
  let g1 := step board prepared (targets := #[Target.permanent (pid board "Angel")])
  let g := step g1 prepared (targets := #[Target.permanent (pid g1 "Angel")])
  isPrepared g "Angel" && g.objects.size == g1.objects.size &&
    logContains g "Angel is already prepared"

#guard
  let g0 := markPrepared board "Angel"
  let g := step g0 prepared (targets := #[Target.permanent (pid g0 "Angel")])
  isPrepared g "Angel" && g.objects.size == g0.objects.size &&
    !seedExiled g "Angel" && logContains g "Angel is already prepared"

#guard
  let g0 := addPermanent board plain caster caster
  let g := step g0 prepared (targets := #[Target.permanent (pid g0 "Plain")])
  !isPrepared g "Plain" && !isPrepared g "Angel" &&
    g.objects.size == g0.objects.size &&
    logContains g "Plain has no prepare spell and can't become prepared"

#guard
  let g := step board prepared
  !isPrepared g "Angel"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 prepared (targets := #[Target.permanent (pid g0 "Field")])
  !isPrepared g "Angel" && !(obj g "Field").status.prepared

#guard
  let g := step board prepared (targets := #[Target.player opp])
  !isPrepared g "Angel"

#guard
  let id := pid board "Angel"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 prepared (targets := #[Target.permanent newId])
  !(anyObj g "Angel").status.prepared

/- The ability's own unified body prepares the announced creature. -/
#guard
  let g := board.applyTriggeredAbility caster onCreature none
    #[Target.permanent (pid board "Angel")]
  isPrepared g "Angel" && seedExiled g "Angel" && !isPrepared g "Bear"

/- The source becomes prepared. A missing source, and a source that has
left, do not. A source with no prepare spell does not. -/
#guard
  let g := step board (prepareInstr .this) (some (pid board "Angel")) (spec := .none)
  isPrepared g "Angel" && !isPrepared g "Bear" && seedExiled g "Angel" &&
    logContains g "Angel becomes prepared. A copy of Seed is exiled"

#guard
  let g0 := addPermanent board plain caster caster
  let g := step g0 (prepareInstr .this) (some (pid g0 "Plain")) (spec := .none)
  !isPrepared g "Plain" && !isPrepared g "Angel" &&
    logContains g "Plain has no prepare spell and can't become prepared"

#guard
  let g := step board (prepareInstr .this) (spec := .none)
  !isPrepared g "Angel"

#guard
  let id := pid board "Angel"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (prepareInstr .this) (some newId) (spec := .none)
  !(anyObj g "Angel").status.prepared

/- The enchanted creature becomes prepared. Nothing enchanted is silent. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Angel"
  let g := step g0 (prepareInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  isPrepared g "Angel" && seedExiled g "Angel" &&
    logContains g "Angel becomes prepared. A copy of Seed is exiled"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (prepareInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  !isPrepared g "Angel" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (prepareInstr .attachedHost) (some newId) (spec := .none)
  !isPrepared g "Angel"

/- The target becomes prepared only while the source remains.
A source that has left is silent. -/
def whileSourcePrepared : Instruction :=
  Instruction.ifThen (.exists .this) prepared

#guard
  let g := step board whileSourcePrepared
    (some (pid board "Bear")) #[Target.permanent (pid board "Angel")]
  isPrepared g "Angel" && !isPrepared g "Bear" && seedExiled g "Angel"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 whileSourcePrepared
    (some newId) #[Target.permanent (pid g0 "Angel")]
  !isPrepared g "Angel" && g.log == g0.log

/- Creatures you control become prepared; hand cards do not. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Angel"
  let sid := some (pid g0 "Bear")
  let handOnly := step g0 (prepareInstr (.inZones (.handOf .you) .anyObject)) sid (spec := .none)
  let yours := step g0 (prepareInstr (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))) sid (spec := .none)
  !isPrepared handOnly "Angel" && !isPrepared handOnly "Bear" &&
    !(obj handOnly "Grasp").status.prepared &&
    isPrepared yours "Angel" && !isPrepared yours "Bear"

/- Printed phrases stay with the recipient that produces them. -/
#guard TriggeredAbility.resolutionPhrase
    { targets := .creature, body := prepared } ==
  "target creature becomes prepared"
#guard TriggeredAbility.resolutionPhrase
    { body := prepareInstr .this } ==
  "this creature becomes prepared"
#guard TriggeredAbility.resolutionPhrase
    { body := prepareInstr .attachedHost } ==
  "enchanted creature becomes prepared"
#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature becomes prepared."
#guard TriggeredAbility.toNotation
    (TriggeredAbility.mkTrigger .thisEnters { body := prepareInstr .this }) ==
  "When this permanent enters, this creature becomes prepared."

end Mtg.Engine.BecomePreparedTests
