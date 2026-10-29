import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.becomePrepared`

Who becomes prepared is an `ObjectSelector`.
The announced permanent, the source, the enchanted creature, and the target
while the source remains become prepared. A creature that is already
prepared, or has no prepare spell, does not. Any other permanent the selector
names becomes prepared. A card or a hand does not.
-/

namespace Mtg.Engine.BecomePreparedTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature .becomePrepared))

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (ab : TriggeredAbility := onCreature) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets
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
  g.changeObject a.id (.attachedTo (some (pid g host)))

def markPrepared (g : Game) (name : String) : Game :=
  let o := obj g name
  g.record (GameEvent.designation g.turnNumber o.asEvent .prepared true)

def seed : AdventureFace := { name := "Seed" }

def angel : CardDef := {
  name := "Angel"
  types := #[.creature]
  power := some 2
  toughness := some 4
  prepareFace := some seed
}

def bear : CardDef := {
  name := "Bear"
  types := #[.creature]
  power := some 2
  toughness := some 2
  prepareFace := some seed
}

def plain : CardDef := creature "Plain" ManaCost.empty #[] 1 1
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def prepared : TriggeredAbility.TriggerResolution :=
  .becomePrepared

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
  !isPrepared g "Angel" && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 prepared (targets := #[Target.permanent (pid g0 "Field")])
  !isPrepared g "Angel" && !(obj g "Field").status.prepared &&
    logContains g "The target is no longer legal"

#guard
  let g := step board prepared (targets := #[Target.player opp])
  !isPrepared g "Angel" && logContains g "The target is no longer legal"

#guard
  let id := pid board "Angel"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 prepared (targets := #[Target.permanent newId])
  !(anyObj g "Angel").status.prepared &&
    logContains g "The target is no longer in play"

#guard prepared == (.becomePrepared .target : TriggeredAbility.TriggerResolution)

/- The ability's own resolution prepares the announced creature. -/
#guard TriggeredAbility.resolution onCreature == prepared

#guard
  let g := board.applyTriggeredAbility caster onCreature none
    #[Target.permanent (pid board "Angel")]
  isPrepared g "Angel" && seedExiled g "Angel" && !isPrepared g "Bear"

/- The source becomes prepared. A missing source, and a source that has
left, do not. A source with no prepare spell does not. -/
#guard
  let g := step board (.becomePrepared .source) (some (pid board "Angel"))
  isPrepared g "Angel" && !isPrepared g "Bear" && seedExiled g "Angel" &&
    logContains g "Angel becomes prepared. A copy of Seed is exiled"

#guard
  let g := step board (TriggeredAbility.TriggerResolution.ofSource .becomePrepared)
    (some (pid board "Angel")) #[Target.permanent (pid board "Bear")]
  isPrepared g "Angel" && !isPrepared g "Bear" && seedExiled g "Angel"

#guard
  let g0 := addPermanent board plain caster caster
  let g := step g0 (.becomePrepared .source) (some (pid g0 "Plain"))
    #[Target.permanent (pid g0 "Angel")]
  !isPrepared g "Plain" && !isPrepared g "Angel" &&
    logContains g "Plain has no prepare spell and can't become prepared"

#guard
  let g := step board (.becomePrepared .source)
  !isPrepared g "Angel" &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let id := pid board "Angel"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.becomePrepared .source) (some newId)
  !(anyObj g "Angel").status.prepared &&
    logContains g "Angel is no longer on the battlefield"

/- The enchanted creature becomes prepared. Nothing enchanted is silent.
An Aura that has left is reported. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Angel"
  let g := step g0 (.becomePrepared .enchanted) (some (pid g0 "Grasp"))
  isPrepared g "Angel" && seedExiled g "Angel" &&
    logContains g "Angel becomes prepared. A copy of Seed is exiled"

#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Angel"
  let g := step g0 (TriggeredAbility.TriggerResolution.ofEnchanted .becomePrepared)
    (some (pid g0 "Grasp")) #[Target.permanent (pid g0 "Bear")]
  isPrepared g "Angel" && !isPrepared g "Bear"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.becomePrepared .enchanted) (some (pid g0 "Grasp"))
  !isPrepared g "Angel" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.becomePrepared .enchanted) (some newId)
  !isPrepared g "Angel" && logContains g "Grasp is no longer on the battlefield"

#guard
  let g := step board (.becomePrepared .enchanted)
  !isPrepared g "Angel" &&
    logContains g "The Aura is no longer in play"

/- The target becomes prepared only while the source remains.
A source that has left is silent. An illegal target is reported while
the source is still there. -/
#guard
  let g := step board (.becomePrepared (.target .whileSource))
    (some (pid board "Bear")) #[Target.permanent (pid board "Angel")]
  isPrepared g "Angel" && !isPrepared g "Bear" && seedExiled g "Angel"

#guard
  let g := step board
    (TriggeredAbility.TriggerResolution.ofTargetWhileSource .becomePrepared)
    (some (pid board "Bear")) #[Target.permanent (pid board "Angel")]
  isPrepared g "Angel" && !isPrepared g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (.becomePrepared (.target .whileSource))
    (some newId) #[Target.permanent (pid g0 "Angel")]
  !isPrepared g "Angel" && g.log == g0.log

#guard
  let g := step board (.becomePrepared (.target .whileSource))
    (some (pid board "Bear"))
  !isPrepared g "Angel" && logContains g "The target is no longer legal"

/- No recorded cause, a player, and a hand do nothing. Creatures you control
become prepared. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Angel"
  let sid := some (pid g0 "Bear")
  let tgt := #[Target.permanent (pid g0 "Angel")]
  let quiet := [
    step g0 (.becomePrepared .cause) sid tgt,
    step g0 (.becomePrepared (.player .you)) sid tgt,
    step g0 (.becomePrepared .hand) sid tgt]
  let yours := step g0 (.becomePrepared .creaturesYouControl) sid tgt
  quiet.all (fun g =>
    !isPrepared g "Angel" && !isPrepared g "Bear" &&
      !(obj g "Grasp").status.prepared && g.log == g0.log) &&
    isPrepared yours "Angel" && !isPrepared yours "Bear"

/- Printed phrases stay with the recipient that produces them. -/
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomePrepared ==
  .becomePrepared
#guard TriggeredAbility.TriggerResolution.ofSource .becomePrepared ==
  .becomePrepared .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .becomePrepared ==
  .becomePrepared .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .becomePrepared ==
  .becomePrepared (.target .whileSource)

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := prepared } ==
  "target creature becomes prepared"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomePrepared .source } ==
  "this creature becomes prepared"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomePrepared .enchanted } ==
  "enchanted creature becomes prepared"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomePrepared (.target .whileSource) } ==
  "that creature becomes prepared"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomePrepared .cause } ==
  "becomes prepared"
#guard TriggeredAbility.resolutionPhrase {
    targeting := .of .creatureYouControl
    resolution := .sequence
      [.attach .source .target, .becomePrepared (.target .whileSource)] } ==
  "attach it to target creature you control. That creature becomes prepared"

#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature becomes prepared."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onSource .becomePrepared))) ==
  "When this permanent enters, this creature becomes prepared."

end Mtg.Engine.BecomePreparedTests
