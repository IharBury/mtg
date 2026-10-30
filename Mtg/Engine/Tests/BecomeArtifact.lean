import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.becomeArtifact`

Who becomes an artifact until end of turn is an `ObjectSelector`.
The announced permanent, the source, the enchanted creature, and the target
while the source remains become artifacts. Any other permanent the selector
names becomes an artifact. A card or a hand does not.
-/

namespace Mtg.Engine.BecomeArtifactTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature .becomeArtifactIndestructible))

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
  g.record (GameEvent.attached g.turnNumber a.id (pid g host) (cause := .gameRule .staticAbility))

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

def artifacted : TriggeredAbility.TriggerResolution :=
  .becomeArtifact

def both : TriggeredAbility.TriggerResolution :=
  .sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]

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
  became g "Titan" && !(obj g "Titan").printed.isArtifact && !flagged g "Bear" &&
    logContains g "Titan becomes an artifact until end of turn"

#guard
  let g := step board artifacted (targets := #[Target.permanent (pid board "Bear")])
  became g "Bear" && !flagged g "Titan" &&
    logContains g "Bear becomes an artifact until end of turn"

#guard
  let g0 := addPermanent board golem caster caster
  let g := step g0 artifacted (targets := #[Target.permanent (pid g0 "Golem")])
  became g "Golem" && (obj g "Golem").printed.isArtifact && !flagged g "Titan"

#guard
  let g := step board artifacted
  !flagged g "Titan" && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 artifacted (targets := #[Target.permanent (pid g0 "Field")])
  !flagged g "Titan" && !g.additionalArtifactUntilEot (obj g "Field") &&
    !(g.types (obj g "Field")).any (· == .artifact) &&
    logContains g "The target is no longer legal"

#guard
  let g := step board artifacted (targets := #[Target.player opp])
  !flagged g "Titan" && logContains g "The target is no longer legal"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 artifacted (targets := #[Target.permanent newId])
  !g.additionalArtifactUntilEot (anyObj g "Titan") &&
    logContains g "The target is no longer in play"

#guard artifacted == (.becomeArtifact .target : TriggeredAbility.TriggerResolution)

/- Becoming an artifact and gaining indestructible is that sequence.
The ability's own resolution does both. -/
#guard TriggeredAbility.resolution onCreature == both

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
  let g := step board (.becomeArtifact .source) (some (pid board "Titan"))
  became g "Titan" && !flagged g "Bear" &&
    logContains g "Titan becomes an artifact until end of turn"

#guard
  let g := step board (TriggeredAbility.TriggerResolution.ofSource .becomeArtifactIndestructible)
    (some (pid board "Titan")) #[Target.permanent (pid board "Titan")]
  became g "Titan" && g.hasIndestructible (obj g "Titan") && !flagged g "Bear"

#guard
  let g := step board (.becomeArtifact .source)
  !flagged g "Titan" &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.becomeArtifact .source) (some newId)
  !g.additionalArtifactUntilEot (anyObj g "Titan") &&
    logContains g "Titan is no longer on the battlefield"

/- The enchanted creature becomes an artifact. Nothing enchanted is
silent. An Aura that has left is reported. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (.becomeArtifact .enchanted) (some (pid g0 "Grasp"))
  became g "Titan" &&
    logContains g "Titan becomes an artifact until end of turn"

#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (TriggeredAbility.TriggerResolution.ofEnchanted .becomeArtifactIndestructible)
    (some (pid g0 "Grasp")) #[Target.permanent (pid g0 "Titan")]
  became g "Titan" && g.hasIndestructible (obj g "Titan")

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.becomeArtifact .enchanted) (some (pid g0 "Grasp"))
  !flagged g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.becomeArtifact .enchanted) (some newId)
  !flagged g "Titan" && logContains g "Grasp is no longer on the battlefield"

#guard
  let g := step board (.becomeArtifact .enchanted)
  !flagged g "Titan" &&
    logContains g "The Aura is no longer in play"

/- The target becomes an artifact only while the source remains.
A source that has left is silent. An illegal target is reported while
the source is still there. -/
#guard
  let g := step board (.becomeArtifact (.target .whileSource))
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  became g "Titan" && !flagged g "Bear"

#guard
  let g := step board
    (TriggeredAbility.TriggerResolution.ofTargetWhileSource .becomeArtifactIndestructible)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  became g "Titan" && g.hasIndestructible (obj g "Titan") && !flagged g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (.becomeArtifact (.target .whileSource))
    (some newId) #[Target.permanent (pid g0 "Titan")]
  !flagged g "Titan" && g.log == g0.log

#guard
  let g := step board (.becomeArtifact (.target .whileSource))
    (some (pid board "Bear"))
  !flagged g "Titan" && logContains g "The target is no longer legal"

/- No recorded cause, a player, and a hand do nothing. Creatures you control
become artifacts. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let tgt := #[Target.permanent (pid g0 "Titan")]
  let quiet := [
    step g0 (.becomeArtifact .cause) sid tgt,
    step g0 (.becomeArtifact (.player .you)) sid tgt,
    step g0 (.becomeArtifact .hand) sid tgt]
  let yours := step g0 (.becomeArtifact .creaturesYouControl) sid tgt
  quiet.all (fun g =>
    !flagged g "Titan" && !flagged g "Bear" &&
      !g.additionalArtifactUntilEot (obj g "Grasp") && g.log == g0.log) &&
    became yours "Titan" && !flagged yours "Bear"

/- Printed phrases stay with the recipient that produces them. -/
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomeArtifactIndestructible ==
  both
#guard TriggeredAbility.TriggerResolution.ofSource .becomeArtifactIndestructible ==
  .sequence [.becomeArtifact .source, .grant (.keywords Keyword.indestructible) .source]
#guard TriggeredAbility.TriggerResolution.ofEnchanted .becomeArtifactIndestructible ==
  .sequence [.becomeArtifact .enchanted, .grant (.keywords Keyword.indestructible) .enchanted]
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .becomeArtifactIndestructible ==
  .sequence [.becomeArtifact (.target .whileSource),
    .grant (.keywords Keyword.indestructible) (.target .whileSource)]

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := artifacted } ==
  "until end of turn, target creature becomes an artifact in addition to its other types"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomeArtifact .source } ==
  "until end of turn, this creature becomes an artifact in addition to its other types"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomeArtifact .enchanted } ==
  "until end of turn, enchanted creature becomes an artifact in addition to its other types"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomeArtifact (.target .whileSource) } ==
  "until end of turn, that creature becomes an artifact in addition to its other types"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := both } ==
  "until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .becomeArtifact .cause } ==
  "becomes an artifact"
#guard TriggeredAbility.resolutionPhrase {
    targeting := .of .creatureYouControl
    resolution := .sequence
      [.attach .source .target, .becomeArtifact (.target .whileSource)] } ==
  "attach it to target creature you control. Until end of turn, that creature becomes an artifact in addition to its other types"

#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onSource .becomeArtifactIndestructible))) ==
  "When this permanent enters, resolve each step."

end Mtg.Engine.BecomeArtifactTests
