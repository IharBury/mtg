import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.setBasePT`

The announced permanent, the source, the enchanted creature, and the target
while the source remains get a fixed base power and toughness until end of
turn. Another target creature's base power and toughness become equal to
this creature's. What the new base is, and who receives it, are arguments.
-/

namespace Mtg.Engine.SetBasePTTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature (.setBasePT 1 1)))

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (ab : TriggeredAbility := onCreature)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets
    (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)
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
  g.setObject { a with attachedTo := some (pid g host) }

def titan : CardDef := creature "Titan" ManaCost.empty #[] 4 4
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def ogre : CardDef := creature "Ogre" ManaCost.empty #[] 3 3
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def fixed : TriggeredAbility.TriggerResolution := .setBasePT 1 1

def equalSource : TriggeredAbility.TriggerResolution :=
  .setBasePT 0 0 (amount := .equalSource)

def base (g : Game) (name : String) : Option (Int × Int) :=
  (obj g name).status.setBasePT

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature's base power and toughness become the fixed
values. Another creature is unchanged. A missing target, a land, a player,
and a creature that has left are not set. -/
#guard
  let g := step board fixed (targets := #[Target.permanent (pid board "Titan")])
  base g "Titan" == some (1, 1) && g.basePower (obj g "Titan") == 1 &&
    g.baseToughness (obj g "Titan") == 1 && g.power (obj g "Titan") == 1 &&
    base g "Bear" == none &&
    logContains g "Titan has base power and toughness 1/1 until end of turn"

#guard
  let o := obj board "Bear"
  let marked := board.setObject { o with status := { o.status with plusOnePlusOne := 1 } }
  let g := step marked fixed (targets := #[Target.permanent (pid marked "Bear")])
  base g "Bear" == some (1, 1) && g.basePower (obj g "Bear") == 1 &&
    g.power (obj g "Bear") == 2 &&
    (obj g "Bear").status.plusOnePlusOne == 1

#guard
  let g := step board fixed
  base g "Titan" == none && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 fixed (targets := #[Target.permanent (pid g0 "Field")])
  base g "Titan" == none && base g "Field" == none &&
    logContains g "The target is no longer legal"

#guard
  let g := step board fixed (targets := #[Target.player opp])
  base g "Titan" == none && logContains g "The target is no longer legal"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 fixed (targets := #[Target.permanent newId])
  (anyObj g "Titan").status.setBasePT == none &&
    logContains g "The target is no longer in play"

#guard (.setBasePT 1 1 : TriggeredAbility.TriggerResolution) ==
  .setBasePT 1 1 .target .fixed

/- The source gets the fixed base. A missing source, and a source that has
left, are not set. -/
#guard
  let g := step board (.setBasePT 5 5 .source) (some (pid board "Titan"))
  base g "Titan" == some (5, 5) && base g "Bear" == none &&
    logContains g "Titan has base power and toughness 5/5 until end of turn"

#guard
  let g := step board (.setBasePT 5 5 .source)
  base g "Titan" == none &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.setBasePT 5 5 .source) (some newId)
  (anyObj g "Titan").status.setBasePT == none &&
    logContains g "Titan is no longer on the battlefield"

/- The enchanted creature gets the fixed base. Nothing enchanted is silent.
An Aura that has left is reported. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (.setBasePT 0 2 .enchanted) (some (pid g0 "Grasp"))
  base g "Titan" == some (0, 2) &&
    logContains g "Titan has base power and toughness 0/2 until end of turn"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.setBasePT 0 2 .enchanted) (some (pid g0 "Grasp"))
  base g "Titan" == none && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.setBasePT 0 2 .enchanted) (some newId)
  base g "Titan" == none && logContains g "Grasp is no longer on the battlefield"

#guard
  let g := step board (.setBasePT 0 2 .enchanted)
  base g "Titan" == none && logContains g "The Aura is no longer in play"

/- The target gets the fixed base only while the source remains. A source
that has left is silent. An illegal target is reported while the source is
still there. -/
#guard
  let g := step board (.setBasePT 3 1 .targetWhileSource)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  base g "Titan" == some (3, 1) && base g "Bear" == none

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (.setBasePT 3 1 .targetWhileSource)
    (some newId) #[Target.permanent (pid g0 "Titan")]
  base g "Titan" == none && g.log == g0.log

#guard
  let g := step board (.setBasePT 3 1 .targetWhileSource) (some (pid board "Bear"))
  base g "Titan" == none && logContains g "The target is no longer legal"

/- Another target creature's base becomes this creature's power and
toughness, including a pump, and including last-known values after the
source has left. No target logs that none was chosen. The source itself,
an opponent's creature, and a creature that has left are not set. -/
#guard
  let g0 := addPermanent board ogre caster caster
  let g := step g0 equalSource (some (pid g0 "Titan"))
    #[Target.permanent (pid g0 "Ogre")] (ab := .onAttackSetOtherBasePT)
  base g "Ogre" == some (4, 4) && g.power (obj g "Ogre") == 4 &&
    base g "Titan" == none &&
    logContains g "Ogre's base power and toughness become 4/4 until end of turn"

#guard
  let g0 := addPermanent board ogre caster caster
  let g0 := g0.pumpPermanent (obj g0 "Titan") 2 1
  let g := step g0 equalSource (some (pid g0 "Titan"))
    #[Target.permanent (pid g0 "Ogre")] (ab := .onAttackSetOtherBasePT)
  g.power (obj g "Titan") == 6 && base g "Ogre" == some (6, 5) &&
    logContains g "Ogre's base power and toughness become 6/5 until end of turn"

#guard
  let g := step board equalSource (some (pid board "Titan"))
    (ab := .onAttackSetOtherBasePT)
  base g "Bear" == none && base g "Titan" == none &&
    logContains g "No target was chosen"

#guard
  let g := step board equalSource (some (pid board "Titan"))
    #[Target.permanent (pid board "Titan")] (ab := .onAttackSetOtherBasePT)
  base g "Titan" == none && logContains g "The target is no longer legal"

#guard
  let g := step board equalSource (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")] (ab := .onAttackSetOtherBasePT)
  base g "Bear" == none && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board ogre caster caster
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 equalSource (some newId) #[Target.permanent (pid g1 "Ogre")]
    (ab := .onAttackSetOtherBasePT)
    (lastKnownPower := some 4) (lastKnownToughness := some 4)
  base g "Ogre" == some (4, 4) &&
    logContains g "Ogre's base power and toughness become 4/4 until end of turn"

#guard
  let g0 := addPermanent board ogre caster caster
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 equalSource (some newId) #[Target.permanent (pid g1 "Ogre")]
    (ab := .onAttackSetOtherBasePT)
  base g "Ogre" == some (0, 0) &&
    logContains g "Ogre's base power and toughness become 0/0 until end of turn"

#guard
  let g0 := addPermanent board ogre caster caster
  let id := pid g0 "Ogre"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 equalSource (some (pid g1 "Titan")) #[Target.permanent newId]
    (ab := .onAttackSetOtherBasePT)
  logContains g "The target is no longer in play"

/- Equal to this creature for anyone but the announced target sets nothing. -/
#guard
  let g0 := attach (addPermanent (addPermanent board ogre caster caster) grasp caster caster)
    "Grasp" "Titan"
  let sid := some (pid g0 "Titan")
  let tgt := #[Target.permanent (pid g0 "Ogre")]
  let crossed := [
    step g0 (.setBasePT 0 0 .source .equalSource) sid tgt
      (ab := .onAttackSetOtherBasePT),
    step g0 (.setBasePT 0 0 .enchanted .equalSource) sid tgt
      (ab := .onAttackSetOtherBasePT),
    step g0 (.setBasePT 0 0 .targetWhileSource .equalSource) sid tgt
      (ab := .onAttackSetOtherBasePT)]
  crossed.all fun g =>
    base g "Titan" == none && base g "Ogre" == none && g.log == g0.log

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.TriggerResolution.ofPermanent (.setBasePT 2 2) == .setBasePT 2 2
#guard TriggeredAbility.TriggerResolution.ofSource (.setBasePT 2 2) ==
  .setBasePT 2 2 .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted (.setBasePT 2 2) ==
  .setBasePT 2 2 .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource (.setBasePT 2 2) ==
  .setBasePT 2 2 .targetWhileSource
#guard equalSource == .setBasePT 0 0 .target .equalSource
#guard TriggeredAbility.resolution .onAttackSetOtherBasePT == equalSource

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := fixed } ==
  "target creature has base power and toughness 1/1 until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .setBasePT 5 5 .source } ==
  "this creature has base power and toughness 5/5 until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .setBasePT 0 2 .enchanted } ==
  "enchanted creature has base power and toughness 0/2 until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .setBasePT 3 1 .targetWhileSource } ==
  "that creature has base power and toughness 3/1 until end of turn"
#guard TriggeredAbility.resolutionPhrase { resolution := equalSource } ==
  "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .setBasePT 0 0 .source .equalSource } ==
  "set base power and toughness"
#guard TriggeredAbility.resolutionPhrase {
    targeting := .of .creatureYouControl
    resolution := .sequence
      [.attach .source .target, .setBasePT 2 2 .targetWhileSource] } ==
  "attach it to target creature you control. That creature has base power and toughness 2/2 until end of turn"

#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature has base power and toughness 1/1 until end of turn."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onSource (.setBasePT 5 5)))) ==
  "When this permanent enters, this creature has base power and toughness 5/5 until end of turn."
#guard TriggeredAbility.toNotation (.onEnterEnchanted (.setBasePT 0 2)) ==
  "When this Aura enters, enchanted creature has base power and toughness 0/2 until end of turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen (.setBasePT 2 2)) ==
  "When this Equipment enters, attach it to target creature you control. That creature has base power and toughness 2/2 until end of turn."
#guard TriggeredAbility.toNotation .onAttackSetOtherBasePT ==
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn."

end Mtg.Engine.SetBasePTTests
