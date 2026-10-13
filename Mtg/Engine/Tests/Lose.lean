import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.lose`

The announced permanent, the source, the enchanted creature, and the target
while the source remains lose indestructible until end of turn. The announced
permanent loses all abilities while the source remains. What is lost, and who
loses it, are arguments.
-/

namespace Mtg.Engine.LoseTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature .loseIndestructible))

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
  g.setObject { a with attachedTo := some (pid g host) }

def titan : CardDef :=
  creature "Titan" ManaCost.empty #[] 4 4 (keywords := Keyword.indestructible)
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def hawk : CardDef :=
  creature "Hawk" ManaCost.empty #[] 1 1 (keywords := Keyword.flying)
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""
def wasp : CardDef := creature "Wasp" ManaCost.empty #[] 1 1

def indestructible : TriggeredAbility.TriggerResolution :=
  .lose .indestructible

def abilities : TriggeredAbility.TriggerResolution :=
  .lose .allAbilities .targetIfPresent

def targetLose : TriggeredAbility.TriggerResolution :=
  .sequence [.tap .targetIfPresent, abilities]

def flagged (g : Game) (name : String) : Bool :=
  (obj g name).status.untilEotLosesIndestructible

def lostFlag (g : Game) (name : String) : Bool :=
  flagged g name && !g.hasIndestructible (obj g name)

def kept (g : Game) (name : String) : Bool :=
  !flagged g name && g.hasIndestructible (obj g name)

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature loses indestructible until end of turn, whether
or not it had the keyword. A counter is lost the same way. A land, a
missing target, and a creature that has left lose nothing. -/
#guard
  let g := step board indestructible (targets := #[Target.permanent (pid board "Titan")])
  lostFlag g "Titan" && !flagged g "Bear" &&
    logContains g "Titan loses indestructible until end of turn"

#guard
  let g := step board indestructible (targets := #[Target.permanent (pid board "Bear")])
  (obj g "Bear").status.untilEotLosesIndestructible &&
    !g.hasIndestructible (obj g "Bear") && kept g "Titan" &&
    logContains g "Bear loses indestructible until end of turn"

#guard
  let marked :=
    let o := obj board "Bear"
    board.setObject { o with status := { o.status with indestructibleCounters := 1 } }
  marked.hasIndestructible (obj marked "Bear") &&
    lostFlag (step marked indestructible
      (targets := #[Target.permanent (pid marked "Bear")])) "Bear"

#guard
  let g := step board indestructible
  kept g "Titan" && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 indestructible (targets := #[Target.permanent (pid g0 "Field")])
  kept g "Titan" && !(obj g "Field").status.untilEotLosesIndestructible &&
    logContains g "The target is no longer legal"

#guard
  let g := step board indestructible (targets := #[Target.player opp])
  kept g "Titan" && logContains g "The target is no longer legal"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 indestructible (targets := #[Target.permanent newId])
  !(anyObj g "Titan").status.untilEotLosesIndestructible &&
    logContains g "The target is no longer in play"

#guard (.lose .indestructible : TriggeredAbility.TriggerResolution) ==
  .lose .indestructible .target

/- The source loses indestructible. A missing source, and a source that
has left, lose nothing. -/
#guard
  let g := step board (.lose .indestructible .source) (some (pid board "Titan"))
  lostFlag g "Titan" && !flagged g "Bear" &&
    logContains g "Titan loses indestructible until end of turn"

#guard
  let g := step board (.lose .indestructible .source)
  kept g "Titan" &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.lose .indestructible .source) (some newId)
  !(anyObj g "Titan").status.untilEotLosesIndestructible &&
    logContains g "Titan is no longer on the battlefield"

/- The enchanted creature loses indestructible. Nothing enchanted is
silent. An Aura that has left is reported. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (.lose .indestructible .enchanted) (some (pid g0 "Grasp"))
  lostFlag g "Titan" &&
    logContains g "Titan loses indestructible until end of turn"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.lose .indestructible .enchanted) (some (pid g0 "Grasp"))
  kept g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.lose .indestructible .enchanted) (some newId)
  kept g "Titan" && logContains g "Grasp is no longer on the battlefield"

#guard
  let g := step board (.lose .indestructible .enchanted)
  kept g "Titan" &&
    logContains g "The Aura is no longer in play"

/- The target loses indestructible only while the source remains.
A source that has left is silent. An illegal target is reported while
the source is still there. -/
#guard
  let g := step board (.lose .indestructible .targetWhileSource)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  lostFlag g "Titan" && !flagged g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (.lose .indestructible .targetWhileSource)
    (some newId) #[Target.permanent (pid g0 "Titan")]
  kept g "Titan" && g.log == g0.log

#guard
  let g := step board (.lose .indestructible .targetWhileSource)
    (some (pid board "Bear"))
  kept g "Titan" && logContains g "The target is no longer legal"

/- The announced permanent loses all abilities while the source remains.
It is not tapped by this step. A missing target loses nothing. A source
that has left leaves the creature able. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 abilities (some (pid g0 "Wasp")) #[Target.permanent (pid g0 "Hawk")]
  !(obj g "Hawk").status.tapped && !g.hasFlying (obj g "Hawk") &&
    (obj g "Hawk").status.losesAbilitiesGrantedBy == #[pid g0 "Wasp"]

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 abilities (some (pid g0 "Wasp"))
  g.hasFlying (obj g "Hawk") &&
    (obj g "Hawk").status.losesAbilitiesGrantedBy.isEmpty && g.log == g0.log

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 abilities (some (pid g0 "Wasp")) #[Target.player opp]
  g.hasFlying (obj g "Hawk") && g.log == g0.log

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let hawkId := pid g0 "Hawk"
  let (g1, newHawk) := g0.move hawkId (.graveyard caster) none
  let g := step g1 abilities (some (pid g1 "Wasp")) #[Target.permanent newHawk]
  g.hasFlying (anyObj g "Hawk") &&
    (anyObj g "Hawk").status.losesAbilitiesGrantedBy.isEmpty && g.log == g1.log

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let waspId := pid g0 "Wasp"
  let (g1, _) := g0.move waspId (.graveyard caster) none
  let g := step g1 abilities (some waspId) #[Target.permanent (pid g1 "Hawk")]
  g.hasFlying (obj g "Hawk") &&
    (obj g "Hawk").status.losesAbilitiesGrantedBy.isEmpty &&
    logContains g "keeps its abilities"

/- Tap, then that loss, is the printed enter ability. The source leaving
before it resolves still taps and leaves the abilities. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 targetLose (some (pid g0 "Wasp")) #[Target.permanent (pid g0 "Hawk")]
    (ab := .onEnter Effect.enterTapLoseAbilitiesWhileSource)
  (obj g "Hawk").status.tapped && !g.hasFlying (obj g "Hawk") &&
    (obj g "Hawk").status.losesAbilitiesGrantedBy == #[pid g0 "Wasp"]

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let waspId := pid g0 "Wasp"
  let (g1, _) := g0.move waspId (.graveyard caster) none
  let g := step g1 targetLose (some waspId) #[Target.permanent (pid g1 "Hawk")]
    (ab := .onEnter Effect.enterTapLoseAbilitiesWhileSource)
  (obj g "Hawk").status.tapped && g.hasFlying (obj g "Hawk") &&
    logContains g "keeps its abilities"

/- The other combinations lose nothing. -/
#guard
  let g0 := addPermanent (addPermanent board grasp caster caster) hawk caster caster
  let g0 := attach g0 "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let tgt := #[Target.permanent (pid g0 "Titan")]
  let crossed := [
    step g0 (.lose .allAbilities) sid tgt,
    step g0 (.lose .allAbilities .source) sid tgt,
    step g0 (.lose .allAbilities .enchanted) sid tgt,
    step g0 (.lose .allAbilities .targetWhileSource) sid tgt,
    step g0 (.lose .indestructible .targetIfPresent) sid tgt]
  crossed.all fun g =>
    kept g "Titan" && g.hasFlying (obj g "Hawk") &&
      (obj g "Hawk").status.losesAbilitiesGrantedBy.isEmpty && g.log == g0.log

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.TriggerResolution.ofPermanent .loseIndestructible ==
  indestructible
#guard TriggeredAbility.TriggerResolution.ofSource .loseIndestructible ==
  .lose .indestructible .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .loseIndestructible ==
  .lose .indestructible .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .loseIndestructible ==
  .lose .indestructible .targetWhileSource
#guard (SharedTrigger.timing (.enter .tapLoseAbilitiesWhileSource)).resolution ==
  targetLose
#guard TriggeredAbility.resolution (.onEnter Effect.enterTapLoseAbilitiesWhileSource) ==
  targetLose

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := indestructible } ==
  "target creature loses indestructible until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .lose .indestructible .source } ==
  "this creature loses indestructible until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .lose .indestructible .enchanted } ==
  "enchanted creature loses indestructible until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .lose .indestructible .targetWhileSource } ==
  "that creature loses indestructible until end of turn"
#guard TriggeredAbility.resolutionPhrase { resolution := abilities } ==
  "it loses all abilities for as long as this remains on the battlefield"
#guard TriggeredAbility.resolutionPhrase { resolution := targetLose } ==
  "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .lose .allAbilities } == "lose"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .lose .indestructible .targetIfPresent } == "lose"
#guard TriggeredAbility.resolutionPhrase {
    targeting := .of .creatureYouControl
    resolution := .sequence
      [.attach .source .target, .lose .indestructible .targetWhileSource] } ==
  "attach it to target creature you control. That creature loses indestructible until end of turn"

#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature loses indestructible until end of turn."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onSource .loseIndestructible))) ==
  "When this permanent enters, this creature loses indestructible until end of turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen .loseIndestructible) ==
  "When this Equipment enters, attach it to target creature you control. That creature loses indestructible until end of turn."
#guard TriggeredAbility.toNotation (.onEnter Effect.enterTapLoseAbilitiesWhileSource) ==
  "When this permanent enters, tap up to one target creature. It loses all abilities for as long as this remains on the battlefield."

end Mtg.Engine.LoseTests
