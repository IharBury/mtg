import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.cant`

The announced permanent, the source, the enchanted creature, and the target
while the source remains can't be blocked this turn. The announced permanent
can't become untapped for as long as you control the source. What it can't
do, and who can't, are one `ActionSelector`.
-/

namespace Mtg.Engine.CantTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature .cantBeBlocked))

def spider : TriggeredAbility :=
  .onEnter Effect.enterTapOppCantUntapWhileControl

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

def titan : CardDef := creature "Titan" ManaCost.empty #[] 4 4
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def unblockable : TriggeredAbility.TriggerResolution :=
  .cant .beBlocked

def frozen : TriggeredAbility.TriggerResolution :=
  .cant .untapWhileYouControl

def tapThenFrozen : TriggeredAbility.TriggerResolution :=
  .sequence [.tap .target, frozen]

def blocked (g : Game) (name : String) : Bool :=
  (obj g name).status.untilEotKeywords.cantBeBlocked

def grantedBy (g : Game) (name : String) : Array ObjectId :=
  (obj g name).status.cantUntapGrantedBy

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature can't be blocked this turn. An opponent's
creature can too. A land, a player, a missing target, and a creature that
has left are not affected. -/
#guard
  let g := step board unblockable (targets := #[Target.permanent (pid board "Titan")])
  blocked g "Titan" && !blocked g "Bear" &&
    logContains g "Titan can't be blocked this turn"

#guard
  let g := step board unblockable (targets := #[Target.permanent (pid board "Bear")])
  blocked g "Bear" && !blocked g "Titan" &&
    logContains g "Bear can't be blocked this turn"

#guard
  let g := step board unblockable
  !blocked g "Titan" && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 unblockable (targets := #[Target.permanent (pid g0 "Field")])
  !blocked g "Titan" && !(obj g "Field").status.untilEotKeywords.cantBeBlocked &&
    logContains g "The target is no longer legal"

#guard
  let g := step board unblockable (targets := #[Target.player opp])
  !blocked g "Titan" && logContains g "The target is no longer legal"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 unblockable (targets := #[Target.permanent newId])
  !(anyObj g "Titan").status.untilEotKeywords.cantBeBlocked &&
    logContains g "The target is no longer in play"

#guard (.cant .beBlocked : TriggeredAbility.TriggerResolution) ==
  .cant (.beBlocked .target)

/- The source can't be blocked. A missing source, and a source that has
left, are not affected. -/
#guard
  let g := step board (.cant (.beBlocked .source)) (some (pid board "Titan"))
  blocked g "Titan" && !blocked g "Bear" &&
    logContains g "Titan can't be blocked this turn"

#guard
  let g := step board (.cant (.beBlocked .source))
  !blocked g "Titan" &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.cant (.beBlocked .source)) (some newId)
  !(anyObj g "Titan").status.untilEotKeywords.cantBeBlocked &&
    logContains g "Titan is no longer on the battlefield"

/- The enchanted creature can't be blocked. Nothing enchanted is silent.
An Aura that has left is reported. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (.cant (.beBlocked .enchanted)) (some (pid g0 "Grasp"))
  blocked g "Titan" &&
    logContains g "Titan can't be blocked this turn"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.cant (.beBlocked .enchanted)) (some (pid g0 "Grasp"))
  !blocked g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.cant (.beBlocked .enchanted)) (some newId)
  !blocked g "Titan" && logContains g "Grasp is no longer on the battlefield"

#guard
  let g := step board (.cant (.beBlocked .enchanted))
  !blocked g "Titan" &&
    logContains g "The Aura is no longer in play"

/- The target can't be blocked only while the source remains.
A source that has left is silent. An illegal target is reported while
the source is still there. -/
#guard
  let g := step board (.cant (.beBlocked (.target .whileSource)))
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  blocked g "Titan" && !blocked g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (.cant (.beBlocked (.target .whileSource)))
    (some newId) #[Target.permanent (pid g0 "Titan")]
  !blocked g "Titan" && g.log == g0.log

#guard
  let g := step board (.cant (.beBlocked (.target .whileSource)))
    (some (pid board "Bear"))
  !blocked g "Titan" && logContains g "The target is no longer legal"

/- The announced opponent's creature can't become untapped while the
source remains on the battlefield. This step does not tap it. A creature
you control, a land, a player, a missing target, and a creature that has
left are left alone. -/
#guard
  let g := step board frozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")] (ab := spider)
  !(obj g "Bear").status.tapped && grantedBy g "Bear" == #[pid board "Titan"] &&
    g.hostCantBecomeUntapped (obj g "Bear") && grantedBy g "Titan" == #[]

#guard
  let g := step board frozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Titan")] (ab := spider)
  grantedBy g "Titan" == #[] && grantedBy g "Bear" == #[] &&
    logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land opp opp
  let g := step g0 frozen (some (pid g0 "Titan"))
    #[Target.permanent (pid g0 "Field")] (ab := spider)
  grantedBy g "Bear" == #[] &&
    (obj g "Field").status.cantUntapGrantedBy == #[] &&
    logContains g "The target is no longer legal"

#guard
  let g := step board frozen (some (pid board "Titan"))
    #[Target.player opp] (ab := spider)
  grantedBy g "Bear" == #[] && logContains g "The target is no longer legal"

#guard
  let g := step board frozen (targets := #[Target.permanent (pid board "Bear")])
    (ab := spider)
  grantedBy g "Bear" == #[⟨0⟩]

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 frozen (some (pid g0 "Titan"))
    #[Target.permanent newId] (ab := spider)
  (anyObj g "Bear").status.cantUntapGrantedBy == #[] &&
    logContains g "The target is no longer in play"

/- A source that has already left still records the restriction. It does
not apply while that object is off the battlefield. -/
#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 frozen (some newId) #[Target.permanent (pid g0 "Bear")]
    (ab := spider)
  (obj g "Bear").status.cantUntapGrantedBy == #[newId] &&
    !g.hostCantBecomeUntapped (obj g "Bear")

/- Moving the source off the battlefield ends the restriction. -/
#guard
  let g0 := step board frozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")] (ab := spider)
  let (g, _) := g0.move (pid g0 "Titan") (.graveyard caster) none
  (obj g "Bear").status.cantUntapGrantedBy == #[pid board "Titan"] &&
    !g.hostCantBecomeUntapped (obj g "Bear")

/- Tap, then that restriction, is the printed enter ability. -/
#guard
  let g := step board tapThenFrozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")] (ab := spider)
  (obj g "Bear").status.tapped && grantedBy g "Bear" == #[pid board "Titan"] &&
    g.hostCantBecomeUntapped (obj g "Bear") && !blocked g "Bear"

#guard
  let g := step board tapThenFrozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Titan")] (ab := spider)
  !(obj g "Titan").status.tapped && grantedBy g "Titan" == #[] &&
    logContains g "The target is no longer legal"

/- An opponent's source can't untap. A creature you control, and nothing
enchanted by that source, is left alone. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let bearId := pid g0 "Bear"
  let tgt := #[Target.permanent (pid g0 "Titan")]
  let yours := step g0 (.cant (.untapWhileYouControl .source)) sid tgt (ab := spider)
  let quiet := [
    step g0 (.cant (.untapWhileYouControl .enchanted)) sid tgt (ab := spider),
    step g0 (.cant (.untapWhileYouControl (.target .whileSource))) sid tgt (ab := spider)]
  grantedBy yours "Bear" == #[bearId] && grantedBy yours "Titan" == #[] &&
    quiet.all fun g =>
      !blocked g "Titan" && grantedBy g "Titan" == #[] &&
        grantedBy g "Bear" == #[] && g.log == g0.log

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.TriggerResolution.ofPermanent .cantBeBlocked ==
  unblockable
#guard TriggeredAbility.TriggerResolution.ofSource .cantBeBlocked ==
  .cant (.beBlocked .source)
#guard TriggeredAbility.TriggerResolution.ofEnchanted .cantBeBlocked ==
  .cant (.beBlocked .enchanted)
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .cantBeBlocked ==
  .cant (.beBlocked (.target .whileSource))
#guard (SharedTrigger.timing (.enter .tapOppCantUntapWhileControl)).resolution ==
  tapThenFrozen
#guard TriggeredAbility.resolution spider == tapThenFrozen

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := unblockable } ==
  "target creature can't be blocked this turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .cant (.beBlocked .source) } ==
  "this creature can't be blocked this turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .cant (.beBlocked .enchanted) } ==
  "enchanted creature can't be blocked this turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .cant (.beBlocked (.target .whileSource)) } ==
  "that creature can't be blocked this turn"
#guard TriggeredAbility.resolutionPhrase { resolution := frozen } ==
  "that creature can't become untapped for as long as you control this creature"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .oppCreature, resolution := tapThenFrozen } ==
  "tap target creature an opponent controls. That creature can't become untapped for as long as you control this creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .cant (.untapWhileYouControl .source) } == "can't"
#guard TriggeredAbility.resolutionPhrase {
    targeting := .of .creatureYouControl
    resolution := .sequence
      [.attach .source .target, .cant (.beBlocked (.target .whileSource))] } ==
  "attach it to target creature you control. That creature can't be blocked this turn"

#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature can't be blocked this turn."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onSource .cantBeBlocked))) ==
  "When this permanent enters, this creature can't be blocked this turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen .cantBeBlocked) ==
  "When this Equipment enters, attach it to target creature you control. That creature can't be blocked this turn."
#guard TriggeredAbility.toNotation spider ==
  "When this permanent enters, tap target creature an opponent controls. That creature can't become untapped for as long as you control this creature."

/- A recipient this effect does not name can't be blocked and changes nothing. -/
#guard TriggeredAbility.resolutionPhrase
    { resolution := .cant (.beBlocked .hand) } == "can't"
#guard
  let g := step board (.cant (.beBlocked .hand)) (some (pid board "Titan"))
  !blocked g "Titan" && g.log == board.log

end Mtg.Engine.CantTests
