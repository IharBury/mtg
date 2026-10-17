import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.untap`

Who is untapped is an `ObjectSelector`. The announced permanent, the source,
the enchanted creature, and the target while the source remains. Each
attacking creature. Any other selector untaps nothing. A stun counter is
removed instead of untapping (CR 122.1d).
-/

namespace Mtg.Engine.UntapTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature .untap))

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (ab : TriggeredAbility := onCreature) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets
    (resolutionOverride := some r)

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.setObject { a with attachedTo := some (pid g host) }

def mark (g : Game) (name : String) (tapped : Bool := true)
    (attacking : Bool := false) (stun : Nat := 0)
    (cantFrom : Option ObjectId := none) : Game :=
  let o := obj g name
  g.setObject { o with status := { o.status with
    tapped
    attacking
    stun
    cantUntapGrantedBy := match cantFrom with | some id => #[id] | none => #[] } }

def tapped (g : Game) (name : String) : Bool :=
  (obj g name).status.tapped

def stunOf (g : Game) (name : String) : Nat :=
  (obj g name).status.stun

def titan : CardDef := creature "Titan" ManaCost.empty #[] 4 4
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def scout : CardDef := creature "Scout" ManaCost.empty #[] 1 1
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def attackers : TriggeredAbility.TriggerResolution :=
  .untap .attackingCreatures

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature untaps. An opponent's creature does too. An
already untapped creature stays untapped. A stun counter is removed
instead. A creature that can't become untapped stays tapped. A land, a
player, a missing target, and a creature that has left are not untapped. -/
#guard
  let g0 := mark (mark board "Titan") "Bear"
  let g := step g0 .untap (targets := #[Target.permanent (pid g0 "Titan")])
  !tapped g "Titan" && tapped g "Bear" &&
    logContains g "Titan untaps"

#guard
  let g0 := mark board "Bear"
  let g := step g0 .untap (targets := #[Target.permanent (pid g0 "Bear")])
  !tapped g "Bear" && logContains g "Bear untaps"

#guard
  let g := step board .untap (targets := #[Target.permanent (pid board "Titan")])
  !tapped g "Titan" && logContains g "Titan is already untapped"

#guard
  let g0 := mark board "Titan" (stun := 2)
  let g := step g0 .untap (targets := #[Target.permanent (pid g0 "Titan")])
  tapped g "Titan" && stunOf g "Titan" == 1 &&
    logContains g "A stun counter is removed from Titan instead of untapping it"

#guard
  let g0 := mark board "Titan" (cantFrom := some (pid board "Bear"))
  let g := step g0 .untap (targets := #[Target.permanent (pid g0 "Titan")])
  tapped g "Titan" && logContains g "Titan can't become untapped"

#guard
  let g0 := addPermanent (mark board "Titan") land caster caster
  let g0 := mark g0 "Field"
  let g := step g0 .untap (targets := #[Target.permanent (pid g0 "Field")])
  tapped g "Titan" && tapped g "Field" &&
    logContains g "The target is no longer legal"

#guard
  let g0 := mark board "Titan"
  let g := step g0 .untap (targets := #[Target.player opp])
  tapped g "Titan" && logContains g "The target is no longer legal"

#guard
  let g := step (mark board "Titan") .untap
  tapped g "Titan" && logContains g "The target is no longer legal"

#guard
  let g0 := mark board "Titan"
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 .untap (targets := #[Target.permanent newId])
  logContains g "The target is no longer in play" &&
    !(logContains g "Titan untaps")

#guard (.untap : TriggeredAbility.TriggerResolution) == .untap .target

/- The source untaps. Another creature stays tapped. A missing source, and
a source that has left, untap nothing. -/
#guard
  let g0 := mark (mark board "Bear") "Titan"
  let g := step g0 (.untap .source) (some (pid g0 "Titan"))
  !tapped g "Titan" && tapped g "Bear" && logContains g "Titan untaps"

#guard
  let g := step (mark board "Titan") (.untap .source)
  tapped g "Titan" &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let g0 := mark board "Titan"
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.untap .source) (some newId)
  logContains g "Titan is no longer on the battlefield" &&
    !(logContains g "Titan untaps")

/- The enchanted creature untaps, including an opponent's. Nothing
enchanted, a missing host, and a missing source untap nothing. An Aura
that has left is reported. -/
#guard
  let g0 := attach
    (addPermanent (mark board "Titan") grasp caster caster) "Grasp" "Titan"
  let g := step g0 (.untap .enchanted) (some (pid g0 "Grasp"))
  !tapped g "Titan" && !tapped g "Grasp" && logContains g "Titan untaps"

#guard
  let g0 := attach
    (addPermanent (mark board "Bear") grasp caster caster) "Grasp" "Bear"
  let g := step g0 (.untap .enchanted) (some (pid g0 "Grasp"))
  !tapped g "Bear" && logContains g "Bear untaps"

#guard
  let g0 := addPermanent (mark board "Titan") grasp caster caster
  let g := step g0 (.untap .enchanted) (some (pid g0 "Grasp"))
  tapped g "Titan" && g.log == g0.log

#guard
  let g0 := attach
    (addPermanent (mark board "Titan") grasp caster caster) "Grasp" "Titan"
  let aura := obj g0 "Grasp"
  let g0 := g0.setObject { aura with attachedTo := some ⟨99999⟩ }
  let g := step g0 (.untap .enchanted) (some (pid g0 "Grasp"))
  tapped g "Titan" && g.log == g0.log

#guard
  let g := step (mark board "Titan") (.untap .enchanted)
  tapped g "Titan" && logContains g "The Aura is no longer in play"

#guard
  let g0 := attach
    (addPermanent (mark board "Titan") grasp caster caster) "Grasp" "Titan"
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.untap .enchanted) (some newId)
  tapped g "Titan" && logContains g "Grasp is no longer on the battlefield"

/- The target untaps only while the source remains. A source that has left
is silent. An illegal target is reported while the source is still there. -/
#guard
  let g0 := mark (mark board "Titan") "Bear"
  let g := step g0 (.untap (.target .whileSource))
    (some (pid g0 "Bear")) #[Target.permanent (pid g0 "Titan")]
  !tapped g "Titan" && tapped g "Bear" && logContains g "Titan untaps"

#guard
  let g0 := mark board "Titan"
  let id := pid g0 "Bear"
  let (g1, newId) := g0.move id (.graveyard opp) none
  let g := step g1 (.untap (.target .whileSource))
    (some newId) #[Target.permanent (pid g1 "Titan")]
  tapped g "Titan" && g.log == g1.log

#guard
  let g0 := mark board "Titan"
  let g := step g0 (.untap (.target .whileSource)) (some (pid g0 "Bear"))
  tapped g "Titan" && logContains g "The target is no longer legal"

#guard
  let g := step (mark board "Titan") (.untap (.target .whileSource))
  tapped g "Titan" && g.log == (mark board "Titan").log

/- Each attacking permanent untaps, including an opponent's creature and a
land. A creature that is not attacking stays tapped. A stun counter is
removed instead. A creature that can't become untapped stays tapped. An
already untapped attacker is unchanged. No attackers changes nothing. -/
#guard
  let g0 := mark (mark board "Titan" (attacking := true)) "Bear" (attacking := true)
  let g0 := addPermanent g0 scout caster caster
  let g0 := mark g0 "Scout"
  let g0 := addPermanent g0 land caster caster
  let g0 := mark g0 "Field" (attacking := true)
  let g := step g0 attackers
  !tapped g "Titan" && !tapped g "Bear" && !tapped g "Field" &&
    tapped g "Scout" && g.additionalCombatPhases == 0 &&
    logContains g "Titan untaps" && logContains g "Bear untaps" &&
    logContains g "Field untaps"

#guard
  let g0 := mark board "Titan" (attacking := true) (stun := 1)
  let g := step g0 attackers
  tapped g "Titan" && stunOf g "Titan" == 0 &&
    logContains g "A stun counter is removed from Titan instead of untapping it"

#guard
  let g0 := mark board "Titan" (attacking := true) (cantFrom := some (pid board "Bear"))
  let g := step g0 attackers
  tapped g "Titan" && logContains g "Titan can't become untapped"

#guard
  let g0 := mark board "Titan" false true
  let g := step g0 attackers
  !tapped g "Titan" && logContains g "Titan is already untapped"

#guard
  let g0 := mark board "Titan"
  let g := step g0 attackers
  tapped g "Titan" && g.log == g0.log

/- Untapping attackers and the extra combat are still one sequence. -/
#guard
  let g0 := mark (mark board "Titan" (attacking := true)) "Bear"
  let g := step g0 (.sequence [.untap .attackingCreatures, .additionalCombatPhase])
    (targets := #[Target.permanent (pid g0 "Bear")])
  !tapped g "Titan" && tapped g "Bear" && g.additionalCombatPhases == 1 &&
    logContains g "Attacking creatures untap. After this phase, there is an additional combat phase"

/- Any other selector untaps nothing. -/
#guard
  let g0 := mark board "Titan"
  let g := step g0 (.untap .humans) (targets := #[Target.permanent (pid g0 "Titan")])
  tapped g "Titan" && g.log == g0.log

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.TriggerResolution.ofPermanent .untap == .untap
#guard TriggeredAbility.TriggerResolution.ofSource .untap == .untap .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .untap == .untap .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .untap ==
  .untap (.target .whileSource)
#guard TriggeredAbility.resolution (.onAttackWithTotalPowerUntapExtraCombat 12) ==
  .sequence [.untap .attackingCreatures, .additionalCombatPhase]

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := .untap } ==
  "untap target creature"
#guard TriggeredAbility.resolutionPhrase { resolution := .untap .source } ==
  "untap this creature"
#guard TriggeredAbility.resolutionPhrase { resolution := .untap .enchanted } ==
  "untap enchanted creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .untap (.target .whileSource) } ==
  "untap that creature"
#guard TriggeredAbility.resolutionPhrase { resolution := attackers } ==
  "untap all attacking creatures"
#guard TriggeredAbility.resolutionPhrase { resolution := .untap .humans } ==
  "untap it"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .sequence [.untap .attackingCreatures, .additionalCombatPhase] } ==
  "untap all attacking creatures. After this phase, there is an additional combat phase"

#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, untap target creature."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onSource .untap))) ==
  "When this permanent enters, untap this creature."
#guard TriggeredAbility.toNotation (.onEnterEnchanted .untap) ==
  "When this Aura enters, untap enchanted creature."
#guard TriggeredAbility.toNotation (.onEnterAttachThen .untap) ==
  "When this Equipment enters, attach it to target creature you control. Untap that creature."
#guard TriggeredAbility.toNotation (.onAttackWithTotalPowerUntapExtraCombat 12) ==
  "Whenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase."

end Mtg.Engine.UntapTests
