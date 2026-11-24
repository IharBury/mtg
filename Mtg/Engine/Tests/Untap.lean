import Mtg.Engine.Tests.Builders
import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified untap instructions (`Instruction.untap` / `PermanentOp.setTapped`)

Target creature, source, enchanted creature, target while source remains,
each attacking creature, and untapping attackers plus an additional combat
phase all execute through `Game/Interpreter.lean`. A stun counter is removed
instead of untapping (CR 122.1d).
-/

namespace Mtg.Engine.UntapTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  TriggeredAbility.mkTrigger .thisEnters {
    targets := .creature
    body := Instruction.untap (.target 0)
  }

def stepEffect (g : Game) (e : Effect)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters e) sourceId targets

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.record (GameEvent.attached g.turnNumber (g.snapshot a) (pid g host) (cause := .gameRule .staticAbility))

def mark (g : Game) (name : String) (tapped : Bool := true)
    (attacking : Bool := false) (stun : Nat := 0)
    (cantFrom : Option ObjectId := none) : Game :=
  let o := obj g name
  let g := if stun > 0 then g.recordPutCounters o.id .stun stun else g
  let g := if attacking then g.markAttacking o.id else g
  let g := setTapped g o.id tapped
  match cantFrom with
  | some srcId => g.createEffect (.cantUntapWhileSource o.id srcId)
  | none => g

def tapped (g : Game) (name : String) : Bool :=
  (obj g name).status.tapped

def stunOf (g : Game) (name : String) : Nat :=
  (obj g name).status.stun

def titan : CardDef := creature "Titan" ManaCost.empty #[] 4 4
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def scout : CardDef := creature "Scout" ManaCost.empty #[] 1 1
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def untapTarget : Effect :=
  { targets := .creature, body := Instruction.untap (.target 0) }

def untapSource : Effect :=
  { body := Instruction.untap .this }

def untapEnchanted : Effect :=
  { body := Instruction.untap .attachedHost }

def untapWhileSource : Effect :=
  { targets := .creature
    body := Instruction.ifThen (.exists .this) (Instruction.untap (.target 0)) }

def untapAttackers : Effect :=
  { body := Instruction.untap (.inZones .battlefield (.combatRole .attacking)) }

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature untaps. An opponent's creature does too. An
already untapped creature stays untapped. A stun counter is removed
instead (CR 122.1d). A creature that can't become untapped stays tapped.
A land, a player, a missing target, and a creature that has left are not
untapped. -/
#guard
  let g0 := mark (mark board "Titan") "Bear"
  let g := stepEffect g0 untapTarget (targets := #[Target.permanent (pid g0 "Titan")])
  !tapped g "Titan" && tapped g "Bear" &&
    logContains g "Titan untaps"

#guard
  let g0 := mark board "Bear"
  let g := stepEffect g0 untapTarget (targets := #[Target.permanent (pid g0 "Bear")])
  !tapped g "Bear" && logContains g "Bear untaps"

#guard
  let g := stepEffect board untapTarget (targets := #[Target.permanent (pid board "Titan")])
  !tapped g "Titan" && logContains g "Titan is already untapped"

#guard
  let g0 := mark board "Titan" (stun := 2)
  let g := stepEffect g0 untapTarget (targets := #[Target.permanent (pid g0 "Titan")])
  tapped g "Titan" && stunOf g "Titan" == 1 &&
    logContains g "A stun counter is removed from Titan instead of untapping it"

#guard
  let g0 := mark board "Titan" (cantFrom := some (pid board "Bear"))
  let g := stepEffect g0 untapTarget (targets := #[Target.permanent (pid g0 "Titan")])
  tapped g "Titan" && logContains g "Titan can't become untapped"

#guard
  let g0 := addPermanent (mark board "Titan") land caster caster
  let g0 := mark g0 "Field"
  let g := stepEffect g0 untapTarget (targets := #[Target.permanent (pid g0 "Field")])
  tapped g "Titan" && tapped g "Field" &&
    logContains g "The target is no longer legal"

#guard
  let g0 := mark board "Titan"
  let g := stepEffect g0 untapTarget (targets := #[Target.player opp])
  tapped g "Titan" && logContains g "The target is no longer legal"

#guard
  let g := stepEffect (mark board "Titan") untapTarget
  tapped g "Titan"

#guard
  let g0 := mark board "Titan"
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := stepEffect g1 untapTarget (targets := #[Target.permanent newId])
  logContains g "The target is no longer in play" &&
    !(logContains g "Titan untaps")

/- The source untaps. Another creature stays tapped. A missing source, and
a source that has left, untap nothing. -/
#guard
  let g0 := mark (mark board "Bear") "Titan"
  let g := stepEffect g0 untapSource (some (pid g0 "Titan"))
  !tapped g "Titan" && tapped g "Bear" && logContains g "Titan untaps"

#guard
  let g := stepEffect (mark board "Titan") untapSource
  tapped g "Titan"

#guard
  let g0 := mark board "Titan"
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := stepEffect g1 untapSource (some newId)
  !(logContains g "Titan untaps")

/- The enchanted creature untaps, including an opponent's. Nothing
enchanted, a missing host, and a missing source untap nothing. -/
#guard
  let g0 := attach
    (addPermanent (mark board "Titan") grasp caster caster) "Grasp" "Titan"
  let g := stepEffect g0 untapEnchanted (some (pid g0 "Grasp"))
  !tapped g "Titan" && !tapped g "Grasp" && logContains g "Titan untaps"

#guard
  let g0 := attach
    (addPermanent (mark board "Bear") grasp caster caster) "Grasp" "Bear"
  let g := stepEffect g0 untapEnchanted (some (pid g0 "Grasp"))
  !tapped g "Bear" && logContains g "Bear untaps"

#guard
  let g0 := addPermanent (mark board "Titan") grasp caster caster
  let g := stepEffect g0 untapEnchanted (some (pid g0 "Grasp"))
  tapped g "Titan" && g.log == g0.log

#guard
  let g0 := attach
    (addPermanent (mark board "Titan") grasp caster caster) "Grasp" "Titan"
  let aura := obj g0 "Grasp"
  let g0 := g0.record (GameEvent.attached g0.turnNumber (g0.snapshot aura) ⟨99999⟩ (cause := .gameRule .staticAbility))
  let g := stepEffect g0 untapEnchanted (some (pid g0 "Grasp"))
  tapped g "Titan" && g.log == g0.log

#guard
  let g := stepEffect (mark board "Titan") untapEnchanted
  tapped g "Titan"

/- The target untaps only while the source remains. A source that has left
is silent. -/
#guard
  let g0 := mark (mark board "Titan") "Bear"
  let g := stepEffect g0 untapWhileSource
    (some (pid g0 "Bear")) #[Target.permanent (pid g0 "Titan")]
  !tapped g "Titan" && tapped g "Bear" && logContains g "Titan untaps"

#guard
  let g0 := mark board "Titan"
  let id := pid g0 "Bear"
  let (g1, newId) := g0.move id (.graveyard opp) none
  let g := stepEffect g1 untapWhileSource
    (some newId) #[Target.permanent (pid g1 "Titan")]
  tapped g "Titan" && g.log == g1.log

#guard
  let g := stepEffect (mark board "Titan") untapWhileSource
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
  let g := stepEffect g0 untapAttackers
  !tapped g "Titan" && !tapped g "Bear" && !tapped g "Field" &&
    tapped g "Scout" && g.additionalCombatPhases == 0 &&
    logContains g "Titan untaps" && logContains g "Bear untaps" &&
    logContains g "Field untaps"

#guard
  let g0 := mark board "Titan" (attacking := true) (stun := 1)
  let g := stepEffect g0 untapAttackers
  tapped g "Titan" && stunOf g "Titan" == 0 &&
    logContains g "A stun counter is removed from Titan instead of untapping it"

#guard
  let g0 := mark board "Titan" (attacking := true) (cantFrom := some (pid board "Bear"))
  let g := stepEffect g0 untapAttackers
  tapped g "Titan" && logContains g "Titan can't become untapped"

#guard
  let g0 := mark board "Titan" false true
  let g := stepEffect g0 untapAttackers
  !tapped g "Titan" && logContains g "Titan is already untapped"

#guard
  let g0 := mark board "Titan"
  let g := stepEffect g0 untapAttackers
  tapped g "Titan" && g.log == g0.log

/- Untapping attackers and the extra combat are one unified sequence. -/
#guard
  let g0 := mark (mark board "Titan" (attacking := true)) "Bear"
  let g := g0.applyTriggeredAbility caster (.onAttackWithTotalPowerUntapExtraCombat 12) none
    #[Target.permanent (pid g0 "Bear")]
  !tapped g "Titan" && tapped g "Bear" && g.additionalCombatPhases == 1 &&
    logContains g "Attacking creatures untap. After this phase, there is an additional combat phase"

/- Printed phrases and notations stay intact. -/
#guard (TriggeredAbility.onAttackWithTotalPowerUntapExtraCombat 12).effect.body ==
  Effect.triggerUntapAttackersExtraCombat.body
#guard TriggeredAbility.resolutionPhrase untapTarget == "untap target creature"
#guard TriggeredAbility.resolutionPhrase untapSource == "untap this creature"
#guard TriggeredAbility.resolutionPhrase untapEnchanted == "untap enchanted creature"
#guard TriggeredAbility.resolutionPhrase Effect.triggerUntapAttackersExtraCombat ==
  "untap all attacking creatures. After this phase, there is an additional combat phase"
#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, untap target creature."
#guard TriggeredAbility.toNotation (TriggeredAbility.mkTrigger .thisEnters untapSource) ==
  "When this permanent enters, untap this creature."
#guard TriggeredAbility.toNotation (.onEnterEnchanted Instruction.untap) ==
  "When this Aura enters, untap enchanted creature."
#guard TriggeredAbility.toNotation (.onEnterAttachThen Instruction.untap) ==
  "When this Equipment enters, attach it to target creature you control. Untap that creature."
#guard TriggeredAbility.toNotation (.onAttackWithTotalPowerUntapExtraCombat 12) ==
  "Whenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase."

end Mtg.Engine.UntapTests
