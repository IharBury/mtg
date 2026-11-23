import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified set-base-P/T instructions (`Instruction.setBasePT` / `ContinuousModification.setBasePT`)

Target creature, source, enchanted creature, target while source remains,
another target creature copying this creature's power and toughness (including
Layer 7a CDA, Layer 7c counters, pumps, and last-known values), and creatures
you control all execute through `Game/Interpreter.lean`.
-/

namespace Mtg.Engine.SetBasePTTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  TriggeredAbility.mkTrigger .thisEnters {
    targeting := .of .creature
    body := Instruction.setBasePTFixed (.target 0) 1 1
  }

def stepEffect (g : Game) (e : Effect)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters e) sourceId targets
    (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)

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
def ogre : CardDef := creature "Ogre" ManaCost.empty #[] 3 3
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def fixedTarget : Effect :=
  { targeting := .of .creature, body := Instruction.setBasePTFixed (.target 0) 1 1 }

def fixedSource : Effect :=
  { body := Instruction.setBasePTFixed .this 5 5 }

def fixedEnchanted : Effect :=
  { body := Instruction.setBasePTFixed .attachedHost 0 2 }

def fixedWhileSource : Effect :=
  { targeting := .of .creature
    body := Instruction.ifThen (.exists .this) (Instruction.setBasePTFixed (.target 0) 3 1) }

def fixedYours : Effect :=
  { body := Instruction.setBasePTFixed
      (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 1 }

def base (g : Game) (name : String) : Option (Int × Int) :=
  g.setBasePT (obj g name)

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature's base power and toughness become the fixed
values. Another creature is unchanged. A missing target, a land, a player,
and a creature that has left are not set. -/
#guard
  let g := stepEffect board fixedTarget (targets := #[Target.permanent (pid board "Titan")])
  base g "Titan" == some (1, 1) && g.basePower (obj g "Titan") == 1 &&
    g.baseToughness (obj g "Titan") == 1 && g.power (obj g "Titan") == 1 &&
    base g "Bear" == none &&
    logContains g "Titan has base power and toughness 1/1 until end of turn"

#guard
  let o := obj board "Bear"
  let marked := board.recordPutCounters o.id .plusOnePlusOne 1
  let g := stepEffect marked fixedTarget (targets := #[Target.permanent (pid marked "Bear")])
  base g "Bear" == some (1, 1) && g.basePower (obj g "Bear") == 1 &&
    g.power (obj g "Bear") == 2 &&
    (obj g "Bear").status.plusOnePlusOne == 1

#guard
  let g := stepEffect board fixedTarget
  base g "Titan" == none

#guard
  let g0 := addPermanent board land caster caster
  let g := stepEffect g0 fixedTarget (targets := #[Target.permanent (pid g0 "Field")])
  base g "Titan" == none && base g "Field" == none &&
    logContains g "The target is no longer legal"

#guard
  let g := stepEffect board fixedTarget (targets := #[Target.player opp])
  base g "Titan" == none && logContains g "The target is no longer legal"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := stepEffect g0 fixedTarget (targets := #[Target.permanent newId])
  g.setBasePT (anyObj g "Titan") == none &&
    logContains g "The target is no longer in play"

/- The source gets the fixed base. A missing source, and a source that has
left, are not set. -/
#guard
  let g := stepEffect board fixedSource (some (pid board "Titan"))
  base g "Titan" == some (5, 5) && base g "Bear" == none &&
    logContains g "Titan has base power and toughness 5/5 until end of turn"

#guard
  let g := stepEffect board fixedSource
  base g "Titan" == none &&
    logContains g "The source is no longer in play"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := stepEffect g0 fixedSource (some newId)
  g.setBasePT (anyObj g "Titan") == none

/- The enchanted creature gets the fixed base. Nothing enchanted is silent. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := stepEffect g0 fixedEnchanted (some (pid g0 "Grasp"))
  base g "Titan" == some (0, 2) &&
    logContains g "Titan has base power and toughness 0/2 until end of turn"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := stepEffect g0 fixedEnchanted (some (pid g0 "Grasp"))
  base g "Titan" == none && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := stepEffect g1 fixedEnchanted (some newId)
  base g "Titan" == none

/- The target gets the fixed base only while the source remains. A source
that has left leaves the target unchanged. -/
#guard
  let g := stepEffect board fixedWhileSource
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  base g "Titan" == some (3, 1) && base g "Bear" == none

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := stepEffect g0 fixedWhileSource
    (some newId) #[Target.permanent (pid g0 "Titan")]
  base g "Titan" == none && g.log == g0.log

/- Another target creature's base becomes this creature's power and
toughness, including a pump, and including last-known values after the
source has left. The source itself, an opponent's creature, and a
creature that has left are not set. -/
#guard
  let g0 := addPermanent board ogre caster caster
  let g := g0.applyTriggeredAbility caster .onAttackSetOtherBasePT (some (pid g0 "Titan"))
    #[Target.permanent (pid g0 "Ogre")]
  base g "Ogre" == some (4, 4) && g.power (obj g "Ogre") == 4 &&
    base g "Titan" == none &&
    logContains g "Ogre's base power and toughness become 4/4 until end of turn"

#guard
  let g0 := addPermanent board ogre caster caster
  let g0 := g0.pumpPermanent (obj g0 "Titan") 2 1
  let g := g0.applyTriggeredAbility caster .onAttackSetOtherBasePT (some (pid g0 "Titan"))
    #[Target.permanent (pid g0 "Ogre")]
  g.power (obj g "Titan") == 6 && base g "Ogre" == some (6, 5) &&
    logContains g "Ogre's base power and toughness become 6/5 until end of turn"

#guard
  let g := board.applyTriggeredAbility caster .onAttackSetOtherBasePT (some (pid board "Titan")) #[]
  base g "Bear" == none && base g "Titan" == none

#guard
  let g := board.applyTriggeredAbility caster .onAttackSetOtherBasePT (some (pid board "Titan"))
    #[Target.permanent (pid board "Titan")]
  base g "Titan" == none && logContains g "The target is no longer legal"

#guard
  let g := board.applyTriggeredAbility caster .onAttackSetOtherBasePT (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")]
  base g "Bear" == none && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board ogre caster caster
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := g1.applyTriggeredAbility caster .onAttackSetOtherBasePT (some newId)
    #[Target.permanent (pid g1 "Ogre")]
    (lastKnownPower := some 4) (lastKnownToughness := some 4)
  base g "Ogre" == some (4, 4)

#guard
  let g0 := addPermanent board ogre caster caster
  let id := pid g0 "Titan"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let gLki := g1.applyTriggeredAbility caster .onAttackSetOtherBasePT (some id)
    #[Target.permanent (pid g1 "Ogre")]
  let gSnap := g1.applyTriggeredAbility caster .onAttackSetOtherBasePT (some newId)
    #[Target.permanent (pid g1 "Ogre")]
  let gNone := g1.applyTriggeredAbility caster .onAttackSetOtherBasePT none
    #[Target.permanent (pid g1 "Ogre")]
  base gLki "Ogre" == some (4, 4) &&
    base gSnap "Ogre" == some (4, 4) &&
    base gNone "Ogre" == some (0, 0)

#guard
  let g0 := addPermanent board ogre caster caster
  let id := pid g0 "Ogre"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := g1.applyTriggeredAbility caster .onAttackSetOtherBasePT (some (pid g1 "Titan"))
    #[Target.permanent newId]
  logContains g "The target is no longer in play"

/- Creatures the controller controls take a fixed base. -/
#guard
  let g0 := addPermanent board ogre caster caster
  let onYours := stepEffect g0 fixedYours (some (pid g0 "Titan"))
  base onYours "Titan" == some (1, 1) && base onYours "Ogre" == some (1, 1) &&
    base onYours "Bear" == none

/- Printed phrases and notations stay intact. -/
#guard TriggeredAbility.onAttackSetOtherBasePT.effect.body == Effect.triggerSetOtherBasePT.body
#guard TriggeredAbility.resolutionPhrase fixedTarget ==
  "target creature has base power and toughness 1/1 until end of turn"
#guard TriggeredAbility.resolutionPhrase fixedSource ==
  "this creature has base power and toughness 5/5 until end of turn"
#guard TriggeredAbility.resolutionPhrase fixedEnchanted ==
  "enchanted creature has base power and toughness 0/2 until end of turn"
#guard TriggeredAbility.resolutionPhrase Effect.triggerSetOtherBasePT ==
  "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature has base power and toughness 1/1 until end of turn."
#guard TriggeredAbility.toNotation (TriggeredAbility.mkTrigger .thisEnters fixedSource) ==
  "When this permanent enters, this creature has base power and toughness 5/5 until end of turn."
#guard TriggeredAbility.toNotation (.onEnterEnchanted (fun o => Instruction.setBasePTFixed o 0 2)) ==
  "When this Aura enters, enchanted creature has base power and toughness 0/2 until end of turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen (fun o => Instruction.setBasePTFixed o 2 2)) ==
  "When this Equipment enters, attach it to target creature you control. That creature has base power and toughness 2/2 until end of turn."
#guard TriggeredAbility.toNotation .onAttackSetOtherBasePT ==
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn."

/- Layer-derived power and toughness (including Layer 7a CDA and Layer 7c
counters) feed `Effect.triggerSetOtherBasePT`, and `attach` snapshots the
Aura's characteristics on `GameEvent.attached`. -/
#guard
  let cdaAvatar : CardDef := {
    name := "Lands Source"
    types := #[.creature]
    subtypes := #["Avatar"]
    staticAbilities := #[.powerToughnessEqualLandsYouControl]
  }
  let g0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw land caster caster) land caster caster) cdaAvatar caster caster) ogre caster caster
  let srcId := pid g0 "Lands Source"
  let g1 := g0.recordPutCounters srcId .plusOnePlusOne 1
  let g2 := g1.applyTriggeredAbility caster .onAttackSetOtherBasePT (some srcId)
    #[Target.permanent (pid g1 "Ogre")]
  let gAtt := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let attSnapOk := gAtt.events.any fun e =>
    match e.change with
    | .rules (.permanent (.attached eo hid _)) =>
      eo.name == "Grasp" && eo.types.contains .enchantment && hid == pid gAtt "Titan"
    | _ => false
  g1.power (obj g1 "Lands Source") == 3 &&
    g1.toughness (obj g1 "Lands Source") == 3 &&
    base g2 "Ogre" == some (3, 3) &&
    attSnapOk

end Mtg.Engine.SetBasePTTests
