import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified continuous restrictions (`cantBeBlocked` / `cantBecomeUntapped`)

The announced permanent, the source, the enchanted creature, and the target
while the source remains can't be blocked this turn. The announced permanent
can't become untapped for as long as you control the source.
-/

namespace Mtg.Engine.CantTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def cantBeBlockedInstr (obj : ObjectExpr) : Instruction :=
  .installEffect (.applyContinuous .untilEndOfTurn obj (.applyRule (.combat (.cantBeBlocked .self))))

def cantUntapWhileControlInstr (obj : ObjectExpr) : Instruction :=
  .installEffect (.applyContinuous (.whileOnBattlefield .this) obj
    (.applyRule (.game (.cantBecomeUntapped .self))))

def onCreature : TriggeredAbility :=
  TriggeredAbility.mkTrigger .thisEnters { targeting := .of .creature, body := cantBeBlockedInstr (.target 0) }

def spider : TriggeredAbility :=
  .onEnter Effect.enterTapOppCantUntapWhileControl

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
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def unblockable : Instruction :=
  cantBeBlockedInstr (.target 0)

def frozen : Instruction :=
  cantUntapWhileControlInstr (.target 0)

def tapThenFrozen : Instruction :=
  Effect.enterTapOppCantUntapWhileControl.body

def blocked (g : Game) (name : String) : Bool :=
  g.hasCantBeBlocked (obj g name)

def grantedBy (g : Game) (name : String) : Array ObjectId :=
  g.cantUntapGrantedBy (obj g name)

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced creature can't be blocked this turn. An opponent's
creature can too. A land, a player, a missing target, and a creature that
has left are not affected. -/
#guard
  let g := step board unblockable (targets := #[Target.permanent (pid board "Titan")])
  blocked g "Titan" && !blocked g "Bear"

#guard
  let g := step board unblockable (targets := #[Target.permanent (pid board "Bear")])
  blocked g "Bear" && !blocked g "Titan"

#guard
  let g := step board unblockable
  !blocked g "Titan"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 unblockable (targets := #[Target.permanent (pid g0 "Field")])
  !blocked g "Titan" && !g.hasCantBeBlocked (obj g "Field")

#guard
  let g := step board unblockable (targets := #[Target.player opp])
  !blocked g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 unblockable (targets := #[Target.permanent newId])
  !g.hasCantBeBlocked (anyObj g "Titan")

/- The source can't be blocked. A missing source, and a source that has
left, are not affected. -/
#guard
  let g := step board (cantBeBlockedInstr .this) (some (pid board "Titan")) (spec := .none)
  blocked g "Titan" && !blocked g "Bear"

#guard
  let g := step board (cantBeBlockedInstr .this) (spec := .none)
  !blocked g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (cantBeBlockedInstr .this) (some newId) (spec := .none)
  !g.hasCantBeBlocked (anyObj g "Titan")

/- The enchanted creature can't be blocked. Nothing enchanted is silent. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (cantBeBlockedInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  blocked g "Titan"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (cantBeBlockedInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  !blocked g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (cantBeBlockedInstr .attachedHost) (some newId) (spec := .none)
  !blocked g "Titan"

/- The target can't be blocked only while the source remains.
A source that has left is silent. -/
def whileSourceUnblockable : Instruction :=
  Instruction.ifThen (.exists .this) unblockable

#guard
  let g := step board whileSourceUnblockable
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  blocked g "Titan" && !blocked g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 whileSourceUnblockable
    (some newId) #[Target.permanent (pid g0 "Titan")]
  !blocked g "Titan" && g.log == g0.log

/- The announced opponent's creature can't become untapped while the
source remains on the battlefield. This step does not tap it. A creature
you control, a land, a player, a missing target, and a creature that has
left are left alone. -/
#guard
  let g := step board frozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")] (spec := .oppCreature)
  !(obj g "Bear").status.tapped && grantedBy g "Bear" == #[pid board "Titan"] &&
    g.hostCantBecomeUntapped (obj g "Bear") && grantedBy g "Titan" == #[]

#guard
  let g := step board frozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Titan")] (spec := .oppCreature)
  grantedBy g "Titan" == #[] && grantedBy g "Bear" == #[]

#guard
  let g0 := addPermanent board land opp opp
  let g := step g0 frozen (some (pid g0 "Titan"))
    #[Target.permanent (pid g0 "Field")] (spec := .oppCreature)
  grantedBy g "Bear" == #[] &&
    g.cantUntapGrantedBy (obj g "Field") == #[]

#guard
  let g := step board frozen (some (pid board "Titan"))
    #[Target.player opp] (spec := .oppCreature)
  grantedBy g "Bear" == #[]

#guard
  let g := step board frozen (targets := #[Target.permanent (pid board "Bear")])
    (spec := .oppCreature)
  grantedBy g "Bear" == #[] && !g.hostCantBecomeUntapped (obj g "Bear")

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 frozen (some (pid g0 "Titan"))
    #[Target.permanent newId] (spec := .oppCreature)
  g.cantUntapGrantedBy (anyObj g "Bear") == #[]

/- CR 611.2b: if the source has already left before the effect would first be
created, a `.whileOnBattlefield` continuous effect does not start at all. -/
#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 frozen (some newId) #[Target.permanent (pid g0 "Bear")]
    (spec := .oppCreature)
  g.cantUntapGrantedBy (obj g "Bear") == #[] &&
    !g.hostCantBecomeUntapped (obj g "Bear")

/- Moving the source off the battlefield ends the restriction. -/
#guard
  let g0 := step board frozen (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")] (spec := .oppCreature)
  let (g, _) := g0.move (pid g0 "Titan") (.graveyard caster) none
  g.cantUntapGrantedBy (obj g "Bear") == #[] &&
    !g.hostCantBecomeUntapped (obj g "Bear")

/- Tap, then that restriction, is the printed enter ability. -/
#guard
  let g := board.applyTriggeredAbility caster spider (some (pid board "Titan"))
    #[Target.permanent (pid board "Bear")]
  (obj g "Bear").status.tapped && grantedBy g "Bear" == #[pid board "Titan"] &&
    g.hostCantBecomeUntapped (obj g "Bear") && !blocked g "Bear"

#guard
  let g := board.applyTriggeredAbility caster spider (some (pid board "Titan"))
    #[Target.permanent (pid board "Titan")]
  !(obj g "Titan").status.tapped && grantedBy g "Titan" == #[]

/- Printed phrases stay with the combination that produces them. -/
#guard spider.effect.body == tapThenFrozen
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, body := unblockable } ==
  "target creature can't be blocked this turn"
#guard TriggeredAbility.resolutionPhrase
    { body := cantBeBlockedInstr .this } ==
  "this creature can't be blocked this turn"
#guard TriggeredAbility.resolutionPhrase
    { body := cantBeBlockedInstr .attachedHost } ==
  "enchanted creature can't be blocked this turn"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .oppCreature, body := tapThenFrozen } ==
  "tap target creature an opponent controls. That creature can't become untapped for as long as you control this creature"
#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature can't be blocked this turn."
#guard TriggeredAbility.toNotation
    (TriggeredAbility.mkTrigger .thisEnters { body := cantBeBlockedInstr .this }) ==
  "When this permanent enters, this creature can't be blocked this turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen Instruction.cantBeBlocked) ==
  "When this Equipment enters, attach it to target creature you control. That creature can't be blocked this turn."
#guard TriggeredAbility.toNotation spider ==
  "When this permanent enters, tap target creature an opponent controls. That creature can't become untapped for as long as you control this creature."

/- A hand-zone object expression changes nothing on battlefield creatures. -/
#guard
  let g := step board (cantBeBlockedInstr (.inZones (.handOf .you) .anyObject))
    (some (pid board "Titan")) (spec := .none)
  !blocked g "Titan"

end Mtg.Engine.CantTests
