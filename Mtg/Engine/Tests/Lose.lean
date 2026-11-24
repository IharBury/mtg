import Mtg.Engine.Tests.Builders
import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified lose-ability continuous effects (`loseKeywords` / `loseAllAbilities`)

The announced permanent, the source, the enchanted creature, and the target
while the source remains lose indestructible until end of turn. The announced
permanent loses all abilities while the source remains.
-/

namespace Mtg.Engine.LoseTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def loseIndestructibleInstr (obj : ObjectExpr) : Instruction :=
  .installEffect (.applyContinuous .untilEndOfTurn obj (.loseKeywords #[Keyword.indestructible]))

def loseAllWhileSourceInstr (obj : ObjectExpr) : Instruction :=
  Instruction.ifThen (.exists .this)
    (.installEffect (.applyContinuous (.whileOnBattlefield .this) obj .loseAllAbilities))

def onCreature : TriggeredAbility :=
  TriggeredAbility.mkTrigger .thisEnters { targets := .creature, body := loseIndestructibleInstr (.target 0) }

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

def titan : CardDef :=
  creature "Titan" ManaCost.empty #[] 4 4 (keywords := #[Keyword.indestructible])
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def hawk : CardDef :=
  creature "Hawk" ManaCost.empty #[] 1 1 (keywords := #[Keyword.flying])
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""
def wasp : CardDef := creature "Wasp" ManaCost.empty #[] 1 1

def indestructible : Instruction :=
  loseIndestructibleInstr (.target 0)

def abilities : Instruction :=
  loseAllWhileSourceInstr (.target 0)

def flagged (g : Game) (name : String) : Bool :=
  g.untilEotLosesIndestructible (obj g name)

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
  lostFlag g "Titan" && !flagged g "Bear"

#guard
  let g := step board indestructible (targets := #[Target.permanent (pid board "Bear")])
  g.untilEotLosesIndestructible (obj g "Bear") &&
    !g.hasIndestructible (obj g "Bear") && kept g "Titan"

#guard
  let marked :=
    let o := obj board "Bear"
    board.recordPutCounters o.id .indestructible 1
  marked.hasIndestructible (obj marked "Bear") &&
    lostFlag (step marked indestructible
      (targets := #[Target.permanent (pid marked "Bear")])) "Bear"

#guard
  let g := step board indestructible
  kept g "Titan"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 indestructible (targets := #[Target.permanent (pid g0 "Field")])
  kept g "Titan" && !g.untilEotLosesIndestructible (obj g "Field")

#guard
  let g := step board indestructible (targets := #[Target.player opp])
  kept g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 indestructible (targets := #[Target.permanent newId])
  !g.untilEotLosesIndestructible (anyObj g "Titan")

/- The source loses indestructible. A missing source, and a source that
has left, lose nothing. -/
#guard
  let g := step board (loseIndestructibleInstr .this) (some (pid board "Titan")) (spec := .none)
  lostFlag g "Titan" && !flagged g "Bear"

#guard
  let g := step board (loseIndestructibleInstr .this) (spec := .none)
  kept g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (loseIndestructibleInstr .this) (some newId) (spec := .none)
  !g.untilEotLosesIndestructible (anyObj g "Titan")

/- The enchanted creature loses indestructible. Nothing enchanted is silent. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (loseIndestructibleInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  lostFlag g "Titan"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (loseIndestructibleInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  kept g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (loseIndestructibleInstr .attachedHost) (some newId) (spec := .none)
  kept g "Titan"

/- The target loses indestructible only while the source remains. -/
#guard
  let g := step board (Instruction.ifThen (.exists .this) indestructible)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  lostFlag g "Titan" && !flagged g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (Instruction.ifThen (.exists .this) indestructible)
    (some newId) #[Target.permanent (pid g0 "Titan")]
  kept g "Titan" && g.log == g0.log

/- The announced permanent loses all abilities while the source remains.
It is not tapped by this step. A missing target or departed source leaves the creature able. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 abilities (some (pid g0 "Wasp")) #[Target.permanent (pid g0 "Hawk")]
  !(obj g "Hawk").status.tapped && !g.hasFlying (obj g "Hawk") &&
    g.losesAbilitiesGrantedBy (obj g "Hawk") == #[pid g0 "Wasp"]

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 abilities (some (pid g0 "Wasp"))
  g.hasFlying (obj g "Hawk") &&
    (g.losesAbilitiesGrantedBy (obj g "Hawk")).isEmpty

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let waspId := pid g0 "Wasp"
  let (g1, _) := g0.move waspId (.graveyard caster) none
  let g := step g1 abilities (some waspId) #[Target.permanent (pid g1 "Hawk")]
  g.hasFlying (obj g "Hawk") &&
    (g.losesAbilitiesGrantedBy (obj g "Hawk")).isEmpty

/- Tap, then lose all abilities while source remains, is the printed enter ability.
The source leaving before it resolves still taps and leaves the abilities. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := g0.applyTriggeredAbility caster (.onEnter Effect.enterTapLoseAbilitiesWhileSource)
    (some (pid g0 "Wasp")) #[Target.permanent (pid g0 "Hawk")]
  (obj g "Hawk").status.tapped && !g.hasFlying (obj g "Hawk") &&
    g.losesAbilitiesGrantedBy (obj g "Hawk") == #[pid g0 "Wasp"]

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let waspId := pid g0 "Wasp"
  let (g1, _) := g0.move waspId (.graveyard caster) none
  let g := g1.applyTriggeredAbility caster (.onEnter Effect.enterTapLoseAbilitiesWhileSource)
    (some waspId) #[Target.permanent (pid g1 "Hawk")]
  (obj g "Hawk").status.tapped && g.hasFlying (obj g "Hawk")

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.resolutionPhrase
    { targets := .creature, body := indestructible } ==
  "target creature loses indestructible until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { body := loseIndestructibleInstr .this } ==
  "this creature loses indestructible until end of turn"
#guard TriggeredAbility.resolutionPhrase
    { body := loseIndestructibleInstr .attachedHost } ==
  "enchanted creature loses indestructible until end of turn"
#guard TriggeredAbility.resolutionPhrase Effect.enterTapLoseAbilitiesWhileSource ==
  "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature loses indestructible until end of turn."
#guard TriggeredAbility.toNotation
    (TriggeredAbility.mkTrigger .thisEnters { body := loseIndestructibleInstr .this }) ==
  "When this permanent enters, this creature loses indestructible until end of turn."
#guard TriggeredAbility.toNotation (.onEnterAttachThen (fun o => .installEffect (.applyContinuous .untilEndOfTurn o (.loseKeywords #[Keyword.indestructible])))) ==
  "When this Equipment enters, attach it to target creature you control. That creature loses indestructible until end of turn."
#guard TriggeredAbility.toNotation (.onEnter Effect.enterTapLoseAbilitiesWhileSource) ==
  "When this permanent enters, tap up to one target creature. It loses all abilities for as long as this remains on the battlefield."

end Mtg.Engine.LoseTests
