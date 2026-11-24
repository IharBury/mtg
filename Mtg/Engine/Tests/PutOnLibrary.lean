import Mtg.Engine.Tests.Builders
import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified put-on-library instructions (`Instruction.moveZone ... (.library ...)`)

The announced permanent, the source, the enchanted creature, and the target
while the source remains go on top or on the bottom of their owner's library.
A card from the controller's hand goes on the bottom.
-/

namespace Mtg.Engine.PutOnLibraryTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def putTopInstr (obj : ObjectExpr) : Instruction :=
  .moveZone obj (.library .owner .top) .put {}

def putBottomInstr (obj : ObjectExpr) : Instruction :=
  .moveZone obj (.library .owner .bottom) .put {}

def onCreature : TriggeredAbility :=
  TriggeredAbility.mkTrigger .thisEnters { targets := .creature, body := putTopInstr (.target 0) }

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

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.record (GameEvent.attached g.turnNumber (g.snapshot a) (pid g host) (cause := .gameRule .staticAbility))

def topName (g : Game) (p : PlayerId) : String :=
  match (g.player p).library.back? with
  | some id => (g.object! id).name
  | none => ""

def bottomName (g : Game) (p : PlayerId) : String :=
  match (g.player p).library[0]? with
  | some id => (g.object! id).name
  | none => ""

def titan : CardDef := creature "Titan" ManaCost.empty #[] 4 4
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def land : CardDef := { name := "Field", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""
def legend : CardDef :=
  legendaryCreature "Unyielding Legend" ManaCost.empty #[] 2 2

def onTop : Instruction := putTopInstr (.target 0)
def onBottom : Instruction := putBottomInstr (.target 0)
def fromHand : Instruction :=
  .moveZone (.inZones (.handOf .you) .anyObject) (.library .owner .bottom) .put
    { choice? := some { chooser := .controller, count := .exact (.const 1) } }

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

def noHand : Game :=
  emptyHand board caster

/- The announced permanent's owner puts it on top. An opponent's creature
goes on that player's library. A missing target, a land, a player, and a
creature that has left stay where they are. -/
#guard
  let oldTop := (board.player caster).library.back!
  let g := step board onTop (targets := #[Target.permanent (pid board "Titan")])
  let lib := (g.player caster).library
  topName g caster == "Titan" && !onBoard g "Titan" && onBoard g "Bear" &&
    lib[lib.size - 2]? == some oldTop &&
    (g.player opp).library.back? == (board.player opp).library.back?

#guard
  let oldTop := (board.player opp).library.back!
  let g := step board onTop (targets := #[Target.permanent (pid board "Bear")])
  let lib := (g.player opp).library
  topName g opp == "Bear" && !onBoard g "Bear" && onBoard g "Titan" &&
    lib[lib.size - 2]? == some oldTop &&
    (g.player caster).library.back? == (board.player caster).library.back?

#guard
  let g := step board onTop
  onBoard g "Titan"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 onTop (targets := #[Target.permanent (pid g0 "Field")])
  onBoard g "Titan" && onBoard g "Field"

#guard
  let g := step board onTop (targets := #[Target.player opp])
  onBoard g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 onTop (targets := #[Target.permanent newId])
  (g.player caster).library.back? == (g0.player caster).library.back?

/- The announced permanent's owner puts it on the bottom. -/
#guard
  let oldBottom := (board.player opp).library[0]!
  let g := step board onBottom (targets := #[Target.permanent (pid board "Bear")])
  let lib := (g.player opp).library
  bottomName g opp == "Bear" && !onBoard g "Bear" && onBoard g "Titan" &&
    lib[1]? == some oldBottom &&
    (g.player caster).library[0]? == (board.player caster).library[0]?

/- The source goes on top or on the bottom of its owner's library. -/
#guard
  let g := step board (putTopInstr .this) (some (pid board "Titan")) (spec := .none)
  topName g caster == "Titan" && !onBoard g "Titan"

#guard
  let oldBottom := (board.player caster).library[0]!
  let g := step board (putBottomInstr .this) (some (pid board "Titan")) (spec := .none)
  bottomName g caster == "Titan" && !onBoard g "Titan" &&
    (g.player caster).library[1]? == some oldBottom

#guard
  let g := step board (putTopInstr .this) (spec := .none)
  onBoard g "Titan"

/- The enchanted creature goes on its owner's library. Nothing enchanted is silent. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (putTopInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  topName g caster == "Titan" && !onBoard g "Titan" && onBoard g "Grasp"

#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Bear"
  let oldBottom := (g0.player opp).library[0]!
  let g := step g0 (putBottomInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  bottomName g opp == "Bear" && !onBoard g "Bear" &&
    (g.player opp).library[1]? == some oldBottom

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (putTopInstr .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  onBoard g "Titan" && g.log == g0.log

/- The target moves only while the source remains. -/
#guard
  let g := step board (Instruction.ifThen (.exists .this) onBottom)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  bottomName g caster == "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (Instruction.ifThen (.exists .this) onTop)
    (some newId) #[Target.permanent (pid g0 "Titan")]
  onBoard g "Titan" && g.log == g0.log

/- A card from hand goes on the bottom of the controller's library. -/
#guard
  let card := (board.handObjects caster).back!
  let before := (board.player caster).library[0]!
  let g0 := step board fromHand (spec := .none)
  let g := mustApply g0 caster (.putOnBottom #[card.id])
  g0.pending == .putOnBottom caster 1 &&
    bottomName g caster == card.name &&
    (g.player caster).library[1]? == some before &&
    (g.player caster).hand.size == (board.player caster).hand.size - 1 &&
    g.pending == .none

#guard
  let g := step noHand fromHand (spec := .none)
  g.pending == .none &&
    (g.player caster).library[0]? == (noHand.player caster).library[0]?

/- Draw, then bottom a card when you control no legendary creature. -/
#guard
  let card := firstHandCard board caster
  let g0 := board.applyTriggeredAbility caster .onEnterDrawThenBottomIfNoLegendary none
  let g := mustApply g0 caster (.putOnBottom #[card.id])
  (g0.player caster).hand.size == (board.player caster).hand.size + 1 &&
    g0.pending == .putOnBottom caster 1 &&
    bottomName g caster == card.name &&
    (g.player caster).hand.size == (board.player caster).hand.size &&
    g.pending == .none

#guard
  let g0 := addPermanent board legend caster caster
  let g := g0.applyTriggeredAbility caster .onEnterDrawThenBottomIfNoLegendary none
  (g.player caster).hand.size == (g0.player caster).hand.size + 1 &&
    g.pending == .none

/- Creatures you control go on the bottom via `ObjectExpr.inZones`. -/
#guard
  let g := step board
    (putBottomInstr (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])))
    (spec := .none)
  !onBoard g "Titan" && onBoard g "Bear"

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature's owner puts it on top of their library."
#guard TriggeredAbility.toNotation
    (TriggeredAbility.mkTrigger .thisEnters { targets := .creature, body := onBottom }) ==
  "When this permanent enters, target creature's owner puts it on the bottom of their library."
#guard TriggeredAbility.toNotation
    (TriggeredAbility.mkTrigger .thisEnters { body := putTopInstr .this }) ==
  "When this permanent enters, this creature's owner puts it on top of their library."
#guard TriggeredAbility.toNotation (.onEnterEnchanted (fun o => .moveZone o (.library .owner .bottom) .put {})) ==
  "When this Aura enters, enchanted creature's owner puts it on the bottom of their library."
#guard TriggeredAbility.toNotation (.onEnterAttachThen (fun o => .moveZone o (.library .owner .top) .put {})) ==
  "When this Equipment enters, attach it to target creature you control. That creature's owner puts it on top of their library."
#guard TriggeredAbility.toNotation .onEnterDrawThenBottomIfNoLegendary ==
  "When this permanent enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library."

end Mtg.Engine.PutOnLibraryTests
