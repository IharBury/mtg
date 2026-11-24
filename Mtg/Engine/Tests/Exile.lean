import Mtg.Engine.Tests.Builders
import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified exile instructions (`Instruction.exile`)

Which cards are exiled is an `ObjectExpr`. The announced permanent, the source,
the enchanted creature, the target while the source remains, each opponent's
permanent until source leaves, the top card with play permission, lands you
control, library search to linked exile, and an opponent's top cards all
execute through unified `Instruction`.
-/

namespace Mtg.Engine.ExileTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

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

def exiled (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.record (GameEvent.attached g.turnNumber (g.snapshot a) (pid g host) (cause := .gameRule .staticAbility))

def topName (g : Game) (p : PlayerId) : String :=
  match (g.player p).library.back? with
  | some id => (g.object! id).name
  | none => ""

def titan : CardDef := creature "Titan" ManaCost.empty #[] 4 4
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def land : CardDef := { name := "Field", types := #[.land] }
def marsh : CardDef := { name := "Marsh", types := #[.land] }
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

/- The announced permanent is exiled. A missing target, a land, a player,
and a creature that has left stay where they are. -/
#guard
  let g := step board (Instruction.exile (.target 0))
    (targets := #[Target.permanent (pid board "Titan")])
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let g := step board (Instruction.exile (.target 0))
    (targets := #[Target.permanent (pid board "Bear")])
  exiled g "Bear" && !onBoard g "Bear" && onBoard g "Titan"

#guard
  let g := step board (Instruction.exile (.target 0))
  onBoard g "Titan"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 (Instruction.exile (.target 0))
    (targets := #[Target.permanent (pid g0 "Field")])
  onBoard g "Field" && onBoard g "Titan"

#guard
  let g := step board (Instruction.exile (.target 0))
    (targets := #[Target.player opp])
  onBoard g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (Instruction.exile (.target 0)) (targets := #[Target.permanent newId])
  !exiled g "Titan"

/- The source is exiled. A missing source, and a source that has left, exile nothing. -/
#guard
  let g := step board (Instruction.exile .this) (some (pid board "Titan")) (spec := .none)
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let g := step board (Instruction.exile .this) (spec := .none)
  onBoard g "Titan"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (Instruction.exile .this) (some newId) (spec := .none)
  !exiled g "Titan"

/- The enchanted creature is exiled. Nothing enchanted is silent. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (Instruction.exile .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Grasp"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (Instruction.exile .attachedHost) (some (pid g0 "Grasp")) (spec := .none)
  onBoard g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (Instruction.exile .attachedHost) (some newId) (spec := .none)
  onBoard g "Titan"

/- The target is exiled only while the source remains. A source that has left is silent. -/
#guard
  let g := step board (Instruction.ifThen (.exists .this) (Instruction.exile (.target 0)))
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (Instruction.ifThen (.exists .this) (Instruction.exile (.target 0)))
    (some newId) #[Target.permanent (pid g0 "Titan")]
  onBoard g "Titan" && g.log == g0.log

/- Each announced permanent is exiled until the source leaves.
A missing source exiles nothing. -/
#guard
  let g0 := addPermanent board grasp caster caster
  let g := g0.applyTriggeredAbility caster .onEnterExileOppNonlandEachUntilLeaves
    (some (pid g0 "Grasp")) #[Target.permanent (pid g0 "Bear")]
  exiled g "Bear" && onBoard g "Grasp" &&
    !(obj g "Grasp").linkedExile.isEmpty

#guard
  let g :=
    board.applyTriggeredAbility caster .onEnterExileOppNonlandEachUntilLeaves
      none #[Target.permanent (pid board "Bear")]
  onBoard g "Bear"

/- The top card of the controller's library is exiled and may be played.
An empty library exiles nothing. -/
#guard
  let before := (board.player caster).library
  let name := topName board caster
  let g := step board Effect.triggerExileTop.body (spec := .none)
  let after := (g.player caster).library
  after.size == before.size - 1 && exiled g name

#guard
  let g0 := emptyLibrary board caster
  let g := step g0 Effect.triggerExileTop.body (spec := .none)
  onBoard g "Titan" && onBoard g "Bear"

/- Exile up to three lands you control, then return them tapped. -/
#guard
  let g0 := addPermanent (addPermanent board land caster caster) marsh opp opp
  let g := g0.applyTriggeredAbility caster .onEnterExileLandsThenReturnTapped none
    #[Target.permanent (pid g0 "Field")]
  onBoard g "Field" && (obj g "Field").status.tapped && onBoard g "Marsh"

/- Search for basic Plains to linked exile opens a library search. -/
#guard
  let g0 := insertObject board plains caster (.library caster)
  let g := g0.applyTriggeredAbility caster
    (TriggeredAbility.sagaChapter 1 (Effect.chapterSearchBasicPlainsExileGainLife 2 2))
    (some (pid g0 "Titan"))
  match g.pending with
  | .fraChoice _ (.searchLibrary _ _ (.exileLinked _) _ _) => true
  | _ => false

/- Creatures you control are exiled until source leaves; source exiled with play permission. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let yours := step g0
    (Instruction.exile (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) { exileUntilSourceLeaves := true })
    sid (spec := .none)
  let source := step g0
    (Instruction.exile .this { grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true } })
    sid (spec := .none)
  exiled yours "Titan" && onBoard yours "Bear" &&
    exiled source "Bear" && onBoard source "Titan" &&
    match source.objects.find? (·.name == "Bear") with
    | some o => (source.playPermission o).isSome
    | none => false

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.resolutionPhrase
    { targets := .creature, body := Instruction.exile (.target 0) } ==
  "exile target creature"
#guard TriggeredAbility.resolutionPhrase
    { body := Instruction.exile .this } ==
  "exile this creature"
#guard TriggeredAbility.resolutionPhrase
    { body := Instruction.exile .attachedHost } ==
  "exile enchanted creature"
#guard TriggeredAbility.resolutionPhrase Effect.triggerExileTop ==
  "exile the top card of your library. Until the end of your next turn, you may play that card"
#guard TriggeredAbility.resolutionPhrase Effect.triggerExileOppNonlandEachUntilLeaves ==
  "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"

end Mtg.Engine.ExileTests
