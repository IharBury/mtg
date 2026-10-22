import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.exile`

Which cards is an `ObjectSelector`.
The announced permanent, the source, the enchanted creature, and the target
while the source remains are exiled with `.forLater`.
Each announced permanent, the top card, lands you control, a basic land
search, and the opponent's top cards use those selectors.
Any other permanent or card the selector names is exiled the same way.
A hand or an unmade choice exiles nothing.
-/

namespace Mtg.Engine.ExileTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature .exile))

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

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def exiled (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.changeObject a.id (.attachedTo (some (pid g host)))

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
  let g := step board (.exile .target .forLater)
    (targets := #[Target.permanent (pid board "Titan")])
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let g := step board (.exile .target .forLater)
    (targets := #[Target.permanent (pid board "Bear")])
  exiled g "Bear" && !onBoard g "Bear" && onBoard g "Titan"

#guard
  let g := step board (.exile .target .forLater)
  onBoard g "Titan" && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 (.exile .target .forLater)
    (targets := #[Target.permanent (pid g0 "Field")])
  onBoard g "Field" && onBoard g "Titan" &&
    logContains g "The target is no longer legal"

#guard
  let g := step board (.exile .target .forLater)
    (targets := #[Target.player opp])
  onBoard g "Titan" && logContains g "The target is no longer legal"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.exile .target .forLater) (targets := #[Target.permanent newId])
  !exiled g "Titan" && logContains g "The target is no longer in play"

/- The source is exiled. A missing source, and a source that has left,
exile nothing. -/
#guard
  let g := step board (.exile .source .forLater) (some (pid board "Titan"))
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let g := step board (.exile .source .forLater)
  onBoard g "Titan" &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.exile .source .forLater) (some newId)
  !exiled g "Titan" && logContains g "Titan is no longer on the battlefield"

/- The enchanted creature is exiled. Nothing enchanted is silent.
An Aura that has left is reported. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (.exile .enchanted .forLater) (some (pid g0 "Grasp"))
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Grasp"

#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Bear"
  let g := step g0 (.exile .enchanted .forLater) (some (pid g0 "Grasp"))
  exiled g "Bear" && !onBoard g "Bear" && onBoard g "Grasp"

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.exile .enchanted .forLater) (some (pid g0 "Grasp"))
  onBoard g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.exile .enchanted .forLater) (some newId)
  onBoard g "Titan" && logContains g "Grasp is no longer on the battlefield"

#guard
  let g := step board (.exile .enchanted .forLater)
  onBoard g "Titan" && logContains g "The Aura is no longer in play"

/- The target is exiled only while the source remains. A source that has
left is silent. An illegal target is reported while the source is still there. -/
#guard
  let g := step board (.exile (.target .whileSource) .forLater)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  exiled g "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let g := step board (.exile (.target .whileSource) .forLater)
    (some (pid board "Titan")) #[Target.permanent (pid board "Bear")]
  exiled g "Bear" && !onBoard g "Bear" && onBoard g "Titan"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (.exile (.target .whileSource) .forLater)
    (some newId) #[Target.permanent (pid g0 "Titan")]
  onBoard g "Titan" && g.log == g0.log

#guard
  let g := step board (.exile (.target .whileSource) .forLater)
    (some (pid board "Bear"))
  onBoard g "Titan" && logContains g "The target is no longer legal"

/- Each announced permanent is exiled until the source leaves.
A missing source exiles nothing. -/
#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.exile (.target .eachPermanent) .untilSourceLeaves)
    (some (pid g0 "Grasp"))
    #[Target.permanent (pid g0 "Titan"), Target.permanent (pid g0 "Bear")]
  exiled g "Titan" && exiled g "Bear" && onBoard g "Grasp" &&
    logContains g "Titan is exiled until the source leaves the battlefield" &&
    logContains g "Bear is exiled until the source leaves the battlefield"

#guard
  let g := step board (.exile (.target .eachPermanent) .untilSourceLeaves)
    (targets := #[Target.permanent (pid board "Titan")])
  onBoard g "Titan" &&
    logContains g "The source has left the battlefield. Nothing is exiled."

/- The top card of the controller's library is exiled and may be played.
An empty library exiles nothing. -/
#guard
  let before := (board.player caster).library
  let name := topName board caster
  let g := step board (.exile .top .playUntilNextTurn)
  let after := (g.player caster).library
  after.size == before.size - 1 && exiled g name &&
    logContains g s!"exiles {name} and may play it until the end of their next turn"

#guard
  let g0 := board.changePlayer caster (.library #[])
  let g := step g0 (.exile .top .playUntilNextTurn)
  onBoard g "Titan" && onBoard g "Bear" &&
    logContains g "has no cards in their library to exile"

/- Lands the controller still controls are exiled and remembered.
A creature, and an opponent's land, stay. -/
#guard
  let g0 := addPermanent (addPermanent board land caster caster) marsh opp opp
  let g := step g0 (.exile .landsYouControl .forLater .lands)
    (targets := #[
      Target.permanent (pid g0 "Field"),
      Target.permanent (pid g0 "Marsh"),
      Target.permanent (pid g0 "Titan")])
  g.exiledIdsThisWay.size == 1 && exiled g "Field" &&
    onBoard g "Marsh" && onBoard g "Titan"

/- Up to `max` basic cards of a subtype open a library search. -/
#guard
  let g0 := insertObject board plains caster (.library caster)
    (updateOwner := fun id _ => #[.pushLibrary id])
  let g := step g0 (.exile (.basicUpTo "Plains" 2) .forLater .linked)
    (some (pid g0 "Titan"))
  match g.pending with
  | .fraChoice _ (.searchLibrary _ _ (.exileLinked _) _ _) => true
  | _ => false

/- The opponent's top cards are exiled, and that many casts are offered.
The reflexive still recognizes that resolution. Several lands can share
a name, so the new top may still be called the same thing. -/
#guard
  let before := (board.player opp).library.size
  let g := step board (.exile (.opponentTop 5) (.mayCastUpTo 2))
    (targets := #[Target.player opp])
  before ≥ 5 && (g.player opp).library.size == before - 5 && onBoard g "Titan" &&
    match g.pending with
    | .fraChoice _ (.mayCastUpToFromExile ids 2) => ids.size == 5
    | _ => false

#guard TriggeredAbility.TriggerResolution.queuedReflexive
    (.exile (.opponentTop 5) (.mayCastUpTo 2)) ==
  .modeled (TriggeredAbility.TriggerReflexiveKind.toNat .exileTopFive) 1

/- A cause that was not recorded, a player, a hand, and an unchosen card
exile nothing. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let tgt := #[Target.permanent (pid g0 "Titan")]
  let quiet := [
    step g0 (.exile .cause .forLater) sid tgt,
    step g0 (.exile (.player .you) .forLater) sid tgt,
    step g0 (.exile .hand .forLater) sid tgt,
    step g0 (.exile .cardFromHand .playUntilNextTurn) sid tgt]
  quiet.all fun g =>
    onBoard g "Titan" && onBoard g "Bear" && onBoard g "Grasp" &&
      g.pending == .none && g.log == g0.log

/- Creatures you control are exiled until the source leaves. The announced
permanent is exiled with no return. The source may be played until the
controller's next turn. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let tgt := #[Target.permanent (pid g0 "Titan")]
  let yours := step g0 (.exile .creaturesYouControl .untilSourceLeaves) sid tgt
  let announced := step g0 (.exile .permanent .forLater) sid tgt
  let source := step g0 (.exile .source .playUntilNextTurn) sid tgt
  exiled yours "Titan" && onBoard yours "Bear" &&
    exiled announced "Titan" && onBoard announced "Bear" &&
    exiled source "Bear" && onBoard source "Titan" &&
    match source.objects.find? (·.name == "Bear") with
    | some o => o.playPermission.isSome
    | none => false

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.TriggerResolution.ofPermanent .exile ==
  .exile .target .forLater
#guard TriggeredAbility.TriggerResolution.ofSource .exile ==
  .exile .source .forLater
#guard TriggeredAbility.TriggerResolution.ofEnchanted .exile ==
  .exile .enchanted .forLater
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .exile ==
  .exile (.target .whileSource) .forLater

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := .exile .target .forLater } ==
  "exile target creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .exile .source .forLater } ==
  "exile this creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .exile .enchanted .forLater } ==
  "exile enchanted creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .exile (.target .whileSource) .forLater } ==
  "exile that creature"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .exile .top .playUntilNextTurn } ==
  "exile the top card of your library. Until the end of your next turn, you may play that card"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .exile (.target .eachPermanent) .untilSourceLeaves } ==
  "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .exile .landsYouControl .forLater .lands } ==
  "exile up to three target lands you control"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .exile .cause .forLater } ==
  "exile it"

end Mtg.Engine.ExileTests
