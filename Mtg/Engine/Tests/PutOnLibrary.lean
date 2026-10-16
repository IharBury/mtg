import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.putOnLibrary`

Which card is an `ObjectSelector`.
The announced permanent, the source, the enchanted creature, and the target
while the source remains go on top or on the bottom of their owner's library.
A card from the controller's hand goes on the bottom. Any other selector
puts nothing.
-/

namespace Mtg.Engine.PutOnLibraryTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def onCreature : TriggeredAbility :=
  .triggered .enter (Effect.ofTrigger (.onPermanent .creature .putOnTopOfLibrary))

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

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.setObject { a with attachedTo := some (pid g host) }

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

def onTop : TriggeredAbility.TriggerResolution := .putOnLibrary .top
def onBottom : TriggeredAbility.TriggerResolution := .putOnLibrary .bottom
def fromHand : TriggeredAbility.TriggerResolution :=
  .putOnLibrary .bottom .cardFromHand

def board : Game :=
  addPermanent (addPermanent afterDraw titan caster caster) bear opp opp

def noHand : Game :=
  board.modifyPlayer caster fun pl => { pl with hand := #[] }

/- The announced permanent's owner puts it on top. An opponent's creature
goes on that player's library. A missing target, a land, a player, and a
creature that has left stay where they are. -/
#guard
  let oldTop := (board.player caster).library.back!
  let g := step board onTop (targets := #[Target.permanent (pid board "Titan")])
  let lib := (g.player caster).library
  topName g caster == "Titan" && !onBoard g "Titan" && onBoard g "Bear" &&
    lib[lib.size - 2]? == some oldTop &&
    (g.player opp).library.back? == (board.player opp).library.back? &&
    logContains g "puts Titan on the top of their library"

#guard
  let oldTop := (board.player opp).library.back!
  let g := step board onTop (targets := #[Target.permanent (pid board "Bear")])
  let lib := (g.player opp).library
  topName g opp == "Bear" && !onBoard g "Bear" && onBoard g "Titan" &&
    lib[lib.size - 2]? == some oldTop &&
    (g.player caster).library.back? == (board.player caster).library.back? &&
    logContains g "puts Bear on the top of their library"

#guard
  let g := step board onTop
  onBoard g "Titan" && logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent board land caster caster
  let g := step g0 onTop (targets := #[Target.permanent (pid g0 "Field")])
  onBoard g "Titan" && onBoard g "Field" &&
    logContains g "The target is no longer legal"

#guard
  let g := step board onTop (targets := #[Target.player opp])
  onBoard g "Titan" && logContains g "The target is no longer legal"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 onTop (targets := #[Target.permanent newId])
  (g.player caster).library.back? == (g0.player caster).library.back? &&
    logContains g "The target is no longer in play"

/- The announced permanent's owner puts it on the bottom, under the cards
that were already there. -/
#guard
  let oldBottom := (board.player opp).library[0]!
  let g := step board onBottom (targets := #[Target.permanent (pid board "Bear")])
  let lib := (g.player opp).library
  bottomName g opp == "Bear" && !onBoard g "Bear" && onBoard g "Titan" &&
    lib[1]? == some oldBottom &&
    (g.player caster).library[0]? == (board.player caster).library[0]? &&
    logContains g "puts Bear on the bottom of their library"

/- The source goes on top or on the bottom of its owner's library. A missing
source, and a source that has left, move nothing. -/
#guard
  let g := step board (.putOnLibrary .top .source)
    (some (pid board "Titan"))
  topName g caster == "Titan" && !onBoard g "Titan" &&
    logContains g "puts Titan on the top of their library"

#guard
  let oldBottom := (board.player caster).library[0]!
  let g := step board (.putOnLibrary .bottom .source)
    (some (pid board "Titan"))
  bottomName g caster == "Titan" && !onBoard g "Titan" &&
    (g.player caster).library[1]? == some oldBottom

#guard
  let g := step board (.putOnLibrary .top .source)
  onBoard g "Titan" &&
    logContains g "The triggered ability's source is no longer in play"

#guard
  let id := pid board "Titan"
  let (g0, newId) := board.move id (.graveyard caster) none
  let g := step g0 (.putOnLibrary .bottom .source) (some newId)
  (g.player caster).library[0]? == (g0.player caster).library[0]? &&
    logContains g "Titan is no longer on the battlefield"

/- The enchanted creature goes on its owner's library. Nothing enchanted is
silent. An Aura that has left is reported. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let g := step g0 (.putOnLibrary .top .enchanted)
    (some (pid g0 "Grasp"))
  topName g caster == "Titan" && !onBoard g "Titan" && onBoard g "Grasp" &&
    logContains g "puts Titan on the top of their library"

#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Bear"
  let oldBottom := (g0.player opp).library[0]!
  let g := step g0 (.putOnLibrary .bottom .enchanted)
    (some (pid g0 "Grasp"))
  bottomName g opp == "Bear" && !onBoard g "Bear" &&
    (g.player opp).library[1]? == some oldBottom

#guard
  let g0 := addPermanent board grasp caster caster
  let g := step g0 (.putOnLibrary .top .enchanted)
    (some (pid g0 "Grasp"))
  onBoard g "Titan" && g.log == g0.log

#guard
  let g0 := addPermanent board grasp caster caster
  let id := pid g0 "Grasp"
  let (g1, newId) := g0.move id (.graveyard caster) none
  let g := step g1 (.putOnLibrary .bottom .enchanted) (some newId)
  onBoard g "Titan" && logContains g "Grasp is no longer on the battlefield"

#guard
  let g := step board (.putOnLibrary .top .enchanted)
  onBoard g "Titan" &&
    logContains g "The Aura is no longer in play"

/- The target moves only while the source remains. A source that has left
is silent. An illegal target is reported while the source is still there. -/
#guard
  let g := step board (.putOnLibrary .bottom .targetWhileSource)
    (some (pid board "Bear")) #[Target.permanent (pid board "Titan")]
  bottomName g caster == "Titan" && !onBoard g "Titan" && onBoard g "Bear"

#guard
  let g := step board (.putOnLibrary .top .targetWhileSource)
    (some (pid board "Titan")) #[Target.permanent (pid board "Bear")]
  topName g opp == "Bear" && !onBoard g "Bear" && onBoard g "Titan"

#guard
  let id := pid board "Bear"
  let (g0, newId) := board.move id (.graveyard opp) none
  let g := step g0 (.putOnLibrary .top .targetWhileSource)
    (some newId) #[Target.permanent (pid g0 "Titan")]
  onBoard g "Titan" && g.log == g0.log

#guard
  let g := step board (.putOnLibrary .bottom .targetWhileSource)
    (some (pid board "Bear"))
  onBoard g "Titan" && logContains g "The target is no longer legal"

/- A card from hand goes on the bottom of the controller's library. The
chosen card is the new bottom. An empty hand skips the choice. Putting a
card from hand on top does nothing. -/
#guard
  let card := (board.handObjects caster).back!
  let before := (board.player caster).library[0]!
  let g0 := step board fromHand
  let g := mustApply g0 caster (.putOnBottom #[card.id])
  g0.pending == .putOnBottom caster 1 &&
    bottomName g caster == card.name &&
    (g.player caster).library[1]? == some before &&
    (g.player caster).hand.size == (board.player caster).hand.size - 1 &&
    g.pending == .none &&
    logContains g0 "puts a card from their hand on the bottom of their library"

#guard
  let g := step noHand fromHand
  g.pending == .none && g.log == noHand.log &&
    (g.player caster).library[0]? == (noHand.player caster).library[0]?

#guard
  let g := step board (.putOnLibrary .top .cardFromHand)
    (targets := #[Target.permanent (pid board "Titan")])
  g.pending == .none && g.log == board.log && onBoard g "Titan" &&
    (g.player caster).hand.size == (board.player caster).hand.size &&
    (g.player caster).library.back? == (board.player caster).library.back?

/- Draw, then bottom a card when you control no legendary creature. The
chosen card is the new bottom, and the drawn card stays in hand. A legendary
creature you already control skips the bottom step. -/
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
    g.pending == .none &&
    !logContains g "bottom of their library"

/- Any other selector puts nothing. -/
#guard
  let g0 := attach (addPermanent board grasp caster caster) "Grasp" "Titan"
  let sid := some (pid g0 "Bear")
  let tgt := #[Target.permanent (pid g0 "Titan")]
  let crossed := [
    step g0 (.putOnLibrary .top .cause) sid tgt,
    step g0 (.putOnLibrary .bottom .creaturesYouControl) sid tgt,
    step g0 (.putOnLibrary .top (.player .you)) sid tgt,
    step g0 (.putOnLibrary .bottom .hand) sid tgt,
    step g0 (.putOnLibrary .top .permanent) sid tgt]
  crossed.all fun g =>
    onBoard g "Titan" && onBoard g "Bear" && onBoard g "Grasp" &&
      g.pending == .none && g.log == g0.log

/- Printed phrases stay with the combination that produces them. -/
#guard (.putOnLibrary .top : TriggeredAbility.TriggerResolution) ==
  .putOnLibrary .top .target
#guard (.putOnLibrary : TriggeredAbility.TriggerResolution) == onTop
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnTopOfLibrary == onTop
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnBottomOfLibrary == onBottom
#guard TriggeredAbility.TriggerResolution.ofSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnTopOfLibrary ==
  .putOnLibrary .top .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .targetWhileSource
#guard TriggeredAbility.resolution .onEnterDrawThenBottomIfNoLegendary ==
  .sequence [.draw (.fixed 1), .«if» .noLegendaryCreature fromHand]

#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := onTop } ==
  "target creature's owner puts it on top of their library"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .creature, resolution := onBottom } ==
  "target creature's owner puts it on the bottom of their library"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .putOnLibrary .top .source } ==
  "this creature's owner puts it on top of their library"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .putOnLibrary .bottom .enchanted } ==
  "enchanted creature's owner puts it on the bottom of their library"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .putOnLibrary .top .targetWhileSource } ==
  "that creature's owner puts it on top of their library"
#guard TriggeredAbility.resolutionPhrase { resolution := fromHand } ==
  "put a card from your hand on the bottom of your library"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .«if» .noLegendaryCreature fromHand } ==
  "if you don't control a legendary creature, put a card from your hand on the bottom of your library"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .putOnLibrary .top .cardFromHand } == "put on library"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .putOnLibrary .bottom .cause } == "put on library"
#guard TriggeredAbility.resolutionPhrase {
    targeting := .of .creatureYouControl
    resolution := .sequence
      [.attach .source .target, .putOnLibrary .bottom .targetWhileSource] } ==
  "attach it to target creature you control. That creature's owner puts it on the bottom of their library"

#guard TriggeredAbility.toNotation onCreature ==
  "When this permanent enters, target creature's owner puts it on top of their library."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onPermanent .creature .putOnBottomOfLibrary))) ==
  "When this permanent enters, target creature's owner puts it on the bottom of their library."
#guard TriggeredAbility.toNotation
    (.triggered .enter (Effect.ofTrigger (.onSource .putOnTopOfLibrary))) ==
  "When this permanent enters, this creature's owner puts it on top of their library."
#guard TriggeredAbility.toNotation (.onEnterEnchanted .putOnBottomOfLibrary) ==
  "When this Aura enters, enchanted creature's owner puts it on the bottom of their library."
#guard TriggeredAbility.toNotation (.onEnterAttachThen .putOnTopOfLibrary) ==
  "When this Equipment enters, attach it to target creature you control. That creature's owner puts it on top of their library."
#guard TriggeredAbility.toNotation .onEnterDrawThenBottomIfNoLegendary ==
  "When this permanent enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library."

end Mtg.Engine.PutOnLibraryTests
