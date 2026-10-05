import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard !isPassSequenceCommand "cast" ["3"]

#guard isPassSequenceAction (.declareBlockers #[])

#guard (shortcutKind? "cast" ["3"]).isNone

#guard !passUntilSkipsAttackers .nextDeclareAttackers

#guard passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨0⟩ (.named .nextTurnCombat)) ==
  some "noattack"

#guard (passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨1⟩
      (.named .nextTurnMain))).isNone

#guard (passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨1⟩
      (.named .nextDeclareAttackers))).isNone

#guard
  match applyKeep Tests.drawnHands ⟨0⟩ ["1"] with
  | .error msg => msg == keepUsage
  | .ok _ => false


#guard
  match Tests.twoAttercopsLandPending.pending with
  | .chooseTriggerToStack _ =>
    let ids := Tests.twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
    match applyInteractiveAsActor Tests.twoAttercopsLandPending "stack"
        [toString ids[0]!, toString ids[1]!] with
    | .ok g' =>
      g'.stack.size == 2 && g'.waitingTriggers.isEmpty &&
        g'.log.any (fun s => Tests.mentions s "CR 603.3b")
    | .error _ => false
  | _ => false


#guard
  match applyInteractiveAsActor Tests.proposedBolt "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.stack.back!.targets == #[Target.player ⟨1⟩]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.gandalfEntered "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[3]
  | .error _ => false


#guard
  match applyTarget Tests.proposedDecree ⟨1⟩
      [toString Tests.paidBolt.stack.back!.objectId] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨1⟩ &&
    g'.stack.back!.targets == #[Target.card Tests.paidBolt.stack.back!.objectId] &&
    g'.log.any (fun s => Tests.mentions s "chooses Lightning Bolt as a target (CR 601.2c)")
  | .error _ => false


#guard
  match applyTarget Tests.elkEntered ⟨0⟩ ["Llanowar Elves"] with
  | .ok g' =>
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.elkAttackDeclared "target" ["Llanowar Elves"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkAttackDeclared ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false


#guard
  let g := Tests.dunedainReady
  let blade := Tests.namedPermanent g "Dúnedain Blade"
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applyActivate g ⟨0⟩ [toString blade.id, "2"] with
  | .error _ => false
  | .ok g' =>
    match applyTarget g' ⟨0⟩ [toString bears.id] with
    | .ok g'' =>
      g''.pending == .activateManaAbilities ⟨0⟩ &&
      g''.log.any (fun s => Tests.mentions s "begins activating Dúnedain Blade")
    | .error _ => false


#guard
  match applyInteractiveAsActor Tests.galionAttackDeclared "decline" [] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.stack.back!.targetsAnnounced &&
    g'.log.any (fun s => Tests.mentions s "chooses no target")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.readyToDeclareBlockers "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.gollumVsOneBearReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking.isEmpty &&
      !(Tests.namedPermanent g' "Gollum, Silent Slinker").status.blocked
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.gollumAndOgreVsOneBearReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id] &&
      !(Tests.namedPermanent g' "Gollum, Silent Slinker").status.blocked
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.struckerMayConnive "connive" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Baron Strucker, HYDRA Overlord").status.optionalOnceUsed &&
      g'.log.any (fun s => Tests.mentions s "connives")
  | .error _ => false


#guard
  let g := Tests.spearKnownMayDiscard
  let forest := Tests.handCardNamed g ⟨0⟩ "Forest"
  match applyInteractiveAsActor g "discard" [toString forest.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "discards Forest")
  | .error _ => false


#guard
  let g := Tests.lookoutKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 1
  match looked[0]? with
  | some forest =>
    match applyInteractiveAsActor g "scry" ["bottom", toString forest] with
    | .ok g' =>
      (g'.object! (g'.player ⟨0⟩).library[0]!).name == "Forest" &&
        g'.log.any (fun s => Tests.mentions s "puts Forest on the bottom")
    | .error _ => false
  | none => false


/-- Surveil 2 with Grizzly Bears on top of Hill Giant. -/
def surveilBearsGiant : Game :=
  let g := Tests.addToLibraryTop Tests.afterDraw hillGiant ⟨0⟩
  let g := Tests.addToLibraryTop g grizzlyBears ⟨0⟩
  g.beginSurveil ⟨0⟩ 2

def surveilCommand (args : List String) : Except String Game :=
  applyInteractiveAsActor surveilBearsGiant "surveil" args

def surveilIdNamed (name : String) : String :=
  match (surveilBearsGiant.scryLookedIds ⟨0⟩ 2).find?
      (fun id => (surveilBearsGiant.object! id).name == name) with
  | some id => toString id
  | none => "?"

def libraryTopName (g : Game) : String :=
  match (g.player ⟨0⟩).library.back? with
  | some id => (g.object! id).name
  | none => ""

def graveyardHas (g : Game) (name : String) : Bool :=
  (g.player ⟨0⟩).graveyard.any (fun id => (g.object! id).name == name)

#guard surveilBearsGiant.pending == .surveil ⟨0⟩ 2

#guard
  match surveilCommand [] with
  | .ok g => g.pending == .none && libraryTopName g == "Grizzly Bears" &&
      !graveyardHas g "Grizzly Bears" && !graveyardHas g "Hill Giant"
  | .error _ => false

#guard
  match surveilCommand ["graveyard", surveilIdNamed "Grizzly Bears"] with
  | .ok g => g.pending == .none && libraryTopName g == "Hill Giant" &&
      graveyardHas g "Grizzly Bears" &&
      g.log.any (fun s => Tests.mentions s "puts Grizzly Bears into their graveyard (surveil)")
  | .error _ => false

#guard
  match surveilCommand ["top", surveilIdNamed "Hill Giant"] with
  | .ok g => libraryTopName g == "Hill Giant" && graveyardHas g "Grizzly Bears"
  | .error _ => false

#guard
  match surveilCommand ["top", surveilIdNamed "Grizzly Bears", surveilIdNamed "Hill Giant",
      "graveyard"] with
  | .ok g => libraryTopName g == "Hill Giant" && !graveyardHas g "Grizzly Bears"
  | .error _ => false

#guard
  match surveilCommand ["graveyard", surveilIdNamed "Hill Giant",
      surveilIdNamed "Grizzly Bears"] with
  | .ok g =>
    (g.player ⟨0⟩).graveyard.toList.map (fun id => (g.object! id).name) ==
      ["Hill Giant", "Grizzly Bears"]
  | .error _ => false

#guard
  match surveilCommand ["bottom", surveilIdNamed "Hill Giant"] with
  | .error e => e == surveilUsage
  | .ok _ => false

#guard
  match applyInteractiveAsActor surveilBearsGiant "scry" [] with
  | .error e => Tests.mentions e "use surveil"
  | .ok _ => false

#guard
  match applyInteractiveAsActor Tests.lookoutKnownScrying "surveil" [] with
  | .error e => Tests.mentions e "use scry"
  | .ok _ => false

#guard
  match applyInteractiveAsActor Tests.afterDraw "surveil" [] with
  | .error e => Tests.mentions e "Not time to surveil"
  | .ok _ => false

#guard (header surveilBearsGiant).contains "[surveil 2 ("
#guard
  match scryLookBlock surveilBearsGiant with
  | some b => b.startsWith "Surveil (top last):" && (b.splitOn "Grizzly Bears").length == 2
  | none => false
#guard scryLookBlock surveilBearsGiant (some ⟨1⟩) == some s!"{(surveilBearsGiant.player ⟨0⟩).name} is surveilling 2"


#guard
  match applyInteractiveAsActor Tests.woodElvesKnownLib "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      g'.stack.isEmpty &&
      g'.log.any (fun s => Tests.mentions s "puts Forest onto the battlefield") &&
      g'.battlefield.any (fun o => o.name == "Forest" && !o.status.tapped)
    | .error _ => false
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.weavemasterElfEntered "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      g'.power (Tests.namedPermanent g' "Woodland Weavemaster") == 2 &&
        g'.log.any (fun s => Tests.mentions s "gets +1/+1 until end of turn")
    | .error _ => false
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.paidPathmaker "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      g'.stack.isEmpty &&
      g'.power (Tests.namedPermanent g' "Mirkwood Pathmaker") == 2 &&
        g'.log.any (fun s => Tests.mentions s "enters the battlefield")
    | .error _ => false
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.proposedFireOfOrthanc "target"
      [toString (Tests.namedPermanent Tests.proposedFireOfOrthanc "Forest").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Forest").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.targetedBolt "autopay" [] with
  | .ok g' =>
    g'.pending == .none &&
      g'.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false


#guard
  match applyYourTurn Tests.afterDraw ⟨0⟩ [] with
  | .error msg => msg == yourTurnUsage
  | .ok _ => false


#guard
  match applyLoggedAction Tests.afterDraw "my" ["turn"] "my turn" with
  | .error msg => msg == "The next turn is not yours"
  | .ok _ => false


#guard
  match applyLoggedAction Tests.readyToDeclareAttackers "ignore" [] "ignore" with
  | .ok (g', cmds) =>
    cmds.contains "noattack" &&
      g'.pending != .declareAttackers
  | .error _ => false


#guard
  match applyLoggedAction (skipTo Tests.afterDraw .beginningOfCombat 80)
      "attack" ["step"] "attack step" with
  | .ok (g', cmds) =>
    cmds == #["pass"] &&
      g'.step == .beginningOfCombat &&
      g'.pending != .declareAttackers &&
      g'.turnNumber == 1 &&
      g'.hasPriority ⟨1⟩
  | .error _ => false


#guard
  let gReady := Tests.addPermanent Tests.nissaDraw grizzlyBears ⟨1⟩ ⟨1⟩
  match gReady.apply ⟨1⟩ .pass with
  | .error _ => false
  | .ok g =>
    match applyLoggedAction g "my" ["turn"] "my turn" with
    | .ok (g', cmds) =>
      cmds == #["pass"] &&
        !cmds.contains "noattack" &&
        g'.step == .precombatMain &&
        g'.turnNumber == 2 &&
        g'.activePlayer == ⟨1⟩ &&
        g'.hasPriority ⟨1⟩
    | .error _ => false

