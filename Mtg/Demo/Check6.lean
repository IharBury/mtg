import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard shouldAutoTarget Tests.proposedEquip []

#guard targetCommand Tests.proposedBolt ⟨0⟩ (Target.player ⟨1⟩) == "target opponent"

#guard (autoTargetStep? Tests.proposedBolt []).isNone

#guard
  let tid := (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id
  match autoTargetStep? Tests.proposedSmite [] with
  | some (.ok (_, cmd)) =>
    let parts := cmd.splitOn " "
    match applyInteractiveAsActor Tests.proposedSmite (parts.headD "") (parts.drop 1) with
    | .ok g' => g'.stack.back!.targets == #[Target.permanent tid]
    | .error _ => false
  | _ => false


#guard looksLikeDeckFile "alice.txt"

#guard !looksLikeDeckFile "red"


#guard deckAssignmentLine { name := "Chandra", deck := .welcome .red } ==
  "Chandra uses the red Hobbit Welcome Deck."

#guard
  match parseArgs ["--multiplayer"] with
  | .ok opt => opt.interactive && opt.multiplayer && !opt.playerView
  | _ => false


#guard
  match parseArgs ["--visible"] with
  | .error msg => msg == "--visible requires --interactive or --multiplayer"
  | .ok _ => false


#guard
  match parseArgs ["--input", "opening.txt"] with
  | .error msg => msg == "--input requires --interactive or --multiplayer"
  | .ok _ => false


#guard
  match parseArgs [] with
  | .ok opt => !opt.constructed
  | _ => false


#guard
  match parseArgsWithFlags [] ["--constructed"] with
  | .ok opt => opt.constructed
  | _ => false


#guard
  match Start.start (demoConfig 1) with
  | .ok g => g.format == .limited
  | .error _ => false


#guard
  match parseArgsWithFlags ["--norandom", "--input", "opening.txt"] ["--norandom"] with
  | .ok opt => opt.norandom
  | _ => false


#guard
  match parseArgs ["--check", "--multiplayer", "--input", "foo.txt"] with
  | .ok opt => opt.check && opt.interactive && opt.multiplayer
  | _ => false

