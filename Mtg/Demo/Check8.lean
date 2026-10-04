import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard
  match parseArgs ["--deck", "--seed", "1"] with
  | .error msg => msg == "Missing Welcome Deck color or deck list file"
  | .ok _ => false


#guard
  match parseArgs ["--chandra", "white"] with
  | .error msg => msg == "Unknown argument: --chandra"
  | .ok _ => false


#guard
  match parseArgs ["--multiplayer", "--decides", "Chandra"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.decides == some 0
  | _ => false


#guard
  match parseArgs [
      "--name", "Elspeth", "--deck", "white",
      "--name", "Jace", "--deck", "blue",
      "--decides", "Nissa"] with
  | .error msg => msg == "No player named Nissa"
  | .ok _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--visible"] with
  | .ok opt => opt.interactive && opt.playerView && opt.inputFile == some "opening.txt"
  | _ => false


#guard
  match parseArgsWithFlags ["--input", "opening.txt"] ["--interactive"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.inputFile == some "opening.txt"
  | _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"]
      ["--name Elspeth --deck white", "--name Jace --deck blue"] with
  | .ok opt => opt.players == elspethJace
  | _ => false


#guard
  match parseDecider defaultDemoPlayers ["Nissa"] with
  | .ok 1 => true
  | _ => false

