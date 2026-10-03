import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard
  match parseArgs ["--check", "--input", "foo.txt"] with
  | .ok opt =>
    match checkCompleteGame opt demoSeats ["first Chandra", "keep", "keep", "concede"] with
    | .ok g => g.over && describeCheckResult g == "Winner: Nissa"
    | .error _ => false
  | _ => false


#guard
  match parseArgs ["--interactive", "--input", "--visible"] with
  | .error msg => msg == "Missing input file path"
  | .ok _ => false


#guard
  match parseArgs ["--interactive", "--input", "opening.txt", "--output", "session.txt"] with
  | .ok opt => opt.inputFile == some "opening.txt" && opt.outputFile == some "session.txt"
  | _ => false


#guard
  match parseArgs ["--auto", "--output", "session.txt"] with
  | .error msg => msg == "--output requires --interactive or --multiplayer"
  | .ok _ => false

