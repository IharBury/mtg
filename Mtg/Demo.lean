import Mtg.Engine

/-!
# Mtg.Demo

Console demonstration of `Mtg.Engine`. Default mode runs a scripted two-player
game with a heuristic agent. Pass `--interactive` to play Chandra against the
agent-controlled Nissa.
-/

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Render

def usage : String :=
  "Mtg.Demo — demonstration of the Mtg.Engine rules engine

Usage:
  lake exe mtg-demo [--auto | --interactive] [--seed N] [--fuel N]

Options:
  --auto          Run a heuristic two-player game (default)
  --interactive   Play as Chandra; Nissa is heuristic-controlled
  --seed N        RNG seed (default 20260807)
  --fuel N        Maximum heuristic actions (default 800)
  --help          Show this help

The engine follows the Magic: The Gathering Comprehensive Rules
effective 7 August 2026.
"

def demoConfig (seed : UInt64) : StartConfig := {
  seats := #[
    { name := "Chandra", deck := redDeck },
    { name := "Nissa", deck := greenDeck }
  ]
  format := .constructed
  seed := seed
  startingPlayer := some 0
}

def printLog (g : Game) (startIdx : Nat) : IO Nat := do
  for line in newLog g startIdx do
    IO.println s!"  {line}"
  return g.log.size

def printState (g : Game) : IO Unit := do
  IO.println ""
  IO.println (snapshot g)
  IO.println ""

def startDemo (seed : UInt64) : IO Game := do
  match Start.start (demoConfig seed) with
  | .error e =>
    IO.eprintln s!"Failed to start game: {e}"
    throw (IO.userError e)
  | .ok g =>
    IO.println Mtg.Engine.identification
    IO.println s!"Rules source: {Rules.sourceUrl}"
    IO.println ""
    let _ ← printLog g 0
    printState g
    return g

partial def runAuto (g : Game) (fuel : Nat) : IO Unit := do
  let mut g := g
  let mut seen := g.log.size
  let mut remaining := fuel
  while remaining > 0 && !g.over do
    remaining := remaining - 1
    match Agent.step g with
    | .error e =>
      IO.println s!"Agent stopped: {e}"
      break
    | .ok g' =>
      seen ← printLog g' seen
      g := g'
  printState g
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => IO.println s!"Stopped after {fuel} actions (turn {g.turnNumber})."

def helpInteractive : String :=
  "Commands:
  help                 Show this help
  state                Print the board
  pass                 Pass priority
  play <id>            Play a land
  tap <id>             Tap a permanent for its first mana ability
  cast <id>            Cast a spell (burn targets the opponent)
  attack               Attack with every creature that can
  noattack             Declare no attackers
  noblock              Declare no blockers
  concede              Concede
  quit                 Exit
"

partial def interactiveLoop (g : Game) : IO Unit := do
  let mut g := g
  let mut seen := g.log.size
  let chandra : PlayerId := ⟨0⟩
  let nissa : PlayerId := ⟨1⟩
  IO.println helpInteractive
  while !g.over do
    -- If Nissa must act, let the agent play until Chandra is the actor (or the game ends).
    while !g.over && g.actor == some nissa do
      match Agent.step g with
      | .error e =>
        IO.println s!"Nissa could not act: {e}"
        break
      | .ok g' =>
        seen ← printLog g' seen
        g := g'
    if g.over then break
    IO.print "mtg> "
    let stdin ← IO.getStdin
    let line := (← stdin.getLine).trim
    if line.isEmpty then
      continue
    let parts := line.splitOn " "
    let cmd := parts.headD ""
    let arg := parts.drop 1 |>.headD ""
    let act : Except String Game :=
      match cmd with
      | "help" => .ok g
      | "state" => .ok g
      | "quit" | "exit" => .ok g
      | "pass" => g.apply chandra .pass
      | "concede" => g.apply chandra .concede
      | "attack" =>
        let ids := g.battlefield.filter (g.canAttack) |>.map (·.id)
        g.apply chandra (.declareAttackers ids)
      | "noattack" => g.apply chandra (.declareAttackers #[])
      | "noblock" => g.apply chandra (.declareBlockers #[])
      | "play" =>
        match arg.toNat? with
        | none => .error "usage: play <id>"
        | some n => g.apply chandra (.playLand ⟨n⟩)
      | "tap" =>
        match arg.toNat? with
        | none => .error "usage: tap <id>"
        | some n =>
          match g.findObject? ⟨n⟩ with
          | none => .error "no such object"
          | some o =>
            match o.printed.manaAbilities[0]? with
            | none => .error s!"{o.name} has no mana ability"
            | some m => g.apply chandra (.tapForMana ⟨n⟩ m)
      | "cast" =>
        match arg.toNat? with
        | none => .error "usage: cast <id>"
        | some n =>
          match g.findObject? ⟨n⟩ with
          | none => .error "no such object"
          | some o =>
            let tgt :=
              match o.printed.spellEffect with
              | some (.dealDamage _) => some (Target.player (g.opponent chandra))
              | some (.pump _ _) =>
                (g.permanentsOf chandra).filter (·.printed.isCreature) |>.back?
                  |>.map (fun c => Target.permanent c.id)
              | none => none
            g.apply chandra (.cast ⟨n⟩ tgt)
      | _ => .error s!"Unknown command: {cmd}"
    match cmd with
    | "quit" | "exit" =>
      IO.println "Goodbye."
      return
    | "help" => IO.println helpInteractive
    | "state" => printState g
    | _ =>
      match act with
      | .error e => IO.println s!"! {e}"
      | .ok g' =>
        seen ← printLog g' seen
        g := g'
        if g.over then
          printState g
  match g.result with
  | some (.won p) => IO.println s!"Winner: {g.player p |>.name}"
  | some .draw => IO.println "The game is a draw."
  | none => pure ()

def parseArgs (args : List String) : Except String (Bool × UInt64 × Nat) :=
  Id.run do
    let mut interactive := false
    let mut seed : UInt64 := 20260807
    let mut fuel : Nat := 800
    let mut rest := args
    while !rest.isEmpty do
      match rest with
      | "--" :: xs =>
        rest := xs
      | "--help" :: _ => return .error "help"
      | "--auto" :: xs =>
        interactive := false
        rest := xs
      | "--interactive" :: xs =>
        interactive := true
        rest := xs
      | "--seed" :: n :: xs =>
        match n.toNat? with
        | none => return .error s!"Bad seed: {n}"
        | some v =>
          seed := UInt64.ofNat v
          rest := xs
      | "--fuel" :: n :: xs =>
        match n.toNat? with
        | none => return .error s!"Bad fuel: {n}"
        | some v =>
          fuel := v
          rest := xs
      | x :: _ => return .error s!"Unknown argument: {x}"
      | [] => break
    return .ok (interactive, seed, fuel)

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error "help" =>
    IO.println usage
    return 0
  | .error e =>
    IO.eprintln e
    IO.println usage
    return 1
  | .ok (interactive, seed, fuel) =>
    let g ← startDemo seed
    if interactive then
      interactiveLoop g
    else
      runAuto g fuel
    return 0
